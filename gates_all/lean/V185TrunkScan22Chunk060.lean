import V185TrunkScan22Chunk059

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_537864 : List Nat := [2, 1, 3, 2, 4, 1, 1, 3, 5]
def baseStart_537864 : Nat := 118140960795 + 537864 * 2 ^ 59
def prefixEnd_537864 : Nat := 4983230072969 + 3 ^ 40 * 537864 * 2
def baseEnd_537864 : Nat := 61373946388886408516981

theorem tailTrace_537864 : CollatzResearch.WordTrace tailWord_537864 prefixEnd_537864 61373946388886408516981 := by
  unfold tailWord_537864
  simp only [CollatzResearch.WordTrace]
  refine ⟨9808755861709031351486323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13078341148945375135315097 9808755861709031351486323)
  ·
    refine ⟨14713133792563547027229485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9808755861709031351486323 14713133792563547027229485)
    ·
      refine ⟨5517425172211330135211057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14713133792563547027229485 5517425172211330135211057)
      ·
        refine ⟨4138068879158497601408293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5517425172211330135211057 4138068879158497601408293)
        ·
          refine ⟨775887914842218300264055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4138068879158497601408293 775887914842218300264055)
          ·
            refine ⟨1163831872263327450396083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 775887914842218300264055 1163831872263327450396083)
            ·
              refine ⟨1745747808394991175594125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1163831872263327450396083 1745747808394991175594125)
              ·
                refine ⟨654655428148121690847797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1745747808394991175594125 654655428148121690847797)
                ·
                  refine ⟨61373946388886408516981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 654655428148121690847797 61373946388886408516981)
                  ·
                    rfl

theorem cell22_537864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 3, 5].length) (baseStart_537864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_537864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_537864 prefixEnd_537864 := by exact prefixLift 537864
  have htrace : WordTrace (prefixWord ++ tailWord_537864) baseStart_537864 baseEnd_537864 := by
    simpa [prefixWord, tailWord_537864, baseEnd_537864] using wordTrace_append hprefix tailTrace_537864
  have hstable : (prefixWord ++ tailWord_537864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537864).length < 2 ^ (prefixWord ++ tailWord_537864).sum := by decide
  have hdescent : baseEnd_537864 < baseStart_537864 := by decide
  rcases family_descends (prefixWord ++ tailWord_537864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537969 : List Nat := [1, 2, 2, 2, 1, 2, 3, 3, 3, 3]
def baseStart_537969 : Nat := 118140960795 + 537969 * 2 ^ 59
def prefixEnd_537969 : Nat := 4983230072969 + 3 ^ 40 * 537969 * 2
def baseEnd_537969 : Nat := 184157782812473951675621

theorem tailTrace_537969 : CollatzResearch.WordTrace tailWord_537969 prefixEnd_537969 184157782812473951675621 := by
  unfold tailWord_537969
  simp only [CollatzResearch.WordTrace]
  refine ⟨19621341388037665635544961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13080894258691777090363307 19621341388037665635544961)
  ·
    refine ⟨14716006041028249226658721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19621341388037665635544961 14716006041028249226658721)
    ·
      refine ⟨11037004530771186919994041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14716006041028249226658721 11037004530771186919994041)
      ·
        refine ⟨8277753398078390189995531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11037004530771186919994041 8277753398078390189995531)
        ·
          refine ⟨12416630097117585284993297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8277753398078390189995531 12416630097117585284993297)
          ·
            refine ⟨9312472572838188963744973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12416630097117585284993297 9312472572838188963744973)
            ·
              refine ⟨3492177214814320861404365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9312472572838188963744973 3492177214814320861404365)
              ·
                refine ⟨1309566455555370323026637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3492177214814320861404365 1309566455555370323026637)
                ·
                  refine ⟨491087420833263871134989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1309566455555370323026637 491087420833263871134989)
                  ·
                    refine ⟨184157782812473951675621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 491087420833263871134989 184157782812473951675621)
                    ·
                      rfl

theorem cell22_537969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 3, 3, 3].length) (baseStart_537969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_537969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_537969 prefixEnd_537969 := by exact prefixLift 537969
  have htrace : WordTrace (prefixWord ++ tailWord_537969) baseStart_537969 baseEnd_537969 := by
    simpa [prefixWord, tailWord_537969, baseEnd_537969] using wordTrace_append hprefix tailTrace_537969
  have hstable : (prefixWord ++ tailWord_537969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537969).length < 2 ^ (prefixWord ++ tailWord_537969).sum := by decide
  have hdescent : baseEnd_537969 < baseStart_537969 := by decide
  rcases family_descends (prefixWord ++ tailWord_537969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538059 : List Nat := [1, 1, 1, 1, 3, 3, 2, 1, 6, 3]
def baseStart_538059 : Nat := 118140960795 + 538059 * 2 ^ 59
def prefixEnd_538059 : Nat := 4983230072969 + 3 ^ 40 * 538059 * 2
def baseEnd_538059 : Nat := 184188591651743716925345

theorem tailTrace_538059 : CollatzResearch.WordTrace tailWord_538059 prefixEnd_538059 184188591651743716925345 := by
  unfold tailWord_538059
  simp only [CollatzResearch.WordTrace]
  refine ⟨19624623957711611006321231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13083082638474407337547487 19624623957711611006321231)
  ·
    refine ⟨29436935936567416509481847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19624623957711611006321231 29436935936567416509481847)
    ·
      refine ⟨44155403904851124764222771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29436935936567416509481847 44155403904851124764222771)
      ·
        refine ⟨66233105857276687146334157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44155403904851124764222771 66233105857276687146334157)
        ·
          refine ⟨24837414696478757679875309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66233105857276687146334157 24837414696478757679875309)
          ·
            refine ⟨9314030511179534129953241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24837414696478757679875309 9314030511179534129953241)
            ·
              refine ⟨6985522883384650597464931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9314030511179534129953241 6985522883384650597464931)
              ·
                refine ⟨10478284325076975896197397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6985522883384650597464931 10478284325076975896197397)
                ·
                  refine ⟨491169577737983245134253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10478284325076975896197397 491169577737983245134253)
                  ·
                    refine ⟨184188591651743716925345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 491169577737983245134253 184188591651743716925345)
                    ·
                      rfl

theorem cell22_538059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 1, 6, 3].length) (baseStart_538059 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_538059 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_538059 prefixEnd_538059 := by exact prefixLift 538059
  have htrace : WordTrace (prefixWord ++ tailWord_538059) baseStart_538059 baseEnd_538059 := by
    simpa [prefixWord, tailWord_538059, baseEnd_538059] using wordTrace_append hprefix tailTrace_538059
  have hstable : (prefixWord ++ tailWord_538059).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538059).length < 2 ^ (prefixWord ++ tailWord_538059).sum := by decide
  have hdescent : baseEnd_538059 < baseStart_538059 := by decide
  rcases family_descends (prefixWord ++ tailWord_538059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538093 : List Nat := [1, 5, 1, 3, 2, 1, 2, 1, 1, 5]
def baseStart_538093 : Nat := 118140960795 + 538093 * 2 ^ 59
def prefixEnd_538093 : Nat := 4983230072969 + 3 ^ 40 * 538093 * 2
def baseEnd_538093 : Nat := 184200230546578961575241

theorem tailTrace_538093 : CollatzResearch.WordTrace tailWord_538093 prefixEnd_538093 184200230546578961575241 := by
  unfold tailWord_538093
  simp only [CollatzResearch.WordTrace]
  refine ⟨19625864039588434813058933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13083909359725623208705955 19625864039588434813058933)
  ·
    refine ⟨1839924753711415763724275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19625864039588434813058933 1839924753711415763724275)
    ·
      refine ⟨2759887130567123645586413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1839924753711415763724275 2759887130567123645586413)
      ·
        refine ⟨1034957673962671367094905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2759887130567123645586413 1034957673962671367094905)
        ·
          refine ⟨776218255472003525321179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1034957673962671367094905 776218255472003525321179)
          ·
            refine ⟨1164327383208005287981769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 776218255472003525321179 1164327383208005287981769)
            ·
              refine ⟨873245537406003965986327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1164327383208005287981769 873245537406003965986327)
              ·
                refine ⟨1309868306109005948979491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 873245537406003965986327 1309868306109005948979491)
                ·
                  refine ⟨1964802459163508923469237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1309868306109005948979491 1964802459163508923469237)
                  ·
                    refine ⟨184200230546578961575241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1964802459163508923469237 184200230546578961575241)
                    ·
                      rfl

theorem cell22_538093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 2, 1, 1, 5].length) (baseStart_538093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_538093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_538093 prefixEnd_538093 := by exact prefixLift 538093
  have htrace : WordTrace (prefixWord ++ tailWord_538093) baseStart_538093 baseEnd_538093 := by
    simpa [prefixWord, tailWord_538093, baseEnd_538093] using wordTrace_append hprefix tailTrace_538093
  have hstable : (prefixWord ++ tailWord_538093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538093).length < 2 ^ (prefixWord ++ tailWord_538093).sum := by decide
  have hdescent : baseEnd_538093 < baseStart_538093 := by decide
  rcases family_descends (prefixWord ++ tailWord_538093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538172 : List Nat := [2, 2, 2, 2, 4, 2, 1, 3, 1, 3]
def baseStart_538172 : Nat := 118140960795 + 538172 * 2 ^ 59
def prefixEnd_538172 : Nat := 4983230072969 + 3 ^ 40 * 538172 * 2
def baseEnd_538172 : Nat := 184227273861049088849999

theorem tailTrace_538172 : CollatzResearch.WordTrace tailWord_538172 prefixEnd_538172 184227273861049088849999 := by
  unfold tailWord_538172
  simp only [CollatzResearch.WordTrace]
  refine ⟨9814372703151115652592385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13085830270868154203456513 9814372703151115652592385)
  ·
    refine ⟨7360779527363336739444289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9814372703151115652592385 7360779527363336739444289)
    ·
      refine ⟨5520584645522502554583217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7360779527363336739444289 5520584645522502554583217)
      ·
        refine ⟨4140438484141876915937413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5520584645522502554583217 4140438484141876915937413)
        ·
          refine ⟨776332215776601921738265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4140438484141876915937413 776332215776601921738265)
          ·
            refine ⟨582249161832451441303699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 776332215776601921738265 582249161832451441303699)
            ·
              refine ⟨873373742748677161955549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 582249161832451441303699 873373742748677161955549)
              ·
                refine ⟨327515153530753935733331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 873373742748677161955549 327515153530753935733331)
                ·
                  refine ⟨491272730296130903599997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 327515153530753935733331 491272730296130903599997)
                  ·
                    refine ⟨184227273861049088849999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 491272730296130903599997 184227273861049088849999)
                    ·
                      rfl

theorem cell22_538172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 1, 3, 1, 3].length) (baseStart_538172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_538172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_538172 prefixEnd_538172 := by exact prefixLift 538172
  have htrace : WordTrace (prefixWord ++ tailWord_538172) baseStart_538172 baseEnd_538172 := by
    simpa [prefixWord, tailWord_538172, baseEnd_538172] using wordTrace_append hprefix tailTrace_538172
  have hstable : (prefixWord ++ tailWord_538172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538172).length < 2 ^ (prefixWord ++ tailWord_538172).sum := by decide
  have hdescent : baseEnd_538172 < baseStart_538172 := by decide
  rcases family_descends (prefixWord ++ tailWord_538172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538181 : List Nat := [1, 3, 1, 1, 1, 4, 1, 5, 1, 4]
def baseStart_538181 : Nat := 118140960795 + 538181 * 2 ^ 59
def prefixEnd_538181 : Nat := 4983230072969 + 3 ^ 40 * 538181 * 2
def baseEnd_538181 : Nat := 184230354744976065374971

theorem tailTrace_538181 : CollatzResearch.WordTrace tailWord_538181 prefixEnd_538181 184230354744976065374971 := by
  unfold tailWord_538181
  simp only [CollatzResearch.WordTrace]
  refine ⟨19629073663269625842262397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13086049108846417228174931 19629073663269625842262397)
  ·
    refine ⟨7360902623726109690848399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19629073663269625842262397 7360902623726109690848399)
    ·
      refine ⟨11041353935589164536272599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7360902623726109690848399 11041353935589164536272599)
      ·
        refine ⟨16562030903383746804408899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11041353935589164536272599 16562030903383746804408899)
        ·
          refine ⟨24843046355075620206613349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16562030903383746804408899 24843046355075620206613349)
          ·
            refine ⟨4658071191576678788740003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24843046355075620206613349 4658071191576678788740003)
            ·
              refine ⟨6987106787365018183110005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4658071191576678788740003 6987106787365018183110005)
              ·
                refine ⟨655041261315470454666563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6987106787365018183110005 655041261315470454666563)
                ·
                  refine ⟨982561891973205681999845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 655041261315470454666563 982561891973205681999845)
                  ·
                    refine ⟨184230354744976065374971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 982561891973205681999845 184230354744976065374971)
                    ·
                      rfl

theorem cell22_538181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 5, 1, 4].length) (baseStart_538181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_538181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_538181 prefixEnd_538181 := by exact prefixLift 538181
  have htrace : WordTrace (prefixWord ++ tailWord_538181) baseStart_538181 baseEnd_538181 := by
    simpa [prefixWord, tailWord_538181, baseEnd_538181] using wordTrace_append hprefix tailTrace_538181
  have hstable : (prefixWord ++ tailWord_538181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538181).length < 2 ^ (prefixWord ++ tailWord_538181).sum := by decide
  have hdescent : baseEnd_538181 < baseStart_538181 := by decide
  rcases family_descends (prefixWord ++ tailWord_538181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538189 : List Nat := [1, 6, 1, 1, 3, 1, 3, 2, 1, 3]
def baseStart_538189 : Nat := 118140960795 + 538189 * 2 ^ 59
def prefixEnd_538189 : Nat := 4983230072969 + 3 ^ 40 * 538189 * 2
def baseEnd_538189 : Nat := 184233093308466711174947

theorem tailTrace_538189 : CollatzResearch.WordTrace tailWord_538189 prefixEnd_538189 184233093308466711174947 := by
  unfold tailWord_538189
  simp only [CollatzResearch.WordTrace]
  refine ⟨19629365447240643208553621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13086243631493762139035747 19629365447240643208553621)
  ·
    refine ⟨920126505339405150400951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 19629365447240643208553621 920126505339405150400951)
    ·
      refine ⟨1380189758009107725601427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 920126505339405150400951 1380189758009107725601427)
      ·
        refine ⟨2070284637013661588402141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1380189758009107725601427 2070284637013661588402141)
        ·
          refine ⟨776356738880123095650803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2070284637013661588402141 776356738880123095650803)
          ·
            refine ⟨1164535108320184643476205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 776356738880123095650803 1164535108320184643476205)
            ·
              refine ⟨436700665620069241303577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1164535108320184643476205 436700665620069241303577)
              ·
                refine ⟨327525499215051930977683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 436700665620069241303577 327525499215051930977683)
                ·
                  refine ⟨491288248822577896466525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 327525499215051930977683 491288248822577896466525)
                  ·
                    refine ⟨184233093308466711174947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 491288248822577896466525 184233093308466711174947)
                    ·
                      rfl

theorem cell22_538189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 3, 2, 1, 3].length) (baseStart_538189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_538189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_538189 prefixEnd_538189 := by exact prefixLift 538189
  have htrace : WordTrace (prefixWord ++ tailWord_538189) baseStart_538189 baseEnd_538189 := by
    simpa [prefixWord, tailWord_538189, baseEnd_538189] using wordTrace_append hprefix tailTrace_538189
  have hstable : (prefixWord ++ tailWord_538189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538189).length < 2 ^ (prefixWord ++ tailWord_538189).sum := by decide
  have hdescent : baseEnd_538189 < baseStart_538189 := by decide
  rcases family_descends (prefixWord ++ tailWord_538189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538239 : List Nat := [1, 1, 2, 2, 1, 1, 1, 2, 4, 7]
def baseStart_538239 : Nat := 118140960795 + 538239 * 2 ^ 59
def prefixEnd_538239 : Nat := 4983230072969 + 3 ^ 40 * 538239 * 2
def baseEnd_538239 : Nat := 184250209330283247424793

theorem tailTrace_538239 : CollatzResearch.WordTrace tailWord_538239 prefixEnd_538239 184250209330283247424793 := by
  unfold tailWord_538239
  simp only [CollatzResearch.WordTrace]
  refine ⟨19631189097059501747873771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13087459398039667831915847 19631189097059501747873771)
  ·
    refine ⟨29446783645589252621810657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19631189097059501747873771 29446783645589252621810657)
    ·
      refine ⟨22085087734191939466357993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29446783645589252621810657 22085087734191939466357993)
      ·
        refine ⟨16563815800643954599768495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22085087734191939466357993 16563815800643954599768495)
        ·
          refine ⟨24845723700965931899652743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16563815800643954599768495 24845723700965931899652743)
          ·
            refine ⟨37268585551448897849479115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24845723700965931899652743 37268585551448897849479115)
            ·
              refine ⟨55902878327173346774218673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37268585551448897849479115 55902878327173346774218673)
              ·
                refine ⟨41927158745380010080664005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55902878327173346774218673 41927158745380010080664005)
                ·
                  refine ⟨7861342264758751890124501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41927158745380010080664005 7861342264758751890124501)
                  ·
                    refine ⟨184250209330283247424793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7861342264758751890124501 184250209330283247424793)
                    ·
                      rfl

theorem cell22_538239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 4, 7].length) (baseStart_538239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_538239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_538239 prefixEnd_538239 := by exact prefixLift 538239
  have htrace : WordTrace (prefixWord ++ tailWord_538239) baseStart_538239 baseEnd_538239 := by
    simpa [prefixWord, tailWord_538239, baseEnd_538239] using wordTrace_append hprefix tailTrace_538239
  have hstable : (prefixWord ++ tailWord_538239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538239).length < 2 ^ (prefixWord ++ tailWord_538239).sum := by decide
  have hdescent : baseEnd_538239 < baseStart_538239 := by decide
  rcases family_descends (prefixWord ++ tailWord_538239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538256 : List Nat := [2, 1, 1, 1, 1, 1, 3, 2, 7, 3]
def baseStart_538256 : Nat := 118140960795 + 538256 * 2 ^ 59
def prefixEnd_538256 : Nat := 4983230072969 + 3 ^ 40 * 538256 * 2
def baseEnd_538256 : Nat := 184256028777700869749741

theorem tailTrace_538256 : CollatzResearch.WordTrace tailWord_538256 prefixEnd_538256 184256028777700869749741 := by
  unfold tailWord_538256
  simp only [CollatzResearch.WordTrace]
  refine ⟨9815904568998956825621311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13087872758665275767495081 9815904568998956825621311)
  ·
    refine ⟨14723856853498435238431967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9815904568998956825621311 14723856853498435238431967)
    ·
      refine ⟨22085785280247652857647951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14723856853498435238431967 22085785280247652857647951)
      ·
        refine ⟨33128677920371479286471927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22085785280247652857647951 33128677920371479286471927)
        ·
          refine ⟨49693016880557218929707891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33128677920371479286471927 49693016880557218929707891)
          ·
            refine ⟨74539525320835828394561837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49693016880557218929707891 74539525320835828394561837)
            ·
              refine ⟨27952321995313435647960689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 74539525320835828394561837 27952321995313435647960689)
              ·
                refine ⟨20964241496485076735970517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27952321995313435647960689 20964241496485076735970517)
                ·
                  refine ⟨491349410073868985999309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20964241496485076735970517 491349410073868985999309)
                  ·
                    refine ⟨184256028777700869749741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 491349410073868985999309 184256028777700869749741)
                    ·
                      rfl

theorem cell22_538256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 7, 3].length) (baseStart_538256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_538256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_538256 prefixEnd_538256 := by exact prefixLift 538256
  have htrace : WordTrace (prefixWord ++ tailWord_538256) baseStart_538256 baseEnd_538256 := by
    simpa [prefixWord, tailWord_538256, baseEnd_538256] using wordTrace_append hprefix tailTrace_538256
  have hstable : (prefixWord ++ tailWord_538256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538256).length < 2 ^ (prefixWord ++ tailWord_538256).sum := by decide
  have hdescent : baseEnd_538256 < baseStart_538256 := by decide
  rcases family_descends (prefixWord ++ tailWord_538256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538273 : List Nat := [1, 2, 3, 3, 2, 1, 1, 1, 5, 3]
def baseStart_538273 : Nat := 118140960795 + 538273 * 2 ^ 59
def prefixEnd_538273 : Nat := 4983230072969 + 3 ^ 40 * 538273 * 2
def baseEnd_538273 : Nat := 184261848225118492074689

theorem tailTrace_538273 : CollatzResearch.WordTrace tailWord_538273 prefixEnd_538273 184261848225118492074689 := by
  unfold tailWord_538273
  simp only [CollatzResearch.WordTrace]
  refine ⟨19632429178936325554611473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13088286119290883703074315 19632429178936325554611473)
  ·
    refine ⟨14724321884202244165958605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19632429178936325554611473 14724321884202244165958605)
    ·
      refine ⟨5521620706575841562234477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14724321884202244165958605 5521620706575841562234477)
      ·
        refine ⟨2070607764965940585837929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5521620706575841562234477 2070607764965940585837929)
        ·
          refine ⟨1552955823724455439378447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2070607764965940585837929 1552955823724455439378447)
          ·
            refine ⟨2329433735586683159067671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1552955823724455439378447 2329433735586683159067671)
            ·
              refine ⟨3494150603380024738601507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2329433735586683159067671 3494150603380024738601507)
              ·
                refine ⟨5241225905070037107902261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3494150603380024738601507 5241225905070037107902261)
                ·
                  refine ⟨491364928600315978865837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5241225905070037107902261 491364928600315978865837)
                  ·
                    refine ⟨184261848225118492074689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 491364928600315978865837 184261848225118492074689)
                    ·
                      rfl

theorem cell22_538273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 1, 5, 3].length) (baseStart_538273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_538273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_538273 prefixEnd_538273 := by exact prefixLift 538273
  have htrace : WordTrace (prefixWord ++ tailWord_538273) baseStart_538273 baseEnd_538273 := by
    simpa [prefixWord, tailWord_538273, baseEnd_538273] using wordTrace_append hprefix tailTrace_538273
  have hstable : (prefixWord ++ tailWord_538273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538273).length < 2 ^ (prefixWord ++ tailWord_538273).sum := by decide
  have hdescent : baseEnd_538273 < baseStart_538273 := by decide
  rcases family_descends (prefixWord ++ tailWord_538273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538290 : List Nat := [3, 2, 1, 1, 1, 2, 3, 5, 1, 3]
def baseStart_538290 : Nat := 118140960795 + 538290 * 2 ^ 59
def prefixEnd_538290 : Nat := 4983230072969 + 3 ^ 40 * 538290 * 2
def baseEnd_538290 : Nat := 184267667672536114399637

theorem tailTrace_538290 : CollatzResearch.WordTrace tailWord_538290 prefixEnd_538290 184267667672536114399637 := by
  unfold tailWord_538290
  simp only [CollatzResearch.WordTrace]
  refine ⟨4908262304968684364495081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13088699479916491638653549 4908262304968684364495081)
  ·
    refine ⟨3681196728726513273371311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4908262304968684364495081 3681196728726513273371311)
    ·
      refine ⟨5521795093089769910056967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3681196728726513273371311 5521795093089769910056967)
      ·
        refine ⟨8282692639634654865085451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5521795093089769910056967 8282692639634654865085451)
        ·
          refine ⟨12424038959451982297628177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8282692639634654865085451 12424038959451982297628177)
          ·
            refine ⟨9318029219588986723221133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12424038959451982297628177 9318029219588986723221133)
            ·
              refine ⟨3494260957345870021207925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9318029219588986723221133 3494260957345870021207925)
              ·
                refine ⟨327586964751175314488243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3494260957345870021207925 327586964751175314488243)
                ·
                  refine ⟨491380447126762971732365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 327586964751175314488243 491380447126762971732365)
                  ·
                    refine ⟨184267667672536114399637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 491380447126762971732365 184267667672536114399637)
                    ·
                      rfl

theorem cell22_538290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 5, 1, 3].length) (baseStart_538290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_538290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_538290 prefixEnd_538290 := by exact prefixLift 538290
  have htrace : WordTrace (prefixWord ++ tailWord_538290) baseStart_538290 baseEnd_538290 := by
    simpa [prefixWord, tailWord_538290, baseEnd_538290] using wordTrace_append hprefix tailTrace_538290
  have hstable : (prefixWord ++ tailWord_538290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538290).length < 2 ^ (prefixWord ++ tailWord_538290).sum := by decide
  have hdescent : baseEnd_538290 < baseStart_538290 := by decide
  rcases family_descends (prefixWord ++ tailWord_538290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538301 : List Nat := [1, 4, 1, 2, 1, 2, 1, 1, 4, 5]
def baseStart_538301 : Nat := 118140960795 + 538301 * 2 ^ 59
def prefixEnd_538301 : Nat := 4983230072969 + 3 ^ 40 * 538301 * 2
def baseEnd_538301 : Nat := 184271433197335752374603

theorem tailTrace_538301 : CollatzResearch.WordTrace tailWord_538301 prefixEnd_538301 184271433197335752374603 := by
  unfold tailWord_538301
  simp only [CollatzResearch.WordTrace]
  refine ⟨19633450422834886336630757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13088966948556590891087171 19633450422834886336630757)
  ·
    refine ⟨3681271954281541188118267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19633450422834886336630757 3681271954281541188118267)
    ·
      refine ⟨5521907931422311782177401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3681271954281541188118267 5521907931422311782177401)
      ·
        refine ⟨4141430948566733836633051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5521907931422311782177401 4141430948566733836633051)
        ·
          refine ⟨6212146422850100754949577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4141430948566733836633051 6212146422850100754949577)
          ·
            refine ⟨4659109817137575566212183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6212146422850100754949577 4659109817137575566212183)
            ·
              refine ⟨6988664725706363349318275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4659109817137575566212183 6988664725706363349318275)
              ·
                refine ⟨10482997088559545023977413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6988664725706363349318275 10482997088559545023977413)
                ·
                  refine ⟨1965561954104914691995765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10482997088559545023977413 1965561954104914691995765)
                  ·
                    refine ⟨184271433197335752374603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1965561954104914691995765 184271433197335752374603)
                    ·
                      rfl

theorem cell22_538301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 1, 4, 5].length) (baseStart_538301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_538301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_538301 prefixEnd_538301 := by exact prefixLift 538301
  have htrace : WordTrace (prefixWord ++ tailWord_538301) baseStart_538301 baseEnd_538301 := by
    simpa [prefixWord, tailWord_538301, baseEnd_538301] using wordTrace_append hprefix tailTrace_538301
  have hstable : (prefixWord ++ tailWord_538301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538301).length < 2 ^ (prefixWord ++ tailWord_538301).sum := by decide
  have hdescent : baseEnd_538301 < baseStart_538301 := by decide
  rcases family_descends (prefixWord ++ tailWord_538301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538414 : List Nat := [4, 1, 3, 2, 2, 1, 2, 2, 2, 3]
def baseStart_538414 : Nat := 118140960795 + 538414 * 2 ^ 59
def prefixEnd_538414 : Nat := 4983230072969 + 3 ^ 40 * 538414 * 2
def baseEnd_538414 : Nat := 184310115406641124299257

theorem tailTrace_538414 : CollatzResearch.WordTrace tailWord_538414 prefixEnd_538414 184310115406641124299257 := by
  unfold tailWord_538414
  simp only [CollatzResearch.WordTrace]
  refine ⟨2454696483928188329436787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13091714580950337756996197 2454696483928188329436787)
  ·
    refine ⟨3682044725892282494155181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2454696483928188329436787 3682044725892282494155181)
    ·
      refine ⟨1380766772209605935308193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3682044725892282494155181 1380766772209605935308193)
      ·
        refine ⟨1035575079157204451481145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1380766772209605935308193 1035575079157204451481145)
        ·
          refine ⟨776681309367903338610859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1035575079157204451481145 776681309367903338610859)
          ·
            refine ⟨1165021964051855007916289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 776681309367903338610859 1165021964051855007916289)
            ·
              refine ⟨873766473038891255937217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1165021964051855007916289 873766473038891255937217)
              ·
                refine ⟨655324854779168441952913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 873766473038891255937217 655324854779168441952913)
                ·
                  refine ⟨491493641084376331464685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 655324854779168441952913 491493641084376331464685)
                  ·
                    refine ⟨184310115406641124299257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 491493641084376331464685 184310115406641124299257)
                    ·
                      rfl

theorem cell22_538414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 2, 2, 2, 3].length) (baseStart_538414 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_538414 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_538414 prefixEnd_538414 := by exact prefixLift 538414
  have htrace : WordTrace (prefixWord ++ tailWord_538414) baseStart_538414 baseEnd_538414 := by
    simpa [prefixWord, tailWord_538414, baseEnd_538414] using wordTrace_append hprefix tailTrace_538414
  have hstable : (prefixWord ++ tailWord_538414).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538414).length < 2 ^ (prefixWord ++ tailWord_538414).sum := by decide
  have hdescent : baseEnd_538414 < baseStart_538414 := by decide
  rcases family_descends (prefixWord ++ tailWord_538414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538513 : List Nat := [1, 2, 2, 1, 1, 1, 6, 1, 1, 6]
def baseStart_538513 : Nat := 118140960795 + 538513 * 2 ^ 59
def prefixEnd_538513 : Nat := 4983230072969 + 3 ^ 40 * 538513 * 2
def baseEnd_538513 : Nat := 184344005129837866073953

theorem tailTrace_538513 : CollatzResearch.WordTrace tailWord_538513 prefixEnd_538513 184344005129837866073953 := by
  unfold tailWord_538513
  simp only [CollatzResearch.WordTrace]
  refine ⟨19641182698066846543348193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13094121798711231028898795 19641182698066846543348193)
  ·
    refine ⟨14730887023550134907511145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19641182698066846543348193 14730887023550134907511145)
    ·
      refine ⟨11048165267662601180633359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14730887023550134907511145 11048165267662601180633359)
      ·
        refine ⟨16572247901493901770950039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11048165267662601180633359 16572247901493901770950039)
        ·
          refine ⟨24858371852240852656425059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16572247901493901770950039 24858371852240852656425059)
          ·
            refine ⟨37287557778361278984637589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24858371852240852656425059 37287557778361278984637589)
            ·
              refine ⟨1747854270860684952404887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 37287557778361278984637589 1747854270860684952404887)
              ·
                refine ⟨2621781406291027428607331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1747854270860684952404887 2621781406291027428607331)
                ·
                  refine ⟨3932672109436541142910997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2621781406291027428607331 3932672109436541142910997)
                  ·
                    refine ⟨184344005129837866073953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3932672109436541142910997 184344005129837866073953)
                    ·
                      rfl

theorem cell22_538513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 6].length) (baseStart_538513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_538513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_538513 prefixEnd_538513 := by exact prefixLift 538513
  have htrace : WordTrace (prefixWord ++ tailWord_538513) baseStart_538513 baseEnd_538513 := by
    simpa [prefixWord, tailWord_538513, baseEnd_538513] using wordTrace_append hprefix tailTrace_538513
  have hstable : (prefixWord ++ tailWord_538513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538513).length < 2 ^ (prefixWord ++ tailWord_538513).sum := by decide
  have hdescent : baseEnd_538513 < baseStart_538513 := by decide
  rcases family_descends (prefixWord ++ tailWord_538513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538545 : List Nat := [1, 2, 2, 4, 2, 2, 2, 7]
def baseStart_538545 : Nat := 118140960795 + 538545 * 2 ^ 59
def prefixEnd_538545 : Nat := 4983230072969 + 3 ^ 40 * 538545 * 2
def baseEnd_538545 : Nat := 20483884375977827697095

theorem tailTrace_538545 : CollatzResearch.WordTrace tailWord_538545 prefixEnd_538545 20483884375977827697095 := by
  unfold tailWord_538545
  simp only [CollatzResearch.WordTrace]
  refine ⟨19642349833950916008513089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13094899889300610672342059 19642349833950916008513089)
  ·
    refine ⟨14731762375463187006384817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19642349833950916008513089 14731762375463187006384817)
    ·
      refine ⟨11048821781597390254788613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14731762375463187006384817 11048821781597390254788613)
      ·
        refine ⟨2071654084049510672772865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11048821781597390254788613 2071654084049510672772865)
        ·
          refine ⟨1553740563037133004579649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2071654084049510672772865 1553740563037133004579649)
          ·
            refine ⟨1165305422277849753434737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1553740563037133004579649 1165305422277849753434737)
            ·
              refine ⟨873979066708387315076053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1165305422277849753434737 873979066708387315076053)
              ·
                refine ⟨20483884375977827697095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 873979066708387315076053 20483884375977827697095)
                ·
                  rfl

theorem cell22_538545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 2, 7].length) (baseStart_538545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_538545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_538545 prefixEnd_538545 := by exact prefixLift 538545
  have htrace : WordTrace (prefixWord ++ tailWord_538545) baseStart_538545 baseEnd_538545 := by
    simpa [prefixWord, tailWord_538545, baseEnd_538545] using wordTrace_append hprefix tailTrace_538545
  have hstable : (prefixWord ++ tailWord_538545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538545).length < 2 ^ (prefixWord ++ tailWord_538545).sum := by decide
  have hdescent : baseEnd_538545 < baseStart_538545 := by decide
  rcases family_descends (prefixWord ++ tailWord_538545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538549 : List Nat := [1, 3, 3, 2, 1, 2, 4, 1, 2, 3]
def baseStart_538549 : Nat := 118140960795 + 538549 * 2 ^ 59
def prefixEnd_538549 : Nat := 4983230072969 + 3 ^ 40 * 538549 * 2
def baseEnd_538549 : Nat := 184356328665545772173843

theorem tailTrace_538549 : CollatzResearch.WordTrace tailWord_538549 prefixEnd_538549 184356328665545772173843 := by
  unfold tailWord_538549
  simp only [CollatzResearch.WordTrace]
  refine ⟨19642495725936424691658701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13094997150624283127772467 19642495725936424691658701)
  ·
    refine ⟨7365935897226159259372013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19642495725936424691658701 7365935897226159259372013)
    ·
      refine ⟨2762225961459809722264505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7365935897226159259372013 2762225961459809722264505)
      ·
        refine ⟨2071669471094857291698379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2762225961459809722264505 2071669471094857291698379)
        ·
          refine ⟨3107504206642285937547569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2071669471094857291698379 3107504206642285937547569)
          ·
            refine ⟨2330628154981714453160677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3107504206642285937547569 2330628154981714453160677)
            ·
              refine ⟨436992779059071459967627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2330628154981714453160677 436992779059071459967627)
              ·
                refine ⟨655489168588607189951441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 436992779059071459967627 655489168588607189951441)
                ·
                  refine ⟨491616876441455392463581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 655489168588607189951441 491616876441455392463581)
                  ·
                    refine ⟨184356328665545772173843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 491616876441455392463581 184356328665545772173843)
                    ·
                      rfl

theorem cell22_538549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 4, 1, 2, 3].length) (baseStart_538549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_538549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_538549 prefixEnd_538549 := by exact prefixLift 538549
  have htrace : WordTrace (prefixWord ++ tailWord_538549) baseStart_538549 baseEnd_538549 := by
    simpa [prefixWord, tailWord_538549, baseEnd_538549] using wordTrace_append hprefix tailTrace_538549
  have hstable : (prefixWord ++ tailWord_538549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538549).length < 2 ^ (prefixWord ++ tailWord_538549).sum := by decide
  have hdescent : baseEnd_538549 < baseStart_538549 := by decide
  rcases family_descends (prefixWord ++ tailWord_538549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538560 : List Nat := [2, 1, 1, 2, 3, 2, 2, 1, 5, 3]
def baseStart_538560 : Nat := 118140960795 + 538560 * 2 ^ 59
def prefixEnd_538560 : Nat := 4983230072969 + 3 ^ 40 * 538560 * 2
def baseEnd_538560 : Nat := 184360094190345410148809

theorem tailTrace_538560 : CollatzResearch.WordTrace tailWord_538560 prefixEnd_538560 184360094190345410148809 := by
  unfold tailWord_538560
  simp only [CollatzResearch.WordTrace]
  refine ⟨9821448464448286785154567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13095264619264382380206089 9821448464448286785154567)
  ·
    refine ⟨14732172696672430177731851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9821448464448286785154567 14732172696672430177731851)
    ·
      refine ⟨22098259045008645266597777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14732172696672430177731851 22098259045008645266597777)
      ·
        refine ⟨16573694283756483949948333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22098259045008645266597777 16573694283756483949948333)
        ·
          refine ⟨6215135356408681481230625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16573694283756483949948333 6215135356408681481230625)
          ·
            refine ⟨4661351517306511110922969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6215135356408681481230625 4661351517306511110922969)
            ·
              refine ⟨3496013637979883333192227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4661351517306511110922969 3496013637979883333192227)
              ·
                refine ⟨5244020456969824999788341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3496013637979883333192227 5244020456969824999788341)
                ·
                  refine ⟨491626917840921093730157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5244020456969824999788341 491626917840921093730157)
                  ·
                    refine ⟨184360094190345410148809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 491626917840921093730157 184360094190345410148809)
                    ·
                      rfl

theorem cell22_538560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 1, 5, 3].length) (baseStart_538560 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_538560 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_538560 prefixEnd_538560 := by exact prefixLift 538560
  have htrace : WordTrace (prefixWord ++ tailWord_538560) baseStart_538560 baseEnd_538560 := by
    simpa [prefixWord, tailWord_538560, baseEnd_538560] using wordTrace_append hprefix tailTrace_538560
  have hstable : (prefixWord ++ tailWord_538560).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538560).length < 2 ^ (prefixWord ++ tailWord_538560).sum := by decide
  have hdescent : baseEnd_538560 < baseStart_538560 := by decide
  rcases family_descends (prefixWord ++ tailWord_538560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538620 : List Nat := [2, 2, 2, 1, 2, 2, 1, 3, 3, 4]
def baseStart_538620 : Nat := 118140960795 + 538620 * 2 ^ 59
def prefixEnd_538620 : Nat := 4983230072969 + 3 ^ 40 * 538620 * 2
def baseEnd_538620 : Nat := 184380633416525253648625

theorem tailTrace_538620 : CollatzResearch.WordTrace tailWord_538620 prefixEnd_538620 184380633416525253648625 := by
  unfold tailWord_538620
  simp only [CollatzResearch.WordTrace]
  refine ⟨9822542654339601908746657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13096723539119469211662209 9822542654339601908746657)
  ·
    refine ⟨7366906990754701431559993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9822542654339601908746657 7366906990754701431559993)
    ·
      refine ⟨5525180243066026073669995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7366906990754701431559993 5525180243066026073669995)
      ·
        refine ⟨8287770364599039110504993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5525180243066026073669995 8287770364599039110504993)
        ·
          refine ⟨6215827773449279332878745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8287770364599039110504993 6215827773449279332878745)
          ·
            refine ⟨4661870830086959499659059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6215827773449279332878745 4661870830086959499659059)
            ·
              refine ⟨6992806245130439249488589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4661870830086959499659059 6992806245130439249488589)
              ·
                refine ⟨2622302341923914718558221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6992806245130439249488589 2622302341923914718558221)
                ·
                  refine ⟨983363378221468019459333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2622302341923914718558221 983363378221468019459333)
                  ·
                    refine ⟨184380633416525253648625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 983363378221468019459333 184380633416525253648625)
                    ·
                      rfl

theorem cell22_538620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 3, 3, 4].length) (baseStart_538620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_538620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_538620 prefixEnd_538620 := by exact prefixLift 538620
  have htrace : WordTrace (prefixWord ++ tailWord_538620) baseStart_538620 baseEnd_538620 := by
    simpa [prefixWord, tailWord_538620, baseEnd_538620] using wordTrace_append hprefix tailTrace_538620
  have hstable : (prefixWord ++ tailWord_538620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538620).length < 2 ^ (prefixWord ++ tailWord_538620).sum := by decide
  have hdescent : baseEnd_538620 < baseStart_538620 := by decide
  rcases family_descends (prefixWord ++ tailWord_538620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538628 : List Nat := [2, 3, 2, 4, 1, 1, 2, 3, 1, 3]
def baseStart_538628 : Nat := 118140960795 + 538628 * 2 ^ 59
def prefixEnd_538628 : Nat := 4983230072969 + 3 ^ 40 * 538628 * 2
def baseEnd_538628 : Nat := 184383371980015899448601

theorem tailTrace_538628 : CollatzResearch.WordTrace tailWord_538628 prefixEnd_538628 184383371980015899448601 := by
  unfold tailWord_538628
  simp only [CollatzResearch.WordTrace]
  refine ⟨9822688546325110591892269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13096918061766814122523025 9822688546325110591892269)
  ·
    refine ⟨3683508204871916471959601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9822688546325110591892269 3683508204871916471959601)
    ·
      refine ⟨2762631153653937353969701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3683508204871916471959601 2762631153653937353969701)
      ·
        refine ⟨517993341310113253869319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2762631153653937353969701 517993341310113253869319)
        ·
          refine ⟨776990011965169880803979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 517993341310113253869319 776990011965169880803979)
          ·
            refine ⟨1165485017947754821205969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 776990011965169880803979 1165485017947754821205969)
            ·
              refine ⟨874113763460816115904477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1165485017947754821205969 874113763460816115904477)
              ·
                refine ⟨327792661297806043464179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 874113763460816115904477 327792661297806043464179)
                ·
                  refine ⟨491688991946709065196269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 327792661297806043464179 491688991946709065196269)
                  ·
                    refine ⟨184383371980015899448601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 491688991946709065196269 184383371980015899448601)
                    ·
                      rfl

theorem cell22_538628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 2, 3, 1, 3].length) (baseStart_538628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_538628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_538628 prefixEnd_538628 := by exact prefixLift 538628
  have htrace : WordTrace (prefixWord ++ tailWord_538628) baseStart_538628 baseEnd_538628 := by
    simpa [prefixWord, tailWord_538628, baseEnd_538628] using wordTrace_append hprefix tailTrace_538628
  have hstable : (prefixWord ++ tailWord_538628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538628).length < 2 ^ (prefixWord ++ tailWord_538628).sum := by decide
  have hdescent : baseEnd_538628 < baseStart_538628 := by decide
  rcases family_descends (prefixWord ++ tailWord_538628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538652 : List Nat := [2, 2, 3, 1, 3, 2, 2, 1, 6]
def baseStart_538652 : Nat := 118140960795 + 538652 * 2 ^ 59
def prefixEnd_538652 : Nat := 4983230072969 + 3 ^ 40 * 538652 * 2
def baseEnd_538652 : Nat := 61463862556829278949509

theorem tailTrace_538652 : CollatzResearch.WordTrace tailWord_538652 prefixEnd_538652 61463862556829278949509 := by
  unfold tailWord_538652
  simp only [CollatzResearch.WordTrace]
  refine ⟨9823126222281636641329105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13097501629708848855105473 9823126222281636641329105)
  ·
    refine ⟨7367344666711227480996829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9823126222281636641329105 7367344666711227480996829)
    ·
      refine ⟨2762754250016710305373811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7367344666711227480996829 2762754250016710305373811)
      ·
        refine ⟨4144131375025065458060717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2762754250016710305373811 4144131375025065458060717)
        ·
          refine ⟨1554049265634399546772769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4144131375025065458060717 1554049265634399546772769)
          ·
            refine ⟨1165536949225799660079577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1554049265634399546772769 1165536949225799660079577)
            ·
              refine ⟨874152711919349745059683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1165536949225799660079577 874152711919349745059683)
              ·
                refine ⟨1311229067879024617589525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 874152711919349745059683 1311229067879024617589525)
                ·
                  refine ⟨61463862556829278949509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1311229067879024617589525 61463862556829278949509)
                  ·
                    rfl

theorem cell22_538652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 2, 1, 6].length) (baseStart_538652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_538652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_538652 prefixEnd_538652 := by exact prefixLift 538652
  have htrace : WordTrace (prefixWord ++ tailWord_538652) baseStart_538652 baseEnd_538652 := by
    simpa [prefixWord, tailWord_538652, baseEnd_538652] using wordTrace_append hprefix tailTrace_538652
  have hstable : (prefixWord ++ tailWord_538652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538652).length < 2 ^ (prefixWord ++ tailWord_538652).sum := by decide
  have hdescent : baseEnd_538652 < baseStart_538652 := by decide
  rcases family_descends (prefixWord ++ tailWord_538652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538802 : List Nat := [3, 2, 1, 1, 1, 3, 1, 4, 1, 5]
def baseStart_538802 : Nat := 118140960795 + 538802 * 2 ^ 59
def prefixEnd_538802 : Nat := 4983230072969 + 3 ^ 40 * 538802 * 2
def baseEnd_538802 : Nat := 184442935735937445598067

theorem tailTrace_538802 : CollatzResearch.WordTrace tailWord_538802 prefixEnd_538802 184442935735937445598067 := by
  unfold tailWord_538802
  simp only [CollatzResearch.WordTrace]
  refine ⟨4912930848504962225154665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13101148929346565933745773 4912930848504962225154665)
  ·
    refine ⟨3684698136378721668865999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4912930848504962225154665 3684698136378721668865999)
    ·
      refine ⟨5527047204568082503298999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3684698136378721668865999 5527047204568082503298999)
      ·
        refine ⟨8290570806852123754948499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5527047204568082503298999 8290570806852123754948499)
        ·
          refine ⟨12435856210278185632422749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8290570806852123754948499 12435856210278185632422749)
          ·
            refine ⟨4663446078854319612158531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12435856210278185632422749 4663446078854319612158531)
            ·
              refine ⟨6995169118281479418237797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4663446078854319612158531 6995169118281479418237797)
              ·
                refine ⟨1311594209677777390919587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6995169118281479418237797 1311594209677777390919587)
                ·
                  refine ⟨1967391314516666086379381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1311594209677777390919587 1967391314516666086379381)
                  ·
                    refine ⟨184442935735937445598067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1967391314516666086379381 184442935735937445598067)
                    ·
                      rfl

theorem cell22_538802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 4, 1, 5].length) (baseStart_538802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_538802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_538802 prefixEnd_538802 := by exact prefixLift 538802
  have htrace : WordTrace (prefixWord ++ tailWord_538802) baseStart_538802 baseEnd_538802 := by
    simpa [prefixWord, tailWord_538802, baseEnd_538802] using wordTrace_append hprefix tailTrace_538802
  have hstable : (prefixWord ++ tailWord_538802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538802).length < 2 ^ (prefixWord ++ tailWord_538802).sum := by decide
  have hdescent : baseEnd_538802 < baseStart_538802 := by decide
  rcases family_descends (prefixWord ++ tailWord_538802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538862 : List Nat := [4, 1, 2, 1, 1, 1, 1, 2, 1, 8]
def baseStart_538862 : Nat := 118140960795 + 538862 * 2 ^ 59
def prefixEnd_538862 : Nat := 4983230072969 + 3 ^ 40 * 538862 * 2
def baseEnd_538862 : Nat := 184463474962117289097883

theorem tailTrace_538862 : CollatzResearch.WordTrace tailWord_538862 prefixEnd_538862 184463474962117289097883 := by
  unfold tailWord_538862
  simp only [CollatzResearch.WordTrace]
  refine ⟨2456738971725309893475355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13102607849201652765201893 2456738971725309893475355)
  ·
    refine ⟨3685108457587964840213033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2456738971725309893475355 3685108457587964840213033)
    ·
      refine ⟨2763831343190973630159775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3685108457587964840213033 2763831343190973630159775)
      ·
        refine ⟨4145747014786460445239663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2763831343190973630159775 4145747014786460445239663)
        ·
          refine ⟨6218620522179690667859495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4145747014786460445239663 6218620522179690667859495)
          ·
            refine ⟨9327930783269536001789243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6218620522179690667859495 9327930783269536001789243)
            ·
              refine ⟨13991896174904304002683865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9327930783269536001789243 13991896174904304002683865)
              ·
                refine ⟨10493922131178228002012899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13991896174904304002683865 10493922131178228002012899)
                ·
                  refine ⟨15740883196767342003019349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10493922131178228002012899 15740883196767342003019349)
                  ·
                    refine ⟨184463474962117289097883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 15740883196767342003019349 184463474962117289097883)
                    ·
                      rfl

theorem cell22_538862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 2, 1, 8].length) (baseStart_538862 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_538862 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_538862 prefixEnd_538862 := by exact prefixLift 538862
  have htrace : WordTrace (prefixWord ++ tailWord_538862) baseStart_538862 baseEnd_538862 := by
    simpa [prefixWord, tailWord_538862, baseEnd_538862] using wordTrace_append hprefix tailTrace_538862
  have hstable : (prefixWord ++ tailWord_538862).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538862).length < 2 ^ (prefixWord ++ tailWord_538862).sum := by decide
  have hdescent : baseEnd_538862 < baseStart_538862 := by decide
  rcases family_descends (prefixWord ++ tailWord_538862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538887 : List Nat := [1, 1, 4, 5, 2, 1, 2, 1, 2, 3]
def baseStart_538887 : Nat := 118140960795 + 538887 * 2 ^ 59
def prefixEnd_538887 : Nat := 4983230072969 + 3 ^ 40 * 538887 * 2
def baseEnd_538887 : Nat := 184472032973025557222807

theorem tailTrace_538887 : CollatzResearch.WordTrace tailWord_538887 prefixEnd_538887 184472032973025557222807 := by
  unfold tailWord_538887
  simp only [CollatzResearch.WordTrace]
  refine ⟨19654823598711908417462915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13103215732474605611641943 19654823598711908417462915)
  ·
    refine ⟨29482235398067862626194373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19654823598711908417462915 29482235398067862626194373)
    ·
      refine ⟨5527919137137724242411445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29482235398067862626194373 5527919137137724242411445)
      ·
        refine ⟨518242419106661647726073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5527919137137724242411445 518242419106661647726073)
        ·
          refine ⟨388681814329996235794555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 518242419106661647726073 388681814329996235794555)
          ·
            refine ⟨583022721494994353691833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 388681814329996235794555 583022721494994353691833)
            ·
              refine ⟨437267041121245765268875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 583022721494994353691833 437267041121245765268875)
              ·
                refine ⟨655900561681868647903313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 437267041121245765268875 655900561681868647903313)
                ·
                  refine ⟨491925421261401485927485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 655900561681868647903313 491925421261401485927485)
                  ·
                    refine ⟨184472032973025557222807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 491925421261401485927485 184472032973025557222807)
                    ·
                      rfl

theorem cell22_538887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 2, 1, 2, 3].length) (baseStart_538887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_538887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_538887 prefixEnd_538887 := by exact prefixLift 538887
  have htrace : WordTrace (prefixWord ++ tailWord_538887) baseStart_538887 baseEnd_538887 := by
    simpa [prefixWord, tailWord_538887, baseEnd_538887] using wordTrace_append hprefix tailTrace_538887
  have hstable : (prefixWord ++ tailWord_538887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538887).length < 2 ^ (prefixWord ++ tailWord_538887).sum := by decide
  have hdescent : baseEnd_538887 < baseStart_538887 := by decide
  rcases family_descends (prefixWord ++ tailWord_538887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538892 : List Nat := [2, 2, 1, 2, 2, 2, 2, 1, 1, 7]
def baseStart_538892 : Nat := 118140960795 + 538892 * 2 ^ 59
def prefixEnd_538892 : Nat := 4983230072969 + 3 ^ 40 * 538892 * 2
def baseEnd_538892 : Nat := 184473744575207210847791

theorem tailTrace_538892 : CollatzResearch.WordTrace tailWord_538892 prefixEnd_538892 184473744575207210847791 := by
  unfold tailWord_538892
  simp only [CollatzResearch.WordTrace]
  refine ⟨9827502981846897135697465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13103337309129196180929953 9827502981846897135697465)
  ·
    refine ⟨7370627236385172851773099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9827502981846897135697465 7370627236385172851773099)
    ·
      refine ⟨11055940854577759277659649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7370627236385172851773099 11055940854577759277659649)
      ·
        refine ⟨8291955640933319458244737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11055940854577759277659649 8291955640933319458244737)
        ·
          refine ⟨6218966730699989593683553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8291955640933319458244737 6218966730699989593683553)
          ·
            refine ⟨4664225048024992195262665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6218966730699989593683553 4664225048024992195262665)
            ·
              refine ⟨3498168786018744146446999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4664225048024992195262665 3498168786018744146446999)
              ·
                refine ⟨5247253179028116219670499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3498168786018744146446999 5247253179028116219670499)
                ·
                  refine ⟨7870879768542174329505749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5247253179028116219670499 7870879768542174329505749)
                  ·
                    refine ⟨184473744575207210847791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7870879768542174329505749 184473744575207210847791)
                    ·
                      rfl

theorem cell22_538892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 1, 1, 7].length) (baseStart_538892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_538892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_538892 prefixEnd_538892 := by exact prefixLift 538892
  have htrace : WordTrace (prefixWord ++ tailWord_538892) baseStart_538892 baseEnd_538892 := by
    simpa [prefixWord, tailWord_538892, baseEnd_538892] using wordTrace_append hprefix tailTrace_538892
  have hstable : (prefixWord ++ tailWord_538892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538892).length < 2 ^ (prefixWord ++ tailWord_538892).sum := by decide
  have hdescent : baseEnd_538892 < baseStart_538892 := by decide
  rcases family_descends (prefixWord ++ tailWord_538892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538894 : List Nat := [4, 1, 1, 2, 1, 2, 3, 3, 5]
def baseStart_538894 : Nat := 118140960795 + 538894 * 2 ^ 59
def prefixEnd_538894 : Nat := 4983230072969 + 3 ^ 40 * 538894 * 2
def baseEnd_538894 : Nat := 61491476405359957432595

theorem tailTrace_538894 : CollatzResearch.WordTrace tailWord_538894 prefixEnd_538894 61491476405359957432595 := by
  unfold tailWord_538894
  simp only [CollatzResearch.WordTrace]
  refine ⟨2456884863710818576620967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13103385939791032408645157 2456884863710818576620967)
  ·
    refine ⟨3685327295566227864931451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2456884863710818576620967 3685327295566227864931451)
    ·
      refine ⟨5527990943349341797397177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3685327295566227864931451 5527990943349341797397177)
      ·
        refine ⟨4145993207512006348047883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5527990943349341797397177 4145993207512006348047883)
        ·
          refine ⟨6218989811268009522071825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4145993207512006348047883 6218989811268009522071825)
          ·
            refine ⟨4664242358451007141553869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6218989811268009522071825 4664242358451007141553869)
            ·
              refine ⟨1749090884419127678082701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4664242358451007141553869 1749090884419127678082701)
              ·
                refine ⟨655909081657172879281013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1749090884419127678082701 655909081657172879281013)
                ·
                  refine ⟨61491476405359957432595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 655909081657172879281013 61491476405359957432595)
                  ·
                    rfl

theorem cell22_538894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 3, 5].length) (baseStart_538894 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_538894 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_538894 prefixEnd_538894 := by exact prefixLift 538894
  have htrace : WordTrace (prefixWord ++ tailWord_538894) baseStart_538894 baseEnd_538894 := by
    simpa [prefixWord, tailWord_538894, baseEnd_538894] using wordTrace_append hprefix tailTrace_538894
  have hstable : (prefixWord ++ tailWord_538894).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538894).length < 2 ^ (prefixWord ++ tailWord_538894).sum := by decide
  have hdescent : baseEnd_538894 < baseStart_538894 := by decide
  rcases family_descends (prefixWord ++ tailWord_538894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538924 : List Nat := [2, 2, 1, 1, 1, 3, 2, 5, 1, 4]
def baseStart_538924 : Nat := 118140960795 + 538924 * 2 ^ 59
def prefixEnd_538924 : Nat := 4983230072969 + 3 ^ 40 * 538924 * 2
def baseEnd_538924 : Nat := 184484698829169794047693

theorem tailTrace_538924 : CollatzResearch.WordTrace tailWord_538924 prefixEnd_538924 184484698829169794047693 := by
  unfold tailWord_538924
  simp only [CollatzResearch.WordTrace]
  refine ⟨9828086549788931868279913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13104115399718575824373217 9828086549788931868279913)
  ·
    refine ⟨7371064912341698901209935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9828086549788931868279913 7371064912341698901209935)
    ·
      refine ⟨11056597368512548351814903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7371064912341698901209935 11056597368512548351814903)
      ·
        refine ⟨16584896052768822527722355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11056597368512548351814903 16584896052768822527722355)
        ·
          refine ⟨24877344079153233791583533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16584896052768822527722355 24877344079153233791583533)
          ·
            refine ⟨9329004029682462671843825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24877344079153233791583533 9329004029682462671843825)
            ·
              refine ⟨6996753022261847003882869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9329004029682462671843825 6996753022261847003882869)
              ·
                refine ⟨655945595837048156614019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6996753022261847003882869 655945595837048156614019)
                ·
                  refine ⟨983918393755572234921029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 655945595837048156614019 983918393755572234921029)
                  ·
                    refine ⟨184484698829169794047693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 983918393755572234921029 184484698829169794047693)
                    ·
                      rfl

theorem cell22_538924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 4].length) (baseStart_538924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_538924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_538924 prefixEnd_538924 := by exact prefixLift 538924
  have htrace : WordTrace (prefixWord ++ tailWord_538924) baseStart_538924 baseEnd_538924 := by
    simpa [prefixWord, tailWord_538924, baseEnd_538924] using wordTrace_append hprefix tailTrace_538924
  have hstable : (prefixWord ++ tailWord_538924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538924).length < 2 ^ (prefixWord ++ tailWord_538924).sum := by decide
  have hdescent : baseEnd_538924 < baseStart_538924 := by decide
  rcases family_descends (prefixWord ++ tailWord_538924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538932 : List Nat := [2, 5, 1, 1, 1, 4, 2, 2, 1, 3]
def baseStart_538932 : Nat := 118140960795 + 538932 * 2 ^ 59
def prefixEnd_538932 : Nat := 4983230072969 + 3 ^ 40 * 538932 * 2
def baseEnd_538932 : Nat := 184487437392660439847669

theorem tailTrace_538932 : CollatzResearch.WordTrace tailWord_538932 prefixEnd_538932 184487437392660439847669 := by
  unfold tailWord_538932
  simp only [CollatzResearch.WordTrace]
  refine ⟨9828232441774440551425525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13104309922365920735234033 9828232441774440551425525)
  ·
    refine ⟨921396791416353801696143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9828232441774440551425525 921396791416353801696143)
    ·
      refine ⟨1382095187124530702544215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 921396791416353801696143 1382095187124530702544215)
      ·
        refine ⟨2073142780686796053816323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1382095187124530702544215 2073142780686796053816323)
        ·
          refine ⟨3109714171030194080724485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2073142780686796053816323 3109714171030194080724485)
          ·
            refine ⟨583071407068161390135841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3109714171030194080724485 583071407068161390135841)
            ·
              refine ⟨437303555301121042601881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 583071407068161390135841 437303555301121042601881)
              ·
                refine ⟨327977666475840781951411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 437303555301121042601881 327977666475840781951411)
                ·
                  refine ⟨491966499713761172927117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 327977666475840781951411 491966499713761172927117)
                  ·
                    refine ⟨184487437392660439847669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 491966499713761172927117 184487437392660439847669)
                    ·
                      rfl

theorem cell22_538932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 2, 2, 1, 3].length) (baseStart_538932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_538932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_538932 prefixEnd_538932 := by exact prefixLift 538932
  have htrace : WordTrace (prefixWord ++ tailWord_538932) baseStart_538932 baseEnd_538932 := by
    simpa [prefixWord, tailWord_538932, baseEnd_538932] using wordTrace_append hprefix tailTrace_538932
  have hstable : (prefixWord ++ tailWord_538932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538932).length < 2 ^ (prefixWord ++ tailWord_538932).sum := by decide
  have hdescent : baseEnd_538932 < baseStart_538932 := by decide
  rcases family_descends (prefixWord ++ tailWord_538932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538954 : List Nat := [3, 1, 2, 1, 1, 1, 1, 1, 8, 3]
def baseStart_538954 : Nat := 118140960795 + 538954 * 2 ^ 59
def prefixEnd_538954 : Nat := 4983230072969 + 3 ^ 40 * 538954 * 2
def baseEnd_538954 : Nat := 184494968442259715797601

theorem tailTrace_538954 : CollatzResearch.WordTrace tailWord_538954 prefixEnd_538954 184494968442259715797601 := by
  unfold tailWord_538954
  simp only [CollatzResearch.WordTrace]
  refine ⟨4914316822367294715037979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13104844859646119240101277 4914316822367294715037979)
  ·
    refine ⟨7371475233550942072556969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4914316822367294715037979 7371475233550942072556969)
    ·
      refine ⟨5528606425163206554417727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7371475233550942072556969 5528606425163206554417727)
      ·
        refine ⟨8292909637744809831626591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5528606425163206554417727 8292909637744809831626591)
        ·
          refine ⟨12439364456617214747439887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8292909637744809831626591 12439364456617214747439887)
          ·
            refine ⟨18659046684925822121159831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12439364456617214747439887 18659046684925822121159831)
            ·
              refine ⟨27988570027388733181739747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18659046684925822121159831 27988570027388733181739747)
              ·
                refine ⟨41982855041083099772609621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27988570027388733181739747 41982855041083099772609621)
                ·
                  refine ⟨491986582512692575460269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 41982855041083099772609621 491986582512692575460269)
                  ·
                    refine ⟨184494968442259715797601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 491986582512692575460269 184494968442259715797601)
                    ·
                      rfl

theorem cell22_538954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 8, 3].length) (baseStart_538954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_538954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_538954 prefixEnd_538954 := by exact prefixLift 538954
  have htrace : WordTrace (prefixWord ++ tailWord_538954) baseStart_538954 baseEnd_538954 := by
    simpa [prefixWord, tailWord_538954, baseEnd_538954] using wordTrace_append hprefix tailTrace_538954
  have hstable : (prefixWord ++ tailWord_538954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538954).length < 2 ^ (prefixWord ++ tailWord_538954).sum := by decide
  have hdescent : baseEnd_538954 < baseStart_538954 := by decide
  rcases family_descends (prefixWord ++ tailWord_538954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538984 : List Nat := [2, 1, 4, 2, 2, 2, 9]
def baseStart_538984 : Nat := 118140960795 + 538984 * 2 ^ 59
def prefixEnd_538984 : Nat := 4983230072969 + 3 ^ 40 * 538984 * 2
def baseEnd_538984 : Nat := 6833527335383319909167

theorem tailTrace_538984 : CollatzResearch.WordTrace tailWord_538984 prefixEnd_538984 6833527335383319909167 := by
  unfold tailWord_538984
  simp only [CollatzResearch.WordTrace]
  refine ⟨9829180739680246991872003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13105574319573662655829337 9829180739680246991872003)
  ·
    refine ⟨14743771109520370487808005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9829180739680246991872003 14743771109520370487808005)
    ·
      refine ⟨2764457083035069466464001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14743771109520370487808005 2764457083035069466464001)
      ·
        refine ⟨2073342812276302099848001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2764457083035069466464001 2073342812276302099848001)
        ·
          refine ⟨1555007109207226574886001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2073342812276302099848001 1555007109207226574886001)
          ·
            refine ⟨1166255331905419931164501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1555007109207226574886001 1166255331905419931164501)
            ·
              refine ⟨6833527335383319909167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1166255331905419931164501 6833527335383319909167)
              ·
                rfl

theorem cell22_538984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 9].length) (baseStart_538984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_538984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_538984 prefixEnd_538984 := by exact prefixLift 538984
  have htrace : WordTrace (prefixWord ++ tailWord_538984) baseStart_538984 baseEnd_538984 := by
    simpa [prefixWord, tailWord_538984, baseEnd_538984] using wordTrace_append hprefix tailTrace_538984
  have hstable : (prefixWord ++ tailWord_538984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538984).length < 2 ^ (prefixWord ++ tailWord_538984).sum := by decide
  have hdescent : baseEnd_538984 < baseStart_538984 := by decide
  rcases family_descends (prefixWord ++ tailWord_538984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_539016 : List Nat := [2, 1, 3, 3, 1, 1, 1, 4, 3, 3]
def baseStart_539016 : Nat := 118140960795 + 539016 * 2 ^ 59
def prefixEnd_539016 : Nat := 4983230072969 + 3 ^ 40 * 539016 * 2
def baseEnd_539016 : Nat := 184516192309312220747411

theorem tailTrace_539016 : CollatzResearch.WordTrace tailWord_539016 prefixEnd_539016 184516192309312220747411 := by
  unfold tailWord_539016
  simp only [CollatzResearch.WordTrace]
  refine ⟨9829764307622281724454451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13106352410163042299272601 9829764307622281724454451)
  ·
    refine ⟨14744646461433422586681677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9829764307622281724454451 14744646461433422586681677)
    ·
      refine ⟨5529242423037533470005629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14744646461433422586681677 5529242423037533470005629)
      ·
        refine ⟨2073465908639075051252111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5529242423037533470005629 2073465908639075051252111)
        ·
          refine ⟨3110198862958612576878167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2073465908639075051252111 3110198862958612576878167)
          ·
            refine ⟨4665298294437918865317251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3110198862958612576878167 4665298294437918865317251)
            ·
              refine ⟨6997947441656878297975877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4665298294437918865317251 6997947441656878297975877)
              ·
                refine ⟨1312115145310664680870477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6997947441656878297975877 1312115145310664680870477)
                ·
                  refine ⟨492043179491499255326429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1312115145310664680870477 492043179491499255326429)
                  ·
                    refine ⟨184516192309312220747411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 492043179491499255326429 184516192309312220747411)
                    ·
                      rfl

theorem cell22_539016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 4, 3, 3].length) (baseStart_539016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_539016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_539016 prefixEnd_539016 := by exact prefixLift 539016
  have htrace : WordTrace (prefixWord ++ tailWord_539016) baseStart_539016 baseEnd_539016 := by
    simpa [prefixWord, tailWord_539016, baseEnd_539016] using wordTrace_append hprefix tailTrace_539016
  have hstable : (prefixWord ++ tailWord_539016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_539016).length < 2 ^ (prefixWord ++ tailWord_539016).sum := by decide
  have hdescent : baseEnd_539016 < baseStart_539016 := by decide
  rcases family_descends (prefixWord ++ tailWord_539016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_539044 : List Nat := [2, 3, 1, 2, 1, 1, 2, 1, 4, 5]
def baseStart_539044 : Nat := 118140960795 + 539044 * 2 ^ 59
def prefixEnd_539044 : Nat := 4983230072969 + 3 ^ 40 * 539044 * 2
def baseEnd_539044 : Nat := 184525777281529481047325

theorem tailTrace_539044 : CollatzResearch.WordTrace tailWord_539044 prefixEnd_539044 184525777281529481047325 := by
  unfold tailWord_539044
  simp only [CollatzResearch.WordTrace]
  refine ⟨9830274929571562115464093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13107033239428749487285457 9830274929571562115464093)
  ·
    refine ⟨3686353098589335793299035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9830274929571562115464093 3686353098589335793299035)
    ·
      refine ⟨5529529647884003689948553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3686353098589335793299035 5529529647884003689948553)
      ·
        refine ⟨4147147235913002767461415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5529529647884003689948553 4147147235913002767461415)
        ·
          refine ⟨6220720853869504151192123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4147147235913002767461415 6220720853869504151192123)
          ·
            refine ⟨9331081280804256226788185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6220720853869504151192123 9331081280804256226788185)
            ·
              refine ⟨6998310960603192170091139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9331081280804256226788185 6998310960603192170091139)
              ·
                refine ⟨10497466440904788255136709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6998310960603192170091139 10497466440904788255136709)
                ·
                  refine ⟨1968274957669647797838133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10497466440904788255136709 1968274957669647797838133)
                  ·
                    refine ⟨184525777281529481047325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1968274957669647797838133 184525777281529481047325)
                    ·
                      rfl

theorem cell22_539044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 1, 4, 5].length) (baseStart_539044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_539044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_539044 prefixEnd_539044 := by exact prefixLift 539044
  have htrace : WordTrace (prefixWord ++ tailWord_539044) baseStart_539044 baseEnd_539044 := by
    simpa [prefixWord, tailWord_539044, baseEnd_539044] using wordTrace_append hprefix tailTrace_539044
  have hstable : (prefixWord ++ tailWord_539044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_539044).length < 2 ^ (prefixWord ++ tailWord_539044).sum := by decide
  have hdescent : baseEnd_539044 < baseStart_539044 := by decide
  rcases family_descends (prefixWord ++ tailWord_539044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_539063 : List Nat := [1, 1, 3, 1, 3, 5, 2, 1, 5]
def baseStart_539063 : Nat := 118140960795 + 539063 * 2 ^ 59
def prefixEnd_539063 : Nat := 4983230072969 + 3 ^ 40 * 539063 * 2
def baseEnd_539063 : Nat := 61510760456606588274089

theorem tailTrace_539063 : CollatzResearch.WordTrace tailWord_539063 prefixEnd_539063 61510760456606588274089 := by
  unfold tailWord_539063
  simp only [CollatzResearch.WordTrace]
  refine ⟨19661242846074290475869843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13107495230716193650579895 19661242846074290475869843)
  ·
    refine ⟨29491864269111435713804765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19661242846074290475869843 29491864269111435713804765)
    ·
      refine ⟨11059449100916788392676787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29491864269111435713804765 11059449100916788392676787)
      ·
        refine ⟨16589173651375182589015181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11059449100916788392676787 16589173651375182589015181)
        ·
          refine ⟨6220940119265693470880693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16589173651375182589015181 6220940119265693470880693)
          ·
            refine ⟨583213136181158762895065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6220940119265693470880693 583213136181158762895065)
            ·
              refine ⟨437409852135869072171299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 583213136181158762895065 437409852135869072171299)
              ·
                refine ⟨656114778203803608256949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 437409852135869072171299 656114778203803608256949)
                ·
                  refine ⟨61510760456606588274089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 656114778203803608256949 61510760456606588274089)
                  ·
                    rfl

theorem cell22_539063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 2, 1, 5].length) (baseStart_539063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_539063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_539063 prefixEnd_539063 := by exact prefixLift 539063
  have htrace : WordTrace (prefixWord ++ tailWord_539063) baseStart_539063 baseEnd_539063 := by
    simpa [prefixWord, tailWord_539063, baseEnd_539063] using wordTrace_append hprefix tailTrace_539063
  have hstable : (prefixWord ++ tailWord_539063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_539063).length < 2 ^ (prefixWord ++ tailWord_539063).sum := by decide
  have hdescent : baseEnd_539063 < baseStart_539063 := by decide
  rcases family_descends (prefixWord ++ tailWord_539063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_539241 : List Nat := [1, 2, 1, 1, 1, 4, 1, 5, 1, 5]
def baseStart_539241 : Nat := 118140960795 + 539241 * 2 ^ 59
def prefixEnd_539241 : Nat := 4983230072969 + 3 ^ 40 * 539241 * 2
def baseEnd_539241 : Nat := 184593214407486633871721

theorem tailTrace_539241 : CollatzResearch.WordTrace tailWord_539241 prefixEnd_539241 184593214407486633871721 := by
  unfold tailWord_539241
  simp only [CollatzResearch.WordTrace]
  refine ⟨19667735039429426875849577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13111823359619617917233051 19667735039429426875849577)
  ·
    refine ⟨14750801279572070156887183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19667735039429426875849577 14750801279572070156887183)
    ·
      refine ⟨22126201919358105235330775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14750801279572070156887183 22126201919358105235330775)
      ·
        refine ⟨33189302879037157852996163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22126201919358105235330775 33189302879037157852996163)
        ·
          refine ⟨49783954318555736779494245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33189302879037157852996163 49783954318555736779494245)
          ·
            refine ⟨9334491434729200646155171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49783954318555736779494245 9334491434729200646155171)
            ·
              refine ⟨14001737152093800969232757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9334491434729200646155171 14001737152093800969232757)
              ·
                refine ⟨1312662858008793840865571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14001737152093800969232757 1312662858008793840865571)
                ·
                  refine ⟨1968994287013190761298357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1312662858008793840865571 1968994287013190761298357)
                  ·
                    refine ⟨184593214407486633871721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1968994287013190761298357 184593214407486633871721)
                    ·
                      rfl

theorem cell22_539241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 5, 1, 5].length) (baseStart_539241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_539241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_539241 prefixEnd_539241 := by exact prefixLift 539241
  have htrace : WordTrace (prefixWord ++ tailWord_539241) baseStart_539241 baseEnd_539241 := by
    simpa [prefixWord, tailWord_539241, baseEnd_539241] using wordTrace_append hprefix tailTrace_539241
  have hstable : (prefixWord ++ tailWord_539241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_539241).length < 2 ^ (prefixWord ++ tailWord_539241).sum := by decide
  have hdescent : baseEnd_539241 < baseStart_539241 := by decide
  rcases family_descends (prefixWord ++ tailWord_539241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_539245 : List Nat := [1, 5, 1, 1, 3, 1, 3, 2, 1, 4]
def baseStart_539245 : Nat := 118140960795 + 539245 * 2 ^ 59
def prefixEnd_539245 : Nat := 4983230072969 + 3 ^ 40 * 539245 * 2
def baseEnd_539245 : Nat := 184594583689231956771709

theorem tailTrace_539245 : CollatzResearch.WordTrace tailWord_539245 prefixEnd_539245 184594583689231956771709 := by
  unfold tailWord_539245
  simp only [CollatzResearch.WordTrace]
  refine ⟨19667880931414935558995189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13111920620943290372663459 19667880931414935558995189)
  ·
    refine ⟨1843863837320150208655799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19667880931414935558995189 1843863837320150208655799)
    ·
      refine ⟨2765795755980225312983699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1843863837320150208655799 2765795755980225312983699)
      ·
        refine ⟨4148693633970337969475549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2765795755980225312983699 4148693633970337969475549)
        ·
          refine ⟨1555760112738876738553331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4148693633970337969475549 1555760112738876738553331)
          ·
            refine ⟨2333640169108315107829997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1555760112738876738553331 2333640169108315107829997)
            ·
              refine ⟨875115063415618165436249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2333640169108315107829997 875115063415618165436249)
              ·
                refine ⟨656336297561713624077187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 875115063415618165436249 656336297561713624077187)
                ·
                  refine ⟨984504446342570436115781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 656336297561713624077187 984504446342570436115781)
                  ·
                    refine ⟨184594583689231956771709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 984504446342570436115781 184594583689231956771709)
                    ·
                      rfl

theorem cell22_539245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 3, 2, 1, 4].length) (baseStart_539245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_539245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_539245 prefixEnd_539245 := by exact prefixLift 539245
  have htrace : WordTrace (prefixWord ++ tailWord_539245) baseStart_539245 baseEnd_539245 := by
    simpa [prefixWord, tailWord_539245, baseEnd_539245] using wordTrace_append hprefix tailTrace_539245
  have hstable : (prefixWord ++ tailWord_539245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_539245).length < 2 ^ (prefixWord ++ tailWord_539245).sum := by decide
  have hdescent : baseEnd_539245 < baseStart_539245 := by decide
  rcases family_descends (prefixWord ++ tailWord_539245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_539256 : List Nat := [2, 1, 2, 1, 1, 1, 2, 2, 6, 4]
def baseStart_539256 : Nat := 118140960795 + 539256 * 2 ^ 59
def prefixEnd_539256 : Nat := 4983230072969 + 3 ^ 40 * 539256 * 2
def baseEnd_539256 : Nat := 184598349214031594746675

theorem tailTrace_539256 : CollatzResearch.WordTrace tailWord_539256 prefixEnd_539256 184598349214031594746675 := by
  unfold tailWord_539256
  simp only [CollatzResearch.WordTrace]
  refine ⟨9834141067187542218822811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13112188089583389625097081 9834141067187542218822811)
  ·
    refine ⟨14751211600781313328234217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9834141067187542218822811 14751211600781313328234217)
    ·
      refine ⟨11063408700585984996175663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14751211600781313328234217 11063408700585984996175663)
      ·
        refine ⟨16595113050878977494263495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11063408700585984996175663 16595113050878977494263495)
        ·
          refine ⟨24892669576318466241395243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16595113050878977494263495 24892669576318466241395243)
          ·
            refine ⟨37339004364477699362092865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24892669576318466241395243 37339004364477699362092865)
            ·
              refine ⟨28004253273358274521569649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37339004364477699362092865 28004253273358274521569649)
              ·
                refine ⟨21003189955018705891177237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28004253273358274521569649 21003189955018705891177237)
                ·
                  refine ⟨984524529141501838648933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 21003189955018705891177237 984524529141501838648933)
                  ·
                    refine ⟨184598349214031594746675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 984524529141501838648933 184598349214031594746675)
                    ·
                      rfl

theorem cell22_539256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 6, 4].length) (baseStart_539256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_539256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_539256 prefixEnd_539256 := by exact prefixLift 539256
  have htrace : WordTrace (prefixWord ++ tailWord_539256) baseStart_539256 baseEnd_539256 := by
    simpa [prefixWord, tailWord_539256, baseEnd_539256] using wordTrace_append hprefix tailTrace_539256
  have hstable : (prefixWord ++ tailWord_539256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_539256).length < 2 ^ (prefixWord ++ tailWord_539256).sum := by decide
  have hdescent : baseEnd_539256 < baseStart_539256 := by decide
  rcases family_descends (prefixWord ++ tailWord_539256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_539301 : List Nat := [1, 3, 1, 2, 1, 2, 1, 1, 4, 6]
def baseStart_539301 : Nat := 118140960795 + 539301 * 2 ^ 59
def prefixEnd_539301 : Nat := 4983230072969 + 3 ^ 40 * 539301 * 2
def baseEnd_539301 : Nat := 184613753633666477371537

theorem tailTrace_539301 : CollatzResearch.WordTrace tailWord_539301 prefixEnd_539301 184613753633666477371537 := by
  unfold tailWord_539301
  simp only [CollatzResearch.WordTrace]
  refine ⟨19669923419212057123033757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13113282279474704748689171 19669923419212057123033757)
  ·
    refine ⟨7376221282204521421137659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19669923419212057123033757 7376221282204521421137659)
    ·
      refine ⟨11064331923306782131706489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7376221282204521421137659 11064331923306782131706489)
      ·
        refine ⟨8298248942480086598779867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11064331923306782131706489 8298248942480086598779867)
        ·
          refine ⟨12447373413720129898169801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8298248942480086598779867 12447373413720129898169801)
          ·
            refine ⟨9335530060290097423627351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12447373413720129898169801 9335530060290097423627351)
            ·
              refine ⟨14003295090435146135441027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9335530060290097423627351 14003295090435146135441027)
              ·
                refine ⟨21004942635652719203161541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14003295090435146135441027 21004942635652719203161541)
                ·
                  refine ⟨3938426744184884850592789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21004942635652719203161541 3938426744184884850592789)
                  ·
                    refine ⟨184613753633666477371537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3938426744184884850592789 184613753633666477371537)
                    ·
                      rfl

theorem cell22_539301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 4, 6].length) (baseStart_539301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_539301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_539301 prefixEnd_539301 := by exact prefixLift 539301
  have htrace : WordTrace (prefixWord ++ tailWord_539301) baseStart_539301 baseEnd_539301 := by
    simpa [prefixWord, tailWord_539301, baseEnd_539301] using wordTrace_append hprefix tailTrace_539301
  have hstable : (prefixWord ++ tailWord_539301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_539301).length < 2 ^ (prefixWord ++ tailWord_539301).sum := by decide
  have hdescent : baseEnd_539301 < baseStart_539301 := by decide
  rcases family_descends (prefixWord ++ tailWord_539301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_539423 : List Nat := [1, 1, 2, 4, 2, 2, 2, 8]
def baseStart_539423 : Nat := 118140960795 + 539423 * 2 ^ 59
def prefixEnd_539423 : Nat := 4983230072969 + 3 ^ 40 * 539423 * 2
def baseEnd_539423 : Nat := 20517279636322091757907

theorem tailTrace_539423 : CollatzResearch.WordTrace tailWord_539423 prefixEnd_539423 20517279636322091757907 := by
  unfold tailWord_539423
  simp only [CollatzResearch.WordTrace]
  refine ⟨19674373124770071958974923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13116248749846714639316615 19674373124770071958974923)
  ·
    refine ⟨29511559687155107938462385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19674373124770071958974923 29511559687155107938462385)
    ·
      refine ⟨22133669765366330953846789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29511559687155107938462385 22133669765366330953846789)
      ·
        refine ⟨4150063081006187053846273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22133669765366330953846789 4150063081006187053846273)
        ·
          refine ⟨3112547310754640290384705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4150063081006187053846273 3112547310754640290384705)
          ·
            refine ⟨2334410483065980217788529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3112547310754640290384705 2334410483065980217788529)
            ·
              refine ⟨1750807862299485163341397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2334410483065980217788529 1750807862299485163341397)
              ·
                refine ⟨20517279636322091757907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1750807862299485163341397 20517279636322091757907)
                ·
                  rfl

theorem cell22_539423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 8].length) (baseStart_539423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_539423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_539423 prefixEnd_539423 := by exact prefixLift 539423
  have htrace : WordTrace (prefixWord ++ tailWord_539423) baseStart_539423 baseEnd_539423 := by
    simpa [prefixWord, tailWord_539423, baseEnd_539423] using wordTrace_append hprefix tailTrace_539423
  have hstable : (prefixWord ++ tailWord_539423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_539423).length < 2 ^ (prefixWord ++ tailWord_539423).sum := by decide
  have hdescent : baseEnd_539423 < baseStart_539423 := by decide
  rcases family_descends (prefixWord ++ tailWord_539423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_539425 : List Nat := [1, 2, 3, 2, 1, 2, 4, 1, 2, 4]
def baseStart_539425 : Nat := 118140960795 + 539425 * 2 ^ 59
def prefixEnd_539425 : Nat := 4983230072969 + 3 ^ 40 * 539425 * 2
def baseEnd_539425 : Nat := 184656201367771487271157

theorem tailTrace_539425 : CollatzResearch.WordTrace tailWord_539425 prefixEnd_539425 184656201367771487271157 := by
  unfold tailWord_539425
  simp only [CollatzResearch.WordTrace]
  refine ⟨19674446070762826300547729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13116297380508550867031819 19674446070762826300547729)
  ·
    refine ⟨14755834553072119725410797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19674446070762826300547729 14755834553072119725410797)
    ·
      refine ⟨5533437957402044897029049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14755834553072119725410797 5533437957402044897029049)
      ·
        refine ⟨4150078468051533672771787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5533437957402044897029049 4150078468051533672771787)
        ·
          refine ⟨6225117702077300509157681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4150078468051533672771787 6225117702077300509157681)
          ·
            refine ⟨4668838276557975381868261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6225117702077300509157681 4668838276557975381868261)
            ·
              refine ⟨875407176854620384100299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4668838276557975381868261 875407176854620384100299)
              ·
                refine ⟨1313110765281930576150449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 875407176854620384100299 1313110765281930576150449)
                ·
                  refine ⟨984833073961447932112837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1313110765281930576150449 984833073961447932112837)
                  ·
                    refine ⟨184656201367771487271157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 984833073961447932112837 184656201367771487271157)
                    ·
                      rfl

theorem cell22_539425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 4, 1, 2, 4].length) (baseStart_539425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_539425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_539425 prefixEnd_539425 := by exact prefixLift 539425
  have htrace : WordTrace (prefixWord ++ tailWord_539425) baseStart_539425 baseEnd_539425 := by
    simpa [prefixWord, tailWord_539425, baseEnd_539425] using wordTrace_append hprefix tailTrace_539425
  have hstable : (prefixWord ++ tailWord_539425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_539425).length < 2 ^ (prefixWord ++ tailWord_539425).sum := by decide
  have hdescent : baseEnd_539425 < baseStart_539425 := by decide
  rcases family_descends (prefixWord ++ tailWord_539425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_539502 : List Nat := [4, 1, 2, 3, 2, 1, 1, 1, 7]
def baseStart_539502 : Nat := 118140960795 + 539502 * 2 ^ 59
def prefixEnd_539502 : Nat := 4983230072969 + 3 ^ 40 * 539502 * 2
def baseEnd_539502 : Nat := 61560853347122984365307

theorem tailTrace_539502 : CollatzResearch.WordTrace tailWord_539502 prefixEnd_539502 61560853347122984365307 := by
  unfold tailWord_539502
  simp only [CollatzResearch.WordTrace]
  refine ⟨2459656811435483556387595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13118169660989245634067173 2459656811435483556387595)
  ·
    refine ⟨3689485217153225334581393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2459656811435483556387595 3689485217153225334581393)
    ·
      refine ⟨2767113912864919000936045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3689485217153225334581393 2767113912864919000936045)
      ·
        refine ⟨1037667717324344625351017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2767113912864919000936045 1037667717324344625351017)
        ·
          refine ⟨778250787993258469013263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1037667717324344625351017 778250787993258469013263)
          ·
            refine ⟨1167376181989887703519895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 778250787993258469013263 1167376181989887703519895)
            ·
              refine ⟨1751064272984831555279843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1167376181989887703519895 1751064272984831555279843)
              ·
                refine ⟨2626596409477247332919765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1751064272984831555279843 2626596409477247332919765)
                ·
                  refine ⟨61560853347122984365307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2626596409477247332919765 61560853347122984365307)
                  ·
                    rfl

theorem cell22_539502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 1, 7].length) (baseStart_539502 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_539502 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_539502 prefixEnd_539502 := by exact prefixLift 539502
  have htrace : WordTrace (prefixWord ++ tailWord_539502) baseStart_539502 baseEnd_539502 := by
    simpa [prefixWord, tailWord_539502, baseEnd_539502] using wordTrace_append hprefix tailTrace_539502
  have hstable : (prefixWord ++ tailWord_539502).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_539502).length < 2 ^ (prefixWord ++ tailWord_539502).sum := by decide
  have hdescent : baseEnd_539502 < baseStart_539502 := by decide
  rcases family_descends (prefixWord ++ tailWord_539502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_539682 : List Nat := [3, 3, 1, 1, 1, 3, 1, 3, 6]
def baseStart_539682 : Nat := 118140960795 + 539682 * 2 ^ 59
def prefixEnd_539682 : Nat := 4983230072969 + 3 ^ 40 * 539682 * 2
def baseEnd_539682 : Nat := 61581392573302827865123

theorem tailTrace_539682 : CollatzResearch.WordTrace tailWord_539682 prefixEnd_539682 61581392573302827865123 := by
  unfold tailWord_539682
  simp only [CollatzResearch.WordTrace]
  refine ⟨4920954907707939798163325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13122546420554506128435533 4920954907707939798163325)
  ·
    refine ⟨1845358090390477424311247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4920954907707939798163325 1845358090390477424311247)
    ·
      refine ⟨2768037135585716136466871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1845358090390477424311247 2768037135585716136466871)
      ·
        refine ⟨4152055703378574204700307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2768037135585716136466871 4152055703378574204700307)
        ·
          refine ⟨6228083555067861307050461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4152055703378574204700307 6228083555067861307050461)
          ·
            refine ⟨2335531333150447990143923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6228083555067861307050461 2335531333150447990143923)
            ·
              refine ⟨3503296999725671985215885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2335531333150447990143923 3503296999725671985215885)
              ·
                refine ⟨1313736374897126994455957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3503296999725671985215885 1313736374897126994455957)
                ·
                  refine ⟨61581392573302827865123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1313736374897126994455957 61581392573302827865123)
                  ·
                    rfl

theorem cell22_539682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 3, 6].length) (baseStart_539682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_539682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_539682 prefixEnd_539682 := by exact prefixLift 539682
  have htrace : WordTrace (prefixWord ++ tailWord_539682) baseStart_539682 baseEnd_539682 := by
    simpa [prefixWord, tailWord_539682, baseEnd_539682] using wordTrace_append hprefix tailTrace_539682
  have hstable : (prefixWord ++ tailWord_539682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_539682).length < 2 ^ (prefixWord ++ tailWord_539682).sum := by decide
  have hdescent : baseEnd_539682 < baseStart_539682 := by decide
  rcases family_descends (prefixWord ++ tailWord_539682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_539712 : List Nat := [2, 1, 1, 2, 2, 3, 2, 3, 2, 4]
def baseStart_539712 : Nat := 118140960795 + 539712 * 2 ^ 59
def prefixEnd_539712 : Nat := 4983230072969 + 3 ^ 40 * 539712 * 2
def baseEnd_539712 : Nat := 184754447332998405345277

theorem tailTrace_539712 : CollatzResearch.WordTrace tailWord_539712 prefixEnd_539712 184754447332998405345277 := by
  unfold tailWord_539712
  simp only [CollatzResearch.WordTrace]
  refine ⟨9842456910361537158122695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13123275880482049544163593 9842456910361537158122695)
  ·
    refine ⟨14763685365542305737184043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9842456910361537158122695 14763685365542305737184043)
    ·
      refine ⟨22145528048313458605776065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14763685365542305737184043 22145528048313458605776065)
      ·
        refine ⟨16609146036235093954332049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22145528048313458605776065 16609146036235093954332049)
        ·
          refine ⟨12456859527176320465749037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16609146036235093954332049 12456859527176320465749037)
          ·
            refine ⟨4671322322691120174655889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12456859527176320465749037 4671322322691120174655889)
            ·
              refine ⟨3503491742018340130991917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4671322322691120174655889 3503491742018340130991917)
              ·
                refine ⟨1313809403256877549121969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3503491742018340130991917 1313809403256877549121969)
                ·
                  refine ⟨985357052442658161841477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1313809403256877549121969 985357052442658161841477)
                  ·
                    refine ⟨184754447332998405345277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 985357052442658161841477 184754447332998405345277)
                    ·
                      rfl

theorem cell22_539712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 3, 2, 4].length) (baseStart_539712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_539712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_539712 prefixEnd_539712 := by exact prefixLift 539712
  have htrace : WordTrace (prefixWord ++ tailWord_539712) baseStart_539712 baseEnd_539712 := by
    simpa [prefixWord, tailWord_539712, baseEnd_539712] using wordTrace_append hprefix tailTrace_539712
  have hstable : (prefixWord ++ tailWord_539712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_539712).length < 2 ^ (prefixWord ++ tailWord_539712).sum := by decide
  have hdescent : baseEnd_539712 < baseStart_539712 := by decide
  rcases family_descends (prefixWord ++ tailWord_539712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_539804 : List Nat := [2, 2, 3, 2, 1, 3, 1, 1, 2, 5]
def baseStart_539804 : Nat := 118140960795 + 539804 * 2 ^ 59
def prefixEnd_539804 : Nat := 4983230072969 + 3 ^ 40 * 539804 * 2
def baseEnd_539804 : Nat := 184785940813140832044995

theorem tailTrace_539804 : CollatzResearch.WordTrace tailWord_539804 prefixEnd_539804 184785940813140832044995 := by
  unfold tailWord_539804
  simp only [CollatzResearch.WordTrace]
  refine ⟨9844134668194887014297233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13125512890926516019062977 9844134668194887014297233)
  ·
    refine ⟨7383101001146165260722925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9844134668194887014297233 7383101001146165260722925)
    ·
      refine ⟨2768662875429811972771097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7383101001146165260722925 2768662875429811972771097)
      ·
        refine ⟨2076497156572358979578323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2768662875429811972771097 2076497156572358979578323)
        ·
          refine ⟨3114745734858538469367485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2076497156572358979578323 3114745734858538469367485)
          ·
            refine ⟨1168029650571951926012807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3114745734858538469367485 1168029650571951926012807)
            ·
              refine ⟨1752044475857927889019211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1168029650571951926012807 1752044475857927889019211)
              ·
                refine ⟨2628066713786891833528817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1752044475857927889019211 2628066713786891833528817)
                ·
                  refine ⟨1971050035340168875146613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2628066713786891833528817 1971050035340168875146613)
                  ·
                    refine ⟨184785940813140832044995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1971050035340168875146613 184785940813140832044995)
                    ·
                      rfl

theorem cell22_539804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 1, 2, 5].length) (baseStart_539804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_539804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_539804 prefixEnd_539804 := by exact prefixLift 539804
  have htrace : WordTrace (prefixWord ++ tailWord_539804) baseStart_539804 baseEnd_539804 := by
    simpa [prefixWord, tailWord_539804, baseEnd_539804] using wordTrace_append hprefix tailTrace_539804
  have hstable : (prefixWord ++ tailWord_539804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_539804).length < 2 ^ (prefixWord ++ tailWord_539804).sum := by decide
  have hdescent : baseEnd_539804 < baseStart_539804 := by decide
  rcases family_descends (prefixWord ++ tailWord_539804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_539806 : List Nat := [4, 3, 1, 1, 2, 1, 2, 3, 5]
def baseStart_539806 : Nat := 118140960795 + 539806 * 2 ^ 59
def prefixEnd_539806 : Nat := 4983230072969 + 3 ^ 40 * 539806 * 2
def baseEnd_539806 : Nat := 61595541818004497831663

theorem tailTrace_539806 : CollatzResearch.WordTrace tailWord_539806 prefixEnd_539806 61595541818004497831663 := by
  unfold tailWord_539806
  simp only [CollatzResearch.WordTrace]
  refine ⟨2461042785297816046270909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13125561521588352246778181 2461042785297816046270909)
  ·
    refine ⟨922891044486681017351591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2461042785297816046270909 922891044486681017351591)
    ·
      refine ⟨1384336566730021526027387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 922891044486681017351591 1384336566730021526027387)
      ·
        refine ⟨2076504850095032289041081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1384336566730021526027387 2076504850095032289041081)
        ·
          refine ⟨1557378637571274216780811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2076504850095032289041081 1557378637571274216780811)
          ·
            refine ⟨2336067956356911325171217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1557378637571274216780811 2336067956356911325171217)
            ·
              refine ⟨1752050967267683493878413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2336067956356911325171217 1752050967267683493878413)
              ·
                refine ⟨657019112725381310204405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1752050967267683493878413 657019112725381310204405)
                ·
                  refine ⟨61595541818004497831663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 657019112725381310204405 61595541818004497831663)
                  ·
                    rfl

theorem cell22_539806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 3, 5].length) (baseStart_539806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_539806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_539806 prefixEnd_539806 := by exact prefixLift 539806
  have htrace : WordTrace (prefixWord ++ tailWord_539806) baseStart_539806 baseEnd_539806 := by
    simpa [prefixWord, tailWord_539806, baseEnd_539806] using wordTrace_append hprefix tailTrace_539806
  have hstable : (prefixWord ++ tailWord_539806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_539806).length < 2 ^ (prefixWord ++ tailWord_539806).sum := by decide
  have hdescent : baseEnd_539806 < baseStart_539806 := by decide
  rcases family_descends (prefixWord ++ tailWord_539806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_539832 : List Nat := [2, 1, 2, 1, 2, 1, 2, 3, 3, 5]
def baseStart_539832 : Nat := 118140960795 + 539832 * 2 ^ 59
def prefixEnd_539832 : Nat := 4983230072969 + 3 ^ 40 * 539832 * 2
def baseEnd_539832 : Nat := 184795525785358092344909

theorem tailTrace_539832 : CollatzResearch.WordTrace tailWord_539832 prefixEnd_539832 184795525785358092344909 := by
  unfold tailWord_539832
  simp only [CollatzResearch.WordTrace]
  refine ⟨9844645290144167405306875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13126193720192223207075833 9844645290144167405306875)
  ·
    refine ⟨14766967935216251107960313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9844645290144167405306875 14766967935216251107960313)
    ·
      refine ⟨11075225951412188330970235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14766967935216251107960313 11075225951412188330970235)
      ·
        refine ⟨16612838927118282496455353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11075225951412188330970235 16612838927118282496455353)
        ·
          refine ⟨12459629195338711872341515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16612838927118282496455353 12459629195338711872341515)
          ·
            refine ⟨18689443793008067808512273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12459629195338711872341515 18689443793008067808512273)
            ·
              refine ⟨14017082844756050856384205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18689443793008067808512273 14017082844756050856384205)
              ·
                refine ⟨5256406066783519071144077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14017082844756050856384205 5256406066783519071144077)
                ·
                  refine ⟨1971152275043819651679029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5256406066783519071144077 1971152275043819651679029)
                  ·
                    refine ⟨184795525785358092344909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1971152275043819651679029 184795525785358092344909)
                    ·
                      rfl

theorem cell22_539832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 3, 3, 5].length) (baseStart_539832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_539832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_539832 prefixEnd_539832 := by exact prefixLift 539832
  have htrace : WordTrace (prefixWord ++ tailWord_539832) baseStart_539832 baseEnd_539832 := by
    simpa [prefixWord, tailWord_539832, baseEnd_539832] using wordTrace_append hprefix tailTrace_539832
  have hstable : (prefixWord ++ tailWord_539832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_539832).length < 2 ^ (prefixWord ++ tailWord_539832).sum := by decide
  have hdescent : baseEnd_539832 < baseStart_539832 := by decide
  rcases family_descends (prefixWord ++ tailWord_539832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_539836 : List Nat := [2, 2, 2, 3, 2, 2, 1, 3, 1, 4]
def baseStart_539836 : Nat := 118140960795 + 539836 * 2 ^ 59
def prefixEnd_539836 : Nat := 4983230072969 + 3 ^ 40 * 539836 * 2
def baseEnd_539836 : Nat := 184796895067103415244897

theorem tailTrace_539836 : CollatzResearch.WordTrace tailWord_539836 prefixEnd_539836 184796895067103415244897 := by
  unfold tailWord_539836
  simp only [CollatzResearch.WordTrace]
  refine ⟨9844718236136921746879681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13126290981515895662506241 9844718236136921746879681)
  ·
    refine ⟨7383538677102691310159761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9844718236136921746879681 7383538677102691310159761)
    ·
      refine ⟨5537654007827018482619821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7383538677102691310159761 5537654007827018482619821)
      ·
        refine ⟨2076620252935131930982433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5537654007827018482619821 2076620252935131930982433)
        ·
          refine ⟨1557465189701348948236825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2076620252935131930982433 1557465189701348948236825)
          ·
            refine ⟨1168098892276011711177619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1557465189701348948236825 1168098892276011711177619)
            ·
              refine ⟨1752148338414017566766429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1168098892276011711177619 1752148338414017566766429)
              ·
                refine ⟨657055626905256587537411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1752148338414017566766429 657055626905256587537411)
                ·
                  refine ⟨985583440357884881306117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 657055626905256587537411 985583440357884881306117)
                  ·
                    refine ⟨184796895067103415244897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 985583440357884881306117 184796895067103415244897)
                    ·
                      rfl

theorem cell22_539836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 3, 1, 4].length) (baseStart_539836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_539836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_539836 prefixEnd_539836 := by exact prefixLift 539836
  have htrace : WordTrace (prefixWord ++ tailWord_539836) baseStart_539836 baseEnd_539836 := by
    simpa [prefixWord, tailWord_539836, baseEnd_539836] using wordTrace_append hprefix tailTrace_539836
  have hstable : (prefixWord ++ tailWord_539836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_539836).length < 2 ^ (prefixWord ++ tailWord_539836).sum := by decide
  have hdescent : baseEnd_539836 < baseStart_539836 := by decide
  rcases family_descends (prefixWord ++ tailWord_539836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_539956 : List Nat := [2, 5, 1, 1, 1, 1, 2, 2, 2, 5]
def baseStart_539956 : Nat := 118140960795 + 539956 * 2 ^ 59
def prefixEnd_539956 : Nat := 4983230072969 + 3 ^ 40 * 539956 * 2
def baseEnd_539956 : Nat := 184837973519463102244529

theorem tailTrace_539956 : CollatzResearch.WordTrace tailWord_539956 prefixEnd_539956 184837973519463102244529 := by
  unfold tailWord_539956
  simp only [CollatzResearch.WordTrace]
  refine ⟨9846906615919551994063861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13129208821226069325418481 9846906615919551994063861)
  ·
    refine ⟨923147495242457999443487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9846906615919551994063861 923147495242457999443487)
    ·
      refine ⟨1384721242863686999165231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 923147495242457999443487 1384721242863686999165231)
      ·
        refine ⟨2077081864295530498747847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1384721242863686999165231 2077081864295530498747847)
        ·
          refine ⟨3115622796443295748121771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2077081864295530498747847 3115622796443295748121771)
          ·
            refine ⟨4673434194664943622182657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3115622796443295748121771 4673434194664943622182657)
            ·
              refine ⟨3505075645998707716636993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4673434194664943622182657 3505075645998707716636993)
              ·
                refine ⟨2628806734499030787477745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3505075645998707716636993 2628806734499030787477745)
                ·
                  refine ⟨1971605050874273090608309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2628806734499030787477745 1971605050874273090608309)
                  ·
                    refine ⟨184837973519463102244529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1971605050874273090608309 184837973519463102244529)
                    ·
                      rfl

theorem cell22_539956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_539956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_539956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_539956 prefixEnd_539956 := by exact prefixLift 539956
  have htrace : WordTrace (prefixWord ++ tailWord_539956) baseStart_539956 baseEnd_539956 := by
    simpa [prefixWord, tailWord_539956, baseEnd_539956] using wordTrace_append hprefix tailTrace_539956
  have hstable : (prefixWord ++ tailWord_539956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_539956).length < 2 ^ (prefixWord ++ tailWord_539956).sum := by decide
  have hdescent : baseEnd_539956 < baseStart_539956 := by decide
  rcases family_descends (prefixWord ++ tailWord_539956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_540003 : List Nat := [1, 1, 1, 5, 2, 3, 2, 3, 4]
def baseStart_540003 : Nat := 118140960795 + 540003 * 2 ^ 59
def prefixEnd_540003 : Nat := 4983230072969 + 3 ^ 40 * 540003 * 2
def baseEnd_540003 : Nat := 61618020859990215439795

theorem tailTrace_540003 : CollatzResearch.WordTrace tailWord_540003 prefixEnd_540003 61618020859990215439795 := by
  unfold tailWord_540003
  simp only [CollatzResearch.WordTrace]
  refine ⟨19695527462668831015088663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13130351641779220676725775 19695527462668831015088663)
  ·
    refine ⟨29543291194003246522632995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19695527462668831015088663 29543291194003246522632995)
    ·
      refine ⟨44314936791004869783949493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29543291194003246522632995 44314936791004869783949493)
      ·
        refine ⟨4154525324156706542245265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 44314936791004869783949493 4154525324156706542245265)
        ·
          refine ⟨3115893993117529906683949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4154525324156706542245265 3115893993117529906683949)
          ·
            refine ⟨1168460247419073715006481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3115893993117529906683949 1168460247419073715006481)
            ·
              refine ⟨876345185564305286254861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1168460247419073715006481 876345185564305286254861)
              ·
                refine ⟨328629444586614482345573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 876345185564305286254861 328629444586614482345573)
                ·
                  refine ⟨61618020859990215439795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 328629444586614482345573 61618020859990215439795)
                  ·
                    rfl

theorem cell22_540003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 2, 3, 4].length) (baseStart_540003 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_540003 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_540003 prefixEnd_540003 := by exact prefixLift 540003
  have htrace : WordTrace (prefixWord ++ tailWord_540003) baseStart_540003 baseEnd_540003 := by
    simpa [prefixWord, tailWord_540003, baseEnd_540003] using wordTrace_append hprefix tailTrace_540003
  have hstable : (prefixWord ++ tailWord_540003).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_540003).length < 2 ^ (prefixWord ++ tailWord_540003).sum := by decide
  have hdescent : baseEnd_540003 < baseStart_540003 := by decide
  rcases family_descends (prefixWord ++ tailWord_540003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_540035 : List Nat := [1, 1, 1, 3, 5, 2, 3, 1, 2, 3]
def baseStart_540035 : Nat := 118140960795 + 540035 * 2 ^ 59
def prefixEnd_540035 : Nat := 4983230072969 + 3 ^ 40 * 540035 * 2
def baseEnd_540035 : Nat := 184865016833933229519287

theorem tailTrace_540035 : CollatzResearch.WordTrace tailWord_540035 prefixEnd_540035 184865016833933229519287 := by
  unfold tailWord_540035
  simp only [CollatzResearch.WordTrace]
  refine ⟨19696694598552900480253559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13131129732368600320169039 19696694598552900480253559)
  ·
    refine ⟨29545041897829350720380339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19696694598552900480253559 29545041897829350720380339)
    ·
      refine ⟨44317562846744026080570509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29545041897829350720380339 44317562846744026080570509)
      ·
        refine ⟨16619086067529009780213941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44317562846744026080570509 16619086067529009780213941)
        ·
          refine ⟨1558039318830844666895057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16619086067529009780213941 1558039318830844666895057)
          ·
            refine ⟨1168529489123133500171293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1558039318830844666895057 1168529489123133500171293)
            ·
              refine ⟨438198558421175062564235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1168529489123133500171293 438198558421175062564235)
              ·
                refine ⟨657297837631762593846353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 438198558421175062564235 657297837631762593846353)
                ·
                  refine ⟨492973378223821945384765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 657297837631762593846353 492973378223821945384765)
                  ·
                    refine ⟨184865016833933229519287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 492973378223821945384765 184865016833933229519287)
                    ·
                      rfl

theorem cell22_540035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 3, 1, 2, 3].length) (baseStart_540035 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_540035 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_540035 prefixEnd_540035 := by exact prefixLift 540035
  have htrace : WordTrace (prefixWord ++ tailWord_540035) baseStart_540035 baseEnd_540035 := by
    simpa [prefixWord, tailWord_540035, baseEnd_540035] using wordTrace_append hprefix tailTrace_540035
  have hstable : (prefixWord ++ tailWord_540035).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_540035).length < 2 ^ (prefixWord ++ tailWord_540035).sum := by decide
  have hdescent : baseEnd_540035 < baseStart_540035 := by decide
  rcases family_descends (prefixWord ++ tailWord_540035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_540136 : List Nat := [2, 1, 4, 1, 1, 2, 1, 2, 3, 5]
def baseStart_540136 : Nat := 118140960795 + 540136 * 2 ^ 59
def prefixEnd_540136 : Nat := 4983230072969 + 3 ^ 40 * 540136 * 2
def baseEnd_540136 : Nat := 184899591198002632743977

theorem tailTrace_540136 : CollatzResearch.WordTrace tailWord_540136 prefixEnd_540136 184899591198002632743977 := by
  unfold tailWord_540136
  simp only [CollatzResearch.WordTrace]
  refine ⟨9850189185593497364840131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13133585580791329819786841 9850189185593497364840131)
  ·
    refine ⟨14775283778390246047260197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9850189185593497364840131 14775283778390246047260197)
    ·
      refine ⟨2770365708448171133861287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14775283778390246047260197 2770365708448171133861287)
      ·
        refine ⟨4155548562672256700791931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2770365708448171133861287 4155548562672256700791931)
        ·
          refine ⟨6233322844008385051187897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4155548562672256700791931 6233322844008385051187897)
          ·
            refine ⟨4674992133006288788390923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6233322844008385051187897 4674992133006288788390923)
            ·
              refine ⟨7012488199509433182586385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4674992133006288788390923 7012488199509433182586385)
              ·
                refine ⟨5259366149632074886939789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7012488199509433182586385 5259366149632074886939789)
                ·
                  refine ⟨1972262306112028082602421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5259366149632074886939789 1972262306112028082602421)
                  ·
                    refine ⟨184899591198002632743977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1972262306112028082602421 184899591198002632743977)
                    ·
                      rfl

theorem cell22_540136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 2, 3, 5].length) (baseStart_540136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_540136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_540136 prefixEnd_540136 := by exact prefixLift 540136
  have htrace : WordTrace (prefixWord ++ tailWord_540136) baseStart_540136 baseEnd_540136 := by
    simpa [prefixWord, tailWord_540136, baseEnd_540136] using wordTrace_append hprefix tailTrace_540136
  have hstable : (prefixWord ++ tailWord_540136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_540136).length < 2 ^ (prefixWord ++ tailWord_540136).sum := by decide
  have hdescent : baseEnd_540136 < baseStart_540136 := by decide
  rcases family_descends (prefixWord ++ tailWord_540136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_540168 : List Nat := [2, 1, 3, 2, 1, 1, 5, 1, 2, 4]
def baseStart_540168 : Nat := 118140960795 + 540168 * 2 ^ 59
def prefixEnd_540168 : Nat := 4983230072969 + 3 ^ 40 * 540168 * 2
def baseEnd_540168 : Nat := 184910545451965215943879

theorem tailTrace_540168 : CollatzResearch.WordTrace tailWord_540168 prefixEnd_540168 184910545451965215943879 := by
  unfold tailWord_540168
  simp only [CollatzResearch.WordTrace]
  refine ⟨9850772753535532097422579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13134363671380709463230105 9850772753535532097422579)
  ·
    refine ⟨14776159130303298146133869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9850772753535532097422579 14776159130303298146133869)
    ·
      refine ⟨5541059673863736804800201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14776159130303298146133869 5541059673863736804800201)
      ·
        refine ⟨4155794755397802603600151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5541059673863736804800201 4155794755397802603600151)
        ·
          refine ⟨6233692133096703905400227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4155794755397802603600151 6233692133096703905400227)
          ·
            refine ⟨9350538199645055858100341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6233692133096703905400227 9350538199645055858100341)
            ·
              refine ⟨876612956216723986696907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9350538199645055858100341 876612956216723986696907)
              ·
                refine ⟨1314919434325085980045361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 876612956216723986696907 1314919434325085980045361)
                ·
                  refine ⟨986189575743814485034021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1314919434325085980045361 986189575743814485034021)
                  ·
                    refine ⟨184910545451965215943879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 986189575743814485034021 184910545451965215943879)
                    ·
                      rfl

theorem cell22_540168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 5, 1, 2, 4].length) (baseStart_540168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_540168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_540168 prefixEnd_540168 := by exact prefixLift 540168
  have htrace : WordTrace (prefixWord ++ tailWord_540168) baseStart_540168 baseEnd_540168 := by
    simpa [prefixWord, tailWord_540168, baseEnd_540168] using wordTrace_append hprefix tailTrace_540168
  have hstable : (prefixWord ++ tailWord_540168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_540168).length < 2 ^ (prefixWord ++ tailWord_540168).sum := by decide
  have hdescent : baseEnd_540168 < baseStart_540168 := by decide
  rcases family_descends (prefixWord ++ tailWord_540168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_540174 : List Nat := [4, 1, 1, 2, 5, 1, 2, 1, 1, 4]
def baseStart_540174 : Nat := 118140960795 + 540174 * 2 ^ 59
def prefixEnd_540174 : Nat := 4983230072969 + 3 ^ 40 * 540174 * 2
def baseEnd_540174 : Nat := 184912599374583200293861

theorem tailTrace_540174 : CollatzResearch.WordTrace tailWord_540174 prefixEnd_540174 184912599374583200293861 := by
  unfold tailWord_540174
  simp only [CollatzResearch.WordTrace]
  refine ⟨2462720543131165902445447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13134509563366218146375717 2462720543131165902445447)
  ·
    refine ⟨3694080814696748853668171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2462720543131165902445447 3694080814696748853668171)
    ·
      refine ⟨5541121222045123280502257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3694080814696748853668171 5541121222045123280502257)
      ·
        refine ⟨4155840916533842460376693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5541121222045123280502257 4155840916533842460376693)
        ·
          refine ⟨389610085925047730660315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4155840916533842460376693 389610085925047730660315)
          ·
            refine ⟨584415128887571595990473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 389610085925047730660315 584415128887571595990473)
            ·
              refine ⟨438311346665678696992855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 584415128887571595990473 438311346665678696992855)
              ·
                refine ⟨657467019998518045489283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 438311346665678696992855 657467019998518045489283)
                ·
                  refine ⟨986200529997777068233925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 657467019998518045489283 986200529997777068233925)
                  ·
                    refine ⟨184912599374583200293861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 986200529997777068233925 184912599374583200293861)
                    ·
                      rfl

theorem cell22_540174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 2, 1, 1, 4].length) (baseStart_540174 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_540174 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_540174 prefixEnd_540174 := by exact prefixLift 540174
  have htrace : WordTrace (prefixWord ++ tailWord_540174) baseStart_540174 baseEnd_540174 := by
    simpa [prefixWord, tailWord_540174, baseEnd_540174] using wordTrace_append hprefix tailTrace_540174
  have hstable : (prefixWord ++ tailWord_540174).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_540174).length < 2 ^ (prefixWord ++ tailWord_540174).sum := by decide
  have hdescent : baseEnd_540174 < baseStart_540174 := by decide
  rcases family_descends (prefixWord ++ tailWord_540174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_540288 : List Nat := [2, 1, 1, 2, 1, 4, 3, 2, 1, 5]
def baseStart_540288 : Nat := 118140960795 + 540288 * 2 ^ 59
def prefixEnd_540288 : Nat := 4983230072969 + 3 ^ 40 * 540288 * 2
def baseEnd_540288 : Nat := 184951623904324902943511

theorem tailTrace_540288 : CollatzResearch.WordTrace tailWord_540288 prefixEnd_540288 184951623904324902943511 := by
  unfold tailWord_540288
  simp only [CollatzResearch.WordTrace]
  refine ⟨9852961133318162344606759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13137281511090883126142345 9852961133318162344606759)
  ·
    refine ⟨14779441699977243516910139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9852961133318162344606759 14779441699977243516910139)
    ·
      refine ⟨22169162549965865275365209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14779441699977243516910139 22169162549965865275365209)
      ·
        refine ⟨16626871912474398956523907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22169162549965865275365209 16626871912474398956523907)
        ·
          refine ⟨24940307868711598434785861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16626871912474398956523907 24940307868711598434785861)
          ·
            refine ⟨4676307725383424706522349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24940307868711598434785861 4676307725383424706522349)
            ·
              refine ⟨1753615397018784264945881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4676307725383424706522349 1753615397018784264945881)
              ·
                refine ⟨1315211547764088198709411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1753615397018784264945881 1315211547764088198709411)
                ·
                  refine ⟨1972817321646132298064117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1315211547764088198709411 1972817321646132298064117)
                  ·
                    refine ⟨184951623904324902943511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1972817321646132298064117 184951623904324902943511)
                    ·
                      rfl

theorem cell22_540288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 2, 1, 5].length) (baseStart_540288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_540288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_540288 prefixEnd_540288 := by exact prefixLift 540288
  have htrace : WordTrace (prefixWord ++ tailWord_540288) baseStart_540288 baseEnd_540288 := by
    simpa [prefixWord, tailWord_540288, baseEnd_540288] using wordTrace_append hprefix tailTrace_540288
  have hstable : (prefixWord ++ tailWord_540288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_540288).length < 2 ^ (prefixWord ++ tailWord_540288).sum := by decide
  have hdescent : baseEnd_540288 < baseStart_540288 := by decide
  rcases family_descends (prefixWord ++ tailWord_540288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_540301 : List Nat := [1, 21]
def baseStart_540301 : Nat := 118140960795 + 540301 * 2 ^ 59
def prefixEnd_540301 : Nat := 4983230072969 + 3 ^ 40 * 540301 * 2
def baseEnd_540301 : Nat := 28190226195701448311

theorem tailTrace_540301 : CollatzResearch.WordTrace tailWord_540301 prefixEnd_540301 28190226195701448311 := by
  unfold tailWord_540301
  simp only [CollatzResearch.WordTrace]
  refine ⟨19706396415589227909436757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13137597610392818606291171 19706396415589227909436757)
  ·
    refine ⟨28190226195701448311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 21 19706396415589227909436757 28190226195701448311)
    ·
      rfl

theorem cell22_540301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 21].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 21].length) (baseStart_540301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_540301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_540301 prefixEnd_540301 := by exact prefixLift 540301
  have htrace : WordTrace (prefixWord ++ tailWord_540301) baseStart_540301 baseEnd_540301 := by
    simpa [prefixWord, tailWord_540301, baseEnd_540301] using wordTrace_append hprefix tailTrace_540301
  have hstable : (prefixWord ++ tailWord_540301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_540301).length < 2 ^ (prefixWord ++ tailWord_540301).sum := by decide
  have hdescent : baseEnd_540301 < baseStart_540301 := by decide
  rcases family_descends (prefixWord ++ tailWord_540301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_540474 : List Nat := [3, 1, 1, 1, 5, 2, 2, 2, 2, 3]
def baseStart_540474 : Nat := 118140960795 + 540474 * 2 ^ 59
def prefixEnd_540474 : Nat := 4983230072969 + 3 ^ 40 * 540474 * 2
def baseEnd_540474 : Nat := 185015295505482417792941

theorem tailTrace_540474 : CollatzResearch.WordTrace tailWord_540474 prefixEnd_540474 185015295505482417792941 := by
  unfold tailWord_540474
  simp only [CollatzResearch.WordTrace]
  refine ⟨4928176560990619613871119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13141804162641652303656317 4928176560990619613871119)
  ·
    refine ⟨7392264841485929420806679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4928176560990619613871119 7392264841485929420806679)
    ·
      refine ⟨11088397262228894131210019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7392264841485929420806679 11088397262228894131210019)
      ·
        refine ⟨16632595893343341196815029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11088397262228894131210019 16632595893343341196815029)
        ·
          refine ⟨1559305865000938237201409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16632595893343341196815029 1559305865000938237201409)
          ·
            refine ⟨1169479398750703677901057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1559305865000938237201409 1169479398750703677901057)
            ·
              refine ⟨877109549063027758425793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1169479398750703677901057 877109549063027758425793)
              ·
                refine ⟨657832161797270818819345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 877109549063027758425793 657832161797270818819345)
                ·
                  refine ⟨493374121347953114114509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 657832161797270818819345 493374121347953114114509)
                  ·
                    refine ⟨185015295505482417792941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 493374121347953114114509 185015295505482417792941)
                    ·
                      rfl

theorem cell22_540474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 2, 2, 2, 3].length) (baseStart_540474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_540474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_540474 prefixEnd_540474 := by exact prefixLift 540474
  have htrace : WordTrace (prefixWord ++ tailWord_540474) baseStart_540474 baseEnd_540474 := by
    simpa [prefixWord, tailWord_540474, baseEnd_540474] using wordTrace_append hprefix tailTrace_540474
  have hstable : (prefixWord ++ tailWord_540474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_540474).length < 2 ^ (prefixWord ++ tailWord_540474).sum := by decide
  have hdescent : baseEnd_540474 < baseStart_540474 := by decide
  rcases family_descends (prefixWord ++ tailWord_540474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_540667 : List Nat := [1, 1, 1, 1, 1, 3, 6, 3, 5]
def baseStart_540667 : Nat := 118140960795 + 540667 * 2 ^ 59
def prefixEnd_540667 : Nat := 4983230072969 + 3 ^ 40 * 540667 * 2
def baseEnd_540667 : Nat := 61693787783231415905783

theorem tailTrace_540667 : CollatzResearch.WordTrace tailWord_540667 prefixEnd_540667 61693787783231415905783 := by
  unfold tailWord_540667
  simp only [CollatzResearch.WordTrace]
  refine ⟨19719745532263272417260255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13146497021508848278173503 19719745532263272417260255)
  ·
    refine ⟨29579618298394908625890383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19719745532263272417260255 29579618298394908625890383)
    ·
      refine ⟨44369427447592362938835575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29579618298394908625890383 44369427447592362938835575)
      ·
        refine ⟨66554141171388544408253363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44369427447592362938835575 66554141171388544408253363)
        ·
          refine ⟨99831211757082816612380045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66554141171388544408253363 99831211757082816612380045)
          ·
            refine ⟨37436704408906056229642517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 99831211757082816612380045 37436704408906056229642517)
            ·
              refine ⟨1754845519167471385764493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 37436704408906056229642517 1754845519167471385764493)
              ·
                refine ⟨658067069687801769661685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1754845519167471385764493 658067069687801769661685)
                ·
                  refine ⟨61693787783231415905783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 658067069687801769661685 61693787783231415905783)
                  ·
                    rfl

theorem cell22_540667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 3, 5].length) (baseStart_540667 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_540667 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_540667 prefixEnd_540667 := by exact prefixLift 540667
  have htrace : WordTrace (prefixWord ++ tailWord_540667) baseStart_540667 baseEnd_540667 := by
    simpa [prefixWord, tailWord_540667, baseEnd_540667] using wordTrace_append hprefix tailTrace_540667
  have hstable : (prefixWord ++ tailWord_540667).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_540667).length < 2 ^ (prefixWord ++ tailWord_540667).sum := by decide
  have hdescent : baseEnd_540667 < baseStart_540667 := by decide
  rcases family_descends (prefixWord ++ tailWord_540667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_540701 : List Nat := [1, 4, 2, 2, 2, 3, 1, 2, 5]
def baseStart_540701 : Nat := 118140960795 + 540701 * 2 ^ 59
def prefixEnd_540701 : Nat := 4983230072969 + 3 ^ 40 * 540701 * 2
def baseEnd_540701 : Nat := 61697667414843164122415

theorem tailTrace_540701 : CollatzResearch.WordTrace tailWord_540701 prefixEnd_540701 61697667414843164122415 := by
  unfold tailWord_540701
  simp only [CollatzResearch.WordTrace]
  refine ⟨19720985614140096223997957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13147323742760064149331971 19720985614140096223997957)
  ·
    refine ⟨3697684802651268041999617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19720985614140096223997957 3697684802651268041999617)
    ·
      refine ⟨2773263601988451031499713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3697684802651268041999617 2773263601988451031499713)
      ·
        refine ⟨2079947701491338273624785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2773263601988451031499713 2079947701491338273624785)
        ·
          refine ⟨1559960776118503705218589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2079947701491338273624785 1559960776118503705218589)
          ·
            refine ⟨584985291044438889456971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1559960776118503705218589 584985291044438889456971)
            ·
              refine ⟨877477936566658334185457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 584985291044438889456971 877477936566658334185457)
              ·
                refine ⟨658108452424993750639093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 877477936566658334185457 658108452424993750639093)
                ·
                  refine ⟨61697667414843164122415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 658108452424993750639093 61697667414843164122415)
                  ·
                    rfl

theorem cell22_540701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 1, 2, 5].length) (baseStart_540701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_540701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_540701 prefixEnd_540701 := by exact prefixLift 540701
  have htrace : WordTrace (prefixWord ++ tailWord_540701) baseStart_540701 baseEnd_540701 := by
    simpa [prefixWord, tailWord_540701, baseEnd_540701] using wordTrace_append hprefix tailTrace_540701
  have hstable : (prefixWord ++ tailWord_540701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_540701).length < 2 ^ (prefixWord ++ tailWord_540701).sum := by decide
  have hdescent : baseEnd_540701 < baseStart_540701 := by decide
  rcases family_descends (prefixWord ++ tailWord_540701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_540757 : List Nat := [1, 3, 2, 2, 1, 3, 10]
def baseStart_540757 : Nat := 118140960795 + 540757 * 2 ^ 59
def prefixEnd_540757 : Nat := 4983230072969 + 3 ^ 40 * 540757 * 2
def baseEnd_540757 : Nat := 6856006377369037517299

theorem tailTrace_540757 : CollatzResearch.WordTrace tailWord_540757 prefixEnd_540757 6856006377369037517299 := by
  unfold tailWord_540757
  simp only [CollatzResearch.WordTrace]
  refine ⟨19723028101937217788036525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13148685401291478525357683 19723028101937217788036525)
  ·
    refine ⟨7396135538226456670513697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19723028101937217788036525 7396135538226456670513697)
    ·
      refine ⟨5547101653669842502885273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7396135538226456670513697 5547101653669842502885273)
      ·
        refine ⟨4160326240252381877163955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5547101653669842502885273 4160326240252381877163955)
        ·
          refine ⟨6240489360378572815745933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4160326240252381877163955 6240489360378572815745933)
          ·
            refine ⟨2340183510141964805904725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6240489360378572815745933 2340183510141964805904725)
            ·
              refine ⟨6856006377369037517299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 2340183510141964805904725 6856006377369037517299)
              ·
                rfl

theorem cell22_540757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 10].length) (baseStart_540757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_540757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_540757 prefixEnd_540757 := by exact prefixLift 540757
  have htrace : WordTrace (prefixWord ++ tailWord_540757) baseStart_540757 baseEnd_540757 := by
    simpa [prefixWord, tailWord_540757, baseEnd_540757] using wordTrace_append hprefix tailTrace_540757
  have hstable : (prefixWord ++ tailWord_540757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_540757).length < 2 ^ (prefixWord ++ tailWord_540757).sum := by decide
  have hdescent : baseEnd_540757 < baseStart_540757 := by decide
  rcases family_descends (prefixWord ++ tailWord_540757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_540778 : List Nat := [3, 1, 3, 2, 3, 1, 1, 3, 2, 3]
def baseStart_540778 : Nat := 118140960795 + 540778 * 2 ^ 59
def prefixEnd_540778 : Nat := 4983230072969 + 3 ^ 40 * 540778 * 2
def baseEnd_540778 : Nat := 185119360918126958192009

theorem tailTrace_540778 : CollatzResearch.WordTrace tailWord_540778 prefixEnd_540778 185119360918126958192009 := by
  unfold tailWord_540778
  simp only [CollatzResearch.WordTrace]
  refine ⟨4930948508715284593637747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13149196023240758916367325 4930948508715284593637747)
  ·
    refine ⟨7396422763072926890456621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4930948508715284593637747 7396422763072926890456621)
    ·
      refine ⟨2773658536152347583921233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7396422763072926890456621 2773658536152347583921233)
      ·
        refine ⟨2080243902114260687940925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2773658536152347583921233 2080243902114260687940925)
        ·
          refine ⟨780091463292847757977847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2080243902114260687940925 780091463292847757977847)
          ·
            refine ⟨1170137194939271636966771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 780091463292847757977847 1170137194939271636966771)
            ·
              refine ⟨1755205792408907455450157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1170137194939271636966771 1755205792408907455450157)
              ·
                refine ⟨658202172153340295793809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1755205792408907455450157 658202172153340295793809)
                ·
                  refine ⟨493651629115005221845357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 658202172153340295793809 493651629115005221845357)
                  ·
                    refine ⟨185119360918126958192009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 493651629115005221845357 185119360918126958192009)
                    ·
                      rfl

theorem cell22_540778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 3, 2, 3].length) (baseStart_540778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_540778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_540778 prefixEnd_540778 := by exact prefixLift 540778
  have htrace : WordTrace (prefixWord ++ tailWord_540778) baseStart_540778 baseEnd_540778 := by
    simpa [prefixWord, tailWord_540778, baseEnd_540778] using wordTrace_append hprefix tailTrace_540778
  have hstable : (prefixWord ++ tailWord_540778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_540778).length < 2 ^ (prefixWord ++ tailWord_540778).sum := by decide
  have hdescent : baseEnd_540778 < baseStart_540778 := by decide
  rcases family_descends (prefixWord ++ tailWord_540778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_540817 : List Nat := [1, 2, 2, 1, 1, 1, 1, 1, 5, 7]
def baseStart_540817 : Nat := 118140960795 + 540817 * 2 ^ 59
def prefixEnd_540817 : Nat := 4983230072969 + 3 ^ 40 * 540817 * 2
def baseEnd_540817 : Nat := 185132711415143856466889

theorem tailTrace_540817 : CollatzResearch.WordTrace tailWord_540817 prefixEnd_540817 185132711415143856466889 := by
  unfold tailWord_540817
  simp only [CollatzResearch.WordTrace]
  refine ⟨19725216481719848035220705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13150144321146565356813803 19725216481719848035220705)
  ·
    refine ⟨14793912361289886026415529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19725216481719848035220705 14793912361289886026415529)
    ·
      refine ⟨11095434270967414519811647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14793912361289886026415529 11095434270967414519811647)
      ·
        refine ⟨16643151406451121779717471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11095434270967414519811647 16643151406451121779717471)
        ·
          refine ⟨24964727109676682669576207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16643151406451121779717471 24964727109676682669576207)
          ·
            refine ⟨37447090664515024004364311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24964727109676682669576207 37447090664515024004364311)
            ·
              refine ⟨56170635996772536006546467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37447090664515024004364311 56170635996772536006546467)
              ·
                refine ⟨84255953995158804009819701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56170635996772536006546467 84255953995158804009819701)
                ·
                  refine ⟨7898995687046137875920597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 84255953995158804009819701 7898995687046137875920597)
                  ·
                    refine ⟨185132711415143856466889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7898995687046137875920597 185132711415143856466889)
                    ·
                      rfl

theorem cell22_540817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 7].length) (baseStart_540817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_540817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_540817 prefixEnd_540817 := by exact prefixLift 540817
  have htrace : WordTrace (prefixWord ++ tailWord_540817) baseStart_540817 baseEnd_540817 := by
    simpa [prefixWord, tailWord_540817, baseEnd_540817] using wordTrace_append hprefix tailTrace_540817
  have hstable : (prefixWord ++ tailWord_540817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_540817).length < 2 ^ (prefixWord ++ tailWord_540817).sum := by decide
  have hdescent : baseEnd_540817 < baseStart_540817 := by decide
  rcases family_descends (prefixWord ++ tailWord_540817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_540881 : List Nat := [1, 2, 2, 1, 2, 2, 4, 4, 4]
def baseStart_540881 : Nat := 118140960795 + 540881 * 2 ^ 59
def prefixEnd_540881 : Nat := 4983230072969 + 3 ^ 40 * 540881 * 2
def baseEnd_540881 : Nat := 61718206641023007622231

theorem tailTrace_540881 : CollatzResearch.WordTrace tailWord_540881 prefixEnd_540881 61718206641023007622231 := by
  unfold tailWord_540881
  simp only [CollatzResearch.WordTrace]
  refine ⟨19727550753487986965550497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13151700502325324643700331 19727550753487986965550497)
  ·
    refine ⟨14795663065115990224162873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19727550753487986965550497 14795663065115990224162873)
    ·
      refine ⟨11096747298836992668122155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14795663065115990224162873 11096747298836992668122155)
      ·
        refine ⟨16645120948255489002183233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11096747298836992668122155 16645120948255489002183233)
        ·
          refine ⟨12483840711191616751637425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16645120948255489002183233 12483840711191616751637425)
          ·
            refine ⟨9362880533393712563728069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12483840711191616751637425 9362880533393712563728069)
            ·
              refine ⟨1755540100011321105699013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9362880533393712563728069 1755540100011321105699013)
              ·
                refine ⟨329163768752122707318565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1755540100011321105699013 329163768752122707318565)
                ·
                  refine ⟨61718206641023007622231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 329163768752122707318565 61718206641023007622231)
                  ·
                    rfl

theorem cell22_540881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 4, 4].length) (baseStart_540881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_540881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_540881 prefixEnd_540881 := by exact prefixLift 540881
  have htrace : WordTrace (prefixWord ++ tailWord_540881) baseStart_540881 baseEnd_540881 := by
    simpa [prefixWord, tailWord_540881, baseEnd_540881] using wordTrace_append hprefix tailTrace_540881
  have hstable : (prefixWord ++ tailWord_540881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_540881).length < 2 ^ (prefixWord ++ tailWord_540881).sum := by decide
  have hdescent : baseEnd_540881 < baseStart_540881 := by decide
  rcases family_descends (prefixWord ++ tailWord_540881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_540939 : List Nat := [1, 1, 1, 1, 5, 2, 2, 1, 2, 6]
def baseStart_540939 : Nat := 118140960795 + 540939 * 2 ^ 59
def prefixEnd_540939 : Nat := 4983230072969 + 3 ^ 40 * 540939 * 2
def baseEnd_540939 : Nat := 185174474508376204916515

theorem tailTrace_540939 : CollatzResearch.WordTrace tailWord_540939 prefixEnd_540939 185174474508376204916515 := by
  unfold tailWord_540939
  simp only [CollatzResearch.WordTrace]
  refine ⟨19729666187277862871161871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13153110791518575247441247 19729666187277862871161871)
  ·
    refine ⟨29594499280916794306742807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19729666187277862871161871 29594499280916794306742807)
    ·
      refine ⟨44391748921375191460114211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29594499280916794306742807 44391748921375191460114211)
      ·
        refine ⟨66587623382062787190171317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44391748921375191460114211 66587623382062787190171317)
        ·
          refine ⟨6242589692068386299078561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 66587623382062787190171317 6242589692068386299078561)
          ·
            refine ⟨4681942269051289724308921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6242589692068386299078561 4681942269051289724308921)
            ·
              refine ⟨3511456701788467293231691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4681942269051289724308921 3511456701788467293231691)
              ·
                refine ⟨5267185052682700939847537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3511456701788467293231691 5267185052682700939847537)
                ·
                  refine ⟨3950388789512025704885653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5267185052682700939847537 3950388789512025704885653)
                  ·
                    refine ⟨185174474508376204916515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3950388789512025704885653 185174474508376204916515)
                    ·
                      rfl

theorem cell22_540939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 1, 2, 6].length) (baseStart_540939 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_540939 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_540939 prefixEnd_540939 := by exact prefixLift 540939
  have htrace : WordTrace (prefixWord ++ tailWord_540939) baseStart_540939 baseEnd_540939 := by
    simpa [prefixWord, tailWord_540939, baseEnd_540939] using wordTrace_append hprefix tailTrace_540939
  have hstable : (prefixWord ++ tailWord_540939).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_540939).length < 2 ^ (prefixWord ++ tailWord_540939).sum := by decide
  have hdescent : baseEnd_540939 < baseStart_540939 := by decide
  rcases family_descends (prefixWord ++ tailWord_540939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541033 : List Nat := [1, 2, 1, 1, 1, 3, 6, 3, 4]
def baseStart_541033 : Nat := 118140960795 + 541033 * 2 ^ 59
def prefixEnd_541033 : Nat := 4983230072969 + 3 ^ 40 * 541033 * 2
def baseEnd_541033 : Nat := 61735550876463764355409

theorem tailTrace_541033 : CollatzResearch.WordTrace tailWord_541033 prefixEnd_541033 61735550876463764355409 := by
  unfold tailWord_541033
  simp only [CollatzResearch.WordTrace]
  refine ⟨19733094648937316925083753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13155396432624877950055835 19733094648937316925083753)
  ·
    refine ⟨14799820986702987693812815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19733094648937316925083753 14799820986702987693812815)
    ·
      refine ⟨22199731480054481540719223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14799820986702987693812815 22199731480054481540719223)
      ·
        refine ⟨33299597220081722311078835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22199731480054481540719223 33299597220081722311078835)
        ·
          refine ⟨49949395830122583466618253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33299597220081722311078835 49949395830122583466618253)
          ·
            refine ⟨18731023436295968799981845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49949395830122583466618253 18731023436295968799981845)
            ·
              refine ⟨878016723576373537499149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 18731023436295968799981845 878016723576373537499149)
              ·
                refine ⟨329256271341140076562181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 878016723576373537499149 329256271341140076562181)
                ·
                  refine ⟨61735550876463764355409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 329256271341140076562181 61735550876463764355409)
                  ·
                    rfl

theorem cell22_541033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 6, 3, 4].length) (baseStart_541033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_541033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_541033 prefixEnd_541033 := by exact prefixLift 541033
  have htrace : WordTrace (prefixWord ++ tailWord_541033) baseStart_541033 baseEnd_541033 := by
    simpa [prefixWord, tailWord_541033, baseEnd_541033] using wordTrace_append hprefix tailTrace_541033
  have hstable : (prefixWord ++ tailWord_541033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541033).length < 2 ^ (prefixWord ++ tailWord_541033).sum := by decide
  have hdescent : baseEnd_541033 < baseStart_541033 := by decide
  rcases family_descends (prefixWord ++ tailWord_541033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541106 : List Nat := [3, 2, 1, 1, 1, 1, 3, 3, 7]
def baseStart_541106 : Nat := 118140960795 + 541106 * 2 ^ 59
def prefixEnd_541106 : Nat := 4983230072969 + 3 ^ 40 * 541106 * 2
def baseEnd_541106 : Nat := 61743880673747811997001

theorem tailTrace_541106 : CollatzResearch.WordTrace tailWord_541106 prefixEnd_541106 61743880673747811997001 := by
  unfold tailWord_541106
  simp only [CollatzResearch.WordTrace]
  refine ⟨4933939294418212598122793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13157171451781900261660781 4933939294418212598122793)
  ·
    refine ⟨3700454470813659448592095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4933939294418212598122793 3700454470813659448592095)
    ·
      refine ⟨5550681706220489172888143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3700454470813659448592095 5550681706220489172888143)
      ·
        refine ⟨8326022559330733759332215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5550681706220489172888143 8326022559330733759332215)
        ·
          refine ⟨12489033838996100638998323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8326022559330733759332215 12489033838996100638998323)
          ·
            refine ⟨18733550758494150958497485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12489033838996100638998323 18733550758494150958497485)
            ·
              refine ⟨7025081534435306609436557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18733550758494150958497485 7025081534435306609436557)
              ·
                refine ⟨2634405575413239978538709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7025081534435306609436557 2634405575413239978538709)
                ·
                  refine ⟨61743880673747811997001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2634405575413239978538709 61743880673747811997001)
                  ·
                    rfl

theorem cell22_541106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 3, 7].length) (baseStart_541106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_541106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_541106 prefixEnd_541106 := by exact prefixLift 541106
  have htrace : WordTrace (prefixWord ++ tailWord_541106) baseStart_541106 baseEnd_541106 := by
    simpa [prefixWord, tailWord_541106, baseEnd_541106] using wordTrace_append hprefix tailTrace_541106
  have hstable : (prefixWord ++ tailWord_541106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541106).length < 2 ^ (prefixWord ++ tailWord_541106).sum := by decide
  have hdescent : baseEnd_541106 < baseStart_541106 := by decide
  rcases family_descends (prefixWord ++ tailWord_541106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541183 : List Nat := [1, 1, 2, 2, 1, 2, 6, 1, 1, 5]
def baseStart_541183 : Nat := 118140960795 + 541183 * 2 ^ 59
def prefixEnd_541183 : Nat := 4983230072969 + 3 ^ 40 * 541183 * 2
def baseEnd_541183 : Nat := 185258000694840901815767

theorem tailTrace_541183 : CollatzResearch.WordTrace tailWord_541183 prefixEnd_541183 185258000694840901815767 := by
  unfold tailWord_541183
  simp only [CollatzResearch.WordTrace]
  refine ⟨19738565598393892543044203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13159043732262595028696135 19738565598393892543044203)
  ·
    refine ⟨29607848397590838814566305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19738565598393892543044203 29607848397590838814566305)
    ·
      refine ⟨22205886298193129110924729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29607848397590838814566305 22205886298193129110924729)
      ·
        refine ⟨16654414723644846833193547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22205886298193129110924729 16654414723644846833193547)
        ·
          refine ⟨24981622085467270249790321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16654414723644846833193547 24981622085467270249790321)
          ·
            refine ⟨18736216564100452687342741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24981622085467270249790321 18736216564100452687342741)
            ·
              refine ⟨878260151442208719719191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 18736216564100452687342741 878260151442208719719191)
              ·
                refine ⟨1317390227163313079578787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 878260151442208719719191 1317390227163313079578787)
                ·
                  refine ⟨1976085340744969619368181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1317390227163313079578787 1976085340744969619368181)
                  ·
                    refine ⟨185258000694840901815767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1976085340744969619368181 185258000694840901815767)
                    ·
                      rfl

theorem cell22_541183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 6, 1, 1, 5].length) (baseStart_541183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_541183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_541183 prefixEnd_541183 := by exact prefixLift 541183
  have htrace : WordTrace (prefixWord ++ tailWord_541183) baseStart_541183 baseEnd_541183 := by
    simpa [prefixWord, tailWord_541183, baseEnd_541183] using wordTrace_append hprefix tailTrace_541183
  have hstable : (prefixWord ++ tailWord_541183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541183).length < 2 ^ (prefixWord ++ tailWord_541183).sum := by decide
  have hdescent : baseEnd_541183 < baseStart_541183 := by decide
  rcases family_descends (prefixWord ++ tailWord_541183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541204 : List Nat := [2, 4, 3, 1, 1, 1, 4, 1, 1, 4]
def baseStart_541204 : Nat := 118140960795 + 541204 * 2 ^ 59
def prefixEnd_541204 : Nat := 4983230072969 + 3 ^ 40 * 541204 * 2
def baseEnd_541204 : Nat := 185265189424003847040703

theorem tailTrace_541204 : CollatzResearch.WordTrace tailWord_541204 prefixEnd_541204 185265189424003847040703 := by
  unfold tailWord_541204
  simp only [CollatzResearch.WordTrace]
  refine ⟨9869665765658906564779333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13159554354211875419705777 9869665765658906564779333)
  ·
    refine ⟨1850562331061044980896125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9869665765658906564779333 1850562331061044980896125)
    ·
      refine ⟨693960874147891867836047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1850562331061044980896125 693960874147891867836047)
      ·
        refine ⟨1040941311221837801754071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 693960874147891867836047 1040941311221837801754071)
        ·
          refine ⟨1561411966832756702631107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1040941311221837801754071 1561411966832756702631107)
          ·
            refine ⟨2342117950249135053946661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1561411966832756702631107 2342117950249135053946661)
            ·
              refine ⟨439147115671712822614999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2342117950249135053946661 439147115671712822614999)
              ·
                refine ⟨658720673507569233922499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 439147115671712822614999 658720673507569233922499)
                ·
                  refine ⟨988081010261353850883749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 658720673507569233922499 988081010261353850883749)
                  ·
                    refine ⟨185265189424003847040703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 988081010261353850883749 185265189424003847040703)
                    ·
                      rfl

theorem cell22_541204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_541204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_541204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_541204 prefixEnd_541204 := by exact prefixLift 541204
  have htrace : WordTrace (prefixWord ++ tailWord_541204) baseStart_541204 baseEnd_541204 := by
    simpa [prefixWord, tailWord_541204, baseEnd_541204] using wordTrace_append hprefix tailTrace_541204
  have hstable : (prefixWord ++ tailWord_541204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541204).length < 2 ^ (prefixWord ++ tailWord_541204).sum := by decide
  have hdescent : baseEnd_541204 < baseStart_541204 := by decide
  rcases family_descends (prefixWord ++ tailWord_541204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541211 : List Nat := [1, 1, 1, 1, 1, 1, 3, 1, 3, 9]
def baseStart_541211 : Nat := 118140960795 + 541211 * 2 ^ 59
def prefixEnd_541211 : Nat := 4983230072969 + 3 ^ 40 * 541211 * 2
def baseEnd_541211 : Nat := 185267585667058162115681

theorem tailTrace_541211 : CollatzResearch.WordTrace tailWord_541211 prefixEnd_541211 185267585667058162115681 := by
  unfold tailWord_541211
  simp only [CollatzResearch.WordTrace]
  refine ⟨19739586842292453325063487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13159724561528302216708991 19739586842292453325063487)
  ·
    refine ⟨29609380263438679987595231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19739586842292453325063487 29609380263438679987595231)
    ·
      refine ⟨44414070395158019981392847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29609380263438679987595231 44414070395158019981392847)
      ·
        refine ⟨66621105592737029972089271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44414070395158019981392847 66621105592737029972089271)
        ·
          refine ⟨99931658389105544958133907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66621105592737029972089271 99931658389105544958133907)
          ·
            refine ⟨149897487583658317437200861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99931658389105544958133907 149897487583658317437200861)
            ·
              refine ⟨56211557843871869038950323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 149897487583658317437200861 56211557843871869038950323)
              ·
                refine ⟨84317336765807803558425485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56211557843871869038950323 84317336765807803558425485)
                ·
                  refine ⟨31619001287177926334409557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 84317336765807803558425485 31619001287177926334409557)
                  ·
                    refine ⟨185267585667058162115681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 31619001287177926334409557 185267585667058162115681)
                    ·
                      rfl

theorem cell22_541211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 9].length) (baseStart_541211 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_541211 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_541211 prefixEnd_541211 := by exact prefixLift 541211
  have htrace : WordTrace (prefixWord ++ tailWord_541211) baseStart_541211 baseEnd_541211 := by
    simpa [prefixWord, tailWord_541211, baseEnd_541211] using wordTrace_append hprefix tailTrace_541211
  have hstable : (prefixWord ++ tailWord_541211).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541211).length < 2 ^ (prefixWord ++ tailWord_541211).sum := by decide
  have hdescent : baseEnd_541211 < baseStart_541211 := by decide
  rcases family_descends (prefixWord ++ tailWord_541211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541213 : List Nat := [1, 4, 2, 2, 1, 3, 9]
def baseStart_541213 : Nat := 118140960795 + 541213 * 2 ^ 59
def prefixEnd_541213 : Nat := 4983230072969 + 3 ^ 40 * 541213 * 2
def baseEnd_541213 : Nat := 6861787789182623095025

theorem tailTrace_541213 : CollatzResearch.WordTrace tailWord_541213 prefixEnd_541213 6861787789182623095025 := by
  unfold tailWord_541213
  simp only [CollatzResearch.WordTrace]
  refine ⟨19739659788285207666636293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13159773192190138444424195 19739659788285207666636293)
  ·
    refine ⟨3701186210303476437494305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19739659788285207666636293 3701186210303476437494305)
    ·
      refine ⟨2775889657727607328120729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3701186210303476437494305 2775889657727607328120729)
      ·
        refine ⟨2081917243295705496090547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2775889657727607328120729 2081917243295705496090547)
        ·
          refine ⟨3122875864943558244135821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2081917243295705496090547 3122875864943558244135821)
          ·
            refine ⟨1171078449353834341550933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3122875864943558244135821 1171078449353834341550933)
            ·
              refine ⟨6861787789182623095025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1171078449353834341550933 6861787789182623095025)
              ·
                rfl

theorem cell22_541213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 9].length) (baseStart_541213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_541213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_541213 prefixEnd_541213 := by exact prefixLift 541213
  have htrace : WordTrace (prefixWord ++ tailWord_541213) baseStart_541213 baseEnd_541213 := by
    simpa [prefixWord, tailWord_541213, baseEnd_541213] using wordTrace_append hprefix tailTrace_541213
  have hstable : (prefixWord ++ tailWord_541213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541213).length < 2 ^ (prefixWord ++ tailWord_541213).sum := by decide
  have hdescent : baseEnd_541213 < baseStart_541213 := by decide
  rcases family_descends (prefixWord ++ tailWord_541213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541258 : List Nat := [3, 1, 2, 1, 1, 4, 1, 2, 7]
def baseStart_541258 : Nat := 118140960795 + 541258 * 2 ^ 59
def prefixEnd_541258 : Nat := 4983230072969 + 3 ^ 40 * 541258 * 2
def baseEnd_541258 : Nat := 61761224909188568730179

theorem tailTrace_541258 : CollatzResearch.WordTrace tailWord_541258 prefixEnd_541258 61761224909188568730179 := by
  unfold tailWord_541258
  simp only [CollatzResearch.WordTrace]
  refine ⟨4935325268280545088006107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13160867382081453568016285 4935325268280545088006107)
  ·
    refine ⟨7402987902420817632009161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4935325268280545088006107 7402987902420817632009161)
    ·
      refine ⟨5552240926815613224006871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7402987902420817632009161 5552240926815613224006871)
      ·
        refine ⟨8328361390223419836010307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5552240926815613224006871 8328361390223419836010307)
        ·
          refine ⟨12492542085335129754015461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8328361390223419836010307 12492542085335129754015461)
          ·
            refine ⟨2342351641000336828877899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12492542085335129754015461 2342351641000336828877899)
            ·
              refine ⟨3513527461500505243316849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2342351641000336828877899 3513527461500505243316849)
              ·
                refine ⟨2635145596125378932487637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3513527461500505243316849 2635145596125378932487637)
                ·
                  refine ⟨61761224909188568730179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2635145596125378932487637 61761224909188568730179)
                  ·
                    rfl

theorem cell22_541258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 2, 7].length) (baseStart_541258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_541258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_541258 prefixEnd_541258 := by exact prefixLift 541258
  have htrace : WordTrace (prefixWord ++ tailWord_541258) baseStart_541258 baseEnd_541258 := by
    simpa [prefixWord, tailWord_541258, baseEnd_541258] using wordTrace_append hprefix tailTrace_541258
  have hstable : (prefixWord ++ tailWord_541258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541258).length < 2 ^ (prefixWord ++ tailWord_541258).sum := by decide
  have hdescent : baseEnd_541258 < baseStart_541258 := by decide
  rcases family_descends (prefixWord ++ tailWord_541258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541303 : List Nat := [1, 1, 3, 1, 1, 3, 2, 4, 6]
def baseStart_541303 : Nat := 118140960795 + 541303 * 2 ^ 59
def prefixEnd_541303 : Nat := 4983230072969 + 3 ^ 40 * 541303 * 2
def baseEnd_541303 : Nat := 61766359715733529605133

theorem tailTrace_541303 : CollatzResearch.WordTrace tailWord_541303 prefixEnd_541303 61766359715733529605133 := by
  unfold tailWord_541303
  simp only [CollatzResearch.WordTrace]
  refine ⟨19742942357959153037412563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13161961571972768691608375 19742942357959153037412563)
  ·
    refine ⟨29614413536938729556118845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19742942357959153037412563 29614413536938729556118845)
    ·
      refine ⟨11105405076352023583544567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29614413536938729556118845 11105405076352023583544567)
      ·
        refine ⟨16658107614528035375316851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11105405076352023583544567 16658107614528035375316851)
        ·
          refine ⟨24987161421792053062975277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16658107614528035375316851 24987161421792053062975277)
          ·
            refine ⟨9370185533172019898615729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24987161421792053062975277 9370185533172019898615729)
            ·
              refine ⟨7027639149879014923961797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9370185533172019898615729 7027639149879014923961797)
              ·
                refine ⟨1317682340602315298242837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7027639149879014923961797 1317682340602315298242837)
                ·
                  refine ⟨61766359715733529605133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1317682340602315298242837 61766359715733529605133)
                  ·
                    rfl

theorem cell22_541303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 4, 6].length) (baseStart_541303 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_541303 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_541303 prefixEnd_541303 := by exact prefixLift 541303
  have htrace : WordTrace (prefixWord ++ tailWord_541303) baseStart_541303 baseEnd_541303 := by
    simpa [prefixWord, tailWord_541303, baseEnd_541303] using wordTrace_append hprefix tailTrace_541303
  have hstable : (prefixWord ++ tailWord_541303).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541303).length < 2 ^ (prefixWord ++ tailWord_541303).sum := by decide
  have hdescent : baseEnd_541303 < baseStart_541303 := by decide
  rcases family_descends (prefixWord ++ tailWord_541303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541305 : List Nat := [1, 2, 1, 3, 3, 3, 1, 1, 3, 4]
def baseStart_541305 : Nat := 118140960795 + 541305 * 2 ^ 59
def prefixEnd_541305 : Nat := 4983230072969 + 3 ^ 40 * 541305 * 2
def baseEnd_541305 : Nat := 185299763788073250265393

theorem tailTrace_541305 : CollatzResearch.WordTrace tailWord_541305 prefixEnd_541305 185299763788073250265393 := by
  unfold tailWord_541305
  simp only [CollatzResearch.WordTrace]
  refine ⟨19743015303951907378985369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13162010202634604919323579 19743015303951907378985369)
  ·
    refine ⟨14807261477963930534239027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19743015303951907378985369 14807261477963930534239027)
    ·
      refine ⟨22210892216945895801358541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14807261477963930534239027 22210892216945895801358541)
      ·
        refine ⟨8329084581354710925509453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22210892216945895801358541 8329084581354710925509453)
        ·
          refine ⟨3123406718008016597066045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8329084581354710925509453 3123406718008016597066045)
          ·
            refine ⟨1171277519253006223899767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3123406718008016597066045 1171277519253006223899767)
            ·
              refine ⟨1756916278879509335849651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1171277519253006223899767 1756916278879509335849651)
              ·
                refine ⟨2635374418319264003774477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1756916278879509335849651 2635374418319264003774477)
                ·
                  refine ⟨988265406869724001415429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2635374418319264003774477 988265406869724001415429)
                  ·
                    refine ⟨185299763788073250265393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 988265406869724001415429 185299763788073250265393)
                    ·
                      rfl

theorem cell22_541305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 1, 3, 4].length) (baseStart_541305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_541305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_541305 prefixEnd_541305 := by exact prefixLift 541305
  have htrace : WordTrace (prefixWord ++ tailWord_541305) baseStart_541305 baseEnd_541305 := by
    simpa [prefixWord, tailWord_541305, baseEnd_541305] using wordTrace_append hprefix tailTrace_541305
  have hstable : (prefixWord ++ tailWord_541305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541305).length < 2 ^ (prefixWord ++ tailWord_541305).sum := by decide
  have hdescent : baseEnd_541305 < baseStart_541305 := by decide
  rcases family_descends (prefixWord ++ tailWord_541305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541333 : List Nat := [1, 3, 2, 1, 1, 1, 1, 1, 5, 6]
def baseStart_541333 : Nat := 118140960795 + 541333 * 2 ^ 59
def prefixEnd_541333 : Nat := 4983230072969 + 3 ^ 40 * 541333 * 2
def baseEnd_541333 : Nat := 185309348760290510565307

theorem tailTrace_541333 : CollatzResearch.WordTrace tailWord_541333 prefixEnd_541333 185309348760290510565307 := by
  unfold tailWord_541333
  simp only [CollatzResearch.WordTrace]
  refine ⟨19744036547850468161004653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13162691031900312107336435 19744036547850468161004653)
  ·
    refine ⟨7404013705443925560376745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19744036547850468161004653 7404013705443925560376745)
    ·
      refine ⟨5553010279082944170282559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7404013705443925560376745 5553010279082944170282559)
      ·
        refine ⟨8329515418624416255423839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5553010279082944170282559 8329515418624416255423839)
        ·
          refine ⟨12494273127936624383135759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8329515418624416255423839 12494273127936624383135759)
          ·
            refine ⟨18741409691904936574703639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12494273127936624383135759 18741409691904936574703639)
            ·
              refine ⟨28112114537857404862055459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18741409691904936574703639 28112114537857404862055459)
              ·
                refine ⟨42168171806786107293083189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28112114537857404862055459 42168171806786107293083189)
                ·
                  refine ⟨3953266106886197558726549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 42168171806786107293083189 3953266106886197558726549)
                  ·
                    refine ⟨185309348760290510565307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3953266106886197558726549 185309348760290510565307)
                    ·
                      rfl

theorem cell22_541333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 5, 6].length) (baseStart_541333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_541333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_541333 prefixEnd_541333 := by exact prefixLift 541333
  have htrace : WordTrace (prefixWord ++ tailWord_541333) baseStart_541333 baseEnd_541333 := by
    simpa [prefixWord, tailWord_541333, baseEnd_541333] using wordTrace_append hprefix tailTrace_541333
  have hstable : (prefixWord ++ tailWord_541333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541333).length < 2 ^ (prefixWord ++ tailWord_541333).sum := by decide
  have hdescent : baseEnd_541333 < baseStart_541333 := by decide
  rcases family_descends (prefixWord ++ tailWord_541333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541354 : List Nat := [3, 1, 5, 2, 1, 1, 1, 2, 6]
def baseStart_541354 : Nat := 118140960795 + 541354 * 2 ^ 59
def prefixEnd_541354 : Nat := 4983230072969 + 3 ^ 40 * 541354 * 2
def baseEnd_541354 : Nat := 61772179163151151930081

theorem tailTrace_541354 : CollatzResearch.WordTrace tailWord_541354 prefixEnd_541354 61772179163151151930081 := by
  unfold tailWord_541354
  simp only [CollatzResearch.WordTrace]
  refine ⟨4936200620193597186879779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13163201653849592498346077 4936200620193597186879779)
  ·
    refine ⟨7404300930290395780319669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4936200620193597186879779 7404300930290395780319669)
    ·
      refine ⟨694153212214724604404969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7404300930290395780319669 694153212214724604404969)
      ·
        refine ⟨520614909161043453303727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 694153212214724604404969 520614909161043453303727)
        ·
          refine ⟨780922363741565179955591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 520614909161043453303727 780922363741565179955591)
          ·
            refine ⟨1171383545612347769933387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 780922363741565179955591 1171383545612347769933387)
            ·
              refine ⟨1757075318418521654900081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1171383545612347769933387 1757075318418521654900081)
              ·
                refine ⟨1317806488813891241175061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1757075318418521654900081 1317806488813891241175061)
                ·
                  refine ⟨61772179163151151930081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1317806488813891241175061 61772179163151151930081)
                  ·
                    rfl

theorem cell22_541354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 2, 6].length) (baseStart_541354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_541354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_541354 prefixEnd_541354 := by exact prefixLift 541354
  have htrace : WordTrace (prefixWord ++ tailWord_541354) baseStart_541354 baseEnd_541354 := by
    simpa [prefixWord, tailWord_541354, baseEnd_541354] using wordTrace_append hprefix tailTrace_541354
  have hstable : (prefixWord ++ tailWord_541354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541354).length < 2 ^ (prefixWord ++ tailWord_541354).sum := by decide
  have hdescent : baseEnd_541354 < baseStart_541354 := by decide
  rcases family_descends (prefixWord ++ tailWord_541354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541474 : List Nat := [3, 3, 1, 1, 2, 2, 3, 2, 1, 4]
def baseStart_541474 : Nat := 118140960795 + 541474 * 2 ^ 59
def prefixEnd_541474 : Nat := 4983230072969 + 3 ^ 40 * 541474 * 2
def baseEnd_541474 : Nat := 185357615941813142789875

theorem tailTrace_541474 : CollatzResearch.WordTrace tailWord_541474 prefixEnd_541474 185357615941813142789875 := by
  unfold tailWord_541474
  simp only [CollatzResearch.WordTrace]
  refine ⟨4937294810084912310471869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13166119493559766161258317 4937294810084912310471869)
  ·
    refine ⟨1851485553781842116426951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4937294810084912310471869 1851485553781842116426951)
    ·
      refine ⟨2777228330672763174640427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1851485553781842116426951 2777228330672763174640427)
      ·
        refine ⟨4165842496009144761960641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2777228330672763174640427 4165842496009144761960641)
        ·
          refine ⟨3124381872006858571470481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4165842496009144761960641 3124381872006858571470481)
          ·
            refine ⟨2343286404005143928602861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3124381872006858571470481 2343286404005143928602861)
            ·
              refine ⟨878732401501928973226073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2343286404005143928602861 878732401501928973226073)
              ·
                refine ⟨659049301126446729919555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 878732401501928973226073 659049301126446729919555)
                ·
                  refine ⟨988573951689670094879333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 659049301126446729919555 988573951689670094879333)
                  ·
                    refine ⟨185357615941813142789875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 988573951689670094879333 185357615941813142789875)
                    ·
                      rfl

theorem cell22_541474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 3, 2, 1, 4].length) (baseStart_541474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_541474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_541474 prefixEnd_541474 := by exact prefixLift 541474
  have htrace : WordTrace (prefixWord ++ tailWord_541474) baseStart_541474 baseEnd_541474 := by
    simpa [prefixWord, tailWord_541474, baseEnd_541474] using wordTrace_append hprefix tailTrace_541474
  have hstable : (prefixWord ++ tailWord_541474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541474).length < 2 ^ (prefixWord ++ tailWord_541474).sum := by decide
  have hdescent : baseEnd_541474 < baseStart_541474 := by decide
  rcases family_descends (prefixWord ++ tailWord_541474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541577 : List Nat := [1, 2, 1, 1, 5, 2, 2, 1, 2, 5]
def baseStart_541577 : Nat := 118140960795 + 541577 * 2 ^ 59
def prefixEnd_541577 : Nat := 4983230072969 + 3 ^ 40 * 541577 * 2
def baseEnd_541577 : Nat := 185392874946755207464559

theorem tailTrace_541577 : CollatzResearch.WordTrace tailWord_541577 prefixEnd_541577 185392874946755207464559 := by
  unfold tailWord_541577
  simp only [CollatzResearch.WordTrace]
  refine ⟨19752935958966497832886985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13168623972644331888591323 19752935958966497832886985)
  ·
    refine ⟨14814701969224873374665239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19752935958966497832886985 14814701969224873374665239)
    ·
      refine ⟨22222052953837310061997859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14814701969224873374665239 22222052953837310061997859)
      ·
        refine ⟨33333079430755965092996789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22222052953837310061997859 33333079430755965092996789)
        ·
          refine ⟨3124976196633371727468449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 33333079430755965092996789 3124976196633371727468449)
          ·
            refine ⟨2343732147475028795601337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3124976196633371727468449 2343732147475028795601337)
            ·
              refine ⟨1757799110606271596701003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2343732147475028795601337 1757799110606271596701003)
              ·
                refine ⟨2636698665909407395051505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1757799110606271596701003 2636698665909407395051505)
                ·
                  refine ⟨1977523999432055546288629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2636698665909407395051505 1977523999432055546288629)
                  ·
                    refine ⟨185392874946755207464559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1977523999432055546288629 185392874946755207464559)
                    ·
                      rfl

theorem cell22_541577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 1, 2, 5].length) (baseStart_541577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_541577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_541577 prefixEnd_541577 := by exact prefixLift 541577
  have htrace : WordTrace (prefixWord ++ tailWord_541577) baseStart_541577 baseEnd_541577 := by
    simpa [prefixWord, tailWord_541577, baseEnd_541577] using wordTrace_append hprefix tailTrace_541577
  have hstable : (prefixWord ++ tailWord_541577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541577).length < 2 ^ (prefixWord ++ tailWord_541577).sum := by decide
  have hdescent : baseEnd_541577 < baseStart_541577 := by decide
  rcases family_descends (prefixWord ++ tailWord_541577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541624 : List Nat := [2, 1, 2, 1, 2, 6, 1, 1, 6]
def baseStart_541624 : Nat := 118140960795 + 541624 * 2 ^ 59
def prefixEnd_541624 : Nat := 4983230072969 + 3 ^ 40 * 541624 * 2
def baseEnd_541624 : Nat := 61802988002420917179805

theorem tailTrace_541624 : CollatzResearch.WordTrace tailWord_541624 prefixEnd_541624 61802988002420917179805 := by
  unfold tailWord_541624
  simp only [CollatzResearch.WordTrace]
  refine ⟨9877325094898112429923963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13169766793197483239898617 9877325094898112429923963)
  ·
    refine ⟨14815987642347168644885945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9877325094898112429923963 14815987642347168644885945)
    ·
      refine ⟨11111990731760376483664459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14815987642347168644885945 11111990731760376483664459)
      ·
        refine ⟨16667986097640564725496689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11111990731760376483664459 16667986097640564725496689)
        ·
          refine ⟨12500989573230423544122517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16667986097640564725496689 12500989573230423544122517)
          ·
            refine ⟨585983886245176103630743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 12500989573230423544122517 585983886245176103630743)
            ·
              refine ⟨878975829367764155446115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 585983886245176103630743 878975829367764155446115)
              ·
                refine ⟨1318463744051646233169173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 878975829367764155446115 1318463744051646233169173)
                ·
                  refine ⟨61802988002420917179805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1318463744051646233169173 61802988002420917179805)
                  ·
                    rfl

theorem cell22_541624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 1, 1, 6].length) (baseStart_541624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_541624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_541624 prefixEnd_541624 := by exact prefixLift 541624
  have htrace : WordTrace (prefixWord ++ tailWord_541624) baseStart_541624 baseEnd_541624 := by
    simpa [prefixWord, tailWord_541624, baseEnd_541624] using wordTrace_append hprefix tailTrace_541624
  have hstable : (prefixWord ++ tailWord_541624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541624).length < 2 ^ (prefixWord ++ tailWord_541624).sum := by decide
  have hdescent : baseEnd_541624 < baseStart_541624 := by decide
  rcases family_descends (prefixWord ++ tailWord_541624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541669 : List Nat := [1, 3, 1, 6, 1, 10]
def baseStart_541669 : Nat := 118140960795 + 541669 * 2 ^ 59
def prefixEnd_541669 : Nat := 4983230072969 + 3 ^ 40 * 541669 * 2
def baseEnd_541669 : Nat := 2289189733665402890917

theorem tailTrace_541669 : CollatzResearch.WordTrace tailWord_541669 prefixEnd_541669 2289189733665402890917 := by
  unfold tailWord_541669
  simp only [CollatzResearch.WordTrace]
  refine ⟨19756291474633197545236061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13170860983088798363490707 19756291474633197545236061)
  ·
    refine ⟨7408609302987449079463523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19756291474633197545236061 7408609302987449079463523)
    ·
      refine ⟨11112913954481173619195285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7408609302987449079463523 11112913954481173619195285)
      ·
        refine ⟨520917841616305013399779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 11112913954481173619195285 520917841616305013399779)
        ·
          refine ⟨781376762424457520099669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 520917841616305013399779 781376762424457520099669)
          ·
            refine ⟨2289189733665402890917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 781376762424457520099669 2289189733665402890917)
            ·
              rfl

theorem cell22_541669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 10].length) (baseStart_541669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_541669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_541669 prefixEnd_541669 := by exact prefixLift 541669
  have htrace : WordTrace (prefixWord ++ tailWord_541669) baseStart_541669 baseEnd_541669 := by
    simpa [prefixWord, tailWord_541669, baseEnd_541669] using wordTrace_append hprefix tailTrace_541669
  have hstable : (prefixWord ++ tailWord_541669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541669).length < 2 ^ (prefixWord ++ tailWord_541669).sum := by decide
  have hdescent : baseEnd_541669 < baseStart_541669 := by decide
  rcases family_descends (prefixWord ++ tailWord_541669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541686 : List Nat := [5, 1, 1, 1, 3, 3, 1, 7]
def baseStart_541686 : Nat := 118140960795 + 541686 * 2 ^ 59
def prefixEnd_541686 : Nat := 4983230072969 + 3 ^ 40 * 541686 * 2
def baseEnd_541686 : Nat := 20603354208257250721025

theorem tailTrace_541686 : CollatzResearch.WordTrace tailWord_541686 prefixEnd_541686 20603354208257250721025 := by
  unfold tailWord_541686
  simp only [CollatzResearch.WordTrace]
  refine ⟨1234806969723225590537807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13171274343714406299069941 1234806969723225590537807)
  ·
    refine ⟨1852210454584838385806711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1234806969723225590537807 1852210454584838385806711)
    ·
      refine ⟨2778315681877257578710067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1852210454584838385806711 2778315681877257578710067)
      ·
        refine ⟨4167473522815886368065101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2778315681877257578710067 4167473522815886368065101)
        ·
          refine ⟨1562802571055957388024413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4167473522815886368065101 1562802571055957388024413)
          ·
            refine ⟨586050964145984020509155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1562802571055957388024413 586050964145984020509155)
            ·
              refine ⟨879076446218976030763733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 586050964145984020509155 879076446218976030763733)
              ·
                refine ⟨20603354208257250721025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 879076446218976030763733 20603354208257250721025)
                ·
                  rfl

theorem cell22_541686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 1, 7].length) (baseStart_541686 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_541686 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_541686 prefixEnd_541686 := by exact prefixLift 541686
  have htrace : WordTrace (prefixWord ++ tailWord_541686) baseStart_541686 baseEnd_541686 := by
    simpa [prefixWord, tailWord_541686, baseEnd_541686] using wordTrace_append hprefix tailTrace_541686
  have hstable : (prefixWord ++ tailWord_541686).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541686).length < 2 ^ (prefixWord ++ tailWord_541686).sum := by decide
  have hdescent : baseEnd_541686 < baseStart_541686 := by decide
  rcases family_descends (prefixWord ++ tailWord_541686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541712 : List Nat := [2, 1, 1, 1, 1, 1, 1, 3, 6, 5]
def baseStart_541712 : Nat := 118140960795 + 541712 * 2 ^ 59
def prefixEnd_541712 : Nat := 4983230072969 + 3 ^ 40 * 541712 * 2
def baseEnd_541712 : Nat := 185439088205659855339145

theorem tailTrace_541712 : CollatzResearch.WordTrace tailWord_541712 prefixEnd_541712 185439088205659855339145 := by
  unfold tailWord_541712
  simp only [CollatzResearch.WordTrace]
  refine ⟨9878929906738707944525695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13171906542318277259367593 9878929906738707944525695)
  ·
    refine ⟨14818394860108061916788543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9878929906738707944525695 14818394860108061916788543)
    ·
      refine ⟨22227592290162092875182815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14818394860108061916788543 22227592290162092875182815)
      ·
        refine ⟨33341388435243139312774223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22227592290162092875182815 33341388435243139312774223)
        ·
          refine ⟨50012082652864708969161335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33341388435243139312774223 50012082652864708969161335)
          ·
            refine ⟨75018123979297063453742003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50012082652864708969161335 75018123979297063453742003)
            ·
              refine ⟨112527185968945595180613005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75018123979297063453742003 112527185968945595180613005)
              ·
                refine ⟨42197694738354598192729877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 112527185968945595180613005 42197694738354598192729877)
                ·
                  refine ⟨1978016940860371790284213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 42197694738354598192729877 1978016940860371790284213)
                  ·
                    refine ⟨185439088205659855339145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1978016940860371790284213 185439088205659855339145)
                    ·
                      rfl

theorem cell22_541712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 6, 5].length) (baseStart_541712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_541712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_541712 prefixEnd_541712 := by exact prefixLift 541712
  have htrace : WordTrace (prefixWord ++ tailWord_541712) baseStart_541712 baseEnd_541712 := by
    simpa [prefixWord, tailWord_541712, baseEnd_541712] using wordTrace_append hprefix tailTrace_541712
  have hstable : (prefixWord ++ tailWord_541712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541712).length < 2 ^ (prefixWord ++ tailWord_541712).sum := by decide
  have hdescent : baseEnd_541712 < baseStart_541712 := by decide
  rcases family_descends (prefixWord ++ tailWord_541712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541729 : List Nat := [1, 2, 3, 2, 3, 1, 1, 2, 2, 5]
def baseStart_541729 : Nat := 118140960795 + 541729 * 2 ^ 59
def prefixEnd_541729 : Nat := 4983230072969 + 3 ^ 40 * 541729 * 2
def baseEnd_541729 : Nat := 185444907653077477664093

theorem tailTrace_541729 : CollatzResearch.WordTrace tailWord_541729 prefixEnd_541729 185444907653077477664093 := by
  unfold tailWord_541729
  simp only [CollatzResearch.WordTrace]
  refine ⟨19758479854415827792420241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13172319902943885194946827 19758479854415827792420241)
  ·
    refine ⟨14818859890811870844315181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19758479854415827792420241 14818859890811870844315181)
    ·
      refine ⟨5557072459054451566618193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14818859890811870844315181 5557072459054451566618193)
      ·
        refine ⟨4167804344290838674963645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5557072459054451566618193 4167804344290838674963645)
        ·
          refine ⟨1562926629109064503111367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4167804344290838674963645 1562926629109064503111367)
          ·
            refine ⟨2344389943663596754667051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1562926629109064503111367 2344389943663596754667051)
            ·
              refine ⟨3516584915495395132000577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2344389943663596754667051 3516584915495395132000577)
              ·
                refine ⟨2637438686621546349000433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3516584915495395132000577 2637438686621546349000433)
                ·
                  refine ⟨1978079014966159761750325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2637438686621546349000433 1978079014966159761750325)
                  ·
                    refine ⟨185444907653077477664093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1978079014966159761750325 185444907653077477664093)
                    ·
                      rfl

theorem cell22_541729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 2, 2, 5].length) (baseStart_541729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_541729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_541729 prefixEnd_541729 := by exact prefixLift 541729
  have htrace : WordTrace (prefixWord ++ tailWord_541729) baseStart_541729 baseEnd_541729 := by
    simpa [prefixWord, tailWord_541729, baseEnd_541729] using wordTrace_append hprefix tailTrace_541729
  have hstable : (prefixWord ++ tailWord_541729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541729).length < 2 ^ (prefixWord ++ tailWord_541729).sum := by decide
  have hdescent : baseEnd_541729 < baseStart_541729 := by decide
  rcases family_descends (prefixWord ++ tailWord_541729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541731 : List Nat := [1, 1, 1, 4, 3, 4, 1, 2, 5]
def baseStart_541731 : Nat := 118140960795 + 541731 * 2 ^ 59
def prefixEnd_541731 : Nat := 4983230072969 + 3 ^ 40 * 541731 * 2
def baseEnd_541731 : Nat := 61815197431316713038029

theorem tailTrace_541731 : CollatzResearch.WordTrace tailWord_541731 prefixEnd_541731 61815197431316713038029 := by
  unfold tailWord_541731
  simp only [CollatzResearch.WordTrace]
  refine ⟨19758552800408582133993047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13172368533605721422662031 19758552800408582133993047)
  ·
    refine ⟨29637829200612873200989571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19758552800408582133993047 29637829200612873200989571)
    ·
      refine ⟨44456743800919309801484357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29637829200612873200989571 44456743800919309801484357)
      ·
        refine ⟨8335639462672370587778317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44456743800919309801484357 8335639462672370587778317)
        ·
          refine ⟨3125864798502138970416869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8335639462672370587778317 3125864798502138970416869)
          ·
            refine ⟨586099649719151056953163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3125864798502138970416869 586099649719151056953163)
            ·
              refine ⟨879149474578726585429745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 586099649719151056953163 879149474578726585429745)
              ·
                refine ⟨659362105934044939072309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 879149474578726585429745 659362105934044939072309)
                ·
                  refine ⟨61815197431316713038029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 659362105934044939072309 61815197431316713038029)
                  ·
                    rfl

theorem cell22_541731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 1, 2, 5].length) (baseStart_541731 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_541731 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_541731 prefixEnd_541731 := by exact prefixLift 541731
  have htrace : WordTrace (prefixWord ++ tailWord_541731) baseStart_541731 baseEnd_541731 := by
    simpa [prefixWord, tailWord_541731, baseEnd_541731] using wordTrace_append hprefix tailTrace_541731
  have hstable : (prefixWord ++ tailWord_541731).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541731).length < 2 ^ (prefixWord ++ tailWord_541731).sum := by decide
  have hdescent : baseEnd_541731 < baseStart_541731 := by decide
  rcases family_descends (prefixWord ++ tailWord_541731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541735 : List Nat := [1, 1, 7, 1, 1, 1, 2, 4, 1, 3]
def baseStart_541735 : Nat := 118140960795 + 541735 * 2 ^ 59
def prefixEnd_541735 : Nat := 4983230072969 + 3 ^ 40 * 541735 * 2
def baseEnd_541735 : Nat := 185446961575695462014075

theorem tailTrace_541735 : CollatzResearch.WordTrace tailWord_541735 prefixEnd_541735 185446961575695462014075 := by
  unfold tailWord_541735
  simp only [CollatzResearch.WordTrace]
  refine ⟨19758698692394090817138659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13172465794929393878092439 19758698692394090817138659)
  ·
    refine ⟨29638048038591136225707989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19758698692394090817138659 29638048038591136225707989)
    ·
      refine ⟨694641750904479755290031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 29638048038591136225707989 694641750904479755290031)
      ·
        refine ⟨1041962626356719632935047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 694641750904479755290031 1041962626356719632935047)
        ·
          refine ⟨1562943939535079449402571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1041962626356719632935047 1562943939535079449402571)
          ·
            refine ⟨2344415909302619174103857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1562943939535079449402571 2344415909302619174103857)
            ·
              refine ⟨1758311931976964380577893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2344415909302619174103857 1758311931976964380577893)
              ·
                refine ⟨329683487245680821358355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1758311931976964380577893 329683487245680821358355)
                ·
                  refine ⟨494525230868521232037533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 329683487245680821358355 494525230868521232037533)
                  ·
                    refine ⟨185446961575695462014075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 494525230868521232037533 185446961575695462014075)
                    ·
                      rfl

theorem cell22_541735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_541735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_541735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_541735 prefixEnd_541735 := by exact prefixLift 541735
  have htrace : WordTrace (prefixWord ++ tailWord_541735) baseStart_541735 baseEnd_541735 := by
    simpa [prefixWord, tailWord_541735, baseEnd_541735] using wordTrace_append hprefix tailTrace_541735
  have hstable : (prefixWord ++ tailWord_541735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541735).length < 2 ^ (prefixWord ++ tailWord_541735).sum := by decide
  have hdescent : baseEnd_541735 < baseStart_541735 := by decide
  rcases family_descends (prefixWord ++ tailWord_541735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541774 : List Nat := [4, 1, 1, 1, 1, 3, 2, 1, 3, 5]
def baseStart_541774 : Nat := 118140960795 + 541774 * 2 ^ 59
def prefixEnd_541774 : Nat := 4983230072969 + 3 ^ 40 * 541774 * 2
def baseEnd_541774 : Nat := 185460312072712360288955

theorem tailTrace_541774 : CollatzResearch.WordTrace tailWord_541774 prefixEnd_541774 185460312072712360288955 := by
  unfold tailWord_541774
  simp only [CollatzResearch.WordTrace]
  refine ⟨2470015142406600059726047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13173414092835200318538917 2470015142406600059726047)
  ·
    refine ⟨3705022713609900089589071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2470015142406600059726047 3705022713609900089589071)
    ·
      refine ⟨5557534070414850134383607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3705022713609900089589071 5557534070414850134383607)
      ·
        refine ⟨8336301105622275201575411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5557534070414850134383607 8336301105622275201575411)
        ·
          refine ⟨12504451658433412802363117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8336301105622275201575411 12504451658433412802363117)
          ·
            refine ⟨4689169371912529800886169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12504451658433412802363117 4689169371912529800886169)
            ·
              refine ⟨3516877028934397350664627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4689169371912529800886169 3516877028934397350664627)
              ·
                refine ⟨5275315543401596025996941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3516877028934397350664627 5275315543401596025996941)
                ·
                  refine ⟨1978243328775598509748853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5275315543401596025996941 1978243328775598509748853)
                  ·
                    refine ⟨185460312072712360288955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1978243328775598509748853 185460312072712360288955)
                    ·
                      rfl

theorem cell22_541774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 1, 3, 5].length) (baseStart_541774 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_541774 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_541774 prefixEnd_541774 := by exact prefixLift 541774
  have htrace : WordTrace (prefixWord ++ tailWord_541774) baseStart_541774 baseEnd_541774 := by
    simpa [prefixWord, tailWord_541774, baseEnd_541774] using wordTrace_append hprefix tailTrace_541774
  have hstable : (prefixWord ++ tailWord_541774).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541774).length < 2 ^ (prefixWord ++ tailWord_541774).sum := by decide
  have hdescent : baseEnd_541774 < baseStart_541774 := by decide
  rcases family_descends (prefixWord ++ tailWord_541774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541791 : List Nat := [1, 1, 2, 3, 1, 1, 4, 4, 2, 3]
def baseStart_541791 : Nat := 118140960795 + 541791 * 2 ^ 59
def prefixEnd_541791 : Nat := 4983230072969 + 3 ^ 40 * 541791 * 2
def baseEnd_541791 : Nat := 185466131520129982613903

theorem tailTrace_541791 : CollatzResearch.WordTrace tailWord_541791 prefixEnd_541791 185466131520129982613903 := by
  unfold tailWord_541791
  simp only [CollatzResearch.WordTrace]
  refine ⟨19760741180191212381177227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13173827453460808254118151 19760741180191212381177227)
  ·
    refine ⟨29641111770286818571765841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19760741180191212381177227 29641111770286818571765841)
    ·
      refine ⟨22230833827715113928824381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29641111770286818571765841 22230833827715113928824381)
      ·
        refine ⟨8336562685393167723309143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22230833827715113928824381 8336562685393167723309143)
        ·
          refine ⟨12504844028089751584963715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8336562685393167723309143 12504844028089751584963715)
          ·
            refine ⟨18757266042134627377445573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12504844028089751584963715 18757266042134627377445573)
            ·
              refine ⟨3516987382900242633271045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18757266042134627377445573 3516987382900242633271045)
              ·
                refine ⟨659435134293795493738321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3516987382900242633271045 659435134293795493738321)
                ·
                  refine ⟨494576350720346620303741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 659435134293795493738321 494576350720346620303741)
                  ·
                    refine ⟨185466131520129982613903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 494576350720346620303741 185466131520129982613903)
                    ·
                      rfl

theorem cell22_541791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 4, 2, 3].length) (baseStart_541791 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_541791 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_541791 prefixEnd_541791 := by exact prefixLift 541791
  have htrace : WordTrace (prefixWord ++ tailWord_541791) baseStart_541791 baseEnd_541791 := by
    simpa [prefixWord, tailWord_541791, baseEnd_541791] using wordTrace_append hprefix tailTrace_541791
  have hstable : (prefixWord ++ tailWord_541791).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541791).length < 2 ^ (prefixWord ++ tailWord_541791).sum := by decide
  have hdescent : baseEnd_541791 < baseStart_541791 := by decide
  rcases family_descends (prefixWord ++ tailWord_541791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541804 : List Nat := [2, 2, 1, 1, 3, 2, 4, 7]
def baseStart_541804 : Nat := 118140960795 + 541804 * 2 ^ 59
def prefixEnd_541804 : Nat := 4983230072969 + 3 ^ 40 * 541804 * 2
def baseEnd_541804 : Nat := 20607842409533586893207

theorem tailTrace_541804 : CollatzResearch.WordTrace tailWord_541804 prefixEnd_541804 20607842409533586893207 := by
  unfold tailWord_541804
  simp only [CollatzResearch.WordTrace]
  refine ⟨9880607664572057800700233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13174143552762743734266977 9880607664572057800700233)
  ·
    refine ⟨7410455748429043350525175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9880607664572057800700233 7410455748429043350525175)
    ·
      refine ⟨11115683622643565025787763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7410455748429043350525175 11115683622643565025787763)
      ·
        refine ⟨16673525433965347538681645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11115683622643565025787763 16673525433965347538681645)
        ·
          refine ⟨6252572037737005327005617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16673525433965347538681645 6252572037737005327005617)
          ·
            refine ⟨4689429028302753995254213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6252572037737005327005617 4689429028302753995254213)
            ·
              refine ⟨879267942806766374110165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4689429028302753995254213 879267942806766374110165)
              ·
                refine ⟨20607842409533586893207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 879267942806766374110165 20607842409533586893207)
                ·
                  rfl

theorem cell22_541804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 4, 7].length) (baseStart_541804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_541804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_541804 prefixEnd_541804 := by exact prefixLift 541804
  have htrace : WordTrace (prefixWord ++ tailWord_541804) baseStart_541804 baseEnd_541804 := by
    simpa [prefixWord, tailWord_541804, baseEnd_541804] using wordTrace_append hprefix tailTrace_541804
  have hstable : (prefixWord ++ tailWord_541804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541804).length < 2 ^ (prefixWord ++ tailWord_541804).sum := by decide
  have hdescent : baseEnd_541804 < baseStart_541804 := by decide
  rcases family_descends (prefixWord ++ tailWord_541804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541956 : List Nat := [2, 3, 2, 2, 2, 1, 10]
def baseStart_541956 : Nat := 118140960795 + 541956 * 2 ^ 59
def prefixEnd_541956 : Nat := 4983230072969 + 3 ^ 40 * 541956 * 2
def baseEnd_541956 : Nat := 6871207940449057490311

theorem tailTrace_541956 : CollatzResearch.WordTrace tailWord_541956 prefixEnd_541956 6871207940449057490311 := by
  unfold tailWord_541956
  simp only [CollatzResearch.WordTrace]
  refine ⟨9883379612296722780466861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13177839483062297040622481 9883379612296722780466861)
  ·
    refine ⟨3706267354611271042675073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9883379612296722780466861 3706267354611271042675073)
    ·
      refine ⟨2779700515958453282006305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3706267354611271042675073 2779700515958453282006305)
      ·
        refine ⟨2084775386968839961504729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2779700515958453282006305 2084775386968839961504729)
        ·
          refine ⟨1563581540226629971128547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2084775386968839961504729 1563581540226629971128547)
          ·
            refine ⟨2345372310339944956692821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1563581540226629971128547 2345372310339944956692821)
            ·
              refine ⟨6871207940449057490311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 2345372310339944956692821 6871207940449057490311)
              ·
                rfl

theorem cell22_541956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 10].length) (baseStart_541956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_541956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_541956 prefixEnd_541956 := by exact prefixLift 541956
  have htrace : WordTrace (prefixWord ++ tailWord_541956) baseStart_541956 baseEnd_541956 := by
    simpa [prefixWord, tailWord_541956, baseEnd_541956] using wordTrace_append hprefix tailTrace_541956
  have hstable : (prefixWord ++ tailWord_541956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541956).length < 2 ^ (prefixWord ++ tailWord_541956).sum := by decide
  have hdescent : baseEnd_541956 < baseStart_541956 := by decide
  rcases family_descends (prefixWord ++ tailWord_541956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541988 : List Nat := [2, 3, 1, 3, 1, 1, 2, 1, 5, 3]
def baseStart_541988 : Nat := 118140960795 + 541988 * 2 ^ 59
def prefixEnd_541988 : Nat := 4983230072969 + 3 ^ 40 * 541988 * 2
def baseEnd_541988 : Nat := 185533568646087135438299

theorem tailTrace_541988 : CollatzResearch.WordTrace tailWord_541988 prefixEnd_541988 185533568646087135438299 := by
  unfold tailWord_541988
  simp only [CollatzResearch.WordTrace]
  refine ⟨9883963180238757513049309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13178617573651676684065745 9883963180238757513049309)
  ·
    refine ⟨3706486192589534067393491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9883963180238757513049309 3706486192589534067393491)
    ·
      refine ⟨5559729288884301101090237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3706486192589534067393491 5559729288884301101090237)
      ·
        refine ⟨2084898483331612912908839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5559729288884301101090237 2084898483331612912908839)
        ·
          refine ⟨3127347724997419369363259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2084898483331612912908839 3127347724997419369363259)
          ·
            refine ⟨4691021587496129054044889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3127347724997419369363259 4691021587496129054044889)
            ·
              refine ⟨3518266190622096790533667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4691021587496129054044889 3518266190622096790533667)
              ·
                refine ⟨5277399285933145185800501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3518266190622096790533667 5277399285933145185800501)
                ·
                  refine ⟨494756183056232361168797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5277399285933145185800501 494756183056232361168797)
                  ·
                    refine ⟨185533568646087135438299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 494756183056232361168797 185533568646087135438299)
                    ·
                      rfl

theorem cell22_541988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 1, 5, 3].length) (baseStart_541988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_541988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_541988 prefixEnd_541988 := by exact prefixLift 541988
  have htrace : WordTrace (prefixWord ++ tailWord_541988) baseStart_541988 baseEnd_541988 := by
    simpa [prefixWord, tailWord_541988, baseEnd_541988] using wordTrace_append hprefix tailTrace_541988
  have hstable : (prefixWord ++ tailWord_541988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541988).length < 2 ^ (prefixWord ++ tailWord_541988).sum := by decide
  have hdescent : baseEnd_541988 < baseStart_541988 := by decide
  rcases family_descends (prefixWord ++ tailWord_541988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542016 : List Nat := [2, 1, 1, 2, 2, 1, 4, 2, 2, 5]
def baseStart_542016 : Nat := 118140960795 + 542016 * 2 ^ 59
def prefixEnd_542016 : Nat := 4983230072969 + 3 ^ 40 * 542016 * 2
def baseEnd_542016 : Nat := 185543153618304395738213

theorem tailTrace_542016 : CollatzResearch.WordTrace tailWord_542016 prefixEnd_542016 185543153618304395738213 := by
  unfold tailWord_542016
  simp only [CollatzResearch.WordTrace]
  refine ⟨9884473802188037904058951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13179298402917383872078601 9884473802188037904058951)
  ·
    refine ⟨14826710703282056856088427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9884473802188037904058951 14826710703282056856088427)
    ·
      refine ⟨22240066054923085284132641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14826710703282056856088427 22240066054923085284132641)
      ·
        refine ⟨16680049541192313963099481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22240066054923085284132641 16680049541192313963099481)
        ·
          refine ⟨12510037155894235472324611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16680049541192313963099481 12510037155894235472324611)
          ·
            refine ⟨18765055733841353208486917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12510037155894235472324611 18765055733841353208486917)
            ·
              refine ⟨3518447950095253726591297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18765055733841353208486917 3518447950095253726591297)
              ·
                refine ⟨2638835962571440294943473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3518447950095253726591297 2638835962571440294943473)
                ·
                  refine ⟨1979126971928580221207605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2638835962571440294943473 1979126971928580221207605)
                  ·
                    refine ⟨185543153618304395738213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1979126971928580221207605 185543153618304395738213)
                    ·
                      rfl

theorem cell22_542016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 2, 2, 5].length) (baseStart_542016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_542016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_542016 prefixEnd_542016 := by exact prefixLift 542016
  have htrace : WordTrace (prefixWord ++ tailWord_542016) baseStart_542016 baseEnd_542016 := by
    simpa [prefixWord, tailWord_542016, baseEnd_542016] using wordTrace_append hprefix tailTrace_542016
  have hstable : (prefixWord ++ tailWord_542016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542016).length < 2 ^ (prefixWord ++ tailWord_542016).sum := by decide
  have hdescent : baseEnd_542016 < baseStart_542016 := by decide
  rcases family_descends (prefixWord ++ tailWord_542016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542048 : List Nat := [2, 1, 1, 3, 4, 1, 2, 1, 3, 4]
def baseStart_542048 : Nat := 118140960795 + 542048 * 2 ^ 59
def prefixEnd_542048 : Nat := 4983230072969 + 3 ^ 40 * 542048 * 2
def baseEnd_542048 : Nat := 185554107872266978938115

theorem tailTrace_542048 : CollatzResearch.WordTrace tailWord_542048 prefixEnd_542048 185554107872266978938115 := by
  unfold tailWord_542048
  simp only [CollatzResearch.WordTrace]
  refine ⟨9885057370130072636641399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13180076493506763515521865 9885057370130072636641399)
  ·
    refine ⟨14827586055195108954962099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9885057370130072636641399 14827586055195108954962099)
    ·
      refine ⟨22241379082792663432443149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14827586055195108954962099 22241379082792663432443149)
      ·
        refine ⟨8340517156047248787166181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22241379082792663432443149 8340517156047248787166181)
        ·
          refine ⟨1563846966758859147593659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8340517156047248787166181 1563846966758859147593659)
          ·
            refine ⟨2345770450138288721390489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1563846966758859147593659 2345770450138288721390489)
            ·
              refine ⟨1759327837603716541042867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2345770450138288721390489 1759327837603716541042867)
              ·
                refine ⟨2638991756405574811564301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1759327837603716541042867 2638991756405574811564301)
                ·
                  refine ⟨989621908652090554336613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2638991756405574811564301 989621908652090554336613)
                  ·
                    refine ⟨185554107872266978938115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 989621908652090554336613 185554107872266978938115)
                    ·
                      rfl

theorem cell22_542048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 1, 3, 4].length) (baseStart_542048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_542048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_542048 prefixEnd_542048 := by exact prefixLift 542048
  have htrace : WordTrace (prefixWord ++ tailWord_542048) baseStart_542048 baseEnd_542048 := by
    simpa [prefixWord, tailWord_542048, baseEnd_542048] using wordTrace_append hprefix tailTrace_542048
  have hstable : (prefixWord ++ tailWord_542048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542048).length < 2 ^ (prefixWord ++ tailWord_542048).sum := by decide
  have hdescent : baseEnd_542048 < baseStart_542048 := by decide
  rcases family_descends (prefixWord ++ tailWord_542048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542065 : List Nat := [1, 2, 2, 2, 1, 2, 6, 1, 1, 4]
def baseStart_542065 : Nat := 118140960795 + 542065 * 2 ^ 59
def prefixEnd_542065 : Nat := 4983230072969 + 3 ^ 40 * 542065 * 2
def baseEnd_542065 : Nat := 185559927319684601263063

theorem tailTrace_542065 : CollatzResearch.WordTrace tailWord_542065 prefixEnd_542065 185559927319684601263063 := by
  unfold tailWord_542065
  simp only [CollatzResearch.WordTrace]
  refine ⟨19770734781198557176651649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13180489854132371451101099 19770734781198557176651649)
  ·
    refine ⟨14828051085898917882488737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19770734781198557176651649 14828051085898917882488737)
    ·
      refine ⟨11121038314424188411866553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14828051085898917882488737 11121038314424188411866553)
      ·
        refine ⟨8340778735818141308899915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11121038314424188411866553 8340778735818141308899915)
        ·
          refine ⟨12511168103727211963349873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8340778735818141308899915 12511168103727211963349873)
          ·
            refine ⟨9383376077795408972512405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12511168103727211963349873 9383376077795408972512405)
            ·
              refine ⟨439845753646659795586519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 9383376077795408972512405 439845753646659795586519)
              ·
                refine ⟨659768630469989693379779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 439845753646659795586519 659768630469989693379779)
                ·
                  refine ⟨989652945704984540069669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 659768630469989693379779 989652945704984540069669)
                  ·
                    refine ⟨185559927319684601263063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 989652945704984540069669 185559927319684601263063)
                    ·
                      rfl

theorem cell22_542065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 6, 1, 1, 4].length) (baseStart_542065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_542065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_542065 prefixEnd_542065 := by exact prefixLift 542065
  have htrace : WordTrace (prefixWord ++ tailWord_542065) baseStart_542065 baseEnd_542065 := by
    simpa [prefixWord, tailWord_542065, baseEnd_542065] using wordTrace_append hprefix tailTrace_542065
  have hstable : (prefixWord ++ tailWord_542065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542065).length < 2 ^ (prefixWord ++ tailWord_542065).sum := by decide
  have hdescent : baseEnd_542065 < baseStart_542065 := by decide
  rcases family_descends (prefixWord ++ tailWord_542065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542091 : List Nat := [1, 1, 1, 1, 4, 3, 2, 9]
def baseStart_542091 : Nat := 118140960795 + 542091 * 2 ^ 59
def prefixEnd_542091 : Nat := 4983230072969 + 3 ^ 40 * 542091 * 2
def baseEnd_542091 : Nat := 20618758627892133345887

theorem tailTrace_542091 : CollatzResearch.WordTrace tailWord_542091 prefixEnd_542091 20618758627892133345887 := by
  unfold tailWord_542091
  simp only [CollatzResearch.WordTrace]
  refine ⟨19771683079104363617098127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13181122052736242411398751 19771683079104363617098127)
  ·
    refine ⟨29657524618656545425647191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19771683079104363617098127 29657524618656545425647191)
    ·
      refine ⟨44486286927984818138470787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29657524618656545425647191 44486286927984818138470787)
      ·
        refine ⟨66729430391977227207706181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44486286927984818138470787 66729430391977227207706181)
        ·
          refine ⟨12511768198495730101444909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 66729430391977227207706181 12511768198495730101444909)
          ·
            refine ⟨4691913074435898788041841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12511768198495730101444909 4691913074435898788041841)
            ·
              refine ⟨3518934805826924091031381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4691913074435898788041841 3518934805826924091031381)
              ·
                refine ⟨20618758627892133345887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3518934805826924091031381 20618758627892133345887)
                ·
                  rfl

theorem cell22_542091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 9].length) (baseStart_542091 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_542091 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_542091 prefixEnd_542091 := by exact prefixLift 542091
  have htrace : WordTrace (prefixWord ++ tailWord_542091) baseStart_542091 baseEnd_542091 := by
    simpa [prefixWord, tailWord_542091, baseEnd_542091] using wordTrace_append hprefix tailTrace_542091
  have hstable : (prefixWord ++ tailWord_542091).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542091).length < 2 ^ (prefixWord ++ tailWord_542091).sum := by decide
  have hdescent : baseEnd_542091 < baseStart_542091 := by decide
  rcases family_descends (prefixWord ++ tailWord_542091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542121 : List Nat := [1, 2, 1, 1, 1, 1, 3, 1, 3, 8]
def baseStart_542121 : Nat := 118140960795 + 542121 * 2 ^ 59
def prefixEnd_542121 : Nat := 4983230072969 + 3 ^ 40 * 542121 * 2
def baseEnd_542121 : Nat := 185579097264119121862891

theorem tailTrace_542121 : CollatzResearch.WordTrace tailWord_542121 prefixEnd_542121 185579097264119121862891 := by
  unfold tailWord_542121
  simp only [CollatzResearch.WordTrace]
  refine ⟨19772777268995678740690217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13181851512663785827126811 19772777268995678740690217)
  ·
    refine ⟨14829582951746759055517663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19772777268995678740690217 14829582951746759055517663)
    ·
      refine ⟨22244374427620138583276495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14829582951746759055517663 22244374427620138583276495)
      ·
        refine ⟨33366561641430207874914743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22244374427620138583276495 33366561641430207874914743)
        ·
          refine ⟨50049842462145311812372115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33366561641430207874914743 50049842462145311812372115)
          ·
            refine ⟨75074763693217967718558173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50049842462145311812372115 75074763693217967718558173)
            ·
              refine ⟨28153036384956737894459315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 75074763693217967718558173 28153036384956737894459315)
              ·
                refine ⟨42229554577435106841688973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28153036384956737894459315 42229554577435106841688973)
                ·
                  refine ⟨15836082966538165065633365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42229554577435106841688973 15836082966538165065633365)
                  ·
                    refine ⟨185579097264119121862891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 15836082966538165065633365 185579097264119121862891)
                    ·
                      rfl

theorem cell22_542121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 8].length) (baseStart_542121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_542121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_542121 prefixEnd_542121 := by exact prefixLift 542121
  have htrace : WordTrace (prefixWord ++ tailWord_542121) baseStart_542121 baseEnd_542121 := by
    simpa [prefixWord, tailWord_542121, baseEnd_542121] using wordTrace_append hprefix tailTrace_542121
  have hstable : (prefixWord ++ tailWord_542121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542121).length < 2 ^ (prefixWord ++ tailWord_542121).sum := by decide
  have hdescent : baseEnd_542121 < baseStart_542121 := by decide
  rcases family_descends (prefixWord ++ tailWord_542121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542125 : List Nat := [1, 5, 2, 2, 1, 3, 8]
def baseStart_542125 : Nat := 118140960795 + 542125 * 2 ^ 59
def prefixEnd_542125 : Nat := 4983230072969 + 3 ^ 40 * 542125 * 2
def baseEnd_542125 : Nat := 6873350612809794250477

theorem tailTrace_542125 : CollatzResearch.WordTrace tailWord_542125 prefixEnd_542125 6873350612809794250477 := by
  unfold tailWord_542125
  simp only [CollatzResearch.WordTrace]
  refine ⟨19772923160981187423835829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13181948773987458282557219 19772923160981187423835829)
  ·
    refine ⟨1853711546341986320984609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19772923160981187423835829 1853711546341986320984609)
    ·
      refine ⟨1390283659756489740738457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1853711546341986320984609 1390283659756489740738457)
      ·
        refine ⟨1042712744817367305553843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1390283659756489740738457 1042712744817367305553843)
        ·
          refine ⟨1564069117226050958330765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1042712744817367305553843 1564069117226050958330765)
          ·
            refine ⟨586525918959769109374037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1564069117226050958330765 586525918959769109374037)
            ·
              refine ⟨6873350612809794250477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 586525918959769109374037 6873350612809794250477)
              ·
                rfl

theorem cell22_542125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 8].length) (baseStart_542125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_542125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_542125 prefixEnd_542125 := by exact prefixLift 542125
  have htrace : WordTrace (prefixWord ++ tailWord_542125) baseStart_542125 baseEnd_542125 := by
    simpa [prefixWord, tailWord_542125, baseEnd_542125] using wordTrace_append hprefix tailTrace_542125
  have hstable : (prefixWord ++ tailWord_542125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542125).length < 2 ^ (prefixWord ++ tailWord_542125).sum := by decide
  have hdescent : baseEnd_542125 < baseStart_542125 := by decide
  rcases family_descends (prefixWord ++ tailWord_542125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542215 : List Nat := [1, 1, 4, 3, 2, 2, 1, 2, 6]
def baseStart_542215 : Nat := 118140960795 + 542215 * 2 ^ 59
def prefixEnd_542215 : Nat := 4983230072969 + 3 ^ 40 * 542215 * 2
def baseEnd_542215 : Nat := 61870425128378070004201

theorem tailTrace_542215 : CollatzResearch.WordTrace tailWord_542215 prefixEnd_542215 61870425128378070004201 := by
  unfold tailWord_542215
  simp only [CollatzResearch.WordTrace]
  refine ⟨19776205730655132794612099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13184137153770088529741399 19776205730655132794612099)
  ·
    refine ⟨29664308595982699191918149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19776205730655132794612099 29664308595982699191918149)
    ·
      refine ⟨5562057861746756098484653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29664308595982699191918149 5562057861746756098484653)
      ·
        refine ⟨2085771698155033536931745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5562057861746756098484653 2085771698155033536931745)
        ·
          refine ⟨1564328773616275152698809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2085771698155033536931745 1564328773616275152698809)
          ·
            refine ⟨1173246580212206364524107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1564328773616275152698809 1173246580212206364524107)
            ·
              refine ⟨1759869870318309546786161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1173246580212206364524107 1759869870318309546786161)
              ·
                refine ⟨1319902402738732160089621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1759869870318309546786161 1319902402738732160089621)
                ·
                  refine ⟨61870425128378070004201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1319902402738732160089621 61870425128378070004201)
                  ·
                    rfl

theorem cell22_542215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 2, 6].length) (baseStart_542215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_542215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_542215 prefixEnd_542215 := by exact prefixLift 542215
  have htrace : WordTrace (prefixWord ++ tailWord_542215) baseStart_542215 baseEnd_542215 := by
    simpa [prefixWord, tailWord_542215, baseEnd_542215] using wordTrace_append hprefix tailTrace_542215
  have hstable : (prefixWord ++ tailWord_542215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542215).length < 2 ^ (prefixWord ++ tailWord_542215).sum := by decide
  have hdescent : baseEnd_542215 < baseStart_542215 := by decide
  rcases family_descends (prefixWord ++ tailWord_542215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542238 : List Nat := [4, 3, 3, 1, 1, 2, 1, 2, 5]
def baseStart_542238 : Nat := 118140960795 + 542238 * 2 ^ 59
def prefixEnd_542238 : Nat := 4983230072969 + 3 ^ 40 * 542238 * 2
def baseEnd_542238 : Nat := 61873049585056605562511

theorem tailTrace_542238 : CollatzResearch.WordTrace tailWord_542238 prefixEnd_542238 61873049585056605562511 := by
  unfold tailWord_542238
  simp only [CollatzResearch.WordTrace]
  refine ⟨2472130576196475965337421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13184696406381205148466245 2472130576196475965337421)
  ·
    refine ⟨927048966073678487001533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2472130576196475965337421 927048966073678487001533)
    ·
      refine ⟨347643362277629432625575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 927048966073678487001533 347643362277629432625575)
      ·
        refine ⟨521465043416444148938363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 347643362277629432625575 521465043416444148938363)
        ·
          refine ⟨782197565124666223407545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 521465043416444148938363 782197565124666223407545)
          ·
            refine ⟨586648173843499667555659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 782197565124666223407545 586648173843499667555659)
            ·
              refine ⟨879972260765249501333489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 586648173843499667555659 879972260765249501333489)
              ·
                refine ⟨659979195573937126000117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 879972260765249501333489 659979195573937126000117)
                ·
                  refine ⟨61873049585056605562511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 659979195573937126000117 61873049585056605562511)
                  ·
                    rfl

theorem cell22_542238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 1, 2, 5].length) (baseStart_542238 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_542238 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_542238 prefixEnd_542238 := by exact prefixLift 542238
  have htrace : WordTrace (prefixWord ++ tailWord_542238) baseStart_542238 baseEnd_542238 := by
    simpa [prefixWord, tailWord_542238, baseEnd_542238] using wordTrace_append hprefix tailTrace_542238
  have hstable : (prefixWord ++ tailWord_542238).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542238).length < 2 ^ (prefixWord ++ tailWord_542238).sum := by decide
  have hdescent : baseEnd_542238 < baseStart_542238 := by decide
  rcases family_descends (prefixWord ++ tailWord_542238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542264 : List Nat := [2, 1, 2, 1, 4, 3, 3, 1, 2, 3]
def baseStart_542264 : Nat := 118140960795 + 542264 * 2 ^ 59
def prefixEnd_542264 : Nat := 4983230072969 + 3 ^ 40 * 542264 * 2
def baseEnd_542264 : Nat := 185628049086514415537453

theorem tailTrace_542264 : CollatzResearch.WordTrace tailWord_542264 prefixEnd_542264 185628049086514415537453 := by
  unfold tailWord_542264
  simp only [CollatzResearch.WordTrace]
  refine ⟨9888996453738807081572923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13185328604985076108763897 9888996453738807081572923)
  ·
    refine ⟨14833494680608210622359385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9888996453738807081572923 14833494680608210622359385)
    ·
      refine ⟨11125121010456157966769539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14833494680608210622359385 11125121010456157966769539)
      ·
        refine ⟨16687681515684236950154309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11125121010456157966769539 16687681515684236950154309)
        ·
          refine ⟨3128940284190794428153933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16687681515684236950154309 3128940284190794428153933)
          ·
            refine ⟨1173352606571547910557725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3128940284190794428153933 1173352606571547910557725)
            ·
              refine ⟨440007227464330466459147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1173352606571547910557725 440007227464330466459147)
              ·
                refine ⟨660010841196495699688721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 440007227464330466459147 660010841196495699688721)
                ·
                  refine ⟨495008130897371774766541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 660010841196495699688721 495008130897371774766541)
                  ·
                    refine ⟨185628049086514415537453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 495008130897371774766541 185628049086514415537453)
                    ·
                      rfl

theorem cell22_542264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 3, 1, 2, 3].length) (baseStart_542264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_542264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_542264 prefixEnd_542264 := by exact prefixLift 542264
  have htrace : WordTrace (prefixWord ++ tailWord_542264) baseStart_542264 baseEnd_542264 := by
    simpa [prefixWord, tailWord_542264, baseEnd_542264] using wordTrace_append hprefix tailTrace_542264
  have hstable : (prefixWord ++ tailWord_542264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542264).length < 2 ^ (prefixWord ++ tailWord_542264).sum := by decide
  have hdescent : baseEnd_542264 < baseStart_542264 := by decide
  rcases family_descends (prefixWord ++ tailWord_542264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542288 : List Nat := [2, 1, 1, 1, 1, 3, 3, 1, 9]
def baseStart_542288 : Nat := 118140960795 + 542288 * 2 ^ 59
def prefixEnd_542288 : Nat := 4983230072969 + 3 ^ 40 * 542288 * 2
def baseEnd_542288 : Nat := 61878754925662117645793

theorem tailTrace_542288 : CollatzResearch.WordTrace tailWord_542288 prefixEnd_542288 61878754925662117645793 := by
  unfold tailWord_542288
  simp only [CollatzResearch.WordTrace]
  refine ⟨9889434129695333131009759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13185912172927110841346345 9889434129695333131009759)
  ·
    refine ⟨14834151194542999696514639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9889434129695333131009759 14834151194542999696514639)
    ·
      refine ⟨22251226791814499544771959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14834151194542999696514639 22251226791814499544771959)
      ·
        refine ⟨33376840187721749317157939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22251226791814499544771959 33376840187721749317157939)
        ·
          refine ⟨50065260281582623975736909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33376840187721749317157939 50065260281582623975736909)
          ·
            refine ⟨18774472605593483990901341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50065260281582623975736909 18774472605593483990901341)
            ·
              refine ⟨7040427227097556496588003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18774472605593483990901341 7040427227097556496588003)
              ·
                refine ⟨10560640840646334744882005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7040427227097556496588003 10560640840646334744882005)
                ·
                  refine ⟨61878754925662117645793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 10560640840646334744882005 61878754925662117645793)
                  ·
                    rfl

theorem cell22_542288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 9].length) (baseStart_542288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_542288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_542288 prefixEnd_542288 := by exact prefixLift 542288
  have htrace : WordTrace (prefixWord ++ tailWord_542288) baseStart_542288 baseEnd_542288 := by
    simpa [prefixWord, tailWord_542288, baseEnd_542288] using wordTrace_append hprefix tailTrace_542288
  have hstable : (prefixWord ++ tailWord_542288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542288).length < 2 ^ (prefixWord ++ tailWord_542288).sum := by decide
  have hdescent : baseEnd_542288 < baseStart_542288 := by decide
  rcases family_descends (prefixWord ++ tailWord_542288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542305 : List Nat := [1, 2, 3, 1, 1, 3, 2, 4, 5]
def baseStart_542305 : Nat := 118140960795 + 542305 * 2 ^ 59
def prefixEnd_542305 : Nat := 4983230072969 + 3 ^ 40 * 542305 * 2
def baseEnd_542305 : Nat := 61880694741467991754109

theorem tailTrace_542305 : CollatzResearch.WordTrace tailWord_542305 prefixEnd_542305 61880694741467991754109 := by
  unfold tailWord_542305
  simp only [CollatzResearch.WordTrace]
  refine ⟨19779488300329078165388369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13186325533552718776925579 19779488300329078165388369)
  ·
    refine ⟨14834616225246808624041277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19779488300329078165388369 14834616225246808624041277)
    ·
      refine ⟨5562981084467553234015479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14834616225246808624041277 5562981084467553234015479)
      ·
        refine ⟨8344471626701329851023219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5562981084467553234015479 8344471626701329851023219)
        ·
          refine ⟨12516707440051994776534829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8344471626701329851023219 12516707440051994776534829)
          ·
            refine ⟨4693765290019498041200561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12516707440051994776534829 4693765290019498041200561)
            ·
              refine ⟨3520323967514623530900421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4693765290019498041200561 3520323967514623530900421)
              ·
                refine ⟨660060743908991912043829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3520323967514623530900421 660060743908991912043829)
                ·
                  refine ⟨61880694741467991754109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 660060743908991912043829 61880694741467991754109)
                  ·
                    rfl

theorem cell22_542305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 4, 5].length) (baseStart_542305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_542305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_542305 prefixEnd_542305 := by exact prefixLift 542305
  have htrace : WordTrace (prefixWord ++ tailWord_542305) baseStart_542305 baseEnd_542305 := by
    simpa [prefixWord, tailWord_542305, baseEnd_542305] using wordTrace_append hprefix tailTrace_542305
  have hstable : (prefixWord ++ tailWord_542305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542305).length < 2 ^ (prefixWord ++ tailWord_542305).sum := by decide
  have hdescent : baseEnd_542305 < baseStart_542305 := by decide
  rcases family_descends (prefixWord ++ tailWord_542305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542309 : List Nat := [1, 3, 1, 3, 3, 3, 1, 1, 3, 3]
def baseStart_542309 : Nat := 118140960795 + 542309 * 2 ^ 59
def prefixEnd_542309 : Nat := 4983230072969 + 3 ^ 40 * 542309 * 2
def baseEnd_542309 : Nat := 185643453506149298162315

theorem tailTrace_542309 : CollatzResearch.WordTrace tailWord_542309 prefixEnd_542309 185643453506149298162315 := by
  unfold tailWord_542309
  simp only [CollatzResearch.WordTrace]
  refine ⟨19779634192314586848533981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13186422794876391232355987 19779634192314586848533981)
  ·
    refine ⟨7417362822117970068200243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19779634192314586848533981 7417362822117970068200243)
    ·
      refine ⟨11126044233176955102300365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7417362822117970068200243 11126044233176955102300365)
      ·
        refine ⟨4172266587441358163362637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11126044233176955102300365 4172266587441358163362637)
        ·
          refine ⟨1564599970290509311260989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4172266587441358163362637 1564599970290509311260989)
          ·
            refine ⟨586724988858940991722871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1564599970290509311260989 586724988858940991722871)
            ·
              refine ⟨880087483288411487584307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 586724988858940991722871 880087483288411487584307)
              ·
                refine ⟨1320131224932617231376461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 880087483288411487584307 1320131224932617231376461)
                ·
                  refine ⟨495049209349731461766173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1320131224932617231376461 495049209349731461766173)
                  ·
                    refine ⟨185643453506149298162315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 495049209349731461766173 185643453506149298162315)
                    ·
                      rfl

theorem cell22_542309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 1, 1, 3, 3].length) (baseStart_542309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_542309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_542309 prefixEnd_542309 := by exact prefixLift 542309
  have htrace : WordTrace (prefixWord ++ tailWord_542309) baseStart_542309 baseEnd_542309 := by
    simpa [prefixWord, tailWord_542309, baseEnd_542309] using wordTrace_append hprefix tailTrace_542309
  have hstable : (prefixWord ++ tailWord_542309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542309).length < 2 ^ (prefixWord ++ tailWord_542309).sum := by decide
  have hdescent : baseEnd_542309 < baseStart_542309 := by decide
  rcases family_descends (prefixWord ++ tailWord_542309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542322 : List Nat := [3, 2, 1, 2, 3, 2, 1, 3, 5]
def baseStart_542322 : Nat := 118140960795 + 542322 * 2 ^ 59
def prefixEnd_542322 : Nat := 4983230072969 + 3 ^ 40 * 542322 * 2
def baseEnd_542322 : Nat := 61882634557273865862425

theorem tailTrace_542322 : CollatzResearch.WordTrace tailWord_542322 prefixEnd_542322 61882634557273865862425 := by
  unfold tailWord_542322
  simp only [CollatzResearch.WordTrace]
  refine ⟨4945027085316872517189305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13186738894178326712504813 4945027085316872517189305)
  ·
    refine ⟨3708770313987654387891979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4945027085316872517189305 3708770313987654387891979)
    ·
      refine ⟨5563155470981481581837969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3708770313987654387891979 5563155470981481581837969)
      ·
        refine ⟨4172366603236111186378477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5563155470981481581837969 4172366603236111186378477)
        ·
          refine ⟨1564637476213541694891929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4172366603236111186378477 1564637476213541694891929)
          ·
            refine ⟨1173478107160156271168947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1564637476213541694891929 1173478107160156271168947)
            ·
              refine ⟨1760217160740234406753421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1173478107160156271168947 1760217160740234406753421)
              ·
                refine ⟨660081435277587902532533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1760217160740234406753421 660081435277587902532533)
                ·
                  refine ⟨61882634557273865862425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 660081435277587902532533 61882634557273865862425)
                  ·
                    rfl

theorem cell22_542322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 3, 5].length) (baseStart_542322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_542322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_542322 prefixEnd_542322 := by exact prefixLift 542322
  have htrace : WordTrace (prefixWord ++ tailWord_542322) baseStart_542322 baseEnd_542322 := by
    simpa [prefixWord, tailWord_542322, baseEnd_542322] using wordTrace_append hprefix tailTrace_542322
  have hstable : (prefixWord ++ tailWord_542322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542322).length < 2 ^ (prefixWord ++ tailWord_542322).sum := by decide
  have hdescent : baseEnd_542322 < baseStart_542322 := by decide
  rcases family_descends (prefixWord ++ tailWord_542322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542365 : List Nat := [1, 4, 2, 1, 1, 1, 1, 1, 5, 5]
def baseStart_542365 : Nat := 118140960795 + 542365 * 2 ^ 59
def prefixEnd_542365 : Nat := 4983230072969 + 3 ^ 40 * 542365 * 2
def baseEnd_542365 : Nat := 185662623450583818762143

theorem tailTrace_542365 : CollatzResearch.WordTrace tailWord_542365 prefixEnd_542365 185662623450583818762143 := by
  unfold tailWord_542365
  simp only [CollatzResearch.WordTrace]
  refine ⟨19781676680111708412572549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13187784453407805608381699 19781676680111708412572549)
  ·
    refine ⟨3709064377520945327357353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19781676680111708412572549 3709064377520945327357353)
    ·
      refine ⟨2781798283140708995518015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3709064377520945327357353 2781798283140708995518015)
      ·
        refine ⟨4172697424711063493277023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2781798283140708995518015 4172697424711063493277023)
        ·
          refine ⟨6259046137066595239915535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4172697424711063493277023 6259046137066595239915535)
          ·
            refine ⟨9388569205599892859873303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6259046137066595239915535 9388569205599892859873303)
            ·
              refine ⟨14082853808399839289809955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9388569205599892859873303 14082853808399839289809955)
              ·
                refine ⟨21124280712599758934714933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14082853808399839289809955 21124280712599758934714933)
                ·
                  refine ⟨1980401316806227400129525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21124280712599758934714933 1980401316806227400129525)
                  ·
                    refine ⟨185662623450583818762143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1980401316806227400129525 185662623450583818762143)
                    ·
                      rfl

theorem cell22_542365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 5, 5].length) (baseStart_542365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_542365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_542365 prefixEnd_542365 := by exact prefixLift 542365
  have htrace : WordTrace (prefixWord ++ tailWord_542365) baseStart_542365 baseEnd_542365 := by
    simpa [prefixWord, tailWord_542365, baseEnd_542365] using wordTrace_append hprefix tailTrace_542365
  have hstable : (prefixWord ++ tailWord_542365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542365).length < 2 ^ (prefixWord ++ tailWord_542365).sum := by decide
  have hdescent : baseEnd_542365 < baseStart_542365 := by decide
  rcases family_descends (prefixWord ++ tailWord_542365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542412 : List Nat := [2, 2, 1, 5, 2, 1, 9]
def baseStart_542412 : Nat := 118140960795 + 542412 * 2 ^ 59
def prefixEnd_542412 : Nat := 4983230072969 + 3 ^ 40 * 542412 * 2
def baseEnd_542412 : Nat := 6876989352262643068037

theorem tailTrace_542412 : CollatzResearch.WordTrace tailWord_542412 prefixEnd_542412 6876989352262643068037 := by
  unfold tailWord_542412
  simp only [CollatzResearch.WordTrace]
  refine ⟨9891695455470717719766745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13188927273960956959688993 9891695455470717719766745)
  ·
    refine ⟨7418771591603038289825059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9891695455470717719766745 7418771591603038289825059)
    ·
      refine ⟨11128157387404557434737589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7418771591603038289825059 11128157387404557434737589)
      ·
        refine ⟨1043264755069177259506649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11128157387404557434737589 1043264755069177259506649)
        ·
          refine ⟨782448566301882944629987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1043264755069177259506649 782448566301882944629987)
          ·
            refine ⟨1173672849452824416944981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 782448566301882944629987 1173672849452824416944981)
            ·
              refine ⟨6876989352262643068037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1173672849452824416944981 6876989352262643068037)
              ·
                rfl

theorem cell22_542412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 9].length) (baseStart_542412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_542412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_542412 prefixEnd_542412 := by exact prefixLift 542412
  have htrace : WordTrace (prefixWord ++ tailWord_542412) baseStart_542412 baseEnd_542412 := by
    simpa [prefixWord, tailWord_542412, baseEnd_542412] using wordTrace_append hprefix tailTrace_542412
  have hstable : (prefixWord ++ tailWord_542412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542412).length < 2 ^ (prefixWord ++ tailWord_542412).sum := by decide
  have hdescent : baseEnd_542412 < baseStart_542412 := by decide
  rcases family_descends (prefixWord ++ tailWord_542412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542455 : List Nat := [1, 1, 3, 1, 1, 1, 4, 2, 1, 7]
def baseStart_542455 : Nat := 118140960795 + 542455 * 2 ^ 59
def prefixEnd_542455 : Nat := 4983230072969 + 3 ^ 40 * 542455 * 2
def baseEnd_542455 : Nat := 185693432289853584011867

theorem tailTrace_542455 : CollatzResearch.WordTrace tailWord_542455 prefixEnd_542455 185693432289853584011867 := by
  unfold tailWord_542455
  simp only [CollatzResearch.WordTrace]
  refine ⟨19784959249785653783348819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13189972833190435855565879 19784959249785653783348819)
  ·
    refine ⟨29677438874678480675023229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19784959249785653783348819 29677438874678480675023229)
    ·
      refine ⟨11129039578004430253133711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29677438874678480675023229 11129039578004430253133711)
      ·
        refine ⟨16693559367006645379700567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11129039578004430253133711 16693559367006645379700567)
        ·
          refine ⟨25040339050509968069550851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16693559367006645379700567 25040339050509968069550851)
          ·
            refine ⟨37560508575764952104326277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25040339050509968069550851 37560508575764952104326277)
            ·
              refine ⟨7042595357955928519561177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37560508575764952104326277 7042595357955928519561177)
              ·
                refine ⟨5281946518466946389670883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7042595357955928519561177 5281946518466946389670883)
                ·
                  refine ⟨7922919777700419584506325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5281946518466946389670883 7922919777700419584506325)
                  ·
                    refine ⟨185693432289853584011867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7922919777700419584506325 185693432289853584011867)
                    ·
                      rfl

theorem cell22_542455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 2, 1, 7].length) (baseStart_542455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_542455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_542455 prefixEnd_542455 := by exact prefixLift 542455
  have htrace : WordTrace (prefixWord ++ tailWord_542455) baseStart_542455 baseEnd_542455 := by
    simpa [prefixWord, tailWord_542455, baseEnd_542455] using wordTrace_append hprefix tailTrace_542455
  have hstable : (prefixWord ++ tailWord_542455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542455).length < 2 ^ (prefixWord ++ tailWord_542455).sum := by decide
  have hdescent : baseEnd_542455 < baseStart_542455 := by decide
  rcases family_descends (prefixWord ++ tailWord_542455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542484 : List Nat := [2, 4, 4, 1, 2, 1, 2, 1, 2, 3]
def baseStart_542484 : Nat := 118140960795 + 542484 * 2 ^ 59
def prefixEnd_542484 : Nat := 4983230072969 + 3 ^ 40 * 542484 * 2
def baseEnd_542484 : Nat := 185703359582507175036779

theorem tailTrace_542484 : CollatzResearch.WordTrace tailWord_542484 prefixEnd_542484 185703359582507175036779 := by
  unfold tailWord_542484
  simp only [CollatzResearch.WordTrace]
  refine ⟨9893008483340295868077253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13190677977787061157436337 9893008483340295868077253)
  ·
    refine ⟨1854939090626305475264485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9893008483340295868077253 1854939090626305475264485)
    ·
      refine ⟨347801079492432276612091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1854939090626305475264485 347801079492432276612091)
      ·
        refine ⟨521701619238648414918137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 347801079492432276612091 521701619238648414918137)
        ·
          refine ⟨391276214428986311188603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 521701619238648414918137 391276214428986311188603)
          ·
            refine ⟨586914321643479466782905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 391276214428986311188603 586914321643479466782905)
            ·
              refine ⟨440185741232609600087179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 586914321643479466782905 440185741232609600087179)
              ·
                refine ⟨660278611848914400130769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 440185741232609600087179 660278611848914400130769)
                ·
                  refine ⟨495208958886685800098077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 660278611848914400130769 495208958886685800098077)
                  ·
                    refine ⟨185703359582507175036779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 495208958886685800098077 185703359582507175036779)
                    ·
                      rfl

theorem cell22_542484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_542484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_542484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_542484 prefixEnd_542484 := by exact prefixLift 542484
  have htrace : WordTrace (prefixWord ++ tailWord_542484) baseStart_542484 baseEnd_542484 := by
    simpa [prefixWord, tailWord_542484, baseEnd_542484] using wordTrace_append hprefix tailTrace_542484
  have hstable : (prefixWord ++ tailWord_542484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542484).length < 2 ^ (prefixWord ++ tailWord_542484).sum := by decide
  have hdescent : baseEnd_542484 < baseStart_542484 := by decide
  rcases family_descends (prefixWord ++ tailWord_542484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542504 : List Nat := [2, 1, 5, 1, 1, 3, 1, 1, 3, 4]
def baseStart_542504 : Nat := 118140960795 + 542504 * 2 ^ 59
def prefixEnd_542504 : Nat := 4983230072969 + 3 ^ 40 * 542504 * 2
def baseEnd_542504 : Nat := 185710205991233789536717

theorem tailTrace_542504 : CollatzResearch.WordTrace tailWord_542504 prefixEnd_542504 185710205991233789536717 := by
  unfold tailWord_542504
  simp only [CollatzResearch.WordTrace]
  refine ⟨9893373213304067575941283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13191164284405423434588377 9893373213304067575941283)
  ·
    refine ⟨14840059819956101363911925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9893373213304067575941283 14840059819956101363911925)
    ·
      refine ⟨1391255608120884502866743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14840059819956101363911925 1391255608120884502866743)
      ·
        refine ⟨2086883412181326754300115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1391255608120884502866743 2086883412181326754300115)
        ·
          refine ⟨3130325118271990131450173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2086883412181326754300115 3130325118271990131450173)
          ·
            refine ⟨1173871919351996299293815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3130325118271990131450173 1173871919351996299293815)
            ·
              refine ⟨1760807879027994448940723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1173871919351996299293815 1760807879027994448940723)
              ·
                refine ⟨2641211818541991673411085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1760807879027994448940723 2641211818541991673411085)
                ·
                  refine ⟨990454431953246877529157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2641211818541991673411085 990454431953246877529157)
                  ·
                    refine ⟨185710205991233789536717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 990454431953246877529157 185710205991233789536717)
                    ·
                      rfl

theorem cell22_542504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_542504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_542504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_542504 prefixEnd_542504 := by exact prefixLift 542504
  have htrace : WordTrace (prefixWord ++ tailWord_542504) baseStart_542504 baseEnd_542504 := by
    simpa [prefixWord, tailWord_542504, baseEnd_542504] using wordTrace_append hprefix tailTrace_542504
  have hstable : (prefixWord ++ tailWord_542504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542504).length < 2 ^ (prefixWord ++ tailWord_542504).sum := by decide
  have hdescent : baseEnd_542504 < baseStart_542504 := by decide
  rcases family_descends (prefixWord ++ tailWord_542504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542536 : List Nat := [2, 1, 3, 1, 1, 4, 4, 2, 4]
def baseStart_542536 : Nat := 118140960795 + 542536 * 2 ^ 59
def prefixEnd_542536 : Nat := 4983230072969 + 3 ^ 40 * 542536 * 2
def baseEnd_542536 : Nat := 61907053415065457578873

theorem tailTrace_542536 : CollatzResearch.WordTrace tailWord_542536 prefixEnd_542536 61907053415065457578873 := by
  unfold tailWord_542536
  simp only [CollatzResearch.WordTrace]
  refine ⟨9893956781246102308523731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13191942374994803078031641 9893956781246102308523731)
  ·
    refine ⟨14840935171869153462785597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9893956781246102308523731 14840935171869153462785597)
    ·
      refine ⟨5565350689450932548544599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14840935171869153462785597 5565350689450932548544599)
      ·
        refine ⟨8348026034176398822816899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5565350689450932548544599 8348026034176398822816899)
        ·
          refine ⟨12522039051264598234225349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8348026034176398822816899 12522039051264598234225349)
          ·
            refine ⟨2347882322112112168917253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12522039051264598234225349 2347882322112112168917253)
            ·
              refine ⟨440227935396021031671985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2347882322112112168917253 440227935396021031671985)
              ·
                refine ⟨330170951547015773753989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 440227935396021031671985 330170951547015773753989)
                ·
                  refine ⟨61907053415065457578873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 330170951547015773753989 61907053415065457578873)
                  ·
                    rfl

theorem cell22_542536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 4, 2, 4].length) (baseStart_542536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_542536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_542536 prefixEnd_542536 := by exact prefixLift 542536
  have htrace : WordTrace (prefixWord ++ tailWord_542536) baseStart_542536 baseEnd_542536 := by
    simpa [prefixWord, tailWord_542536, baseEnd_542536] using wordTrace_append hprefix tailTrace_542536
  have hstable : (prefixWord ++ tailWord_542536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542536).length < 2 ^ (prefixWord ++ tailWord_542536).sum := by decide
  have hdescent : baseEnd_542536 < baseStart_542536 := by decide
  rcases family_descends (prefixWord ++ tailWord_542536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542592 : List Nat := [2, 1, 1, 2, 1, 2, 5, 1, 7]
def baseStart_542592 : Nat := 118140960795 + 542592 * 2 ^ 59
def prefixEnd_542592 : Nat := 4983230072969 + 3 ^ 40 * 542592 * 2
def baseEnd_542592 : Nat := 61913443396543631112149

theorem tailTrace_542592 : CollatzResearch.WordTrace tailWord_542592 prefixEnd_542592 61913443396543631112149 := by
  unfold tailWord_542592
  simp only [CollatzResearch.WordTrace]
  refine ⟨9894978025144663090543015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13193304033526217454057353 9894978025144663090543015)
  ·
    refine ⟨14842467037716994635814523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9894978025144663090543015 14842467037716994635814523)
    ·
      refine ⟨22263700556575491953721785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14842467037716994635814523 22263700556575491953721785)
      ·
        refine ⟨16697775417431618965291339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22263700556575491953721785 16697775417431618965291339)
        ·
          refine ⟨25046663126147428447937009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16697775417431618965291339 25046663126147428447937009)
          ·
            refine ⟨18784997344610571335952757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25046663126147428447937009 18784997344610571335952757)
            ·
              refine ⟨1761093501057241062745571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18784997344610571335952757 1761093501057241062745571)
              ·
                refine ⟨2641640251585861594118357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1761093501057241062745571 2641640251585861594118357)
                ·
                  refine ⟨61913443396543631112149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2641640251585861594118357 61913443396543631112149)
                  ·
                    rfl

theorem cell22_542592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 1, 7].length) (baseStart_542592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_542592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_542592 prefixEnd_542592 := by exact prefixLift 542592
  have htrace : WordTrace (prefixWord ++ tailWord_542592) baseStart_542592 baseEnd_542592 := by
    simpa [prefixWord, tailWord_542592, baseEnd_542592] using wordTrace_append hprefix tailTrace_542592
  have hstable : (prefixWord ++ tailWord_542592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542592).length < 2 ^ (prefixWord ++ tailWord_542592).sum := by decide
  have hdescent : baseEnd_542592 < baseStart_542592 := by decide
  rcases family_descends (prefixWord ++ tailWord_542592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542639 : List Nat := [1, 1, 2, 1, 2, 2, 3, 5, 1, 4]
def baseStart_542639 : Nat := 118140960795 + 542639 * 2 ^ 59
def prefixEnd_542639 : Nat := 4983230072969 + 3 ^ 40 * 542639 * 2
def baseEnd_542639 : Nat := 185756419250138437411303

theorem tailTrace_542639 : CollatzResearch.WordTrace tailWord_542639 prefixEnd_542639 185756419250138437411303 := by
  unfold tailWord_542639
  simp only [CollatzResearch.WordTrace]
  refine ⟨19791670281119053208046971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13194446854079368805364647 19791670281119053208046971)
  ·
    refine ⟨29687505421678579812070457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19791670281119053208046971 29687505421678579812070457)
    ·
      refine ⟨22265629066258934859052843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29687505421678579812070457 22265629066258934859052843)
      ·
        refine ⟨33398443599388402288579265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22265629066258934859052843 33398443599388402288579265)
        ·
          refine ⟨25048832699541301716434449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33398443599388402288579265 25048832699541301716434449)
          ·
            refine ⟨18786624524655976287325837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25048832699541301716434449 18786624524655976287325837)
            ·
              refine ⟨7044984196745991107747189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18786624524655976287325837 7044984196745991107747189)
              ·
                refine ⟨660467268444936666351299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7044984196745991107747189 660467268444936666351299)
                ·
                  refine ⟨990700902667404999526949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 660467268444936666351299 990700902667404999526949)
                  ·
                    refine ⟨185756419250138437411303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 990700902667404999526949 185756419250138437411303)
                    ·
                      rfl

theorem cell22_542639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 5, 1, 4].length) (baseStart_542639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_542639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_542639 prefixEnd_542639 := by exact prefixLift 542639
  have htrace : WordTrace (prefixWord ++ tailWord_542639) baseStart_542639 baseEnd_542639 := by
    simpa [prefixWord, tailWord_542639, baseEnd_542639] using wordTrace_append hprefix tailTrace_542639
  have hstable : (prefixWord ++ tailWord_542639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542639).length < 2 ^ (prefixWord ++ tailWord_542639).sum := by decide
  have hdescent : baseEnd_542639 < baseStart_542639 := by decide
  rcases family_descends (prefixWord ++ tailWord_542639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542705 : List Nat := [1, 2, 2, 2, 5, 2, 2, 2, 4]
def baseStart_542705 : Nat := 118140960795 + 542705 * 2 ^ 59
def prefixEnd_542705 : Nat := 4983230072969 + 3 ^ 40 * 542705 * 2
def baseEnd_542705 : Nat := 61926337466312088420367

theorem tailTrace_542705 : CollatzResearch.WordTrace tailWord_542705 prefixEnd_542705 61926337466312088420367 := by
  unfold tailWord_542705
  simp only [CollatzResearch.WordTrace]
  refine ⟨19794077498879946479949569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13196051665919964319966379 19794077498879946479949569)
  ·
    refine ⟨14845558124159959859962177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19794077498879946479949569 14845558124159959859962177)
    ·
      refine ⟨11134168593119969894971633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14845558124159959859962177 11134168593119969894971633)
      ·
        refine ⟨8350626444839977421228725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11134168593119969894971633 8350626444839977421228725)
        ·
          refine ⟨782871229203747883240193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8350626444839977421228725 782871229203747883240193)
          ·
            refine ⟨587153421902810912430145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 782871229203747883240193 587153421902810912430145)
            ·
              refine ⟨440365066427108184322609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 587153421902810912430145 440365066427108184322609)
              ·
                refine ⟨330273799820331138241957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 440365066427108184322609 330273799820331138241957)
                ·
                  refine ⟨61926337466312088420367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 330273799820331138241957 61926337466312088420367)
                  ·
                    rfl

theorem cell22_542705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 2, 2, 4].length) (baseStart_542705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_542705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_542705 prefixEnd_542705 := by exact prefixLift 542705
  have htrace : WordTrace (prefixWord ++ tailWord_542705) baseStart_542705 baseEnd_542705 := by
    simpa [prefixWord, tailWord_542705, baseEnd_542705] using wordTrace_append hprefix tailTrace_542705
  have hstable : (prefixWord ++ tailWord_542705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542705).length < 2 ^ (prefixWord ++ tailWord_542705).sum := by decide
  have hdescent : baseEnd_542705 < baseStart_542705 := by decide
  rcases family_descends (prefixWord ++ tailWord_542705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542731 : List Nat := [1, 1, 1, 1, 6, 1, 3, 2, 3, 3]
def baseStart_542731 : Nat := 118140960795 + 542731 * 2 ^ 59
def prefixEnd_542731 : Nat := 4983230072969 + 3 ^ 40 * 542731 * 2
def baseEnd_542731 : Nat := 185787912730280864111021

theorem tailTrace_542731 : CollatzResearch.WordTrace tailWord_542731 prefixEnd_542731 185787912730280864111021 := by
  unfold tailWord_542731
  simp only [CollatzResearch.WordTrace]
  refine ⟨19795025796785752920396047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13196683864523835280264031 19795025796785752920396047)
  ·
    refine ⟨29692538695178629380594071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19795025796785752920396047 29692538695178629380594071)
    ·
      refine ⟨44538808042767944070891107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29692538695178629380594071 44538808042767944070891107)
      ·
        refine ⟨66808212064151916106336661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44538808042767944070891107 66808212064151916106336661)
        ·
          refine ⟨3131634940507121067484531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 66808212064151916106336661 3131634940507121067484531)
          ·
            refine ⟨4697452410760681601226797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3131634940507121067484531 4697452410760681601226797)
            ·
              refine ⟨1761544654035255600460049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4697452410760681601226797 1761544654035255600460049)
              ·
                refine ⟨1321158490526441700345037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1761544654035255600460049 1321158490526441700345037)
                ·
                  refine ⟨495434433947415637629389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1321158490526441700345037 495434433947415637629389)
                  ·
                    refine ⟨185787912730280864111021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 495434433947415637629389 185787912730280864111021)
                    ·
                      rfl

theorem cell22_542731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 2, 3, 3].length) (baseStart_542731 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_542731 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_542731 prefixEnd_542731 := by exact prefixLift 542731
  have htrace : WordTrace (prefixWord ++ tailWord_542731) baseStart_542731 baseEnd_542731 := by
    simpa [prefixWord, tailWord_542731, baseEnd_542731] using wordTrace_append hprefix tailTrace_542731
  have hstable : (prefixWord ++ tailWord_542731).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542731).length < 2 ^ (prefixWord ++ tailWord_542731).sum := by decide
  have hdescent : baseEnd_542731 < baseStart_542731 := by decide
  rcases family_descends (prefixWord ++ tailWord_542731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542744 : List Nat := [2, 1, 2, 3, 2, 1, 2, 2, 7]
def baseStart_542744 : Nat := 118140960795 + 542744 * 2 ^ 59
def prefixEnd_542744 : Nat := 4983230072969 + 3 ^ 40 * 542744 * 2
def baseEnd_542744 : Nat := 61930787631984387845327

theorem tailTrace_542744 : CollatzResearch.WordTrace tailWord_542744 prefixEnd_542744 61930787631984387845327 := by
  unfold tailWord_542744
  simp only [CollatzResearch.WordTrace]
  refine ⟨9897749972869328070309643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13196999963825770760412857 9897749972869328070309643)
  ·
    refine ⟨14846624959303992105464465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9897749972869328070309643 14846624959303992105464465)
    ·
      refine ⟨11134968719477994079098349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14846624959303992105464465 11134968719477994079098349)
      ·
        refine ⟨4175613269804247779661881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11134968719477994079098349 4175613269804247779661881)
        ·
          refine ⟨3131709952353185834746411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4175613269804247779661881 3131709952353185834746411)
          ·
            refine ⟨4697564928529778752119617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3131709952353185834746411 4697564928529778752119617)
            ·
              refine ⟨3523173696397334064089713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4697564928529778752119617 3523173696397334064089713)
              ·
                refine ⟨2642380272298000548067285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3523173696397334064089713 2642380272298000548067285)
                ·
                  refine ⟨61930787631984387845327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2642380272298000548067285 61930787631984387845327)
                  ·
                    rfl

theorem cell22_542744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 2, 7].length) (baseStart_542744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_542744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_542744 prefixEnd_542744 := by exact prefixLift 542744
  have htrace : WordTrace (prefixWord ++ tailWord_542744) baseStart_542744 baseEnd_542744 := by
    simpa [prefixWord, tailWord_542744, baseEnd_542744] using wordTrace_append hprefix tailTrace_542744
  have hstable : (prefixWord ++ tailWord_542744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542744).length < 2 ^ (prefixWord ++ tailWord_542744).sum := by decide
  have hdescent : baseEnd_542744 < baseStart_542744 := by decide
  rcases family_descends (prefixWord ++ tailWord_542744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542853 : List Nat := [1, 3, 1, 1, 5, 2, 2, 1, 2, 4]
def baseStart_542853 : Nat := 118140960795 + 542853 * 2 ^ 59
def prefixEnd_542853 : Nat := 4983230072969 + 3 ^ 40 * 542853 * 2
def baseEnd_542853 : Nat := 185829675823513212560647

theorem tailTrace_542853 : CollatzResearch.WordTrace tailWord_542853 prefixEnd_542853 185829675823513212560647 := by
  unfold tailWord_542853
  simp only [CollatzResearch.WordTrace]
  refine ⟨19799475502343767756337213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13199650334895845170891475 19799475502343767756337213)
  ·
    refine ⟨7424803313378912908626455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19799475502343767756337213 7424803313378912908626455)
    ·
      refine ⟨11137204970068369362939683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7424803313378912908626455 11137204970068369362939683)
      ·
        refine ⟨16705807455102554044409525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11137204970068369362939683 16705807455102554044409525)
        ·
          refine ⟨1566169448915864441663393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16705807455102554044409525 1566169448915864441663393)
          ·
            refine ⟨1174627086686898331247545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1566169448915864441663393 1174627086686898331247545)
            ·
              refine ⟨880970315015173748435659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1174627086686898331247545 880970315015173748435659)
              ·
                refine ⟨1321455472522760622653489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 880970315015173748435659 1321455472522760622653489)
                ·
                  refine ⟨991091604392070466990117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1321455472522760622653489 991091604392070466990117)
                  ·
                    refine ⟨185829675823513212560647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 991091604392070466990117 185829675823513212560647)
                    ·
                      rfl

theorem cell22_542853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 2, 1, 2, 4].length) (baseStart_542853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_542853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_542853 prefixEnd_542853 := by exact prefixLift 542853
  have htrace : WordTrace (prefixWord ++ tailWord_542853) baseStart_542853 baseEnd_542853 := by
    simpa [prefixWord, tailWord_542853, baseEnd_542853] using wordTrace_append hprefix tailTrace_542853
  have hstable : (prefixWord ++ tailWord_542853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542853).length < 2 ^ (prefixWord ++ tailWord_542853).sum := by decide
  have hdescent : baseEnd_542853 < baseStart_542853 := by decide
  rcases family_descends (prefixWord ++ tailWord_542853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542868 : List Nat := [2, 4, 2, 3, 1, 10]
def baseStart_542868 : Nat := 118140960795 + 542868 * 2 ^ 59
def prefixEnd_542868 : Nat := 4983230072969 + 3 ^ 40 * 542868 * 2
def baseEnd_542868 : Nat := 2294256921358742881921

theorem tailTrace_542868 : CollatzResearch.WordTrace tailWord_542868 prefixEnd_542868 2294256921358742881921 := by
  unfold tailWord_542868
  simp only [CollatzResearch.WordTrace]
  refine ⟨9900011298644712659066629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13200015064859616878755505 9900011298644712659066629)
  ·
    refine ⟨1856252118495883623574993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9900011298644712659066629 1856252118495883623574993)
    ·
      refine ⟨1392189088871912717681245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1856252118495883623574993 1392189088871912717681245)
      ·
        refine ⟨522070908326967269130467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1392189088871912717681245 522070908326967269130467)
        ·
          refine ⟨783106362490450903695701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 522070908326967269130467 783106362490450903695701)
          ·
            refine ⟨2294256921358742881921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 783106362490450903695701 2294256921358742881921)
            ·
              rfl

theorem cell22_542868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 10].length) (baseStart_542868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_542868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_542868 prefixEnd_542868 := by exact prefixLift 542868
  have htrace : WordTrace (prefixWord ++ tailWord_542868) baseStart_542868 baseEnd_542868 := by
    simpa [prefixWord, tailWord_542868, baseEnd_542868] using wordTrace_append hprefix tailTrace_542868
  have hstable : (prefixWord ++ tailWord_542868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542868).length < 2 ^ (prefixWord ++ tailWord_542868).sum := by decide
  have hdescent : baseEnd_542868 < baseStart_542868 := by decide
  rcases family_descends (prefixWord ++ tailWord_542868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542874 : List Nat := [3, 1, 1, 5, 3, 1, 2, 2, 4]
def baseStart_542874 : Nat := 118140960795 + 542874 * 2 ^ 59
def prefixEnd_542874 : Nat := 4983230072969 + 3 ^ 40 * 542874 * 2
def baseEnd_542874 : Nat := 61945621517558719261861

theorem tailTrace_542874 : CollatzResearch.WordTrace tailWord_542874 prefixEnd_542874 61945621517558719261861 := by
  unfold tailWord_542874
  simp only [CollatzResearch.WordTrace]
  refine ⟨4950060358816922085712919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13200160956845125561901117 4950060358816922085712919)
  ·
    refine ⟨7425090538225383128569379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4950060358816922085712919 7425090538225383128569379)
    ·
      refine ⟨11137635807338074692854069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7425090538225383128569379 11137635807338074692854069)
      ·
        refine ⟨1044153356937944502455069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11137635807338074692854069 1044153356937944502455069)
        ·
          refine ⟨391557508851729188420651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1044153356937944502455069 391557508851729188420651)
          ·
            refine ⟨587336263277593782630977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 391557508851729188420651 587336263277593782630977)
            ·
              refine ⟨440502197458195336973233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 587336263277593782630977 440502197458195336973233)
              ·
                refine ⟨330376648093646502729925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 440502197458195336973233 330376648093646502729925)
                ·
                  refine ⟨61945621517558719261861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 330376648093646502729925 61945621517558719261861)
                  ·
                    rfl

theorem cell22_542874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 2, 2, 4].length) (baseStart_542874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_542874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_542874 prefixEnd_542874 := by exact prefixLift 542874
  have htrace : WordTrace (prefixWord ++ tailWord_542874) baseStart_542874 baseEnd_542874 := by
    simpa [prefixWord, tailWord_542874, baseEnd_542874] using wordTrace_append hprefix tailTrace_542874
  have hstable : (prefixWord ++ tailWord_542874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542874).length < 2 ^ (prefixWord ++ tailWord_542874).sum := by decide
  have hdescent : baseEnd_542874 < baseStart_542874 := by decide
  rcases family_descends (prefixWord ++ tailWord_542874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542881 : List Nat := [1, 2, 3, 3, 1, 2, 1, 1, 2, 6]
def baseStart_542881 : Nat := 118140960795 + 542881 * 2 ^ 59
def prefixEnd_542881 : Nat := 4983230072969 + 3 ^ 40 * 542881 * 2
def baseEnd_542881 : Nat := 185839260795730472860561

theorem tailTrace_542881 : CollatzResearch.WordTrace tailWord_542881 prefixEnd_542881 185839260795730472860561 := by
  unfold tailWord_542881
  simp only [CollatzResearch.WordTrace]
  refine ⟨19800496746242328538356497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13200331164161552358904331 19800496746242328538356497)
  ·
    refine ⟨14850372559681746403767373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19800496746242328538356497 14850372559681746403767373)
    ·
      refine ⟨5568889709880654901412765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14850372559681746403767373 5568889709880654901412765)
      ·
        refine ⟨2088333641205245588029787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5568889709880654901412765 2088333641205245588029787)
        ·
          refine ⟨3132500461807868382044681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2088333641205245588029787 3132500461807868382044681)
          ·
            refine ⟨2349375346355901286533511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3132500461807868382044681 2349375346355901286533511)
            ·
              refine ⟨3524063019533851929800267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2349375346355901286533511 3524063019533851929800267)
              ·
                refine ⟨5286094529300777894700401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3524063019533851929800267 5286094529300777894700401)
                ·
                  refine ⟨3964570896975583421025301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5286094529300777894700401 3964570896975583421025301)
                  ·
                    refine ⟨185839260795730472860561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3964570896975583421025301 185839260795730472860561)
                    ·
                      rfl

theorem cell22_542881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 1, 2, 6].length) (baseStart_542881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_542881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_542881 prefixEnd_542881 := by exact prefixLift 542881
  have htrace : WordTrace (prefixWord ++ tailWord_542881) baseStart_542881 baseEnd_542881 := by
    simpa [prefixWord, tailWord_542881, baseEnd_542881] using wordTrace_append hprefix tailTrace_542881
  have hstable : (prefixWord ++ tailWord_542881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542881).length < 2 ^ (prefixWord ++ tailWord_542881).sum := by decide
  have hdescent : baseEnd_542881 < baseStart_542881 := by decide
  rcases family_descends (prefixWord ++ tailWord_542881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542930 : List Nat := [3, 2, 2, 2, 1, 4, 1, 2, 5]
def baseStart_542930 : Nat := 118140960795 + 542930 * 2 ^ 59
def prefixEnd_542930 : Nat := 4983230072969 + 3 ^ 40 * 542930 * 2
def baseEnd_542930 : Nat := 61952011499036892795137

theorem tailTrace_542930 : CollatzResearch.WordTrace tailWord_542930 prefixEnd_542930 61952011499036892795137 := by
  unfold tailWord_542930
  simp only [CollatzResearch.WordTrace]
  refine ⟨4950570980766202476722561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13201522615376539937926829 4950570980766202476722561)
  ·
    refine ⟨3712928235574651857541921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4950570980766202476722561 3712928235574651857541921)
    ·
      refine ⟨2784696176680988893156441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3712928235574651857541921 2784696176680988893156441)
      ·
        refine ⟨2088522132510741669867331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2784696176680988893156441 2088522132510741669867331)
        ·
          refine ⟨3132783198766112504800997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2088522132510741669867331 3132783198766112504800997)
          ·
            refine ⟨587396849768646094650187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3132783198766112504800997 587396849768646094650187)
            ·
              refine ⟨881095274652969141975281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 587396849768646094650187 881095274652969141975281)
              ·
                refine ⟨660821455989726856481461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 881095274652969141975281 660821455989726856481461)
                ·
                  refine ⟨61952011499036892795137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 660821455989726856481461 61952011499036892795137)
                  ·
                    rfl

theorem cell22_542930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 1, 2, 5].length) (baseStart_542930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_542930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_542930 prefixEnd_542930 := by exact prefixLift 542930
  have htrace : WordTrace (prefixWord ++ tailWord_542930) baseStart_542930 baseEnd_542930 := by
    simpa [prefixWord, tailWord_542930, baseEnd_542930] using wordTrace_append hprefix tailTrace_542930
  have hstable : (prefixWord ++ tailWord_542930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542930).length < 2 ^ (prefixWord ++ tailWord_542930).sum := by decide
  have hdescent : baseEnd_542930 < baseStart_542930 := by decide
  rcases family_descends (prefixWord ++ tailWord_542930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542934 : List Nat := [5, 2, 1, 2, 1, 1, 2, 4, 1, 3]
def baseStart_542934 : Nat := 118140960795 + 542934 * 2 ^ 59
def prefixEnd_542934 : Nat := 4983230072969 + 3 ^ 40 * 542934 * 2
def baseEnd_542934 : Nat := 185857403778856001285399

theorem tailTrace_542934 : CollatzResearch.WordTrace tailWord_542934 prefixEnd_542934 185857403778856001285399 := by
  unfold tailWord_542934
  simp only [CollatzResearch.WordTrace]
  refine ⟨1237651863440644911877241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13201619876700212393357237 1237651863440644911877241)
  ·
    refine ⟨928238897580483683907931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1237651863440644911877241 928238897580483683907931)
    ·
      refine ⟨1392358346370725525861897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 928238897580483683907931 1392358346370725525861897)
      ·
        refine ⟨1044268759778044144396423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1392358346370725525861897 1044268759778044144396423)
        ·
          refine ⟨1566403139667066216594635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1044268759778044144396423 1566403139667066216594635)
          ·
            refine ⟨2349604709500599324891953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1566403139667066216594635 2349604709500599324891953)
            ·
              refine ⟨1762203532125449493668965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2349604709500599324891953 1762203532125449493668965)
              ·
                refine ⟨330413162273521780062931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1762203532125449493668965 330413162273521780062931)
                ·
                  refine ⟨495619743410282670094397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 330413162273521780062931 495619743410282670094397)
                  ·
                    refine ⟨185857403778856001285399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 495619743410282670094397 185857403778856001285399)
                    ·
                      rfl

theorem cell22_542934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 4, 1, 3].length) (baseStart_542934 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_542934 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_542934 prefixEnd_542934 := by exact prefixLift 542934
  have htrace : WordTrace (prefixWord ++ tailWord_542934) baseStart_542934 baseEnd_542934 := by
    simpa [prefixWord, tailWord_542934, baseEnd_542934] using wordTrace_append hprefix tailTrace_542934
  have hstable : (prefixWord ++ tailWord_542934).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542934).length < 2 ^ (prefixWord ++ tailWord_542934).sum := by decide
  have hdescent : baseEnd_542934 < baseStart_542934 := by decide
  rcases family_descends (prefixWord ++ tailWord_542934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542947 : List Nat := [1, 1, 1, 8, 1, 1, 3, 1, 5]
def baseStart_542947 : Nat := 118140960795 + 542947 * 2 ^ 59
def prefixEnd_542947 : Nat := 4983230072969 + 3 ^ 40 * 542947 * 2
def baseEnd_542947 : Nat := 61953951314842766903453

theorem tailTrace_542947 : CollatzResearch.WordTrace tailWord_542947 prefixEnd_542947 61953951314842766903453 := by
  unfold tailWord_542947
  simp only [CollatzResearch.WordTrace]
  refine ⟨19802903964003221810259095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13201935976002147873506063 19802903964003221810259095)
  ·
    refine ⟨29704355946004832715388643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19802903964003221810259095 29704355946004832715388643)
    ·
      refine ⟨44556533919007249073082965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29704355946004832715388643 44556533919007249073082965)
      ·
        refine ⟨522146881863366200075191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 44556533919007249073082965 522146881863366200075191)
        ·
          refine ⟨783220322795049300112787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 522146881863366200075191 783220322795049300112787)
          ·
            refine ⟨1174830484192573950169181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 783220322795049300112787 1174830484192573950169181)
            ·
              refine ⟨440561431572215231313443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1174830484192573950169181 440561431572215231313443)
              ·
                refine ⟨660842147358322846970165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 440561431572215231313443 660842147358322846970165)
                ·
                  refine ⟨61953951314842766903453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 660842147358322846970165 61953951314842766903453)
                  ·
                    rfl

theorem cell22_542947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 3, 1, 5].length) (baseStart_542947 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_542947 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_542947 prefixEnd_542947 := by exact prefixLift 542947
  have htrace : WordTrace (prefixWord ++ tailWord_542947) baseStart_542947 baseEnd_542947 := by
    simpa [prefixWord, tailWord_542947, baseEnd_542947] using wordTrace_append hprefix tailTrace_542947
  have hstable : (prefixWord ++ tailWord_542947).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542947).length < 2 ^ (prefixWord ++ tailWord_542947).sum := by decide
  have hdescent : baseEnd_542947 < baseStart_542947 := by decide
  rcases family_descends (prefixWord ++ tailWord_542947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542971 : List Nat := [1, 1, 1, 1, 1, 3, 1, 1, 8, 4]
def baseStart_542971 : Nat := 118140960795 + 542971 * 2 ^ 59
def prefixEnd_542971 : Nat := 4983230072969 + 3 ^ 40 * 542971 * 2
def baseEnd_542971 : Nat := 185870069635000238110285

theorem tailTrace_542971 : CollatzResearch.WordTrace tailWord_542971 prefixEnd_542971 185870069635000238110285 := by
  unfold tailWord_542971
  simp only [CollatzResearch.WordTrace]
  refine ⟨19803779315916273909132767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13202519543944182606088511 19803779315916273909132767)
  ·
    refine ⟨29705668973874410863699151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19803779315916273909132767 29705668973874410863699151)
    ·
      refine ⟨44558503460811616295548727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29705668973874410863699151 44558503460811616295548727)
      ·
        refine ⟨66837755191217424443323091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44558503460811616295548727 66837755191217424443323091)
        ·
          refine ⟨100256632786826136664984637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66837755191217424443323091 100256632786826136664984637)
          ·
            refine ⟨37596237295059801249369239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 100256632786826136664984637 37596237295059801249369239)
            ·
              refine ⟨56394355942589701874053859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37596237295059801249369239 56394355942589701874053859)
              ·
                refine ⟨84591533913884552811080789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56394355942589701874053859 84591533913884552811080789)
                ·
                  refine ⟨991307038053334603254853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 84591533913884552811080789 991307038053334603254853)
                  ·
                    refine ⟨185870069635000238110285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 991307038053334603254853 185870069635000238110285)
                    ·
                      rfl

theorem cell22_542971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 8, 4].length) (baseStart_542971 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_542971 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_542971 prefixEnd_542971 := by exact prefixLift 542971
  have htrace : WordTrace (prefixWord ++ tailWord_542971) baseStart_542971 baseEnd_542971 := by
    simpa [prefixWord, tailWord_542971, baseEnd_542971] using wordTrace_append hprefix tailTrace_542971
  have hstable : (prefixWord ++ tailWord_542971).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542971).length < 2 ^ (prefixWord ++ tailWord_542971).sum := by decide
  have hdescent : baseEnd_542971 < baseStart_542971 := by decide
  rcases family_descends (prefixWord ++ tailWord_542971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542986 : List Nat := [3, 1, 2, 2, 1, 1, 12]
def baseStart_542986 : Nat := 118140960795 + 542986 * 2 ^ 59
def prefixEnd_542986 : Nat := 4983230072969 + 3 ^ 40 * 542986 * 2
def baseEnd_542986 : Nat := 6884266831168340703157

theorem tailTrace_542986 : CollatzResearch.WordTrace tailWord_542986 prefixEnd_542986 6884266831168340703157 := by
  unfold tailWord_542986
  simp only [CollatzResearch.WordTrace]
  refine ⟨4951081602715482867732203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13202884273907954313952541 4951081602715482867732203)
  ·
    refine ⟨7426622404073224301598305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4951081602715482867732203 7426622404073224301598305)
    ·
      refine ⟨5569966803054918226198729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7426622404073224301598305 5569966803054918226198729)
      ·
        refine ⟨4177475102291188669649047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5569966803054918226198729 4177475102291188669649047)
        ·
          refine ⟨6266212653436783004473571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4177475102291188669649047 6266212653436783004473571)
          ·
            refine ⟨9399318980155174506710357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6266212653436783004473571 9399318980155174506710357)
            ·
              refine ⟨6884266831168340703157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 9399318980155174506710357 6884266831168340703157)
              ·
                rfl

theorem cell22_542986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 12].length) (baseStart_542986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_542986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_542986 prefixEnd_542986 := by exact prefixLift 542986
  have htrace : WordTrace (prefixWord ++ tailWord_542986) baseStart_542986 baseEnd_542986 := by
    simpa [prefixWord, tailWord_542986, baseEnd_542986] using wordTrace_append hprefix tailTrace_542986
  have hstable : (prefixWord ++ tailWord_542986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542986).length < 2 ^ (prefixWord ++ tailWord_542986).sum := by decide
  have hdescent : baseEnd_542986 < baseStart_542986 := by decide
  rcases family_descends (prefixWord ++ tailWord_542986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542988 : List Nat := [2, 2, 1, 2, 2, 2, 3, 2, 2, 4]
def baseStart_542988 : Nat := 118140960795 + 542988 * 2 ^ 59
def prefixEnd_542988 : Nat := 4983230072969 + 3 ^ 40 * 542988 * 2
def baseEnd_542988 : Nat := 185875889082417860435233

theorem tailTrace_542988 : CollatzResearch.WordTrace tailWord_542988 prefixEnd_542988 185875889082417860435233 := by
  unfold tailWord_542988
  simp only [CollatzResearch.WordTrace]
  refine ⟨9902199678427342906250809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13202932904569790541667745 9902199678427342906250809)
  ·
    refine ⟨7426649758820507179688107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9902199678427342906250809 7426649758820507179688107)
    ·
      refine ⟨11139974638230760769532161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7426649758820507179688107 11139974638230760769532161)
      ·
        refine ⟨8354980978673070577149121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11139974638230760769532161 8354980978673070577149121)
        ·
          refine ⟨6266235734004802932861841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8354980978673070577149121 6266235734004802932861841)
          ·
            refine ⟨4699676800503602199646381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6266235734004802932861841 4699676800503602199646381)
            ·
              refine ⟨1762378800188850824867393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4699676800503602199646381 1762378800188850824867393)
              ·
                refine ⟨1321784100141638118650545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1762378800188850824867393 1321784100141638118650545)
                ·
                  refine ⟨991338075106228588987909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1321784100141638118650545 991338075106228588987909)
                  ·
                    refine ⟨185875889082417860435233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 991338075106228588987909 185875889082417860435233)
                    ·
                      rfl

theorem cell22_542988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 2, 2, 4].length) (baseStart_542988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_542988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_542988 prefixEnd_542988 := by exact prefixLift 542988
  have htrace : WordTrace (prefixWord ++ tailWord_542988) baseStart_542988 baseEnd_542988 := by
    simpa [prefixWord, tailWord_542988, baseEnd_542988] using wordTrace_append hprefix tailTrace_542988
  have hstable : (prefixWord ++ tailWord_542988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542988).length < 2 ^ (prefixWord ++ tailWord_542988).sum := by decide
  have hdescent : baseEnd_542988 < baseStart_542988 := by decide
  rcases family_descends (prefixWord ++ tailWord_542988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542990 : List Nat := [4, 1, 1, 2, 1, 2, 2, 4, 2, 3]
def baseStart_542990 : Nat := 118140960795 + 542990 * 2 ^ 59
def prefixEnd_542990 : Nat := 4983230072969 + 3 ^ 40 * 542990 * 2
def baseEnd_542990 : Nat := 185876573723290521885227

theorem tailTrace_542990 : CollatzResearch.WordTrace tailWord_542990 prefixEnd_542990 185876573723290521885227 := by
  unfold tailWord_542990
  simp only [CollatzResearch.WordTrace]
  refine ⟨2475559037855930019259303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13202981535231626769382949 2475559037855930019259303)
  ·
    refine ⟨3713338556783895028888955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2475559037855930019259303 3713338556783895028888955)
    ·
      refine ⟨5570007835175842543333433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3713338556783895028888955 5570007835175842543333433)
      ·
        refine ⟨4177505876381881907500075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5570007835175842543333433 4177505876381881907500075)
        ·
          refine ⟨6266258814572822861250113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4177505876381881907500075 6266258814572822861250113)
          ·
            refine ⟨4699694110929617145937585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6266258814572822861250113 4699694110929617145937585)
            ·
              refine ⟨3524770583197212859453189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4699694110929617145937585 3524770583197212859453189)
              ·
                refine ⟨660894484349477411147473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3524770583197212859453189 660894484349477411147473)
                ·
                  refine ⟨495670863262108058360605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 660894484349477411147473 495670863262108058360605)
                  ·
                    refine ⟨185876573723290521885227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 495670863262108058360605 185876573723290521885227)
                    ·
                      rfl

theorem cell22_542990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 4, 2, 3].length) (baseStart_542990 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_542990 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_542990 prefixEnd_542990 := by exact prefixLift 542990
  have htrace : WordTrace (prefixWord ++ tailWord_542990) baseStart_542990 baseEnd_542990 := by
    simpa [prefixWord, tailWord_542990, baseEnd_542990] using wordTrace_append hprefix tailTrace_542990
  have hstable : (prefixWord ++ tailWord_542990).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542990).length < 2 ^ (prefixWord ++ tailWord_542990).sum := by decide
  have hdescent : baseEnd_542990 < baseStart_542990 := by decide
  rcases family_descends (prefixWord ++ tailWord_542990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543007 : List Nat := [1, 1, 2, 4, 3, 1, 4, 1, 2, 3]
def baseStart_543007 : Nat := 118140960795 + 543007 * 2 ^ 59
def prefixEnd_543007 : Nat := 4983230072969 + 3 ^ 40 * 543007 * 2
def baseEnd_543007 : Nat := 185882393170708144210175

theorem tailTrace_543007 : CollatzResearch.WordTrace tailWord_543007 prefixEnd_543007 185882393170708144210175 := by
  unfold tailWord_543007
  simp only [CollatzResearch.WordTrace]
  refine ⟨19805092343785852057443275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13203394895857234704962183 19805092343785852057443275)
  ·
    refine ⟨29707638515678778086164913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19805092343785852057443275 29707638515678778086164913)
    ·
      refine ⟨22280728886759083564623685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29707638515678778086164913 22280728886759083564623685)
      ·
        refine ⟨4177636666267328168366941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22280728886759083564623685 4177636666267328168366941)
        ·
          refine ⟨1566613749850248063137603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4177636666267328168366941 1566613749850248063137603)
          ·
            refine ⟨2349920624775372094706405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1566613749850248063137603 2349920624775372094706405)
            ·
              refine ⟨440610117145382267757451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2349920624775372094706405 440610117145382267757451)
              ·
                refine ⟨660915175718073401636177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 440610117145382267757451 660915175718073401636177)
                ·
                  refine ⟨495686381788555051227133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 660915175718073401636177 495686381788555051227133)
                  ·
                    refine ⟨185882393170708144210175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 495686381788555051227133 185882393170708144210175)
                    ·
                      rfl

theorem cell22_543007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 4, 1, 2, 3].length) (baseStart_543007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_543007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_543007 prefixEnd_543007 := by exact prefixLift 543007
  have htrace : WordTrace (prefixWord ++ tailWord_543007) baseStart_543007 baseEnd_543007 := by
    simpa [prefixWord, tailWord_543007, baseEnd_543007] using wordTrace_append hprefix tailTrace_543007
  have hstable : (prefixWord ++ tailWord_543007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543007).length < 2 ^ (prefixWord ++ tailWord_543007).sum := by decide
  have hdescent : baseEnd_543007 < baseStart_543007 := by decide
  rcases family_descends (prefixWord ++ tailWord_543007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543031 : List Nat := [1, 1, 3, 1, 2, 1, 1, 3, 9]
def baseStart_543031 : Nat := 118140960795 + 543031 * 2 ^ 59
def prefixEnd_543031 : Nat := 4983230072969 + 3 ^ 40 * 543031 * 2
def baseEnd_543031 : Nat := 61963536287060027203367

theorem tailTrace_543031 : CollatzResearch.WordTrace tailWord_543031 prefixEnd_543031 61963536287060027203367 := by
  unfold tailWord_543031
  simp only [CollatzResearch.WordTrace]
  refine ⟨19805967695698904156316947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13203978463799269437544631 19805967695698904156316947)
  ·
    refine ⟨29708951543548356234475421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19805967695698904156316947 29708951543548356234475421)
    ·
      refine ⟨11140856828830633587928283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29708951543548356234475421 11140856828830633587928283)
      ·
        refine ⟨16711285243245950381892425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11140856828830633587928283 16711285243245950381892425)
        ·
          refine ⟨12533463932434462786419319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16711285243245950381892425 12533463932434462786419319)
          ·
            refine ⟨18800195898651694179628979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12533463932434462786419319 18800195898651694179628979)
            ·
              refine ⟨28200293847977541269443469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18800195898651694179628979 28200293847977541269443469)
              ·
                refine ⟨10575110192991577976041301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28200293847977541269443469 10575110192991577976041301)
                ·
                  refine ⟨61963536287060027203367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 10575110192991577976041301 61963536287060027203367)
                  ·
                    rfl

theorem cell22_543031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 3, 9].length) (baseStart_543031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_543031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_543031 prefixEnd_543031 := by exact prefixLift 543031
  have htrace : WordTrace (prefixWord ++ tailWord_543031) baseStart_543031 baseEnd_543031 := by
    simpa [prefixWord, tailWord_543031, baseEnd_543031] using wordTrace_append hprefix tailTrace_543031
  have hstable : (prefixWord ++ tailWord_543031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543031).length < 2 ^ (prefixWord ++ tailWord_543031).sum := by decide
  have hdescent : baseEnd_543031 < baseStart_543031 := by decide
  rcases family_descends (prefixWord ++ tailWord_543031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543048 : List Nat := [2, 1, 3, 1, 1, 2, 3, 4, 5]
def baseStart_543048 : Nat := 118140960795 + 543048 * 2 ^ 59
def prefixEnd_543048 : Nat := 4983230072969 + 3 ^ 40 * 543048 * 2
def baseEnd_543048 : Nat := 61965476102865901311683

theorem tailTrace_543048 : CollatzResearch.WordTrace tailWord_543048 prefixEnd_543048 61965476102865901311683 := by
  unfold tailWord_543048
  simp only [CollatzResearch.WordTrace]
  refine ⟨9903293868318658029842899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13204391824424877373123865 9903293868318658029842899)
  ·
    refine ⟨14854940802477987044764349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9903293868318658029842899 14854940802477987044764349)
    ·
      refine ⟨5570602800929245141786631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14854940802477987044764349 5570602800929245141786631)
      ·
        refine ⟨8355904201393867712679947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5570602800929245141786631 8355904201393867712679947)
        ·
          refine ⟨12533856302090801569019921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8355904201393867712679947 12533856302090801569019921)
          ·
            refine ⟨9400392226568101176764941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12533856302090801569019921 9400392226568101176764941)
            ·
              refine ⟨3525147084963037941286853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9400392226568101176764941 3525147084963037941286853)
              ·
                refine ⟨660965078430569613991285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3525147084963037941286853 660965078430569613991285)
                ·
                  refine ⟨61965476102865901311683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 660965078430569613991285 61965476102865901311683)
                  ·
                    rfl

theorem cell22_543048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 4, 5].length) (baseStart_543048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_543048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_543048 prefixEnd_543048 := by exact prefixLift 543048
  have htrace : WordTrace (prefixWord ++ tailWord_543048) baseStart_543048 baseEnd_543048 := by
    simpa [prefixWord, tailWord_543048, baseEnd_543048] using wordTrace_append hprefix tailTrace_543048
  have hstable : (prefixWord ++ tailWord_543048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543048).length < 2 ^ (prefixWord ++ tailWord_543048).sum := by decide
  have hdescent : baseEnd_543048 < baseStart_543048 := by decide
  rcases family_descends (prefixWord ++ tailWord_543048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543052 : List Nat := [2, 2, 1, 3, 2, 1, 3, 4, 1, 3]
def baseStart_543052 : Nat := 118140960795 + 543052 * 2 ^ 59
def prefixEnd_543052 : Nat := 4983230072969 + 3 ^ 40 * 543052 * 2
def baseEnd_543052 : Nat := 185897797590343026835037

theorem tailTrace_543052 : CollatzResearch.WordTrace tailWord_543052 prefixEnd_543052 185897797590343026835037 := by
  unfold tailWord_543052
  simp only [CollatzResearch.WordTrace]
  refine ⟨9903366814311412371415705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13204489085748549828554273 9903366814311412371415705)
  ·
    refine ⟨7427525110733559278561779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9903366814311412371415705 7427525110733559278561779)
    ·
      refine ⟨11141287666100338917842669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7427525110733559278561779 11141287666100338917842669)
      ·
        refine ⟨4177982874787627094191001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11141287666100338917842669 4177982874787627094191001)
        ·
          refine ⟨3133487156090720320643251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4177982874787627094191001 3133487156090720320643251)
          ·
            refine ⟨4700230734136080480964877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3133487156090720320643251 4700230734136080480964877)
            ·
              refine ⟨1762586525301030180361829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4700230734136080480964877 1762586525301030180361829)
              ·
                refine ⟨330484973493943158817843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1762586525301030180361829 330484973493943158817843)
                ·
                  refine ⟨495727460240914738226765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 330484973493943158817843 495727460240914738226765)
                  ·
                    refine ⟨185897797590343026835037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 495727460240914738226765 185897797590343026835037)
                    ·
                      rfl

theorem cell22_543052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 4, 1, 3].length) (baseStart_543052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_543052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_543052 prefixEnd_543052 := by exact prefixLift 543052
  have htrace : WordTrace (prefixWord ++ tailWord_543052) baseStart_543052 baseEnd_543052 := by
    simpa [prefixWord, tailWord_543052, baseEnd_543052] using wordTrace_append hprefix tailTrace_543052
  have hstable : (prefixWord ++ tailWord_543052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543052).length < 2 ^ (prefixWord ++ tailWord_543052).sum := by decide
  have hdescent : baseEnd_543052 < baseStart_543052 := by decide
  rcases family_descends (prefixWord ++ tailWord_543052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543063 : List Nat := [1, 1, 3, 2, 3, 1, 3, 1, 2, 5]
def baseStart_543063 : Nat := 118140960795 + 543063 * 2 ^ 59
def prefixEnd_543063 : Nat := 4983230072969 + 3 ^ 40 * 543063 * 2
def baseEnd_543063 : Nat := 185901563115142664810003

theorem tailTrace_543063 : CollatzResearch.WordTrace tailWord_543063 prefixEnd_543063 185901563115142664810003 := by
  unfold tailWord_543063
  simp only [CollatzResearch.WordTrace]
  refine ⟨19807134831582973621481843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13204756554388649080987895 19807134831582973621481843)
  ·
    refine ⟨29710702247374460432222765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19807134831582973621481843 29710702247374460432222765)
    ·
      refine ⟨11141513342765422662083537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29710702247374460432222765 11141513342765422662083537)
      ·
        refine ⟨8356135007074066996562653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11141513342765422662083537 8356135007074066996562653)
        ·
          refine ⟨3133550627652775123710995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8356135007074066996562653 3133550627652775123710995)
          ·
            refine ⟨4700325941479162685566493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3133550627652775123710995 4700325941479162685566493)
            ·
              refine ⟨1762622228054686007087435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4700325941479162685566493 1762622228054686007087435)
              ·
                refine ⟨2643933342082029010631153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1762622228054686007087435 2643933342082029010631153)
                ·
                  refine ⟨1982950006561521757973365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2643933342082029010631153 1982950006561521757973365)
                  ·
                    refine ⟨185901563115142664810003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1982950006561521757973365 185901563115142664810003)
                    ·
                      rfl

theorem cell22_543063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 1, 2, 5].length) (baseStart_543063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_543063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_543063 prefixEnd_543063 := by exact prefixLift 543063
  have htrace : WordTrace (prefixWord ++ tailWord_543063) baseStart_543063 baseEnd_543063 := by
    simpa [prefixWord, tailWord_543063, baseEnd_543063] using wordTrace_append hprefix tailTrace_543063
  have hstable : (prefixWord ++ tailWord_543063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543063).length < 2 ^ (prefixWord ++ tailWord_543063).sum := by decide
  have hdescent : baseEnd_543063 < baseStart_543063 := by decide
  rcases family_descends (prefixWord ++ tailWord_543063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543144 : List Nat := [2, 1, 6, 1, 1, 1, 3, 3, 4]
def baseStart_543144 : Nat := 118140960795 + 543144 * 2 ^ 59
def prefixEnd_543144 : Nat := 4983230072969 + 3 ^ 40 * 543144 * 2
def baseEnd_543144 : Nat := 61976430356828484511585

theorem tailTrace_543144 : CollatzResearch.WordTrace tailWord_543144 prefixEnd_543144 61976430356828484511585 := by
  unfold tailWord_543144
  simp only [CollatzResearch.WordTrace]
  refine ⟨9905044572144762227590243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13206726096193016303453657 9905044572144762227590243)
  ·
    refine ⟨14857566858217143341385365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9905044572144762227590243 14857566858217143341385365)
    ·
      refine ⟨696448446478928594127439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 14857566858217143341385365 696448446478928594127439)
      ·
        refine ⟨1044672669718392891191159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 696448446478928594127439 1044672669718392891191159)
        ·
          refine ⟨1567009004577589336786739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1044672669718392891191159 1567009004577589336786739)
          ·
            refine ⟨2350513506866384005180109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1567009004577589336786739 2350513506866384005180109)
            ·
              refine ⟨881442565074894001942541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2350513506866384005180109 881442565074894001942541)
              ·
                refine ⟨330540961903085250728453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 881442565074894001942541 330540961903085250728453)
                ·
                  refine ⟨61976430356828484511585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 330540961903085250728453 61976430356828484511585)
                  ·
                    rfl

theorem cell22_543144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 3, 3, 4].length) (baseStart_543144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_543144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_543144 prefixEnd_543144 := by exact prefixLift 543144
  have htrace : WordTrace (prefixWord ++ tailWord_543144) baseStart_543144 baseEnd_543144 := by
    simpa [prefixWord, tailWord_543144, baseEnd_543144] using wordTrace_append hprefix tailTrace_543144
  have hstable : (prefixWord ++ tailWord_543144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543144).length < 2 ^ (prefixWord ++ tailWord_543144).sum := by decide
  have hdescent : baseEnd_543144 < baseStart_543144 := by decide
  rcases family_descends (prefixWord ++ tailWord_543144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543157 : List Nat := [1, 3, 3, 2, 3, 1, 1, 2, 2, 4]
def baseStart_543157 : Nat := 118140960795 + 543157 * 2 ^ 59
def prefixEnd_543157 : Nat := 4983230072969 + 3 ^ 40 * 543157 * 2
def baseEnd_543157 : Nat := 185933741236157752959715

theorem tailTrace_543157 : CollatzResearch.WordTrace tailWord_543157 prefixEnd_543157 185933741236157752959715 := by
  unfold tailWord_543157
  simp only [CollatzResearch.WordTrace]
  refine ⟨19810563293242427675403725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13207042195494951783602483 19810563293242427675403725)
  ·
    refine ⟨7428961234965910378276397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19810563293242427675403725 7428961234965910378276397)
    ·
      refine ⟨2785860463112216391853649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7428961234965910378276397 2785860463112216391853649)
      ·
        refine ⟨2089395347334162293890237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2785860463112216391853649 2089395347334162293890237)
        ·
          refine ⟨783523255250310860208839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2089395347334162293890237 783523255250310860208839)
          ·
            refine ⟨1175284882875466290313259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 783523255250310860208839 1175284882875466290313259)
            ·
              refine ⟨1762927324313199435469889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1175284882875466290313259 1762927324313199435469889)
              ·
                refine ⟨1322195493234899576602417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1762927324313199435469889 1322195493234899576602417)
                ·
                  refine ⟨991646619926174682451813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1322195493234899576602417 991646619926174682451813)
                  ·
                    refine ⟨185933741236157752959715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 991646619926174682451813 185933741236157752959715)
                    ·
                      rfl

theorem cell22_543157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 2, 2, 4].length) (baseStart_543157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_543157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_543157 prefixEnd_543157 := by exact prefixLift 543157
  have htrace : WordTrace (prefixWord ++ tailWord_543157) baseStart_543157 baseEnd_543157 := by
    simpa [prefixWord, tailWord_543157, baseEnd_543157] using wordTrace_append hprefix tailTrace_543157
  have hstable : (prefixWord ++ tailWord_543157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543157).length < 2 ^ (prefixWord ++ tailWord_543157).sum := by decide
  have hdescent : baseEnd_543157 < baseStart_543157 := by decide
  rcases family_descends (prefixWord ++ tailWord_543157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543168 : List Nat := [2, 1, 1, 2, 3, 1, 1, 3, 2, 6]
def baseStart_543168 : Nat := 118140960795 + 543168 * 2 ^ 59
def prefixEnd_543168 : Nat := 4983230072969 + 3 ^ 40 * 543168 * 2
def baseEnd_543168 : Nat := 185937506760957390934681

theorem tailTrace_543168 : CollatzResearch.WordTrace tailWord_543168 prefixEnd_543168 185937506760957390934681 := by
  unfold tailWord_543168
  simp only [CollatzResearch.WordTrace]
  refine ⟨9905482248101288277027079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13207309664135051036036105 9905482248101288277027079)
  ·
    refine ⟨14858223372151932415540619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9905482248101288277027079 14858223372151932415540619)
    ·
      refine ⟨22287335058227898623310929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14858223372151932415540619 22287335058227898623310929)
      ·
        refine ⟨16715501293670923967483197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22287335058227898623310929 16715501293670923967483197)
        ·
          refine ⟨6268312985126596487806199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16715501293670923967483197 6268312985126596487806199)
          ·
            refine ⟨9402469477689894731709299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6268312985126596487806199 9402469477689894731709299)
            ·
              refine ⟨14103704216534842097563949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9402469477689894731709299 14103704216534842097563949)
              ·
                refine ⟨5288889081200565786586481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14103704216534842097563949 5288889081200565786586481)
                ·
                  refine ⟨3966666810900424339939861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5288889081200565786586481 3966666810900424339939861)
                  ·
                    refine ⟨185937506760957390934681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3966666810900424339939861 185937506760957390934681)
                    ·
                      rfl

theorem cell22_543168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 3, 2, 6].length) (baseStart_543168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_543168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_543168 prefixEnd_543168 := by exact prefixLift 543168
  have htrace : WordTrace (prefixWord ++ tailWord_543168) baseStart_543168 baseEnd_543168 := by
    simpa [prefixWord, tailWord_543168, baseEnd_543168] using wordTrace_append hprefix tailTrace_543168
  have hstable : (prefixWord ++ tailWord_543168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543168).length < 2 ^ (prefixWord ++ tailWord_543168).sum := by decide
  have hdescent : baseEnd_543168 < baseStart_543168 := by decide
  rcases family_descends (prefixWord ++ tailWord_543168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543172 : List Nat := [2, 3, 3, 2, 2, 1, 2, 7]
def baseStart_543172 : Nat := 118140960795 + 543172 * 2 ^ 59
def prefixEnd_543172 : Nat := 4983230072969 + 3 ^ 40 * 543172 * 2
def baseEnd_543172 : Nat := 20659875115855857092741

theorem tailTrace_543172 : CollatzResearch.WordTrace tailWord_543172 prefixEnd_543172 20659875115855857092741 := by
  unfold tailWord_543172
  simp only [CollatzResearch.WordTrace]
  refine ⟨9905555194094042618599885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13207406925458723491466513 9905555194094042618599885)
  ·
    refine ⟨3714583197785265981974957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9905555194094042618599885 3714583197785265981974957)
    ·
      refine ⟨1392968699169474743240609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3714583197785265981974957 1392968699169474743240609)
      ·
        refine ⟨1044726524377106057430457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1392968699169474743240609 1044726524377106057430457)
        ·
          refine ⟨783544893282829543072843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1044726524377106057430457 783544893282829543072843)
          ·
            refine ⟨1175317339924244314609265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 783544893282829543072843 1175317339924244314609265)
            ·
              refine ⟨881488004943183235956949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1175317339924244314609265 881488004943183235956949)
              ·
                refine ⟨20659875115855857092741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 881488004943183235956949 20659875115855857092741)
                ·
                  rfl

theorem cell22_543172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 2, 7].length) (baseStart_543172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_543172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_543172 prefixEnd_543172 := by exact prefixLift 543172
  have htrace : WordTrace (prefixWord ++ tailWord_543172) baseStart_543172 baseEnd_543172 := by
    simpa [prefixWord, tailWord_543172, baseEnd_543172] using wordTrace_append hprefix tailTrace_543172
  have hstable : (prefixWord ++ tailWord_543172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543172).length < 2 ^ (prefixWord ++ tailWord_543172).sum := by decide
  have hdescent : baseEnd_543172 < baseStart_543172 := by decide
  rcases family_descends (prefixWord ++ tailWord_543172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543238 : List Nat := [6, 2, 1, 1, 1, 2, 1, 2, 3, 3]
def baseStart_543238 : Nat := 118140960795 + 543238 * 2 ^ 59
def prefixEnd_543238 : Nat := 4983230072969 + 3 ^ 40 * 543238 * 2
def baseEnd_543238 : Nat := 185961469191500541684467

theorem tailTrace_543238 : CollatzResearch.WordTrace tailWord_543238 prefixEnd_543238 185961469191500541684467 := by
  unfold tailWord_543238
  simp only [CollatzResearch.WordTrace]
  refine ⟨619172425185905578409449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 13209011737299319006068245 619172425185905578409449)
  ·
    refine ⟨464379318889429183807087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 619172425185905578409449 464379318889429183807087)
    ·
      refine ⟨696568978334143775710631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 464379318889429183807087 696568978334143775710631)
      ·
        refine ⟨1044853467501215663565947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 696568978334143775710631 1044853467501215663565947)
        ·
          refine ⟨1567280201251823495348921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1044853467501215663565947 1567280201251823495348921)
          ·
            refine ⟨1175460150938867621511691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1567280201251823495348921 1175460150938867621511691)
            ·
              refine ⟨1763190226408301432267537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1175460150938867621511691 1763190226408301432267537)
              ·
                refine ⟨1322392669806226074200653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1763190226408301432267537 1322392669806226074200653)
                ·
                  refine ⟨495897251177334777825245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1322392669806226074200653 495897251177334777825245)
                  ·
                    refine ⟨185961469191500541684467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 495897251177334777825245 185961469191500541684467)
                    ·
                      rfl

theorem cell22_543238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_543238 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_543238 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_543238 prefixEnd_543238 := by exact prefixLift 543238
  have htrace : WordTrace (prefixWord ++ tailWord_543238) baseStart_543238 baseEnd_543238 := by
    simpa [prefixWord, tailWord_543238, baseEnd_543238] using wordTrace_append hprefix tailTrace_543238
  have hstable : (prefixWord ++ tailWord_543238).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543238).length < 2 ^ (prefixWord ++ tailWord_543238).sum := by decide
  have hdescent : baseEnd_543238 < baseStart_543238 := by decide
  rcases family_descends (prefixWord ++ tailWord_543238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543264 : List Nat := [2, 1, 1, 6, 2, 1, 1, 3, 1, 4]
def baseStart_543264 : Nat := 118140960795 + 543264 * 2 ^ 59
def prefixEnd_543264 : Nat := 4983230072969 + 3 ^ 40 * 543264 * 2
def baseEnd_543264 : Nat := 185970369522845140534387

theorem tailTrace_543264 : CollatzResearch.WordTrace tailWord_543264 prefixEnd_543264 185970369522845140534387 := by
  unfold tailWord_543264
  simp only [CollatzResearch.WordTrace]
  refine ⟨9907232951927392474774423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13209643935903189966365897 9907232951927392474774423)
  ·
    refine ⟨14860849427891088712161635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9907232951927392474774423 14860849427891088712161635)
    ·
      refine ⟨22291274141836633068242453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14860849427891088712161635 22291274141836633068242453)
      ·
        refine ⟨1044903475398592175073865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 22291274141836633068242453 1044903475398592175073865)
        ·
          refine ⟨783677606548944131305399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1044903475398592175073865 783677606548944131305399)
          ·
            refine ⟨1175516409823416196958099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 783677606548944131305399 1175516409823416196958099)
            ·
              refine ⟨1763274614735124295437149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1175516409823416196958099 1763274614735124295437149)
              ·
                refine ⟨661227980525671610788931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1763274614735124295437149 661227980525671610788931)
                ·
                  refine ⟨991841970788507416183397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 661227980525671610788931 991841970788507416183397)
                  ·
                    refine ⟨185970369522845140534387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 991841970788507416183397 185970369522845140534387)
                    ·
                      rfl

theorem cell22_543264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 3, 1, 4].length) (baseStart_543264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_543264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_543264 prefixEnd_543264 := by exact prefixLift 543264
  have htrace : WordTrace (prefixWord ++ tailWord_543264) baseStart_543264 baseEnd_543264 := by
    simpa [prefixWord, tailWord_543264, baseEnd_543264] using wordTrace_append hprefix tailTrace_543264
  have hstable : (prefixWord ++ tailWord_543264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543264).length < 2 ^ (prefixWord ++ tailWord_543264).sum := by decide
  have hdescent : baseEnd_543264 < baseStart_543264 := by decide
  rcases family_descends (prefixWord ++ tailWord_543264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543275 : List Nat := [1, 1, 1, 1, 2, 1, 3, 6, 2, 4]
def baseStart_543275 : Nat := 118140960795 + 543275 * 2 ^ 59
def prefixEnd_543275 : Nat := 4983230072969 + 3 ^ 40 * 543275 * 2
def baseEnd_543275 : Nat := 185974135047644778509353

theorem tailTrace_543275 : CollatzResearch.WordTrace tailWord_543275 prefixEnd_543275 185974135047644778509353 := by
  unfold tailWord_543275
  simp only [CollatzResearch.WordTrace]
  refine ⟨19814867106814933828199279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13209911404543289218799519 19814867106814933828199279)
  ·
    refine ⟨29722300660222400742298919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19814867106814933828199279 29722300660222400742298919)
    ·
      refine ⟨44583450990333601113448379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29722300660222400742298919 44583450990333601113448379)
      ·
        refine ⟨66875176485500401670172569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44583450990333601113448379 66875176485500401670172569)
        ·
          refine ⟨50156382364125301252629427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66875176485500401670172569 50156382364125301252629427)
          ·
            refine ⟨75234573546187951878944141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50156382364125301252629427 75234573546187951878944141)
            ·
              refine ⟨28212965079820481954604053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 75234573546187951878944141 28212965079820481954604053)
              ·
                refine ⟨1322482738116585091622065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 28212965079820481954604053 1322482738116585091622065)
                ·
                  refine ⟨991862053587438818716549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1322482738116585091622065 991862053587438818716549)
                  ·
                    refine ⟨185974135047644778509353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 991862053587438818716549 185974135047644778509353)
                    ·
                      rfl

theorem cell22_543275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 6, 2, 4].length) (baseStart_543275 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_543275 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_543275 prefixEnd_543275 := by exact prefixLift 543275
  have htrace : WordTrace (prefixWord ++ tailWord_543275) baseStart_543275 baseEnd_543275 := by
    simpa [prefixWord, tailWord_543275, baseEnd_543275] using wordTrace_append hprefix tailTrace_543275
  have hstable : (prefixWord ++ tailWord_543275).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543275).length < 2 ^ (prefixWord ++ tailWord_543275).sum := by decide
  have hdescent : baseEnd_543275 < baseStart_543275 := by decide
  rcases family_descends (prefixWord ++ tailWord_543275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543324 : List Nat := [2, 2, 4, 1, 4, 1, 8]
def baseStart_543324 : Nat := 118140960795 + 543324 * 2 ^ 59
def prefixEnd_543324 : Nat := 4983230072969 + 3 ^ 40 * 543324 * 2
def baseEnd_543324 : Nat := 6888552175889814223489

theorem tailTrace_543324 : CollatzResearch.WordTrace tailWord_543324 prefixEnd_543324 6888552175889814223489 := by
  unfold tailWord_543324
  simp only [CollatzResearch.WordTrace]
  refine ⟨9908327141818707598366513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13211102855758276797822017 9908327141818707598366513)
  ·
    refine ⟨7431245356364030698774885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9908327141818707598366513 7431245356364030698774885)
    ·
      refine ⟨1393358504318255756020291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7431245356364030698774885 1393358504318255756020291)
      ·
        refine ⟨2090037756477383634030437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1393358504318255756020291 2090037756477383634030437)
        ·
          refine ⟨391882079339509431380707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2090037756477383634030437 391882079339509431380707)
          ·
            refine ⟨587823119009264147071061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 391882079339509431380707 587823119009264147071061)
            ·
              refine ⟨6888552175889814223489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 587823119009264147071061 6888552175889814223489)
              ·
                rfl

theorem cell22_543324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 8].length) (baseStart_543324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_543324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_543324 prefixEnd_543324 := by exact prefixLift 543324
  have htrace : WordTrace (prefixWord ++ tailWord_543324) baseStart_543324 baseEnd_543324 := by
    simpa [prefixWord, tailWord_543324, baseEnd_543324] using wordTrace_append hprefix tailTrace_543324
  have hstable : (prefixWord ++ tailWord_543324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543324).length < 2 ^ (prefixWord ++ tailWord_543324).sum := by decide
  have hdescent : baseEnd_543324 < baseStart_543324 := by decide
  rcases family_descends (prefixWord ++ tailWord_543324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543386 : List Nat := [3, 1, 1, 6, 1, 1, 2, 2, 5]
def baseStart_543386 : Nat := 118140960795 + 543386 * 2 ^ 59
def prefixEnd_543386 : Nat := 4983230072969 + 3 ^ 40 * 543386 * 2
def baseEnd_543386 : Nat := 62004044205359162994671

theorem tailTrace_543386 : CollatzResearch.WordTrace tailWord_543386 prefixEnd_543386 62004044205359162994671 := by
  unfold tailWord_543386
  simp only [CollatzResearch.WordTrace]
  refine ⟨4954728902353199946372503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13212610406275199856993341 4954728902353199946372503)
  ·
    refine ⟨7432093353529799919558755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4954728902353199946372503 7432093353529799919558755)
    ·
      refine ⟨11148140030294699879338133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7432093353529799919558755 11148140030294699879338133)
      ·
        refine ⟨522569063920064056843975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 11148140030294699879338133 522569063920064056843975)
        ·
          refine ⟨783853595880096085265963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 522569063920064056843975 783853595880096085265963)
          ·
            refine ⟨1175780393820144127898945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 783853595880096085265963 1175780393820144127898945)
            ·
              refine ⟨881835295365108095924209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1175780393820144127898945 881835295365108095924209)
              ·
                refine ⟨661376471523831071943157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 881835295365108095924209 661376471523831071943157)
                ·
                  refine ⟨62004044205359162994671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 661376471523831071943157 62004044205359162994671)
                  ·
                    rfl

theorem cell22_543386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 2, 2, 5].length) (baseStart_543386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_543386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_543386 prefixEnd_543386 := by exact prefixLift 543386
  have htrace : WordTrace (prefixWord ++ tailWord_543386) baseStart_543386 baseEnd_543386 := by
    simpa [prefixWord, tailWord_543386, baseEnd_543386] using wordTrace_append hprefix tailTrace_543386
  have hstable : (prefixWord ++ tailWord_543386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543386).length < 2 ^ (prefixWord ++ tailWord_543386).sum := by decide
  have hdescent : baseEnd_543386 < baseStart_543386 := by decide
  rcases family_descends (prefixWord ++ tailWord_543386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543532 : List Nat := [2, 2, 1, 1, 1, 4, 2, 1, 8]
def baseStart_543532 : Nat := 118140960795 + 543532 * 2 ^ 59
def prefixEnd_543532 : Nat := 4983230072969 + 3 ^ 40 * 543532 * 2
def baseEnd_543532 : Nat := 62020703799927258277855

theorem tailTrace_543532 : CollatzResearch.WordTrace tailWord_543532 prefixEnd_543532 62020703799927258277855 := by
  unfold tailWord_543532
  simp only [CollatzResearch.WordTrace]
  refine ⟨9912120333441933360152425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13216160444589244480203233 9912120333441933360152425)
  ·
    refine ⟨7434090250081450020114319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9912120333441933360152425 7434090250081450020114319)
    ·
      refine ⟨11151135375122175030171479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7434090250081450020114319 11151135375122175030171479)
      ·
        refine ⟨16726703062683262545257219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11151135375122175030171479 16726703062683262545257219)
        ·
          refine ⟨25090054594024893817885829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16726703062683262545257219 25090054594024893817885829)
          ·
            refine ⟨4704385236379667590853593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25090054594024893817885829 4704385236379667590853593)
            ·
              refine ⟨3528288927284750693140195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4704385236379667590853593 3528288927284750693140195)
              ·
                refine ⟨5292433390927126039710293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3528288927284750693140195 5292433390927126039710293)
                ·
                  refine ⟨62020703799927258277855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5292433390927126039710293 62020703799927258277855)
                  ·
                    rfl

theorem cell22_543532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 8].length) (baseStart_543532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_543532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_543532 prefixEnd_543532 := by exact prefixLift 543532
  have htrace : WordTrace (prefixWord ++ tailWord_543532) baseStart_543532 baseEnd_543532 := by
    simpa [prefixWord, tailWord_543532, baseEnd_543532] using wordTrace_append hprefix tailTrace_543532
  have hstable : (prefixWord ++ tailWord_543532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543532).length < 2 ^ (prefixWord ++ tailWord_543532).sum := by decide
  have hdescent : baseEnd_543532 < baseStart_543532 := by decide
  rcases family_descends (prefixWord ++ tailWord_543532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543677 : List Nat := [1, 4, 1, 2, 4, 1, 3, 2, 1, 3]
def baseStart_543677 : Nat := 118140960795 + 543677 * 2 ^ 59
def prefixEnd_543677 : Nat := 4983230072969 + 3 ^ 40 * 543677 * 2
def baseEnd_543677 : Nat := 186111747863049729958121

theorem tailTrace_543677 : CollatzResearch.WordTrace tailWord_543677 prefixEnd_543677 186111747863049729958121 := by
  unfold tailWord_543677
  simp only [CollatzResearch.WordTrace]
  refine ⟨19829529251358556484333285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13219686167572370989555523 19829529251358556484333285)
  ·
    refine ⟨3718036734629729340812491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19829529251358556484333285 3718036734629729340812491)
    ·
      refine ⟨5577055101944594011218737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3718036734629729340812491 5577055101944594011218737)
      ·
        refine ⟨4182791326458445508414053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5577055101944594011218737 4182791326458445508414053)
        ·
          refine ⟨784273373710958532827635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4182791326458445508414053 784273373710958532827635)
          ·
            refine ⟨1176410060566437799241453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 784273373710958532827635 1176410060566437799241453)
            ·
              refine ⟨441153772712414174715545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1176410060566437799241453 441153772712414174715545)
              ·
                refine ⟨330865329534310631036659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 441153772712414174715545 330865329534310631036659)
                ·
                  refine ⟨496297994301465946554989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 330865329534310631036659 496297994301465946554989)
                  ·
                    refine ⟨186111747863049729958121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 496297994301465946554989 186111747863049729958121)
                    ·
                      rfl

theorem cell22_543677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 3, 2, 1, 3].length) (baseStart_543677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_543677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_543677 prefixEnd_543677 := by exact prefixLift 543677
  have htrace : WordTrace (prefixWord ++ tailWord_543677) baseStart_543677 baseEnd_543677 := by
    simpa [prefixWord, tailWord_543677, baseEnd_543677] using wordTrace_append hprefix tailTrace_543677
  have hstable : (prefixWord ++ tailWord_543677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543677).length < 2 ^ (prefixWord ++ tailWord_543677).sum := by decide
  have hdescent : baseEnd_543677 < baseStart_543677 := by decide
  rcases family_descends (prefixWord ++ tailWord_543677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543716 : List Nat := [2, 3, 1, 1, 1, 1, 2, 4, 4, 3]
def baseStart_543716 : Nat := 118140960795 + 543716 * 2 ^ 59
def prefixEnd_543716 : Nat := 4983230072969 + 3 ^ 40 * 543716 * 2
def baseEnd_543716 : Nat := 186125098360066628233001

theorem tailTrace_543716 : CollatzResearch.WordTrace tailWord_543716 prefixEnd_543716 186125098360066628233001 := by
  unfold tailWord_543716
  simp only [CollatzResearch.WordTrace]
  refine ⟨9915475849108633072501501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13220634465478177430002001 9915475849108633072501501)
  ·
    refine ⟨3718303443415737402188063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9915475849108633072501501 3718303443415737402188063)
    ·
      refine ⟨5577455165123606103282095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3718303443415737402188063 5577455165123606103282095)
      ·
        refine ⟨8366182747685409154923143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5577455165123606103282095 8366182747685409154923143)
        ·
          refine ⟨12549274121528113732384715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8366182747685409154923143 12549274121528113732384715)
          ·
            refine ⟨18823911182292170598577073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12549274121528113732384715 18823911182292170598577073)
            ·
              refine ⟨14117933386719127948932805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18823911182292170598577073 14117933386719127948932805)
              ·
                refine ⟨2647112510009836490424901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14117933386719127948932805 2647112510009836490424901)
                ·
                  refine ⟨496333595626844341954669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2647112510009836490424901 496333595626844341954669)
                  ·
                    refine ⟨186125098360066628233001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 496333595626844341954669 186125098360066628233001)
                    ·
                      rfl

theorem cell22_543716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 4, 4, 3].length) (baseStart_543716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_543716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_543716 prefixEnd_543716 := by exact prefixLift 543716
  have htrace : WordTrace (prefixWord ++ tailWord_543716) baseStart_543716 baseEnd_543716 := by
    simpa [prefixWord, tailWord_543716, baseEnd_543716] using wordTrace_append hprefix tailTrace_543716
  have hstable : (prefixWord ++ tailWord_543716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543716).length < 2 ^ (prefixWord ++ tailWord_543716).sum := by decide
  have hdescent : baseEnd_543716 < baseStart_543716 := by decide
  rcases family_descends (prefixWord ++ tailWord_543716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543729 : List Nat := [1, 2, 2, 2, 4, 11]
def baseStart_543729 : Nat := 118140960795 + 543729 * 2 ^ 59
def prefixEnd_543729 : Nat := 4983230072969 + 3 ^ 40 * 543729 * 2
def baseEnd_543729 : Nat := 2297895660811591699481

theorem tailTrace_543729 : CollatzResearch.WordTrace tailWord_543729 prefixEnd_543729 2297895660811591699481 := by
  unfold tailWord_543729
  simp only [CollatzResearch.WordTrace]
  refine ⟨19831425847170169365226241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13220950564780112910150827 19831425847170169365226241)
  ·
    refine ⟨14873569385377627023919681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19831425847170169365226241 14873569385377627023919681)
    ·
      refine ⟨11155177039033220267939761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14873569385377627023919681 11155177039033220267939761)
      ·
        refine ⟨8366382779274915200954821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11155177039033220267939761 8366382779274915200954821)
        ·
          refine ⟨1568696771114046600179029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8366382779274915200954821 1568696771114046600179029)
          ·
            refine ⟨2297895660811591699481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 1568696771114046600179029 2297895660811591699481)
            ·
              rfl

theorem cell22_543729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 11].length) (baseStart_543729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_543729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_543729 prefixEnd_543729 := by exact prefixLift 543729
  have htrace : WordTrace (prefixWord ++ tailWord_543729) baseStart_543729 baseEnd_543729 := by
    simpa [prefixWord, tailWord_543729, baseEnd_543729] using wordTrace_append hprefix tailTrace_543729
  have hstable : (prefixWord ++ tailWord_543729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543729).length < 2 ^ (prefixWord ++ tailWord_543729).sum := by decide
  have hdescent : baseEnd_543729 < baseStart_543729 := by decide
  rcases family_descends (prefixWord ++ tailWord_543729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543808 : List Nat := [2, 1, 1, 2, 2, 3, 5, 1, 5]
def baseStart_543808 : Nat := 118140960795 + 543808 * 2 ^ 59
def prefixEnd_543808 : Nat := 4983230072969 + 3 ^ 40 * 543808 * 2
def baseEnd_543808 : Nat := 62052197280069684977573

theorem tailTrace_543808 : CollatzResearch.WordTrace tailWord_543808 prefixEnd_543808 62052197280069684977573 := by
  unfold tailWord_543808
  simp only [CollatzResearch.WordTrace]
  refine ⟨9917153606941982928676039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13222871475922643904901385 9917153606941982928676039)
  ·
    refine ⟨14875730410412974393014059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9917153606941982928676039 14875730410412974393014059)
    ·
      refine ⟨22313595615619461589521089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14875730410412974393014059 22313595615619461589521089)
      ·
        refine ⟨16735196711714596192140817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22313595615619461589521089 16735196711714596192140817)
        ·
          refine ⟨12551397533785947144105613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16735196711714596192140817 12551397533785947144105613)
          ·
            refine ⟨4706774075169730179039605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12551397533785947144105613 4706774075169730179039605)
            ·
              refine ⟨441260069547162204284963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4706774075169730179039605 441260069547162204284963)
              ·
                refine ⟨661890104320743306427445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 441260069547162204284963 661890104320743306427445)
                ·
                  refine ⟨62052197280069684977573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 661890104320743306427445 62052197280069684977573)
                  ·
                    rfl

theorem cell22_543808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 5, 1, 5].length) (baseStart_543808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_543808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_543808 prefixEnd_543808 := by exact prefixLift 543808
  have htrace : WordTrace (prefixWord ++ tailWord_543808) baseStart_543808 baseEnd_543808 := by
    simpa [prefixWord, tailWord_543808, baseEnd_543808] using wordTrace_append hprefix tailTrace_543808
  have hstable : (prefixWord ++ tailWord_543808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543808).length < 2 ^ (prefixWord ++ tailWord_543808).sum := by decide
  have hdescent : baseEnd_543808 < baseStart_543808 := by decide
  rcases family_descends (prefixWord ++ tailWord_543808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543853 : List Nat := [1, 5, 1, 1, 2, 2, 3, 1, 6]
def baseStart_543853 : Nat := 118140960795 + 543853 * 2 ^ 59
def prefixEnd_543853 : Nat := 4983230072969 + 3 ^ 40 * 543853 * 2
def baseEnd_543853 : Nat := 62057332086614645852527

theorem tailTrace_543853 : CollatzResearch.WordTrace tailWord_543853 prefixEnd_543853 62057332086614645852527 := by
  unfold tailWord_543853
  simp only [CollatzResearch.WordTrace]
  refine ⟨19835948498720938542740213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13223965665813959028493475 19835948498720938542740213)
  ·
    refine ⟨1859620171755087988381895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19835948498720938542740213 1859620171755087988381895)
    ·
      refine ⟨2789430257632631982572843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1859620171755087988381895 2789430257632631982572843)
      ·
        refine ⟨4184145386448947973859265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2789430257632631982572843 4184145386448947973859265)
        ·
          refine ⟨3138109039836710980394449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4184145386448947973859265 3138109039836710980394449)
          ·
            refine ⟨2353581779877533235295837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3138109039836710980394449 2353581779877533235295837)
            ·
              refine ⟨882593167454074963235939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2353581779877533235295837 882593167454074963235939)
              ·
                refine ⟨1323889751181112444853909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 882593167454074963235939 1323889751181112444853909)
                ·
                  refine ⟨62057332086614645852527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1323889751181112444853909 62057332086614645852527)
                  ·
                    rfl

theorem cell22_543853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 3, 1, 6].length) (baseStart_543853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_543853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_543853 prefixEnd_543853 := by exact prefixLift 543853
  have htrace : WordTrace (prefixWord ++ tailWord_543853) baseStart_543853 baseEnd_543853 := by
    simpa [prefixWord, tailWord_543853, baseEnd_543853] using wordTrace_append hprefix tailTrace_543853
  have hstable : (prefixWord ++ tailWord_543853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543853).length < 2 ^ (prefixWord ++ tailWord_543853).sum := by decide
  have hdescent : baseEnd_543853 < baseStart_543853 := by decide
  rcases family_descends (prefixWord ++ tailWord_543853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543881 : List Nat := [1, 2, 1, 1, 4, 3, 2, 8]
def baseStart_543881 : Nat := 118140960795 + 543881 * 2 ^ 59
def prefixEnd_543881 : Nat := 4983230072969 + 3 ^ 40 * 543881 * 2
def baseEnd_543881 : Nat := 20686842359117910873055

theorem tailTrace_543881 : CollatzResearch.WordTrace tailWord_543881 prefixEnd_543881 20686842359117910873055 := by
  unfold tailWord_543881
  simp only [CollatzResearch.WordTrace]
  refine ⟨19836969742619499324759497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13224646495079666216506331 19836969742619499324759497)
  ·
    refine ⟨14877727306964624493569623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19836969742619499324759497 14877727306964624493569623)
    ·
      refine ⟨22316590960446936740354435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14877727306964624493569623 22316590960446936740354435)
      ·
        refine ⟨33474886440670405110531653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22316590960446936740354435 33474886440670405110531653)
        ·
          refine ⟨6276541207625700958224685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33474886440670405110531653 6276541207625700958224685)
          ·
            refine ⟨2353702952859637859334257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6276541207625700958224685 2353702952859637859334257)
            ·
              refine ⟨1765277214644728394500693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2353702952859637859334257 1765277214644728394500693)
              ·
                refine ⟨20686842359117910873055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1765277214644728394500693 20686842359117910873055)
                ·
                  rfl

theorem cell22_543881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 8].length) (baseStart_543881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_543881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_543881 prefixEnd_543881 := by exact prefixLift 543881
  have htrace : WordTrace (prefixWord ++ tailWord_543881) baseStart_543881 baseEnd_543881 := by
    simpa [prefixWord, tailWord_543881, baseEnd_543881] using wordTrace_append hprefix tailTrace_543881
  have hstable : (prefixWord ++ tailWord_543881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543881).length < 2 ^ (prefixWord ++ tailWord_543881).sum := by decide
  have hdescent : baseEnd_543881 < baseStart_543881 := by decide
  rcases family_descends (prefixWord ++ tailWord_543881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543902 : List Nat := [4, 3, 1, 1, 2, 1, 1, 4, 2, 3]
def baseStart_543902 : Nat := 118140960795 + 543902 * 2 ^ 59
def prefixEnd_543902 : Nat := 4983230072969 + 3 ^ 40 * 543902 * 2
def baseEnd_543902 : Nat := 186188769961224143082431

theorem tailTrace_543902 : CollatzResearch.WordTrace tailWord_543902 prefixEnd_543902 186188769961224143082431 := by
  unfold tailWord_543902
  simp only [CollatzResearch.WordTrace]
  refine ⟨2479716959442927488909245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13225157117028946607515973 2479716959442927488909245)
  ·
    refine ⟨929893859791097808340967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2479716959442927488909245 929893859791097808340967)
    ·
      refine ⟨1394840789686646712511451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 929893859791097808340967 1394840789686646712511451)
      ·
        refine ⟨2092261184529970068767177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1394840789686646712511451 2092261184529970068767177)
        ·
          refine ⟨1569195888397477551575383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2092261184529970068767177 1569195888397477551575383)
          ·
            refine ⟨2353793832596216327363075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1569195888397477551575383 2353793832596216327363075)
            ·
              refine ⟨3530690748894324491044613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2353793832596216327363075 3530690748894324491044613)
              ·
                refine ⟨662004515417685842070865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3530690748894324491044613 662004515417685842070865)
                ·
                  refine ⟨496503386563264381553149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 662004515417685842070865 496503386563264381553149)
                  ·
                    refine ⟨186188769961224143082431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 496503386563264381553149 186188769961224143082431)
                    ·
                      rfl

theorem cell22_543902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 4, 2, 3].length) (baseStart_543902 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_543902 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_543902 prefixEnd_543902 := by exact prefixLift 543902
  have htrace : WordTrace (prefixWord ++ tailWord_543902) baseStart_543902 baseEnd_543902 := by
    simpa [prefixWord, tailWord_543902, baseEnd_543902] using wordTrace_append hprefix tailTrace_543902
  have hstable : (prefixWord ++ tailWord_543902).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543902).length < 2 ^ (prefixWord ++ tailWord_543902).sum := by decide
  have hdescent : baseEnd_543902 < baseStart_543902 := by decide
  rcases family_descends (prefixWord ++ tailWord_543902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543941 : List Nat := [1, 3, 1, 1, 1, 1, 3, 1, 3, 7]
def baseStart_543941 : Nat := 118140960795 + 543941 * 2 ^ 59
def prefixEnd_543941 : Nat := 4983230072969 + 3 ^ 40 * 543941 * 2
def baseEnd_543941 : Nat := 186202120458241041357311

theorem tailTrace_543941 : CollatzResearch.WordTrace tailWord_543941 prefixEnd_543941 186202120458241041357311 := by
  unfold tailWord_543941
  simp only [CollatzResearch.WordTrace]
  refine ⟨19839158122402129571943677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13226105414934753047962451 19839158122402129571943677)
  ·
    refine ⟨7439684295900798589478879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19839158122402129571943677 7439684295900798589478879)
    ·
      refine ⟨11159526443851197884218319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7439684295900798589478879 11159526443851197884218319)
      ·
        refine ⟨16739289665776796826327479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11159526443851197884218319 16739289665776796826327479)
        ·
          refine ⟨25108934498665195239491219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16739289665776796826327479 25108934498665195239491219)
          ·
            refine ⟨37663401747997792859236829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25108934498665195239491219 37663401747997792859236829)
            ·
              refine ⟨14123775655499172322213811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37663401747997792859236829 14123775655499172322213811)
              ·
                refine ⟨21185663483248758483320717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14123775655499172322213811 21185663483248758483320717)
                ·
                  refine ⟨7944623806218284431245269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21185663483248758483320717 7944623806218284431245269)
                  ·
                    refine ⟨186202120458241041357311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7944623806218284431245269 186202120458241041357311)
                    ·
                      rfl

theorem cell22_543941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 3, 7].length) (baseStart_543941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_543941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_543941 prefixEnd_543941 := by exact prefixLift 543941
  have htrace : WordTrace (prefixWord ++ tailWord_543941) baseStart_543941 baseEnd_543941 := by
    simpa [prefixWord, tailWord_543941, baseEnd_543941] using wordTrace_append hprefix tailTrace_543941
  have hstable : (prefixWord ++ tailWord_543941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543941).length < 2 ^ (prefixWord ++ tailWord_543941).sum := by decide
  have hdescent : baseEnd_543941 < baseStart_543941 := by decide
  rcases family_descends (prefixWord ++ tailWord_543941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544037 : List Nat := [1, 3, 1, 2, 4, 2, 1, 3, 2, 3]
def baseStart_544037 : Nat := 118140960795 + 544037 * 2 ^ 59
def prefixEnd_544037 : Nat := 4983230072969 + 3 ^ 40 * 544037 * 2
def baseEnd_544037 : Nat := 186234983220128790957017

theorem tailTrace_544037 : CollatzResearch.WordTrace tailWord_544037 prefixEnd_544037 186234983220128790957017 := by
  unfold tailWord_544037
  simp only [CollatzResearch.WordTrace]
  refine ⟨19842659530054337967438365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13228439686702891978292243 19842659530054337967438365)
  ·
    refine ⟨7440997323770376737789387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19842659530054337967438365 7440997323770376737789387)
    ·
      refine ⟨11161495985655565106684081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7440997323770376737789387 11161495985655565106684081)
      ·
        refine ⟨8371121989241673830013061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11161495985655565106684081 8371121989241673830013061)
        ·
          refine ⟨1569585372982813843127449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8371121989241673830013061 1569585372982813843127449)
          ·
            refine ⟨1177189029737110382345587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1569585372982813843127449 1177189029737110382345587)
            ·
              refine ⟨1765783544605665573518381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1177189029737110382345587 1765783544605665573518381)
              ·
                refine ⟨662168829227124590069393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1765783544605665573518381 662168829227124590069393)
                ·
                  refine ⟨496626621920343442552045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 662168829227124590069393 496626621920343442552045)
                  ·
                    refine ⟨186234983220128790957017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 496626621920343442552045 186234983220128790957017)
                    ·
                      rfl

theorem cell22_544037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 3, 2, 3].length) (baseStart_544037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_544037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_544037 prefixEnd_544037 := by exact prefixLift 544037
  have htrace : WordTrace (prefixWord ++ tailWord_544037) baseStart_544037 baseEnd_544037 := by
    simpa [prefixWord, tailWord_544037, baseEnd_544037] using wordTrace_append hprefix tailTrace_544037
  have hstable : (prefixWord ++ tailWord_544037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544037).length < 2 ^ (prefixWord ++ tailWord_544037).sum := by decide
  have hdescent : baseEnd_544037 < baseStart_544037 := by decide
  rcases family_descends (prefixWord ++ tailWord_544037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544052 : List Nat := [2, 5, 1, 1, 1, 1, 4, 1, 2, 4]
def baseStart_544052 : Nat := 118140960795 + 544052 * 2 ^ 59
def prefixEnd_544052 : Nat := 4983230072969 + 3 ^ 40 * 544052 * 2
def baseEnd_544052 : Nat := 186240118026673751831971

theorem tailTrace_544052 : CollatzResearch.WordTrace tailWord_544052 prefixEnd_544052 186240118026673751831971 := by
  unfold tailWord_544052
  simp only [CollatzResearch.WordTrace]
  refine ⟨9921603312499997764617205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13228804416666663686156273 9921603312499997764617205)
  ·
    refine ⟨930150310546874790432863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9921603312499997764617205 930150310546874790432863)
    ·
      refine ⟨1395225465820312185649295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 930150310546874790432863 1395225465820312185649295)
      ·
        refine ⟨2092838198730468278473943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1395225465820312185649295 2092838198730468278473943)
        ·
          refine ⟨3139257298095702417710915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2092838198730468278473943 3139257298095702417710915)
          ·
            refine ⟨4708885947143553626566373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3139257298095702417710915 4708885947143553626566373)
            ·
              refine ⟨882916115089416304981195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4708885947143553626566373 882916115089416304981195)
              ·
                refine ⟨1324374172634124457471793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 882916115089416304981195 1324374172634124457471793)
                ·
                  refine ⟨993280629475593343103845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1324374172634124457471793 993280629475593343103845)
                  ·
                    refine ⟨186240118026673751831971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 993280629475593343103845 186240118026673751831971)
                    ·
                      rfl

theorem cell22_544052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_544052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_544052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_544052 prefixEnd_544052 := by exact prefixLift 544052
  have htrace : WordTrace (prefixWord ++ tailWord_544052) baseStart_544052 baseEnd_544052 := by
    simpa [prefixWord, tailWord_544052, baseEnd_544052] using wordTrace_append hprefix tailTrace_544052
  have hstable : (prefixWord ++ tailWord_544052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544052).length < 2 ^ (prefixWord ++ tailWord_544052).sum := by decide
  have hdescent : baseEnd_544052 < baseStart_544052 := by decide
  rcases family_descends (prefixWord ++ tailWord_544052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544054 : List Nat := [5, 1, 2, 3, 1, 1, 1, 2, 1, 5]
def baseStart_544054 : Nat := 118140960795 + 544054 * 2 ^ 59
def prefixEnd_544054 : Nat := 4983230072969 + 3 ^ 40 * 544054 * 2
def baseEnd_544054 : Nat := 186240802667546413281965

theorem tailTrace_544054 : CollatzResearch.WordTrace tailWord_544054 prefixEnd_544054 186240802667546413281965 := by
  unfold tailWord_544054
  simp only [CollatzResearch.WordTrace]
  refine ⟨1240204973187046866925451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13228853047328499913871477 1240204973187046866925451)
  ·
    refine ⟨1860307459780570300388177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1240204973187046866925451 1860307459780570300388177)
    ·
      refine ⟨1395230594835427725291133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1860307459780570300388177 1395230594835427725291133)
      ·
        refine ⟨523211473063285396984175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1395230594835427725291133 523211473063285396984175)
        ·
          refine ⟨784817209594928095476263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 523211473063285396984175 784817209594928095476263)
          ·
            refine ⟨1177225814392392143214395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 784817209594928095476263 1177225814392392143214395)
            ·
              refine ⟨1765838721588588214821593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1177225814392392143214395 1765838721588588214821593)
              ·
                refine ⟨1324379041191441161116195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1765838721588588214821593 1324379041191441161116195)
                ·
                  refine ⟨1986568561787161741674293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1324379041191441161116195 1986568561787161741674293)
                  ·
                    refine ⟨186240802667546413281965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1986568561787161741674293 186240802667546413281965)
                    ·
                      rfl

theorem cell22_544054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 2, 1, 5].length) (baseStart_544054 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_544054 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_544054 prefixEnd_544054 := by exact prefixLift 544054
  have htrace : WordTrace (prefixWord ++ tailWord_544054) baseStart_544054 baseEnd_544054 := by
    simpa [prefixWord, tailWord_544054, baseEnd_544054] using wordTrace_append hprefix tailTrace_544054
  have hstable : (prefixWord ++ tailWord_544054).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544054).length < 2 ^ (prefixWord ++ tailWord_544054).sum := by decide
  have hdescent : baseEnd_544054 < baseStart_544054 := by decide
  rcases family_descends (prefixWord ++ tailWord_544054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544123 : List Nat := [1, 1, 1, 1, 1, 6, 1, 2, 8]
def baseStart_544123 : Nat := 118140960795 + 544123 * 2 ^ 59
def prefixEnd_544123 : Nat := 4983230072969 + 3 ^ 40 * 544123 * 2
def baseEnd_544123 : Nat := 62088140925884411102251

theorem tailTrace_544123 : CollatzResearch.WordTrace tailWord_544123 prefixEnd_544123 62088140925884411102251 := by
  unfold tailWord_544123
  simp only [CollatzResearch.WordTrace]
  refine ⟨19845796207742774655069023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13230530805161849770046015 19845796207742774655069023)
  ·
    refine ⟨29768694311614161982603535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19845796207742774655069023 29768694311614161982603535)
    ·
      refine ⟨44653041467421242973905303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29768694311614161982603535 44653041467421242973905303)
      ·
        refine ⟨66979562201131864460857955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44653041467421242973905303 66979562201131864460857955)
        ·
          refine ⟨100469343301697796691286933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66979562201131864460857955 100469343301697796691286933)
          ·
            refine ⟨4709500467267084219904075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 100469343301697796691286933 4709500467267084219904075)
            ·
              refine ⟨7064250700900626329856113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4709500467267084219904075 7064250700900626329856113)
              ·
                refine ⟨5298188025675469747392085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7064250700900626329856113 5298188025675469747392085)
                ·
                  refine ⟨62088140925884411102251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5298188025675469747392085 62088140925884411102251)
                  ·
                    rfl

theorem cell22_544123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 2, 8].length) (baseStart_544123 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_544123 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_544123 prefixEnd_544123 := by exact prefixLift 544123
  have htrace : WordTrace (prefixWord ++ tailWord_544123) baseStart_544123 baseEnd_544123 := by
    simpa [prefixWord, tailWord_544123, baseEnd_544123] using wordTrace_append hprefix tailTrace_544123
  have hstable : (prefixWord ++ tailWord_544123).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544123).length < 2 ^ (prefixWord ++ tailWord_544123).sum := by decide
  have hdescent : baseEnd_544123 < baseStart_544123 := by decide
  rcases family_descends (prefixWord ++ tailWord_544123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544129 : List Nat := [1, 2, 4, 3, 2, 2, 1, 2, 5]
def baseStart_544129 : Nat := 118140960795 + 544129 * 2 ^ 59
def prefixEnd_544129 : Nat := 4983230072969 + 3 ^ 40 * 544129 * 2
def baseEnd_544129 : Nat := 62088825566757072552245

theorem tailTrace_544129 : CollatzResearch.WordTrace tailWord_544129 prefixEnd_544129 62088825566757072552245 := by
  unfold tailWord_544129
  simp only [CollatzResearch.WordTrace]
  refine ⟨19846015045721037679787441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13230676697147358453191627 19846015045721037679787441)
  ·
    refine ⟨14884511284290778259840581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19846015045721037679787441 14884511284290778259840581)
    ·
      refine ⟨2790845865804520923720109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14884511284290778259840581 2790845865804520923720109)
      ·
        refine ⟨1046567199676695346395041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2790845865804520923720109 1046567199676695346395041)
        ·
          refine ⟨784925399757521509796281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1046567199676695346395041 784925399757521509796281)
          ·
            refine ⟨588694049818141132347211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 784925399757521509796281 588694049818141132347211)
            ·
              refine ⟨883041074727211698520817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 588694049818141132347211 883041074727211698520817)
              ·
                refine ⟨662280806045408773890613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 883041074727211698520817 662280806045408773890613)
                ·
                  refine ⟨62088825566757072552245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 662280806045408773890613 62088825566757072552245)
                  ·
                    rfl

theorem cell22_544129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 1, 2, 5].length) (baseStart_544129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_544129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_544129 prefixEnd_544129 := by exact prefixLift 544129
  have htrace : WordTrace (prefixWord ++ tailWord_544129) baseStart_544129 baseEnd_544129 := by
    simpa [prefixWord, tailWord_544129, baseEnd_544129] using wordTrace_append hprefix tailTrace_544129
  have hstable : (prefixWord ++ tailWord_544129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544129).length < 2 ^ (prefixWord ++ tailWord_544129).sum := by decide
  have hdescent : baseEnd_544129 < baseStart_544129 := by decide
  rcases family_descends (prefixWord ++ tailWord_544129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544140 : List Nat := [2, 2, 1, 2, 1, 3, 4, 1, 6]
def baseStart_544140 : Nat := 118140960795 + 544140 * 2 ^ 59
def prefixEnd_544140 : Nat := 4983230072969 + 3 ^ 40 * 544140 * 2
def baseEnd_544140 : Nat := 62090080741690285210567

theorem tailTrace_544140 : CollatzResearch.WordTrace tailWord_544140 prefixEnd_544140 62090080741690285210567 := by
  unfold tailWord_544140
  simp only [CollatzResearch.WordTrace]
  refine ⟨9923208124340593279218937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13230944165787457705625249 9923208124340593279218937)
  ·
    refine ⟨7442406093255444959414203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9923208124340593279218937 7442406093255444959414203)
    ·
      refine ⟨11163609139883167439121305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7442406093255444959414203 11163609139883167439121305)
      ·
        refine ⟨8372706854912375579340979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11163609139883167439121305 8372706854912375579340979)
        ·
          refine ⟨12559060282368563369011469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8372706854912375579340979 12559060282368563369011469)
          ·
            refine ⟨4709647605888211263379301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12559060282368563369011469 4709647605888211263379301)
            ·
              refine ⟨883058926104039611883619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4709647605888211263379301 883058926104039611883619)
              ·
                refine ⟨1324588389156059417825429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 883058926104039611883619 1324588389156059417825429)
                ·
                  refine ⟨62090080741690285210567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1324588389156059417825429 62090080741690285210567)
                  ·
                    rfl

theorem cell22_544140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 4, 1, 6].length) (baseStart_544140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_544140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_544140 prefixEnd_544140 := by exact prefixLift 544140
  have htrace : WordTrace (prefixWord ++ tailWord_544140) baseStart_544140 baseEnd_544140 := by
    simpa [prefixWord, tailWord_544140, baseEnd_544140] using wordTrace_append hprefix tailTrace_544140
  have hstable : (prefixWord ++ tailWord_544140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544140).length < 2 ^ (prefixWord ++ tailWord_544140).sum := by decide
  have hdescent : baseEnd_544140 < baseStart_544140 := by decide
  rcases family_descends (prefixWord ++ tailWord_544140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544146 : List Nat := [3, 2, 3, 3, 1, 1, 3, 1, 5]
def baseStart_544146 : Nat := 118140960795 + 544146 * 2 ^ 59
def prefixEnd_544146 : Nat := 4983230072969 + 3 ^ 40 * 544146 * 2
def baseEnd_544146 : Nat := 62090765382562946660561

theorem tailTrace_544146 : CollatzResearch.WordTrace tailWord_544146 prefixEnd_544146 62090765382562946660561 := by
  unfold tailWord_544146
  simp only [CollatzResearch.WordTrace]
  refine ⟨4961658771664862395789073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13231090057772966388770861 4961658771664862395789073)
  ·
    refine ⟨3721244078748646796841805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4961658771664862395789073 3721244078748646796841805)
    ·
      refine ⟨1395466529530742548815677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3721244078748646796841805 1395466529530742548815677)
      ·
        refine ⟨523299948574028455805879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1395466529530742548815677 523299948574028455805879)
        ·
          refine ⟨784949922861042683708819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 523299948574028455805879 784949922861042683708819)
          ·
            refine ⟨1177424884291564025563229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 784949922861042683708819 1177424884291564025563229)
            ·
              refine ⟨441534331609336509586211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1177424884291564025563229 441534331609336509586211)
              ·
                refine ⟨662301497414004764379317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 441534331609336509586211 662301497414004764379317)
                ·
                  refine ⟨62090765382562946660561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 662301497414004764379317 62090765382562946660561)
                  ·
                    rfl

theorem cell22_544146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 3, 1, 5].length) (baseStart_544146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_544146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_544146 prefixEnd_544146 := by exact prefixLift 544146
  have htrace : WordTrace (prefixWord ++ tailWord_544146) baseStart_544146 baseEnd_544146 := by
    simpa [prefixWord, tailWord_544146, baseEnd_544146] using wordTrace_append hprefix tailTrace_544146
  have hstable : (prefixWord ++ tailWord_544146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544146).length < 2 ^ (prefixWord ++ tailWord_544146).sum := by decide
  have hdescent : baseEnd_544146 < baseStart_544146 := by decide
  rcases family_descends (prefixWord ++ tailWord_544146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544275 : List Nat := [1, 1, 1, 2, 1, 6, 1, 1, 8]
def baseStart_544275 : Nat := 118140960795 + 544275 * 2 ^ 59
def prefixEnd_544275 : Nat := 4983230072969 + 3 ^ 40 * 544275 * 2
def baseEnd_544275 : Nat := 62105485161325167835429

theorem tailTrace_544275 : CollatzResearch.WordTrace tailWord_544275 prefixEnd_544275 62105485161325167835429 := by
  unfold tailWord_544275
  simp only [CollatzResearch.WordTrace]
  refine ⟨19851340103192104614602279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13234226735461403076401519 19851340103192104614602279)
  ·
    refine ⟨29777010154788156921903419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19851340103192104614602279 29777010154788156921903419)
    ·
      refine ⟨44665515232182235382855129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29777010154788156921903419 44665515232182235382855129)
      ·
        refine ⟨33499136424136676537141347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44665515232182235382855129 33499136424136676537141347)
        ·
          refine ⟨50248704636205014805712021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33499136424136676537141347 50248704636205014805712021)
          ·
            refine ⟨2355408029822110069017751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 50248704636205014805712021 2355408029822110069017751)
            ·
              refine ⟨3533112044733165103526627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2355408029822110069017751 3533112044733165103526627)
              ·
                refine ⟨5299668067099747655289941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3533112044733165103526627 5299668067099747655289941)
                ·
                  refine ⟨62105485161325167835429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5299668067099747655289941 62105485161325167835429)
                  ·
                    rfl

theorem cell22_544275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 1, 8].length) (baseStart_544275 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_544275 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_544275 prefixEnd_544275 := by exact prefixLift 544275
  have htrace : WordTrace (prefixWord ++ tailWord_544275) baseStart_544275 baseEnd_544275 := by
    simpa [prefixWord, tailWord_544275, baseEnd_544275] using wordTrace_append hprefix tailTrace_544275
  have hstable : (prefixWord ++ tailWord_544275).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544275).length < 2 ^ (prefixWord ++ tailWord_544275).sum := by decide
  have hdescent : baseEnd_544275 < baseStart_544275 := by decide
  rcases family_descends (prefixWord ++ tailWord_544275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544277 : List Nat := [1, 3, 2, 1, 3, 2, 2, 1, 3, 4]
def baseStart_544277 : Nat := 118140960795 + 544277 * 2 ^ 59
def prefixEnd_544277 : Nat := 4983230072969 + 3 ^ 40 * 544277 * 2
def baseEnd_544277 : Nat := 186317140124848164956281

theorem tailTrace_544277 : CollatzResearch.WordTrace tailWord_544277 prefixEnd_544277 186317140124848164956281 := by
  unfold tailWord_544277
  simp only [CollatzResearch.WordTrace]
  refine ⟨19851413049184858956175085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13234275366123239304116723 19851413049184858956175085)
  ·
    refine ⟨7444279893444322108565657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19851413049184858956175085 7444279893444322108565657)
    ·
      refine ⟨5583209920083241581424243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7444279893444322108565657 5583209920083241581424243)
      ·
        refine ⟨8374814880124862372136365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5583209920083241581424243 8374814880124862372136365)
        ·
          refine ⟨3140555580046823389551137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8374814880124862372136365 3140555580046823389551137)
          ·
            refine ⟨2355416685035117542163353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3140555580046823389551137 2355416685035117542163353)
            ·
              refine ⟨1766562513776338156622515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2355416685035117542163353 1766562513776338156622515)
              ·
                refine ⟨2649843770664507234933773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1766562513776338156622515 2649843770664507234933773)
                ·
                  refine ⟨993691413999190213100165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2649843770664507234933773 993691413999190213100165)
                  ·
                    refine ⟨186317140124848164956281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 993691413999190213100165 186317140124848164956281)
                    ·
                      rfl

theorem cell22_544277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 1, 3, 4].length) (baseStart_544277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_544277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_544277 prefixEnd_544277 := by exact prefixLift 544277
  have htrace : WordTrace (prefixWord ++ tailWord_544277) baseStart_544277 baseEnd_544277 := by
    simpa [prefixWord, tailWord_544277, baseEnd_544277] using wordTrace_append hprefix tailTrace_544277
  have hstable : (prefixWord ++ tailWord_544277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544277).length < 2 ^ (prefixWord ++ tailWord_544277).sum := by decide
  have hdescent : baseEnd_544277 < baseStart_544277 := by decide
  rcases family_descends (prefixWord ++ tailWord_544277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544309 : List Nat := [1, 3, 3, 1, 1, 3, 2, 4, 4]
def baseStart_544309 : Nat := 118140960795 + 544309 * 2 ^ 59
def prefixEnd_544309 : Nat := 4983230072969 + 3 ^ 40 * 544309 * 2
def baseEnd_544309 : Nat := 62109364792936916052061

theorem tailTrace_544309 : CollatzResearch.WordTrace tailWord_544309 prefixEnd_544309 62109364792936916052061 := by
  unfold tailWord_544309
  simp only [CollatzResearch.WordTrace]
  refine ⟨19852580185068928421339981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13235053456712618947559987 19852580185068928421339981)
  ·
    refine ⟨7444717569400848158002493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19852580185068928421339981 7444717569400848158002493)
    ·
      refine ⟨2791769088525318059250935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7444717569400848158002493 2791769088525318059250935)
      ·
        refine ⟨4187653632787977088876403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2791769088525318059250935 4187653632787977088876403)
        ·
          refine ⟨6281480449181965633314605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4187653632787977088876403 6281480449181965633314605)
          ·
            refine ⟨2355555168443237112492977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6281480449181965633314605 2355555168443237112492977)
            ·
              refine ⟨1766666376332427834369733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2355555168443237112492977 1766666376332427834369733)
              ·
                refine ⟨331249945562330218944325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1766666376332427834369733 331249945562330218944325)
                ·
                  refine ⟨62109364792936916052061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 331249945562330218944325 62109364792936916052061)
                  ·
                    rfl

theorem cell22_544309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 4, 4].length) (baseStart_544309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_544309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_544309 prefixEnd_544309 := by exact prefixLift 544309
  have htrace : WordTrace (prefixWord ++ tailWord_544309) baseStart_544309 baseEnd_544309 := by
    simpa [prefixWord, tailWord_544309, baseEnd_544309] using wordTrace_append hprefix tailTrace_544309
  have hstable : (prefixWord ++ tailWord_544309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544309).length < 2 ^ (prefixWord ++ tailWord_544309).sum := by decide
  have hdescent : baseEnd_544309 < baseStart_544309 := by decide
  rcases family_descends (prefixWord ++ tailWord_544309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544320 : List Nat := [2, 1, 1, 2, 2, 2, 1, 11]
def baseStart_544320 : Nat := 118140960795 + 544320 * 2 ^ 59
def prefixEnd_544320 : Nat := 4983230072969 + 3 ^ 40 * 544320 * 2
def baseEnd_544320 : Nat := 20703539989290042903461

theorem tailTrace_544320 : CollatzResearch.WordTrace tailWord_544320 prefixEnd_544320 20703539989290042903461 := by
  unfold tailWord_544320
  simp only [CollatzResearch.WordTrace]
  refine ⟨9926490694014538649995207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13235320925352718199993609 9926490694014538649995207)
  ·
    refine ⟨14889736041021807974992811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9926490694014538649995207 14889736041021807974992811)
    ·
      refine ⟨22334604061532711962489217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14889736041021807974992811 22334604061532711962489217)
      ·
        refine ⟨16750953046149533971866913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22334604061532711962489217 16750953046149533971866913)
        ·
          refine ⟨12563214784612150478900185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16750953046149533971866913 12563214784612150478900185)
          ·
            refine ⟨9422411088459112859175139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12563214784612150478900185 9422411088459112859175139)
            ·
              refine ⟨14133616632688669288762709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9422411088459112859175139 14133616632688669288762709)
              ·
                refine ⟨20703539989290042903461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 14133616632688669288762709 20703539989290042903461)
                ·
                  rfl

theorem cell22_544320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 11].length) (baseStart_544320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_544320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_544320 prefixEnd_544320 := by exact prefixLift 544320
  have htrace : WordTrace (prefixWord ++ tailWord_544320) baseStart_544320 baseEnd_544320 := by
    simpa [prefixWord, tailWord_544320, baseEnd_544320] using wordTrace_append hprefix tailTrace_544320
  have hstable : (prefixWord ++ tailWord_544320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544320).length < 2 ^ (prefixWord ++ tailWord_544320).sum := by decide
  have hdescent : baseEnd_544320 < baseStart_544320 := by decide
  rcases family_descends (prefixWord ++ tailWord_544320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544335 : List Nat := [1, 1, 2, 1, 1, 2, 3, 1, 1, 9]
def baseStart_544335 : Nat := 118140960795 + 544335 * 2 ^ 59
def prefixEnd_544335 : Nat := 4983230072969 + 3 ^ 40 * 544335 * 2
def baseEnd_544335 : Nat := 186336994710155347006103

theorem tailTrace_544335 : CollatzResearch.WordTrace tailWord_544335 prefixEnd_544335 186336994710155347006103 := by
  unfold tailWord_544335
  simp only [CollatzResearch.WordTrace]
  refine ⟨19853528482974734861786459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13235685655316489907857639 19853528482974734861786459)
  ·
    refine ⟨29780292724462102292679689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19853528482974734861786459 29780292724462102292679689)
    ·
      refine ⟨22335219543346576719509767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29780292724462102292679689 22335219543346576719509767)
      ·
        refine ⟨33502829315019865079264651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22335219543346576719509767 33502829315019865079264651)
        ·
          refine ⟨50254243972529797618896977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33502829315019865079264651 50254243972529797618896977)
          ·
            refine ⟨37690682979397348214172733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50254243972529797618896977 37690682979397348214172733)
            ·
              refine ⟨14134006117274005580314775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37690682979397348214172733 14134006117274005580314775)
              ·
                refine ⟨21201009175911008370472163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14134006117274005580314775 21201009175911008370472163)
                ·
                  refine ⟨31801513763866512555708245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21201009175911008370472163 31801513763866512555708245)
                  ·
                    refine ⟨186336994710155347006103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 31801513763866512555708245 186336994710155347006103)
                    ·
                      rfl

theorem cell22_544335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 9].length) (baseStart_544335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_544335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_544335 prefixEnd_544335 := by exact prefixLift 544335
  have htrace : WordTrace (prefixWord ++ tailWord_544335) baseStart_544335 baseEnd_544335 := by
    simpa [prefixWord, tailWord_544335, baseEnd_544335] using wordTrace_append hprefix tailTrace_544335
  have hstable : (prefixWord ++ tailWord_544335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544335).length < 2 ^ (prefixWord ++ tailWord_544335).sum := by decide
  have hdescent : baseEnd_544335 < baseStart_544335 := by decide
  rcases family_descends (prefixWord ++ tailWord_544335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544420 : List Nat := [2, 3, 1, 2, 2, 4, 2, 2, 1, 3]
def baseStart_544420 : Nat := 118140960795 + 544420 * 2 ^ 59
def prefixEnd_544420 : Nat := 4983230072969 + 3 ^ 40 * 544420 * 2
def baseEnd_544420 : Nat := 186366091947243458630843

theorem tailTrace_544420 : CollatzResearch.WordTrace tailWord_544420 prefixEnd_544420 186366091947243458630843 := by
  unfold tailWord_544420
  simp only [CollatzResearch.WordTrace]
  refine ⟨9928314343833397189315357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13237752458444529585753809 9928314343833397189315357)
  ·
    refine ⟨3723117878937523945993259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9928314343833397189315357 3723117878937523945993259)
    ·
      refine ⟨5584676818406285918989889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3723117878937523945993259 5584676818406285918989889)
      ·
        refine ⟨4188507613804714439242417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5584676818406285918989889 4188507613804714439242417)
        ·
          refine ⟨3141380710353535829431813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4188507613804714439242417 3141380710353535829431813)
          ·
            refine ⟨589008883191287968018465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3141380710353535829431813 589008883191287968018465)
            ·
              refine ⟨441756662393465976013849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 589008883191287968018465 441756662393465976013849)
              ·
                refine ⟨331317496795099482010387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 441756662393465976013849 331317496795099482010387)
                ·
                  refine ⟨496976245192649223015581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 331317496795099482010387 496976245192649223015581)
                  ·
                    refine ⟨186366091947243458630843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 496976245192649223015581 186366091947243458630843)
                    ·
                      rfl

theorem cell22_544420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 2, 2, 1, 3].length) (baseStart_544420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_544420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_544420 prefixEnd_544420 := by exact prefixLift 544420
  have htrace : WordTrace (prefixWord ++ tailWord_544420) baseStart_544420 baseEnd_544420 := by
    simpa [prefixWord, tailWord_544420, baseEnd_544420] using wordTrace_append hprefix tailTrace_544420
  have hstable : (prefixWord ++ tailWord_544420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544420).length < 2 ^ (prefixWord ++ tailWord_544420).sum := by decide
  have hdescent : baseEnd_544420 < baseStart_544420 := by decide
  rcases family_descends (prefixWord ++ tailWord_544420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544429 : List Nat := [1, 5, 2, 1, 1, 1, 1, 1, 5, 4]
def baseStart_544429 : Nat := 118140960795 + 544429 * 2 ^ 59
def prefixEnd_544429 : Nat := 4983230072969 + 3 ^ 40 * 544429 * 2
def baseEnd_544429 : Nat := 186369172831170435155815

theorem tailTrace_544429 : CollatzResearch.WordTrace tailWord_544429 prefixEnd_544429 186369172831170435155815 := by
  unfold tailWord_544429
  simp only [CollatzResearch.WordTrace]
  refine ⟨19856956944634188915708341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13237971296422792610472227 19856956944634188915708341)
  ·
    refine ⟨1861589713559455210847657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19856956944634188915708341 1861589713559455210847657)
    ·
      refine ⟨1396192285169591408135743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1861589713559455210847657 1396192285169591408135743)
      ·
        refine ⟨2094288427754387112203615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1396192285169591408135743 2094288427754387112203615)
        ·
          refine ⟨3141432641631580668305423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2094288427754387112203615 3141432641631580668305423)
          ·
            refine ⟨4712148962447371002458135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3141432641631580668305423 4712148962447371002458135)
            ·
              refine ⟨7068223443671056503687203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4712148962447371002458135 7068223443671056503687203)
              ·
                refine ⟨10602335165506584755530805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7068223443671056503687203 10602335165506584755530805)
                ·
                  refine ⟨993968921766242320831013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10602335165506584755530805 993968921766242320831013)
                  ·
                    refine ⟨186369172831170435155815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 993968921766242320831013 186369172831170435155815)
                    ·
                      rfl

theorem cell22_544429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_544429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_544429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_544429 prefixEnd_544429 := by exact prefixLift 544429
  have htrace : WordTrace (prefixWord ++ tailWord_544429) baseStart_544429 baseEnd_544429 := by
    simpa [prefixWord, tailWord_544429, baseEnd_544429] using wordTrace_append hprefix tailTrace_544429
  have hstable : (prefixWord ++ tailWord_544429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544429).length < 2 ^ (prefixWord ++ tailWord_544429).sum := by decide
  have hdescent : baseEnd_544429 < baseStart_544429 := by decide
  rcases family_descends (prefixWord ++ tailWord_544429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544444 : List Nat := [2, 2, 2, 3, 1, 3, 1, 2, 6]
def baseStart_544444 : Nat := 118140960795 + 544444 * 2 ^ 59
def prefixEnd_544444 : Nat := 4983230072969 + 3 ^ 40 * 544444 * 2
def baseEnd_544444 : Nat := 62124769212571798676923

theorem tailTrace_544444 : CollatzResearch.WordTrace tailWord_544444 prefixEnd_544444 62124769212571798676923 := by
  unfold tailWord_544444
  simp only [CollatzResearch.WordTrace]
  refine ⟨9928752019789923238752193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13238336026386564318336257 9928752019789923238752193)
  ·
    refine ⟨7446564014842442429064145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9928752019789923238752193 7446564014842442429064145)
    ·
      refine ⟨5584923011131831821798109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7446564014842442429064145 5584923011131831821798109)
      ·
        refine ⟨2094346129174436933174291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5584923011131831821798109 2094346129174436933174291)
        ·
          refine ⟨3141519193761655399761437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2094346129174436933174291 3141519193761655399761437)
          ·
            refine ⟨1178069697660620774910539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3141519193761655399761437 1178069697660620774910539)
            ·
              refine ⟨1767104546490931162365809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1178069697660620774910539 1767104546490931162365809)
              ·
                refine ⟨1325328409868198371774357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1767104546490931162365809 1325328409868198371774357)
                ·
                  refine ⟨62124769212571798676923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1325328409868198371774357 62124769212571798676923)
                  ·
                    rfl

theorem cell22_544444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 2, 6].length) (baseStart_544444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_544444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_544444 prefixEnd_544444 := by exact prefixLift 544444
  have htrace : WordTrace (prefixWord ++ tailWord_544444) baseStart_544444 baseEnd_544444 := by
    simpa [prefixWord, tailWord_544444, baseEnd_544444] using wordTrace_append hprefix tailTrace_544444
  have hstable : (prefixWord ++ tailWord_544444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544444).length < 2 ^ (prefixWord ++ tailWord_544444).sum := by decide
  have hdescent : baseEnd_544444 < baseStart_544444 := by decide
  rcases family_descends (prefixWord ++ tailWord_544444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544472 : List Nat := [2, 1, 2, 2, 3, 1, 11]
def baseStart_544472 : Nat := 118140960795 + 544472 * 2 ^ 59
def prefixEnd_544472 : Nat := 4983230072969 + 3 ^ 40 * 544472 * 2
def baseEnd_544472 : Nat := 6903107133701209493729

theorem tailTrace_544472 : CollatzResearch.WordTrace tailWord_544472 prefixEnd_544472 6903107133701209493729 := by
  unfold tailWord_544472
  simp only [CollatzResearch.WordTrace]
  refine ⟨9929262641739203629761835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13239016855652271506349113 9929262641739203629761835)
  ·
    refine ⟨14893893962608805444642753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9929262641739203629761835 14893893962608805444642753)
    ·
      refine ⟨11170420471956604083482065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14893893962608805444642753 11170420471956604083482065)
      ·
        refine ⟨8377815353967453062611549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11170420471956604083482065 8377815353967453062611549)
        ·
          refine ⟨3141680757737794898479331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8377815353967453062611549 3141680757737794898479331)
          ·
            refine ⟨4712521136606692347718997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3141680757737794898479331 4712521136606692347718997)
            ·
              refine ⟨6903107133701209493729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 4712521136606692347718997 6903107133701209493729)
              ·
                rfl

theorem cell22_544472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 11].length) (baseStart_544472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_544472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_544472 prefixEnd_544472 := by exact prefixLift 544472
  have htrace : WordTrace (prefixWord ++ tailWord_544472) baseStart_544472 baseEnd_544472 := by
    simpa [prefixWord, tailWord_544472, baseEnd_544472] using wordTrace_append hprefix tailTrace_544472
  have hstable : (prefixWord ++ tailWord_544472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544472).length < 2 ^ (prefixWord ++ tailWord_544472).sum := by decide
  have hdescent : baseEnd_544472 < baseStart_544472 := by decide
  rcases family_descends (prefixWord ++ tailWord_544472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544504 : List Nat := [2, 1, 2, 1, 1, 2, 2, 3, 5, 3]
def baseStart_544504 : Nat := 118140960795 + 544504 * 2 ^ 59
def prefixEnd_544504 : Nat := 4983230072969 + 3 ^ 40 * 544504 * 2
def baseEnd_544504 : Nat := 186394846863895239530585

theorem tailTrace_544504 : CollatzResearch.WordTrace tailWord_544504 prefixEnd_544504 186394846863895239530585 := by
  unfold tailWord_544504
  simp only [CollatzResearch.WordTrace]
  refine ⟨9929846209681238362344283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13239794946241651149792377 9929846209681238362344283)
  ·
    refine ⟨14894769314521857543516425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9929846209681238362344283 14894769314521857543516425)
    ·
      refine ⟨11171076985891393157637319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14894769314521857543516425 11171076985891393157637319)
      ·
        refine ⟨16756615478837089736455979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11171076985891393157637319 16756615478837089736455979)
        ·
          refine ⟨25134923218255634604683969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16756615478837089736455979 25134923218255634604683969)
          ·
            refine ⟨18851192413691725953512977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25134923218255634604683969 18851192413691725953512977)
            ·
              refine ⟨14138394310268794465134733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18851192413691725953512977 14138394310268794465134733)
              ·
                refine ⟨5301897866350797924425525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14138394310268794465134733 5301897866350797924425525)
                ·
                  refine ⟨497052924970387305414893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5301897866350797924425525 497052924970387305414893)
                  ·
                    refine ⟨186394846863895239530585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 497052924970387305414893 186394846863895239530585)
                    ·
                      rfl

theorem cell22_544504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 3, 5, 3].length) (baseStart_544504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_544504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_544504 prefixEnd_544504 := by exact prefixLift 544504
  have htrace : WordTrace (prefixWord ++ tailWord_544504) baseStart_544504 baseEnd_544504 := by
    simpa [prefixWord, tailWord_544504, baseEnd_544504] using wordTrace_append hprefix tailTrace_544504
  have hstable : (prefixWord ++ tailWord_544504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544504).length < 2 ^ (prefixWord ++ tailWord_544504).sum := by decide
  have hdescent : baseEnd_544504 < baseStart_544504 := by decide
  rcases family_descends (prefixWord ++ tailWord_544504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544538 : List Nat := [3, 1, 1, 3, 2, 4, 1, 1, 3, 3]
def baseStart_544538 : Nat := 118140960795 + 544538 * 2 ^ 59
def prefixEnd_544538 : Nat := 4983230072969 + 3 ^ 40 * 544538 * 2
def baseEnd_544538 : Nat := 186406485758730484180481

theorem tailTrace_544538 : CollatzResearch.WordTrace tailWord_544538 prefixEnd_544538 186406485758730484180481 := by
  unfold tailWord_544538
  simp only [CollatzResearch.WordTrace]
  refine ⟨4965233125309825132856567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13240621667492867020950845 4965233125309825132856567)
  ·
    refine ⟨7447849687964737699284851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4965233125309825132856567 7447849687964737699284851)
    ·
      refine ⟨11171774531947106548927277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7447849687964737699284851 11171774531947106548927277)
      ·
        refine ⟨4189415449480164955847729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11171774531947106548927277 4189415449480164955847729)
        ·
          refine ⟨3142061587110123716885797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4189415449480164955847729 3142061587110123716885797)
          ·
            refine ⟨589136547583148196916087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3142061587110123716885797 589136547583148196916087)
            ·
              refine ⟨883704821374722295374131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 589136547583148196916087 883704821374722295374131)
              ·
                refine ⟨1325557232062083443061197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 883704821374722295374131 1325557232062083443061197)
                ·
                  refine ⟨497083962023281291147949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1325557232062083443061197 497083962023281291147949)
                  ·
                    refine ⟨186406485758730484180481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 497083962023281291147949 186406485758730484180481)
                    ·
                      rfl

theorem cell22_544538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 1, 1, 3, 3].length) (baseStart_544538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_544538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_544538 prefixEnd_544538 := by exact prefixLift 544538
  have htrace : WordTrace (prefixWord ++ tailWord_544538) baseStart_544538 baseEnd_544538 := by
    simpa [prefixWord, tailWord_544538, baseEnd_544538] using wordTrace_append hprefix tailTrace_544538
  have hstable : (prefixWord ++ tailWord_544538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544538).length < 2 ^ (prefixWord ++ tailWord_544538).sum := by decide
  have hdescent : baseEnd_544538 < baseStart_544538 := by decide
  rcases family_descends (prefixWord ++ tailWord_544538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544589 : List Nat := [1, 6, 1, 2, 1, 3, 2, 2, 1, 3]
def baseStart_544589 : Nat := 118140960795 + 544589 * 2 ^ 59
def prefixEnd_544589 : Nat := 4983230072969 + 3 ^ 40 * 544589 * 2
def baseEnd_544589 : Nat := 186423944100983351155325

theorem tailTrace_544589 : CollatzResearch.WordTrace tailWord_544589 prefixEnd_544589 186423944100983351155325 := by
  unfold tailWord_544589
  simp only [CollatzResearch.WordTrace]
  refine ⟨19862792624054536241532821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13241861749369690827688547 19862792624054536241532821)
  ·
    refine ⟨931068404252556386321851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 19862792624054536241532821 931068404252556386321851)
    ·
      refine ⟨1396602606378834579482777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 931068404252556386321851 1396602606378834579482777)
      ·
        refine ⟨1047451954784125934612083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1396602606378834579482777 1047451954784125934612083)
        ·
          refine ⟨1571177932176188901918125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1047451954784125934612083 1571177932176188901918125)
          ·
            refine ⟨589191724566070838219297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1571177932176188901918125 589191724566070838219297)
            ·
              refine ⟨441893793424553128664473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 589191724566070838219297 441893793424553128664473)
              ·
                refine ⟨331420345068414846498355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 441893793424553128664473 331420345068414846498355)
                ·
                  refine ⟨497130517602622269747533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 331420345068414846498355 497130517602622269747533)
                  ·
                    refine ⟨186423944100983351155325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 497130517602622269747533 186423944100983351155325)
                    ·
                      rfl

theorem cell22_544589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 2, 2, 1, 3].length) (baseStart_544589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_544589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_544589 prefixEnd_544589 := by exact prefixLift 544589
  have htrace : WordTrace (prefixWord ++ tailWord_544589) baseStart_544589 baseEnd_544589 := by
    simpa [prefixWord, tailWord_544589, baseEnd_544589] using wordTrace_append hprefix tailTrace_544589
  have hstable : (prefixWord ++ tailWord_544589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544589).length < 2 ^ (prefixWord ++ tailWord_544589).sum := by decide
  have hdescent : baseEnd_544589 < baseStart_544589 := by decide
  rcases family_descends (prefixWord ++ tailWord_544589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544609 : List Nat := [1, 2, 3, 1, 1, 1, 4, 2, 1, 6]
def baseStart_544609 : Nat := 118140960795 + 544609 * 2 ^ 59
def prefixEnd_544609 : Nat := 4983230072969 + 3 ^ 40 * 544609 * 2
def baseEnd_544609 : Nat := 186430790509709965655263

theorem tailTrace_544609 : CollatzResearch.WordTrace tailWord_544609 prefixEnd_544609 186430790509709965655263 := by
  unfold tailWord_544609
  simp only [CollatzResearch.WordTrace]
  refine ⟨19863522083982079657260881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13242348055988053104840587 19863522083982079657260881)
  ·
    refine ⟨14897641562986559742945661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19863522083982079657260881 14897641562986559742945661)
    ·
      refine ⟨5586615586119959903604623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14897641562986559742945661 5586615586119959903604623)
      ·
        refine ⟨8379923379179939855406935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5586615586119959903604623 8379923379179939855406935)
        ·
          refine ⟨12569885068769909783110403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8379923379179939855406935 12569885068769909783110403)
          ·
            refine ⟨18854827603154864674665605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12569885068769909783110403 18854827603154864674665605)
            ·
              refine ⟨3535280175591537126499801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18854827603154864674665605 3535280175591537126499801)
              ·
                refine ⟨2651460131693652844874851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3535280175591537126499801 2651460131693652844874851)
                ·
                  refine ⟨3977190197540479267312277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2651460131693652844874851 3977190197540479267312277)
                  ·
                    refine ⟨186430790509709965655263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3977190197540479267312277 186430790509709965655263)
                    ·
                      rfl

theorem cell22_544609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 2, 1, 6].length) (baseStart_544609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_544609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_544609 prefixEnd_544609 := by exact prefixLift 544609
  have htrace : WordTrace (prefixWord ++ tailWord_544609) baseStart_544609 baseEnd_544609 := by
    simpa [prefixWord, tailWord_544609, baseEnd_544609] using wordTrace_append hprefix tailTrace_544609
  have hstable : (prefixWord ++ tailWord_544609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544609).length < 2 ^ (prefixWord ++ tailWord_544609).sum := by decide
  have hdescent : baseEnd_544609 < baseStart_544609 := by decide
  rcases family_descends (prefixWord ++ tailWord_544609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544656 : List Nat := [2, 1, 1, 1, 1, 1, 2, 7, 3, 3]
def baseStart_544656 : Nat := 118140960795 + 544656 * 2 ^ 59
def prefixEnd_544656 : Nat := 4983230072969 + 3 ^ 40 * 544656 * 2
def baseEnd_544656 : Nat := 186446879570217509730119

theorem tailTrace_544656 : CollatzResearch.WordTrace tailWord_544656 prefixEnd_544656 186446879570217509730119 := by
  unfold tailWord_544656
  simp only [CollatzResearch.WordTrace]
  refine ⟨9932618157405903342110911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13243490876541204456147881 9932618157405903342110911)
  ·
    refine ⟨14898927236108855013166367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9932618157405903342110911 14898927236108855013166367)
    ·
      refine ⟨22348390854163282519749551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14898927236108855013166367 22348390854163282519749551)
      ·
        refine ⟨33522586281244923779624327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22348390854163282519749551 33522586281244923779624327)
        ·
          refine ⟨50283879421867385669436491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33522586281244923779624327 50283879421867385669436491)
          ·
            refine ⟨75425819132801078504154737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50283879421867385669436491 75425819132801078504154737)
            ·
              refine ⟨56569364349600808878116053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75425819132801078504154737 56569364349600808878116053)
              ·
                refine ⟨1325844476943768958080845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 56569364349600808878116053 1325844476943768958080845)
                ·
                  refine ⟨497191678853913359280317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1325844476943768958080845 497191678853913359280317)
                  ·
                    refine ⟨186446879570217509730119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 497191678853913359280317 186446879570217509730119)
                    ·
                      rfl

theorem cell22_544656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 7, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 7, 3, 3].length) (baseStart_544656 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_544656 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_544656 prefixEnd_544656 := by exact prefixLift 544656
  have htrace : WordTrace (prefixWord ++ tailWord_544656) baseStart_544656 baseEnd_544656 := by
    simpa [prefixWord, tailWord_544656, baseEnd_544656] using wordTrace_append hprefix tailTrace_544656
  have hstable : (prefixWord ++ tailWord_544656).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544656).length < 2 ^ (prefixWord ++ tailWord_544656).sum := by decide
  have hdescent : baseEnd_544656 < baseStart_544656 := by decide
  rcases family_descends (prefixWord ++ tailWord_544656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544763 : List Nat := [1, 1, 1, 1, 1, 3, 5, 4, 2, 3]
def baseStart_544763 : Nat := 118140960795 + 544763 * 2 ^ 59
def prefixEnd_544763 : Nat := 4983230072969 + 3 ^ 40 * 544763 * 2
def baseEnd_544763 : Nat := 186483507856904897304791

theorem tailTrace_544763 : CollatzResearch.WordTrace tailWord_544763 prefixEnd_544763 186483507856904897304791 := by
  unfold tailWord_544763
  simp only [CollatzResearch.WordTrace]
  refine ⟨19869138925424163958366943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13246092616949442638911295 19869138925424163958366943)
  ·
    refine ⟨29803708388136245937550415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19869138925424163958366943 29803708388136245937550415)
    ·
      refine ⟨44705562582204368906325623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29803708388136245937550415 44705562582204368906325623)
      ·
        refine ⟨67058343873306553359488435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44705562582204368906325623 67058343873306553359488435)
        ·
          refine ⟨100587515809959830039232653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67058343873306553359488435 100587515809959830039232653)
          ·
            refine ⟨37720318428734936264712245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 100587515809959830039232653 37720318428734936264712245)
            ·
              refine ⟨3536279852693900274816773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37720318428734936264712245 3536279852693900274816773)
              ·
                refine ⟨663052472380106301528145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3536279852693900274816773 663052472380106301528145)
                ·
                  refine ⟨497289354285079726146109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 663052472380106301528145 497289354285079726146109)
                  ·
                    refine ⟨186483507856904897304791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 497289354285079726146109 186483507856904897304791)
                    ·
                      rfl

theorem cell22_544763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 4, 2, 3].length) (baseStart_544763 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_544763 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_544763 prefixEnd_544763 := by exact prefixLift 544763
  have htrace : WordTrace (prefixWord ++ tailWord_544763) baseStart_544763 baseEnd_544763 := by
    simpa [prefixWord, tailWord_544763, baseEnd_544763] using wordTrace_append hprefix tailTrace_544763
  have hstable : (prefixWord ++ tailWord_544763).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544763).length < 2 ^ (prefixWord ++ tailWord_544763).sum := by decide
  have hdescent : baseEnd_544763 < baseStart_544763 := by decide
  rcases family_descends (prefixWord ++ tailWord_544763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544765 : List Nat := [1, 4, 1, 1, 1, 2, 6, 2, 4]
def baseStart_544765 : Nat := 118140960795 + 544765 * 2 ^ 59
def prefixEnd_544765 : Nat := 4983230072969 + 3 ^ 40 * 544765 * 2
def baseEnd_544765 : Nat := 62161397499259186251595

theorem tailTrace_544765 : CollatzResearch.WordTrace tailWord_544765 prefixEnd_544765 62161397499259186251595 := by
  unfold tailWord_544765
  simp only [CollatzResearch.WordTrace]
  refine ⟨19869211871416918299939749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13246141247611278866626499 19869211871416918299939749)
  ·
    refine ⟨3725477225890672181238703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19869211871416918299939749 3725477225890672181238703)
    ·
      refine ⟨5588215838836008271858055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3725477225890672181238703 5588215838836008271858055)
      ·
        refine ⟨8382323758254012407787083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5588215838836008271858055 8382323758254012407787083)
        ·
          refine ⟨12573485637381018611680625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8382323758254012407787083 12573485637381018611680625)
          ·
            refine ⟨9430114228035763958760469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12573485637381018611680625 9430114228035763958760469)
            ·
              refine ⟨442036604439176435566897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 9430114228035763958760469 442036604439176435566897)
              ·
                refine ⟨331527453329382326675173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 442036604439176435566897 331527453329382326675173)
                ·
                  refine ⟨62161397499259186251595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 331527453329382326675173 62161397499259186251595)
                  ·
                    rfl

theorem cell22_544765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 6, 2, 4].length) (baseStart_544765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_544765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_544765 prefixEnd_544765 := by exact prefixLift 544765
  have htrace : WordTrace (prefixWord ++ tailWord_544765) baseStart_544765 baseEnd_544765 := by
    simpa [prefixWord, tailWord_544765, baseEnd_544765] using wordTrace_append hprefix tailTrace_544765
  have hstable : (prefixWord ++ tailWord_544765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544765).length < 2 ^ (prefixWord ++ tailWord_544765).sum := by decide
  have hdescent : baseEnd_544765 < baseStart_544765 := by decide
  rcases family_descends (prefixWord ++ tailWord_544765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544960 : List Nat := [2, 1, 1, 2, 5, 1, 1, 1, 5, 3]
def baseStart_544960 : Nat := 118140960795 + 544960 * 2 ^ 59
def prefixEnd_544960 : Nat := 4983230072969 + 3 ^ 40 * 544960 * 2
def baseEnd_544960 : Nat := 186550944982862050129187

theorem tailTrace_544960 : CollatzResearch.WordTrace tailWord_544960 prefixEnd_544960 186550944982862050129187 := by
  unfold tailWord_544960
  simp only [CollatzResearch.WordTrace]
  refine ⟨9938162052855233301644167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13250882737140311068858889 9938162052855233301644167)
  ·
    refine ⟨14907243079282849952466251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9938162052855233301644167 14907243079282849952466251)
    ·
      refine ⟨22360864618924274928699377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14907243079282849952466251 22360864618924274928699377)
      ·
        refine ⟨16770648464193206196524533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22360864618924274928699377 16770648464193206196524533)
        ·
          refine ⟨1572248293518113080924175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16770648464193206196524533 1572248293518113080924175)
          ·
            refine ⟨2358372440277169621386263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1572248293518113080924175 2358372440277169621386263)
            ·
              refine ⟨3537558660415754432079395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2358372440277169621386263 3537558660415754432079395)
              ·
                refine ⟨5306337990623631648119093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3537558660415754432079395 5306337990623631648119093)
                ·
                  refine ⟨497469186620965467011165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5306337990623631648119093 497469186620965467011165)
                  ·
                    refine ⟨186550944982862050129187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 497469186620965467011165 186550944982862050129187)
                    ·
                      rfl

theorem cell22_544960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 1, 5, 3].length) (baseStart_544960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_544960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_544960 prefixEnd_544960 := by exact prefixLift 544960
  have htrace : WordTrace (prefixWord ++ tailWord_544960) baseStart_544960 baseEnd_544960 := by
    simpa [prefixWord, tailWord_544960, baseEnd_544960] using wordTrace_append hprefix tailTrace_544960
  have hstable : (prefixWord ++ tailWord_544960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544960).length < 2 ^ (prefixWord ++ tailWord_544960).sum := by decide
  have hdescent : baseEnd_544960 < baseStart_544960 := by decide
  rcases family_descends (prefixWord ++ tailWord_544960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544977 : List Nat := [1, 2, 2, 1, 2, 2, 3, 5, 1, 3]
def baseStart_544977 : Nat := 118140960795 + 544977 * 2 ^ 59
def prefixEnd_544977 : Nat := 4983230072969 + 3 ^ 40 * 544977 * 2
def baseEnd_544977 : Nat := 186556764430279672454135

theorem tailTrace_544977 : CollatzResearch.WordTrace tailWord_544977 prefixEnd_544977 186556764430279672454135 := by
  unfold tailWord_544977
  simp only [CollatzResearch.WordTrace]
  refine ⟨19876944146648878506657185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13251296097765919004438123 19876944146648878506657185)
  ·
    refine ⟨14907708109986658879992889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19876944146648878506657185 14907708109986658879992889)
    ·
      refine ⟨11180781082489994159994667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14907708109986658879992889 11180781082489994159994667)
      ·
        refine ⟨16771171623734991239992001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11180781082489994159994667 16771171623734991239992001)
        ·
          refine ⟨12578378717801243429994001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16771171623734991239992001 12578378717801243429994001)
          ·
            refine ⟨9433784038350932572495501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12578378717801243429994001 9433784038350932572495501)
            ·
              refine ⟨3537669014381599714685813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9433784038350932572495501 3537669014381599714685813)
              ·
                refine ⟨331656470098274973251795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3537669014381599714685813 331656470098274973251795)
                ·
                  refine ⟨497484705147412459877693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 331656470098274973251795 497484705147412459877693)
                  ·
                    refine ⟨186556764430279672454135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 497484705147412459877693 186556764430279672454135)
                    ·
                      rfl

theorem cell22_544977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 5, 1, 3].length) (baseStart_544977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_544977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_544977 prefixEnd_544977 := by exact prefixLift 544977
  have htrace : WordTrace (prefixWord ++ tailWord_544977) baseStart_544977 baseEnd_544977 := by
    simpa [prefixWord, tailWord_544977, baseEnd_544977] using wordTrace_append hprefix tailTrace_544977
  have hstable : (prefixWord ++ tailWord_544977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544977).length < 2 ^ (prefixWord ++ tailWord_544977).sum := by decide
  have hdescent : baseEnd_544977 < baseStart_544977 := by decide
  rcases family_descends (prefixWord ++ tailWord_544977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545007 : List Nat := [1, 1, 2, 1, 6, 2, 3, 1, 5]
def baseStart_545007 : Nat := 118140960795 + 545007 * 2 ^ 59
def prefixEnd_545007 : Nat := 4983230072969 + 3 ^ 40 * 545007 * 2
def baseEnd_545007 : Nat := 62189011347789864734681

theorem tailTrace_545007 : CollatzResearch.WordTrace tailWord_545007 prefixEnd_545007 62189011347789864734681 := by
  unfold tailWord_545007
  simp only [CollatzResearch.WordTrace]
  refine ⟨19878038336540193630249275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13252025557693462420166183 19878038336540193630249275)
  ·
    refine ⟨29817057504810290445373913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19878038336540193630249275 29817057504810290445373913)
    ·
      refine ⟨22362793128607717834030435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29817057504810290445373913 22362793128607717834030435)
      ·
        refine ⟨33544189692911576751045653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22362793128607717834030435 33544189692911576751045653)
        ·
          refine ⟨1572383891855230160205265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 33544189692911576751045653 1572383891855230160205265)
          ·
            refine ⟨1179287918891422620153949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1572383891855230160205265 1179287918891422620153949)
            ·
              refine ⟨442232969584283482557731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1179287918891422620153949 442232969584283482557731)
              ·
                refine ⟨663349454376425223836597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 442232969584283482557731 663349454376425223836597)
                ·
                  refine ⟨62189011347789864734681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 663349454376425223836597 62189011347789864734681)
                  ·
                    rfl

theorem cell22_545007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 3, 1, 5].length) (baseStart_545007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_545007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_545007 prefixEnd_545007 := by exact prefixLift 545007
  have htrace : WordTrace (prefixWord ++ tailWord_545007) baseStart_545007 baseEnd_545007 := by
    simpa [prefixWord, tailWord_545007, baseEnd_545007] using wordTrace_append hprefix tailTrace_545007
  have hstable : (prefixWord ++ tailWord_545007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545007).length < 2 ^ (prefixWord ++ tailWord_545007).sum := by decide
  have hdescent : baseEnd_545007 < baseStart_545007 := by decide
  rcases family_descends (prefixWord ++ tailWord_545007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545028 : List Nat := [2, 3, 2, 2, 4, 1, 1, 3, 1, 3]
def baseStart_545028 : Nat := 118140960795 + 545028 * 2 ^ 59
def prefixEnd_545028 : Nat := 4983230072969 + 3 ^ 40 * 545028 * 2
def baseEnd_545028 : Nat := 186574222772532539428979

theorem tailTrace_545028 : CollatzResearch.WordTrace tailWord_545028 prefixEnd_545028 186574222772532539428979 := by
  unfold tailWord_545028
  simp only [CollatzResearch.WordTrace]
  refine ⟨9939402134732057108381869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13252536179642742811175825 9939402134732057108381869)
  ·
    refine ⟨3727275800524521415643201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9939402134732057108381869 3727275800524521415643201)
    ·
      refine ⟨2795456850393391061732401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3727275800524521415643201 2795456850393391061732401)
      ·
        refine ⟨2096592637795043296299301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2795456850393391061732401 2096592637795043296299301)
        ·
          refine ⟨393111119586570618056119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2096592637795043296299301 393111119586570618056119)
          ·
            refine ⟨589666679379855927084179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 393111119586570618056119 589666679379855927084179)
            ·
              refine ⟨884500019069783890626269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 589666679379855927084179 884500019069783890626269)
              ·
                refine ⟨331687507151168958984851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 884500019069783890626269 331687507151168958984851)
                ·
                  refine ⟨497531260726753438477277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 331687507151168958984851 497531260726753438477277)
                  ·
                    refine ⟨186574222772532539428979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 497531260726753438477277 186574222772532539428979)
                    ·
                      rfl

theorem cell22_545028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 1, 3, 1, 3].length) (baseStart_545028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_545028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_545028 prefixEnd_545028 := by exact prefixLift 545028
  have htrace : WordTrace (prefixWord ++ tailWord_545028) baseStart_545028 baseEnd_545028 := by
    simpa [prefixWord, tailWord_545028, baseEnd_545028] using wordTrace_append hprefix tailTrace_545028
  have hstable : (prefixWord ++ tailWord_545028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545028).length < 2 ^ (prefixWord ++ tailWord_545028).sum := by decide
  have hdescent : baseEnd_545028 < baseStart_545028 := by decide
  rcases family_descends (prefixWord ++ tailWord_545028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545082 : List Nat := [3, 1, 1, 1, 4, 3, 2, 1, 2, 4]
def baseStart_545082 : Nat := 118140960795 + 545082 * 2 ^ 59
def prefixEnd_545082 : Nat := 4983230072969 + 3 ^ 40 * 545082 * 2
def baseEnd_545082 : Nat := 186592708076094398578813

theorem tailTrace_545082 : CollatzResearch.WordTrace tailWord_545082 prefixEnd_545082 186592708076094398578813 := by
  unfold tailWord_545082
  simp only [CollatzResearch.WordTrace]
  refine ⟨4970193452817120359807375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13253849207512320959486333 4970193452817120359807375)
  ·
    refine ⟨7455290179225680539711063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4970193452817120359807375 7455290179225680539711063)
    ·
      refine ⟨11182935268838520809566595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7455290179225680539711063 11182935268838520809566595)
      ·
        refine ⟨16774402903257781214349893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11182935268838520809566595 16774402903257781214349893)
        ·
          refine ⟨3145200544360833977690605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16774402903257781214349893 3145200544360833977690605)
          ·
            refine ⟨1179450204135312741633977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3145200544360833977690605 1179450204135312741633977)
            ·
              refine ⟨884587653101484556225483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1179450204135312741633977 884587653101484556225483)
              ·
                refine ⟨1326881479652226834338225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 884587653101484556225483 1326881479652226834338225)
                ·
                  refine ⟨995161109739170125753669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1326881479652226834338225 995161109739170125753669)
                  ·
                    refine ⟨186592708076094398578813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 995161109739170125753669 186592708076094398578813)
                    ·
                      rfl

theorem cell22_545082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 2, 1, 2, 4].length) (baseStart_545082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_545082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_545082 prefixEnd_545082 := by exact prefixLift 545082
  have htrace : WordTrace (prefixWord ++ tailWord_545082) baseStart_545082 baseEnd_545082 := by
    simpa [prefixWord, tailWord_545082, baseEnd_545082] using wordTrace_append hprefix tailTrace_545082
  have hstable : (prefixWord ++ tailWord_545082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545082).length < 2 ^ (prefixWord ++ tailWord_545082).sum := by decide
  have hdescent : baseEnd_545082 < baseStart_545082 := by decide
  rcases family_descends (prefixWord ++ tailWord_545082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545202 : List Nat := [3, 2, 1, 1, 1, 1, 3, 1, 6, 3]
def baseStart_545202 : Nat := 118140960795 + 545202 * 2 ^ 59
def prefixEnd_545202 : Nat := 4983230072969 + 3 ^ 40 * 545202 * 2
def baseEnd_545202 : Nat := 186633786528454085578445

theorem tailTrace_545202 : CollatzResearch.WordTrace tailWord_545202 prefixEnd_545202 186633786528454085578445 := by
  unfold tailWord_545202
  simp only [CollatzResearch.WordTrace]
  refine ⟨4971287642708435483399465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13256767047222494622398573 4971287642708435483399465)
  ·
    refine ⟨3728465732031326612549599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4971287642708435483399465 3728465732031326612549599)
    ·
      refine ⟨5592698598046989918824399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3728465732031326612549599 5592698598046989918824399)
      ·
        refine ⟨8389047897070484878236599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5592698598046989918824399 8389047897070484878236599)
        ·
          refine ⟨12583571845605727317354899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8389047897070484878236599 12583571845605727317354899)
          ·
            refine ⟨18875357768408590976032349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12583571845605727317354899 18875357768408590976032349)
            ·
              refine ⟨7078259163153221616012131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18875357768408590976032349 7078259163153221616012131)
              ·
                refine ⟨10617388744729832424018197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7078259163153221616012131 10617388744729832424018197)
                ·
                  refine ⟨497690097409210894875853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10617388744729832424018197 497690097409210894875853)
                  ·
                    refine ⟨186633786528454085578445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 497690097409210894875853 186633786528454085578445)
                    ·
                      rfl

theorem cell22_545202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 1, 6, 3].length) (baseStart_545202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_545202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_545202 prefixEnd_545202 := by exact prefixLift 545202
  have htrace : WordTrace (prefixWord ++ tailWord_545202) baseStart_545202 baseEnd_545202 := by
    simpa [prefixWord, tailWord_545202, baseEnd_545202] using wordTrace_append hprefix tailTrace_545202
  have hstable : (prefixWord ++ tailWord_545202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545202).length < 2 ^ (prefixWord ++ tailWord_545202).sum := by decide
  have hdescent : baseEnd_545202 < baseStart_545202 := by decide
  rcases family_descends (prefixWord ++ tailWord_545202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545236 : List Nat := [2, 4, 1, 2, 2, 2, 1, 3, 2, 3]
def baseStart_545236 : Nat := 118140960795 + 545236 * 2 ^ 59
def prefixEnd_545236 : Nat := 4983230072969 + 3 ^ 40 * 545236 * 2
def baseEnd_545236 : Nat := 186645425423289330228341

theorem tailTrace_545236 : CollatzResearch.WordTrace tailWord_545236 prefixEnd_545236 186645425423289330228341 := by
  unfold tailWord_545236
  simp only [CollatzResearch.WordTrace]
  refine ⟨9943195326355282870167781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13257593768473710493557041 9943195326355282870167781)
  ·
    refine ⟨1864349123691615538156459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9943195326355282870167781 1864349123691615538156459)
    ·
      refine ⟨2796523685537423307234689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1864349123691615538156459 2796523685537423307234689)
      ·
        refine ⟨2097392764153067480426017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2796523685537423307234689 2097392764153067480426017)
        ·
          refine ⟨1573044573114800610319513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2097392764153067480426017 1573044573114800610319513)
          ·
            refine ⟨1179783429836100457739635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1573044573114800610319513 1179783429836100457739635)
            ·
              refine ⟨1769675144754150686609453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1179783429836100457739635 1769675144754150686609453)
              ·
                refine ⟨663628179282806507478545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1769675144754150686609453 663628179282806507478545)
                ·
                  refine ⟨497721134462104880608909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 663628179282806507478545 497721134462104880608909)
                  ·
                    refine ⟨186645425423289330228341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 497721134462104880608909 186645425423289330228341)
                    ·
                      rfl

theorem cell22_545236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 3, 2, 3].length) (baseStart_545236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_545236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_545236 prefixEnd_545236 := by exact prefixLift 545236
  have htrace : WordTrace (prefixWord ++ tailWord_545236) baseStart_545236 baseEnd_545236 := by
    simpa [prefixWord, tailWord_545236, baseEnd_545236] using wordTrace_append hprefix tailTrace_545236
  have hstable : (prefixWord ++ tailWord_545236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545236).length < 2 ^ (prefixWord ++ tailWord_545236).sum := by decide
  have hdescent : baseEnd_545236 < baseStart_545236 := by decide
  rcases family_descends (prefixWord ++ tailWord_545236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545292 : List Nat := [2, 2, 1, 2, 4, 1, 1, 1, 1, 7]
def baseStart_545292 : Nat := 118140960795 + 545292 * 2 ^ 59
def prefixEnd_545292 : Nat := 4983230072969 + 3 ^ 40 * 545292 * 2
def baseEnd_545292 : Nat := 186664595367723850828169

theorem tailTrace_545292 : CollatzResearch.WordTrace tailWord_545292 prefixEnd_545292 186664595367723850828169 := by
  unfold tailWord_545292
  simp only [CollatzResearch.WordTrace]
  refine ⟨9944216570253843652187065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13258955427005124869582753 9944216570253843652187065)
  ·
    refine ⟨7458162427690382739140299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9944216570253843652187065 7458162427690382739140299)
    ·
      refine ⟨11187243641535574108710449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7458162427690382739140299 11187243641535574108710449)
      ·
        refine ⟨8390432731151680581532837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11187243641535574108710449 8390432731151680581532837)
        ·
          refine ⟨1573206137090940109037407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8390432731151680581532837 1573206137090940109037407)
          ·
            refine ⟨2359809205636410163556111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1573206137090940109037407 2359809205636410163556111)
            ·
              refine ⟨3539713808454615245334167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2359809205636410163556111 3539713808454615245334167)
              ·
                refine ⟨5309570712681922868001251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3539713808454615245334167 5309570712681922868001251)
                ·
                  refine ⟨7964356069022884302001877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5309570712681922868001251 7964356069022884302001877)
                  ·
                    refine ⟨186664595367723850828169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7964356069022884302001877 186664595367723850828169)
                    ·
                      rfl

theorem cell22_545292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 1, 1, 7].length) (baseStart_545292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_545292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_545292 prefixEnd_545292 := by exact prefixLift 545292
  have htrace : WordTrace (prefixWord ++ tailWord_545292) baseStart_545292 baseEnd_545292 := by
    simpa [prefixWord, tailWord_545292, baseEnd_545292] using wordTrace_append hprefix tailTrace_545292
  have hstable : (prefixWord ++ tailWord_545292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545292).length < 2 ^ (prefixWord ++ tailWord_545292).sum := by decide
  have hdescent : baseEnd_545292 < baseStart_545292 := by decide
  rcases family_descends (prefixWord ++ tailWord_545292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545294 : List Nat := [4, 1, 1, 2, 3, 1, 2, 3, 5]
def baseStart_545294 : Nat := 118140960795 + 545294 * 2 ^ 59
def prefixEnd_545294 : Nat := 4983230072969 + 3 ^ 40 * 545294 * 2
def baseEnd_545294 : Nat := 62221760002865504092721

theorem tailTrace_545294 : CollatzResearch.WordTrace tailWord_545294 prefixEnd_545294 62221760002865504092721 := by
  unfold tailWord_545294
  simp only [CollatzResearch.WordTrace]
  refine ⟨2486063260812555205743367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13259004057666961097297957 2486063260812555205743367)
  ·
    refine ⟨3729094891218832808615051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2486063260812555205743367 3729094891218832808615051)
    ·
      refine ⟨5593642336828249212922577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3729094891218832808615051 5593642336828249212922577)
      ·
        refine ⟨4195231752621186909691933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5593642336828249212922577 4195231752621186909691933)
        ·
          refine ⟨1573211907232945091134475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4195231752621186909691933 1573211907232945091134475)
          ·
            refine ⟨2359817860849417636701713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1573211907232945091134475 2359817860849417636701713)
            ·
              refine ⟨1769863395637063227526285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2359817860849417636701713 1769863395637063227526285)
              ·
                refine ⟨663698773363898710322357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1769863395637063227526285 663698773363898710322357)
                ·
                  refine ⟨62221760002865504092721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 663698773363898710322357 62221760002865504092721)
                  ·
                    rfl

theorem cell22_545294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 3, 5].length) (baseStart_545294 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_545294 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_545294 prefixEnd_545294 := by exact prefixLift 545294
  have htrace : WordTrace (prefixWord ++ tailWord_545294) baseStart_545294 baseEnd_545294 := by
    simpa [prefixWord, tailWord_545294, baseEnd_545294] using wordTrace_append hprefix tailTrace_545294
  have hstable : (prefixWord ++ tailWord_545294).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545294).length < 2 ^ (prefixWord ++ tailWord_545294).sum := by decide
  have hdescent : baseEnd_545294 < baseStart_545294 := by decide
  rcases family_descends (prefixWord ++ tailWord_545294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545354 : List Nat := [3, 1, 2, 1, 1, 4, 3, 1, 1, 5]
def baseStart_545354 : Nat := 118140960795 + 545354 * 2 ^ 59
def prefixEnd_545354 : Nat := 4983230072969 + 3 ^ 40 * 545354 * 2
def baseEnd_545354 : Nat := 186685819234776355777979

theorem tailTrace_545354 : CollatzResearch.WordTrace tailWord_545354 prefixEnd_545354 186685819234776355777979 := by
  unfold tailWord_545354
  simp only [CollatzResearch.WordTrace]
  refine ⟨4972673616570767973282779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13260462977522047928754077 4972673616570767973282779)
  ·
    refine ⟨7459010424856151959924169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4972673616570767973282779 7459010424856151959924169)
    ·
      refine ⟨5594257818642113969943127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7459010424856151959924169 5594257818642113969943127)
      ·
        refine ⟨8391386727963170954914691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5594257818642113969943127 8391386727963170954914691)
        ·
          refine ⟨12587080091944756432372037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8391386727963170954914691 12587080091944756432372037)
          ·
            refine ⟨2360077517239641831069757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12587080091944756432372037 2360077517239641831069757)
            ·
              refine ⟨885029068964865686651159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2360077517239641831069757 885029068964865686651159)
              ·
                refine ⟨1327543603447298529976739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 885029068964865686651159 1327543603447298529976739)
                ·
                  refine ⟨1991315405170947794965109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1327543603447298529976739 1991315405170947794965109)
                  ·
                    refine ⟨186685819234776355777979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1991315405170947794965109 186685819234776355777979)
                    ·
                      rfl

theorem cell22_545354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 3, 1, 1, 5].length) (baseStart_545354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_545354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_545354 prefixEnd_545354 := by exact prefixLift 545354
  have htrace : WordTrace (prefixWord ++ tailWord_545354) baseStart_545354 baseEnd_545354 := by
    simpa [prefixWord, tailWord_545354, baseEnd_545354] using wordTrace_append hprefix tailTrace_545354
  have hstable : (prefixWord ++ tailWord_545354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545354).length < 2 ^ (prefixWord ++ tailWord_545354).sum := by decide
  have hdescent : baseEnd_545354 < baseStart_545354 := by decide
  rcases family_descends (prefixWord ++ tailWord_545354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545367 : List Nat := [1, 1, 3, 2, 2, 2, 3, 8]
def baseStart_545367 : Nat := 118140960795 + 545367 * 2 ^ 59
def prefixEnd_545367 : Nat := 4983230072969 + 3 ^ 40 * 545367 * 2
def baseEnd_545367 : Nat := 20743363266716517244771

theorem tailTrace_545367 : CollatzResearch.WordTrace tailWord_545367 prefixEnd_545367 20743363266716517244771 := by
  unfold tailWord_545367
  simp only [CollatzResearch.WordTrace]
  refine ⟨19891168615235975113354355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13260779076823983408902903 19891168615235975113354355)
  ·
    refine ⟨29836752922853962670031533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19891168615235975113354355 29836752922853962670031533)
    ·
      refine ⟨11188782346070236001261825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29836752922853962670031533 11188782346070236001261825)
      ·
        refine ⟨8391586759552677000946369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11188782346070236001261825 8391586759552677000946369)
        ·
          refine ⟨6293690069664507750709777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8391586759552677000946369 6293690069664507750709777)
          ·
            refine ⟨4720267552248380813032333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6293690069664507750709777 4720267552248380813032333)
            ·
              refine ⟨1770100332093142804887125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4720267552248380813032333 1770100332093142804887125)
              ·
                refine ⟨20743363266716517244771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1770100332093142804887125 20743363266716517244771)
                ·
                  rfl

theorem cell22_545367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 8].length) (baseStart_545367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_545367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_545367 prefixEnd_545367 := by exact prefixLift 545367
  have htrace : WordTrace (prefixWord ++ tailWord_545367) baseStart_545367 baseEnd_545367 := by
    simpa [prefixWord, tailWord_545367, baseEnd_545367] using wordTrace_append hprefix tailTrace_545367
  have hstable : (prefixWord ++ tailWord_545367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545367).length < 2 ^ (prefixWord ++ tailWord_545367).sum := by decide
  have hdescent : baseEnd_545367 < baseStart_545367 := by decide
  rcases family_descends (prefixWord ++ tailWord_545367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545405 : List Nat := [1, 4, 1, 1, 5, 2, 2, 1, 2, 3]
def baseStart_545405 : Nat := 118140960795 + 545405 * 2 ^ 59
def prefixEnd_545405 : Nat := 4983230072969 + 3 ^ 40 * 545405 * 2
def baseEnd_545405 : Nat := 186703277577029222752823

theorem tailTrace_545405 : CollatzResearch.WordTrace tailWord_545405 prefixEnd_545405 186703277577029222752823 := by
  unfold tailWord_545405
  simp only [CollatzResearch.WordTrace]
  refine ⟨19892554589098307603237669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13261703059398871735491779 19892554589098307603237669)
  ·
    refine ⟨3729853985455932675607063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19892554589098307603237669 3729853985455932675607063)
    ·
      refine ⟨5594780978183899013410595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3729853985455932675607063 5594780978183899013410595)
      ·
        refine ⟨8392171467275848520115893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5594780978183899013410595 8392171467275848520115893)
        ·
          refine ⟨786766075057110798760865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8392171467275848520115893 786766075057110798760865)
          ·
            refine ⟨590074556292833099070649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 786766075057110798760865 590074556292833099070649)
            ·
              refine ⟨442555917219624824302987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 590074556292833099070649 442555917219624824302987)
              ·
                refine ⟨663833875829437236454481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 442555917219624824302987 663833875829437236454481)
                ·
                  refine ⟨497875406872077927340861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 663833875829437236454481 497875406872077927340861)
                  ·
                    refine ⟨186703277577029222752823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 497875406872077927340861 186703277577029222752823)
                    ·
                      rfl

theorem cell22_545405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 2, 1, 2, 3].length) (baseStart_545405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_545405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_545405 prefixEnd_545405 := by exact prefixLift 545405
  have htrace : WordTrace (prefixWord ++ tailWord_545405) baseStart_545405 baseEnd_545405 := by
    simpa [prefixWord, tailWord_545405, baseEnd_545405] using wordTrace_append hprefix tailTrace_545405
  have hstable : (prefixWord ++ tailWord_545405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545405).length < 2 ^ (prefixWord ++ tailWord_545405).sum := by decide
  have hdescent : baseEnd_545405 < baseStart_545405 := by decide
  rcases family_descends (prefixWord ++ tailWord_545405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545427 : List Nat := [1, 1, 1, 2, 1, 2, 2, 4, 1, 7]
def baseStart_545427 : Nat := 118140960795 + 545427 * 2 ^ 59
def prefixEnd_545427 : Nat := 4983230072969 + 3 ^ 40 * 545427 * 2
def baseEnd_545427 : Nat := 186710808626628498702755

theorem tailTrace_545427 : CollatzResearch.WordTrace tailWord_545427 prefixEnd_545427 186710808626628498702755 := by
  unfold tailWord_545427
  simp only [CollatzResearch.WordTrace]
  refine ⟨19893356995018605360538535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13262237996679070240359023 19893356995018605360538535)
  ·
    refine ⟨29840035492527908040807803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19893356995018605360538535 29840035492527908040807803)
    ·
      refine ⟨44760053238791862061211705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29840035492527908040807803 44760053238791862061211705)
      ·
        refine ⟨33570039929093896545908779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44760053238791862061211705 33570039929093896545908779)
        ·
          refine ⟨50355059893640844818863169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33570039929093896545908779 50355059893640844818863169)
          ·
            refine ⟨37766294920230633614147377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50355059893640844818863169 37766294920230633614147377)
            ·
              refine ⟨28324721190172975210610533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37766294920230633614147377 28324721190172975210610533)
              ·
                refine ⟨5310885223157432851989475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28324721190172975210610533 5310885223157432851989475)
                ·
                  refine ⟨7966327834736149277984213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5310885223157432851989475 7966327834736149277984213)
                  ·
                    refine ⟨186710808626628498702755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7966327834736149277984213 186710808626628498702755)
                    ·
                      rfl

theorem cell22_545427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 4, 1, 7].length) (baseStart_545427 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_545427 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_545427 prefixEnd_545427 := by exact prefixLift 545427
  have htrace : WordTrace (prefixWord ++ tailWord_545427) baseStart_545427 baseEnd_545427 := by
    simpa [prefixWord, tailWord_545427, baseEnd_545427] using wordTrace_append hprefix tailTrace_545427
  have hstable : (prefixWord ++ tailWord_545427).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545427).length < 2 ^ (prefixWord ++ tailWord_545427).sum := by decide
  have hdescent : baseEnd_545427 < baseStart_545427 := by decide
  rcases family_descends (prefixWord ++ tailWord_545427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545444 : List Nat := [2, 3, 1, 2, 2, 1, 2, 2, 2, 5]
def baseStart_545444 : Nat := 118140960795 + 545444 * 2 ^ 59
def prefixEnd_545444 : Nat := 4983230072969 + 3 ^ 40 * 545444 * 2
def baseEnd_545444 : Nat := 186716628074046121027703

theorem tailTrace_545444 : CollatzResearch.WordTrace tailWord_545444 prefixEnd_545444 186716628074046121027703 := by
  unfold tailWord_545444
  simp only [CollatzResearch.WordTrace]
  refine ⟨9946988517978508631953693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13262651357304678175938257 9946988517978508631953693)
  ·
    refine ⟨3730120694241940736982635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9946988517978508631953693 3730120694241940736982635)
    ·
      refine ⟨5595181041362911105473953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3730120694241940736982635 5595181041362911105473953)
      ·
        refine ⟨4196385781022183329105465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5595181041362911105473953 4196385781022183329105465)
        ·
          refine ⟨3147289335766637496829099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4196385781022183329105465 3147289335766637496829099)
          ·
            refine ⟨4720934003649956245243649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3147289335766637496829099 4720934003649956245243649)
            ·
              refine ⟨3540700502737467183932737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4720934003649956245243649 3540700502737467183932737)
              ·
                refine ⟨2655525377053100387949553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3540700502737467183932737 2655525377053100387949553)
                ·
                  refine ⟨1991644032789825290962165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2655525377053100387949553 1991644032789825290962165)
                  ·
                    refine ⟨186716628074046121027703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1991644032789825290962165 186716628074046121027703)
                    ·
                      rfl

theorem cell22_545444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 2, 2, 5].length) (baseStart_545444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_545444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_545444 prefixEnd_545444 := by exact prefixLift 545444
  have htrace : WordTrace (prefixWord ++ tailWord_545444) baseStart_545444 baseEnd_545444 := by
    simpa [prefixWord, tailWord_545444, baseEnd_545444] using wordTrace_append hprefix tailTrace_545444
  have hstable : (prefixWord ++ tailWord_545444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545444).length < 2 ^ (prefixWord ++ tailWord_545444).sum := by decide
  have hdescent : baseEnd_545444 < baseStart_545444 := by decide
  rcases family_descends (prefixWord ++ tailWord_545444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545459 : List Nat := [1, 1, 1, 2, 3, 4, 1, 2, 3, 4]
def baseStart_545459 : Nat := 118140960795 + 545459 * 2 ^ 59
def prefixEnd_545459 : Nat := 4983230072969 + 3 ^ 40 * 545459 * 2
def baseEnd_545459 : Nat := 186721762880591081902657

theorem tailTrace_545459 : CollatzResearch.WordTrace tailWord_545459 prefixEnd_545459 186721762880591081902657 := by
  unfold tailWord_545459
  simp only [CollatzResearch.WordTrace]
  refine ⟨19894524130902674825703431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13263016087268449883802287 19894524130902674825703431)
  ·
    refine ⟨29841786196354012238555147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19894524130902674825703431 29841786196354012238555147)
    ·
      refine ⟨44762679294531018357832721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29841786196354012238555147 44762679294531018357832721)
      ·
        refine ⟨33572009470898263768374541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44762679294531018357832721 33572009470898263768374541)
        ·
          refine ⟨12589503551586848913140453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33572009470898263768374541 12589503551586848913140453)
          ·
            refine ⟨2360531915922534171213835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12589503551586848913140453 2360531915922534171213835)
            ·
              refine ⟨3540797873883801256820753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2360531915922534171213835 3540797873883801256820753)
              ·
                refine ⟨2655598405412850942615565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3540797873883801256820753 2655598405412850942615565)
                ·
                  refine ⟨995849402029819103480837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2655598405412850942615565 995849402029819103480837)
                  ·
                    refine ⟨186721762880591081902657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 995849402029819103480837 186721762880591081902657)
                    ·
                      rfl

theorem cell22_545459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 2, 3, 4].length) (baseStart_545459 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_545459 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_545459 prefixEnd_545459 := by exact prefixLift 545459
  have htrace : WordTrace (prefixWord ++ tailWord_545459) baseStart_545459 baseEnd_545459 := by
    simpa [prefixWord, tailWord_545459, baseEnd_545459] using wordTrace_append hprefix tailTrace_545459
  have hstable : (prefixWord ++ tailWord_545459).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545459).length < 2 ^ (prefixWord ++ tailWord_545459).sum := by decide
  have hdescent : baseEnd_545459 < baseStart_545459 := by decide
  rcases family_descends (prefixWord ++ tailWord_545459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545461 : List Nat := [1, 3, 3, 3, 1, 2, 1, 1, 2, 5]
def baseStart_545461 : Nat := 118140960795 + 545461 * 2 ^ 59
def prefixEnd_545461 : Nat := 4983230072969 + 3 ^ 40 * 545461 * 2
def baseEnd_545461 : Nat := 186722447521463743352651

theorem tailTrace_545461 : CollatzResearch.WordTrace tailWord_545461 prefixEnd_545461 186722447521463743352651 := by
  unfold tailWord_545461
  simp only [CollatzResearch.WordTrace]
  refine ⟨19894597076895429167276237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13263064717930286111517491 19894597076895429167276237)
  ·
    refine ⟨7460473903835785937728589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19894597076895429167276237 7460473903835785937728589)
    ·
      refine ⟨2797677713938419726648221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7460473903835785937728589 2797677713938419726648221)
      ·
        refine ⟨1049129142726907397493083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2797677713938419726648221 1049129142726907397493083)
        ·
          refine ⟨1573693714090361096239625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1049129142726907397493083 1573693714090361096239625)
          ·
            refine ⟨1180270285567770822179719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1573693714090361096239625 1180270285567770822179719)
            ·
              refine ⟨1770405428351656233269579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1180270285567770822179719 1770405428351656233269579)
              ·
                refine ⟨2655608142527484349904369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1770405428351656233269579 2655608142527484349904369)
                ·
                  refine ⟨1991706106895613262428277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2655608142527484349904369 1991706106895613262428277)
                  ·
                    refine ⟨186722447521463743352651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1991706106895613262428277 186722447521463743352651)
                    ·
                      rfl

theorem cell22_545461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 1, 2, 5].length) (baseStart_545461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_545461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_545461 prefixEnd_545461 := by exact prefixLift 545461
  have htrace : WordTrace (prefixWord ++ tailWord_545461) baseStart_545461 baseEnd_545461 := by
    simpa [prefixWord, tailWord_545461, baseEnd_545461] using wordTrace_append hprefix tailTrace_545461
  have hstable : (prefixWord ++ tailWord_545461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545461).length < 2 ^ (prefixWord ++ tailWord_545461).sum := by decide
  have hdescent : baseEnd_545461 < baseStart_545461 := by decide
  rcases family_descends (prefixWord ++ tailWord_545461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545476 : List Nat := [2, 3, 3, 1, 1, 2, 2, 1, 3, 4]
def baseStart_545476 : Nat := 118140960795 + 545476 * 2 ^ 59
def prefixEnd_545476 : Nat := 4983230072969 + 3 ^ 40 * 545476 * 2
def baseEnd_545476 : Nat := 186727582328008704227605

theorem tailTrace_545476 : CollatzResearch.WordTrace tailWord_545476 prefixEnd_545476 186727582328008704227605 := by
  unfold tailWord_545476
  simp only [CollatzResearch.WordTrace]
  refine ⟨9947572085920543364536141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13263429447894057819381521 9947572085920543364536141)
  ·
    refine ⟨3730339532220203761701053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9947572085920543364536141 3730339532220203761701053)
    ·
      refine ⟨1398877324582576410637895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3730339532220203761701053 1398877324582576410637895)
      ·
        refine ⟨2098315986873864615956843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1398877324582576410637895 2098315986873864615956843)
        ·
          refine ⟨3147473980310796923935265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2098315986873864615956843 3147473980310796923935265)
          ·
            refine ⟨2360605485233097692951449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3147473980310796923935265 2360605485233097692951449)
            ·
              refine ⟨1770454113924823269713587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2360605485233097692951449 1770454113924823269713587)
              ·
                refine ⟨2655681170887234904570381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1770454113924823269713587 2655681170887234904570381)
                ·
                  refine ⟨995880439082713089213893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2655681170887234904570381 995880439082713089213893)
                  ·
                    refine ⟨186727582328008704227605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 995880439082713089213893 186727582328008704227605)
                    ·
                      rfl

theorem cell22_545476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_545476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_545476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_545476 prefixEnd_545476 := by exact prefixLift 545476
  have htrace : WordTrace (prefixWord ++ tailWord_545476) baseStart_545476 baseEnd_545476 := by
    simpa [prefixWord, tailWord_545476, baseEnd_545476] using wordTrace_append hprefix tailTrace_545476
  have hstable : (prefixWord ++ tailWord_545476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545476).length < 2 ^ (prefixWord ++ tailWord_545476).sum := by decide
  have hdescent : baseEnd_545476 < baseStart_545476 := by decide
  rcases family_descends (prefixWord ++ tailWord_545476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545489 : List Nat := [1, 2, 2, 1, 2, 3, 1, 4, 1, 5]
def baseStart_545489 : Nat := 118140960795 + 545489 * 2 ^ 59
def prefixEnd_545489 : Nat := 4983230072969 + 3 ^ 40 * 545489 * 2
def baseEnd_545489 : Nat := 186732032493681003652565

theorem tailTrace_545489 : CollatzResearch.WordTrace tailWord_545489 prefixEnd_545489 186732032493681003652565 := by
  unfold tailWord_545489
  simp only [CollatzResearch.WordTrace]
  refine ⟨19895618320793989949295521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13263745547195993299530347 19895618320793989949295521)
  ·
    refine ⟨14921713740595492461971641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19895618320793989949295521 14921713740595492461971641)
    ·
      refine ⟨11191285305446619346478731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14921713740595492461971641 11191285305446619346478731)
      ·
        refine ⟨16786927958169929019718097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11191285305446619346478731 16786927958169929019718097)
        ·
          refine ⟨12590195968627446764788573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16786927958169929019718097 12590195968627446764788573)
          ·
            refine ⟨4721323488235292536795715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12590195968627446764788573 4721323488235292536795715)
            ·
              refine ⟨7081985232352938805193573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4721323488235292536795715 7081985232352938805193573)
              ·
                refine ⟨1327872231066176025973795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7081985232352938805193573 1327872231066176025973795)
                ·
                  refine ⟨1991808346599264038960693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1327872231066176025973795 1991808346599264038960693)
                  ·
                    refine ⟨186732032493681003652565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1991808346599264038960693 186732032493681003652565)
                    ·
                      rfl

theorem cell22_545489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 4, 1, 5].length) (baseStart_545489 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_545489 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_545489 prefixEnd_545489 := by exact prefixLift 545489
  have htrace : WordTrace (prefixWord ++ tailWord_545489) baseStart_545489 baseEnd_545489 := by
    simpa [prefixWord, tailWord_545489, baseEnd_545489] using wordTrace_append hprefix tailTrace_545489
  have hstable : (prefixWord ++ tailWord_545489).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545489).length < 2 ^ (prefixWord ++ tailWord_545489).sum := by decide
  have hdescent : baseEnd_545489 < baseStart_545489 := by decide
  rcases family_descends (prefixWord ++ tailWord_545489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545504 : List Nat := [2, 1, 1, 3, 1, 2, 1, 3, 4, 4]
def baseStart_545504 : Nat := 118140960795 + 545504 * 2 ^ 59
def prefixEnd_545504 : Nat := 4983230072969 + 3 ^ 40 * 545504 * 2
def baseEnd_545504 : Nat := 186737167300225964527519

theorem tailTrace_545504 : CollatzResearch.WordTrace tailWord_545504 prefixEnd_545504 186737167300225964527519 := by
  unfold tailWord_545504
  simp only [CollatzResearch.WordTrace]
  refine ⟨9948082707869823755545783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13264110277159765007394377 9948082707869823755545783)
  ·
    refine ⟨14922124061804735633318675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9948082707869823755545783 14922124061804735633318675)
    ·
      refine ⟨22383186092707103449978013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14922124061804735633318675 22383186092707103449978013)
      ·
        refine ⟨8393694784765163793741755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22383186092707103449978013 8393694784765163793741755)
        ·
          refine ⟨12590542177147745690612633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8393694784765163793741755 12590542177147745690612633)
          ·
            refine ⟨9442906632860809267959475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12590542177147745690612633 9442906632860809267959475)
            ·
              refine ⟨14164359949291213901939213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9442906632860809267959475 14164359949291213901939213)
              ·
                refine ⟨5311634980984205213227205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14164359949291213901939213 5311634980984205213227205)
                ·
                  refine ⟨995931558934538477480101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5311634980984205213227205 995931558934538477480101)
                  ·
                    refine ⟨186737167300225964527519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 995931558934538477480101 186737167300225964527519)
                    ·
                      rfl

theorem cell22_545504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 3, 4, 4].length) (baseStart_545504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_545504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_545504 prefixEnd_545504 := by exact prefixLift 545504
  have htrace : WordTrace (prefixWord ++ tailWord_545504) baseStart_545504 baseEnd_545504 := by
    simpa [prefixWord, tailWord_545504, baseEnd_545504] using wordTrace_append hprefix tailTrace_545504
  have hstable : (prefixWord ++ tailWord_545504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545504).length < 2 ^ (prefixWord ++ tailWord_545504).sum := by decide
  have hdescent : baseEnd_545504 < baseStart_545504 := by decide
  rcases family_descends (prefixWord ++ tailWord_545504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545568 : List Nat := [2, 1, 1, 5, 1, 2, 3, 1, 3, 3]
def baseStart_545568 : Nat := 118140960795 + 545568 * 2 ^ 59
def prefixEnd_545568 : Nat := 4983230072969 + 3 ^ 40 * 545568 * 2
def baseEnd_545568 : Nat := 186759075808151130927323

theorem tailTrace_545568 : CollatzResearch.WordTrace tailWord_545568 prefixEnd_545568 186759075808151130927323 := by
  unfold tailWord_545568
  simp only [CollatzResearch.WordTrace]
  refine ⟨9949249843753893220710679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13265666458338524294280905 9949249843753893220710679)
  ·
    refine ⟨14923874765630839831066019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9949249843753893220710679 14923874765630839831066019)
    ·
      refine ⟨22385812148446259746599029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14923874765630839831066019 22385812148446259746599029)
      ·
        refine ⟨2098669888916836851243659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 22385812148446259746599029 2098669888916836851243659)
        ·
          refine ⟨3148004833375255276865489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2098669888916836851243659 3148004833375255276865489)
          ·
            refine ⟨2361003625031441457649117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3148004833375255276865489 2361003625031441457649117)
            ·
              refine ⟨885376359386790546618419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2361003625031441457649117 885376359386790546618419)
              ·
                refine ⟨1328064539080185819927629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 885376359386790546618419 1328064539080185819927629)
                ·
                  refine ⟨498024202155069682472861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1328064539080185819927629 498024202155069682472861)
                  ·
                    refine ⟨186759075808151130927323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 498024202155069682472861 186759075808151130927323)
                    ·
                      rfl

theorem cell22_545568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 3, 1, 3, 3].length) (baseStart_545568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_545568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_545568 prefixEnd_545568 := by exact prefixLift 545568
  have htrace : WordTrace (prefixWord ++ tailWord_545568) baseStart_545568 baseEnd_545568 := by
    simpa [prefixWord, tailWord_545568, baseEnd_545568] using wordTrace_append hprefix tailTrace_545568
  have hstable : (prefixWord ++ tailWord_545568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545568).length < 2 ^ (prefixWord ++ tailWord_545568).sum := by decide
  have hdescent : baseEnd_545568 < baseStart_545568 := by decide
  rcases family_descends (prefixWord ++ tailWord_545568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545628 : List Nat := [2, 2, 4, 2, 1, 1, 1, 2, 3, 4]
def baseStart_545628 : Nat := 118140960795 + 545628 * 2 ^ 59
def prefixEnd_545628 : Nat := 4983230072969 + 3 ^ 40 * 545628 * 2
def baseEnd_545628 : Nat := 186779615034330974427139

theorem tailTrace_545628 : CollatzResearch.WordTrace tailWord_545628 prefixEnd_545628 186779615034330974427139 := by
  unfold tailWord_545628
  simp only [CollatzResearch.WordTrace]
  refine ⟨9950344033645208344302769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13267125378193611125737025 9950344033645208344302769)
  ·
    refine ⟨7462758025233906258227077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9950344033645208344302769 7462758025233906258227077)
    ·
      refine ⟨1399267129731357423417577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7462758025233906258227077 1399267129731357423417577)
      ·
        refine ⟨1049450347298518067563183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1399267129731357423417577 1049450347298518067563183)
        ·
          refine ⟨1574175520947777101344775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1049450347298518067563183 1574175520947777101344775)
          ·
            refine ⟨2361263281421665652017163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1574175520947777101344775 2361263281421665652017163)
            ·
              refine ⟨3541894922132498478025745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2361263281421665652017163 3541894922132498478025745)
              ·
                refine ⟨2656421191599373858519309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3541894922132498478025745 2656421191599373858519309)
                ·
                  refine ⟨996157946849765196944741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2656421191599373858519309 996157946849765196944741)
                  ·
                    refine ⟨186779615034330974427139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 996157946849765196944741 186779615034330974427139)
                    ·
                      rfl

theorem cell22_545628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_545628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_545628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_545628 prefixEnd_545628 := by exact prefixLift 545628
  have htrace : WordTrace (prefixWord ++ tailWord_545628) baseStart_545628 baseEnd_545628 := by
    simpa [prefixWord, tailWord_545628, baseEnd_545628] using wordTrace_append hprefix tailTrace_545628
  have hstable : (prefixWord ++ tailWord_545628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545628).length < 2 ^ (prefixWord ++ tailWord_545628).sum := by decide
  have hdescent : baseEnd_545628 < baseStart_545628 := by decide
  rcases family_descends (prefixWord ++ tailWord_545628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545641 : List Nat := [1, 2, 1, 1, 1, 3, 1, 1, 8, 3]
def baseStart_545641 : Nat := 118140960795 + 545641 * 2 ^ 59
def prefixEnd_545641 : Nat := 4983230072969 + 3 ^ 40 * 545641 * 2
def baseEnd_545641 : Nat := 186784065200003273852099

theorem tailTrace_545641 : CollatzResearch.WordTrace tailWord_545641 prefixEnd_545641 186784065200003273852099 := by
  unfold tailWord_545641
  simp only [CollatzResearch.WordTrace]
  refine ⟨19901162216243319908828777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13267441477495546605885851 19901162216243319908828777)
  ·
    refine ⟨14925871662182489931621583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19901162216243319908828777 14925871662182489931621583)
    ·
      refine ⟨22388807493273734897432375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14925871662182489931621583 22388807493273734897432375)
      ·
        refine ⟨33583211239910602346148563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22388807493273734897432375 33583211239910602346148563)
        ·
          refine ⟨50374816859865903519222845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33583211239910602346148563 50374816859865903519222845)
          ·
            refine ⟨18890556322449713819708567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50374816859865903519222845 18890556322449713819708567)
            ·
              refine ⟨28335834483674570729562851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18890556322449713819708567 28335834483674570729562851)
              ·
                refine ⟨42503751725511856094344277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28335834483674570729562851 42503751725511856094344277)
                ·
                  refine ⟨498090840533342063605597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 42503751725511856094344277 498090840533342063605597)
                  ·
                    refine ⟨186784065200003273852099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 498090840533342063605597 186784065200003273852099)
                    ·
                      rfl

theorem cell22_545641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 8, 3].length) (baseStart_545641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_545641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_545641 prefixEnd_545641 := by exact prefixLift 545641
  have htrace : WordTrace (prefixWord ++ tailWord_545641) baseStart_545641 baseEnd_545641 := by
    simpa [prefixWord, tailWord_545641, baseEnd_545641] using wordTrace_append hprefix tailTrace_545641
  have hstable : (prefixWord ++ tailWord_545641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545641).length < 2 ^ (prefixWord ++ tailWord_545641).sum := by decide
  have hdescent : baseEnd_545641 < baseStart_545641 := by decide
  rcases family_descends (prefixWord ++ tailWord_545641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545656 : List Nat := [2, 1, 2, 1, 1, 1, 1, 7, 2, 4]
def baseStart_545656 : Nat := 118140960795 + 545656 * 2 ^ 59
def prefixEnd_545656 : Nat := 4983230072969 + 3 ^ 40 * 545656 * 2
def baseEnd_545656 : Nat := 186789200006548234727053

theorem tailTrace_545656 : CollatzResearch.WordTrace tailWord_545656 prefixEnd_545656 186789200006548234727053 := by
  unfold tailWord_545656
  simp only [CollatzResearch.WordTrace]
  refine ⟨9950854655594488735312411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13267806207459318313749881 9950854655594488735312411)
  ·
    refine ⟨14926281983391733102968617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9950854655594488735312411 14926281983391733102968617)
    ·
      refine ⟨11194711487543799827226463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14926281983391733102968617 11194711487543799827226463)
      ·
        refine ⟨16792067231315699740839695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11194711487543799827226463 16792067231315699740839695)
        ·
          refine ⟨25188100846973549611259543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16792067231315699740839695 25188100846973549611259543)
          ·
            refine ⟨37782151270460324416889315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25188100846973549611259543 37782151270460324416889315)
            ·
              refine ⟨56673226905690486625333973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37782151270460324416889315 56673226905690486625333973)
              ·
                refine ⟨1328278755602120780281265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 56673226905690486625333973 1328278755602120780281265)
                ·
                  refine ⟨996209066701590585210949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1328278755602120780281265 996209066701590585210949)
                  ·
                    refine ⟨186789200006548234727053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 996209066701590585210949 186789200006548234727053)
                    ·
                      rfl

theorem cell22_545656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 7, 2, 4].length) (baseStart_545656 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_545656 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_545656 prefixEnd_545656 := by exact prefixLift 545656
  have htrace : WordTrace (prefixWord ++ tailWord_545656) baseStart_545656 baseEnd_545656 := by
    simpa [prefixWord, tailWord_545656, baseEnd_545656] using wordTrace_append hprefix tailTrace_545656
  have hstable : (prefixWord ++ tailWord_545656).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545656).length < 2 ^ (prefixWord ++ tailWord_545656).sum := by decide
  have hdescent : baseEnd_545656 < baseStart_545656 := by decide
  rcases family_descends (prefixWord ++ tailWord_545656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545662 : List Nat := [4, 2, 3, 1, 2, 1, 1, 3, 1, 4]
def baseStart_545662 : Nat := 118140960795 + 545662 * 2 ^ 59
def prefixEnd_545662 : Nat := 4983230072969 + 3 ^ 40 * 545662 * 2
def baseEnd_545662 : Nat := 186791253929166219077035

theorem tailTrace_545662 : CollatzResearch.WordTrace tailWord_545662 prefixEnd_545662 186791253929166219077035 := by
  unfold tailWord_545662
  simp only [CollatzResearch.WordTrace]
  refine ⟨2487741018645905061917905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13267952099444826996895493 2487741018645905061917905)
  ·
    refine ⟨1865805763984428796438429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2487741018645905061917905 1865805763984428796438429)
    ·
      refine ⟨699677161494160798664411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1865805763984428796438429 699677161494160798664411)
      ·
        refine ⟨1049515742241241197996617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 699677161494160798664411 1049515742241241197996617)
        ·
          refine ⟨787136806680930898497463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1049515742241241197996617 787136806680930898497463)
          ·
            refine ⟨1180705210021396347746195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 787136806680930898497463 1180705210021396347746195)
            ·
              refine ⟨1771057815032094521619293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1180705210021396347746195 1771057815032094521619293)
              ·
                refine ⟨664146680637035445607235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1771057815032094521619293 664146680637035445607235)
                ·
                  refine ⟨996220020955553168410853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 664146680637035445607235 996220020955553168410853)
                  ·
                    refine ⟨186791253929166219077035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 996220020955553168410853 186791253929166219077035)
                    ·
                      rfl

theorem cell22_545662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_545662 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_545662 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_545662 prefixEnd_545662 := by exact prefixLift 545662
  have htrace : WordTrace (prefixWord ++ tailWord_545662) baseStart_545662 baseEnd_545662 := by
    simpa [prefixWord, tailWord_545662, baseEnd_545662] using wordTrace_append hprefix tailTrace_545662
  have hstable : (prefixWord ++ tailWord_545662).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545662).length < 2 ^ (prefixWord ++ tailWord_545662).sum := by decide
  have hdescent : baseEnd_545662 < baseStart_545662 := by decide
  rcases family_descends (prefixWord ++ tailWord_545662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545671 : List Nat := [1, 1, 4, 2, 3, 2, 9]
def baseStart_545671 : Nat := 118140960795 + 545671 * 2 ^ 59
def prefixEnd_545671 : Nat := 4983230072969 + 3 ^ 40 * 545671 * 2
def baseEnd_545671 : Nat := 6918308696781229466741

theorem tailTrace_545671 : CollatzResearch.WordTrace tailWord_545671 prefixEnd_545671 6918308696781229466741 := by
  unfold tailWord_545671
  simp only [CollatzResearch.WordTrace]
  refine ⟨19902256406134635032420867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13268170937423090021613911 19902256406134635032420867)
  ·
    refine ⟨29853384609201952548631301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19902256406134635032420867 29853384609201952548631301)
    ·
      refine ⟨5597509614225366102868369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29853384609201952548631301 5597509614225366102868369)
      ·
        refine ⟨4198132210669024577151277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5597509614225366102868369 4198132210669024577151277)
        ·
          refine ⟨1574299579000884216431729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4198132210669024577151277 1574299579000884216431729)
          ·
            refine ⟨1180724684250663162323797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1574299579000884216431729 1180724684250663162323797)
            ·
              refine ⟨6918308696781229466741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1180724684250663162323797 6918308696781229466741)
              ·
                rfl

theorem cell22_545671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 9].length) (baseStart_545671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_545671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_545671 prefixEnd_545671 := by exact prefixLift 545671
  have htrace : WordTrace (prefixWord ++ tailWord_545671) baseStart_545671 baseEnd_545671 := by
    simpa [prefixWord, tailWord_545671, baseEnd_545671] using wordTrace_append hprefix tailTrace_545671
  have hstable : (prefixWord ++ tailWord_545671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545671).length < 2 ^ (prefixWord ++ tailWord_545671).sum := by decide
  have hdescent : baseEnd_545671 < baseStart_545671 := by decide
  rcases family_descends (prefixWord ++ tailWord_545671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545692 : List Nat := [2, 2, 3, 3, 3, 1, 1, 1, 1, 5]
def baseStart_545692 : Nat := 118140960795 + 545692 * 2 ^ 59
def prefixEnd_545692 : Nat := 4983230072969 + 3 ^ 40 * 545692 * 2
def baseEnd_545692 : Nat := 186801523542256140826943

theorem tailTrace_545692 : CollatzResearch.WordTrace tailWord_545692 prefixEnd_545692 186801523542256140826943 := by
  unfold tailWord_545692
  simp only [CollatzResearch.WordTrace]
  refine ⟨9951511169529277809467665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13268681559372370412623553 9951511169529277809467665)
  ·
    refine ⟨7463633377146958357100749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9951511169529277809467665 7463633377146958357100749)
    ·
      refine ⟨2798862516430109383912781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7463633377146958357100749 2798862516430109383912781)
      ·
        refine ⟨1049573443661291018967293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2798862516430109383912781 1049573443661291018967293)
        ·
          refine ⟨393590041372984132112735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1049573443661291018967293 393590041372984132112735)
          ·
            refine ⟨590385062059476198169103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 393590041372984132112735 590385062059476198169103)
            ·
              refine ⟨885577593089214297253655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 590385062059476198169103 885577593089214297253655)
              ·
                refine ⟨1328366389633821445880483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 885577593089214297253655 1328366389633821445880483)
                ·
                  refine ⟨1992549584450732168820725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1328366389633821445880483 1992549584450732168820725)
                  ·
                    refine ⟨186801523542256140826943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1992549584450732168820725 186801523542256140826943)
                    ·
                      rfl

theorem cell22_545692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 1, 1, 1, 5].length) (baseStart_545692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_545692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_545692 prefixEnd_545692 := by exact prefixLift 545692
  have htrace : WordTrace (prefixWord ++ tailWord_545692) baseStart_545692 baseEnd_545692 := by
    simpa [prefixWord, tailWord_545692, baseEnd_545692] using wordTrace_append hprefix tailTrace_545692
  have hstable : (prefixWord ++ tailWord_545692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545692).length < 2 ^ (prefixWord ++ tailWord_545692).sum := by decide
  have hdescent : baseEnd_545692 < baseStart_545692 := by decide
  rcases family_descends (prefixWord ++ tailWord_545692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545761 : List Nat := [1, 2, 3, 1, 2, 1, 1, 3, 8]
def baseStart_545761 : Nat := 118140960795 + 545761 * 2 ^ 59
def prefixEnd_545761 : Nat := 4983230072969 + 3 ^ 40 * 545761 * 2
def baseEnd_545761 : Nat := 62275047884120986950577

theorem tailTrace_545761 : CollatzResearch.WordTrace tailWord_545761 prefixEnd_545761 62275047884120986950577 := by
  unfold tailWord_545761
  simp only [CollatzResearch.WordTrace]
  refine ⟨19905538975808580403197137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13270359317205720268798091 19905538975808580403197137)
  ·
    refine ⟨14929154231856435302397853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19905538975808580403197137 14929154231856435302397853)
    ·
      refine ⟨5598432836946163238399195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14929154231856435302397853 5598432836946163238399195)
      ·
        refine ⟨8397649255419244857598793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5598432836946163238399195 8397649255419244857598793)
        ·
          refine ⟨6298236941564433643199095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8397649255419244857598793 6298236941564433643199095)
          ·
            refine ⟨9447355412346650464798643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6298236941564433643199095 9447355412346650464798643)
            ·
              refine ⟨14171033118519975697197965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9447355412346650464798643 14171033118519975697197965)
              ·
                refine ⟨5314137419444990886449237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14171033118519975697197965 5314137419444990886449237)
                ·
                  refine ⟨62275047884120986950577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5314137419444990886449237 62275047884120986950577)
                  ·
                    rfl

theorem cell22_545761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 3, 8].length) (baseStart_545761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_545761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_545761 prefixEnd_545761 := by exact prefixLift 545761
  have htrace : WordTrace (prefixWord ++ tailWord_545761) baseStart_545761 baseEnd_545761 := by
    simpa [prefixWord, tailWord_545761, baseEnd_545761] using wordTrace_append hprefix tailTrace_545761
  have hstable : (prefixWord ++ tailWord_545761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545761).length < 2 ^ (prefixWord ++ tailWord_545761).sum := by decide
  have hdescent : baseEnd_545761 < baseStart_545761 := by decide
  rcases family_descends (prefixWord ++ tailWord_545761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545763 : List Nat := [1, 1, 1, 6, 1, 1, 3, 1, 3, 4]
def baseStart_545763 : Nat := 118140960795 + 545763 * 2 ^ 59
def prefixEnd_545763 : Nat := 4983230072969 + 3 ^ 40 * 545763 * 2
def baseEnd_545763 : Nat := 186825828293235622301725

theorem tailTrace_545763 : CollatzResearch.WordTrace tailWord_545763 prefixEnd_545763 186825828293235622301725 := by
  unfold tailWord_545763
  simp only [CollatzResearch.WordTrace]
  refine ⟨19905611921801334744769943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13270407947867556496513295 19905611921801334744769943)
  ·
    refine ⟨29858417882702002117154915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19905611921801334744769943 29858417882702002117154915)
    ·
      refine ⟨44787626824053003175732373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29858417882702002117154915 44787626824053003175732373)
      ·
        refine ⟨2099420007377484523862455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 44787626824053003175732373 2099420007377484523862455)
        ·
          refine ⟨3149130011066226785793683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2099420007377484523862455 3149130011066226785793683)
          ·
            refine ⟨4723695016599340178690525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3149130011066226785793683 4723695016599340178690525)
            ·
              refine ⟨1771385631224752567008947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4723695016599340178690525 1771385631224752567008947)
              ·
                refine ⟨2657078446837128850513421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1771385631224752567008947 2657078446837128850513421)
                ·
                  refine ⟨996404417563923318942533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2657078446837128850513421 996404417563923318942533)
                  ·
                    refine ⟨186825828293235622301725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 996404417563923318942533 186825828293235622301725)
                    ·
                      rfl

theorem cell22_545763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 1, 3, 4].length) (baseStart_545763 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_545763 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_545763 prefixEnd_545763 := by exact prefixLift 545763
  have htrace : WordTrace (prefixWord ++ tailWord_545763) baseStart_545763 baseEnd_545763 := by
    simpa [prefixWord, tailWord_545763, baseEnd_545763] using wordTrace_append hprefix tailTrace_545763
  have hstable : (prefixWord ++ tailWord_545763).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545763).length < 2 ^ (prefixWord ++ tailWord_545763).sum := by decide
  have hdescent : baseEnd_545763 < baseStart_545763 := by decide
  rcases family_descends (prefixWord ++ tailWord_545763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545791 : List Nat := [1, 1, 2, 2, 1, 2, 1, 1, 5, 6]
def baseStart_545791 : Nat := 118140960795 + 545791 * 2 ^ 59
def prefixEnd_545791 : Nat := 4983230072969 + 3 ^ 40 * 545791 * 2
def baseEnd_545791 : Nat := 186835413265452882601639

theorem tailTrace_545791 : CollatzResearch.WordTrace tailWord_545791 prefixEnd_545791 186835413265452882601639 := by
  unfold tailWord_545791
  simp only [CollatzResearch.WordTrace]
  refine ⟨19906633165699895526789227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13271088777133263684526151 19906633165699895526789227)
  ·
    refine ⟨29859949748549843290183841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19906633165699895526789227 29859949748549843290183841)
    ·
      refine ⟨22394962311412382467637881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29859949748549843290183841 22394962311412382467637881)
      ·
        refine ⟨16796221733559286850728411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22394962311412382467637881 16796221733559286850728411)
        ·
          refine ⟨25194332600338930276092617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16796221733559286850728411 25194332600338930276092617)
          ·
            refine ⟨18895749450254197707069463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25194332600338930276092617 18895749450254197707069463)
            ·
              refine ⟨28343624175381296560604195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18895749450254197707069463 28343624175381296560604195)
              ·
                refine ⟨42515436263071944840906293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28343624175381296560604195 42515436263071944840906293)
                ·
                  refine ⟨3985822149662994828834965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 42515436263071944840906293 3985822149662994828834965)
                  ·
                    refine ⟨186835413265452882601639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3985822149662994828834965 186835413265452882601639)
                    ·
                      rfl

theorem cell22_545791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 5, 6].length) (baseStart_545791 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_545791 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_545791 prefixEnd_545791 := by exact prefixLift 545791
  have htrace : WordTrace (prefixWord ++ tailWord_545791) baseStart_545791 baseEnd_545791 := by
    simpa [prefixWord, tailWord_545791, baseEnd_545791] using wordTrace_append hprefix tailTrace_545791
  have hstable : (prefixWord ++ tailWord_545791).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545791).length < 2 ^ (prefixWord ++ tailWord_545791).sum := by decide
  have hdescent : baseEnd_545791 < baseStart_545791 := by decide
  rcases family_descends (prefixWord ++ tailWord_545791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545825 : List Nat := [1, 2, 3, 2, 3, 1, 3, 1, 2, 4]
def baseStart_545825 : Nat := 118140960795 + 545825 * 2 ^ 59
def prefixEnd_545825 : Nat := 4983230072969 + 3 ^ 40 * 545825 * 2
def baseEnd_545825 : Nat := 186847052160288127251535

theorem tailTrace_545825 : CollatzResearch.WordTrace tailWord_545825 prefixEnd_545825 186847052160288127251535 := by
  unfold tailWord_545825
  simp only [CollatzResearch.WordTrace]
  refine ⟨19907873247576719333526929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13271915498384479555684619 19907873247576719333526929)
  ·
    refine ⟨14930904935682539500145197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19907873247576719333526929 14930904935682539500145197)
    ·
      refine ⟨5599089350880952312554449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14930904935682539500145197 5599089350880952312554449)
      ·
        refine ⟨4199317013160714234415837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5599089350880952312554449 4199317013160714234415837)
        ·
          refine ⟨1574743879935267837905939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4199317013160714234415837 1574743879935267837905939)
          ·
            refine ⟨2362115819902901756858909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1574743879935267837905939 2362115819902901756858909)
            ·
              refine ⟨885793432463588158822091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2362115819902901756858909 885793432463588158822091)
              ·
                refine ⟨1328690148695382238233137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 885793432463588158822091 1328690148695382238233137)
                ·
                  refine ⟨996517611521536678674853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1328690148695382238233137 996517611521536678674853)
                  ·
                    refine ⟨186847052160288127251535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 996517611521536678674853 186847052160288127251535)
                    ·
                      rfl

theorem cell22_545825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 3, 1, 2, 4].length) (baseStart_545825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_545825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_545825 prefixEnd_545825 := by exact prefixLift 545825
  have htrace : WordTrace (prefixWord ++ tailWord_545825) baseStart_545825 baseEnd_545825 := by
    simpa [prefixWord, tailWord_545825, baseEnd_545825] using wordTrace_append hprefix tailTrace_545825
  have hstable : (prefixWord ++ tailWord_545825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545825).length < 2 ^ (prefixWord ++ tailWord_545825).sum := by decide
  have hdescent : baseEnd_545825 < baseStart_545825 := by decide
  rcases family_descends (prefixWord ++ tailWord_545825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545844 : List Nat := [2, 5, 1, 2, 1, 1, 3, 2, 2, 3]
def baseStart_545844 : Nat := 118140960795 + 545844 * 2 ^ 59
def prefixEnd_545844 : Nat := 4983230072969 + 3 ^ 40 * 545844 * 2
def baseEnd_545844 : Nat := 186853556248578411026477

theorem tailTrace_545844 : CollatzResearch.WordTrace tailWord_545844 prefixEnd_545844 186853556248578411026477 := by
  unfold tailWord_545844
  simp only [CollatzResearch.WordTrace]
  refine ⟨9954283117253942789234293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13272377489671923718979057 9954283117253942789234293)
  ·
    refine ⟨933214042242557136490715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9954283117253942789234293 933214042242557136490715)
    ·
      refine ⟨1399821063363835704736073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 933214042242557136490715 1399821063363835704736073)
      ·
        refine ⟨1049865797522876778552055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1399821063363835704736073 1049865797522876778552055)
        ·
          refine ⟨1574798696284315167828083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1049865797522876778552055 1574798696284315167828083)
          ·
            refine ⟨2362198044426472751742125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1574798696284315167828083 2362198044426472751742125)
            ·
              refine ⟨885824266659927281903297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2362198044426472751742125 885824266659927281903297)
              ·
                refine ⟨664368199994945461427473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 885824266659927281903297 664368199994945461427473)
                ·
                  refine ⟨498276149996209096070605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 664368199994945461427473 498276149996209096070605)
                  ·
                    refine ⟨186853556248578411026477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 498276149996209096070605 186853556248578411026477)
                    ·
                      rfl

theorem cell22_545844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 3, 2, 2, 3].length) (baseStart_545844 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_545844 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_545844 prefixEnd_545844 := by exact prefixLift 545844
  have htrace : WordTrace (prefixWord ++ tailWord_545844) baseStart_545844 baseEnd_545844 := by
    simpa [prefixWord, tailWord_545844, baseEnd_545844] using wordTrace_append hprefix tailTrace_545844
  have hstable : (prefixWord ++ tailWord_545844).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545844).length < 2 ^ (prefixWord ++ tailWord_545844).sum := by decide
  have hdescent : baseEnd_545844 < baseStart_545844 := by decide
  rcases family_descends (prefixWord ++ tailWord_545844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546003 : List Nat := [1, 1, 1, 2, 1, 1, 1, 5, 9]
def baseStart_546003 : Nat := 118140960795 + 546003 * 2 ^ 59
def prefixEnd_546003 : Nat := 4983230072969 + 3 ^ 40 * 546003 * 2
def baseEnd_546003 : Nat := 62302661732651665433663

theorem tailTrace_546003 : CollatzResearch.WordTrace tailWord_546003 prefixEnd_546003 62302661732651665433663 := by
  unfold tailWord_546003
  simp only [CollatzResearch.WordTrace]
  refine ⟨19914365440931855733506663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13276243627287903822337775 19914365440931855733506663)
  ·
    refine ⟨29871548161397783600259995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19914365440931855733506663 29871548161397783600259995)
    ·
      refine ⟨44807322242096675400389993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29871548161397783600259995 44807322242096675400389993)
      ·
        refine ⟨33605491681572506550292495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44807322242096675400389993 33605491681572506550292495)
        ·
          refine ⟨50408237522358759825438743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33605491681572506550292495 50408237522358759825438743)
          ·
            refine ⟨75612356283538139738158115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50408237522358759825438743 75612356283538139738158115)
            ·
              refine ⟨113418534425307209607237173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75612356283538139738158115 113418534425307209607237173)
              ·
                refine ⟨10632987602372550900678485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 113418534425307209607237173 10632987602372550900678485)
                ·
                  refine ⟨62302661732651665433663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 10632987602372550900678485 62302661732651665433663)
                  ·
                    rfl

theorem cell22_546003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 5, 9].length) (baseStart_546003 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_546003 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_546003 prefixEnd_546003 := by exact prefixLift 546003
  have htrace : WordTrace (prefixWord ++ tailWord_546003) baseStart_546003 baseEnd_546003 := by
    simpa [prefixWord, tailWord_546003, baseEnd_546003] using wordTrace_append hprefix tailTrace_546003
  have hstable : (prefixWord ++ tailWord_546003).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546003).length < 2 ^ (prefixWord ++ tailWord_546003).sum := by decide
  have hdescent : baseEnd_546003 < baseStart_546003 := by decide
  rcases family_descends (prefixWord ++ tailWord_546003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546013 : List Nat := [1, 4, 3, 2, 3, 1, 1, 2, 2, 3]
def baseStart_546013 : Nat := 118140960795 + 546013 * 2 ^ 59
def prefixEnd_546013 : Nat := 4983230072969 + 3 ^ 40 * 546013 * 2
def baseEnd_546013 : Nat := 186911408402318303550959

theorem tailTrace_546013 : CollatzResearch.WordTrace tailWord_546013 prefixEnd_546013 186911408402318303550959 := by
  unfold tailWord_546013
  simp only [CollatzResearch.WordTrace]
  refine ⟨19914730170895627441370693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13276486780597084960913795 19914730170895627441370693)
  ·
    refine ⟨3734011907042930145257005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19914730170895627441370693 3734011907042930145257005)
    ·
      refine ⟨1400254465141098804471377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3734011907042930145257005 1400254465141098804471377)
      ·
        refine ⟨1050190848855824103353533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1400254465141098804471377 1050190848855824103353533)
        ·
          refine ⟨393821568320934038757575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1050190848855824103353533 393821568320934038757575)
          ·
            refine ⟨590732352481401058136363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 393821568320934038757575 590732352481401058136363)
            ·
              refine ⟨886098528722101587204545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 590732352481401058136363 886098528722101587204545)
              ·
                refine ⟨664573896541576190403409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 886098528722101587204545 664573896541576190403409)
                ·
                  refine ⟨498430422406182142802557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 664573896541576190403409 498430422406182142802557)
                  ·
                    refine ⟨186911408402318303550959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 498430422406182142802557 186911408402318303550959)
                    ·
                      rfl

theorem cell22_546013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 1, 2, 2, 3].length) (baseStart_546013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_546013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_546013 prefixEnd_546013 := by exact prefixLift 546013
  have htrace : WordTrace (prefixWord ++ tailWord_546013) baseStart_546013 baseEnd_546013 := by
    simpa [prefixWord, tailWord_546013, baseEnd_546013] using wordTrace_append hprefix tailTrace_546013
  have hstable : (prefixWord ++ tailWord_546013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546013).length < 2 ^ (prefixWord ++ tailWord_546013).sum := by decide
  have hdescent : baseEnd_546013 < baseStart_546013 := by decide
  rcases family_descends (prefixWord ++ tailWord_546013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546024 : List Nat := [2, 1, 4, 1, 2, 1, 1, 6, 1, 3]
def baseStart_546024 : Nat := 118140960795 + 546024 * 2 ^ 59
def prefixEnd_546024 : Nat := 4983230072969 + 3 ^ 40 * 546024 * 2
def baseEnd_546024 : Nat := 186915173927117941525925

theorem tailTrace_546024 : CollatzResearch.WordTrace tailWord_546024 prefixEnd_546024 186915173927117941525925 := by
  unfold tailWord_546024
  simp only [CollatzResearch.WordTrace]
  refine ⟨9957565686927888160010563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13276754249237184213347417 9957565686927888160010563)
  ·
    refine ⟨14936348530391832240015845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9957565686927888160010563 14936348530391832240015845)
    ·
      refine ⟨2800565349448468545002971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14936348530391832240015845 2800565349448468545002971)
      ·
        refine ⟨4200848024172702817504457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2800565349448468545002971 4200848024172702817504457)
        ·
          refine ⟨3150636018129527113128343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4200848024172702817504457 3150636018129527113128343)
          ·
            refine ⟨4725954027194290669692515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3150636018129527113128343 4725954027194290669692515)
            ·
              refine ⟨7088931040791436004538773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4725954027194290669692515 7088931040791436004538773)
              ·
                refine ⟨332293642537098562712755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7088931040791436004538773 332293642537098562712755)
                ·
                  refine ⟨498440463805647844069133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 332293642537098562712755 498440463805647844069133)
                  ·
                    refine ⟨186915173927117941525925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 498440463805647844069133 186915173927117941525925)
                    ·
                      rfl

theorem cell22_546024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 6, 1, 3].length) (baseStart_546024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_546024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_546024 prefixEnd_546024 := by exact prefixLift 546024
  have htrace : WordTrace (prefixWord ++ tailWord_546024) baseStart_546024 baseEnd_546024 := by
    simpa [prefixWord, tailWord_546024, baseEnd_546024] using wordTrace_append hprefix tailTrace_546024
  have hstable : (prefixWord ++ tailWord_546024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546024).length < 2 ^ (prefixWord ++ tailWord_546024).sum := by decide
  have hdescent : baseEnd_546024 < baseStart_546024 := by decide
  rcases family_descends (prefixWord ++ tailWord_546024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546035 : List Nat := [1, 1, 1, 2, 2, 5, 2, 1, 2, 5]
def baseStart_546035 : Nat := 118140960795 + 546035 * 2 ^ 59
def prefixEnd_546035 : Nat := 4983230072969 + 3 ^ 40 * 546035 * 2
def baseEnd_546035 : Nat := 186918939451917579500891

theorem tailTrace_546035 : CollatzResearch.WordTrace tailWord_546035 prefixEnd_546035 186918939451917579500891 := by
  unfold tailWord_546035
  simp only [CollatzResearch.WordTrace]
  refine ⟨19915532576815925198671559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13277021717877283465781039 19915532576815925198671559)
  ·
    refine ⟨29873298865223887798007339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19915532576815925198671559 29873298865223887798007339)
    ·
      refine ⟨44809948297835831697011009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29873298865223887798007339 44809948297835831697011009)
      ·
        refine ⟨33607461223376873772758257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44809948297835831697011009 33607461223376873772758257)
        ·
          refine ⟨25205595917532655329568693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33607461223376873772758257 25205595917532655329568693)
          ·
            refine ⟨2363024617268686437147065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 25205595917532655329568693 2363024617268686437147065)
            ·
              refine ⟨1772268462951514827860299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2363024617268686437147065 1772268462951514827860299)
              ·
                refine ⟨2658402694427272241790449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1772268462951514827860299 2658402694427272241790449)
                ·
                  refine ⟨1993802020820454181342837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2658402694427272241790449 1993802020820454181342837)
                  ·
                    refine ⟨186918939451917579500891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1993802020820454181342837 186918939451917579500891)
                    ·
                      rfl

theorem cell22_546035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 1, 2, 5].length) (baseStart_546035 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_546035 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_546035 prefixEnd_546035 := by exact prefixLift 546035
  have htrace : WordTrace (prefixWord ++ tailWord_546035) baseStart_546035 baseEnd_546035 := by
    simpa [prefixWord, tailWord_546035, baseEnd_546035] using wordTrace_append hprefix tailTrace_546035
  have hstable : (prefixWord ++ tailWord_546035).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546035).length < 2 ^ (prefixWord ++ tailWord_546035).sum := by decide
  have hdescent : baseEnd_546035 < baseStart_546035 := by decide
  rcases family_descends (prefixWord ++ tailWord_546035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546095 : List Nat := [1, 1, 2, 1, 2, 1, 3, 1, 6, 4]
def baseStart_546095 : Nat := 118140960795 + 546095 * 2 ^ 59
def prefixEnd_546095 : Nat := 4983230072969 + 3 ^ 40 * 546095 * 2
def baseEnd_546095 : Nat := 186939478678097423000707

theorem tailTrace_546095 : CollatzResearch.WordTrace tailWord_546095 prefixEnd_546095 186939478678097423000707 := by
  unfold tailWord_546095
  simp only [CollatzResearch.WordTrace]
  refine ⟨19917720956598555445855739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13278480637732370297237159 19917720956598555445855739)
  ·
    refine ⟨29876581434897833168783609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19917720956598555445855739 29876581434897833168783609)
    ·
      refine ⟨22407436076173374876587707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29876581434897833168783609 22407436076173374876587707)
      ·
        refine ⟨33611154114260062314881561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22407436076173374876587707 33611154114260062314881561)
        ·
          refine ⟨25208365585695046736161171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33611154114260062314881561 25208365585695046736161171)
          ·
            refine ⟨37812548378542570104241757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25208365585695046736161171 37812548378542570104241757)
            ·
              refine ⟨14179705641953463789090659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37812548378542570104241757 14179705641953463789090659)
              ·
                refine ⟨21269558462930195683635989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14179705641953463789090659 21269558462930195683635989)
                ·
                  refine ⟨997010552949852922670437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 21269558462930195683635989 997010552949852922670437)
                  ·
                    refine ⟨186939478678097423000707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 997010552949852922670437 186939478678097423000707)
                    ·
                      rfl

theorem cell22_546095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 6, 4].length) (baseStart_546095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_546095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_546095 prefixEnd_546095 := by exact prefixLift 546095
  have htrace : WordTrace (prefixWord ++ tailWord_546095) baseStart_546095 baseEnd_546095 := by
    simpa [prefixWord, tailWord_546095, baseEnd_546095] using wordTrace_append hprefix tailTrace_546095
  have hstable : (prefixWord ++ tailWord_546095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546095).length < 2 ^ (prefixWord ++ tailWord_546095).sum := by decide
  have hdescent : baseEnd_546095 < baseStart_546095 := by decide
  rcases family_descends (prefixWord ++ tailWord_546095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546112 : List Nat := [2, 1, 1, 2, 2, 1, 6, 1, 2, 4]
def baseStart_546112 : Nat := 118140960795 + 546112 * 2 ^ 59
def prefixEnd_546112 : Nat := 4983230072969 + 3 ^ 40 * 546112 * 2
def baseEnd_546112 : Nat := 186945298125515045325655

theorem tailTrace_546112 : CollatzResearch.WordTrace tailWord_546112 prefixEnd_546112 186945298125515045325655 := by
  unfold tailWord_546112
  simp only [CollatzResearch.WordTrace]
  refine ⟨9959170498768483674612295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13278893998357978232816393 9959170498768483674612295)
  ·
    refine ⟨14938755748152725511918443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9959170498768483674612295 14938755748152725511918443)
    ·
      refine ⟨22408133622229088267877665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14938755748152725511918443 22408133622229088267877665)
      ·
        refine ⟨16806100216671816200908249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22408133622229088267877665 16806100216671816200908249)
        ·
          refine ⟨12604575162503862150681187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16806100216671816200908249 12604575162503862150681187)
          ·
            refine ⟨18906862743755793226021781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12604575162503862150681187 18906862743755793226021781)
            ·
              refine ⟨886259191113552807469771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 18906862743755793226021781 886259191113552807469771)
              ·
                refine ⟨1329388786670329211204657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 886259191113552807469771 1329388786670329211204657)
                ·
                  refine ⟨997041590002746908403493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1329388786670329211204657 997041590002746908403493)
                  ·
                    refine ⟨186945298125515045325655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 997041590002746908403493 186945298125515045325655)
                    ·
                      rfl

theorem cell22_546112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 6, 1, 2, 4].length) (baseStart_546112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_546112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_546112 prefixEnd_546112 := by exact prefixLift 546112
  have htrace : WordTrace (prefixWord ++ tailWord_546112) baseStart_546112 baseEnd_546112 := by
    simpa [prefixWord, tailWord_546112, baseEnd_546112] using wordTrace_append hprefix tailTrace_546112
  have hstable : (prefixWord ++ tailWord_546112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546112).length < 2 ^ (prefixWord ++ tailWord_546112).sum := by decide
  have hdescent : baseEnd_546112 < baseStart_546112 := by decide
  rcases family_descends (prefixWord ++ tailWord_546112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546232 : List Nat := [2, 1, 2, 1, 2, 2, 2, 4, 1, 5]
def baseStart_546232 : Nat := 118140960795 + 546232 * 2 ^ 59
def prefixEnd_546232 : Nat := 4983230072969 + 3 ^ 40 * 546232 * 2
def baseEnd_546232 : Nat := 186986376577874732325287

theorem tailTrace_546232 : CollatzResearch.WordTrace tailWord_546232 prefixEnd_546232 186986376577874732325287 := by
  unfold tailWord_546232
  simp only [CollatzResearch.WordTrace]
  refine ⟨9961358878551113921796475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13281811838068151895728633 9961358878551113921796475)
  ·
    refine ⟨14942038317826670882694713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9961358878551113921796475 14942038317826670882694713)
    ·
      refine ⟨11206528738370003162021035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14942038317826670882694713 11206528738370003162021035)
      ·
        refine ⟨16809793107555004743031553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11206528738370003162021035 16809793107555004743031553)
        ·
          refine ⟨12607344830666253557273665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16809793107555004743031553 12607344830666253557273665)
          ·
            refine ⟨9455508622999690167955249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12607344830666253557273665 9455508622999690167955249)
            ·
              refine ⟨7091631467249767625966437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9455508622999690167955249 7091631467249767625966437)
              ·
                refine ⟨1329680900109331429868707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7091631467249767625966437 1329680900109331429868707)
                ·
                  refine ⟨1994521350163997144803061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1329680900109331429868707 1994521350163997144803061)
                  ·
                    refine ⟨186986376577874732325287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1994521350163997144803061 186986376577874732325287)
                    ·
                      rfl

theorem cell22_546232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 4, 1, 5].length) (baseStart_546232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_546232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_546232 prefixEnd_546232 := by exact prefixLift 546232
  have htrace : WordTrace (prefixWord ++ tailWord_546232) baseStart_546232 baseEnd_546232 := by
    simpa [prefixWord, tailWord_546232, baseEnd_546232] using wordTrace_append hprefix tailTrace_546232
  have hstable : (prefixWord ++ tailWord_546232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546232).length < 2 ^ (prefixWord ++ tailWord_546232).sum := by decide
  have hdescent : baseEnd_546232 < baseStart_546232 := by decide
  rcases family_descends (prefixWord ++ tailWord_546232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546249 : List Nat := [1, 2, 1, 1, 2, 1, 3, 6, 2, 3]
def baseStart_546249 : Nat := 118140960795 + 546249 * 2 ^ 59
def prefixEnd_546249 : Nat := 4983230072969 + 3 ^ 40 * 546249 * 2
def baseEnd_546249 : Nat := 186992196025292354650235

theorem tailTrace_546249 : CollatzResearch.WordTrace tailWord_546249 prefixEnd_546249 186992196025292354650235 := by
  unfold tailWord_546249
  simp only [CollatzResearch.WordTrace]
  refine ⟨19923337798040639746961801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13282225198693759831307867 19923337798040639746961801)
  ·
    refine ⟨14942503348530479810221351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19923337798040639746961801 14942503348530479810221351)
    ·
      refine ⟨22413755022795719715332027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14942503348530479810221351 22413755022795719715332027)
      ·
        refine ⟨33620632534193579572998041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22413755022795719715332027 33620632534193579572998041)
        ·
          refine ⟨25215474400645184679748531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33620632534193579572998041 25215474400645184679748531)
          ·
            refine ⟨37823211600967777019622797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25215474400645184679748531 37823211600967777019622797)
            ·
              refine ⟨14183704350362916382358549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37823211600967777019622797 14183704350362916382358549)
              ·
                refine ⟨664861141423261705423057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 14183704350362916382358549 664861141423261705423057)
                ·
                  refine ⟨498645856067446279067293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 664861141423261705423057 498645856067446279067293)
                  ·
                    refine ⟨186992196025292354650235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 498645856067446279067293 186992196025292354650235)
                    ·
                      rfl

theorem cell22_546249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 6, 2, 3].length) (baseStart_546249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_546249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_546249 prefixEnd_546249 := by exact prefixLift 546249
  have htrace : WordTrace (prefixWord ++ tailWord_546249) baseStart_546249 baseEnd_546249 := by
    simpa [prefixWord, tailWord_546249, baseEnd_546249] using wordTrace_append hprefix tailTrace_546249
  have hstable : (prefixWord ++ tailWord_546249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546249).length < 2 ^ (prefixWord ++ tailWord_546249).sum := by decide
  have hdescent : baseEnd_546249 < baseStart_546249 := by decide
  rcases family_descends (prefixWord ++ tailWord_546249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546266 : List Nat := [3, 1, 1, 2, 3, 3, 1, 3, 2, 3]
def baseStart_546266 : Nat := 118140960795 + 546266 * 2 ^ 59
def prefixEnd_546266 : Nat := 4983230072969 + 3 ^ 40 * 546266 * 2
def baseEnd_546266 : Nat := 186998015472709976975183

theorem tailTrace_546266 : CollatzResearch.WordTrace tailWord_546266 prefixEnd_546266 186998015472709976975183 := by
  unfold tailWord_546266
  simp only [CollatzResearch.WordTrace]
  refine ⟨4980989459744762912582663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13282638559319367766887101 4980989459744762912582663)
  ·
    refine ⟨7471484189617144368873995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4980989459744762912582663 7471484189617144368873995)
    ·
      refine ⟨11207226284425716553310993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7471484189617144368873995 11207226284425716553310993)
      ·
        refine ⟨8405419713319287414983245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11207226284425716553310993 8405419713319287414983245)
        ·
          refine ⟨3152032392494732780618717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8405419713319287414983245 3152032392494732780618717)
          ·
            refine ⟨1182012147185524792732019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3152032392494732780618717 1182012147185524792732019)
            ·
              refine ⟨1773018220778287189098029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1182012147185524792732019 1773018220778287189098029)
              ·
                refine ⟨664881832791857695911761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1773018220778287189098029 664881832791857695911761)
                ·
                  refine ⟨498661374593893271933821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 664881832791857695911761 498661374593893271933821)
                  ·
                    refine ⟨186998015472709976975183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 498661374593893271933821 186998015472709976975183)
                    ·
                      rfl

theorem cell22_546266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 3, 2, 3].length) (baseStart_546266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_546266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_546266 prefixEnd_546266 := by exact prefixLift 546266
  have htrace : WordTrace (prefixWord ++ tailWord_546266) baseStart_546266 baseEnd_546266 := by
    simpa [prefixWord, tailWord_546266, baseEnd_546266] using wordTrace_append hprefix tailTrace_546266
  have hstable : (prefixWord ++ tailWord_546266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546266).length < 2 ^ (prefixWord ++ tailWord_546266).sum := by decide
  have hdescent : baseEnd_546266 < baseStart_546266 := by decide
  rcases family_descends (prefixWord ++ tailWord_546266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546302 : List Nat := [4, 2, 2, 3, 1, 2, 2, 2, 4]
def baseStart_546302 : Nat := 118140960795 + 546302 * 2 ^ 59
def prefixEnd_546302 : Nat := 4983230072969 + 3 ^ 40 * 546302 * 2
def baseEnd_546302 : Nat := 62336779669472627691691

theorem tailTrace_546302 : CollatzResearch.WordTrace tailWord_546302 prefixEnd_546302 62336779669472627691691 := by
  unfold tailWord_546302
  simp only [CollatzResearch.WordTrace]
  refine ⟨2490658858356078724830145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13283513911232419865760773 2490658858356078724830145)
  ·
    refine ⟨1867994143767059043622609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2490658858356078724830145 1867994143767059043622609)
    ·
      refine ⟨1400995607825294282716957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1867994143767059043622609 1400995607825294282716957)
      ·
        refine ⟨525373352934485356018859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1400995607825294282716957 525373352934485356018859)
        ·
          refine ⟨788060029401728034028289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 525373352934485356018859 788060029401728034028289)
          ·
            refine ⟨591045022051296025521217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 788060029401728034028289 591045022051296025521217)
            ·
              refine ⟨443283766538472019140913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 591045022051296025521217 443283766538472019140913)
              ·
                refine ⟨332462824903854014355685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 443283766538472019140913 332462824903854014355685)
                ·
                  refine ⟨62336779669472627691691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 332462824903854014355685 62336779669472627691691)
                  ·
                    rfl

theorem cell22_546302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 2, 2, 4].length) (baseStart_546302 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_546302 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_546302 prefixEnd_546302 := by exact prefixLift 546302
  have htrace : WordTrace (prefixWord ++ tailWord_546302) baseStart_546302 baseEnd_546302 := by
    simpa [prefixWord, tailWord_546302, baseEnd_546302] using wordTrace_append hprefix tailTrace_546302
  have hstable : (prefixWord ++ tailWord_546302).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546302).length < 2 ^ (prefixWord ++ tailWord_546302).sum := by decide
  have hdescent : baseEnd_546302 < baseStart_546302 := by decide
  rcases family_descends (prefixWord ++ tailWord_546302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546352 : List Nat := [2, 1, 1, 1, 2, 3, 1, 1, 10]
def baseStart_546352 : Nat := 118140960795 + 546352 * 2 ^ 59
def prefixEnd_546352 : Nat := 4983230072969 + 3 ^ 40 * 546352 * 2
def baseEnd_546352 : Nat := 62342485010078139774973

theorem tailTrace_546352 : CollatzResearch.WordTrace tailWord_546352 prefixEnd_546352 62342485010078139774973 := by
  unfold tailWord_546352
  simp only [CollatzResearch.WordTrace]
  refine ⟨9963547258333744168980655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13284729677778325558640873 9963547258333744168980655)
  ·
    refine ⟨14945320887500616253470983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9963547258333744168980655 14945320887500616253470983)
    ·
      refine ⟨22417981331250924380206475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14945320887500616253470983 22417981331250924380206475)
      ·
        refine ⟨33626971996876386570309713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22417981331250924380206475 33626971996876386570309713)
        ·
          refine ⟨25220228997657289927732285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33626971996876386570309713 25220228997657289927732285)
          ·
            refine ⟨9457585874121483722899607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25220228997657289927732285 9457585874121483722899607)
            ·
              refine ⟨14186378811182225584349411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9457585874121483722899607 14186378811182225584349411)
              ·
                refine ⟨21279568216773338376524117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14186378811182225584349411 21279568216773338376524117)
                ·
                  refine ⟨62342485010078139774973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 21279568216773338376524117 62342485010078139774973)
                  ·
                    rfl

theorem cell22_546352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 10].length) (baseStart_546352 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_546352 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_546352 prefixEnd_546352 := by exact prefixLift 546352
  have htrace : WordTrace (prefixWord ++ tailWord_546352) baseStart_546352 baseEnd_546352 := by
    simpa [prefixWord, tailWord_546352, baseEnd_546352] using wordTrace_append hprefix tailTrace_546352
  have hstable : (prefixWord ++ tailWord_546352).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546352).length < 2 ^ (prefixWord ++ tailWord_546352).sum := by decide
  have hdescent : baseEnd_546352 < baseStart_546352 := by decide
  rcases family_descends (prefixWord ++ tailWord_546352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546403 : List Nat := [1, 1, 1, 5, 1, 5, 1, 3, 4]
def baseStart_546403 : Nat := 118140960795 + 546403 * 2 ^ 59
def prefixEnd_546403 : Nat := 4983230072969 + 3 ^ 40 * 546403 * 2
def baseEnd_546403 : Nat := 62348304457495762099921

theorem tailTrace_546403 : CollatzResearch.WordTrace tailWord_546403 prefixEnd_546403 62348304457495762099921 := by
  unfold tailWord_546403
  simp only [CollatzResearch.WordTrace]
  refine ⟨19928954639482724048067863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13285969759655149365378575 19928954639482724048067863)
  ·
    refine ⟨29893431959224086072101795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19928954639482724048067863 29893431959224086072101795)
    ·
      refine ⟨44840147938836129108152693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29893431959224086072101795 44840147938836129108152693)
      ·
        refine ⟨4203763869265887103889315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 44840147938836129108152693 4203763869265887103889315)
        ·
          refine ⟨6305645803898830655833973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4203763869265887103889315 6305645803898830655833973)
          ·
            refine ⟨591154294115515373984435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6305645803898830655833973 591154294115515373984435)
            ·
              refine ⟨886731441173273060976653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 591154294115515373984435 886731441173273060976653)
              ·
                refine ⟨332524290439977397866245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 886731441173273060976653 332524290439977397866245)
                ·
                  refine ⟨62348304457495762099921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 332524290439977397866245 62348304457495762099921)
                  ·
                    rfl

theorem cell22_546403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 1, 3, 4].length) (baseStart_546403 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_546403 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_546403 prefixEnd_546403 := by exact prefixLift 546403
  have htrace : WordTrace (prefixWord ++ tailWord_546403) baseStart_546403 baseEnd_546403 := by
    simpa [prefixWord, tailWord_546403, baseEnd_546403] using wordTrace_append hprefix tailTrace_546403
  have hstable : (prefixWord ++ tailWord_546403).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546403).length < 2 ^ (prefixWord ++ tailWord_546403).sum := by decide
  have hdescent : baseEnd_546403 < baseStart_546403 := by decide
  rcases family_descends (prefixWord ++ tailWord_546403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546416 : List Nat := [2, 1, 1, 1, 6, 2, 1, 2, 2, 4]
def baseStart_546416 : Nat := 118140960795 + 546416 * 2 ^ 59
def prefixEnd_546416 : Nat := 4983230072969 + 3 ^ 40 * 546416 * 2
def baseEnd_546416 : Nat := 187049363538159585724723

theorem tailTrace_546416 : CollatzResearch.WordTrace tailWord_546416 prefixEnd_546416 187049363538159585724723 := by
  unfold tailWord_546416
  simp only [CollatzResearch.WordTrace]
  refine ⟨9964714394217813634145551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13286285858957084845527401 9964714394217813634145551)
  ·
    refine ⟨14947071591326720451218327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9964714394217813634145551 14947071591326720451218327)
    ·
      refine ⟨22420607386990080676827491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14947071591326720451218327 22420607386990080676827491)
      ·
        refine ⟨33630911080485121015241237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22420607386990080676827491 33630911080485121015241237)
        ·
          refine ⟨1576448956897740047589433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 33630911080485121015241237 1576448956897740047589433)
          ·
            refine ⟨1182336717673305035692075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1576448956897740047589433 1182336717673305035692075)
            ·
              refine ⟨1773505076509957553538113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1182336717673305035692075 1773505076509957553538113)
              ·
                refine ⟨1330128807382468165153585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1773505076509957553538113 1330128807382468165153585)
                ·
                  refine ⟨997596605536851123865189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1330128807382468165153585 997596605536851123865189)
                  ·
                    refine ⟨187049363538159585724723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 997596605536851123865189 187049363538159585724723)
                    ·
                      rfl

theorem cell22_546416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 2, 2, 4].length) (baseStart_546416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_546416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_546416 prefixEnd_546416 := by exact prefixLift 546416
  have htrace : WordTrace (prefixWord ++ tailWord_546416) baseStart_546416 baseEnd_546416 := by
    simpa [prefixWord, tailWord_546416, baseEnd_546416] using wordTrace_append hprefix tailTrace_546416
  have hstable : (prefixWord ++ tailWord_546416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546416).length < 2 ^ (prefixWord ++ tailWord_546416).sum := by decide
  have hdescent : baseEnd_546416 < baseStart_546416 := by decide
  rcases family_descends (prefixWord ++ tailWord_546416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546480 : List Nat := [2, 1, 1, 1, 2, 1, 8, 2, 1, 3]
def baseStart_546480 : Nat := 118140960795 + 546480 * 2 ^ 59
def prefixEnd_546480 : Nat := 4983230072969 + 3 ^ 40 * 546480 * 2
def baseEnd_546480 : Nat := 187071272046084752124527

theorem tailTrace_546480 : CollatzResearch.WordTrace tailWord_546480 prefixEnd_546480 187071272046084752124527 := by
  unfold tailWord_546480
  simp only [CollatzResearch.WordTrace]
  refine ⟨9965881530101883099310447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13287842040135844132413929 9965881530101883099310447)
  ·
    refine ⟨14948822295152824648965671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9965881530101883099310447 14948822295152824648965671)
    ·
      refine ⟨22423233442729236973448507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14948822295152824648965671 22423233442729236973448507)
      ·
        refine ⟨33634850164093855460172761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22423233442729236973448507 33634850164093855460172761)
        ·
          refine ⟨25226137623070391595129571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33634850164093855460172761 25226137623070391595129571)
          ·
            refine ⟨37839206434605587392694357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25226137623070391595129571 37839206434605587392694357)
            ·
              refine ⟨443428200405534227258137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 37839206434605587392694357 443428200405534227258137)
              ·
                refine ⟨332571150304150670443603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 443428200405534227258137 332571150304150670443603)
                ·
                  refine ⟨498856725456226005665405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 332571150304150670443603 498856725456226005665405)
                  ·
                    refine ⟨187071272046084752124527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 498856725456226005665405 187071272046084752124527)
                    ·
                      rfl

theorem cell22_546480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 8, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 8, 2, 1, 3].length) (baseStart_546480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_546480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_546480 prefixEnd_546480 := by exact prefixLift 546480
  have htrace : WordTrace (prefixWord ++ tailWord_546480) baseStart_546480 baseEnd_546480 := by
    simpa [prefixWord, tailWord_546480, baseEnd_546480] using wordTrace_append hprefix tailTrace_546480
  have hstable : (prefixWord ++ tailWord_546480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546480).length < 2 ^ (prefixWord ++ tailWord_546480).sum := by decide
  have hdescent : baseEnd_546480 < baseStart_546480 := by decide
  rcases family_descends (prefixWord ++ tailWord_546480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546538 : List Nat := [3, 1, 3, 1, 1, 1, 4, 4, 4]
def baseStart_546538 : Nat := 118140960795 + 546538 * 2 ^ 59
def prefixEnd_546538 : Nat := 4983230072969 + 3 ^ 40 * 546538 * 2
def baseEnd_546538 : Nat := 62363708877130644724783

theorem tailTrace_546538 : CollatzResearch.WordTrace tailWord_546538 prefixEnd_546538 62363708877130644724783 := by
  unfold tailWord_546538
  simp only [CollatzResearch.WordTrace]
  refine ⟨4983469623498410526058067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13289252329329094736154845 4983469623498410526058067)
  ·
    refine ⟨7475204435247615789087101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4983469623498410526058067 7475204435247615789087101)
    ·
      refine ⟨2803201663217855920907663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7475204435247615789087101 2803201663217855920907663)
      ·
        refine ⟨4204802494826783881361495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2803201663217855920907663 4204802494826783881361495)
        ·
          refine ⟨6307203742240175822042243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4204802494826783881361495 6307203742240175822042243)
          ·
            refine ⟨9460805613360263733063365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6307203742240175822042243 9460805613360263733063365)
            ·
              refine ⟨1773901052505049449949381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9460805613360263733063365 1773901052505049449949381)
              ·
                refine ⟨332606447344696771865509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1773901052505049449949381 332606447344696771865509)
                ·
                  refine ⟨62363708877130644724783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 332606447344696771865509 62363708877130644724783)
                  ·
                    rfl

theorem cell22_546538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 4, 4].length) (baseStart_546538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_546538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_546538 prefixEnd_546538 := by exact prefixLift 546538
  have htrace : WordTrace (prefixWord ++ tailWord_546538) baseStart_546538 baseEnd_546538 := by
    simpa [prefixWord, tailWord_546538, baseEnd_546538] using wordTrace_append hprefix tailTrace_546538
  have hstable : (prefixWord ++ tailWord_546538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546538).length < 2 ^ (prefixWord ++ tailWord_546538).sum := by decide
  have hdescent : baseEnd_546538 < baseStart_546538 := by decide
  rcases family_descends (prefixWord ++ tailWord_546538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546688 : List Nat := [2, 1, 1, 2, 1, 2, 4, 2, 4, 3]
def baseStart_546688 : Nat := 118140960795 + 546688 * 2 ^ 59
def prefixEnd_546688 : Nat := 4983230072969 + 3 ^ 40 * 546688 * 2
def baseEnd_546688 : Nat := 187142474696841542923889

theorem tailTrace_546688 : CollatzResearch.WordTrace tailWord_546688 prefixEnd_546688 187142474696841542923889 := by
  unfold tailWord_546688
  simp only [CollatzResearch.WordTrace]
  refine ⟨9969674721725108861096359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13292899628966811814795145 9969674721725108861096359)
  ·
    refine ⟨14954512082587663291644539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9969674721725108861096359 14954512082587663291644539)
    ·
      refine ⟨22431768123881494937466809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14954512082587663291644539 22431768123881494937466809)
      ·
        refine ⟨16823826092911121203100107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22431768123881494937466809 16823826092911121203100107)
        ·
          refine ⟨25235739139366681804650161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16823826092911121203100107 25235739139366681804650161)
          ·
            refine ⟨18926804354525011353487621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25235739139366681804650161 18926804354525011353487621)
            ·
              refine ⟨3548775816473439628778929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18926804354525011353487621 3548775816473439628778929)
              ·
                refine ⟨2661581862355079721584197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3548775816473439628778929 2661581862355079721584197)
                ·
                  refine ⟨499046599191577447797037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2661581862355079721584197 499046599191577447797037)
                  ·
                    refine ⟨187142474696841542923889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 499046599191577447797037 187142474696841542923889)
                    ·
                      rfl

theorem cell22_546688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 2, 4, 3].length) (baseStart_546688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_546688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_546688 prefixEnd_546688 := by exact prefixLift 546688
  have htrace : WordTrace (prefixWord ++ tailWord_546688) baseStart_546688 baseEnd_546688 := by
    simpa [prefixWord, tailWord_546688, baseEnd_546688] using wordTrace_append hprefix tailTrace_546688
  have hstable : (prefixWord ++ tailWord_546688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546688).length < 2 ^ (prefixWord ++ tailWord_546688).sum := by decide
  have hdescent : baseEnd_546688 < baseStart_546688 := by decide
  rcases family_descends (prefixWord ++ tailWord_546688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546705 : List Nat := [1, 2, 2, 1, 1, 1, 7, 2, 2, 3]
def baseStart_546705 : Nat := 118140960795 + 546705 * 2 ^ 59
def prefixEnd_546705 : Nat := 4983230072969 + 3 ^ 40 * 546705 * 2
def baseEnd_546705 : Nat := 187148294144259165248837

theorem tailTrace_546705 : CollatzResearch.WordTrace tailWord_546705 prefixEnd_546705 187148294144259165248837 := by
  unfold tailWord_546705
  simp only [CollatzResearch.WordTrace]
  refine ⟨19939969484388629625561569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13293312989592419750374379 19939969484388629625561569)
  ·
    refine ⟨14954977113291472219171177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19939969484388629625561569 14954977113291472219171177)
    ·
      refine ⟨11216232834968604164378383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14954977113291472219171177 11216232834968604164378383)
      ·
        refine ⟨16824349252452906246567575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11216232834968604164378383 16824349252452906246567575)
        ·
          refine ⟨25236523878679359369851363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16824349252452906246567575 25236523878679359369851363)
          ·
            refine ⟨37854785818019039054777045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25236523878679359369851363 37854785818019039054777045)
            ·
              refine ⟨887221542609821227846337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 37854785818019039054777045 887221542609821227846337)
              ·
                refine ⟨665416156957365920884753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 887221542609821227846337 665416156957365920884753)
                ·
                  refine ⟨499062117718024440663565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 665416156957365920884753 499062117718024440663565)
                  ·
                    refine ⟨187148294144259165248837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 499062117718024440663565 187148294144259165248837)
                    ·
                      rfl

theorem cell22_546705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 7, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 7, 2, 2, 3].length) (baseStart_546705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_546705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_546705 prefixEnd_546705 := by exact prefixLift 546705
  have htrace : WordTrace (prefixWord ++ tailWord_546705) baseStart_546705 baseEnd_546705 := by
    simpa [prefixWord, tailWord_546705, baseEnd_546705] using wordTrace_append hprefix tailTrace_546705
  have hstable : (prefixWord ++ tailWord_546705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546705).length < 2 ^ (prefixWord ++ tailWord_546705).sum := by decide
  have hdescent : baseEnd_546705 < baseStart_546705 := by decide
  rcases family_descends (prefixWord ++ tailWord_546705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546722 : List Nat := [3, 3, 1, 2, 3, 2, 1, 1, 1, 5]
def baseStart_546722 : Nat := 118140960795 + 546722 * 2 ^ 59
def prefixEnd_546722 : Nat := 4983230072969 + 3 ^ 40 * 546722 * 2
def baseEnd_546722 : Nat := 187154113591676787573785

theorem tailTrace_546722 : CollatzResearch.WordTrace tailWord_546722 prefixEnd_546722 187154113591676787573785 := by
  unfold tailWord_546722
  simp only [CollatzResearch.WordTrace]
  refine ⟨4985147381331760382232605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13293726350218027685953613 4985147381331760382232605)
  ·
    refine ⟨1869430267999410143337227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4985147381331760382232605 1869430267999410143337227)
    ·
      refine ⟨2804145401999115215005841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1869430267999410143337227 2804145401999115215005841)
      ·
        refine ⟨2103109051499336411254381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2804145401999115215005841 2103109051499336411254381)
        ·
          refine ⟨788665894312251154220393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2103109051499336411254381 788665894312251154220393)
          ·
            refine ⟨591499420734188365665295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 788665894312251154220393 591499420734188365665295)
            ·
              refine ⟨887249131101282548497943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 591499420734188365665295 887249131101282548497943)
              ·
                refine ⟨1330873696651923822746915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 887249131101282548497943 1330873696651923822746915)
                ·
                  refine ⟨1996310544977885734120373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1330873696651923822746915 1996310544977885734120373)
                  ·
                    refine ⟨187154113591676787573785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1996310544977885734120373 187154113591676787573785)
                    ·
                      rfl

theorem cell22_546722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 1, 1, 1, 5].length) (baseStart_546722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_546722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_546722 prefixEnd_546722 := by exact prefixLift 546722
  have htrace : WordTrace (prefixWord ++ tailWord_546722) baseStart_546722 baseEnd_546722 := by
    simpa [prefixWord, tailWord_546722, baseEnd_546722] using wordTrace_append hprefix tailTrace_546722
  have hstable : (prefixWord ++ tailWord_546722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546722).length < 2 ^ (prefixWord ++ tailWord_546722).sum := by decide
  have hdescent : baseEnd_546722 < baseStart_546722 := by decide
  rcases family_descends (prefixWord ++ tailWord_546722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546763 : List Nat := [1, 1, 1, 1, 3, 4, 2, 4, 5]
def baseStart_546763 : Nat := 118140960795 + 546763 * 2 ^ 59
def prefixEnd_546763 : Nat := 4983230072969 + 3 ^ 40 * 546763 * 2
def baseEnd_546763 : Nat := 62389382909855449099553

theorem tailTrace_546763 : CollatzResearch.WordTrace tailWord_546763 prefixEnd_546763 62389382909855449099553 := by
  unfold tailWord_546763
  simp only [CollatzResearch.WordTrace]
  refine ⟨19942084918178505531172943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13294723278785670354115295 19942084918178505531172943)
  ·
    refine ⟨29913127377267758296759415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19942084918178505531172943 29913127377267758296759415)
    ·
      refine ⟨44869691065901637445139123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29913127377267758296759415 44869691065901637445139123)
      ·
        refine ⟨67304536598852456167708685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44869691065901637445139123 67304536598852456167708685)
        ·
          refine ⟨25239201224569671062890757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67304536598852456167708685 25239201224569671062890757)
          ·
            refine ⟨4732350229606813324292017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25239201224569671062890757 4732350229606813324292017)
            ·
              refine ⟨3549262672205109993219013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4732350229606813324292017 3549262672205109993219013)
              ·
                refine ⟨665486751038458123728565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3549262672205109993219013 665486751038458123728565)
                ·
                  refine ⟨62389382909855449099553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 665486751038458123728565 62389382909855449099553)
                  ·
                    rfl

theorem cell22_546763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 4, 5].length) (baseStart_546763 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_546763 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_546763 prefixEnd_546763 := by exact prefixLift 546763
  have htrace : WordTrace (prefixWord ++ tailWord_546763) baseStart_546763 baseEnd_546763 := by
    simpa [prefixWord, tailWord_546763, baseEnd_546763] using wordTrace_append hprefix tailTrace_546763
  have hstable : (prefixWord ++ tailWord_546763).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546763).length < 2 ^ (prefixWord ++ tailWord_546763).sum := by decide
  have hdescent : baseEnd_546763 < baseStart_546763 := by decide
  rcases family_descends (prefixWord ++ tailWord_546763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546840 : List Nat := [2, 1, 2, 3, 2, 1, 4, 1, 1, 5]
def baseStart_546840 : Nat := 118140960795 + 546840 * 2 ^ 59
def prefixEnd_546840 : Nat := 4983230072969 + 3 ^ 40 * 546840 * 2
def baseEnd_546840 : Nat := 187194507403163813123423

theorem tailTrace_546840 : CollatzResearch.WordTrace tailWord_546840 prefixEnd_546840 187194507403163813123423 := by
  unfold tailWord_546840
  simp only [CollatzResearch.WordTrace]
  refine ⟨9972446669449773840862987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13296595559266365121150649 9972446669449773840862987)
  ·
    refine ⟨14958670004174660761294481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9972446669449773840862987 14958670004174660761294481)
    ·
      refine ⟨11219002503130995570970861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14958670004174660761294481 11219002503130995570970861)
      ·
        refine ⟨4207125938674123339114073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11219002503130995570970861 4207125938674123339114073)
        ·
          refine ⟨3155344454005592504335555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4207125938674123339114073 3155344454005592504335555)
          ·
            refine ⟨4733016681008388756503333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3155344454005592504335555 4733016681008388756503333)
            ·
              refine ⟨887440627689072891844375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4733016681008388756503333 887440627689072891844375)
              ·
                refine ⟨1331160941533609337766563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 887440627689072891844375 1331160941533609337766563)
                ·
                  refine ⟨1996741412300414006649845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1331160941533609337766563 1996741412300414006649845)
                  ·
                    refine ⟨187194507403163813123423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1996741412300414006649845 187194507403163813123423)
                    ·
                      rfl

theorem cell22_546840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 4, 1, 1, 5].length) (baseStart_546840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_546840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_546840 prefixEnd_546840 := by exact prefixLift 546840
  have htrace : WordTrace (prefixWord ++ tailWord_546840) baseStart_546840 baseEnd_546840 := by
    simpa [prefixWord, tailWord_546840, baseEnd_546840] using wordTrace_append hprefix tailTrace_546840
  have hstable : (prefixWord ++ tailWord_546840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546840).length < 2 ^ (prefixWord ++ tailWord_546840).sum := by decide
  have hdescent : baseEnd_546840 < baseStart_546840 := by decide
  rcases family_descends (prefixWord ++ tailWord_546840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546870 : List Nat := [5, 1, 2, 1, 1, 1, 11]
def baseStart_546870 : Nat := 118140960795 + 546870 * 2 ^ 59
def prefixEnd_546870 : Nat := 4983230072969 + 3 ^ 40 * 546870 * 2
def baseEnd_546870 : Nat := 6933510259861249439753

theorem tailTrace_546870 : CollatzResearch.WordTrace tailWord_546870 prefixEnd_546870 6933510259861249439753 := by
  unfold tailWord_546870
  simp only [CollatzResearch.WordTrace]
  refine ⟨1246624220549428925332379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13297325019193908536878709 1246624220549428925332379)
  ·
    refine ⟨1869936330824143387998569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1246624220549428925332379 1869936330824143387998569)
    ·
      refine ⟨1402452248118107540998927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1869936330824143387998569 1402452248118107540998927)
      ·
        refine ⟨2103678372177161311498391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1402452248118107540998927 2103678372177161311498391)
        ·
          refine ⟨3155517558265741967247587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2103678372177161311498391 3155517558265741967247587)
          ·
            refine ⟨4733276337398612950871381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3155517558265741967247587 4733276337398612950871381)
            ·
              refine ⟨6933510259861249439753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 4733276337398612950871381 6933510259861249439753)
              ·
                rfl

theorem cell22_546870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 11].length) (baseStart_546870 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_546870 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_546870 prefixEnd_546870 := by exact prefixLift 546870
  have htrace : WordTrace (prefixWord ++ tailWord_546870) baseStart_546870 baseEnd_546870 := by
    simpa [prefixWord, tailWord_546870, baseEnd_546870] using wordTrace_append hprefix tailTrace_546870
  have hstable : (prefixWord ++ tailWord_546870).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546870).length < 2 ^ (prefixWord ++ tailWord_546870).sum := by decide
  have hdescent : baseEnd_546870 < baseStart_546870 := by decide
  rcases family_descends (prefixWord ++ tailWord_546870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546883 : List Nat := [1, 1, 1, 3, 1, 2, 2, 3, 2, 6]
def baseStart_546883 : Nat := 118140960795 + 546883 * 2 ^ 59
def prefixEnd_546883 : Nat := 4983230072969 + 3 ^ 40 * 546883 * 2
def baseEnd_546883 : Nat := 187209227181926034298291

theorem tailTrace_546883 : CollatzResearch.WordTrace tailWord_546883 prefixEnd_546883 187209227181926034298291 := by
  unfold tailWord_546883
  simp only [CollatzResearch.WordTrace]
  refine ⟨19946461677743766025541303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13297641118495844017027535 19946461677743766025541303)
  ·
    refine ⟨29919692516615649038311955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19946461677743766025541303 29919692516615649038311955)
    ·
      refine ⟨44879538774923473557467933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29919692516615649038311955 44879538774923473557467933)
      ·
        refine ⟨16829827040596302584050475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44879538774923473557467933 16829827040596302584050475)
        ·
          refine ⟨25244740560894453876075713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16829827040596302584050475 25244740560894453876075713)
          ·
            refine ⟨18933555420670840407056785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25244740560894453876075713 18933555420670840407056785)
            ·
              refine ⟨14200166565503130305292589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18933555420670840407056785 14200166565503130305292589)
              ·
                refine ⟨5325062462063673864484721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14200166565503130305292589 5325062462063673864484721)
                ·
                  refine ⟨3993796846547755398363541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5325062462063673864484721 3993796846547755398363541)
                  ·
                    refine ⟨187209227181926034298291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3993796846547755398363541 187209227181926034298291)
                    ·
                      rfl

theorem cell22_546883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 3, 2, 6].length) (baseStart_546883 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_546883 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_546883 prefixEnd_546883 := by exact prefixLift 546883
  have htrace : WordTrace (prefixWord ++ tailWord_546883) baseStart_546883 baseEnd_546883 := by
    simpa [prefixWord, tailWord_546883, baseEnd_546883] using wordTrace_append hprefix tailTrace_546883
  have hstable : (prefixWord ++ tailWord_546883).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546883).length < 2 ^ (prefixWord ++ tailWord_546883).sum := by decide
  have hdescent : baseEnd_546883 < baseStart_546883 := by decide
  rcases family_descends (prefixWord ++ tailWord_546883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546910 : List Nat := [4, 4, 1, 1, 3, 1, 1, 3, 4]
def baseStart_546910 : Nat := 118140960795 + 546910 * 2 ^ 59
def prefixEnd_546910 : Nat := 4983230072969 + 3 ^ 40 * 546910 * 2
def baseEnd_546910 : Nat := 62406156611235654624403

theorem tailTrace_546910 : CollatzResearch.WordTrace tailWord_546910 prefixEnd_546910 62406156611235654624403 := by
  unfold tailWord_546910
  simp only [CollatzResearch.WordTrace]
  refine ⟨2493430806080743704596773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13298297632430633091182789 2493430806080743704596773)
  ·
    refine ⟨467518276140139444611895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2493430806080743704596773 467518276140139444611895)
    ·
      refine ⟨701277414210209166917843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 467518276140139444611895 701277414210209166917843)
      ·
        refine ⟨1051916121315313750376765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 701277414210209166917843 1051916121315313750376765)
        ·
          refine ⟨394468545493242656391287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1051916121315313750376765 394468545493242656391287)
          ·
            refine ⟨591702818239863984586931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 394468545493242656391287 591702818239863984586931)
            ·
              refine ⟨887554227359795976880397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 591702818239863984586931 887554227359795976880397)
              ·
                refine ⟨332832835259923491330149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 887554227359795976880397 332832835259923491330149)
                ·
                  refine ⟨62406156611235654624403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 332832835259923491330149 62406156611235654624403)
                  ·
                    rfl

theorem cell22_546910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_546910 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_546910 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_546910 prefixEnd_546910 := by exact prefixLift 546910
  have htrace : WordTrace (prefixWord ++ tailWord_546910) baseStart_546910 baseEnd_546910 := by
    simpa [prefixWord, tailWord_546910, baseEnd_546910] using wordTrace_append hprefix tailTrace_546910
  have hstable : (prefixWord ++ tailWord_546910).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546910).length < 2 ^ (prefixWord ++ tailWord_546910).sum := by decide
  have hdescent : baseEnd_546910 < baseStart_546910 := by decide
  rcases family_descends (prefixWord ++ tailWord_546910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546949 : List Nat := [1, 3, 1, 1, 5, 3, 2, 1, 5]
def baseStart_546949 : Nat := 118140960795 + 546949 * 2 ^ 59
def prefixEnd_546949 : Nat := 4983230072969 + 3 ^ 40 * 546949 * 2
def baseEnd_546949 : Nat := 62410606776907954049363

theorem tailTrace_546949 : CollatzResearch.WordTrace tailWord_546949 prefixEnd_546949 62410606776907954049363 := by
  unfold tailWord_546949
  simp only [CollatzResearch.WordTrace]
  refine ⟨19948868895504659297443901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13299245930336439531629267 19948868895504659297443901)
  ·
    refine ⟨7480825835814247236541463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19948868895504659297443901 7480825835814247236541463)
    ·
      refine ⟨11221238753721370854812195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7480825835814247236541463 11221238753721370854812195)
      ·
        refine ⟨16831858130582056282218293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11221238753721370854812195 16831858130582056282218293)
        ·
          refine ⟨1577986699742067776457965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16831858130582056282218293 1577986699742067776457965)
          ·
            refine ⟨591745012403275416171737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1577986699742067776457965 591745012403275416171737)
            ·
              refine ⟨443808759302456562128803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 591745012403275416171737 443808759302456562128803)
              ·
                refine ⟨665713138953684843193205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 443808759302456562128803 665713138953684843193205)
                ·
                  refine ⟨62410606776907954049363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 665713138953684843193205 62410606776907954049363)
                  ·
                    rfl

theorem cell22_546949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 2, 1, 5].length) (baseStart_546949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_546949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_546949 prefixEnd_546949 := by exact prefixLift 546949
  have htrace : WordTrace (prefixWord ++ tailWord_546949) baseStart_546949 baseEnd_546949 := by
    simpa [prefixWord, tailWord_546949, baseEnd_546949] using wordTrace_append hprefix tailTrace_546949
  have hstable : (prefixWord ++ tailWord_546949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546949).length < 2 ^ (prefixWord ++ tailWord_546949).sum := by decide
  have hdescent : baseEnd_546949 < baseStart_546949 := by decide
  rcases family_descends (prefixWord ++ tailWord_546949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546962 : List Nat := [3, 2, 3, 1, 1, 1, 3, 1, 3, 4]
def baseStart_546962 : Nat := 118140960795 + 546962 * 2 ^ 59
def prefixEnd_546962 : Nat := 4983230072969 + 3 ^ 40 * 546962 * 2
def baseEnd_546962 : Nat := 187236270496396161573049

theorem tailTrace_546962 : CollatzResearch.WordTrace tailWord_546962 prefixEnd_546962 187236270496396161573049 := by
  unfold tailWord_546962
  simp only [CollatzResearch.WordTrace]
  refine ⟨4987335761114390629416785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13299562029638375011778093 4987335761114390629416785)
  ·
    refine ⟨3740501820835792972062589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4987335761114390629416785 3740501820835792972062589)
    ·
      refine ⟨1402688182813422364523471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3740501820835792972062589 1402688182813422364523471)
      ·
        refine ⟨2104032274220133546785207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1402688182813422364523471 2104032274220133546785207)
        ·
          refine ⟨3156048411330200320177811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2104032274220133546785207 3156048411330200320177811)
          ·
            refine ⟨4734072616995300480266717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3156048411330200320177811 4734072616995300480266717)
            ·
              refine ⟨1775277231373237680100019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4734072616995300480266717 1775277231373237680100019)
              ·
                refine ⟨2662915847059856520150029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1775277231373237680100019 2662915847059856520150029)
                ·
                  refine ⟨998593442647446195056261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2662915847059856520150029 998593442647446195056261)
                  ·
                    refine ⟨187236270496396161573049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 998593442647446195056261 187236270496396161573049)
                    ·
                      rfl

theorem cell22_546962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_546962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_546962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_546962 prefixEnd_546962 := by exact prefixLift 546962
  have htrace : WordTrace (prefixWord ++ tailWord_546962) baseStart_546962 baseEnd_546962 := by
    simpa [prefixWord, tailWord_546962, baseEnd_546962] using wordTrace_append hprefix tailTrace_546962
  have hstable : (prefixWord ++ tailWord_546962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546962).length < 2 ^ (prefixWord ++ tailWord_546962).sum := by decide
  have hdescent : baseEnd_546962 < baseStart_546962 := by decide
  rcases family_descends (prefixWord ++ tailWord_546962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547043 : List Nat := [1, 1, 1, 8, 1, 2, 1, 2, 2, 3]
def baseStart_547043 : Nat := 118140960795 + 547043 * 2 ^ 59
def prefixEnd_547043 : Nat := 4983230072969 + 3 ^ 40 * 547043 * 2
def baseEnd_547043 : Nat := 187263998451738950297801

theorem tailTrace_547043 : CollatzResearch.WordTrace tailWord_547043 prefixEnd_547043 187263998451738950297801 := by
  unfold tailWord_547043
  simp only [CollatzResearch.WordTrace]
  refine ⟨19952297357164113351365783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13301531571442742234243855 19952297357164113351365783)
  ·
    refine ⟨29928446035746170027048675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19952297357164113351365783 29928446035746170027048675)
    ·
      refine ⟨44892669053619255040573013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29928446035746170027048675 44892669053619255040573013)
      ·
        refine ⟨526085965472100645006715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 44892669053619255040573013 526085965472100645006715)
        ·
          refine ⟨789128948208150967510073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 526085965472100645006715 789128948208150967510073)
          ·
            refine ⟨591846711156113225632555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 789128948208150967510073 591846711156113225632555)
            ·
              refine ⟨887770066734169838448833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 591846711156113225632555 887770066734169838448833)
              ·
                refine ⟨665827550050627378836625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 887770066734169838448833 665827550050627378836625)
                ·
                  refine ⟨499370662537970534127469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 665827550050627378836625 499370662537970534127469)
                  ·
                    refine ⟨187263998451738950297801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 499370662537970534127469 187263998451738950297801)
                    ·
                      rfl

theorem cell22_547043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 1, 2, 2, 3].length) (baseStart_547043 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_547043 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_547043 prefixEnd_547043 := by exact prefixLift 547043
  have htrace : WordTrace (prefixWord ++ tailWord_547043) baseStart_547043 baseEnd_547043 := by
    simpa [prefixWord, tailWord_547043, baseEnd_547043] using wordTrace_append hprefix tailTrace_547043
  have hstable : (prefixWord ++ tailWord_547043).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547043).length < 2 ^ (prefixWord ++ tailWord_547043).sum := by decide
  have hdescent : baseEnd_547043 < baseStart_547043 := by decide
  rcases family_descends (prefixWord ++ tailWord_547043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547065 : List Nat := [1, 2, 1, 3, 1, 1, 2, 3, 1, 7]
def baseStart_547065 : Nat := 118140960795 + 547065 * 2 ^ 59
def prefixEnd_547065 : Nat := 4983230072969 + 3 ^ 40 * 547065 * 2
def baseEnd_547065 : Nat := 187271529501338226247733

theorem tailTrace_547065 : CollatzResearch.WordTrace tailWord_547065 prefixEnd_547065 187271529501338226247733 := by
  unfold tailWord_547065
  simp only [CollatzResearch.WordTrace]
  refine ⟨19953099763084411108666649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13302066508722940739111099 19953099763084411108666649)
  ·
    refine ⟨14964824822313308331499987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19953099763084411108666649 14964824822313308331499987)
    ·
      refine ⟨22447237233469962497249981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14964824822313308331499987 22447237233469962497249981)
      ·
        refine ⟨8417713962551235936468743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22447237233469962497249981 8417713962551235936468743)
        ·
          refine ⟨12626570943826853904703115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8417713962551235936468743 12626570943826853904703115)
          ·
            refine ⟨18939856415740280857054673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12626570943826853904703115 18939856415740280857054673)
            ·
              refine ⟨14204892311805210642791005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18939856415740280857054673 14204892311805210642791005)
              ·
                refine ⟨5326834616926953991046627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14204892311805210642791005 5326834616926953991046627)
                ·
                  refine ⟨7990251925390430986569941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5326834616926953991046627 7990251925390430986569941)
                  ·
                    refine ⟨187271529501338226247733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7990251925390430986569941 187271529501338226247733)
                    ·
                      rfl

theorem cell22_547065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 3, 1, 7].length) (baseStart_547065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_547065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_547065 prefixEnd_547065 := by exact prefixLift 547065
  have htrace : WordTrace (prefixWord ++ tailWord_547065) baseStart_547065 baseEnd_547065 := by
    simpa [prefixWord, tailWord_547065, baseEnd_547065] using wordTrace_append hprefix tailTrace_547065
  have hstable : (prefixWord ++ tailWord_547065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547065).length < 2 ^ (prefixWord ++ tailWord_547065).sum := by decide
  have hdescent : baseEnd_547065 < baseStart_547065 := by decide
  rcases family_descends (prefixWord ++ tailWord_547065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547157 : List Nat := [1, 3, 2, 2, 4, 10]
def baseStart_547157 : Nat := 118140960795 + 547157 * 2 ^ 59
def prefixEnd_547157 : Nat := 4983230072969 + 3 ^ 40 * 547157 * 2
def baseEnd_547157 : Nat := 2312382999771366085771

theorem tailTrace_547157 : CollatzResearch.WordTrace tailWord_547157 prefixEnd_547157 2312382999771366085771 := by
  unfold tailWord_547157
  simp only [CollatzResearch.WordTrace]
  refine ⟨19956455278751110821015725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13304303519167407214010483 19956455278751110821015725)
  ·
    refine ⟨7483670729531666557880897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19956455278751110821015725 7483670729531666557880897)
    ·
      refine ⟨5612753047148749918410673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7483670729531666557880897 5612753047148749918410673)
      ·
        refine ⟨4209564785361562438808005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5612753047148749918410673 4209564785361562438808005)
        ·
          refine ⟨789293397255292957276501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4209564785361562438808005 789293397255292957276501)
          ·
            refine ⟨2312382999771366085771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 789293397255292957276501 2312382999771366085771)
            ·
              rfl

theorem cell22_547157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 10].length) (baseStart_547157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_547157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_547157 prefixEnd_547157 := by exact prefixLift 547157
  have htrace : WordTrace (prefixWord ++ tailWord_547157) baseStart_547157 baseEnd_547157 := by
    simpa [prefixWord, tailWord_547157, baseEnd_547157] using wordTrace_append hprefix tailTrace_547157
  have hstable : (prefixWord ++ tailWord_547157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547157).length < 2 ^ (prefixWord ++ tailWord_547157).sum := by decide
  have hdescent : baseEnd_547157 < baseStart_547157 := by decide
  rcases family_descends (prefixWord ++ tailWord_547157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547234 : List Nat := [3, 3, 1, 2, 1, 1, 1, 3, 2, 5]
def baseStart_547234 : Nat := 118140960795 + 547234 * 2 ^ 59
def prefixEnd_547234 : Nat := 4983230072969 + 3 ^ 40 * 547234 * 2
def baseEnd_547234 : Nat := 187329381655078118772215

theorem tailTrace_547234 : CollatzResearch.WordTrace tailWord_547234 prefixEnd_547234 187329381655078118772215 := by
  unfold tailWord_547234
  simp only [CollatzResearch.WordTrace]
  refine ⟨4989815924868038242892189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13306175799648101981045837 4989815924868038242892189)
  ·
    refine ⟨1871180971825514341084571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4989815924868038242892189 1871180971825514341084571)
    ·
      refine ⟨2806771457738271511626857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1871180971825514341084571 2806771457738271511626857)
      ·
        refine ⟨2105078593303703633720143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2806771457738271511626857 2105078593303703633720143)
        ·
          refine ⟨3157617889955555450580215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2105078593303703633720143 3157617889955555450580215)
          ·
            refine ⟨4736426834933333175870323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3157617889955555450580215 4736426834933333175870323)
            ·
              refine ⟨7104640252399999763805485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4736426834933333175870323 7104640252399999763805485)
              ·
                refine ⟨2664240094649999911427057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7104640252399999763805485 2664240094649999911427057)
                ·
                  refine ⟨1998180070987499933570293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2664240094649999911427057 1998180070987499933570293)
                  ·
                    refine ⟨187329381655078118772215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1998180070987499933570293 187329381655078118772215)
                    ·
                      rfl

theorem cell22_547234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 3, 2, 5].length) (baseStart_547234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_547234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_547234 prefixEnd_547234 := by exact prefixLift 547234
  have htrace : WordTrace (prefixWord ++ tailWord_547234) baseStart_547234 baseEnd_547234 := by
    simpa [prefixWord, tailWord_547234, baseEnd_547234] using wordTrace_append hprefix tailTrace_547234
  have hstable : (prefixWord ++ tailWord_547234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547234).length < 2 ^ (prefixWord ++ tailWord_547234).sum := by decide
  have hdescent : baseEnd_547234 < baseStart_547234 := by decide
  rcases family_descends (prefixWord ++ tailWord_547234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547242 : List Nat := [3, 1, 6, 1, 2, 1, 2, 6]
def baseStart_547242 : Nat := 118140960795 + 547242 * 2 ^ 59
def prefixEnd_547242 : Nat := 4983230072969 + 3 ^ 40 * 547242 * 2
def baseEnd_547242 : Nat := 20814680024285418285799

theorem tailTrace_547242 : CollatzResearch.WordTrace tailWord_547242 prefixEnd_547242 20814680024285418285799 := by
  unfold tailWord_547242
  simp only [CollatzResearch.WordTrace]
  refine ⟨4989888870860792584464995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13306370322295446891906653 4989888870860792584464995)
  ·
    refine ⟨7484833306291188876697493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4989888870860792584464995 7484833306291188876697493)
    ·
      refine ⟨350851561232399478595195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 7484833306291188876697493 350851561232399478595195)
      ·
        refine ⟨526277341848599217892793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 350851561232399478595195 526277341848599217892793)
        ·
          refine ⟨394708006386449413419595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 526277341848599217892793 394708006386449413419595)
          ·
            refine ⟨592062009579674120129393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 394708006386449413419595 592062009579674120129393)
            ·
              refine ⟨444046507184755590097045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 592062009579674120129393 444046507184755590097045)
              ·
                refine ⟨20814680024285418285799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 444046507184755590097045 20814680024285418285799)
                ·
                  rfl

theorem cell22_547242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 2, 6].length) (baseStart_547242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_547242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_547242 prefixEnd_547242 := by exact prefixLift 547242
  have htrace : WordTrace (prefixWord ++ tailWord_547242) baseStart_547242 baseEnd_547242 := by
    simpa [prefixWord, tailWord_547242, baseEnd_547242] using wordTrace_append hprefix tailTrace_547242
  have hstable : (prefixWord ++ tailWord_547242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547242).length < 2 ^ (prefixWord ++ tailWord_547242).sum := by decide
  have hdescent : baseEnd_547242 < baseStart_547242 := by decide
  rcases family_descends (prefixWord ++ tailWord_547242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547296 : List Nat := [2, 1, 1, 3, 1, 1, 5, 3, 2, 3]
def baseStart_547296 : Nat := 118140960795 + 547296 * 2 ^ 59
def prefixEnd_547296 : Nat := 4983230072969 + 3 ^ 40 * 547296 * 2
def baseEnd_547296 : Nat := 187350605522130623722025

theorem tailTrace_547296 : CollatzResearch.WordTrace tailWord_547296 prefixEnd_547296 187350605522130623722025 := by
  unfold tailWord_547296
  simp only [CollatzResearch.WordTrace]
  refine ⟨9980762512623768780162871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13307683350165025040217161 9980762512623768780162871)
  ·
    refine ⟨14971143768935653170244307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9980762512623768780162871 14971143768935653170244307)
    ·
      refine ⟨22456715653403479755366461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14971143768935653170244307 22456715653403479755366461)
      ·
        refine ⟨8421268370026304908262423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22456715653403479755366461 8421268370026304908262423)
        ·
          refine ⟨12631902555039457362393635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8421268370026304908262423 12631902555039457362393635)
          ·
            refine ⟨18947853832559186043590453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12631902555039457362393635 18947853832559186043590453)
            ·
              refine ⟨1776361296802423691586605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18947853832559186043590453 1776361296802423691586605)
              ·
                refine ⟨666135486300908884344977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1776361296802423691586605 666135486300908884344977)
                ·
                  refine ⟨499601614725681663258733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 666135486300908884344977 499601614725681663258733)
                  ·
                    refine ⟨187350605522130623722025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 499601614725681663258733 187350605522130623722025)
                    ·
                      rfl

theorem cell22_547296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 3, 2, 3].length) (baseStart_547296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_547296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_547296 prefixEnd_547296 := by exact prefixLift 547296
  have htrace : WordTrace (prefixWord ++ tailWord_547296) baseStart_547296 baseEnd_547296 := by
    simpa [prefixWord, tailWord_547296, baseEnd_547296] using wordTrace_append hprefix tailTrace_547296
  have hstable : (prefixWord ++ tailWord_547296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547296).length < 2 ^ (prefixWord ++ tailWord_547296).sum := by decide
  have hdescent : baseEnd_547296 < baseStart_547296 := by decide
  rcases family_descends (prefixWord ++ tailWord_547296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547339 : List Nat := [1, 1, 1, 1, 7, 1, 1, 1, 2, 6]
def baseStart_547339 : Nat := 118140960795 + 547339 * 2 ^ 59
def prefixEnd_547339 : Nat := 4983230072969 + 3 ^ 40 * 547339 * 2
def baseEnd_547339 : Nat := 187365325300892844896893

theorem tailTrace_547339 : CollatzResearch.WordTrace tailWord_547339 prefixEnd_547339 187365325300892844896893 := by
  unfold tailWord_547339
  simp only [CollatzResearch.WordTrace]
  refine ⟨19963093364091755904141071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13308728909394503936094047 19963093364091755904141071)
  ·
    refine ⟨29944640046137633856211607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19963093364091755904141071 29944640046137633856211607)
    ·
      refine ⟨44916960069206450784317411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29944640046137633856211607 44916960069206450784317411)
      ·
        refine ⟨67375440103809676176476117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44916960069206450784317411 67375440103809676176476117)
        ·
          refine ⟨1579111877433039285386159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 67375440103809676176476117 1579111877433039285386159)
          ·
            refine ⟨2368667816149558928079239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1579111877433039285386159 2368667816149558928079239)
            ·
              refine ⟨3553001724224338392118859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2368667816149558928079239 3553001724224338392118859)
              ·
                refine ⟨5329502586336507588178289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3553001724224338392118859 5329502586336507588178289)
                ·
                  refine ⟨3997126939752380691133717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5329502586336507588178289 3997126939752380691133717)
                  ·
                    refine ⟨187365325300892844896893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3997126939752380691133717 187365325300892844896893)
                    ·
                      rfl

theorem cell22_547339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 1, 2, 6].length) (baseStart_547339 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_547339 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_547339 prefixEnd_547339 := by exact prefixLift 547339
  have htrace : WordTrace (prefixWord ++ tailWord_547339) baseStart_547339 baseEnd_547339 := by
    simpa [prefixWord, tailWord_547339, baseEnd_547339] using wordTrace_append hprefix tailTrace_547339
  have hstable : (prefixWord ++ tailWord_547339).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547339).length < 2 ^ (prefixWord ++ tailWord_547339).sum := by decide
  have hdescent : baseEnd_547339 < baseStart_547339 := by decide
  rcases family_descends (prefixWord ++ tailWord_547339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547388 : List Nat := [2, 2, 2, 2, 3, 3, 1, 2, 5]
def baseStart_547388 : Nat := 118140960795 + 547388 * 2 ^ 59
def prefixEnd_547388 : Nat := 4983230072969 + 3 ^ 40 * 547388 * 2
def baseEnd_547388 : Nat := 62460699667424350140581

theorem tailTrace_547388 : CollatzResearch.WordTrace tailWord_547388 prefixEnd_547388 62460699667424350140581 := by
  unfold tailWord_547388
  simp only [CollatzResearch.WordTrace]
  refine ⟨9982440270457118636337409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13309920360609491515116545 9982440270457118636337409)
  ·
    refine ⟨7486830202842838977253057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9982440270457118636337409 7486830202842838977253057)
    ·
      refine ⟨5615122652132129232939793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7486830202842838977253057 5615122652132129232939793)
      ·
        refine ⟨4211341989099096924704845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5615122652132129232939793 4211341989099096924704845)
        ·
          refine ⟨1579253245912161346764317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4211341989099096924704845 1579253245912161346764317)
          ·
            refine ⟨592219967217060505036619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1579253245912161346764317 592219967217060505036619)
            ·
              refine ⟨888329950825590757554929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 592219967217060505036619 888329950825590757554929)
              ·
                refine ⟨666247463119193068166197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 888329950825590757554929 666247463119193068166197)
                ·
                  refine ⟨62460699667424350140581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 666247463119193068166197 62460699667424350140581)
                  ·
                    rfl

theorem cell22_547388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 1, 2, 5].length) (baseStart_547388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_547388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_547388 prefixEnd_547388 := by exact prefixLift 547388
  have htrace : WordTrace (prefixWord ++ tailWord_547388) baseStart_547388 baseEnd_547388 := by
    simpa [prefixWord, tailWord_547388, baseEnd_547388] using wordTrace_append hprefix tailTrace_547388
  have hstable : (prefixWord ++ tailWord_547388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547388).length < 2 ^ (prefixWord ++ tailWord_547388).sum := by decide
  have hdescent : baseEnd_547388 < baseStart_547388 := by decide
  rcases family_descends (prefixWord ++ tailWord_547388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547405 : List Nat := [1, 6, 1, 1, 2, 2, 3, 1, 5]
def baseStart_547405 : Nat := 118140960795 + 547405 * 2 ^ 59
def prefixEnd_547405 : Nat := 4983230072969 + 3 ^ 40 * 547405 * 2
def baseEnd_547405 : Nat := 62462639483230224248897

theorem tailTrace_547405 : CollatzResearch.WordTrace tailWord_547405 prefixEnd_547405 62462639483230224248897 := by
  unfold tailWord_547405
  simp only [CollatzResearch.WordTrace]
  refine ⟨19965500581852649176043669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13310333721235099450695779 19965500581852649176043669)
  ·
    refine ⟨935882839774342930127047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 19965500581852649176043669 935882839774342930127047)
    ·
      refine ⟨1403824259661514395190571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 935882839774342930127047 1403824259661514395190571)
      ·
        refine ⟨2105736389492271592785857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1403824259661514395190571 2105736389492271592785857)
        ·
          refine ⟨1579302292119203694589393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2105736389492271592785857 1579302292119203694589393)
          ·
            refine ⟨1184476719089402770942045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1579302292119203694589393 1184476719089402770942045)
            ·
              refine ⟨444178769658526039103267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1184476719089402770942045 444178769658526039103267)
              ·
                refine ⟨666268154487789058654901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 444178769658526039103267 666268154487789058654901)
                ·
                  refine ⟨62462639483230224248897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 666268154487789058654901 62462639483230224248897)
                  ·
                    rfl

theorem cell22_547405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 3, 1, 5].length) (baseStart_547405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_547405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_547405 prefixEnd_547405 := by exact prefixLift 547405
  have htrace : WordTrace (prefixWord ++ tailWord_547405) baseStart_547405 baseEnd_547405 := by
    simpa [prefixWord, tailWord_547405, baseEnd_547405] using wordTrace_append hprefix tailTrace_547405
  have hstable : (prefixWord ++ tailWord_547405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547405).length < 2 ^ (prefixWord ++ tailWord_547405).sum := by decide
  have hdescent : baseEnd_547405 < baseStart_547405 := by decide
  rcases family_descends (prefixWord ++ tailWord_547405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547426 : List Nat := [3, 3, 2, 3, 2, 1, 1, 3, 1, 3]
def baseStart_547426 : Nat := 118140960795 + 547426 * 2 ^ 59
def prefixEnd_547426 : Nat := 4983230072969 + 3 ^ 40 * 547426 * 2
def baseEnd_547426 : Nat := 187395107178853617971627

theorem tailTrace_547426 : CollatzResearch.WordTrace tailWord_547426 prefixEnd_547426 187395107178853617971627 := by
  unfold tailWord_547426
  simp only [CollatzResearch.WordTrace]
  refine ⟨4991566628694142440639533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13310844343184379841705421 4991566628694142440639533)
  ·
    refine ⟨1871837485760303415239825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4991566628694142440639533 1871837485760303415239825)
    ·
      refine ⟨1403878114320227561429869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1871837485760303415239825 1403878114320227561429869)
      ·
        refine ⟨526454292870085335536201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1403878114320227561429869 526454292870085335536201)
        ·
          refine ⟨394840719652564001652151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 526454292870085335536201 394840719652564001652151)
          ·
            refine ⟨592261079478846002478227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 394840719652564001652151 592261079478846002478227)
            ·
              refine ⟨888391619218269003717341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 592261079478846002478227 888391619218269003717341)
              ·
                refine ⟨333146857206850876394003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 888391619218269003717341 333146857206850876394003)
                ·
                  refine ⟨499720285810276314591005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 333146857206850876394003 499720285810276314591005)
                  ·
                    refine ⟨187395107178853617971627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 499720285810276314591005 187395107178853617971627)
                    ·
                      rfl

theorem cell22_547426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 1, 3, 1, 3].length) (baseStart_547426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_547426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_547426 prefixEnd_547426 := by exact prefixLift 547426
  have htrace : WordTrace (prefixWord ++ tailWord_547426) baseStart_547426 baseEnd_547426 := by
    simpa [prefixWord, tailWord_547426, baseEnd_547426] using wordTrace_append hprefix tailTrace_547426
  have hstable : (prefixWord ++ tailWord_547426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547426).length < 2 ^ (prefixWord ++ tailWord_547426).sum := by decide
  have hdescent : baseEnd_547426 < baseStart_547426 := by decide
  rcases family_descends (prefixWord ++ tailWord_547426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547461 : List Nat := [1, 3, 1, 1, 4, 3, 2, 7]
def baseStart_547461 : Nat := 118140960795 + 547461 * 2 ^ 59
def prefixEnd_547461 : Nat := 4983230072969 + 3 ^ 40 * 547461 * 2
def baseEnd_547461 : Nat := 20823009821569465927391

theorem tailTrace_547461 : CollatzResearch.WordTrace tailWord_547461 prefixEnd_547461 20823009821569465927391 := by
  unfold tailWord_547461
  simp only [CollatzResearch.WordTrace]
  refine ⟨19967543069649770740082237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13311695379766513826721491 19967543069649770740082237)
  ·
    refine ⟨7487828651118664027530839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19967543069649770740082237 7487828651118664027530839)
    ·
      refine ⟨11231742976677996041296259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7487828651118664027530839 11231742976677996041296259)
      ·
        refine ⟨16847614465016994061944389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11231742976677996041296259 16847614465016994061944389)
        ·
          refine ⟨3158927712190686386614573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16847614465016994061944389 3158927712190686386614573)
          ·
            refine ⟨1184597892071507394980465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3158927712190686386614573 1184597892071507394980465)
            ·
              refine ⟨888448419053630546235349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1184597892071507394980465 888448419053630546235349)
              ·
                refine ⟨20823009821569465927391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 888448419053630546235349 20823009821569465927391)
                ·
                  rfl

theorem cell22_547461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 2, 7].length) (baseStart_547461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_547461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_547461 prefixEnd_547461 := by exact prefixLift 547461
  have htrace : WordTrace (prefixWord ++ tailWord_547461) baseStart_547461 baseEnd_547461 := by
    simpa [prefixWord, tailWord_547461, baseEnd_547461] using wordTrace_append hprefix tailTrace_547461
  have hstable : (prefixWord ++ tailWord_547461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547461).length < 2 ^ (prefixWord ++ tailWord_547461).sum := by decide
  have hdescent : baseEnd_547461 < baseStart_547461 := by decide
  rcases family_descends (prefixWord ++ tailWord_547461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547568 : List Nat := [2, 1, 1, 1, 3, 1, 3, 6, 4]
def baseStart_547568 : Nat := 118140960795 + 547568 * 2 ^ 59
def prefixEnd_547568 : Nat := 4983230072969 + 3 ^ 40 * 547568 * 2
def baseEnd_547568 : Nat := 62481238893604193640397

theorem tailTrace_547568 : CollatzResearch.WordTrace tailWord_547568 prefixEnd_547568 62481238893604193640397 := by
  unfold tailWord_547568
  simp only [CollatzResearch.WordTrace]
  refine ⟨9985722840131064007113679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13314297120174752009484905 9985722840131064007113679)
  ·
    refine ⟨14978584260196596010670519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9985722840131064007113679 14978584260196596010670519)
    ·
      refine ⟨22467876390294894016005779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14978584260196596010670519 22467876390294894016005779)
      ·
        refine ⟨33701814585442341024008669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22467876390294894016005779 33701814585442341024008669)
        ·
          refine ⟨12638180469540877884003251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33701814585442341024008669 12638180469540877884003251)
          ·
            refine ⟨18957270704311316826004877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12638180469540877884003251 18957270704311316826004877)
            ·
              refine ⟨7108976514116743809751829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18957270704311316826004877 7108976514116743809751829)
              ·
                refine ⟨333233274099222366082117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7108976514116743809751829 333233274099222366082117)
                ·
                  refine ⟨62481238893604193640397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 333233274099222366082117 62481238893604193640397)
                  ·
                    rfl

theorem cell22_547568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 6, 4].length) (baseStart_547568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_547568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_547568 prefixEnd_547568 := by exact prefixLift 547568
  have htrace : WordTrace (prefixWord ++ tailWord_547568) baseStart_547568 baseEnd_547568 := by
    simpa [prefixWord, tailWord_547568, baseEnd_547568] using wordTrace_append hprefix tailTrace_547568
  have hstable : (prefixWord ++ tailWord_547568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547568).length < 2 ^ (prefixWord ++ tailWord_547568).sum := by decide
  have hdescent : baseEnd_547568 < baseStart_547568 := by decide
  rcases family_descends (prefixWord ++ tailWord_547568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547581 : List Nat := [1, 4, 1, 1, 1, 1, 3, 1, 3, 6]
def baseStart_547581 : Nat := 118140960795 + 547581 * 2 ^ 59
def prefixEnd_547581 : Nat := 4983230072969 + 3 ^ 40 * 547581 * 2
def baseEnd_547581 : Nat := 187448166846484880346151

theorem tailTrace_547581 : CollatzResearch.WordTrace tailWord_547581 prefixEnd_547581 187448166846484880346151 := by
  unfold tailWord_547581
  simp only [CollatzResearch.WordTrace]
  refine ⟨19971919829215031234450597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13314613219476687489633731 19971919829215031234450597)
  ·
    refine ⟨3744734967977818356459487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19971919829215031234450597 3744734967977818356459487)
    ·
      refine ⟨5617102451966727534689231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3744734967977818356459487 5617102451966727534689231)
      ·
        refine ⟨8425653677950091302033847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5617102451966727534689231 8425653677950091302033847)
        ·
          refine ⟨12638480516925136953050771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8425653677950091302033847 12638480516925136953050771)
          ·
            refine ⟨18957720775387705429576157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12638480516925136953050771 18957720775387705429576157)
            ·
              refine ⟨7109145290770389536091059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18957720775387705429576157 7109145290770389536091059)
              ·
                refine ⟨10663717936155584304136589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7109145290770389536091059 10663717936155584304136589)
                ·
                  refine ⟨3998894226058344114051221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10663717936155584304136589 3998894226058344114051221)
                  ·
                    refine ⟨187448166846484880346151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3998894226058344114051221 187448166846484880346151)
                    ·
                      rfl

theorem cell22_547581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 1, 3, 6].length) (baseStart_547581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_547581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_547581 prefixEnd_547581 := by exact prefixLift 547581
  have htrace : WordTrace (prefixWord ++ tailWord_547581) baseStart_547581 baseEnd_547581 := by
    simpa [prefixWord, tailWord_547581, baseEnd_547581] using wordTrace_append hprefix tailTrace_547581
  have hstable : (prefixWord ++ tailWord_547581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547581).length < 2 ^ (prefixWord ++ tailWord_547581).sum := by decide
  have hdescent : baseEnd_547581 < baseStart_547581 := by decide
  rcases family_descends (prefixWord ++ tailWord_547581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547598 : List Nat := [4, 1, 1, 2, 1, 1, 1, 5, 2, 4]
def baseStart_547598 : Nat := 118140960795 + 547598 * 2 ^ 59
def prefixEnd_547598 : Nat := 4983230072969 + 3 ^ 40 * 547598 * 2
def baseEnd_547598 : Nat := 187453986293902502671099

theorem tailTrace_547598 : CollatzResearch.WordTrace tailWord_547598 prefixEnd_547598 187453986293902502671099 := by
  unfold tailWord_547598
  simp only [CollatzResearch.WordTrace]
  refine ⟨2496567483769180392227431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13315026580102295425212965 2496567483769180392227431)
  ·
    refine ⟨3744851225653770588341147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2496567483769180392227431 3744851225653770588341147)
    ·
      refine ⟨5617276838480655882511721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3744851225653770588341147 5617276838480655882511721)
      ·
        refine ⟨4212957628860491911883791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5617276838480655882511721 4212957628860491911883791)
        ·
          refine ⟨6319436443290737867825687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4212957628860491911883791 6319436443290737867825687)
          ·
            refine ⟨9479154664936106801738531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6319436443290737867825687 9479154664936106801738531)
            ·
              refine ⟨14218731997404160202607797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9479154664936106801738531 14218731997404160202607797)
              ·
                refine ⟨1333006124756640018994481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14218731997404160202607797 1333006124756640018994481)
                ·
                  refine ⟨999754593567480014245861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1333006124756640018994481 999754593567480014245861)
                  ·
                    refine ⟨187453986293902502671099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 999754593567480014245861 187453986293902502671099)
                    ·
                      rfl

theorem cell22_547598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 5, 2, 4].length) (baseStart_547598 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_547598 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_547598 prefixEnd_547598 := by exact prefixLift 547598
  have htrace : WordTrace (prefixWord ++ tailWord_547598) baseStart_547598 baseEnd_547598 := by
    simpa [prefixWord, tailWord_547598, baseEnd_547598] using wordTrace_append hprefix tailTrace_547598
  have hstable : (prefixWord ++ tailWord_547598).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547598).length < 2 ^ (prefixWord ++ tailWord_547598).sum := by decide
  have hdescent : baseEnd_547598 < baseStart_547598 := by decide
  rcases family_descends (prefixWord ++ tailWord_547598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547630 : List Nat := [4, 1, 3, 2, 1, 2, 2, 7]
def baseStart_547630 : Nat := 118140960795 + 547630 * 2 ^ 59
def prefixEnd_547630 : Nat := 4983230072969 + 3 ^ 40 * 547630 * 2
def baseEnd_547630 : Nat := 20829437838651676207889

theorem tailTrace_547630 : CollatzResearch.WordTrace tailWord_547630 prefixEnd_547630 20829437838651676207889 := by
  unfold tailWord_547630
  simp only [CollatzResearch.WordTrace]
  refine ⟨2496713375754689075373043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13315804670691675068656229 2496713375754689075373043)
  ·
    refine ⟨3745070063632033613059565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2496713375754689075373043 3745070063632033613059565)
    ·
      refine ⟨1404401273862012604897337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3745070063632033613059565 1404401273862012604897337)
      ·
        refine ⟨1053300955396509453673003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1404401273862012604897337 1053300955396509453673003)
        ·
          refine ⟨1579951433094764180509505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1053300955396509453673003 1579951433094764180509505)
          ·
            refine ⟨1184963574821073135382129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1579951433094764180509505 1184963574821073135382129)
            ·
              refine ⟨888722681115804851536597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1184963574821073135382129 888722681115804851536597)
              ·
                refine ⟨20829437838651676207889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 888722681115804851536597 20829437838651676207889)
                ·
                  rfl

theorem cell22_547630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 2, 7].length) (baseStart_547630 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_547630 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_547630 prefixEnd_547630 := by exact prefixLift 547630
  have htrace : WordTrace (prefixWord ++ tailWord_547630) baseStart_547630 baseEnd_547630 := by
    simpa [prefixWord, tailWord_547630, baseEnd_547630] using wordTrace_append hprefix tailTrace_547630
  have hstable : (prefixWord ++ tailWord_547630).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547630).length < 2 ^ (prefixWord ++ tailWord_547630).sum := by decide
  have hdescent : baseEnd_547630 < baseStart_547630 := by decide
  rcases family_descends (prefixWord ++ tailWord_547630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547722 : List Nat := [3, 1, 2, 4, 1, 2, 1, 3, 1, 4]
def baseStart_547722 : Nat := 118140960795 + 547722 * 2 ^ 59
def prefixEnd_547722 : Nat := 4983230072969 + 3 ^ 40 * 547722 * 2
def baseEnd_547722 : Nat := 187496434028007512570719

theorem tailTrace_547722 : CollatzResearch.WordTrace tailWord_547722 prefixEnd_547722 187496434028007512570719 := by
  unfold tailWord_547722
  simp only [CollatzResearch.WordTrace]
  refine ⟨4994265630426053078833355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13318041681136141543555613 4994265630426053078833355)
  ·
    refine ⟨7491398445639079618250033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4994265630426053078833355 7491398445639079618250033)
    ·
      refine ⟨5618548834229309713687525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7491398445639079618250033 5618548834229309713687525)
      ·
        refine ⟨1053477906417995571316411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5618548834229309713687525 1053477906417995571316411)
        ·
          refine ⟨1580216859626993356974617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1053477906417995571316411 1580216859626993356974617)
          ·
            refine ⟨1185162644720245017730963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1580216859626993356974617 1185162644720245017730963)
            ·
              refine ⟨1777743967080367526596445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1185162644720245017730963 1777743967080367526596445)
              ·
                refine ⟨666653987655137822473667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1777743967080367526596445 666653987655137822473667)
                ·
                  refine ⟨999980981482706733710501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 666653987655137822473667 999980981482706733710501)
                  ·
                    refine ⟨187496434028007512570719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 999980981482706733710501 187496434028007512570719)
                    ·
                      rfl

theorem cell22_547722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 3, 1, 4].length) (baseStart_547722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_547722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_547722 prefixEnd_547722 := by exact prefixLift 547722
  have htrace : WordTrace (prefixWord ++ tailWord_547722) baseStart_547722 baseEnd_547722 := by
    simpa [prefixWord, tailWord_547722, baseEnd_547722] using wordTrace_append hprefix tailTrace_547722
  have hstable : (prefixWord ++ tailWord_547722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547722).length < 2 ^ (prefixWord ++ tailWord_547722).sum := by decide
  have hdescent : baseEnd_547722 < baseStart_547722 := by decide
  rcases family_descends (prefixWord ++ tailWord_547722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547735 : List Nat := [1, 1, 3, 3, 1, 2, 3, 1, 4, 3]
def baseStart_547735 : Nat := 118140960795 + 547735 * 2 ^ 59
def prefixEnd_547735 : Nat := 4983230072969 + 3 ^ 40 * 547735 * 2
def baseEnd_547735 : Nat := 187500884193679811995679

theorem tailTrace_547735 : CollatzResearch.WordTrace tailWord_547735 prefixEnd_547735 187500884193679811995679 := by
  unfold tailWord_547735
  simp only [CollatzResearch.WordTrace]
  refine ⟨19977536670657115535556659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13318357780438077023704439 19977536670657115535556659)
  ·
    refine ⟨29966305005985673303334989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19977536670657115535556659 29966305005985673303334989)
    ·
      refine ⟨11237364377244627488750621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29966305005985673303334989 11237364377244627488750621)
      ·
        refine ⟨4214011641466735308281483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11237364377244627488750621 4214011641466735308281483)
        ·
          refine ⟨6321017462200102962422225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4214011641466735308281483 6321017462200102962422225)
          ·
            refine ⟨4740763096650077221816669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6321017462200102962422225 4740763096650077221816669)
            ·
              refine ⟨1777786161243778958181251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4740763096650077221816669 1777786161243778958181251)
              ·
                refine ⟨2666679241865668437271877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1777786161243778958181251 2666679241865668437271877)
                ·
                  refine ⟨500002357849812831988477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2666679241865668437271877 500002357849812831988477)
                  ·
                    refine ⟨187500884193679811995679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 500002357849812831988477 187500884193679811995679)
                    ·
                      rfl

theorem cell22_547735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 1, 4, 3].length) (baseStart_547735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_547735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_547735 prefixEnd_547735 := by exact prefixLift 547735
  have htrace : WordTrace (prefixWord ++ tailWord_547735) baseStart_547735 baseEnd_547735 := by
    simpa [prefixWord, tailWord_547735, baseEnd_547735] using wordTrace_append hprefix tailTrace_547735
  have hstable : (prefixWord ++ tailWord_547735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547735).length < 2 ^ (prefixWord ++ tailWord_547735).sum := by decide
  have hdescent : baseEnd_547735 < baseStart_547735 := by decide
  rcases family_descends (prefixWord ++ tailWord_547735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547748 : List Nat := [2, 3, 1, 2, 1, 2, 2, 9]
def baseStart_547748 : Nat := 118140960795 + 547748 * 2 ^ 59
def prefixEnd_547748 : Nat := 4983230072969 + 3 ^ 40 * 547748 * 2
def baseEnd_547748 : Nat := 20833926039928012380071

theorem tailTrace_547748 : CollatzResearch.WordTrace tailWord_547748 prefixEnd_547748 20833926039928012380071 := by
  unfold tailWord_547748
  simp only [CollatzResearch.WordTrace]
  refine ⟨9989005409805009377889949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13318673879740012503853265 9989005409805009377889949)
  ·
    refine ⟨3745877028676878516708731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9989005409805009377889949 3745877028676878516708731)
    ·
      refine ⟨5618815543015317775063097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3745877028676878516708731 5618815543015317775063097)
      ·
        refine ⟨4214111657261488331297323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5618815543015317775063097 4214111657261488331297323)
        ·
          refine ⟨6321167485892232496945985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4214111657261488331297323 6321167485892232496945985)
          ·
            refine ⟨4740875614419174372709489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6321167485892232496945985 4740875614419174372709489)
            ·
              refine ⟨3555656710814380779532117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4740875614419174372709489 3555656710814380779532117)
              ·
                refine ⟨20833926039928012380071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3555656710814380779532117 20833926039928012380071)
                ·
                  rfl

theorem cell22_547748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 9].length) (baseStart_547748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_547748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_547748 prefixEnd_547748 := by exact prefixLift 547748
  have htrace : WordTrace (prefixWord ++ tailWord_547748) baseStart_547748 baseEnd_547748 := by
    simpa [prefixWord, tailWord_547748, baseEnd_547748] using wordTrace_append hprefix tailTrace_547748
  have hstable : (prefixWord ++ tailWord_547748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547748).length < 2 ^ (prefixWord ++ tailWord_547748).sum := by decide
  have hdescent : baseEnd_547748 < baseStart_547748 := by decide
  rcases family_descends (prefixWord ++ tailWord_547748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547793 : List Nat := [1, 2, 2, 1, 2, 1, 3, 3, 7]
def baseStart_547793 : Nat := 118140960795 + 547793 * 2 ^ 59
def prefixEnd_547793 : Nat := 4983230072969 + 3 ^ 40 * 547793 * 2
def baseEnd_547793 : Nat := 62506912926328998015167

theorem tailTrace_547793 : CollatzResearch.WordTrace tailWord_547793 prefixEnd_547793 62506912926328998015167 := by
  unfold tailWord_547793
  simp only [CollatzResearch.WordTrace]
  refine ⟨19979652104446991441168033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13319768069631327627445355 19979652104446991441168033)
  ·
    refine ⟨14984739078335243580876025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19979652104446991441168033 14984739078335243580876025)
    ·
      refine ⟨11238554308751432685657019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14984739078335243580876025 11238554308751432685657019)
      ·
        refine ⟨16857831463127149028485529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11238554308751432685657019 16857831463127149028485529)
        ·
          refine ⟨12643373597345361771364147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16857831463127149028485529 12643373597345361771364147)
          ·
            refine ⟨18965060396018042657046221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12643373597345361771364147 18965060396018042657046221)
            ·
              refine ⟨7111897648506765996392333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18965060396018042657046221 7111897648506765996392333)
              ·
                refine ⟨2666961618190037248647125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7111897648506765996392333 2666961618190037248647125)
                ·
                  refine ⟨62506912926328998015167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2666961618190037248647125 62506912926328998015167)
                  ·
                    rfl

theorem cell22_547793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 3, 7].length) (baseStart_547793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_547793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_547793 prefixEnd_547793 := by exact prefixLift 547793
  have htrace : WordTrace (prefixWord ++ tailWord_547793) baseStart_547793 baseEnd_547793 := by
    simpa [prefixWord, tailWord_547793, baseEnd_547793] using wordTrace_append hprefix tailTrace_547793
  have hstable : (prefixWord ++ tailWord_547793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547793).length < 2 ^ (prefixWord ++ tailWord_547793).sum := by decide
  have hdescent : baseEnd_547793 < baseStart_547793 := by decide
  rcases family_descends (prefixWord ++ tailWord_547793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547900 : List Nat := [2, 2, 2, 2, 2, 3, 9]
def baseStart_547900 : Nat := 118140960795 + 547900 * 2 ^ 59
def prefixEnd_547900 : Nat := 4983230072969 + 3 ^ 40 * 547900 * 2
def baseEnd_547900 : Nat := 6946569150580532652599

theorem tailTrace_547900 : CollatzResearch.WordTrace tailWord_547900 prefixEnd_547900 6946569150580532652599 := by
  unfold tailWord_547900
  simp only [CollatzResearch.WordTrace]
  refine ⟨9991777357529674357656577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13322369810039565810208769 9991777357529674357656577)
  ·
    refine ⟨7493833018147255768242433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9991777357529674357656577 7493833018147255768242433)
    ·
      refine ⟨5620374763610441826181825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7493833018147255768242433 5620374763610441826181825)
      ·
        refine ⟨4215281072707831369636369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5620374763610441826181825 4215281072707831369636369)
        ·
          refine ⟨3161460804530873527227277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4215281072707831369636369 3161460804530873527227277)
          ·
            refine ⟨1185547801699077572710229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3161460804530873527227277 1185547801699077572710229)
            ·
              refine ⟨6946569150580532652599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1185547801699077572710229 6946569150580532652599)
              ·
                rfl

theorem cell22_547900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 9].length) (baseStart_547900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_547900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_547900 prefixEnd_547900 := by exact prefixLift 547900
  have htrace : WordTrace (prefixWord ++ tailWord_547900) baseStart_547900 baseEnd_547900 := by
    simpa [prefixWord, tailWord_547900, baseEnd_547900] using wordTrace_append hprefix tailTrace_547900
  have hstable : (prefixWord ++ tailWord_547900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547900).length < 2 ^ (prefixWord ++ tailWord_547900).sum := by decide
  have hdescent : baseEnd_547900 < baseStart_547900 := by decide
  rcases family_descends (prefixWord ++ tailWord_547900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547945 : List Nat := [1, 2, 1, 1, 1, 6, 1, 2, 7]
def baseStart_547945 : Nat := 118140960795 + 547945 * 2 ^ 59
def prefixEnd_547945 : Nat := 4983230072969 + 3 ^ 40 * 547945 * 2
def baseEnd_547945 : Nat := 62524257161769754748345

theorem tailTrace_547945 : CollatzResearch.WordTrace tailWord_547945 prefixEnd_547945 62524257161769754748345 := by
  unfold tailWord_547945
  simp only [CollatzResearch.WordTrace]
  refine ⟨19985195999896321400701289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13323463999930880933800859 19985195999896321400701289)
  ·
    refine ⟨14988896999922241050525967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19985195999896321400701289 14988896999922241050525967)
    ·
      refine ⟨22483345499883361575788951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14988896999922241050525967 22483345499883361575788951)
      ·
        refine ⟨33725018249825042363683427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22483345499883361575788951 33725018249825042363683427)
        ·
          refine ⟨50587527374737563545525141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33725018249825042363683427 50587527374737563545525141)
          ·
            refine ⟨2371290345690823291196491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 50587527374737563545525141 2371290345690823291196491)
            ·
              refine ⟨3556935518536234936794737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2371290345690823291196491 3556935518536234936794737)
              ·
                refine ⟨2667701638902176202596053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3556935518536234936794737 2667701638902176202596053)
                ·
                  refine ⟨62524257161769754748345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2667701638902176202596053 62524257161769754748345)
                  ·
                    rfl

theorem cell22_547945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 2, 7].length) (baseStart_547945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_547945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_547945 prefixEnd_547945 := by exact prefixLift 547945
  have htrace : WordTrace (prefixWord ++ tailWord_547945) baseStart_547945 baseEnd_547945 := by
    simpa [prefixWord, tailWord_547945, baseEnd_547945] using wordTrace_append hprefix tailTrace_547945
  have hstable : (prefixWord ++ tailWord_547945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547945).length < 2 ^ (prefixWord ++ tailWord_547945).sum := by decide
  have hdescent : baseEnd_547945 < baseStart_547945 := by decide
  rcases family_descends (prefixWord ++ tailWord_547945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547960 : List Nat := [2, 1, 2, 1, 1, 1, 4, 1, 4, 5]
def baseStart_547960 : Nat := 118140960795 + 547960 * 2 ^ 59
def prefixEnd_547960 : Nat := 4983230072969 + 3 ^ 40 * 547960 * 2
def baseEnd_547960 : Nat := 187577906291854225119989

theorem tailTrace_547960 : CollatzResearch.WordTrace tailWord_547960 prefixEnd_547960 187577906291854225119989 := by
  unfold tailWord_547960
  simp only [CollatzResearch.WordTrace]
  refine ⟨9992871547420989481248667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13323828729894652641664889 9992871547420989481248667)
  ·
    refine ⟨14989307321131484221873001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9992871547420989481248667 14989307321131484221873001)
    ·
      refine ⟨11241980490848613166404751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14989307321131484221873001 11241980490848613166404751)
      ·
        refine ⟨16862970736272919749607127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11241980490848613166404751 16862970736272919749607127)
        ·
          refine ⟨25294456104409379624410691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16862970736272919749607127 25294456104409379624410691)
          ·
            refine ⟨37941684156614069436616037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25294456104409379624410691 37941684156614069436616037)
            ·
              refine ⟨7114065779365138019365507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37941684156614069436616037 7114065779365138019365507)
              ·
                refine ⟨10671098669047707029048261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7114065779365138019365507 10671098669047707029048261)
                ·
                  refine ⟨2000831000446445067946549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10671098669047707029048261 2000831000446445067946549)
                  ·
                    refine ⟨187577906291854225119989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2000831000446445067946549 187577906291854225119989)
                    ·
                      rfl

theorem cell22_547960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 4, 5].length) (baseStart_547960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_547960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_547960 prefixEnd_547960 := by exact prefixLift 547960
  have htrace : WordTrace (prefixWord ++ tailWord_547960) baseStart_547960 baseEnd_547960 := by
    simpa [prefixWord, tailWord_547960, baseEnd_547960] using wordTrace_append hprefix tailTrace_547960
  have hstable : (prefixWord ++ tailWord_547960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547960).length < 2 ^ (prefixWord ++ tailWord_547960).sum := by decide
  have hdescent : baseEnd_547960 < baseStart_547960 := by decide
  rcases family_descends (prefixWord ++ tailWord_547960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547975 : List Nat := [1, 1, 4, 2, 1, 1, 1, 1, 2, 8]
def baseStart_547975 : Nat := 118140960795 + 547975 * 2 ^ 59
def prefixEnd_547975 : Nat := 4983230072969 + 3 ^ 40 * 547975 * 2
def baseEnd_547975 : Nat := 187583041098399185994943

theorem tailTrace_547975 : CollatzResearch.WordTrace tailWord_547975 prefixEnd_547975 187583041098399185994943 := by
  unfold tailWord_547975
  simp only [CollatzResearch.WordTrace]
  refine ⟨19986290189787636524293379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13324193459858424349528919 19986290189787636524293379)
  ·
    refine ⟨29979435284681454786440069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19986290189787636524293379 29979435284681454786440069)
    ·
      refine ⟨5621144115877772772457513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29979435284681454786440069 5621144115877772772457513)
      ·
        refine ⟨4215858086908329579343135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5621144115877772772457513 4215858086908329579343135)
        ·
          refine ⟨6323787130362494369014703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4215858086908329579343135 6323787130362494369014703)
          ·
            refine ⟨9485680695543741553522055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6323787130362494369014703 9485680695543741553522055)
            ·
              refine ⟨14228521043315612330283083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9485680695543741553522055 14228521043315612330283083)
              ·
                refine ⟨21342781564973418495424625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14228521043315612330283083 21342781564973418495424625)
                ·
                  refine ⟨16007086173730063871568469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21342781564973418495424625 16007086173730063871568469)
                  ·
                    refine ⟨187583041098399185994943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 16007086173730063871568469 187583041098399185994943)
                    ·
                      rfl

theorem cell22_547975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 2, 8].length) (baseStart_547975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_547975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_547975 prefixEnd_547975 := by exact prefixLift 547975
  have htrace : WordTrace (prefixWord ++ tailWord_547975) baseStart_547975 baseEnd_547975 := by
    simpa [prefixWord, tailWord_547975, baseEnd_547975] using wordTrace_append hprefix tailTrace_547975
  have hstable : (prefixWord ++ tailWord_547975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547975).length < 2 ^ (prefixWord ++ tailWord_547975).sum := by decide
  have hdescent : baseEnd_547975 < baseStart_547975 := by decide
  rcases family_descends (prefixWord ++ tailWord_547975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548035 : List Nat := [1, 1, 1, 3, 1, 1, 1, 13]
def baseStart_548035 : Nat := 118140960795 + 548035 * 2 ^ 59
def prefixEnd_548035 : Nat := 4983230072969 + 3 ^ 40 * 548035 * 2
def baseEnd_548035 : Nat := 20844842258286558832751

theorem tailTrace_548035 : CollatzResearch.WordTrace tailWord_548035 prefixEnd_548035 20844842258286558832751 := by
  unfold tailWord_548035
  simp only [CollatzResearch.WordTrace]
  refine ⟨19988478569570266771477559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13325652379713511180985039 19988478569570266771477559)
  ·
    refine ⟨29982717854355400157216339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19988478569570266771477559 29982717854355400157216339)
    ·
      refine ⟨44974076781533100235824509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29982717854355400157216339 44974076781533100235824509)
      ·
        refine ⟨16865278793074912588434191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44974076781533100235824509 16865278793074912588434191)
        ·
          refine ⟨25297918189612368882651287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16865278793074912588434191 25297918189612368882651287)
          ·
            refine ⟨37946877284418553323976931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25297918189612368882651287 37946877284418553323976931)
            ·
              refine ⟨56920315926627829985965397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37946877284418553323976931 56920315926627829985965397)
              ·
                refine ⟨20844842258286558832751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 56920315926627829985965397 20844842258286558832751)
                ·
                  rfl

theorem cell22_548035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 13].length) (baseStart_548035 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_548035 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_548035 prefixEnd_548035 := by exact prefixLift 548035
  have htrace : WordTrace (prefixWord ++ tailWord_548035) baseStart_548035 baseEnd_548035 := by
    simpa [prefixWord, tailWord_548035, baseEnd_548035] using wordTrace_append hprefix tailTrace_548035
  have hstable : (prefixWord ++ tailWord_548035).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548035).length < 2 ^ (prefixWord ++ tailWord_548035).sum := by decide
  have hdescent : baseEnd_548035 < baseStart_548035 := by decide
  rcases family_descends (prefixWord ++ tailWord_548035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548161 : List Nat := [1, 2, 5, 2, 1, 2, 1, 1, 3, 4]
def baseStart_548161 : Nat := 118140960795 + 548161 * 2 ^ 59
def prefixEnd_548161 : Nat := 4983230072969 + 3 ^ 40 * 548161 * 2
def baseEnd_548161 : Nat := 187646712699556700844373

theorem tailTrace_548161 : CollatzResearch.WordTrace tailWord_548161 prefixEnd_548161 187646712699556700844373 := by
  unfold tailWord_548161
  simp only [CollatzResearch.WordTrace]
  refine ⟨19993074167113790290564337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13328716111409193527042891 19993074167113790290564337)
  ·
    refine ⟨14994805625335342717923253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19993074167113790290564337 14994805625335342717923253)
    ·
      refine ⟨1405763027375188379805305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14994805625335342717923253 1405763027375188379805305)
      ·
        refine ⟨1054322270531391284853979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1405763027375188379805305 1054322270531391284853979)
        ·
          refine ⟨1581483405797086927280969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1054322270531391284853979 1581483405797086927280969)
          ·
            refine ⟨1186112554347815195460727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1581483405797086927280969 1186112554347815195460727)
            ·
              refine ⟨1779168831521722793191091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1186112554347815195460727 1779168831521722793191091)
              ·
                refine ⟨2668753247282584189786637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1779168831521722793191091 2668753247282584189786637)
                ·
                  refine ⟨1000782467730969071169989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2668753247282584189786637 1000782467730969071169989)
                  ·
                    refine ⟨187646712699556700844373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1000782467730969071169989 187646712699556700844373)
                    ·
                      rfl

theorem cell22_548161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_548161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_548161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_548161 prefixEnd_548161 := by exact prefixLift 548161
  have htrace : WordTrace (prefixWord ++ tailWord_548161) baseStart_548161 baseEnd_548161 := by
    simpa [prefixWord, tailWord_548161, baseEnd_548161] using wordTrace_append hprefix tailTrace_548161
  have hstable : (prefixWord ++ tailWord_548161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548161).length < 2 ^ (prefixWord ++ tailWord_548161).sum := by decide
  have hdescent : baseEnd_548161 < baseStart_548161 := by decide
  rcases family_descends (prefixWord ++ tailWord_548161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548174 : List Nat := [4, 1, 1, 1, 1, 1, 5, 2, 1, 5]
def baseStart_548174 : Nat := 118140960795 + 548174 * 2 ^ 59
def prefixEnd_548174 : Nat := 4983230072969 + 3 ^ 40 * 548174 * 2
def baseEnd_548174 : Nat := 187651162865229000269333

theorem tailTrace_548174 : CollatzResearch.WordTrace tailWord_548174 prefixEnd_548174 187651162865229000269333 := by
  unfold tailWord_548174
  simp only [CollatzResearch.WordTrace]
  refine ⟨2499193539508336688848447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13329032210711129007191717 2499193539508336688848447)
  ·
    refine ⟨3748790309262505033272671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2499193539508336688848447 3748790309262505033272671)
    ·
      refine ⟨5623185463893757549909007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3748790309262505033272671 5623185463893757549909007)
      ·
        refine ⟨8434778195840636324863511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5623185463893757549909007 8434778195840636324863511)
        ·
          refine ⟨12652167293760954487295267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8434778195840636324863511 12652167293760954487295267)
          ·
            refine ⟨18978250940641431730942901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12652167293760954487295267 18978250940641431730942901)
            ·
              refine ⟨1779211025685134224775897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18978250940641431730942901 1779211025685134224775897)
              ·
                refine ⟨1334408269263850668581923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1779211025685134224775897 1334408269263850668581923)
                ·
                  refine ⟨2001612403895776002872885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1334408269263850668581923 2001612403895776002872885)
                  ·
                    refine ⟨187651162865229000269333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2001612403895776002872885 187651162865229000269333)
                    ·
                      rfl

theorem cell22_548174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 2, 1, 5].length) (baseStart_548174 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_548174 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_548174 prefixEnd_548174 := by exact prefixLift 548174
  have htrace : WordTrace (prefixWord ++ tailWord_548174) baseStart_548174 baseEnd_548174 := by
    simpa [prefixWord, tailWord_548174, baseEnd_548174] using wordTrace_append hprefix tailTrace_548174
  have hstable : (prefixWord ++ tailWord_548174).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548174).length < 2 ^ (prefixWord ++ tailWord_548174).sum := by decide
  have hdescent : baseEnd_548174 < baseStart_548174 := by decide
  rcases family_descends (prefixWord ++ tailWord_548174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548182 : List Nat := [5, 2, 3, 1, 1, 1, 2, 2, 5]
def baseStart_548182 : Nat := 118140960795 + 548182 * 2 ^ 59
def prefixEnd_548182 : Nat := 4983230072969 + 3 ^ 40 * 548182 * 2
def baseEnd_548182 : Nat := 62551300476239882023103

theorem tailTrace_548182 : CollatzResearch.WordTrace tailWord_548182 prefixEnd_548182 62551300476239882023103 := by
  unfold tailWord_548182
  simp only [CollatzResearch.WordTrace]
  refine ⟨1249615006252356929817425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13329226733358473918052533 1249615006252356929817425)
  ·
    refine ⟨937211254689267697363069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1249615006252356929817425 937211254689267697363069)
    ·
      refine ⟨351454220508475386511151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 937211254689267697363069 351454220508475386511151)
      ·
        refine ⟨527181330762713079766727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 351454220508475386511151 527181330762713079766727)
        ·
          refine ⟨790771996144069619650091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 527181330762713079766727 790771996144069619650091)
          ·
            refine ⟨1186157994216104429475137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 790771996144069619650091 1186157994216104429475137)
            ·
              refine ⟨889618495662078322106353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1186157994216104429475137 889618495662078322106353)
              ·
                refine ⟨667213871746558741579765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 889618495662078322106353 667213871746558741579765)
                ·
                  refine ⟨62551300476239882023103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 667213871746558741579765 62551300476239882023103)
                  ·
                    rfl

theorem cell22_548182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 2, 2, 5].length) (baseStart_548182 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_548182 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_548182 prefixEnd_548182 := by exact prefixLift 548182
  have htrace : WordTrace (prefixWord ++ tailWord_548182) baseStart_548182 baseEnd_548182 := by
    simpa [prefixWord, tailWord_548182, baseEnd_548182] using wordTrace_append hprefix tailTrace_548182
  have hstable : (prefixWord ++ tailWord_548182).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548182).length < 2 ^ (prefixWord ++ tailWord_548182).sum := by decide
  have hdescent : baseEnd_548182 < baseStart_548182 := by decide
  rcases family_descends (prefixWord ++ tailWord_548182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548204 : List Nat := [2, 2, 1, 1, 5, 1, 3, 7]
def baseStart_548204 : Nat := 118140960795 + 548204 * 2 ^ 59
def prefixEnd_548204 : Nat := 4983230072969 + 3 ^ 40 * 548204 * 2
def baseEnd_548204 : Nat := 20851270275368769113249

theorem tailTrace_548204 : CollatzResearch.WordTrace tailWord_548204 prefixEnd_548204 20851270275368769113249 := by
  unfold tailWord_548204
  simp only [CollatzResearch.WordTrace]
  refine ⟨9997321252979004317189833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13329761670638672422919777 9997321252979004317189833)
  ·
    refine ⟨7497990939734253237892375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9997321252979004317189833 7497990939734253237892375)
    ·
      refine ⟨11246986409601379856838563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7497990939734253237892375 11246986409601379856838563)
      ·
        refine ⟨16870479614402069785257845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11246986409601379856838563 16870479614402069785257845)
        ·
          refine ⟨1581607463850194042367923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16870479614402069785257845 1581607463850194042367923)
          ·
            refine ⟨2372411195775291063551885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1581607463850194042367923 2372411195775291063551885)
            ·
              refine ⟨889654198415734148831957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2372411195775291063551885 889654198415734148831957)
              ·
                refine ⟨20851270275368769113249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 889654198415734148831957 20851270275368769113249)
                ·
                  rfl

theorem cell22_548204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 3, 7].length) (baseStart_548204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_548204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_548204 prefixEnd_548204 := by exact prefixLift 548204
  have htrace : WordTrace (prefixWord ++ tailWord_548204) baseStart_548204 baseEnd_548204 := by
    simpa [prefixWord, tailWord_548204, baseEnd_548204] using wordTrace_append hprefix tailTrace_548204
  have hstable : (prefixWord ++ tailWord_548204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548204).length < 2 ^ (prefixWord ++ tailWord_548204).sum := by decide
  have hdescent : baseEnd_548204 < baseStart_548204 := by decide
  rcases family_descends (prefixWord ++ tailWord_548204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548242 : List Nat := [3, 2, 3, 3, 1, 2, 1, 2, 2, 3]
def baseStart_548242 : Nat := 118140960795 + 548242 * 2 ^ 59
def prefixEnd_548242 : Nat := 4983230072969 + 3 ^ 40 * 548242 * 2
def baseEnd_548242 : Nat := 187674440654899489569125

theorem tailTrace_548242 : CollatzResearch.WordTrace tailWord_548242 prefixEnd_548242 187674440654899489569125 := by
  unfold tailWord_548242
  simp only [CollatzResearch.WordTrace]
  refine ⟨4999007119955085281065745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13330685653213560749508653 4999007119955085281065745)
  ·
    refine ⟨3749255339966313960799309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4999007119955085281065745 3749255339966313960799309)
    ·
      refine ⟨1405970752487367735299741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3749255339966313960799309 1405970752487367735299741)
      ·
        refine ⟨527239032182762900737403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1405970752487367735299741 527239032182762900737403)
        ·
          refine ⟨790858548274144351106105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 527239032182762900737403 790858548274144351106105)
          ·
            refine ⟨593143911205608263329579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 790858548274144351106105 593143911205608263329579)
            ·
              refine ⟨889715866808412394994369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 593143911205608263329579 889715866808412394994369)
              ·
                refine ⟨667286900106309296245777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 889715866808412394994369 667286900106309296245777)
                ·
                  refine ⟨500465175079731972184333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 667286900106309296245777 500465175079731972184333)
                  ·
                    refine ⟨187674440654899489569125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 500465175079731972184333 187674440654899489569125)
                    ·
                      rfl

theorem cell22_548242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 1, 2, 2, 3].length) (baseStart_548242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_548242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_548242 prefixEnd_548242 := by exact prefixLift 548242
  have htrace : WordTrace (prefixWord ++ tailWord_548242) baseStart_548242 baseEnd_548242 := by
    simpa [prefixWord, tailWord_548242, baseEnd_548242] using wordTrace_append hprefix tailTrace_548242
  have hstable : (prefixWord ++ tailWord_548242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548242).length < 2 ^ (prefixWord ++ tailWord_548242).sum := by decide
  have hdescent : baseEnd_548242 < baseStart_548242 := by decide
  rcases family_descends (prefixWord ++ tailWord_548242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548249 : List Nat := [1, 2, 1, 2, 1, 6, 1, 1, 7]
def baseStart_548249 : Nat := 118140960795 + 548249 * 2 ^ 59
def prefixEnd_548249 : Nat := 4983230072969 + 3 ^ 40 * 548249 * 2
def baseEnd_548249 : Nat := 62558945632651268214701

theorem tailTrace_548249 : CollatzResearch.WordTrace tailWord_548249 prefixEnd_548249 62558945632651268214701 := by
  unfold tailWord_548249
  simp only [CollatzResearch.WordTrace]
  refine ⟨19996283790794981319767801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13330855860529987546511867 19996283790794981319767801)
  ·
    refine ⟨14997212843096235989825851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19996283790794981319767801 14997212843096235989825851)
    ·
      refine ⟨22495819264644353984738777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14997212843096235989825851 22495819264644353984738777)
      ·
        refine ⟨16871864448483265488554083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22495819264644353984738777 16871864448483265488554083)
        ·
          refine ⟨25307796672724898232831125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16871864448483265488554083 25307796672724898232831125)
          ·
            refine ⟨1186302969033979604663959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 25307796672724898232831125 1186302969033979604663959)
            ·
              refine ⟨1779454453550969406995939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1186302969033979604663959 1779454453550969406995939)
              ·
                refine ⟨2669181680326454110493909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1779454453550969406995939 2669181680326454110493909)
                ·
                  refine ⟨62558945632651268214701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2669181680326454110493909 62558945632651268214701)
                  ·
                    rfl

theorem cell22_548249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 1, 7].length) (baseStart_548249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_548249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_548249 prefixEnd_548249 := by exact prefixLift 548249
  have htrace : WordTrace (prefixWord ++ tailWord_548249) baseStart_548249 baseEnd_548249 := by
    simpa [prefixWord, tailWord_548249, baseEnd_548249] using wordTrace_append hprefix tailTrace_548249
  have hstable : (prefixWord ++ tailWord_548249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548249).length < 2 ^ (prefixWord ++ tailWord_548249).sum := by decide
  have hdescent : baseEnd_548249 < baseStart_548249 := by decide
  rcases family_descends (prefixWord ++ tailWord_548249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548253 : List Nat := [1, 4, 2, 1, 3, 2, 2, 1, 3, 3]
def baseStart_548253 : Nat := 118140960795 + 548253 * 2 ^ 59
def prefixEnd_548253 : Nat := 4983230072969 + 3 ^ 40 * 548253 * 2
def baseEnd_548253 : Nat := 187678206179699127544091

theorem tailTrace_548253 : CollatzResearch.WordTrace tailWord_548253 prefixEnd_548253 187678206179699127544091 := by
  unfold tailWord_548253
  simp only [CollatzResearch.WordTrace]
  refine ⟨19996429682780490002913413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13330953121853660001942275 19996429682780490002913413)
  ·
    refine ⟨3749330565521341875546265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19996429682780490002913413 3749330565521341875546265)
    ·
      refine ⟨2811997924141006406659699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3749330565521341875546265 2811997924141006406659699)
      ·
        refine ⟨4217996886211509609989549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2811997924141006406659699 4217996886211509609989549)
        ·
          refine ⟨1581748832329316103746081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4217996886211509609989549 1581748832329316103746081)
          ·
            refine ⟨1186311624246987077809561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1581748832329316103746081 1186311624246987077809561)
            ·
              refine ⟨889733718185240308357171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1186311624246987077809561 889733718185240308357171)
              ·
                refine ⟨1334600577277860462535757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 889733718185240308357171 1334600577277860462535757)
                ·
                  refine ⟨500475216479197673450909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1334600577277860462535757 500475216479197673450909)
                  ·
                    refine ⟨187678206179699127544091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 500475216479197673450909 187678206179699127544091)
                    ·
                      rfl

theorem cell22_548253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 2, 1, 3, 3].length) (baseStart_548253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_548253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_548253 prefixEnd_548253 := by exact prefixLift 548253
  have htrace : WordTrace (prefixWord ++ tailWord_548253) baseStart_548253 baseEnd_548253 := by
    simpa [prefixWord, tailWord_548253, baseEnd_548253] using wordTrace_append hprefix tailTrace_548253
  have hstable : (prefixWord ++ tailWord_548253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548253).length < 2 ^ (prefixWord ++ tailWord_548253).sum := by decide
  have hdescent : baseEnd_548253 < baseStart_548253 := by decide
  rcases family_descends (prefixWord ++ tailWord_548253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548296 : List Nat := [2, 1, 3, 1, 3, 1, 1, 5, 1, 4]
def baseStart_548296 : Nat := 118140960795 + 548296 * 2 ^ 59
def prefixEnd_548296 : Nat := 4983230072969 + 3 ^ 40 * 548296 * 2
def baseEnd_548296 : Nat := 187692925958461348718959

theorem tailTrace_548296 : CollatzResearch.WordTrace tailWord_548296 prefixEnd_548296 187692925958461348718959 := by
  unfold tailWord_548296
  simp only [CollatzResearch.WordTrace]
  refine ⟨9998999010812354173364371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13331998681083138897819161 9998999010812354173364371)
  ·
    refine ⟨14998498516218531260046557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9998999010812354173364371 14998498516218531260046557)
    ·
      refine ⟨5624436943581949222517459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14998498516218531260046557 5624436943581949222517459)
      ·
        refine ⟨8436655415372923833776189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5624436943581949222517459 8436655415372923833776189)
        ·
          refine ⟨3163745780764846437666071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8436655415372923833776189 3163745780764846437666071)
          ·
            refine ⟨4745618671147269656499107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3163745780764846437666071 4745618671147269656499107)
            ·
              refine ⟨7118428006720904484748661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4745618671147269656499107 7118428006720904484748661)
              ·
                refine ⟨667352625630084795445187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7118428006720904484748661 667352625630084795445187)
                ·
                  refine ⟨1001028938445127193167781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 667352625630084795445187 1001028938445127193167781)
                  ·
                    refine ⟨187692925958461348718959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1001028938445127193167781 187692925958461348718959)
                    ·
                      rfl

theorem cell22_548296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 5, 1, 4].length) (baseStart_548296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_548296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_548296 prefixEnd_548296 := by exact prefixLift 548296
  have htrace : WordTrace (prefixWord ++ tailWord_548296) baseStart_548296 baseEnd_548296 := by
    simpa [prefixWord, tailWord_548296, baseEnd_548296] using wordTrace_append hprefix tailTrace_548296
  have hstable : (prefixWord ++ tailWord_548296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548296).length < 2 ^ (prefixWord ++ tailWord_548296).sum := by decide
  have hdescent : baseEnd_548296 < baseStart_548296 := by decide
  rcases family_descends (prefixWord ++ tailWord_548296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548311 : List Nat := [1, 1, 3, 2, 1, 1, 1, 8, 4]
def baseStart_548311 : Nat := 118140960795 + 548311 * 2 ^ 59
def prefixEnd_548311 : Nat := 4983230072969 + 3 ^ 40 * 548311 * 2
def baseEnd_548311 : Nat := 62566020255002103197971

theorem tailTrace_548311 : CollatzResearch.WordTrace tailWord_548311 prefixEnd_548311 62566020255002103197971 := by
  unfold tailWord_548311
  simp only [CollatzResearch.WordTrace]
  refine ⟨19998545116570365908524787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13332363411046910605683191 19998545116570365908524787)
  ·
    refine ⟨29997817674855548862787181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19998545116570365908524787 29997817674855548862787181)
    ·
      refine ⟨11249181628070830823545193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29997817674855548862787181 11249181628070830823545193)
      ·
        refine ⟨8436886221053123117658895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11249181628070830823545193 8436886221053123117658895)
        ·
          refine ⟨12655329331579684676488343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8436886221053123117658895 12655329331579684676488343)
          ·
            refine ⟨18982993997369527014732515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12655329331579684676488343 18982993997369527014732515)
            ·
              refine ⟨28474490996054290522098773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18982993997369527014732515 28474490996054290522098773)
              ·
                refine ⟨333685441360011217055845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 28474490996054290522098773 333685441360011217055845)
                ·
                  refine ⟨62566020255002103197971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 333685441360011217055845 62566020255002103197971)
                  ·
                    rfl

theorem cell22_548311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 8, 4].length) (baseStart_548311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_548311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_548311 prefixEnd_548311 := by exact prefixLift 548311
  have htrace : WordTrace (prefixWord ++ tailWord_548311) baseStart_548311 baseEnd_548311 := by
    simpa [prefixWord, tailWord_548311, baseEnd_548311] using wordTrace_append hprefix tailTrace_548311
  have hstable : (prefixWord ++ tailWord_548311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548311).length < 2 ^ (prefixWord ++ tailWord_548311).sum := by decide
  have hdescent : baseEnd_548311 < baseStart_548311 := by decide
  rcases family_descends (prefixWord ++ tailWord_548311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
