import V185TrunkScan22Chunk186

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1667925 : List Nat := [1, 3, 2, 2, 2, 1, 2, 3, 3, 3]
def baseStart_1667925 : Nat := 118140960795 + 1667925 * 2 ^ 59
def prefixEnd_1667925 : Nat := 4983230072969 + 3 ^ 40 * 1667925 * 2
def baseEnd_1667925 : Nat := 570964813766994646311239

theorem tailTrace_1667925 : CollatzResearch.WordTrace tailWord_1667925 prefixEnd_1667925 570964813766994646311239 := by
  unfold tailWord_1667925
  simp only [CollatzResearch.WordTrace]
  refine ⟨60834222482400058756333229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40556148321600039170888819 60834222482400058756333229)
  ·
    refine ⟨22812833430900022033624961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60834222482400058756333229 22812833430900022033624961)
    ·
      refine ⟨17109625073175016525218721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22812833430900022033624961 17109625073175016525218721)
      ·
        refine ⟨12832218804881262393914041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17109625073175016525218721 12832218804881262393914041)
        ·
          refine ⟨9624164103660946795435531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12832218804881262393914041 9624164103660946795435531)
          ·
            refine ⟨14436246155491420193153297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9624164103660946795435531 14436246155491420193153297)
            ·
              refine ⟨10827184616618565144864973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14436246155491420193153297 10827184616618565144864973)
              ·
                refine ⟨4060194231231961929324365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10827184616618565144864973 4060194231231961929324365)
                ·
                  refine ⟨1522572836711985723496637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4060194231231961929324365 1522572836711985723496637)
                  ·
                    refine ⟨570964813766994646311239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1522572836711985723496637 570964813766994646311239)
                    ·
                      rfl

theorem cell22_1667925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 3, 3, 3].length) (baseStart_1667925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1667925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1667925 prefixEnd_1667925 := by exact prefixLift 1667925
  have htrace : WordTrace (prefixWord ++ tailWord_1667925) baseStart_1667925 baseEnd_1667925 := by
    simpa [prefixWord, tailWord_1667925, baseEnd_1667925] using wordTrace_append hprefix tailTrace_1667925
  have hstable : (prefixWord ++ tailWord_1667925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1667925).length < 2 ^ (prefixWord ++ tailWord_1667925).sum := by decide
  have hdescent : baseEnd_1667925 < baseStart_1667925 := by decide
  rcases family_descends (prefixWord ++ tailWord_1667925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1667968 : List Nat := [2, 1, 1, 2, 1, 2, 2, 2, 5, 4]
def baseStart_1667968 : Nat := 118140960795 + 1667968 * 2 ^ 59
def prefixEnd_1667968 : Nat := 4983230072969 + 3 ^ 40 * 1667968 * 2
def baseEnd_1667968 : Nat := 570979533545756867486107

theorem tailTrace_1667968 : CollatzResearch.WordTrace tailWord_1667968 prefixEnd_1667968 570979533545756867486107 := by
  unfold tailWord_1667968
  simp only [CollatzResearch.WordTrace]
  refine ⟨30417895410622138550074279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40557193880829518066765705 30417895410622138550074279)
  ·
    refine ⟨45626843115933207825111419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30417895410622138550074279 45626843115933207825111419)
    ·
      refine ⟨68440264673899811737667129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45626843115933207825111419 68440264673899811737667129)
      ·
        refine ⟨51330198505424858803250347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68440264673899811737667129 51330198505424858803250347)
        ·
          refine ⟨76995297758137288204875521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51330198505424858803250347 76995297758137288204875521)
          ·
            refine ⟨57746473318602966153656641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76995297758137288204875521 57746473318602966153656641)
            ·
              refine ⟨43309854988952224615242481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57746473318602966153656641 43309854988952224615242481)
              ·
                refine ⟨32482391241714168461431861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43309854988952224615242481 32482391241714168461431861)
                ·
                  refine ⟨3045224178910703293259237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32482391241714168461431861 3045224178910703293259237)
                  ·
                    refine ⟨570979533545756867486107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3045224178910703293259237 570979533545756867486107)
                    ·
                      rfl

theorem cell22_1667968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 5, 4].length) (baseStart_1667968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1667968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1667968 prefixEnd_1667968 := by exact prefixLift 1667968
  have htrace : WordTrace (prefixWord ++ tailWord_1667968) baseStart_1667968 baseEnd_1667968 := by
    simpa [prefixWord, tailWord_1667968, baseEnd_1667968] using wordTrace_append hprefix tailTrace_1667968
  have hstable : (prefixWord ++ tailWord_1667968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1667968).length < 2 ^ (prefixWord ++ tailWord_1667968).sum := by decide
  have hdescent : baseEnd_1667968 < baseStart_1667968 := by decide
  rcases family_descends (prefixWord ++ tailWord_1667968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1668002 : List Nat := [3, 3, 1, 2, 2, 1, 1, 4, 1, 4]
def baseStart_1668002 : Nat := 118140960795 + 1668002 * 2 ^ 59
def prefixEnd_1668002 : Nat := 4983230072969 + 3 ^ 40 * 1668002 * 2
def baseEnd_1668002 : Nat := 570991172440592112136003

theorem tailTrace_1668002 : CollatzResearch.WordTrace tailWord_1668002 prefixEnd_1668002 570991172440592112136003 := by
  unfold tailWord_1668002
  simp only [CollatzResearch.WordTrace]
  refine ⟨15209257725780275226721565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40558020602080733937924173 15209257725780275226721565)
  ·
    refine ⟨5703471647167603210020587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15209257725780275226721565 5703471647167603210020587)
    ·
      refine ⟨8555207470751404815030881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5703471647167603210020587 8555207470751404815030881)
      ·
        refine ⟨6416405603063553611273161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8555207470751404815030881 6416405603063553611273161)
        ·
          refine ⟨4812304202297665208454871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6416405603063553611273161 4812304202297665208454871)
          ·
            refine ⟨7218456303446497812682307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4812304202297665208454871 7218456303446497812682307)
            ·
              refine ⟨10827684455169746719023461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7218456303446497812682307 10827684455169746719023461)
              ·
                refine ⟨2030190835344327509816899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10827684455169746719023461 2030190835344327509816899)
                ·
                  refine ⟨3045286253016491264725349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2030190835344327509816899 3045286253016491264725349)
                  ·
                    refine ⟨570991172440592112136003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3045286253016491264725349 570991172440592112136003)
                    ·
                      rfl

theorem cell22_1668002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 4, 1, 4].length) (baseStart_1668002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1668002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1668002 prefixEnd_1668002 := by exact prefixLift 1668002
  have htrace : WordTrace (prefixWord ++ tailWord_1668002) baseStart_1668002 baseEnd_1668002 := by
    simpa [prefixWord, tailWord_1668002, baseEnd_1668002] using wordTrace_append hprefix tailTrace_1668002
  have hstable : (prefixWord ++ tailWord_1668002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1668002).length < 2 ^ (prefixWord ++ tailWord_1668002).sum := by decide
  have hdescent : baseEnd_1668002 < baseStart_1668002 := by decide
  rcases family_descends (prefixWord ++ tailWord_1668002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1668085 : List Nat := [1, 3, 5, 2, 2, 1, 2, 2, 4]
def baseStart_1668085 : Nat := 118140960795 + 1668085 * 2 ^ 59
def prefixEnd_1668085 : Nat := 4983230072969 + 3 ^ 40 * 1668085 * 2
def baseEnd_1668085 : Nat := 190339861678935854103583

theorem tailTrace_1668085 : CollatzResearch.WordTrace tailWord_1668085 prefixEnd_1668085 190339861678935854103583 := by
  unfold tailWord_1668085
  simp only [CollatzResearch.WordTrace]
  refine ⟨60840058161820406082157709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40560038774546937388105139 60840058161820406082157709)
  ·
    refine ⟨22815021810682652280809141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60840058161820406082157709 22815021810682652280809141)
    ·
      refine ⟨2138908294751498651325857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22815021810682652280809141 2138908294751498651325857)
      ·
        refine ⟨1604181221063623988494393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2138908294751498651325857 1604181221063623988494393)
        ·
          refine ⟨1203135915797717991370795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1604181221063623988494393 1203135915797717991370795)
          ·
            refine ⟨1804703873696576987056193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1203135915797717991370795 1804703873696576987056193)
            ·
              refine ⟨1353527905272432740292145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1804703873696576987056193 1353527905272432740292145)
              ·
                refine ⟨1015145928954324555219109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1353527905272432740292145 1015145928954324555219109)
                ·
                  refine ⟨190339861678935854103583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1015145928954324555219109 190339861678935854103583)
                  ·
                    rfl

theorem cell22_1668085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 2, 2, 4].length) (baseStart_1668085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1668085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1668085 prefixEnd_1668085 := by exact prefixLift 1668085
  have htrace : WordTrace (prefixWord ++ tailWord_1668085) baseStart_1668085 baseEnd_1668085 := by
    simpa [prefixWord, tailWord_1668085, baseEnd_1668085] using wordTrace_append hprefix tailTrace_1668085
  have hstable : (prefixWord ++ tailWord_1668085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1668085).length < 2 ^ (prefixWord ++ tailWord_1668085).sum := by decide
  have hdescent : baseEnd_1668085 < baseStart_1668085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1668085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1668128 : List Nat := [2, 1, 1, 7, 1, 1, 2, 3, 1, 3]
def baseStart_1668128 : Nat := 118140960795 + 1668128 * 2 ^ 59
def prefixEnd_1668128 : Nat := 4983230072969 + 3 ^ 40 * 1668128 * 2
def baseEnd_1668128 : Nat := 571034304815569783485617

theorem tailTrace_1668128 : CollatzResearch.WordTrace tailWord_1668128 prefixEnd_1668128 571034304815569783485617 := by
  unfold tailWord_1668128
  simp only [CollatzResearch.WordTrace]
  refine ⟨30420813250332312212986519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40561084333776416283982025 30420813250332312212986519)
  ·
    refine ⟨45631219875498468319479779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30420813250332312212986519 45631219875498468319479779)
    ·
      refine ⟨68446829813247702479219669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45631219875498468319479779 68446829813247702479219669)
      ·
        refine ⟨1604222573747993026856711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 68446829813247702479219669 1604222573747993026856711)
        ·
          refine ⟨2406333860621989540285067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1604222573747993026856711 2406333860621989540285067)
          ·
            refine ⟨3609500790932984310427601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2406333860621989540285067 3609500790932984310427601)
            ·
              refine ⟨2707125593199738232820701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3609500790932984310427601 2707125593199738232820701)
              ·
                refine ⟨1015172097449901837307763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2707125593199738232820701 1015172097449901837307763)
                ·
                  refine ⟨1522758146174852755961645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1015172097449901837307763 1522758146174852755961645)
                  ·
                    refine ⟨571034304815569783485617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1522758146174852755961645 571034304815569783485617)
                    ·
                      rfl

theorem cell22_1668128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 2, 3, 1, 3].length) (baseStart_1668128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1668128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1668128 prefixEnd_1668128 := by exact prefixLift 1668128
  have htrace : WordTrace (prefixWord ++ tailWord_1668128) baseStart_1668128 baseEnd_1668128 := by
    simpa [prefixWord, tailWord_1668128, baseEnd_1668128] using wordTrace_append hprefix tailTrace_1668128
  have hstable : (prefixWord ++ tailWord_1668128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1668128).length < 2 ^ (prefixWord ++ tailWord_1668128).sum := by decide
  have hdescent : baseEnd_1668128 < baseStart_1668128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1668128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1668152 : List Nat := [2, 1, 2, 1, 5, 2, 2, 1, 6]
def baseStart_1668152 : Nat := 118140960795 + 1668152 * 2 ^ 59
def prefixEnd_1668152 : Nat := 4983230072969 + 3 ^ 40 * 1668152 * 2
def baseEnd_1668152 : Nat := 190347506835347240295181

theorem tailTrace_1668152 : CollatzResearch.WordTrace tailWord_1668152 prefixEnd_1668152 190347506835347240295181 := by
  unfold tailWord_1668152
  simp only [CollatzResearch.WordTrace]
  refine ⟨30421250926288838262423355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40561667901718451016564473 30421250926288838262423355)
  ·
    refine ⟨45631876389433257393635033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30421250926288838262423355 45631876389433257393635033)
    ·
      refine ⟨34223907292074943045226275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45631876389433257393635033 34223907292074943045226275)
      ·
        refine ⟨51335860938112414567839413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34223907292074943045226275 51335860938112414567839413)
        ·
          refine ⟨4812736962948038865734945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 51335860938112414567839413 4812736962948038865734945)
          ·
            refine ⟨3609552722211029149301209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4812736962948038865734945 3609552722211029149301209)
            ·
              refine ⟨2707164541658271861975907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3609552722211029149301209 2707164541658271861975907)
              ·
                refine ⟨4060746812487407792963861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2707164541658271861975907 4060746812487407792963861)
                ·
                  refine ⟨190347506835347240295181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4060746812487407792963861 190347506835347240295181)
                  ·
                    rfl

theorem cell22_1668152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 2, 1, 6].length) (baseStart_1668152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1668152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1668152 prefixEnd_1668152 := by exact prefixLift 1668152
  have htrace : WordTrace (prefixWord ++ tailWord_1668152) baseStart_1668152 baseEnd_1668152 := by
    simpa [prefixWord, tailWord_1668152, baseEnd_1668152] using wordTrace_append hprefix tailTrace_1668152
  have hstable : (prefixWord ++ tailWord_1668152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1668152).length < 2 ^ (prefixWord ++ tailWord_1668152).sum := by decide
  have hdescent : baseEnd_1668152 < baseStart_1668152 := by decide
  rcases family_descends (prefixWord ++ tailWord_1668152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1668165 : List Nat := [1, 3, 1, 1, 1, 3, 3, 2, 1, 6]
def baseStart_1668165 : Nat := 118140960795 + 1668165 * 2 ^ 59
def prefixEnd_1668165 : Nat := 4983230072969 + 3 ^ 40 * 1668165 * 2
def baseEnd_1668165 : Nat := 571046970671714020310503

theorem tailTrace_1668165 : CollatzResearch.WordTrace tailWord_1668165 prefixEnd_1668165 571046970671714020310503 := by
  unfold tailWord_1668165
  simp only [CollatzResearch.WordTrace]
  refine ⟨60842976001530579745069949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40561984001020386496713299 60842976001530579745069949)
  ·
    refine ⟨22816116000573967404401231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60842976001530579745069949 22816116000573967404401231)
    ·
      refine ⟨34224174000860951106601847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22816116000573967404401231 34224174000860951106601847)
      ·
        refine ⟨51336261001291426659902771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34224174000860951106601847 51336261001291426659902771)
        ·
          refine ⟨77004391501937139989854157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51336261001291426659902771 77004391501937139989854157)
          ·
            refine ⟨28876646813226427496195309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77004391501937139989854157 28876646813226427496195309)
            ·
              refine ⟨10828742554959910311073241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28876646813226427496195309 10828742554959910311073241)
              ·
                refine ⟨8121556916219932733304931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10828742554959910311073241 8121556916219932733304931)
                ·
                  refine ⟨12182335374329899099957397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8121556916219932733304931 12182335374329899099957397)
                  ·
                    refine ⟨571046970671714020310503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12182335374329899099957397 571046970671714020310503)
                    ·
                      rfl

theorem cell22_1668165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 2, 1, 6].length) (baseStart_1668165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1668165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1668165 prefixEnd_1668165 := by exact prefixLift 1668165
  have htrace : WordTrace (prefixWord ++ tailWord_1668165) baseStart_1668165 baseEnd_1668165 := by
    simpa [prefixWord, tailWord_1668165, baseEnd_1668165] using wordTrace_append hprefix tailTrace_1668165
  have hstable : (prefixWord ++ tailWord_1668165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1668165).length < 2 ^ (prefixWord ++ tailWord_1668165).sum := by decide
  have hdescent : baseEnd_1668165 < baseStart_1668165 := by decide
  rcases family_descends (prefixWord ++ tailWord_1668165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1668167 : List Nat := [1, 1, 4, 1, 3, 2, 3, 1, 1, 5]
def baseStart_1668167 : Nat := 118140960795 + 1668167 * 2 ^ 59
def prefixEnd_1668167 : Nat := 4983230072969 + 3 ^ 40 * 1668167 * 2
def baseEnd_1668167 : Nat := 571047655312586681760497

theorem tailTrace_1668167 : CollatzResearch.WordTrace tailWord_1668167 prefixEnd_1668167 571047655312586681760497 := by
  unfold tailWord_1668167
  simp only [CollatzResearch.WordTrace]
  refine ⟨60843048947523334086642755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40562032631682222724428503 60843048947523334086642755)
  ·
    refine ⟨91264573421285001129964133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60843048947523334086642755 91264573421285001129964133)
    ·
      refine ⟨17112107516490937711868275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91264573421285001129964133 17112107516490937711868275)
      ·
        refine ⟨25668161274736406567802413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17112107516490937711868275 25668161274736406567802413)
        ·
          refine ⟨9625560478026152462925905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25668161274736406567802413 9625560478026152462925905)
          ·
            refine ⟨7219170358519614347194429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9625560478026152462925905 7219170358519614347194429)
            ·
              refine ⟨2707188884444855380197911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7219170358519614347194429 2707188884444855380197911)
              ·
                refine ⟨4060783326667283070296867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2707188884444855380197911 4060783326667283070296867)
                ·
                  refine ⟨6091174990000924605445301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4060783326667283070296867 6091174990000924605445301)
                  ·
                    refine ⟨571047655312586681760497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6091174990000924605445301 571047655312586681760497)
                    ·
                      rfl

theorem cell22_1668167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 3, 1, 1, 5].length) (baseStart_1668167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1668167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1668167 prefixEnd_1668167 := by exact prefixLift 1668167
  have htrace : WordTrace (prefixWord ++ tailWord_1668167) baseStart_1668167 baseEnd_1668167 := by
    simpa [prefixWord, tailWord_1668167, baseEnd_1668167] using wordTrace_append hprefix tailTrace_1668167
  have hstable : (prefixWord ++ tailWord_1668167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1668167).length < 2 ^ (prefixWord ++ tailWord_1668167).sum := by decide
  have hdescent : baseEnd_1668167 < baseStart_1668167 := by decide
  rcases family_descends (prefixWord ++ tailWord_1668167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1668222 : List Nat := [4, 2, 4, 1, 2, 1, 1, 2, 1, 4]
def baseStart_1668222 : Nat := 118140960795 + 1668222 * 2 ^ 59
def prefixEnd_1668222 : Nat := 4983230072969 + 3 ^ 40 * 1668222 * 2
def baseEnd_1668222 : Nat := 571066482936584871635329

theorem tailTrace_1668222 : CollatzResearch.WordTrace tailWord_1668222 prefixEnd_1668222 571066482936584871635329 := by
  unfold tailWord_1668222
  simp only [CollatzResearch.WordTrace]
  refine ⟨7605631870290509809986865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40563369974882718986596613 7605631870290509809986865)
  ·
    refine ⟨5704223902717882357490149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7605631870290509809986865 5704223902717882357490149)
    ·
      refine ⟨1069541981759602942029403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5704223902717882357490149 1069541981759602942029403)
      ·
        refine ⟨1604312972639404413044105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1069541981759602942029403 1604312972639404413044105)
        ·
          refine ⟨1203234729479553309783079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1604312972639404413044105 1203234729479553309783079)
          ·
            refine ⟨1804852094219329964674619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1203234729479553309783079 1804852094219329964674619)
            ·
              refine ⟨2707278141328994947011929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1804852094219329964674619 2707278141328994947011929)
              ·
                refine ⟨2030458605996746210258947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2707278141328994947011929 2030458605996746210258947)
                ·
                  refine ⟨3045687908995119315388421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2030458605996746210258947 3045687908995119315388421)
                  ·
                    refine ⟨571066482936584871635329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3045687908995119315388421 571066482936584871635329)
                    ·
                      rfl

theorem cell22_1668222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_1668222 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1668222 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1668222 prefixEnd_1668222 := by exact prefixLift 1668222
  have htrace : WordTrace (prefixWord ++ tailWord_1668222) baseStart_1668222 baseEnd_1668222 := by
    simpa [prefixWord, tailWord_1668222, baseEnd_1668222] using wordTrace_append hprefix tailTrace_1668222
  have hstable : (prefixWord ++ tailWord_1668222).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1668222).length < 2 ^ (prefixWord ++ tailWord_1668222).sum := by decide
  have hdescent : baseEnd_1668222 < baseStart_1668222 := by decide
  rcases family_descends (prefixWord ++ tailWord_1668222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1668240 : List Nat := [2, 1, 1, 1, 1, 1, 4, 1, 3, 7]
def baseStart_1668240 : Nat := 118140960795 + 1668240 * 2 ^ 59
def prefixEnd_1668240 : Nat := 4983230072969 + 3 ^ 40 * 1668240 * 2
def baseEnd_1668240 : Nat := 571072644704438824685273

theorem tailTrace_1668240 : CollatzResearch.WordTrace tailWord_1668240 prefixEnd_1668240 571072644704438824685273 := by
  unfold tailWord_1668240
  simp only [CollatzResearch.WordTrace]
  refine ⟨30422855738129433777025087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40563807650839245036033449 30422855738129433777025087)
  ·
    refine ⟨45634283607194150665537631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30422855738129433777025087 45634283607194150665537631)
    ·
      refine ⟨68451425410791225998306447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45634283607194150665537631 68451425410791225998306447)
      ·
        refine ⟨102677138116186838997459671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68451425410791225998306447 102677138116186838997459671)
        ·
          refine ⟨154015707174280258496189507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102677138116186838997459671 154015707174280258496189507)
          ·
            refine ⟨231023560761420387744284261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154015707174280258496189507 231023560761420387744284261)
            ·
              refine ⟨43316917642766322702053299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 231023560761420387744284261 43316917642766322702053299)
              ·
                refine ⟨64975376464149484053079949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43316917642766322702053299 64975376464149484053079949)
                ·
                  refine ⟨24365766174056056519904981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64975376464149484053079949 24365766174056056519904981)
                  ·
                    refine ⟨571072644704438824685273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24365766174056056519904981 571072644704438824685273)
                    ·
                      rfl

theorem cell22_1668240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 3, 7].length) (baseStart_1668240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1668240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1668240 prefixEnd_1668240 := by exact prefixLift 1668240
  have htrace : WordTrace (prefixWord ++ tailWord_1668240) baseStart_1668240 baseEnd_1668240 := by
    simpa [prefixWord, tailWord_1668240, baseEnd_1668240] using wordTrace_append hprefix tailTrace_1668240
  have hstable : (prefixWord ++ tailWord_1668240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1668240).length < 2 ^ (prefixWord ++ tailWord_1668240).sum := by decide
  have hdescent : baseEnd_1668240 < baseStart_1668240 := by decide
  rcases family_descends (prefixWord ++ tailWord_1668240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1668257 : List Nat := [1, 2, 3, 3, 1, 1, 2, 2, 2, 5]
def baseStart_1668257 : Nat := 118140960795 + 1668257 * 2 ^ 59
def prefixEnd_1668257 : Nat := 4983230072969 + 3 ^ 40 * 1668257 * 2
def baseEnd_1668257 : Nat := 571078464151856447010221

theorem tailTrace_1668257 : CollatzResearch.WordTrace tailWord_1668257 prefixEnd_1668257 571078464151856447010221 := by
  unfold tailWord_1668257
  simp only [CollatzResearch.WordTrace]
  refine ⟨60846331517197279457419025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40564221011464852971612683 60846331517197279457419025)
  ·
    refine ⟨45634748637897959593064269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60846331517197279457419025 45634748637897959593064269)
    ·
      refine ⟨17113030739211734847399101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45634748637897959593064269 17113030739211734847399101)
      ·
        refine ⟨6417386527204400567774663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17113030739211734847399101 6417386527204400567774663)
        ·
          refine ⟨9626079790806600851661995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6417386527204400567774663 9626079790806600851661995)
          ·
            refine ⟨14439119686209901277492993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9626079790806600851661995 14439119686209901277492993)
            ·
              refine ⟨10829339764657425958119745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14439119686209901277492993 10829339764657425958119745)
              ·
                refine ⟨8122004823493069468589809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10829339764657425958119745 8122004823493069468589809)
                ·
                  refine ⟨6091503617619802101442357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8122004823493069468589809 6091503617619802101442357)
                  ·
                    refine ⟨571078464151856447010221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6091503617619802101442357 571078464151856447010221)
                    ·
                      rfl

theorem cell22_1668257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 2, 2, 5].length) (baseStart_1668257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1668257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1668257 prefixEnd_1668257 := by exact prefixLift 1668257
  have htrace : WordTrace (prefixWord ++ tailWord_1668257) baseStart_1668257 baseEnd_1668257 := by
    simpa [prefixWord, tailWord_1668257, baseEnd_1668257] using wordTrace_append hprefix tailTrace_1668257
  have hstable : (prefixWord ++ tailWord_1668257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1668257).length < 2 ^ (prefixWord ++ tailWord_1668257).sum := by decide
  have hdescent : baseEnd_1668257 < baseStart_1668257 := by decide
  rcases family_descends (prefixWord ++ tailWord_1668257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1668263 : List Nat := [1, 1, 6, 2, 1, 2, 1, 4, 1, 3]
def baseStart_1668263 : Nat := 118140960795 + 1668263 * 2 ^ 59
def prefixEnd_1668263 : Nat := 4983230072969 + 3 ^ 40 * 1668263 * 2
def baseEnd_1668263 : Nat := 571080518074474431360203

theorem tailTrace_1668263 : CollatzResearch.WordTrace tailWord_1668263 prefixEnd_1668263 571080518074474431360203 := by
  unfold tailWord_1668263
  simp only [CollatzResearch.WordTrace]
  refine ⟨60846550355175542482137443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40564366903450361654758295 60846550355175542482137443)
  ·
    refine ⟨91269825532763313723206165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60846550355175542482137443 91269825532763313723206165)
    ·
      refine ⟨4278273071848280330775289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 91269825532763313723206165 4278273071848280330775289)
      ·
        refine ⟨3208704803886210248081467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4278273071848280330775289 3208704803886210248081467)
        ·
          refine ⟨4813057205829315372122201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3208704803886210248081467 4813057205829315372122201)
          ·
            refine ⟨3609792904371986529091651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4813057205829315372122201 3609792904371986529091651)
            ·
              refine ⟨5414689356557979793637477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3609792904371986529091651 5414689356557979793637477)
              ·
                refine ⟨1015254254354621211307027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5414689356557979793637477 1015254254354621211307027)
                ·
                  refine ⟨1522881381531931816960541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1015254254354621211307027 1522881381531931816960541)
                  ·
                    refine ⟨571080518074474431360203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1522881381531931816960541 571080518074474431360203)
                    ·
                      rfl

theorem cell22_1668263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 4, 1, 3].length) (baseStart_1668263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1668263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1668263 prefixEnd_1668263 := by exact prefixLift 1668263
  have htrace : WordTrace (prefixWord ++ tailWord_1668263) baseStart_1668263 baseEnd_1668263 := by
    simpa [prefixWord, tailWord_1668263, baseEnd_1668263] using wordTrace_append hprefix tailTrace_1668263
  have hstable : (prefixWord ++ tailWord_1668263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1668263).length < 2 ^ (prefixWord ++ tailWord_1668263).sum := by decide
  have hdescent : baseEnd_1668263 < baseStart_1668263 := by decide
  rcases family_descends (prefixWord ++ tailWord_1668263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1668310 : List Nat := [5, 2, 1, 2, 3, 1, 1, 2, 5]
def baseStart_1668310 : Nat := 118140960795 + 1668310 * 2 ^ 59
def prefixEnd_1668310 : Nat := 4983230072969 + 3 ^ 40 * 1668310 * 2
def baseEnd_1668310 : Nat := 190365535711660658478353

theorem tailTrace_1668310 : CollatzResearch.WordTrace tailWord_1668310 prefixEnd_1668310 190365535711660658478353 := by
  unfold tailWord_1668310
  simp only [CollatzResearch.WordTrace]
  refine ⟨3803016536625329344318649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40565509724003513006065589 3803016536625329344318649)
  ·
    refine ⟨2852262402468997008238987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3803016536625329344318649 2852262402468997008238987)
    ·
      refine ⟨4278393603703495512358481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2852262402468997008238987 4278393603703495512358481)
      ·
        refine ⟨3208795202777621634268861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4278393603703495512358481 3208795202777621634268861)
        ·
          refine ⟨1203298201041608112850823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3208795202777621634268861 1203298201041608112850823)
          ·
            refine ⟨1804947301562412169276235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1203298201041608112850823 1804947301562412169276235)
            ·
              refine ⟨2707420952343618253914353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1804947301562412169276235 2707420952343618253914353)
              ·
                refine ⟨2030565714257713690435765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2707420952343618253914353 2030565714257713690435765)
                ·
                  refine ⟨190365535711660658478353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2030565714257713690435765 190365535711660658478353)
                  ·
                    rfl

theorem cell22_1668310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 1, 2, 5].length) (baseStart_1668310 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1668310 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1668310 prefixEnd_1668310 := by exact prefixLift 1668310
  have htrace : WordTrace (prefixWord ++ tailWord_1668310) baseStart_1668310 baseEnd_1668310 := by
    simpa [prefixWord, tailWord_1668310, baseEnd_1668310] using wordTrace_append hprefix tailTrace_1668310
  have hstable : (prefixWord ++ tailWord_1668310).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1668310).length < 2 ^ (prefixWord ++ tailWord_1668310).sum := by decide
  have hdescent : baseEnd_1668310 < baseStart_1668310 := by decide
  rcases family_descends (prefixWord ++ tailWord_1668310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1668362 : List Nat := [3, 1, 2, 2, 1, 1, 1, 2, 1, 8]
def baseStart_1668362 : Nat := 118140960795 + 1668362 * 2 ^ 59
def prefixEnd_1668362 : Nat := 4983230072969 + 3 ^ 40 * 1668362 * 2
def baseEnd_1668362 : Nat := 571114407797671173134899

theorem tailTrace_1668362 : CollatzResearch.WordTrace tailWord_1668362 prefixEnd_1668362 571114407797671173134899 := by
  unfold tailWord_1668362
  simp only [CollatzResearch.WordTrace]
  refine ⟨15212540295454220597497835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40566774121211254926660893 15212540295454220597497835)
  ·
    refine ⟨22818810443181330896246753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15212540295454220597497835 22818810443181330896246753)
    ·
      refine ⟨17114107832385998172185065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22818810443181330896246753 17114107832385998172185065)
      ·
        refine ⟨12835580874289498629138799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17114107832385998172185065 12835580874289498629138799)
        ·
          refine ⟨19253371311434247943708199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12835580874289498629138799 19253371311434247943708199)
          ·
            refine ⟨28880056967151371915562299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19253371311434247943708199 28880056967151371915562299)
            ·
              refine ⟨43320085450727057873343449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28880056967151371915562299 43320085450727057873343449)
              ·
                refine ⟨32490064088045293405007587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43320085450727057873343449 32490064088045293405007587)
                ·
                  refine ⟨48735096132067940107511381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32490064088045293405007587 48735096132067940107511381)
                  ·
                    refine ⟨571114407797671173134899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 48735096132067940107511381 571114407797671173134899)
                    ·
                      rfl

theorem cell22_1668362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 2, 1, 8].length) (baseStart_1668362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1668362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1668362 prefixEnd_1668362 := by exact prefixLift 1668362
  have htrace : WordTrace (prefixWord ++ tailWord_1668362) baseStart_1668362 baseEnd_1668362 := by
    simpa [prefixWord, tailWord_1668362, baseEnd_1668362] using wordTrace_append hprefix tailTrace_1668362
  have hstable : (prefixWord ++ tailWord_1668362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1668362).length < 2 ^ (prefixWord ++ tailWord_1668362).sum := by decide
  have hdescent : baseEnd_1668362 < baseStart_1668362 := by decide
  rcases family_descends (prefixWord ++ tailWord_1668362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1668456 : List Nat := [2, 1, 4, 2, 3, 1, 1, 2, 6]
def baseStart_1668456 : Nat := 118140960795 + 1668456 * 2 ^ 59
def prefixEnd_1668456 : Nat := 4983230072969 + 3 ^ 40 * 1668456 * 2
def baseEnd_1668456 : Nat := 190382195306228753761537

theorem tailTrace_1668456 : CollatzResearch.WordTrace tailWord_1668456 prefixEnd_1668456 190382195306228753761537 := by
  unfold tailWord_1668456
  simp only [CollatzResearch.WordTrace]
  refine ⟨30426794821738168221956611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40569059762317557629275481 30426794821738168221956611)
  ·
    refine ⟨45640192232607252332934917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30426794821738168221956611 45640192232607252332934917)
    ·
      refine ⟨8557536043613859812425297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45640192232607252332934917 8557536043613859812425297)
      ·
        refine ⟨6418152032710394859318973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8557536043613859812425297 6418152032710394859318973)
        ·
          refine ⟨2406807012266398072244615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6418152032710394859318973 2406807012266398072244615)
          ·
            refine ⟨3610210518399597108366923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2406807012266398072244615 3610210518399597108366923)
            ·
              refine ⟨5415315777599395662550385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3610210518399597108366923 5415315777599395662550385)
              ·
                refine ⟨4061486833199546746912789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5415315777599395662550385 4061486833199546746912789)
                ·
                  refine ⟨190382195306228753761537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4061486833199546746912789 190382195306228753761537)
                  ·
                    rfl

theorem cell22_1668456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 2, 6].length) (baseStart_1668456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1668456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1668456 prefixEnd_1668456 := by exact prefixLift 1668456
  have htrace : WordTrace (prefixWord ++ tailWord_1668456) baseStart_1668456 baseEnd_1668456 := by
    simpa [prefixWord, tailWord_1668456, baseEnd_1668456] using wordTrace_append hprefix tailTrace_1668456
  have hstable : (prefixWord ++ tailWord_1668456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1668456).length < 2 ^ (prefixWord ++ tailWord_1668456).sum := by decide
  have hdescent : baseEnd_1668456 < baseStart_1668456 := by decide
  rcases family_descends (prefixWord ++ tailWord_1668456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1668484 : List Nat := [2, 3, 2, 1, 1, 4, 9]
def baseStart_1668484 : Nat := 118140960795 + 1668484 * 2 ^ 59
def prefixEnd_1668484 : Nat := 4983230072969 + 3 ^ 40 * 1668484 * 2
def baseEnd_1668484 : Nat := 21153932255218648947575

theorem tailTrace_1668484 : CollatzResearch.WordTrace tailWord_1668484 prefixEnd_1668484 21153932255218648947575 := by
  unfold tailWord_1668484
  simp only [CollatzResearch.WordTrace]
  refine ⟨30427305443687448612966253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40569740591583264817288337 30427305443687448612966253)
  ·
    refine ⟨11410239541382793229862345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30427305443687448612966253 11410239541382793229862345)
    ·
      refine ⟨8557679656037094922396759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11410239541382793229862345 8557679656037094922396759)
      ·
        refine ⟨12836519484055642383595139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8557679656037094922396759 12836519484055642383595139)
        ·
          refine ⟨19254779226083463575392709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12836519484055642383595139 19254779226083463575392709)
          ·
            refine ⟨3610271104890649420386133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19254779226083463575392709 3610271104890649420386133)
            ·
              refine ⟨21153932255218648947575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3610271104890649420386133 21153932255218648947575)
              ·
                rfl

theorem cell22_1668484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 9].length) (baseStart_1668484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1668484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1668484 prefixEnd_1668484 := by exact prefixLift 1668484
  have htrace : WordTrace (prefixWord ++ tailWord_1668484) baseStart_1668484 baseEnd_1668484 := by
    simpa [prefixWord, tailWord_1668484, baseEnd_1668484] using wordTrace_append hprefix tailTrace_1668484
  have hstable : (prefixWord ++ tailWord_1668484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1668484).length < 2 ^ (prefixWord ++ tailWord_1668484).sum := by decide
  have hdescent : baseEnd_1668484 < baseStart_1668484 := by decide
  rcases family_descends (prefixWord ++ tailWord_1668484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1668488 : List Nat := [2, 1, 3, 3, 1, 2, 3, 2, 2, 3]
def baseStart_1668488 : Nat := 118140960795 + 1668488 * 2 ^ 59
def prefixEnd_1668488 : Nat := 4983230072969 + 3 ^ 40 * 1668488 * 2
def baseEnd_1668488 : Nat := 571157540172648844484513

theorem tailTrace_1668488 : CollatzResearch.WordTrace tailWord_1668488 prefixEnd_1668488 571157540172648844484513 := by
  unfold tailWord_1668488
  simp only [CollatzResearch.WordTrace]
  refine ⟨30427378389680202954539059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40569837852906937272718745 30427378389680202954539059)
  ·
    refine ⟨45641067584520304431808589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30427378389680202954539059 45641067584520304431808589)
    ·
      refine ⟨17115400344195114161928221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45641067584520304431808589 17115400344195114161928221)
      ·
        refine ⟨6418275129073167810723083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17115400344195114161928221 6418275129073167810723083)
        ·
          refine ⟨9627412693609751716084625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6418275129073167810723083 9627412693609751716084625)
          ·
            refine ⟨7220559520207313787063469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9627412693609751716084625 7220559520207313787063469)
            ·
              refine ⟨2707709820077742670148801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7220559520207313787063469 2707709820077742670148801)
              ·
                refine ⟨2030782365058307002611601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2707709820077742670148801 2030782365058307002611601)
                ·
                  refine ⟨1523086773793730251958701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2030782365058307002611601 1523086773793730251958701)
                  ·
                    refine ⟨571157540172648844484513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1523086773793730251958701 571157540172648844484513)
                    ·
                      rfl

theorem cell22_1668488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 3, 2, 2, 3].length) (baseStart_1668488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1668488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1668488 prefixEnd_1668488 := by exact prefixLift 1668488
  have htrace : WordTrace (prefixWord ++ tailWord_1668488) baseStart_1668488 baseEnd_1668488 := by
    simpa [prefixWord, tailWord_1668488, baseEnd_1668488] using wordTrace_append hprefix tailTrace_1668488
  have hstable : (prefixWord ++ tailWord_1668488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1668488).length < 2 ^ (prefixWord ++ tailWord_1668488).sum := by decide
  have hdescent : baseEnd_1668488 < baseStart_1668488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1668488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1668529 : List Nat := [1, 2, 2, 4, 1, 1, 1, 1, 9]
def baseStart_1668529 : Nat := 118140960795 + 1668529 * 2 ^ 59
def prefixEnd_1668529 : Nat := 4983230072969 + 3 ^ 40 * 1668529 * 2
def baseEnd_1668529 : Nat := 190390525103512801403129

theorem tailTrace_1668529 : CollatzResearch.WordTrace tailWord_1668529 prefixEnd_1668529 190390525103512801403129 := by
  unfold tailWord_1668529
  simp only [CollatzResearch.WordTrace]
  refine ⟨60856252172211869911320641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40570834781474579940880427 60856252172211869911320641)
  ·
    refine ⟨45642189129158902433490481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60856252172211869911320641 45642189129158902433490481)
    ·
      refine ⟨34231641846869176825117861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45642189129158902433490481 34231641846869176825117861)
      ·
        refine ⟨6418432846287970654709599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34231641846869176825117861 6418432846287970654709599)
        ·
          refine ⟨9627649269431955982064399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6418432846287970654709599 9627649269431955982064399)
          ·
            refine ⟨14441473904147933973096599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9627649269431955982064399 14441473904147933973096599)
            ·
              refine ⟨21662210856221900959644899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14441473904147933973096599 21662210856221900959644899)
              ·
                refine ⟨32493316284332851439467349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21662210856221900959644899 32493316284332851439467349)
                ·
                  refine ⟨190390525103512801403129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 32493316284332851439467349 190390525103512801403129)
                  ·
                    rfl

theorem cell22_1668529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 1, 9].length) (baseStart_1668529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1668529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1668529 prefixEnd_1668529 := by exact prefixLift 1668529
  have htrace : WordTrace (prefixWord ++ tailWord_1668529) baseStart_1668529 baseEnd_1668529 := by
    simpa [prefixWord, tailWord_1668529, baseEnd_1668529] using wordTrace_append hprefix tailTrace_1668529
  have hstable : (prefixWord ++ tailWord_1668529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1668529).length < 2 ^ (prefixWord ++ tailWord_1668529).sum := by decide
  have hdescent : baseEnd_1668529 < baseStart_1668529 := by decide
  rcases family_descends (prefixWord ++ tailWord_1668529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1668544 : List Nat := [2, 1, 1, 2, 3, 1, 2, 1, 4, 5]
def baseStart_1668544 : Nat := 118140960795 + 1668544 * 2 ^ 59
def prefixEnd_1668544 : Nat := 4983230072969 + 3 ^ 40 * 1668544 * 2
def baseEnd_1668544 : Nat := 571176710117083365084341

theorem tailTrace_1668544 : CollatzResearch.WordTrace tailWord_1668544 prefixEnd_1668544 571176710117083365084341 := by
  unfold tailWord_1668544
  simp only [CollatzResearch.WordTrace]
  refine ⟨30428399633578763736558343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40571199511438351648744457 30428399633578763736558343)
  ·
    refine ⟨45642599450368145604837515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30428399633578763736558343 45642599450368145604837515)
    ·
      refine ⟨68463899175552218407256273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45642599450368145604837515 68463899175552218407256273)
      ·
        refine ⟨51347924381664163805442205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68463899175552218407256273 51347924381664163805442205)
        ·
          refine ⟨19255471643124061427040827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51347924381664163805442205 19255471643124061427040827)
          ·
            refine ⟨28883207464686092140561241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19255471643124061427040827 28883207464686092140561241)
            ·
              refine ⟨21662405598514569105420931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28883207464686092140561241 21662405598514569105420931)
              ·
                refine ⟨32493608397771853658131397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21662405598514569105420931 32493608397771853658131397)
                ·
                  refine ⟨6092551574582222560899637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32493608397771853658131397 6092551574582222560899637)
                  ·
                    refine ⟨571176710117083365084341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6092551574582222560899637 571176710117083365084341)
                    ·
                      rfl

theorem cell22_1668544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 4, 5].length) (baseStart_1668544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1668544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1668544 prefixEnd_1668544 := by exact prefixLift 1668544
  have htrace : WordTrace (prefixWord ++ tailWord_1668544) baseStart_1668544 baseEnd_1668544 := by
    simpa [prefixWord, tailWord_1668544, baseEnd_1668544] using wordTrace_append hprefix tailTrace_1668544
  have hstable : (prefixWord ++ tailWord_1668544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1668544).length < 2 ^ (prefixWord ++ tailWord_1668544).sum := by decide
  have hdescent : baseEnd_1668544 < baseStart_1668544 := by decide
  rcases family_descends (prefixWord ++ tailWord_1668544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1668576 : List Nat := [2, 1, 1, 3, 1, 1, 2, 6, 1, 4]
def baseStart_1668576 : Nat := 118140960795 + 1668576 * 2 ^ 59
def prefixEnd_1668576 : Nat := 4983230072969 + 3 ^ 40 * 1668576 * 2
def baseEnd_1668576 : Nat := 571187664371045948284243

theorem tailTrace_1668576 : CollatzResearch.WordTrace tailWord_1668576 prefixEnd_1668576 571187664371045948284243 := by
  unfold tailWord_1668576
  simp only [CollatzResearch.WordTrace]
  refine ⟨30428983201520798469140791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40571977602027731292187721 30428983201520798469140791)
  ·
    refine ⟨45643474802281197703711187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30428983201520798469140791 45643474802281197703711187)
    ·
      refine ⟨68465212203421796555566781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45643474802281197703711187 68465212203421796555566781)
      ·
        refine ⟨25674454576283173708337543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68465212203421796555566781 25674454576283173708337543)
        ·
          refine ⟨38511681864424760562506315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25674454576283173708337543 38511681864424760562506315)
          ·
            refine ⟨57767522796637140843759473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38511681864424760562506315 57767522796637140843759473)
            ·
              refine ⟨43325642097477855632819605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57767522796637140843759473 43325642097477855632819605)
              ·
                refine ⟨2030889473319274482788419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 43325642097477855632819605 2030889473319274482788419)
                ·
                  refine ⟨3046334209978911724182629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2030889473319274482788419 3046334209978911724182629)
                  ·
                    refine ⟨571187664371045948284243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3046334209978911724182629 571187664371045948284243)
                    ·
                      rfl

theorem cell22_1668576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 6, 1, 4].length) (baseStart_1668576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1668576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1668576 prefixEnd_1668576 := by exact prefixLift 1668576
  have htrace : WordTrace (prefixWord ++ tailWord_1668576) baseStart_1668576 baseEnd_1668576 := by
    simpa [prefixWord, tailWord_1668576, baseEnd_1668576] using wordTrace_append hprefix tailTrace_1668576
  have hstable : (prefixWord ++ tailWord_1668576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1668576).length < 2 ^ (prefixWord ++ tailWord_1668576).sum := by decide
  have hdescent : baseEnd_1668576 < baseStart_1668576 := by decide
  rcases family_descends (prefixWord ++ tailWord_1668576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1668681 : List Nat := [1, 2, 1, 1, 2, 2, 1, 7, 5]
def baseStart_1668681 : Nat := 118140960795 + 1668681 * 2 ^ 59
def prefixEnd_1668681 : Nat := 4983230072969 + 3 ^ 40 * 1668681 * 2
def baseEnd_1668681 : Nat := 190407869338953558136307

theorem tailTrace_1668681 : CollatzResearch.WordTrace tailWord_1668681 prefixEnd_1668681 190407869338953558136307 := by
  unfold tailWord_1668681
  simp only [CollatzResearch.WordTrace]
  refine ⟨60861796067661199870853897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40574530711774133247235931 60861796067661199870853897)
  ·
    refine ⟨45646347050745899903140423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60861796067661199870853897 45646347050745899903140423)
    ·
      refine ⟨68469520576118849854710635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45646347050745899903140423 68469520576118849854710635)
      ·
        refine ⟨102704280864178274782065953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68469520576118849854710635 102704280864178274782065953)
        ·
          refine ⟨77028210648133706086549465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102704280864178274782065953 77028210648133706086549465)
          ·
            refine ⟨57771157986100279564912099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77028210648133706086549465 57771157986100279564912099)
            ·
              refine ⟨86656736979150419347368149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57771157986100279564912099 86656736979150419347368149)
              ·
                refine ⟨2031017272948837953453941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 86656736979150419347368149 2031017272948837953453941)
                ·
                  refine ⟨190407869338953558136307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2031017272948837953453941 190407869338953558136307)
                  ·
                    rfl

theorem cell22_1668681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 7, 5].length) (baseStart_1668681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1668681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1668681 prefixEnd_1668681 := by exact prefixLift 1668681
  have htrace : WordTrace (prefixWord ++ tailWord_1668681) baseStart_1668681 baseEnd_1668681 := by
    simpa [prefixWord, tailWord_1668681, baseEnd_1668681] using wordTrace_append hprefix tailTrace_1668681
  have hstable : (prefixWord ++ tailWord_1668681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1668681).length < 2 ^ (prefixWord ++ tailWord_1668681).sum := by decide
  have hdescent : baseEnd_1668681 < baseStart_1668681 := by decide
  rcases family_descends (prefixWord ++ tailWord_1668681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1668773 : List Nat := [1, 3, 1, 2, 1, 2, 4, 2, 2, 4]
def baseStart_1668773 : Nat := 118140960795 + 1668773 * 2 ^ 59
def prefixEnd_1668773 : Nat := 4983230072969 + 3 ^ 40 * 1668773 * 2
def baseEnd_1668773 : Nat := 571255101497003101108639

theorem tailTrace_1668773 : CollatzResearch.WordTrace tailWord_1668773 prefixEnd_1668773 571255101497003101108639 := by
  unfold tailWord_1668773
  simp only [CollatzResearch.WordTrace]
  refine ⟨60865151583327899583202973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40576767722218599722135315 60865151583327899583202973)
  ·
    refine ⟨22824431843747962343701115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60865151583327899583202973 22824431843747962343701115)
    ·
      refine ⟨34236647765621943515551673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22824431843747962343701115 34236647765621943515551673)
      ·
        refine ⟨25677485824216457636663755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34236647765621943515551673 25677485824216457636663755)
        ·
          refine ⟨38516228736324686454995633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25677485824216457636663755 38516228736324686454995633)
          ·
            refine ⟨28887171552243514841246725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38516228736324686454995633 28887171552243514841246725)
            ·
              refine ⟨5416344666045659032733761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28887171552243514841246725 5416344666045659032733761)
              ·
                refine ⟨4062258499534244274550321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5416344666045659032733761 4062258499534244274550321)
                ·
                  refine ⟨3046693874650683205912741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4062258499534244274550321 3046693874650683205912741)
                  ·
                    refine ⟨571255101497003101108639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3046693874650683205912741 571255101497003101108639)
                    ·
                      rfl

theorem cell22_1668773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 2, 2, 4].length) (baseStart_1668773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1668773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1668773 prefixEnd_1668773 := by exact prefixLift 1668773
  have htrace : WordTrace (prefixWord ++ tailWord_1668773) baseStart_1668773 baseEnd_1668773 := by
    simpa [prefixWord, tailWord_1668773, baseEnd_1668773] using wordTrace_append hprefix tailTrace_1668773
  have hstable : (prefixWord ++ tailWord_1668773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1668773).length < 2 ^ (prefixWord ++ tailWord_1668773).sum := by decide
  have hdescent : baseEnd_1668773 < baseStart_1668773 := by decide
  rcases family_descends (prefixWord ++ tailWord_1668773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1668822 : List Nat := [5, 2, 1, 3, 1, 1, 9]
def baseStart_1668822 : Nat := 118140960795 + 1668822 * 2 ^ 59
def prefixEnd_1668822 : Nat := 4983230072969 + 3 ^ 40 * 1668822 * 2
def baseEnd_1668822 : Nat := 21158217599940122467907

theorem tailTrace_1668822 : CollatzResearch.WordTrace tailWord_1668822 prefixEnd_1668822 21158217599940122467907 := by
  unfold tailWord_1668822
  simp only [CollatzResearch.WordTrace]
  refine ⟨3804183672509398809483545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40577959173433587301157813 3804183672509398809483545)
  ·
    refine ⟨2853137754382049107112659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3804183672509398809483545 2853137754382049107112659)
    ·
      refine ⟨4279706631573073660668989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2853137754382049107112659 4279706631573073660668989)
      ·
        refine ⟨1604889986839902622750871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4279706631573073660668989 1604889986839902622750871)
        ·
          refine ⟨2407334980259853934126307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1604889986839902622750871 2407334980259853934126307)
          ·
            refine ⟨3611002470389780901189461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2407334980259853934126307 3611002470389780901189461)
            ·
              refine ⟨21158217599940122467907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3611002470389780901189461 21158217599940122467907)
              ·
                rfl

theorem cell22_1668822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 9].length) (baseStart_1668822 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1668822 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1668822 prefixEnd_1668822 := by exact prefixLift 1668822
  have htrace : WordTrace (prefixWord ++ tailWord_1668822) baseStart_1668822 baseEnd_1668822 := by
    simpa [prefixWord, tailWord_1668822, baseEnd_1668822] using wordTrace_append hprefix tailTrace_1668822
  have hstable : (prefixWord ++ tailWord_1668822).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1668822).length < 2 ^ (prefixWord ++ tailWord_1668822).sum := by decide
  have hdescent : baseEnd_1668822 < baseStart_1668822 := by decide
  rcases family_descends (prefixWord ++ tailWord_1668822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1668837 : List Nat := [1, 3, 1, 4, 1, 1, 1, 6, 1, 3]
def baseStart_1668837 : Nat := 118140960795 + 1668837 * 2 ^ 59
def prefixEnd_1668837 : Nat := 4983230072969 + 3 ^ 40 * 1668837 * 2
def baseEnd_1668837 : Nat := 571277010004928267508443

theorem tailTrace_1668837 : CollatzResearch.WordTrace tailWord_1668837 prefixEnd_1668837 571277010004928267508443 := by
  unfold tailWord_1668837
  simp only [CollatzResearch.WordTrace]
  refine ⟨60867485855096038513532765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40578323903397359009021843 60867485855096038513532765)
  ·
    refine ⟨22825307195661014442574787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60867485855096038513532765 22825307195661014442574787)
    ·
      refine ⟨34237960793491521663862181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22825307195661014442574787 34237960793491521663862181)
      ·
        refine ⟨6419617648779660311974159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34237960793491521663862181 6419617648779660311974159)
        ·
          refine ⟨9629426473169490467961239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6419617648779660311974159 9629426473169490467961239)
          ·
            refine ⟨14444139709754235701941859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9629426473169490467961239 14444139709754235701941859)
            ·
              refine ⟨21666209564631353552912789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14444139709754235701941859 21666209564631353552912789)
              ·
                refine ⟨1015603573342094697792787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 21666209564631353552912789 1015603573342094697792787)
                ·
                  refine ⟨1523405360013142046689181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1015603573342094697792787 1523405360013142046689181)
                  ·
                    refine ⟨571277010004928267508443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1523405360013142046689181 571277010004928267508443)
                    ·
                      rfl

theorem cell22_1668837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 6, 1, 3].length) (baseStart_1668837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1668837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1668837 prefixEnd_1668837 := by exact prefixLift 1668837
  have htrace : WordTrace (prefixWord ++ tailWord_1668837) baseStart_1668837 baseEnd_1668837 := by
    simpa [prefixWord, tailWord_1668837, baseEnd_1668837] using wordTrace_append hprefix tailTrace_1668837
  have hstable : (prefixWord ++ tailWord_1668837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1668837).length < 2 ^ (prefixWord ++ tailWord_1668837).sum := by decide
  have hdescent : baseEnd_1668837 < baseStart_1668837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1668837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1668863 : List Nat := [1, 1, 2, 2, 1, 3, 2, 3, 3, 4]
def baseStart_1668863 : Nat := 118140960795 + 1668863 * 2 ^ 59
def prefixEnd_1668863 : Nat := 4983230072969 + 3 ^ 40 * 1668863 * 2
def baseEnd_1668863 : Nat := 571285910336272866358363

theorem tailTrace_1668863 : CollatzResearch.WordTrace tailWord_1668863 prefixEnd_1668863 571285910336272866358363 := by
  unfold tailWord_1668863
  simp only [CollatzResearch.WordTrace]
  refine ⟨60868434153001844953979243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40578956102001229969319495 60868434153001844953979243)
  ·
    refine ⟨91302651229502767430968865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60868434153001844953979243 91302651229502767430968865)
    ·
      refine ⟨68476988422127075573226649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91302651229502767430968865 68476988422127075573226649)
      ·
        refine ⟨51357741316595306679919987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68476988422127075573226649 51357741316595306679919987)
        ·
          refine ⟨77036611974892960019879981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51357741316595306679919987 77036611974892960019879981)
          ·
            refine ⟨28888729490584860007454993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77036611974892960019879981 28888729490584860007454993)
            ·
              refine ⟨21666547117938645005591245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28888729490584860007454993 21666547117938645005591245)
              ·
                refine ⟨8124955169226991877096717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21666547117938645005591245 8124955169226991877096717)
                ·
                  refine ⟨3046858188460121953911269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8124955169226991877096717 3046858188460121953911269)
                  ·
                    refine ⟨571285910336272866358363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3046858188460121953911269 571285910336272866358363)
                    ·
                      rfl

theorem cell22_1668863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 3, 3, 4].length) (baseStart_1668863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1668863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1668863 prefixEnd_1668863 := by exact prefixLift 1668863
  have htrace : WordTrace (prefixWord ++ tailWord_1668863) baseStart_1668863 baseEnd_1668863 := by
    simpa [prefixWord, tailWord_1668863, baseEnd_1668863] using wordTrace_append hprefix tailTrace_1668863
  have hstable : (prefixWord ++ tailWord_1668863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1668863).length < 2 ^ (prefixWord ++ tailWord_1668863).sum := by decide
  have hdescent : baseEnd_1668863 < baseStart_1668863 := by decide
  rcases family_descends (prefixWord ++ tailWord_1668863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1668871 : List Nat := [1, 1, 4, 4, 2, 2, 1, 3, 1, 3]
def baseStart_1668871 : Nat := 118140960795 + 1668871 * 2 ^ 59
def prefixEnd_1668871 : Nat := 4983230072969 + 3 ^ 40 * 1668871 * 2
def baseEnd_1668871 : Nat := 571288648899763512158339

theorem tailTrace_1668871 : CollatzResearch.WordTrace tailWord_1668871 prefixEnd_1668871 571288648899763512158339 := by
  unfold tailWord_1668871
  simp only [CollatzResearch.WordTrace]
  refine ⟨60868725936972862320270467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40579150624648574880180311 60868725936972862320270467)
  ·
    refine ⟨91303088905459293480405701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60868725936972862320270467 91303088905459293480405701)
    ·
      refine ⟨17119329169773617527576069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91303088905459293480405701 17119329169773617527576069)
      ·
        refine ⟨3209874219332553286420513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17119329169773617527576069 3209874219332553286420513)
        ·
          refine ⟨2407405664499414964815385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3209874219332553286420513 2407405664499414964815385)
          ·
            refine ⟨1805554248374561223611539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2407405664499414964815385 1805554248374561223611539)
            ·
              refine ⟨2708331372561841835417309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1805554248374561223611539 2708331372561841835417309)
              ·
                refine ⟨1015624264710690688281491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2708331372561841835417309 1015624264710690688281491)
                ·
                  refine ⟨1523436397066036032422237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1015624264710690688281491 1523436397066036032422237)
                  ·
                    refine ⟨571288648899763512158339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1523436397066036032422237 571288648899763512158339)
                    ·
                      rfl

theorem cell22_1668871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 1, 3, 1, 3].length) (baseStart_1668871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1668871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1668871 prefixEnd_1668871 := by exact prefixLift 1668871
  have htrace : WordTrace (prefixWord ++ tailWord_1668871) baseStart_1668871 baseEnd_1668871 := by
    simpa [prefixWord, tailWord_1668871, baseEnd_1668871] using wordTrace_append hprefix tailTrace_1668871
  have hstable : (prefixWord ++ tailWord_1668871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1668871).length < 2 ^ (prefixWord ++ tailWord_1668871).sum := by decide
  have hdescent : baseEnd_1668871 < baseStart_1668871 := by decide
  rcases family_descends (prefixWord ++ tailWord_1668871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1668878 : List Nat := [4, 1, 1, 2, 1, 1, 2, 2, 8]
def baseStart_1668878 : Nat := 118140960795 + 1668878 * 2 ^ 59
def prefixEnd_1668878 : Nat := 4983230072969 + 3 ^ 40 * 1668878 * 2
def baseEnd_1668878 : Nat := 190430348380939275744439

theorem tailTrace_1668878 : CollatzResearch.WordTrace tailWord_1668878 prefixEnd_1668878 190430348380939275744439 := by
  unfold tailWord_1668878
  simp only [CollatzResearch.WordTrace]
  refine ⟨7608622655993437814471911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40579320831965001677183525 7608622655993437814471911)
  ·
    refine ⟨11412933983990156721707867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7608622655993437814471911 11412933983990156721707867)
    ·
      refine ⟨17119400975985235082561801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11412933983990156721707867 17119400975985235082561801)
      ·
        refine ⟨12839550731988926311921351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17119400975985235082561801 12839550731988926311921351)
        ·
          refine ⟨19259326097983389467882027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12839550731988926311921351 19259326097983389467882027)
          ·
            refine ⟨28888989146975084201823041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19259326097983389467882027 28888989146975084201823041)
            ·
              refine ⟨21666741860231313151367281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28888989146975084201823041 21666741860231313151367281)
              ·
                refine ⟨16250056395173484863525461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21666741860231313151367281 16250056395173484863525461)
                ·
                  refine ⟨190430348380939275744439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16250056395173484863525461 190430348380939275744439)
                  ·
                    rfl

theorem cell22_1668878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 2, 8].length) (baseStart_1668878 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1668878 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1668878 prefixEnd_1668878 := by exact prefixLift 1668878
  have htrace : WordTrace (prefixWord ++ tailWord_1668878) baseStart_1668878 baseEnd_1668878 := by
    simpa [prefixWord, tailWord_1668878, baseEnd_1668878] using wordTrace_append hprefix tailTrace_1668878
  have hstable : (prefixWord ++ tailWord_1668878).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1668878).length < 2 ^ (prefixWord ++ tailWord_1668878).sum := by decide
  have hdescent : baseEnd_1668878 < baseStart_1668878 := by decide
  rcases family_descends (prefixWord ++ tailWord_1668878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1668940 : List Nat := [2, 2, 1, 3, 5, 9]
def baseStart_1668940 : Nat := 118140960795 + 1668940 * 2 ^ 59
def prefixEnd_1668940 : Nat := 4983230072969 + 3 ^ 40 * 1668940 * 2
def baseEnd_1668940 : Nat := 7053237889010744841767

theorem tailTrace_1668940 : CollatzResearch.WordTrace tailWord_1668940 prefixEnd_1668940 7053237889010744841767 := by
  unfold tailWord_1668940
  simp only [CollatzResearch.WordTrace]
  refine ⟨30435621286861443552266137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40580828382481924736354849 30435621286861443552266137)
  ·
    refine ⟨22826715965146082664199603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30435621286861443552266137 22826715965146082664199603)
    ·
      refine ⟨34240073947719123996299405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22826715965146082664199603 34240073947719123996299405)
      ·
        refine ⟨12840027730394671498612277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34240073947719123996299405 12840027730394671498612277)
        ·
          refine ⟨1203752599724500452994901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12840027730394671498612277 1203752599724500452994901)
          ·
            refine ⟨7053237889010744841767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1203752599724500452994901 7053237889010744841767)
            ·
              rfl

theorem cell22_1668940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 9].length) (baseStart_1668940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1668940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1668940 prefixEnd_1668940 := by exact prefixLift 1668940
  have htrace : WordTrace (prefixWord ++ tailWord_1668940) baseStart_1668940 baseEnd_1668940 := by
    simpa [prefixWord, tailWord_1668940, baseEnd_1668940] using wordTrace_append hprefix tailTrace_1668940
  have hstable : (prefixWord ++ tailWord_1668940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1668940).length < 2 ^ (prefixWord ++ tailWord_1668940).sum := by decide
  have hdescent : baseEnd_1668940 < baseStart_1668940 := by decide
  rcases family_descends (prefixWord ++ tailWord_1668940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1668953 : List Nat := [1, 2, 1, 2, 2, 3, 1, 1, 1, 8]
def baseStart_1668953 : Nat := 118140960795 + 1668953 * 2 ^ 59
def prefixEnd_1668953 : Nat := 4983230072969 + 3 ^ 40 * 1668953 * 2
def baseEnd_1668953 : Nat := 571316719175542631608087

theorem tailTrace_1668953 : CollatzResearch.WordTrace tailWord_1668953 prefixEnd_1668953 571316719175542631608087 := by
  unfold tailWord_1668953
  simp only [CollatzResearch.WordTrace]
  refine ⟨60871716722675790324755513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40581144481783860216503675 60871716722675790324755513)
  ·
    refine ⟨45653787542006842743566635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60871716722675790324755513 45653787542006842743566635)
    ·
      refine ⟨68480681313010264115349953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45653787542006842743566635 68480681313010264115349953)
      ·
        refine ⟨51360510984757698086512465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68480681313010264115349953 51360510984757698086512465)
        ·
          refine ⟨38520383238568273564884349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51360510984757698086512465 38520383238568273564884349)
          ·
            refine ⟨14445143714463102586831631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38520383238568273564884349 14445143714463102586831631)
            ·
              refine ⟨21667715571694653880247447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14445143714463102586831631 21667715571694653880247447)
              ·
                refine ⟨32501573357541980820371171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21667715571694653880247447 32501573357541980820371171)
                ·
                  refine ⟨48752360036312971230556757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32501573357541980820371171 48752360036312971230556757)
                  ·
                    refine ⟨571316719175542631608087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 48752360036312971230556757 571316719175542631608087)
                    ·
                      rfl

theorem cell22_1668953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 1, 1, 8].length) (baseStart_1668953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1668953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1668953 prefixEnd_1668953 := by exact prefixLift 1668953
  have htrace : WordTrace (prefixWord ++ tailWord_1668953) baseStart_1668953 baseEnd_1668953 := by
    simpa [prefixWord, tailWord_1668953, baseEnd_1668953] using wordTrace_append hprefix tailTrace_1668953
  have hstable : (prefixWord ++ tailWord_1668953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1668953).length < 2 ^ (prefixWord ++ tailWord_1668953).sum := by decide
  have hdescent : baseEnd_1668953 < baseStart_1668953 := by decide
  rcases family_descends (prefixWord ++ tailWord_1668953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1668972 : List Nat := [2, 2, 1, 1, 4, 3, 1, 2, 3, 3]
def baseStart_1668972 : Nat := 118140960795 + 1668972 * 2 ^ 59
def prefixEnd_1668972 : Nat := 4983230072969 + 3 ^ 40 * 1668972 * 2
def baseEnd_1668972 : Nat := 571323223263832915383029

theorem tailTrace_1668972 : CollatzResearch.WordTrace tailWord_1668972 prefixEnd_1668972 571323223263832915383029 := by
  unfold tailWord_1668972
  simp only [CollatzResearch.WordTrace]
  refine ⟨30436204854803478284848585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40581606473071304379798113 30436204854803478284848585)
  ·
    refine ⟨22827153641102608713636439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30436204854803478284848585 22827153641102608713636439)
    ·
      refine ⟨34240730461653913070454659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22827153641102608713636439 34240730461653913070454659)
      ·
        refine ⟨51361095692480869605681989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34240730461653913070454659 51361095692480869605681989)
        ·
          refine ⟨9630205442340163051065373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51361095692480869605681989 9630205442340163051065373)
          ·
            refine ⟨3611327040877561144149515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9630205442340163051065373 3611327040877561144149515)
            ·
              refine ⟨5416990561316341716224273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3611327040877561144149515 5416990561316341716224273)
              ·
                refine ⟨4062742920987256287168205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5416990561316341716224273 4062742920987256287168205)
                ·
                  refine ⟨1523528595370221107688077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4062742920987256287168205 1523528595370221107688077)
                  ·
                    refine ⟨571323223263832915383029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1523528595370221107688077 571323223263832915383029)
                    ·
                      rfl

theorem cell22_1668972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 3].length) (baseStart_1668972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1668972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1668972 prefixEnd_1668972 := by exact prefixLift 1668972
  have htrace : WordTrace (prefixWord ++ tailWord_1668972) baseStart_1668972 baseEnd_1668972 := by
    simpa [prefixWord, tailWord_1668972, baseEnd_1668972] using wordTrace_append hprefix tailTrace_1668972
  have hstable : (prefixWord ++ tailWord_1668972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1668972).length < 2 ^ (prefixWord ++ tailWord_1668972).sum := by decide
  have hdescent : baseEnd_1668972 < baseStart_1668972 := by decide
  rcases family_descends (prefixWord ++ tailWord_1668972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1669002 : List Nat := [3, 1, 2, 4, 2, 1, 1, 1, 7]
def baseStart_1669002 : Nat := 118140960795 + 1669002 * 2 ^ 59
def prefixEnd_1669002 : Nat := 4983230072969 + 3 ^ 40 * 1669002 * 2
def baseEnd_1669002 : Nat := 190444497625640945710979

theorem tailTrace_1669002 : CollatzResearch.WordTrace tailWord_1669002 prefixEnd_1669002 190444497625640945710979 := by
  unfold tailWord_1669002
  simp only [CollatzResearch.WordTrace]
  refine ⟨15218375974874567923322315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40582335932998847795526173 15218375974874567923322315)
  ·
    refine ⟨22827563962311851884983473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15218375974874567923322315 22827563962311851884983473)
    ·
      refine ⟨17120672971733888913737605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22827563962311851884983473 17120672971733888913737605)
      ·
        refine ⟨3210126182200104171325801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17120672971733888913737605 3210126182200104171325801)
        ·
          refine ⟨2407594636650078128494351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3210126182200104171325801 2407594636650078128494351)
          ·
            refine ⟨3611391954975117192741527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2407594636650078128494351 3611391954975117192741527)
            ·
              refine ⟨5417087932462675789112291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3611391954975117192741527 5417087932462675789112291)
              ·
                refine ⟨8125631898694013683668437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5417087932462675789112291 8125631898694013683668437)
                ·
                  refine ⟨190444497625640945710979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8125631898694013683668437 190444497625640945710979)
                  ·
                    rfl

theorem cell22_1669002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 1, 7].length) (baseStart_1669002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1669002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1669002 prefixEnd_1669002 := by exact prefixLift 1669002
  have htrace : WordTrace (prefixWord ++ tailWord_1669002) baseStart_1669002 baseEnd_1669002 := by
    simpa [prefixWord, tailWord_1669002, baseEnd_1669002] using wordTrace_append hprefix tailTrace_1669002
  have hstable : (prefixWord ++ tailWord_1669002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1669002).length < 2 ^ (prefixWord ++ tailWord_1669002).sum := by decide
  have hdescent : baseEnd_1669002 < baseStart_1669002 := by decide
  rcases family_descends (prefixWord ++ tailWord_1669002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1669006 : List Nat := [4, 1, 1, 5, 1, 1, 2, 1, 3, 3]
def baseStart_1669006 : Nat := 118140960795 + 1669006 * 2 ^ 59
def prefixEnd_1669006 : Nat := 4983230072969 + 3 ^ 40 * 1669006 * 2
def baseEnd_1669006 : Nat := 571334862158668160032925

theorem tailTrace_1669006 : CollatzResearch.WordTrace tailWord_1669006 prefixEnd_1669006 571334862158668160032925 := by
  unfold tailWord_1669006
  simp only [CollatzResearch.WordTrace]
  refine ⟨7609206223935472547054359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40582433194322520250956581 7609206223935472547054359)
  ·
    refine ⟨11413809335903208820581539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7609206223935472547054359 11413809335903208820581539)
    ·
      refine ⟨17120714003854813230872309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11413809335903208820581539 17120714003854813230872309)
      ·
        refine ⟨1605066937861388740394279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17120714003854813230872309 1605066937861388740394279)
        ·
          refine ⟨2407600406792083110591419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1605066937861388740394279 2407600406792083110591419)
          ·
            refine ⟨3611400610188124665887129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2407600406792083110591419 3611400610188124665887129)
            ·
              refine ⟨2708550457641093499415347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3611400610188124665887129 2708550457641093499415347)
              ·
                refine ⟨4062825686461640249123021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2708550457641093499415347 4062825686461640249123021)
                ·
                  refine ⟨1523559632423115093421133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4062825686461640249123021 1523559632423115093421133)
                  ·
                    refine ⟨571334862158668160032925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1523559632423115093421133 571334862158668160032925)
                    ·
                      rfl

theorem cell22_1669006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 2, 1, 3, 3].length) (baseStart_1669006 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1669006 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1669006 prefixEnd_1669006 := by exact prefixLift 1669006
  have htrace : WordTrace (prefixWord ++ tailWord_1669006) baseStart_1669006 baseEnd_1669006 := by
    simpa [prefixWord, tailWord_1669006, baseEnd_1669006] using wordTrace_append hprefix tailTrace_1669006
  have hstable : (prefixWord ++ tailWord_1669006).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1669006).length < 2 ^ (prefixWord ++ tailWord_1669006).sum := by decide
  have hdescent : baseEnd_1669006 < baseStart_1669006 := by decide
  rcases family_descends (prefixWord ++ tailWord_1669006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1669216 : List Nat := [2, 1, 1, 3, 2, 5, 1, 3, 4]
def baseStart_1669216 : Nat := 118140960795 + 1669216 * 2 ^ 59
def prefixEnd_1669216 : Nat := 4983230072969 + 3 ^ 40 * 1669216 * 2
def baseEnd_1669216 : Nat := 190468916483432537427427

theorem tailTrace_1669216 : CollatzResearch.WordTrace tailWord_1669216 prefixEnd_1669216 190468916483432537427427 := by
  unfold tailWord_1669216
  simp only [CollatzResearch.WordTrace]
  refine ⟨30440654560361493120789751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40587539413815324161053001 30440654560361493120789751)
  ·
    refine ⟨45660981840542239681184627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30440654560361493120789751 45660981840542239681184627)
    ·
      refine ⟨68491472760813359521776941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45660981840542239681184627 68491472760813359521776941)
      ·
        refine ⟨25684302285305009820666353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68491472760813359521776941 25684302285305009820666353)
        ·
          refine ⟨19263226713978757365499765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25684302285305009820666353 19263226713978757365499765)
          ·
            refine ⟨1805927504435508503015603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19263226713978757365499765 1805927504435508503015603)
            ·
              refine ⟨2708891256653262754523405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1805927504435508503015603 2708891256653262754523405)
              ·
                refine ⟨1015834221244973532946277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2708891256653262754523405 1015834221244973532946277)
                ·
                  refine ⟨190468916483432537427427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1015834221244973532946277 190468916483432537427427)
                  ·
                    rfl

theorem cell22_1669216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 1, 3, 4].length) (baseStart_1669216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1669216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1669216 prefixEnd_1669216 := by exact prefixLift 1669216
  have htrace : WordTrace (prefixWord ++ tailWord_1669216) baseStart_1669216 baseEnd_1669216 := by
    simpa [prefixWord, tailWord_1669216, baseEnd_1669216] using wordTrace_append hprefix tailTrace_1669216
  have hstable : (prefixWord ++ tailWord_1669216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1669216).length < 2 ^ (prefixWord ++ tailWord_1669216).sum := by decide
  have hdescent : baseEnd_1669216 < baseStart_1669216 := by decide
  rcases family_descends (prefixWord ++ tailWord_1669216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1669229 : List Nat := [1, 5, 1, 1, 2, 1, 3, 2, 2, 4]
def baseStart_1669229 : Nat := 118140960795 + 1669229 * 2 ^ 59
def prefixEnd_1669229 : Nat := 4983230072969 + 3 ^ 40 * 1669229 * 2
def baseEnd_1669229 : Nat := 571411199615969911707241

theorem tailTrace_1669229 : CollatzResearch.WordTrace tailWord_1669229 prefixEnd_1669229 571411199615969911707241 := by
  unfold tailWord_1669229
  simp only [CollatzResearch.WordTrace]
  refine ⟨60881783269675889461802741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40587855513117259641201827 60881783269675889461802741)
  ·
    refine ⟨5707667181532114637044007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 60881783269675889461802741 5707667181532114637044007)
    ·
      refine ⟨8561500772298171955566011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5707667181532114637044007 8561500772298171955566011)
      ·
        refine ⟨12842251158447257933349017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8561500772298171955566011 12842251158447257933349017)
        ·
          refine ⟨9631688368835443450011763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12842251158447257933349017 9631688368835443450011763)
          ·
            refine ⟨14447532553253165175017645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9631688368835443450011763 14447532553253165175017645)
            ·
              refine ⟨5417824707469936940631617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14447532553253165175017645 5417824707469936940631617)
              ·
                refine ⟨4063368530602452705473713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5417824707469936940631617 4063368530602452705473713)
                ·
                  refine ⟨3047526397951839529105285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4063368530602452705473713 3047526397951839529105285)
                  ·
                    refine ⟨571411199615969911707241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3047526397951839529105285 571411199615969911707241)
                    ·
                      rfl

theorem cell22_1669229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 2, 2, 4].length) (baseStart_1669229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1669229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1669229 prefixEnd_1669229 := by exact prefixLift 1669229
  have htrace : WordTrace (prefixWord ++ tailWord_1669229) baseStart_1669229 baseEnd_1669229 := by
    simpa [prefixWord, tailWord_1669229, baseEnd_1669229] using wordTrace_append hprefix tailTrace_1669229
  have hstable : (prefixWord ++ tailWord_1669229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1669229).length < 2 ^ (prefixWord ++ tailWord_1669229).sum := by decide
  have hdescent : baseEnd_1669229 < baseStart_1669229 := by decide
  rcases family_descends (prefixWord ++ tailWord_1669229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1669317 : List Nat := [1, 3, 1, 1, 1, 1, 5, 1, 8]
def baseStart_1669317 : Nat := 118140960795 + 1669317 * 2 ^ 59
def prefixEnd_1669317 : Nat := 4983230072969 + 3 ^ 40 * 1669317 * 2
def baseEnd_1669317 : Nat := 190480441271455671835657

theorem tailTrace_1669317 : CollatzResearch.WordTrace tailWord_1669317 prefixEnd_1669317 190480441271455671835657 := by
  unfold tailWord_1669317
  simp only [CollatzResearch.WordTrace]
  refine ⟨60884992893357080491006205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40589995262238053660670803 60884992893357080491006205)
  ·
    refine ⟨22831872335008905184127327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60884992893357080491006205 22831872335008905184127327)
    ·
      refine ⟨34247808502513357776190991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22831872335008905184127327 34247808502513357776190991)
      ·
        refine ⟨51371712753770036664286487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34247808502513357776190991 51371712753770036664286487)
        ·
          refine ⟨77057569130655054996429731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51371712753770036664286487 77057569130655054996429731)
          ·
            refine ⟨115586353695982582494644597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77057569130655054996429731 115586353695982582494644597)
            ·
              refine ⟨10836220658998367108872931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 115586353695982582494644597 10836220658998367108872931)
              ·
                refine ⟨16254330988497550663309397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10836220658998367108872931 16254330988497550663309397)
                ·
                  refine ⟨190480441271455671835657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16254330988497550663309397 190480441271455671835657)
                  ·
                    rfl

theorem cell22_1669317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 1, 8].length) (baseStart_1669317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1669317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1669317 prefixEnd_1669317 := by exact prefixLift 1669317
  have htrace : WordTrace (prefixWord ++ tailWord_1669317) baseStart_1669317 baseEnd_1669317 := by
    simpa [prefixWord, tailWord_1669317, baseEnd_1669317] using wordTrace_append hprefix tailTrace_1669317
  have hstable : (prefixWord ++ tailWord_1669317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1669317).length < 2 ^ (prefixWord ++ tailWord_1669317).sum := by decide
  have hdescent : baseEnd_1669317 < baseStart_1669317 := by decide
  rcases family_descends (prefixWord ++ tailWord_1669317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1669336 : List Nat := [2, 1, 2, 2, 4, 2, 1, 3, 1, 4]
def baseStart_1669336 : Nat := 118140960795 + 1669336 * 2 ^ 59
def prefixEnd_1669336 : Nat := 4983230072969 + 3 ^ 40 * 1669336 * 2
def baseEnd_1669336 : Nat := 571447827902657299281913

theorem tailTrace_1669336 : CollatzResearch.WordTrace tailWord_1669336 prefixEnd_1669336 571447827902657299281913 := by
  unfold tailWord_1669336
  simp only [CollatzResearch.WordTrace]
  refine ⟨30442842940144123367973931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40590457253525497823965241 30442842940144123367973931)
  ·
    refine ⟨45664264410216185051960897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30442842940144123367973931 45664264410216185051960897)
    ·
      refine ⟨34248198307662138788970673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45664264410216185051960897 34248198307662138788970673)
      ·
        refine ⟨25686148730746604091728005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34248198307662138788970673 25686148730746604091728005)
        ·
          refine ⟨4816152887014988267199001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25686148730746604091728005 4816152887014988267199001)
          ·
            refine ⟨3612114665261241200399251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4816152887014988267199001 3612114665261241200399251)
            ·
              refine ⟨5418171997891861800598877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3612114665261241200399251 5418171997891861800598877)
              ·
                refine ⟨2031814499209448175224579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5418171997891861800598877 2031814499209448175224579)
                ·
                  refine ⟨3047721748814172262836869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2031814499209448175224579 3047721748814172262836869)
                  ·
                    refine ⟨571447827902657299281913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3047721748814172262836869 571447827902657299281913)
                    ·
                      rfl

theorem cell22_1669336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 3, 1, 4].length) (baseStart_1669336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1669336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1669336 prefixEnd_1669336 := by exact prefixLift 1669336
  have htrace : WordTrace (prefixWord ++ tailWord_1669336) baseStart_1669336 baseEnd_1669336 := by
    simpa [prefixWord, tailWord_1669336, baseEnd_1669336] using wordTrace_append hprefix tailTrace_1669336
  have hstable : (prefixWord ++ tailWord_1669336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1669336).length < 2 ^ (prefixWord ++ tailWord_1669336).sum := by decide
  have hdescent : baseEnd_1669336 < baseStart_1669336 := by decide
  rcases family_descends (prefixWord ++ tailWord_1669336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1669340 : List Nat := [2, 2, 5, 2, 1, 2, 1, 2, 5]
def baseStart_1669340 : Nat := 118140960795 + 1669340 * 2 ^ 59
def prefixEnd_1669340 : Nat := 4983230072969 + 3 ^ 40 * 1669340 * 2
def baseEnd_1669340 : Nat := 190483065728134207393967

theorem tailTrace_1669340 : CollatzResearch.WordTrace tailWord_1669340 prefixEnd_1669340 190483065728134207393967 := by
  unfold tailWord_1669340
  simp only [CollatzResearch.WordTrace]
  refine ⟨30442915886136877709546737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40590554514849170279395649 30442915886136877709546737)
  ·
    refine ⟨22832186914602658282160053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30442915886136877709546737 22832186914602658282160053)
    ·
      refine ⟨2140517523243999213952505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22832186914602658282160053 2140517523243999213952505)
      ·
        refine ⟨1605388142432999410464379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2140517523243999213952505 1605388142432999410464379)
        ·
          refine ⟨2408082213649499115696569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1605388142432999410464379 2408082213649499115696569)
          ·
            refine ⟨1806061660237124336772427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2408082213649499115696569 1806061660237124336772427)
            ·
              refine ⟨2709092490355686505158641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1806061660237124336772427 2709092490355686505158641)
              ·
                refine ⟨2031819367766764878868981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2709092490355686505158641 2031819367766764878868981)
                ·
                  refine ⟨190483065728134207393967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2031819367766764878868981 190483065728134207393967)
                  ·
                    rfl

theorem cell22_1669340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 1, 2, 5].length) (baseStart_1669340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1669340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1669340 prefixEnd_1669340 := by exact prefixLift 1669340
  have htrace : WordTrace (prefixWord ++ tailWord_1669340) baseStart_1669340 baseEnd_1669340 := by
    simpa [prefixWord, tailWord_1669340, baseEnd_1669340] using wordTrace_append hprefix tailTrace_1669340
  have hstable : (prefixWord ++ tailWord_1669340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1669340).length < 2 ^ (prefixWord ++ tailWord_1669340).sum := by decide
  have hdescent : baseEnd_1669340 < baseStart_1669340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1669340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1669351 : List Nat := [1, 1, 5, 3, 1, 2, 2, 1, 6]
def baseStart_1669351 : Nat := 118140960795 + 1669351 * 2 ^ 59
def prefixEnd_1669351 : Nat := 4983230072969 + 3 ^ 40 * 1669351 * 2
def baseEnd_1669351 : Nat := 190484320903067420052289

theorem tailTrace_1669351 : CollatzResearch.WordTrace tailWord_1669351 prefixEnd_1669351 190484320903067420052289 := by
  unfold tailWord_1669351
  simp only [CollatzResearch.WordTrace]
  refine ⟨60886232975233904297743907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40590821983489269531829271 60886232975233904297743907)
  ·
    refine ⟨91329349462850856446615861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60886232975233904297743907 91329349462850856446615861)
    ·
      refine ⟨8562126512142267791870237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 91329349462850856446615861 8562126512142267791870237)
      ·
        refine ⟨3210797442053350421951339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8562126512142267791870237 3210797442053350421951339)
        ·
          refine ⟨4816196163080025632927009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3210797442053350421951339 4816196163080025632927009)
          ·
            refine ⟨3612147122310019224695257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4816196163080025632927009 3612147122310019224695257)
            ·
              refine ⟨2709110341732514418521443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3612147122310019224695257 2709110341732514418521443)
              ·
                refine ⟨4063665512598771627782165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2709110341732514418521443 4063665512598771627782165)
                ·
                  refine ⟨190484320903067420052289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4063665512598771627782165 190484320903067420052289)
                  ·
                    rfl

theorem cell22_1669351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 2, 1, 6].length) (baseStart_1669351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1669351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1669351 prefixEnd_1669351 := by exact prefixLift 1669351
  have htrace : WordTrace (prefixWord ++ tailWord_1669351) baseStart_1669351 baseEnd_1669351 := by
    simpa [prefixWord, tailWord_1669351, baseEnd_1669351] using wordTrace_append hprefix tailTrace_1669351
  have hstable : (prefixWord ++ tailWord_1669351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1669351).length < 2 ^ (prefixWord ++ tailWord_1669351).sum := by decide
  have hdescent : baseEnd_1669351 < baseStart_1669351 := by decide
  rcases family_descends (prefixWord ++ tailWord_1669351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1669366 : List Nat := [5, 1, 1, 1, 1, 1, 5, 1, 1, 5]
def baseStart_1669366 : Nat := 118140960795 + 1669366 * 2 ^ 59
def prefixEnd_1669366 : Nat := 4983230072969 + 3 ^ 40 * 1669366 * 2
def baseEnd_1669366 : Nat := 571458097515747221031821

theorem tailTrace_1669366 : CollatzResearch.WordTrace tailWord_1669366 prefixEnd_1669366 571458097515747221031821 := by
  unfold tailWord_1669366
  simp only [CollatzResearch.WordTrace]
  refine ⟨3805423754386222616221247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40591186713453041239693301 3805423754386222616221247)
  ·
    refine ⟨5708135631579333924331871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3805423754386222616221247 5708135631579333924331871)
    ·
      refine ⟨8562203447369000886497807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5708135631579333924331871 8562203447369000886497807)
      ·
        refine ⟨12843305171053501329746711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8562203447369000886497807 12843305171053501329746711)
        ·
          refine ⟨19264957756580251994620067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12843305171053501329746711 19264957756580251994620067)
          ·
            refine ⟨28897436634870377991930101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19264957756580251994620067 28897436634870377991930101)
            ·
              refine ⟨2709134684519097936743447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28897436634870377991930101 2709134684519097936743447)
              ·
                refine ⟨4063702026778646905115171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2709134684519097936743447 4063702026778646905115171)
                ·
                  refine ⟨6095553040167970357672757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4063702026778646905115171 6095553040167970357672757)
                  ·
                    refine ⟨571458097515747221031821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6095553040167970357672757 571458097515747221031821)
                    ·
                      rfl

theorem cell22_1669366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 5, 1, 1, 5].length) (baseStart_1669366 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1669366 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1669366 prefixEnd_1669366 := by exact prefixLift 1669366
  have htrace : WordTrace (prefixWord ++ tailWord_1669366) baseStart_1669366 baseEnd_1669366 := by
    simpa [prefixWord, tailWord_1669366, baseEnd_1669366] using wordTrace_append hprefix tailTrace_1669366
  have hstable : (prefixWord ++ tailWord_1669366).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1669366).length < 2 ^ (prefixWord ++ tailWord_1669366).sum := by decide
  have hdescent : baseEnd_1669366 < baseStart_1669366 := by decide
  rcases family_descends (prefixWord ++ tailWord_1669366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1669501 : List Nat := [1, 4, 1, 1, 2, 3, 2, 2, 1, 5]
def baseStart_1669501 : Nat := 118140960795 + 1669501 * 2 ^ 59
def prefixEnd_1669501 : Nat := 4983230072969 + 3 ^ 40 * 1669501 * 2
def baseEnd_1669501 : Nat := 571504310774651868906407

theorem tailTrace_1669501 : CollatzResearch.WordTrace tailWord_1669501 prefixEnd_1669501 571504310774651868906407 := by
  unfold tailWord_1669501
  simp only [CollatzResearch.WordTrace]
  refine ⟨60891703924690479915704357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40594469283126986610469571 60891703924690479915704357)
  ·
    refine ⟨11417194485879464984194567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60891703924690479915704357 11417194485879464984194567)
    ·
      refine ⟨17125791728819197476291851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11417194485879464984194567 17125791728819197476291851)
      ·
        refine ⟨25688687593228796214437777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17125791728819197476291851 25688687593228796214437777)
        ·
          refine ⟨19266515694921597160828333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25688687593228796214437777 19266515694921597160828333)
          ·
            refine ⟨7224943385595598935310625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19266515694921597160828333 7224943385595598935310625)
            ·
              refine ⟨5418707539196699201482969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7224943385595598935310625 5418707539196699201482969)
              ·
                refine ⟨4064030654397524401112227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5418707539196699201482969 4064030654397524401112227)
                ·
                  refine ⟨6096045981596286601668341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4064030654397524401112227 6096045981596286601668341)
                  ·
                    refine ⟨571504310774651868906407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6096045981596286601668341 571504310774651868906407)
                    ·
                      rfl

theorem cell22_1669501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 2, 1, 5].length) (baseStart_1669501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1669501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1669501 prefixEnd_1669501 := by exact prefixLift 1669501
  have htrace : WordTrace (prefixWord ++ tailWord_1669501) baseStart_1669501 baseEnd_1669501 := by
    simpa [prefixWord, tailWord_1669501, baseEnd_1669501] using wordTrace_append hprefix tailTrace_1669501
  have hstable : (prefixWord ++ tailWord_1669501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1669501).length < 2 ^ (prefixWord ++ tailWord_1669501).sum := by decide
  have hdescent : baseEnd_1669501 < baseStart_1669501 := by decide
  rcases family_descends (prefixWord ++ tailWord_1669501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1669505 : List Nat := [1, 2, 4, 3, 1, 1, 4, 1, 1, 4]
def baseStart_1669505 : Nat := 118140960795 + 1669505 * 2 ^ 59
def prefixEnd_1669505 : Nat := 4983230072969 + 3 ^ 40 * 1669505 * 2
def baseEnd_1669505 : Nat := 571505680056397191806395

theorem tailTrace_1669505 : CollatzResearch.WordTrace tailWord_1669505 prefixEnd_1669505 571505680056397191806395 := by
  unfold tailWord_1669505
  simp only [CollatzResearch.WordTrace]
  refine ⟨60891849816675988598849969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40594566544450659065899979 60891849816675988598849969)
  ·
    refine ⟨45668887362506991449137477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60891849816675988598849969 45668887362506991449137477)
    ·
      refine ⟨8562916380470060896713277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45668887362506991449137477 8562916380470060896713277)
      ·
        refine ⟨3211093642676272836267479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8562916380470060896713277 3211093642676272836267479)
        ·
          refine ⟨4816640464014409254401219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3211093642676272836267479 4816640464014409254401219)
          ·
            refine ⟨7224960696021613881601829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4816640464014409254401219 7224960696021613881601829)
            ·
              refine ⟨1354680130504052602800343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7224960696021613881601829 1354680130504052602800343)
              ·
                refine ⟨2032020195756078904200515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1354680130504052602800343 2032020195756078904200515)
                ·
                  refine ⟨3048030293634118356300773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2032020195756078904200515 3048030293634118356300773)
                  ·
                    refine ⟨571505680056397191806395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3048030293634118356300773 571505680056397191806395)
                    ·
                      rfl

theorem cell22_1669505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 4, 1, 1, 4].length) (baseStart_1669505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1669505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1669505 prefixEnd_1669505 := by exact prefixLift 1669505
  have htrace : WordTrace (prefixWord ++ tailWord_1669505) baseStart_1669505 baseEnd_1669505 := by
    simpa [prefixWord, tailWord_1669505, baseEnd_1669505] using wordTrace_append hprefix tailTrace_1669505
  have hstable : (prefixWord ++ tailWord_1669505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1669505).length < 2 ^ (prefixWord ++ tailWord_1669505).sum := by decide
  have hdescent : baseEnd_1669505 < baseStart_1669505 := by decide
  rcases family_descends (prefixWord ++ tailWord_1669505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1669535 : List Nat := [1, 1, 2, 5, 1, 1, 5, 1, 2, 3]
def baseStart_1669535 : Nat := 118140960795 + 1669535 * 2 ^ 59
def prefixEnd_1669535 : Nat := 4983230072969 + 3 ^ 40 * 1669535 * 2
def baseEnd_1669535 : Nat := 571515949669487113556303

theorem tailTrace_1669535 : CollatzResearch.WordTrace tailWord_1669535 prefixEnd_1669535 571515949669487113556303 := by
  unfold tailWord_1669535
  simp only [CollatzResearch.WordTrace]
  refine ⟨60892944006567303722442059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40595296004378202481628039 60892944006567303722442059)
  ·
    refine ⟨91339416009850955583663089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60892944006567303722442059 91339416009850955583663089)
    ·
      refine ⟨68504562007388216687747317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91339416009850955583663089 68504562007388216687747317)
      ·
        refine ⟨6422302688192645314476311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 68504562007388216687747317 6422302688192645314476311)
        ·
          refine ⟨9633454032288967971714467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6422302688192645314476311 9633454032288967971714467)
          ·
            refine ⟨14450181048433451957571701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9633454032288967971714467 14450181048433451957571701)
            ·
              refine ⟨1354704473290636121022347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14450181048433451957571701 1354704473290636121022347)
              ·
                refine ⟨2032056709935954181533521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1354704473290636121022347 2032056709935954181533521)
                ·
                  refine ⟨1524042532451965636150141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2032056709935954181533521 1524042532451965636150141)
                  ·
                    refine ⟨571515949669487113556303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1524042532451965636150141 571515949669487113556303)
                    ·
                      rfl

theorem cell22_1669535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 5, 1, 2, 3].length) (baseStart_1669535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1669535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1669535 prefixEnd_1669535 := by exact prefixLift 1669535
  have htrace : WordTrace (prefixWord ++ tailWord_1669535) baseStart_1669535 baseEnd_1669535 := by
    simpa [prefixWord, tailWord_1669535, baseEnd_1669535] using wordTrace_append hprefix tailTrace_1669535
  have hstable : (prefixWord ++ tailWord_1669535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1669535).length < 2 ^ (prefixWord ++ tailWord_1669535).sum := by decide
  have hdescent : baseEnd_1669535 < baseStart_1669535 := by decide
  rcases family_descends (prefixWord ++ tailWord_1669535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1669576 : List Nat := [2, 1, 3, 1, 3, 2, 2, 1, 7]
def baseStart_1669576 : Nat := 118140960795 + 1669576 * 2 ^ 59
def prefixEnd_1669576 : Nat := 4983230072969 + 3 ^ 40 * 1669576 * 2
def baseEnd_1669576 : Nat := 190509994935792224427059

theorem tailTrace_1669576 : CollatzResearch.WordTrace tailWord_1669576 prefixEnd_1669576 190509994935792224427059 := by
  unfold tailWord_1669576
  simp only [CollatzResearch.WordTrace]
  refine ⟨30447219699709383862342291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40596292932945845149789721 30447219699709383862342291)
  ·
    refine ⟨45670829549564075793513437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30447219699709383862342291 45670829549564075793513437)
    ·
      refine ⟨17126561081086528422567539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45670829549564075793513437 17126561081086528422567539)
      ·
        refine ⟨25689841621629792633851309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17126561081086528422567539 25689841621629792633851309)
        ·
          refine ⟨9633690608111172237694241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25689841621629792633851309 9633690608111172237694241)
          ·
            refine ⟨7225267956083379178270681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9633690608111172237694241 7225267956083379178270681)
            ·
              refine ⟨5418950967062534383703011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7225267956083379178270681 5418950967062534383703011)
              ·
                refine ⟨8128426450593801575554517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5418950967062534383703011 8128426450593801575554517)
                ·
                  refine ⟨190509994935792224427059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8128426450593801575554517 190509994935792224427059)
                  ·
                    rfl

theorem cell22_1669576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 1, 7].length) (baseStart_1669576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1669576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1669576 prefixEnd_1669576 := by exact prefixLift 1669576
  have htrace : WordTrace (prefixWord ++ tailWord_1669576) baseStart_1669576 baseEnd_1669576 := by
    simpa [prefixWord, tailWord_1669576, baseEnd_1669576] using wordTrace_append hprefix tailTrace_1669576
  have hstable : (prefixWord ++ tailWord_1669576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1669576).length < 2 ^ (prefixWord ++ tailWord_1669576).sum := by decide
  have hdescent : baseEnd_1669576 < baseStart_1669576 := by decide
  rcases family_descends (prefixWord ++ tailWord_1669576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1669586 : List Nat := [3, 2, 2, 4, 2, 1, 2, 1, 2, 3]
def baseStart_1669586 : Nat := 118140960795 + 1669586 * 2 ^ 59
def prefixEnd_1669586 : Nat := 4983230072969 + 3 ^ 40 * 1669586 * 2
def baseEnd_1669586 : Nat := 571533408011739980531147

theorem tailTrace_1669586 : CollatzResearch.WordTrace tailWord_1669586 prefixEnd_1669586 571533408011739980531147 := by
  unfold tailWord_1669586
  simp only [CollatzResearch.WordTrace]
  refine ⟨15223701032345634858137153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40596536086255026288365741 15223701032345634858137153)
  ·
    refine ⟨11417775774259226143602865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15223701032345634858137153 11417775774259226143602865)
    ·
      refine ⟨8563331830694419607702149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11417775774259226143602865 8563331830694419607702149)
      ·
        refine ⟨1605624718255203676444153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8563331830694419607702149 1605624718255203676444153)
        ·
          refine ⟨1204218538691402757333115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1605624718255203676444153 1204218538691402757333115)
          ·
            refine ⟨1806327808037104135999673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1204218538691402757333115 1806327808037104135999673)
            ·
              refine ⟨1354745856027828101999755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1806327808037104135999673 1354745856027828101999755)
              ·
                refine ⟨2032118784041742152999633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1354745856027828101999755 2032118784041742152999633)
                ·
                  refine ⟨1524089088031306614749725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2032118784041742152999633 1524089088031306614749725)
                  ·
                    refine ⟨571533408011739980531147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1524089088031306614749725 571533408011739980531147)
                    ·
                      rfl

theorem cell22_1669586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 2, 1, 2, 3].length) (baseStart_1669586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1669586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1669586 prefixEnd_1669586 := by exact prefixLift 1669586
  have htrace : WordTrace (prefixWord ++ tailWord_1669586) baseStart_1669586 baseEnd_1669586 := by
    simpa [prefixWord, tailWord_1669586, baseEnd_1669586] using wordTrace_append hprefix tailTrace_1669586
  have hstable : (prefixWord ++ tailWord_1669586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1669586).length < 2 ^ (prefixWord ++ tailWord_1669586).sum := by decide
  have hdescent : baseEnd_1669586 < baseStart_1669586 := by decide
  rcases family_descends (prefixWord ++ tailWord_1669586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1669651 : List Nat := [1, 1, 1, 2, 1, 5, 2, 2, 1, 6]
def baseStart_1669651 : Nat := 118140960795 + 1669651 * 2 ^ 59
def prefixEnd_1669651 : Nat := 4983230072969 + 3 ^ 40 * 1669651 * 2
def baseEnd_1669651 : Nat := 571555658840101477655947

theorem tailTrace_1669651 : CollatzResearch.WordTrace tailWord_1669651 prefixEnd_1669651 571555658840101477655947 := by
  unfold tailWord_1669651
  simp only [CollatzResearch.WordTrace]
  refine ⟨60897174874147055533664807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40598116582764703689109871 60897174874147055533664807)
  ·
    refine ⟨91345762311220583300497211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60897174874147055533664807 91345762311220583300497211)
    ·
      refine ⟨137018643466830874950745817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91345762311220583300497211 137018643466830874950745817)
      ·
        refine ⟨102763982600123156213059363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137018643466830874950745817 102763982600123156213059363)
        ·
          refine ⟨154145973900184734319589045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102763982600123156213059363 154145973900184734319589045)
          ·
            refine ⟨14451185053142318842461473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 154145973900184734319589045 14451185053142318842461473)
            ·
              refine ⟨10838388789856739131846105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14451185053142318842461473 10838388789856739131846105)
              ·
                refine ⟨8128791592392554348884579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10838388789856739131846105 8128791592392554348884579)
                ·
                  refine ⟨12193187388588831523326869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8128791592392554348884579 12193187388588831523326869)
                  ·
                    refine ⟨571555658840101477655947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12193187388588831523326869 571555658840101477655947)
                    ·
                      rfl

theorem cell22_1669651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 2, 1, 6].length) (baseStart_1669651 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1669651 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1669651 prefixEnd_1669651 := by exact prefixLift 1669651
  have htrace : WordTrace (prefixWord ++ tailWord_1669651) baseStart_1669651 baseEnd_1669651 := by
    simpa [prefixWord, tailWord_1669651, baseEnd_1669651] using wordTrace_append hprefix tailTrace_1669651
  have hstable : (prefixWord ++ tailWord_1669651).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1669651).length < 2 ^ (prefixWord ++ tailWord_1669651).sum := by decide
  have hdescent : baseEnd_1669651 < baseStart_1669651 := by decide
  rcases family_descends (prefixWord ++ tailWord_1669651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1669653 : List Nat := [1, 3, 2, 1, 3, 1, 4, 1, 1, 5]
def baseStart_1669653 : Nat := 118140960795 + 1669653 * 2 ^ 59
def prefixEnd_1669653 : Nat := 4983230072969 + 3 ^ 40 * 1669653 * 2
def baseEnd_1669653 : Nat := 571556343480974139105941

theorem tailTrace_1669653 : CollatzResearch.WordTrace tailWord_1669653 prefixEnd_1669653 571556343480974139105941 := by
  unfold tailWord_1669653
  simp only [CollatzResearch.WordTrace]
  refine ⟨60897247820139809875237613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40598165213426539916825075 60897247820139809875237613)
  ·
    refine ⟨22836467932552428703214105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60897247820139809875237613 22836467932552428703214105)
    ·
      refine ⟨17127350949414321527410579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22836467932552428703214105 17127350949414321527410579)
      ·
        refine ⟨25691026424121482291115869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17127350949414321527410579 25691026424121482291115869)
        ·
          refine ⟨9634134909045555859168451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25691026424121482291115869 9634134909045555859168451)
          ·
            refine ⟨14451202363568333788752677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9634134909045555859168451 14451202363568333788752677)
            ·
              refine ⟨2709600443169062585391127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14451202363568333788752677 2709600443169062585391127)
              ·
                refine ⟨4064400664753593878086691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2709600443169062585391127 4064400664753593878086691)
                ·
                  refine ⟨6096600997130390817130037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4064400664753593878086691 6096600997130390817130037)
                  ·
                    refine ⟨571556343480974139105941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6096600997130390817130037 571556343480974139105941)
                    ·
                      rfl

theorem cell22_1669653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 4, 1, 1, 5].length) (baseStart_1669653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1669653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1669653 prefixEnd_1669653 := by exact prefixLift 1669653
  have htrace : WordTrace (prefixWord ++ tailWord_1669653) baseStart_1669653 baseEnd_1669653 := by
    simpa [prefixWord, tailWord_1669653, baseEnd_1669653] using wordTrace_append hprefix tailTrace_1669653
  have hstable : (prefixWord ++ tailWord_1669653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1669653).length < 2 ^ (prefixWord ++ tailWord_1669653).sum := by decide
  have hdescent : baseEnd_1669653 < baseStart_1669653 := by decide
  rcases family_descends (prefixWord ++ tailWord_1669653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1669655 : List Nat := [1, 1, 3, 6, 1, 1, 1, 2, 6]
def baseStart_1669655 : Nat := 118140960795 + 1669655 * 2 ^ 59
def prefixEnd_1669655 : Nat := 4983230072969 + 3 ^ 40 * 1669655 * 2
def baseEnd_1669655 : Nat := 190519009373948933518645

theorem tailTrace_1669655 : CollatzResearch.WordTrace tailWord_1669655 prefixEnd_1669655 190519009373948933518645 := by
  unfold tailWord_1669655
  simp only [CollatzResearch.WordTrace]
  refine ⟨60897320766132564216810419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40598213844088376144540279 60897320766132564216810419)
  ·
    refine ⟨91345981149198846325215629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60897320766132564216810419 91345981149198846325215629)
    ·
      refine ⟨34254742930949567371955861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91345981149198846325215629 34254742930949567371955861)
      ·
        refine ⟨1605691074888260970560431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 34254742930949567371955861 1605691074888260970560431)
        ·
          refine ⟨2408536612332391455840647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1605691074888260970560431 2408536612332391455840647)
          ·
            refine ⟨3612804918498587183760971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2408536612332391455840647 3612804918498587183760971)
            ·
              refine ⟨5419207377747880775641457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3612804918498587183760971 5419207377747880775641457)
              ·
                refine ⟨4064405533310910581731093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5419207377747880775641457 4064405533310910581731093)
                ·
                  refine ⟨190519009373948933518645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4064405533310910581731093 190519009373948933518645)
                  ·
                    rfl

theorem cell22_1669655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 2, 6].length) (baseStart_1669655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1669655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1669655 prefixEnd_1669655 := by exact prefixLift 1669655
  have htrace : WordTrace (prefixWord ++ tailWord_1669655) baseStart_1669655 baseEnd_1669655 := by
    simpa [prefixWord, tailWord_1669655, baseEnd_1669655] using wordTrace_append hprefix tailTrace_1669655
  have hstable : (prefixWord ++ tailWord_1669655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1669655).length < 2 ^ (prefixWord ++ tailWord_1669655).sum := by decide
  have hdescent : baseEnd_1669655 < baseStart_1669655 := by decide
  rcases family_descends (prefixWord ++ tailWord_1669655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1669672 : List Nat := [2, 1, 5, 2, 1, 2, 2, 3, 4]
def baseStart_1669672 : Nat := 118140960795 + 1669672 * 2 ^ 59
def prefixEnd_1669672 : Nat := 4983230072969 + 3 ^ 40 * 1669672 * 2
def baseEnd_1669672 : Nat := 190520949189754807626961

theorem tailTrace_1669672 : CollatzResearch.WordTrace tailWord_1669672 prefixEnd_1669672 190520949189754807626961 := by
  unfold tailWord_1669672
  simp only [CollatzResearch.WordTrace]
  refine ⟨30448970403535488060089635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40598627204713984080119513 30448970403535488060089635)
  ·
    refine ⟨45673455605303232090134453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30448970403535488060089635 45673455605303232090134453)
    ·
      refine ⟨4281886462997178008450105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 45673455605303232090134453 4281886462997178008450105)
      ·
        refine ⟨3211414847247883506337579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4281886462997178008450105 3211414847247883506337579)
        ·
          refine ⟨4817122270871825259506369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3211414847247883506337579 4817122270871825259506369)
          ·
            refine ⟨3612841703153868944629777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4817122270871825259506369 3612841703153868944629777)
            ·
              refine ⟨2709631277365401708472333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3612841703153868944629777 2709631277365401708472333)
              ·
                refine ⟨1016111729012025640677125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2709631277365401708472333 1016111729012025640677125)
                ·
                  refine ⟨190520949189754807626961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1016111729012025640677125 190520949189754807626961)
                  ·
                    rfl

theorem cell22_1669672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 2, 3, 4].length) (baseStart_1669672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1669672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1669672 prefixEnd_1669672 := by exact prefixLift 1669672
  have htrace : WordTrace (prefixWord ++ tailWord_1669672) baseStart_1669672 baseEnd_1669672 := by
    simpa [prefixWord, tailWord_1669672, baseEnd_1669672] using wordTrace_append hprefix tailTrace_1669672
  have hstable : (prefixWord ++ tailWord_1669672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1669672).length < 2 ^ (prefixWord ++ tailWord_1669672).sum := by decide
  have hdescent : baseEnd_1669672 < baseStart_1669672 := by decide
  rcases family_descends (prefixWord ++ tailWord_1669672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1669696 : List Nat := [2, 1, 1, 2, 2, 2, 2, 1, 1, 8]
def baseStart_1669696 : Nat := 118140960795 + 1669696 * 2 ^ 59
def prefixEnd_1669696 : Nat := 4983230072969 + 3 ^ 40 * 1669696 * 2
def baseEnd_1669696 : Nat := 571571063259736360280809

theorem tailTrace_1669696 : CollatzResearch.WordTrace tailWord_1669696 prefixEnd_1669696 571571063259736360280809 := by
  unfold tailWord_1669696
  simp only [CollatzResearch.WordTrace]
  refine ⟨30449408079492014109526471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40599210772656018812701961 30449408079492014109526471)
  ·
    refine ⟨45674112119238021164289707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30449408079492014109526471 45674112119238021164289707)
    ·
      refine ⟨68511168178857031746434561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45674112119238021164289707 68511168178857031746434561)
      ·
        refine ⟨51383376134142773809825921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68511168178857031746434561 51383376134142773809825921)
        ·
          refine ⟨38537532100607080357369441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51383376134142773809825921 38537532100607080357369441)
          ·
            refine ⟨28903149075455310268027081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38537532100607080357369441 28903149075455310268027081)
            ·
              refine ⟨21677361806591482701020311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28903149075455310268027081 21677361806591482701020311)
              ·
                refine ⟨32516042709887224051530467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21677361806591482701020311 32516042709887224051530467)
                ·
                  refine ⟨48774064064830836077295701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32516042709887224051530467 48774064064830836077295701)
                  ·
                    refine ⟨571571063259736360280809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 48774064064830836077295701 571571063259736360280809)
                    ·
                      rfl

theorem cell22_1669696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 1, 8].length) (baseStart_1669696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1669696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1669696 prefixEnd_1669696 := by exact prefixLift 1669696
  have htrace : WordTrace (prefixWord ++ tailWord_1669696) baseStart_1669696 baseEnd_1669696 := by
    simpa [prefixWord, tailWord_1669696, baseEnd_1669696] using wordTrace_append hprefix tailTrace_1669696
  have hstable : (prefixWord ++ tailWord_1669696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1669696).length < 2 ^ (prefixWord ++ tailWord_1669696).sum := by decide
  have hdescent : baseEnd_1669696 < baseStart_1669696 := by decide
  rcases family_descends (prefixWord ++ tailWord_1669696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1669749 : List Nat := [1, 3, 4, 2, 2, 2, 1, 1, 3, 3]
def baseStart_1669749 : Nat := 118140960795 + 1669749 * 2 ^ 59
def prefixEnd_1669749 : Nat := 4983230072969 + 3 ^ 40 * 1669749 * 2
def baseEnd_1669749 : Nat := 571589206242861888705647

theorem tailTrace_1669749 : CollatzResearch.WordTrace tailWord_1669749 prefixEnd_1669749 571589206242861888705647 := by
  unfold tailWord_1669749
  simp only [CollatzResearch.WordTrace]
  refine ⟨60900749227792018270732301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40600499485194678847154867 60900749227792018270732301)
  ·
    refine ⟨22837780960422006851524613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60900749227792018270732301 22837780960422006851524613)
    ·
      refine ⟨4282083930079126284660865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22837780960422006851524613 4282083930079126284660865)
      ·
        refine ⟨3211562947559344713495649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4282083930079126284660865 3211562947559344713495649)
        ·
          refine ⟨2408672210669508535121737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3211562947559344713495649 2408672210669508535121737)
          ·
            refine ⟨1806504158002131401341303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2408672210669508535121737 1806504158002131401341303)
            ·
              refine ⟨2709756237003197102011955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1806504158002131401341303 2709756237003197102011955)
              ·
                refine ⟨4064634355504795653017933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2709756237003197102011955 4064634355504795653017933)
                ·
                  refine ⟨1524237883314298369881725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4064634355504795653017933 1524237883314298369881725)
                  ·
                    refine ⟨571589206242861888705647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1524237883314298369881725 571589206242861888705647)
                    ·
                      rfl

theorem cell22_1669749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 1, 1, 3, 3].length) (baseStart_1669749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1669749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1669749 prefixEnd_1669749 := by exact prefixLift 1669749
  have htrace : WordTrace (prefixWord ++ tailWord_1669749) baseStart_1669749 baseEnd_1669749 := by
    simpa [prefixWord, tailWord_1669749, baseEnd_1669749] using wordTrace_append hprefix tailTrace_1669749
  have hstable : (prefixWord ++ tailWord_1669749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1669749).length < 2 ^ (prefixWord ++ tailWord_1669749).sum := by decide
  have hdescent : baseEnd_1669749 < baseStart_1669749 := by decide
  rcases family_descends (prefixWord ++ tailWord_1669749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1669807 : List Nat := [1, 1, 2, 1, 2, 5, 4, 2, 4]
def baseStart_1669807 : Nat := 118140960795 + 1669807 * 2 ^ 59
def prefixEnd_1669807 : Nat := 4983230072969 + 3 ^ 40 * 1669807 * 2
def baseEnd_1669807 : Nat := 190536353609389690251823

theorem tailTrace_1669807 : CollatzResearch.WordTrace tailWord_1669807 prefixEnd_1669807 190536353609389690251823 := by
  unfold tailWord_1669807
  simp only [CollatzResearch.WordTrace]
  refine ⟨60902864661581894176343675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40601909774387929450895783 60902864661581894176343675)
  ·
    refine ⟨91354296992372841264515513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60902864661581894176343675 91354296992372841264515513)
    ·
      refine ⟨68515722744279630948386635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91354296992372841264515513 68515722744279630948386635)
      ·
        refine ⟨102773584116419446422579953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68515722744279630948386635 102773584116419446422579953)
        ·
          refine ⟨77080188087314584816934965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102773584116419446422579953 77080188087314584816934965)
          ·
            refine ⟨7226267633185742326587653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 77080188087314584816934965 7226267633185742326587653)
            ·
              refine ⟨1354925181222326686235185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7226267633185742326587653 1354925181222326686235185)
              ·
                refine ⟨1016193885916745014676389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1354925181222326686235185 1016193885916745014676389)
                ·
                  refine ⟨190536353609389690251823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1016193885916745014676389 190536353609389690251823)
                  ·
                    rfl

theorem cell22_1669807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 4, 2, 4].length) (baseStart_1669807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1669807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1669807 prefixEnd_1669807 := by exact prefixLift 1669807
  have htrace : WordTrace (prefixWord ++ tailWord_1669807) baseStart_1669807 baseEnd_1669807 := by
    simpa [prefixWord, tailWord_1669807, baseEnd_1669807] using wordTrace_append hprefix tailTrace_1669807
  have hstable : (prefixWord ++ tailWord_1669807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1669807).length < 2 ^ (prefixWord ++ tailWord_1669807).sum := by decide
  have hdescent : baseEnd_1669807 < baseStart_1669807 := by decide
  rcases family_descends (prefixWord ++ tailWord_1669807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1669822 : List Nat := [4, 2, 1, 1, 2, 1, 1, 5, 2, 3]
def baseStart_1669822 : Nat := 118140960795 + 1669822 * 2 ^ 59
def prefixEnd_1669822 : Nat := 4983230072969 + 3 ^ 40 * 1669822 * 2
def baseEnd_1669822 : Nat := 571614195634714031630423

theorem tailTrace_1669822 : CollatzResearch.WordTrace tailWord_1669822 prefixEnd_1669822 571614195634714031630423 := by
  unfold tailWord_1669822
  simp only [CollatzResearch.WordTrace]
  refine ⟨7612926469565943967267465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40602274504351701158759813 7612926469565943967267465)
  ·
    refine ⟨5709694852174457975450599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7612926469565943967267465 5709694852174457975450599)
    ·
      refine ⟨8564542278261686963175899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5709694852174457975450599 8564542278261686963175899)
      ·
        refine ⟨12846813417392530444763849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8564542278261686963175899 12846813417392530444763849)
        ·
          refine ⟨9635110063044397833572887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12846813417392530444763849 9635110063044397833572887)
          ·
            refine ⟨14452665094566596750359331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9635110063044397833572887 14452665094566596750359331)
            ·
              refine ⟨21678997641849895125538997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14452665094566596750359331 21678997641849895125538997)
              ·
                refine ⟨2032406028923427668019281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21678997641849895125538997 2032406028923427668019281)
                ·
                  refine ⟨1524304521692570751014461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2032406028923427668019281 1524304521692570751014461)
                  ·
                    refine ⟨571614195634714031630423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1524304521692570751014461 571614195634714031630423)
                    ·
                      rfl

theorem cell22_1669822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 5, 2, 3].length) (baseStart_1669822 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1669822 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1669822 prefixEnd_1669822 := by exact prefixLift 1669822
  have htrace : WordTrace (prefixWord ++ tailWord_1669822) baseStart_1669822 baseEnd_1669822 := by
    simpa [prefixWord, tailWord_1669822, baseEnd_1669822] using wordTrace_append hprefix tailTrace_1669822
  have hstable : (prefixWord ++ tailWord_1669822).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1669822).length < 2 ^ (prefixWord ++ tailWord_1669822).sum := by decide
  have hdescent : baseEnd_1669822 < baseStart_1669822 := by decide
  rcases family_descends (prefixWord ++ tailWord_1669822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1669850 : List Nat := [3, 1, 1, 2, 2, 2, 1, 2, 5, 3]
def baseStart_1669850 : Nat := 118140960795 + 1669850 * 2 ^ 59
def prefixEnd_1669850 : Nat := 4983230072969 + 3 ^ 40 * 1669850 * 2
def baseEnd_1669850 : Nat := 571623780606931291930337

theorem tailTrace_1669850 : CollatzResearch.WordTrace tailWord_1669850 prefixEnd_1669850 571623780606931291930337 := by
  unfold tailWord_1669850
  simp only [CollatzResearch.WordTrace]
  refine ⟨15226108250106528130039751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40602955333617408346772669 15226108250106528130039751)
  ·
    refine ⟨22839162375159792195059627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15226108250106528130039751 22839162375159792195059627)
    ·
      refine ⟨34258743562739688292589441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22839162375159792195059627 34258743562739688292589441)
      ·
        refine ⟨25694057672054766219442081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34258743562739688292589441 25694057672054766219442081)
        ·
          refine ⟨19270543254041074664581561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25694057672054766219442081 19270543254041074664581561)
          ·
            refine ⟨14452907440530805998436171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19270543254041074664581561 14452907440530805998436171)
            ·
              refine ⟨21679361160796208997654257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14452907440530805998436171 21679361160796208997654257)
              ·
                refine ⟨16259520870597156748240693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21679361160796208997654257 16259520870597156748240693)
                ·
                  refine ⟨1524330081618483445147565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16259520870597156748240693 1524330081618483445147565)
                  ·
                    refine ⟨571623780606931291930337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1524330081618483445147565 571623780606931291930337)
                    ·
                      rfl

theorem cell22_1669850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 2, 5, 3].length) (baseStart_1669850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1669850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1669850 prefixEnd_1669850 := by exact prefixLift 1669850
  have htrace : WordTrace (prefixWord ++ tailWord_1669850) baseStart_1669850 baseEnd_1669850 := by
    simpa [prefixWord, tailWord_1669850, baseEnd_1669850] using wordTrace_append hprefix tailTrace_1669850
  have hstable : (prefixWord ++ tailWord_1669850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1669850).length < 2 ^ (prefixWord ++ tailWord_1669850).sum := by decide
  have hdescent : baseEnd_1669850 < baseStart_1669850 := by decide
  rcases family_descends (prefixWord ++ tailWord_1669850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1669893 : List Nat := [1, 3, 1, 1, 2, 1, 1, 2, 2, 8]
def baseStart_1669893 : Nat := 118140960795 + 1669893 * 2 ^ 59
def prefixEnd_1669893 : Nat := 4983230072969 + 3 ^ 40 * 1669893 * 2
def baseEnd_1669893 : Nat := 571638500385693513105205

theorem tailTrace_1669893 : CollatzResearch.WordTrace tailWord_1669893 prefixEnd_1669893 571638500385693513105205 := by
  unfold tailWord_1669893
  simp only [CollatzResearch.WordTrace]
  refine ⟨60906001339270330863974333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40604000892846887242649555 60906001339270330863974333)
  ·
    refine ⟨22839750502226374073990375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60906001339270330863974333 22839750502226374073990375)
    ·
      refine ⟨34259625753339561110985563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22839750502226374073990375 34259625753339561110985563)
      ·
        refine ⟨51389438630009341666478345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34259625753339561110985563 51389438630009341666478345)
        ·
          refine ⟨38542078972507006249858759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51389438630009341666478345 38542078972507006249858759)
          ·
            refine ⟨57813118458760509374788139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38542078972507006249858759 57813118458760509374788139)
            ·
              refine ⟨86719677688140764062182209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57813118458760509374788139 86719677688140764062182209)
              ·
                refine ⟨65039758266105573046636657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86719677688140764062182209 65039758266105573046636657)
                ·
                  refine ⟨48779818699579179784977493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65039758266105573046636657 48779818699579179784977493)
                  ·
                    refine ⟨571638500385693513105205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 48779818699579179784977493 571638500385693513105205)
                    ·
                      rfl

theorem cell22_1669893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 2, 8].length) (baseStart_1669893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1669893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1669893 prefixEnd_1669893 := by exact prefixLift 1669893
  have htrace : WordTrace (prefixWord ++ tailWord_1669893) baseStart_1669893 baseEnd_1669893 := by
    simpa [prefixWord, tailWord_1669893, baseEnd_1669893] using wordTrace_append hprefix tailTrace_1669893
  have hstable : (prefixWord ++ tailWord_1669893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1669893).length < 2 ^ (prefixWord ++ tailWord_1669893).sum := by decide
  have hdescent : baseEnd_1669893 < baseStart_1669893 := by decide
  rcases family_descends (prefixWord ++ tailWord_1669893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1669987 : List Nat := [1, 1, 1, 5, 3, 3, 1, 7]
def baseStart_1669987 : Nat := 118140960795 + 1669987 * 2 ^ 59
def prefixEnd_1669987 : Nat := 4983230072969 + 3 ^ 40 * 1669987 * 2
def baseEnd_1669987 : Nat := 63518964278523177917213

theorem tailTrace_1669987 : CollatzResearch.WordTrace tailWord_1669987 prefixEnd_1669987 63518964278523177917213 := by
  unfold tailWord_1669987
  simp only [CollatzResearch.WordTrace]
  refine ⟨60909429800929784917896215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40606286533953189945264143 60909429800929784917896215)
  ·
    refine ⟨91364144701394677376844323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60909429800929784917896215 91364144701394677376844323)
    ·
      refine ⟨137046217052092016065266485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91364144701394677376844323 137046217052092016065266485)
      ·
        refine ⟨12848082848633626506118733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 137046217052092016065266485 12848082848633626506118733)
        ·
          refine ⟨4818031068237609939794525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12848082848633626506118733 4818031068237609939794525)
          ·
            refine ⟨1806761650589103727422947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4818031068237609939794525 1806761650589103727422947)
            ·
              refine ⟨2710142475883655591134421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1806761650589103727422947 2710142475883655591134421)
              ·
                refine ⟨63518964278523177917213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2710142475883655591134421 63518964278523177917213)
                ·
                  rfl

theorem cell22_1669987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 1, 7].length) (baseStart_1669987 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1669987 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1669987 prefixEnd_1669987 := by exact prefixLift 1669987
  have htrace : WordTrace (prefixWord ++ tailWord_1669987) baseStart_1669987 baseEnd_1669987 := by
    simpa [prefixWord, tailWord_1669987, baseEnd_1669987] using wordTrace_append hprefix tailTrace_1669987
  have hstable : (prefixWord ++ tailWord_1669987).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1669987).length < 2 ^ (prefixWord ++ tailWord_1669987).sum := by decide
  have hdescent : baseEnd_1669987 < baseStart_1669987 := by decide
  rcases family_descends (prefixWord ++ tailWord_1669987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1670002 : List Nat := [3, 2, 1, 2, 1, 1, 3, 1, 5, 3]
def baseStart_1670002 : Nat := 118140960795 + 1670002 * 2 ^ 59
def prefixEnd_1670002 : Nat := 4983230072969 + 3 ^ 40 * 1670002 * 2
def baseEnd_1670002 : Nat := 571675813313253562129871

theorem tailTrace_1670002 : CollatzResearch.WordTrace tailWord_1670002 prefixEnd_1670002 571675813313253562129871 := by
  unfold tailWord_1670002
  simp only [CollatzResearch.WordTrace]
  refine ⟨15227494223968860619923065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40606651263916961653128173 15227494223968860619923065)
  ·
    refine ⟨11420620667976645464942299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15227494223968860619923065 11420620667976645464942299)
    ·
      refine ⟨17130931001964968197413449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11420620667976645464942299 17130931001964968197413449)
      ·
        refine ⟨12848198251473726148060087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17130931001964968197413449 12848198251473726148060087)
        ·
          refine ⟨19272297377210589222090131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12848198251473726148060087 19272297377210589222090131)
          ·
            refine ⟨28908446065815883833135197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19272297377210589222090131 28908446065815883833135197)
            ·
              refine ⟨10840667274680956437425699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28908446065815883833135197 10840667274680956437425699)
              ·
                refine ⟨16261000912021434656138549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10840667274680956437425699 16261000912021434656138549)
                ·
                  refine ⟨1524468835502009499012989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16261000912021434656138549 1524468835502009499012989)
                  ·
                    refine ⟨571675813313253562129871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1524468835502009499012989 571675813313253562129871)
                    ·
                      rfl

theorem cell22_1670002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 1, 5, 3].length) (baseStart_1670002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1670002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1670002 prefixEnd_1670002 := by exact prefixLift 1670002
  have htrace : WordTrace (prefixWord ++ tailWord_1670002) baseStart_1670002 baseEnd_1670002 := by
    simpa [prefixWord, tailWord_1670002, baseEnd_1670002] using wordTrace_append hprefix tailTrace_1670002
  have hstable : (prefixWord ++ tailWord_1670002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1670002).length < 2 ^ (prefixWord ++ tailWord_1670002).sum := by decide
  have hdescent : baseEnd_1670002 < baseStart_1670002 := by decide
  rcases family_descends (prefixWord ++ tailWord_1670002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1670006 : List Nat := [5, 1, 1, 3, 1, 3, 1, 1, 2, 4]
def baseStart_1670006 : Nat := 118140960795 + 1670006 * 2 ^ 59
def prefixEnd_1670006 : Nat := 4983230072969 + 3 ^ 40 * 1670006 * 2
def baseEnd_1670006 : Nat := 571677182594998885029859

theorem tailTrace_1670006 : CollatzResearch.WordTrace tailWord_1670006 prefixEnd_1670006 571677182594998885029859 := by
  unfold tailWord_1670006
  simp only [CollatzResearch.WordTrace]
  refine ⟨3806882674241309447677367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40606748525240634108558581 3806882674241309447677367)
  ·
    refine ⟨5710324011361964171516051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3806882674241309447677367 5710324011361964171516051)
    ·
      refine ⟨8565486017042946257274077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5710324011361964171516051 8565486017042946257274077)
      ·
        refine ⟨3212057256391104846477779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8565486017042946257274077 3212057256391104846477779)
        ·
          refine ⟨4818085884586657269716669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3212057256391104846477779 4818085884586657269716669)
          ·
            refine ⟨1806782206719996476143751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4818085884586657269716669 1806782206719996476143751)
            ·
              refine ⟨2710173310079994714215627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1806782206719996476143751 2710173310079994714215627)
              ·
                refine ⟨4065259965119992071323441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2710173310079994714215627 4065259965119992071323441)
                ·
                  refine ⟨3048944973839994053492581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4065259965119992071323441 3048944973839994053492581)
                  ·
                    refine ⟨571677182594998885029859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3048944973839994053492581 571677182594998885029859)
                    ·
                      rfl

theorem cell22_1670006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 1, 1, 2, 4].length) (baseStart_1670006 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1670006 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1670006 prefixEnd_1670006 := by exact prefixLift 1670006
  have htrace : WordTrace (prefixWord ++ tailWord_1670006) baseStart_1670006 baseEnd_1670006 := by
    simpa [prefixWord, tailWord_1670006, baseEnd_1670006] using wordTrace_append hprefix tailTrace_1670006
  have hstable : (prefixWord ++ tailWord_1670006).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1670006).length < 2 ^ (prefixWord ++ tailWord_1670006).sum := by decide
  have hdescent : baseEnd_1670006 < baseStart_1670006 := by decide
  rcases family_descends (prefixWord ++ tailWord_1670006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1670036 : List Nat := [2, 4, 2, 1, 1, 1, 1, 6, 1, 3]
def baseStart_1670036 : Nat := 118140960795 + 1670036 * 2 ^ 59
def prefixEnd_1670036 : Nat := 4983230072969 + 3 ^ 40 * 1670036 * 2
def baseEnd_1670036 : Nat := 571687452208088806779767

theorem tailTrace_1670036 : CollatzResearch.WordTrace tailWord_1670036 prefixEnd_1670036 571687452208088806779767 := by
  unfold tailWord_1670036
  simp only [CollatzResearch.WordTrace]
  refine ⟨30455608488876133143214981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40607477985168177524286641 30455608488876133143214981)
  ·
    refine ⟨5710426591664274964352809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30455608488876133143214981 5710426591664274964352809)
    ·
      refine ⟨4282819943748206223264607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5710426591664274964352809 4282819943748206223264607)
      ·
        refine ⟨6424229915622309334896911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4282819943748206223264607 6424229915622309334896911)
        ·
          refine ⟨9636344873433464002345367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6424229915622309334896911 9636344873433464002345367)
          ·
            refine ⟨14454517310150196003518051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9636344873433464002345367 14454517310150196003518051)
            ·
              refine ⟨21681775965225294005277077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14454517310150196003518051 21681775965225294005277077)
              ·
                refine ⟨1016333248369935656497363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 21681775965225294005277077 1016333248369935656497363)
                ·
                  refine ⟨1524499872554903484746045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1016333248369935656497363 1524499872554903484746045)
                  ·
                    refine ⟨571687452208088806779767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1524499872554903484746045 571687452208088806779767)
                    ·
                      rfl

theorem cell22_1670036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 6, 1, 3].length) (baseStart_1670036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1670036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1670036 prefixEnd_1670036 := by exact prefixLift 1670036
  have htrace : WordTrace (prefixWord ++ tailWord_1670036) baseStart_1670036 baseEnd_1670036 := by
    simpa [prefixWord, tailWord_1670036, baseEnd_1670036] using wordTrace_append hprefix tailTrace_1670036
  have hstable : (prefixWord ++ tailWord_1670036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1670036).length < 2 ^ (prefixWord ++ tailWord_1670036).sum := by decide
  have hdescent : baseEnd_1670036 < baseStart_1670036 := by decide
  rcases family_descends (prefixWord ++ tailWord_1670036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1670047 : List Nat := [1, 1, 2, 5, 2, 1, 2, 1, 2, 5]
def baseStart_1670047 : Nat := 118140960795 + 1670047 * 2 ^ 59
def prefixEnd_1670047 : Nat := 4983230072969 + 3 ^ 40 * 1670047 * 2
def baseEnd_1670047 : Nat := 571691217732888444754733

theorem tailTrace_1670047 : CollatzResearch.WordTrace tailWord_1670047 prefixEnd_1670047 571691217732888444754733 := by
  unfold tailWord_1670047
  simp only [CollatzResearch.WordTrace]
  refine ⟨60911618180712415165080395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40607745453808276776720263 60911618180712415165080395)
  ·
    refine ⟨91367427271068622747620593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60911618180712415165080395 91367427271068622747620593)
    ·
      refine ⟨68525570453301467060715445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91367427271068622747620593 68525570453301467060715445)
      ·
        refine ⟨6424272229997012536942073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 68525570453301467060715445 6424272229997012536942073)
        ·
          refine ⟨4818204172497759402706555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6424272229997012536942073 4818204172497759402706555)
          ·
            refine ⟨7227306258746639104059833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4818204172497759402706555 7227306258746639104059833)
            ·
              refine ⟨5420479694059979328044875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7227306258746639104059833 5420479694059979328044875)
              ·
                refine ⟨8130719541089968992067313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5420479694059979328044875 8130719541089968992067313)
                ·
                  refine ⟨6098039655817476744050485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8130719541089968992067313 6098039655817476744050485)
                  ·
                    refine ⟨571691217732888444754733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6098039655817476744050485 571691217732888444754733)
                    ·
                      rfl

theorem cell22_1670047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 1, 2, 5].length) (baseStart_1670047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1670047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1670047 prefixEnd_1670047 := by exact prefixLift 1670047
  have htrace : WordTrace (prefixWord ++ tailWord_1670047) baseStart_1670047 baseEnd_1670047 := by
    simpa [prefixWord, tailWord_1670047, baseEnd_1670047] using wordTrace_append hprefix tailTrace_1670047
  have hstable : (prefixWord ++ tailWord_1670047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1670047).length < 2 ^ (prefixWord ++ tailWord_1670047).sum := by decide
  have hdescent : baseEnd_1670047 < baseStart_1670047 := by decide
  rcases family_descends (prefixWord ++ tailWord_1670047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1670094 : List Nat := [4, 1, 1, 1, 2, 5, 1, 1, 6]
def baseStart_1670094 : Nat := 118140960795 + 1670094 * 2 ^ 59
def prefixEnd_1670094 : Nat := 4983230072969 + 3 ^ 40 * 1670094 * 2
def baseEnd_1670094 : Nat := 190569102264465329609863

theorem tailTrace_1670094 : CollatzResearch.WordTrace tailWord_1670094 prefixEnd_1670094 190569102264465329609863 := by
  unfold tailWord_1670094
  simp only [CollatzResearch.WordTrace]
  refine ⟨7614166551442767774005167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40608888274361428128027557 7614166551442767774005167)
  ·
    refine ⟨11421249827164151661007751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7614166551442767774005167 11421249827164151661007751)
    ·
      refine ⟨17131874740746227491511627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11421249827164151661007751 17131874740746227491511627)
      ·
        refine ⟨25697812111119341237267441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17131874740746227491511627 25697812111119341237267441)
        ·
          refine ⟨19273359083339505927950581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25697812111119341237267441 19273359083339505927950581)
          ·
            refine ⟨1806877414063078680745367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19273359083339505927950581 1806877414063078680745367)
            ·
              refine ⟨2710316121094618021118051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1806877414063078680745367 2710316121094618021118051)
              ·
                refine ⟨4065474181641927031677077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2710316121094618021118051 4065474181641927031677077)
                ·
                  refine ⟨190569102264465329609863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4065474181641927031677077 190569102264465329609863)
                  ·
                    rfl

theorem cell22_1670094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 1, 1, 6].length) (baseStart_1670094 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1670094 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1670094 prefixEnd_1670094 := by exact prefixLift 1670094
  have htrace : WordTrace (prefixWord ++ tailWord_1670094) baseStart_1670094 baseEnd_1670094 := by
    simpa [prefixWord, tailWord_1670094, baseEnd_1670094] using wordTrace_append hprefix tailTrace_1670094
  have hstable : (prefixWord ++ tailWord_1670094).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1670094).length < 2 ^ (prefixWord ++ tailWord_1670094).sum := by decide
  have hdescent : baseEnd_1670094 < baseStart_1670094 := by decide
  rcases family_descends (prefixWord ++ tailWord_1670094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1670122 : List Nat := [3, 1, 3, 1, 2, 2, 2, 8]
def baseStart_1670122 : Nat := 118140960795 + 1670122 * 2 ^ 59
def prefixEnd_1670122 : Nat := 4983230072969 + 3 ^ 40 * 1670122 * 2
def baseEnd_1670122 : Nat := 63524099085068138792167

theorem tailTrace_1670122 : CollatzResearch.WordTrace tailWord_1670122 prefixEnd_1670122 63524099085068138792167 := by
  unfold tailWord_1670122
  simp only [CollatzResearch.WordTrace]
  refine ⟨15228588413860175743515155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40609569103627135316040413 15228588413860175743515155)
  ·
    refine ⟨22842882620790263615272733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15228588413860175743515155 22842882620790263615272733)
    ·
      refine ⟨8566080982796348855727275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22842882620790263615272733 8566080982796348855727275)
      ·
        refine ⟨12849121474194523283590913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8566080982796348855727275 12849121474194523283590913)
        ·
          refine ⟨9636841105645892462693185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12849121474194523283590913 9636841105645892462693185)
          ·
            refine ⟨7227630829234419347019889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9636841105645892462693185 7227630829234419347019889)
            ·
              refine ⟨5420723121925814510264917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7227630829234419347019889 5420723121925814510264917)
              ·
                refine ⟨63524099085068138792167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5420723121925814510264917 63524099085068138792167)
                ·
                  rfl

theorem cell22_1670122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 8].length) (baseStart_1670122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1670122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1670122 prefixEnd_1670122 := by exact prefixLift 1670122
  have htrace : WordTrace (prefixWord ++ tailWord_1670122) baseStart_1670122 baseEnd_1670122 := by
    simpa [prefixWord, tailWord_1670122, baseEnd_1670122] using wordTrace_append hprefix tailTrace_1670122
  have hstable : (prefixWord ++ tailWord_1670122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1670122).length < 2 ^ (prefixWord ++ tailWord_1670122).sum := by decide
  have hdescent : baseEnd_1670122 < baseStart_1670122 := by decide
  rcases family_descends (prefixWord ++ tailWord_1670122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1670152 : List Nat := [2, 1, 3, 2, 1, 3, 1, 1, 2, 6]
def baseStart_1670152 : Nat := 118140960795 + 1670152 * 2 ^ 59
def prefixEnd_1670152 : Nat := 4983230072969 + 3 ^ 40 * 1670152 * 2
def baseEnd_1670152 : Nat := 571727161378703170879411

theorem tailTrace_1670152 : CollatzResearch.WordTrace tailWord_1670152 prefixEnd_1670152 571727161378703170879411 := by
  unfold tailWord_1670152
  simp only [CollatzResearch.WordTrace]
  refine ⟨30457723922666009048826355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40610298563554678731768473 30457723922666009048826355)
  ·
    refine ⟨45686585883999013573239533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30457723922666009048826355 45686585883999013573239533)
    ·
      refine ⟨17132469706499630089964825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45686585883999013573239533 17132469706499630089964825)
      ·
        refine ⟨12849352279874722567473619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17132469706499630089964825 12849352279874722567473619)
        ·
          refine ⟨19274028419812083851210429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12849352279874722567473619 19274028419812083851210429)
          ·
            refine ⟨7227760657429531444203911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19274028419812083851210429 7227760657429531444203911)
            ·
              refine ⟨10841640986144297166305867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7227760657429531444203911 10841640986144297166305867)
              ·
                refine ⟨16262461479216445749458801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10841640986144297166305867 16262461479216445749458801)
                ·
                  refine ⟨12196846109412334312094101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16262461479216445749458801 12196846109412334312094101)
                  ·
                    refine ⟨571727161378703170879411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12196846109412334312094101 571727161378703170879411)
                    ·
                      rfl

theorem cell22_1670152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 1, 2, 6].length) (baseStart_1670152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1670152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1670152 prefixEnd_1670152 := by exact prefixLift 1670152
  have htrace : WordTrace (prefixWord ++ tailWord_1670152) baseStart_1670152 baseEnd_1670152 := by
    simpa [prefixWord, tailWord_1670152, baseEnd_1670152] using wordTrace_append hprefix tailTrace_1670152
  have hstable : (prefixWord ++ tailWord_1670152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1670152).length < 2 ^ (prefixWord ++ tailWord_1670152).sum := by decide
  have hdescent : baseEnd_1670152 < baseStart_1670152 := by decide
  rcases family_descends (prefixWord ++ tailWord_1670152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1670201 : List Nat := [1, 2, 1, 5, 2, 3, 1, 2, 5]
def baseStart_1670201 : Nat := 118140960795 + 1670201 * 2 ^ 59
def prefixEnd_1670201 : Nat := 4983230072969 + 3 ^ 40 * 1670201 * 2
def baseEnd_1670201 : Nat := 190581311693361125468087

theorem tailTrace_1670201 : CollatzResearch.WordTrace tailWord_1670201 prefixEnd_1670201 190581311693361125468087 := by
  unfold tailWord_1670201
  simp only [CollatzResearch.WordTrace]
  refine ⟨60917235022154499466186457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40611490014769666310790971 60917235022154499466186457)
  ·
    refine ⟨45687926266615874599639843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60917235022154499466186457 45687926266615874599639843)
    ·
      refine ⟨68531889399923811899459765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45687926266615874599639843 68531889399923811899459765)
      ·
        refine ⟨6424864631242857365574353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 68531889399923811899459765 6424864631242857365574353)
        ·
          refine ⟨4818648473432143024180765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6424864631242857365574353 4818648473432143024180765)
          ·
            refine ⟨1806993177537053634067787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4818648473432143024180765 1806993177537053634067787)
            ·
              refine ⟨2710489766305580451101681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1806993177537053634067787 2710489766305580451101681)
              ·
                refine ⟨2032867324729185338326261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2710489766305580451101681 2032867324729185338326261)
                ·
                  refine ⟨190581311693361125468087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2032867324729185338326261 190581311693361125468087)
                  ·
                    rfl

theorem cell22_1670201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 1, 2, 5].length) (baseStart_1670201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1670201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1670201 prefixEnd_1670201 := by exact prefixLift 1670201
  have htrace : WordTrace (prefixWord ++ tailWord_1670201) baseStart_1670201 baseEnd_1670201 := by
    simpa [prefixWord, tailWord_1670201, baseEnd_1670201] using wordTrace_append hprefix tailTrace_1670201
  have hstable : (prefixWord ++ tailWord_1670201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1670201).length < 2 ^ (prefixWord ++ tailWord_1670201).sum := by decide
  have hdescent : baseEnd_1670201 < baseStart_1670201 := by decide
  rcases family_descends (prefixWord ++ tailWord_1670201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1670319 : List Nat := [1, 1, 2, 1, 2, 3, 3, 4, 5]
def baseStart_1670319 : Nat := 118140960795 + 1670319 * 2 ^ 59
def prefixEnd_1670319 : Nat := 4983230072969 + 3 ^ 40 * 1670319 * 2
def baseEnd_1670319 : Nat := 190594776297190133984633

theorem tailTrace_1670319 : CollatzResearch.WordTrace tailWord_1670319 prefixEnd_1670319 190594776297190133984633 := by
  unfold tailWord_1670319
  simp only [CollatzResearch.WordTrace]
  refine ⟨60921538835727005618982011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40614359223818003745988007 60921538835727005618982011)
  ·
    refine ⟨91382308253590508428473017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60921538835727005618982011 91382308253590508428473017)
    ·
      refine ⟨68536731190192881321354763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91382308253590508428473017 68536731190192881321354763)
      ·
        refine ⟨102805096785289321982032145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68536731190192881321354763 102805096785289321982032145)
        ·
          refine ⟨77103822588966991486524109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102805096785289321982032145 77103822588966991486524109)
          ·
            refine ⟨28913933470862621807446541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77103822588966991486524109 28913933470862621807446541)
            ·
              refine ⟨10842725051573483177792453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28913933470862621807446541 10842725051573483177792453)
              ·
                refine ⟨2033010947170028095836085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10842725051573483177792453 2033010947170028095836085)
                ·
                  refine ⟨190594776297190133984633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2033010947170028095836085 190594776297190133984633)
                  ·
                    rfl

theorem cell22_1670319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 4, 5].length) (baseStart_1670319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1670319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1670319 prefixEnd_1670319 := by exact prefixLift 1670319
  have htrace : WordTrace (prefixWord ++ tailWord_1670319) baseStart_1670319 baseEnd_1670319 := by
    simpa [prefixWord, tailWord_1670319, baseEnd_1670319] using wordTrace_append hprefix tailTrace_1670319
  have hstable : (prefixWord ++ tailWord_1670319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1670319).length < 2 ^ (prefixWord ++ tailWord_1670319).sum := by decide
  have hdescent : baseEnd_1670319 < baseStart_1670319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1670319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1670342 : List Nat := [6, 1, 2, 2, 1, 1, 3, 6]
def baseStart_1670342 : Nat := 118140960795 + 1670342 * 2 ^ 59
def prefixEnd_1670342 : Nat := 4983230072969 + 3 ^ 40 * 1670342 * 2
def baseEnd_1670342 : Nat := 63532466917956223180981

theorem tailTrace_1670342 : CollatzResearch.WordTrace tailWord_1670342 prefixEnd_1670342 63532466917956223180981 := by
  unfold tailWord_1670342
  simp only [CollatzResearch.WordTrace]
  refine ⟨1903824303582615017095915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 40614918476429120364712853 1903824303582615017095915)
  ·
    refine ⟨2855736455373922525643873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1903824303582615017095915 2855736455373922525643873)
    ·
      refine ⟨2141802341530441894232905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2855736455373922525643873 2141802341530441894232905)
      ·
        refine ⟨1606351756147831420674679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2141802341530441894232905 1606351756147831420674679)
        ·
          refine ⟨2409527634221747131012019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1606351756147831420674679 2409527634221747131012019)
          ·
            refine ⟨3614291451332620696518029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2409527634221747131012019 3614291451332620696518029)
            ·
              refine ⟨1355359294249732761194261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3614291451332620696518029 1355359294249732761194261)
              ·
                refine ⟨63532466917956223180981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1355359294249732761194261 63532466917956223180981)
                ·
                  rfl

theorem cell22_1670342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 3, 6].length) (baseStart_1670342 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1670342 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1670342 prefixEnd_1670342 := by exact prefixLift 1670342
  have htrace : WordTrace (prefixWord ++ tailWord_1670342) baseStart_1670342 baseEnd_1670342 := by
    simpa [prefixWord, tailWord_1670342, baseEnd_1670342] using wordTrace_append hprefix tailTrace_1670342
  have hstable : (prefixWord ++ tailWord_1670342).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1670342).length < 2 ^ (prefixWord ++ tailWord_1670342).sum := by decide
  have hdescent : baseEnd_1670342 < baseStart_1670342 := by decide
  rcases family_descends (prefixWord ++ tailWord_1670342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1670381 : List Nat := [1, 5, 1, 2, 2, 1, 1, 3, 6]
def baseStart_1670381 : Nat := 118140960795 + 1670381 * 2 ^ 59
def prefixEnd_1670381 : Nat := 4983230072969 + 3 ^ 40 * 1670381 * 2
def baseEnd_1670381 : Nat := 190601850919540968967903

theorem tailTrace_1670381 : CollatzResearch.WordTrace tailWord_1670381 prefixEnd_1670381 190601850919540968967903 := by
  unfold tailWord_1670381
  simp only [CollatzResearch.WordTrace]
  refine ⟨60923800161502390207738997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40615866774334926805159331 60923800161502390207738997)
  ·
    refine ⟨5711606265140849081975531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 60923800161502390207738997 5711606265140849081975531)
    ·
      refine ⟨8567409397711273622963297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5711606265140849081975531 8567409397711273622963297)
      ·
        refine ⟨6425557048283455217222473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8567409397711273622963297 6425557048283455217222473)
        ·
          refine ⟨4819167786212591412916855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6425557048283455217222473 4819167786212591412916855)
          ·
            refine ⟨7228751679318887119375283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4819167786212591412916855 7228751679318887119375283)
            ·
              refine ⟨10843127518978330679062925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7228751679318887119375283 10843127518978330679062925)
              ·
                refine ⟨4066172819616874004648597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10843127518978330679062925 4066172819616874004648597)
                ·
                  refine ⟨190601850919540968967903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4066172819616874004648597 190601850919540968967903)
                  ·
                    rfl

theorem cell22_1670381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 3, 6].length) (baseStart_1670381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1670381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1670381 prefixEnd_1670381 := by exact prefixLift 1670381
  have htrace : WordTrace (prefixWord ++ tailWord_1670381) baseStart_1670381 baseEnd_1670381 := by
    simpa [prefixWord, tailWord_1670381, baseEnd_1670381] using wordTrace_append hprefix tailTrace_1670381
  have hstable : (prefixWord ++ tailWord_1670381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1670381).length < 2 ^ (prefixWord ++ tailWord_1670381).sum := by decide
  have hdescent : baseEnd_1670381 < baseStart_1670381 := by decide
  rcases family_descends (prefixWord ++ tailWord_1670381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1670394 : List Nat := [3, 1, 1, 1, 1, 4, 1, 1, 3, 6]
def baseStart_1670394 : Nat := 118140960795 + 1670394 * 2 ^ 59
def prefixEnd_1670394 : Nat := 4983230072969 + 3 ^ 40 * 1670394 * 2
def baseEnd_1670394 : Nat := 571810002924295206328669

theorem tailTrace_1670394 : CollatzResearch.WordTrace tailWord_1670394 prefixEnd_1670394 571810002924295206328669 := by
  unfold tailWord_1670394
  simp only [CollatzResearch.WordTrace]
  refine ⟨15231068577613823356990559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40616182873636862285308157 15231068577613823356990559)
  ·
    refine ⟨22846602866420735035485839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15231068577613823356990559 22846602866420735035485839)
    ·
      refine ⟨34269904299631102553228759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22846602866420735035485839 34269904299631102553228759)
      ·
        refine ⟨51404856449446653829843139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34269904299631102553228759 51404856449446653829843139)
        ·
          refine ⟨77107284674169980744764709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51404856449446653829843139 77107284674169980744764709)
          ·
            refine ⟨14457615876406871389643383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77107284674169980744764709 14457615876406871389643383)
            ·
              refine ⟨21686423814610307084465075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14457615876406871389643383 21686423814610307084465075)
              ·
                refine ⟨32529635721915460626697613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21686423814610307084465075 32529635721915460626697613)
                ·
                  refine ⟨12198613395718297735011605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32529635721915460626697613 12198613395718297735011605)
                  ·
                    refine ⟨571810002924295206328669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12198613395718297735011605 571810002924295206328669)
                    ·
                      rfl

theorem cell22_1670394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 1, 3, 6].length) (baseStart_1670394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1670394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1670394 prefixEnd_1670394 := by exact prefixLift 1670394
  have htrace : WordTrace (prefixWord ++ tailWord_1670394) baseStart_1670394 baseEnd_1670394 := by
    simpa [prefixWord, tailWord_1670394, baseEnd_1670394] using wordTrace_append hprefix tailTrace_1670394
  have hstable : (prefixWord ++ tailWord_1670394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1670394).length < 2 ^ (prefixWord ++ tailWord_1670394).sum := by decide
  have hdescent : baseEnd_1670394 < baseStart_1670394 := by decide
  rcases family_descends (prefixWord ++ tailWord_1670394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1670409 : List Nat := [1, 2, 1, 1, 3, 3, 3, 8]
def baseStart_1670409 : Nat := 118140960795 + 1670409 * 2 ^ 59
def prefixEnd_1670409 : Nat := 4983230072969 + 3 ^ 40 * 1670409 * 2
def baseEnd_1670409 : Nat := 63535015303426685244847

theorem tailTrace_1670409 : CollatzResearch.WordTrace tailWord_1670409 prefixEnd_1670409 63535015303426685244847 := by
  unfold tailWord_1670409
  simp only [CollatzResearch.WordTrace]
  refine ⟨60924821405400950989758281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40616547603600633993172187 60924821405400950989758281)
  ·
    refine ⟨45693616054050713242318711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60924821405400950989758281 45693616054050713242318711)
    ·
      refine ⟨68540424081076069863478067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45693616054050713242318711 68540424081076069863478067)
      ·
        refine ⟨102810636121614104795217101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68540424081076069863478067 102810636121614104795217101)
        ·
          refine ⟨38553988545605289298206413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102810636121614104795217101 38553988545605289298206413)
          ·
            refine ⟨14457745704601983486827405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38553988545605289298206413 14457745704601983486827405)
            ·
              refine ⟨5421654639225743807560277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14457745704601983486827405 5421654639225743807560277)
              ·
                refine ⟨63535015303426685244847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5421654639225743807560277 63535015303426685244847)
                ·
                  rfl

theorem cell22_1670409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 8].length) (baseStart_1670409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1670409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1670409 prefixEnd_1670409 := by exact prefixLift 1670409
  have htrace : WordTrace (prefixWord ++ tailWord_1670409) baseStart_1670409 baseEnd_1670409 := by
    simpa [prefixWord, tailWord_1670409, baseEnd_1670409] using wordTrace_append hprefix tailTrace_1670409
  have hstable : (prefixWord ++ tailWord_1670409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1670409).length < 2 ^ (prefixWord ++ tailWord_1670409).sum := by decide
  have hdescent : baseEnd_1670409 < baseStart_1670409 := by decide
  rcases family_descends (prefixWord ++ tailWord_1670409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1670426 : List Nat := [3, 1, 1, 3, 3, 3, 8]
def baseStart_1670426 : Nat := 118140960795 + 1670426 * 2 ^ 59
def prefixEnd_1670426 : Nat := 4983230072969 + 3 ^ 40 * 1670426 * 2
def baseEnd_1670426 : Nat := 21178553969565103315873

theorem tailTrace_1670426 : CollatzResearch.WordTrace tailWord_1670426 prefixEnd_1670426 21178553969565103315873 := by
  unfold tailWord_1670426
  simp only [CollatzResearch.WordTrace]
  refine ⟨15231360361584840723281783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40616960964226241928751421 15231360361584840723281783)
  ·
    refine ⟨22847040542377261084922675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15231360361584840723281783 22847040542377261084922675)
    ·
      refine ⟨34270560813565891627384013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22847040542377261084922675 34270560813565891627384013)
      ·
        refine ⟨12851460305087209360269005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34270560813565891627384013 12851460305087209360269005)
        ·
          refine ⟨4819297614407703510100877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12851460305087209360269005 4819297614407703510100877)
          ·
            refine ⟨1807236605402888816287829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4819297614407703510100877 1807236605402888816287829)
            ·
              refine ⟨21178553969565103315873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1807236605402888816287829 21178553969565103315873)
              ·
                rfl

theorem cell22_1670426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 8].length) (baseStart_1670426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1670426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1670426 prefixEnd_1670426 := by exact prefixLift 1670426
  have htrace : WordTrace (prefixWord ++ tailWord_1670426) baseStart_1670426 baseEnd_1670426 := by
    simpa [prefixWord, tailWord_1670426, baseEnd_1670426] using wordTrace_append hprefix tailTrace_1670426
  have hstable : (prefixWord ++ tailWord_1670426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1670426).length < 2 ^ (prefixWord ++ tailWord_1670426).sum := by decide
  have hdescent : baseEnd_1670426 < baseStart_1670426 := by decide
  rcases family_descends (prefixWord ++ tailWord_1670426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1670501 : List Nat := [1, 3, 1, 3, 1, 2, 1, 1, 5, 4]
def baseStart_1670501 : Nat := 118140960795 + 1670501 * 2 ^ 59
def prefixEnd_1670501 : Nat := 4983230072969 + 3 ^ 40 * 1670501 * 2
def baseEnd_1670501 : Nat := 571846631210982593903341

theorem tailTrace_1670501 : CollatzResearch.WordTrace tailWord_1670501 prefixEnd_1670501 571846631210982593903341 := by
  unfold tailWord_1670501
  simp only [CollatzResearch.WordTrace]
  refine ⟨60928176921067650702107357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40618784614045100468071571 60928176921067650702107357)
  ·
    refine ⟨22848066345400369013290259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60928176921067650702107357 22848066345400369013290259)
    ·
      refine ⟨34272099518100553519935389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22848066345400369013290259 34272099518100553519935389)
      ·
        refine ⟨12852037319287707569975771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34272099518100553519935389 12852037319287707569975771)
        ·
          refine ⟨19278055978931561354963657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12852037319287707569975771 19278055978931561354963657)
          ·
            refine ⟨14458541984198671016222743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19278055978931561354963657 14458541984198671016222743)
            ·
              refine ⟨21687812976298006524334115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14458541984198671016222743 21687812976298006524334115)
              ·
                refine ⟨32531719464447009786501173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21687812976298006524334115 32531719464447009786501173)
                ·
                  refine ⟨3049848699791907167484485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32531719464447009786501173 3049848699791907167484485)
                  ·
                    refine ⟨571846631210982593903341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3049848699791907167484485 571846631210982593903341)
                    ·
                      rfl

theorem cell22_1670501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 1, 5, 4].length) (baseStart_1670501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1670501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1670501 prefixEnd_1670501 := by exact prefixLift 1670501
  have htrace : WordTrace (prefixWord ++ tailWord_1670501) baseStart_1670501 baseEnd_1670501 := by
    simpa [prefixWord, tailWord_1670501, baseEnd_1670501] using wordTrace_append hprefix tailTrace_1670501
  have hstable : (prefixWord ++ tailWord_1670501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1670501).length < 2 ^ (prefixWord ++ tailWord_1670501).sum := by decide
  have hdescent : baseEnd_1670501 < baseStart_1670501 := by decide
  rcases family_descends (prefixWord ++ tailWord_1670501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1670503 : List Nat := [1, 1, 5, 1, 4, 1, 1, 1, 2, 5]
def baseStart_1670503 : Nat := 118140960795 + 1670503 * 2 ^ 59
def prefixEnd_1670503 : Nat := 4983230072969 + 3 ^ 40 * 1670503 * 2
def baseEnd_1670503 : Nat := 571847315851855255353335

theorem tailTrace_1670503 : CollatzResearch.WordTrace tailWord_1670503 prefixEnd_1670503 571847315851855255353335 := by
  unfold tailWord_1670503
  simp only [CollatzResearch.WordTrace]
  refine ⟨60928249867060405043680163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40618833244706936695786775 60928249867060405043680163)
  ·
    refine ⟨91392374800590607565520245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60928249867060405043680163 91392374800590607565520245)
    ·
      refine ⟨8568035137555369459267523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 91392374800590607565520245 8568035137555369459267523)
      ·
        refine ⟨12852052706333054188901285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8568035137555369459267523 12852052706333054188901285)
        ·
          refine ⟨2409759882437447660418991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12852052706333054188901285 2409759882437447660418991)
          ·
            refine ⟨3614639823656171490628487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2409759882437447660418991 3614639823656171490628487)
            ·
              refine ⟨5421959735484257235942731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3614639823656171490628487 5421959735484257235942731)
              ·
                refine ⟨8132939603226385853914097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5421959735484257235942731 8132939603226385853914097)
                ·
                  refine ⟨6099704702419789390435573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8132939603226385853914097 6099704702419789390435573)
                  ·
                    refine ⟨571847315851855255353335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6099704702419789390435573 571847315851855255353335)
                    ·
                      rfl

theorem cell22_1670503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 1, 2, 5].length) (baseStart_1670503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1670503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1670503 prefixEnd_1670503 := by exact prefixLift 1670503
  have htrace : WordTrace (prefixWord ++ tailWord_1670503) baseStart_1670503 baseEnd_1670503 := by
    simpa [prefixWord, tailWord_1670503, baseEnd_1670503] using wordTrace_append hprefix tailTrace_1670503
  have hstable : (prefixWord ++ tailWord_1670503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1670503).length < 2 ^ (prefixWord ++ tailWord_1670503).sum := by decide
  have hdescent : baseEnd_1670503 < baseStart_1670503 := by decide
  rcases family_descends (prefixWord ++ tailWord_1670503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1670526 : List Nat := [4, 2, 3, 2, 1, 1, 2, 3, 1, 3]
def baseStart_1670526 : Nat := 118140960795 + 1670526 * 2 ^ 59
def prefixEnd_1670526 : Nat := 4983230072969 + 3 ^ 40 * 1670526 * 2
def baseEnd_1670526 : Nat := 571855189221890862028265

theorem tailTrace_1670526 : CollatzResearch.WordTrace tailWord_1670526 prefixEnd_1670526 571855189221890862028265 := by
  unfold tailWord_1670526
  simp only [CollatzResearch.WordTrace]
  refine ⟨7616136093247134996470929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40619392497318053314511621 7616136093247134996470929)
  ·
    refine ⟨5712102069935351247353197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7616136093247134996470929 5712102069935351247353197)
    ·
      refine ⟨2142038276225756717757449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5712102069935351247353197 2142038276225756717757449)
      ·
        refine ⟨1606528707169317538318087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2142038276225756717757449 1606528707169317538318087)
        ·
          refine ⟨2409793060753976307477131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1606528707169317538318087 2409793060753976307477131)
          ·
            refine ⟨3614689591130964461215697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2409793060753976307477131 3614689591130964461215697)
            ·
              refine ⟨2711017193348223345911773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3614689591130964461215697 2711017193348223345911773)
              ·
                refine ⟨1016631447505583754716915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2711017193348223345911773 1016631447505583754716915)
                ·
                  refine ⟨1524947171258375632075373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1016631447505583754716915 1524947171258375632075373)
                  ·
                    refine ⟨571855189221890862028265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1524947171258375632075373 571855189221890862028265)
                    ·
                      rfl

theorem cell22_1670526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_1670526 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1670526 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1670526 prefixEnd_1670526 := by exact prefixLift 1670526
  have htrace : WordTrace (prefixWord ++ tailWord_1670526) baseStart_1670526 baseEnd_1670526 := by
    simpa [prefixWord, tailWord_1670526, baseEnd_1670526] using wordTrace_append hprefix tailTrace_1670526
  have hstable : (prefixWord ++ tailWord_1670526).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1670526).length < 2 ^ (prefixWord ++ tailWord_1670526).sum := by decide
  have hdescent : baseEnd_1670526 < baseStart_1670526 := by decide
  rcases family_descends (prefixWord ++ tailWord_1670526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1670533 : List Nat := [1, 3, 1, 1, 3, 1, 3, 5, 4]
def baseStart_1670533 : Nat := 118140960795 + 1670533 * 2 ^ 59
def prefixEnd_1670533 : Nat := 4983230072969 + 3 ^ 40 * 1670533 * 2
def baseEnd_1670533 : Nat := 190619195154981725701081

theorem tailTrace_1670533 : CollatzResearch.WordTrace tailWord_1670533 prefixEnd_1670533 190619195154981725701081 := by
  unfold tailWord_1670533
  simp only [CollatzResearch.WordTrace]
  refine ⟨60929344056951720167272253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40619562704634480111514835 60929344056951720167272253)
  ·
    refine ⟨22848504021356895062727095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60929344056951720167272253 22848504021356895062727095)
    ·
      refine ⟨34272756032035342594090643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22848504021356895062727095 34272756032035342594090643)
      ·
        refine ⟨51409134048053013891135965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34272756032035342594090643 51409134048053013891135965)
        ·
          refine ⟨19278425268019880209175987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51409134048053013891135965 19278425268019880209175987)
          ·
            refine ⟨28917637902029820313763981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19278425268019880209175987 28917637902029820313763981)
            ·
              refine ⟨10844114213261182617661493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28917637902029820313763981 10844114213261182617661493)
              ·
                refine ⟨1016635707493235870405765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10844114213261182617661493 1016635707493235870405765)
                ·
                  refine ⟨190619195154981725701081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1016635707493235870405765 190619195154981725701081)
                  ·
                    rfl

theorem cell22_1670533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 5, 4].length) (baseStart_1670533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1670533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1670533 prefixEnd_1670533 := by exact prefixLift 1670533
  have htrace : WordTrace (prefixWord ++ tailWord_1670533) baseStart_1670533 baseEnd_1670533 := by
    simpa [prefixWord, tailWord_1670533, baseEnd_1670533] using wordTrace_append hprefix tailTrace_1670533
  have hstable : (prefixWord ++ tailWord_1670533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1670533).length < 2 ^ (prefixWord ++ tailWord_1670533).sum := by decide
  have hdescent : baseEnd_1670533 < baseStart_1670533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1670533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1670535 : List Nat := [1, 1, 4, 2, 2, 2, 4, 1, 1, 4]
def baseStart_1670535 : Nat := 118140960795 + 1670535 * 2 ^ 59
def prefixEnd_1670535 : Nat := 4983230072969 + 3 ^ 40 * 1670535 * 2
def baseEnd_1670535 : Nat := 571858270105817838553237

theorem tailTrace_1670535 : CollatzResearch.WordTrace tailWord_1670535 prefixEnd_1670535 571858270105817838553237 := by
  unfold tailWord_1670535
  simp only [CollatzResearch.WordTrace]
  refine ⟨60929417002944474508845059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40619611335296316339230039 60929417002944474508845059)
  ·
    refine ⟨91394125504416711763267589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60929417002944474508845059 91394125504416711763267589)
    ·
      refine ⟨17136398532078133455612673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91394125504416711763267589 17136398532078133455612673)
      ·
        refine ⟨12852298899058600091709505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17136398532078133455612673 12852298899058600091709505)
        ·
          refine ⟨9639224174293950068782129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12852298899058600091709505 9639224174293950068782129)
          ·
            refine ⟨7229418130720462551586597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9639224174293950068782129 7229418130720462551586597)
            ·
              refine ⟨1355515899510086728422487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7229418130720462551586597 1355515899510086728422487)
              ·
                refine ⟨2033273849265130092633731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1355515899510086728422487 2033273849265130092633731)
                ·
                  refine ⟨3049910773897695138950597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2033273849265130092633731 3049910773897695138950597)
                  ·
                    refine ⟨571858270105817838553237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3049910773897695138950597 571858270105817838553237)
                    ·
                      rfl

theorem cell22_1670535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 4, 1, 1, 4].length) (baseStart_1670535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1670535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1670535 prefixEnd_1670535 := by exact prefixLift 1670535
  have htrace : WordTrace (prefixWord ++ tailWord_1670535) baseStart_1670535 baseEnd_1670535 := by
    simpa [prefixWord, tailWord_1670535, baseEnd_1670535] using wordTrace_append hprefix tailTrace_1670535
  have hstable : (prefixWord ++ tailWord_1670535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1670535).length < 2 ^ (prefixWord ++ tailWord_1670535).sum := by decide
  have hdescent : baseEnd_1670535 < baseStart_1670535 := by decide
  rcases family_descends (prefixWord ++ tailWord_1670535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1670623 : List Nat := [1, 1, 2, 3, 3, 1, 3, 3, 5]
def baseStart_1670623 : Nat := 118140960795 + 1670623 * 2 ^ 59
def prefixEnd_1670623 : Nat := 4983230072969 + 3 ^ 40 * 1670623 * 2
def baseEnd_1670623 : Nat := 190629464768071647450989

theorem tailTrace_1670623 : CollatzResearch.WordTrace tailWord_1670623 prefixEnd_1670623 190629464768071647450989 := by
  unfold tailWord_1670623
  simp only [CollatzResearch.WordTrace]
  refine ⟨60932626626625665538048523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40621751084417110358699015 60932626626625665538048523)
  ·
    refine ⟨91398939939938498307072785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60932626626625665538048523 91398939939938498307072785)
    ·
      refine ⟨68549204954953873730304589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91398939939938498307072785 68549204954953873730304589)
      ·
        refine ⟨25705951858107702648864221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68549204954953873730304589 25705951858107702648864221)
        ·
          refine ⟨9639731946790388493324083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25705951858107702648864221 9639731946790388493324083)
          ·
            refine ⟨14459597920185582739986125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9639731946790388493324083 14459597920185582739986125)
            ·
              refine ⟨5422349220069593527494797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14459597920185582739986125 5422349220069593527494797)
              ·
                refine ⟨2033380957526097572810549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5422349220069593527494797 2033380957526097572810549)
                ·
                  refine ⟨190629464768071647450989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2033380957526097572810549 190629464768071647450989)
                  ·
                    rfl

theorem cell22_1670623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 3, 5].length) (baseStart_1670623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1670623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1670623 prefixEnd_1670623 := by exact prefixLift 1670623
  have htrace : WordTrace (prefixWord ++ tailWord_1670623) baseStart_1670623 baseEnd_1670623 := by
    simpa [prefixWord, tailWord_1670623, baseEnd_1670623] using wordTrace_append hprefix tailTrace_1670623
  have hstable : (prefixWord ++ tailWord_1670623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1670623).length < 2 ^ (prefixWord ++ tailWord_1670623).sum := by decide
  have hdescent : baseEnd_1670623 < baseStart_1670623 := by decide
  rcases family_descends (prefixWord ++ tailWord_1670623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1670651 : List Nat := [1, 1, 1, 1, 1, 3, 2, 4, 8]
def baseStart_1670651 : Nat := 118140960795 + 1670651 * 2 ^ 59
def prefixEnd_1670651 : Nat := 4983230072969 + 3 ^ 40 * 1670651 * 2
def baseEnd_1670651 : Nat := 190632659758810734217627

theorem tailTrace_1670651 : CollatzResearch.WordTrace tailWord_1670651 prefixEnd_1670651 190632659758810734217627 := by
  unfold tailWord_1670651
  simp only [CollatzResearch.WordTrace]
  refine ⟨60933647870524226320067807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40622431913682817546711871 60933647870524226320067807)
  ·
    refine ⟨91400471805786339480101711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60933647870524226320067807 91400471805786339480101711)
    ·
      refine ⟨137100707708679509220152567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91400471805786339480101711 137100707708679509220152567)
      ·
        refine ⟨205651061563019263830228851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137100707708679509220152567 205651061563019263830228851)
        ·
          refine ⟨308476592344528895745343277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205651061563019263830228851 308476592344528895745343277)
          ·
            refine ⟨115678722129198335904503729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 308476592344528895745343277 115678722129198335904503729)
            ·
              refine ⟨86759041596898751928377797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115678722129198335904503729 86759041596898751928377797)
              ·
                refine ⟨16267320299418515986570837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 86759041596898751928377797 16267320299418515986570837)
                ·
                  refine ⟨190632659758810734217627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16267320299418515986570837 190632659758810734217627)
                  ·
                    rfl

theorem cell22_1670651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 4, 8].length) (baseStart_1670651 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1670651 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1670651 prefixEnd_1670651 := by exact prefixLift 1670651
  have htrace : WordTrace (prefixWord ++ tailWord_1670651) baseStart_1670651 baseEnd_1670651 := by
    simpa [prefixWord, tailWord_1670651, baseEnd_1670651] using wordTrace_append hprefix tailTrace_1670651
  have hstable : (prefixWord ++ tailWord_1670651).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1670651).length < 2 ^ (prefixWord ++ tailWord_1670651).sum := by decide
  have hdescent : baseEnd_1670651 < baseStart_1670651 := by decide
  rcases family_descends (prefixWord ++ tailWord_1670651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1670702 : List Nat := [4, 1, 3, 1, 2, 1, 1, 5, 4]
def baseStart_1670702 : Nat := 118140960795 + 1670702 * 2 ^ 59
def prefixEnd_1670702 : Nat := 4983230072969 + 3 ^ 40 * 1670702 * 2
def baseEnd_1670702 : Nat := 190638479206228356542575

theorem tailTrace_1670702 : CollatzResearch.WordTrace tailWord_1670702 prefixEnd_1670702 190638479206228356542575 := by
  unfold tailWord_1670702
  simp only [CollatzResearch.WordTrace]
  refine ⟨7616938499167432753771795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40623671995559641353449573 7616938499167432753771795)
  ·
    refine ⟨11425407748751149130657693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7616938499167432753771795 11425407748751149130657693)
    ·
      refine ⟨4284527905781680923996635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11425407748751149130657693 4284527905781680923996635)
      ·
        refine ⟨6426791858672521385994953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4284527905781680923996635 6426791858672521385994953)
        ·
          refine ⟨4820093894004391039496215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6426791858672521385994953 4820093894004391039496215)
          ·
            refine ⟨7230140841006586559244323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4820093894004391039496215 7230140841006586559244323)
            ·
              refine ⟨10845211261509879838866485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7230140841006586559244323 10845211261509879838866485)
              ·
                refine ⟨1016738555766551234893733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10845211261509879838866485 1016738555766551234893733)
                ·
                  refine ⟨190638479206228356542575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1016738555766551234893733 190638479206228356542575)
                  ·
                    rfl

theorem cell22_1670702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 5, 4].length) (baseStart_1670702 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1670702 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1670702 prefixEnd_1670702 := by exact prefixLift 1670702
  have htrace : WordTrace (prefixWord ++ tailWord_1670702) baseStart_1670702 baseEnd_1670702 := by
    simpa [prefixWord, tailWord_1670702, baseEnd_1670702] using wordTrace_append hprefix tailTrace_1670702
  have hstable : (prefixWord ++ tailWord_1670702).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1670702).length < 2 ^ (prefixWord ++ tailWord_1670702).sum := by decide
  have hdescent : baseEnd_1670702 < baseStart_1670702 := by decide
  rcases family_descends (prefixWord ++ tailWord_1670702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1670713 : List Nat := [1, 2, 1, 5, 1, 3, 9]
def baseStart_1670713 : Nat := 118140960795 + 1670713 * 2 ^ 59
def prefixEnd_1670713 : Nat := 4983230072969 + 3 ^ 40 * 1670713 * 2
def baseEnd_1670713 : Nat := 21182192709017952133433

theorem tailTrace_1670713 : CollatzResearch.WordTrace tailWord_1670713 prefixEnd_1670713 21182192709017952133433 := by
  unfold tailWord_1670713
  simp only [CollatzResearch.WordTrace]
  refine ⟨60935909196299610908824793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40623939464199740605883195 60935909196299610908824793)
  ·
    refine ⟨45701931897224708181618595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60935909196299610908824793 45701931897224708181618595)
    ·
      refine ⟨68552897845837062272427893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45701931897224708181618595 68552897845837062272427893)
      ·
        refine ⟨6426834173047224588040115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 68552897845837062272427893 6426834173047224588040115)
        ·
          refine ⟨9640251259570836882060173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6426834173047224588040115 9640251259570836882060173)
          ·
            refine ⟨3615094222339063830772565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9640251259570836882060173 3615094222339063830772565)
            ·
              refine ⟨21182192709017952133433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3615094222339063830772565 21182192709017952133433)
              ·
                rfl

theorem cell22_1670713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 9].length) (baseStart_1670713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1670713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1670713 prefixEnd_1670713 := by exact prefixLift 1670713
  have htrace : WordTrace (prefixWord ++ tailWord_1670713) baseStart_1670713 baseEnd_1670713 := by
    simpa [prefixWord, tailWord_1670713, baseEnd_1670713] using wordTrace_append hprefix tailTrace_1670713
  have hstable : (prefixWord ++ tailWord_1670713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1670713).length < 2 ^ (prefixWord ++ tailWord_1670713).sum := by decide
  have hdescent : baseEnd_1670713 < baseStart_1670713 := by decide
  rcases family_descends (prefixWord ++ tailWord_1670713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1670717 : List Nat := [1, 4, 1, 3, 3, 1, 1, 1, 4, 3]
def baseStart_1670717 : Nat := 118140960795 + 1670717 * 2 ^ 59
def prefixEnd_1670717 : Nat := 4983230072969 + 3 ^ 40 * 1670717 * 2
def baseEnd_1670717 : Nat := 571920572425230030502679

theorem tailTrace_1670717 : CollatzResearch.WordTrace tailWord_1670717 prefixEnd_1670717 571920572425230030502679 := by
  unfold tailWord_1670717
  simp only [CollatzResearch.WordTrace]
  refine ⟨60936055088285119591970405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40624036725523413061313603 60936055088285119591970405)
  ·
    refine ⟨11425510329053459923494451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60936055088285119591970405 11425510329053459923494451)
    ·
      refine ⟨17138265493580189885241677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11425510329053459923494451 17138265493580189885241677)
      ·
        refine ⟨6426849560092571206965629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17138265493580189885241677 6426849560092571206965629)
        ·
          refine ⟨2410068585034714202612111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6426849560092571206965629 2410068585034714202612111)
          ·
            refine ⟨3615102877552071303918167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2410068585034714202612111 3615102877552071303918167)
            ·
              refine ⟨5422654316328106955877251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3615102877552071303918167 5422654316328106955877251)
              ·
                refine ⟨8133981474492160433815877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5422654316328106955877251 8133981474492160433815877)
                ·
                  refine ⟨1525121526467280081340477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8133981474492160433815877 1525121526467280081340477)
                  ·
                    refine ⟨571920572425230030502679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1525121526467280081340477 571920572425230030502679)
                    ·
                      rfl

theorem cell22_1670717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 1, 4, 3].length) (baseStart_1670717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1670717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1670717 prefixEnd_1670717 := by exact prefixLift 1670717
  have htrace : WordTrace (prefixWord ++ tailWord_1670717) baseStart_1670717 baseEnd_1670717 := by
    simpa [prefixWord, tailWord_1670717, baseEnd_1670717] using wordTrace_append hprefix tailTrace_1670717
  have hstable : (prefixWord ++ tailWord_1670717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1670717).length < 2 ^ (prefixWord ++ tailWord_1670717).sum := by decide
  have hdescent : baseEnd_1670717 < baseStart_1670717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1670717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1670779 : List Nat := [1, 1, 1, 1, 1, 4, 7, 2, 1, 3]
def baseStart_1670779 : Nat := 118140960795 + 1670779 * 2 ^ 59
def prefixEnd_1670779 : Nat := 4983230072969 + 3 ^ 40 * 1670779 * 2
def baseEnd_1670779 : Nat := 571941796292282535452489

theorem tailTrace_1670779 : CollatzResearch.WordTrace tailWord_1670779 prefixEnd_1670779 571941796292282535452489 := by
  unfold tailWord_1670779
  simp only [CollatzResearch.WordTrace]
  refine ⟨60938316414060504180727391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40625544276040336120484927 60938316414060504180727391)
  ·
    refine ⟨91407474621090756271091087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60938316414060504180727391 91407474621090756271091087)
    ·
      refine ⟨137111211931636134406636631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91407474621090756271091087 137111211931636134406636631)
      ·
        refine ⟨205666817897454201609954947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137111211931636134406636631 205666817897454201609954947)
        ·
          refine ⟨308500226846181302414932421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205666817897454201609954947 308500226846181302414932421)
          ·
            refine ⟨57843792533658994202799829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 308500226846181302414932421 57843792533658994202799829)
            ·
              refine ⟨1355713887507632676628121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 57843792533658994202799829 1355713887507632676628121)
              ·
                refine ⟨1016785415630724507471091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1355713887507632676628121 1016785415630724507471091)
                ·
                  refine ⟨1525178123446086761206637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1016785415630724507471091 1525178123446086761206637)
                  ·
                    refine ⟨571941796292282535452489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1525178123446086761206637 571941796292282535452489)
                    ·
                      rfl

theorem cell22_1670779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 7, 2, 1, 3].length) (baseStart_1670779 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1670779 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1670779 prefixEnd_1670779 := by exact prefixLift 1670779
  have htrace : WordTrace (prefixWord ++ tailWord_1670779) baseStart_1670779 baseEnd_1670779 := by
    simpa [prefixWord, tailWord_1670779, baseEnd_1670779] using wordTrace_append hprefix tailTrace_1670779
  have hstable : (prefixWord ++ tailWord_1670779).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1670779).length < 2 ^ (prefixWord ++ tailWord_1670779).sum := by decide
  have hdescent : baseEnd_1670779 < baseStart_1670779 := by decide
  rcases family_descends (prefixWord ++ tailWord_1670779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1670830 : List Nat := [4, 1, 4, 1, 2, 2, 2, 2, 1, 3]
def baseStart_1670830 : Nat := 118140960795 + 1670830 * 2 ^ 59
def prefixEnd_1670830 : Nat := 4983230072969 + 3 ^ 40 * 1670830 * 2
def baseEnd_1670830 : Nat := 571959254634535402427333

theorem tailTrace_1670830 : CollatzResearch.WordTrace tailWord_1670830 prefixEnd_1670830 571959254634535402427333 := by
  unfold tailWord_1670830
  simp only [CollatzResearch.WordTrace]
  refine ⟨7617522067109467486354243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40626784357917159927222629 7617522067109467486354243)
  ·
    refine ⟨11426283100664201229531365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7617522067109467486354243 11426283100664201229531365)
    ·
      refine ⟨2142428081374537730537131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11426283100664201229531365 2142428081374537730537131)
      ·
        refine ⟨3213642122061806595805697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2142428081374537730537131 3213642122061806595805697)
        ·
          refine ⟨2410231591546354946854273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3213642122061806595805697 2410231591546354946854273)
          ·
            refine ⟨1807673693659766210140705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2410231591546354946854273 1807673693659766210140705)
            ·
              refine ⟨1355755270244824657605529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1807673693659766210140705 1355755270244824657605529)
              ·
                refine ⟨1016816452683618493204147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1355755270244824657605529 1016816452683618493204147)
                ·
                  refine ⟨1525224679025427739806221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1016816452683618493204147 1525224679025427739806221)
                  ·
                    refine ⟨571959254634535402427333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1525224679025427739806221 571959254634535402427333)
                    ·
                      rfl

theorem cell22_1670830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_1670830 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1670830 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1670830 prefixEnd_1670830 := by exact prefixLift 1670830
  have htrace : WordTrace (prefixWord ++ tailWord_1670830) baseStart_1670830 baseEnd_1670830 := by
    simpa [prefixWord, tailWord_1670830, baseEnd_1670830] using wordTrace_append hprefix tailTrace_1670830
  have hstable : (prefixWord ++ tailWord_1670830).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1670830).length < 2 ^ (prefixWord ++ tailWord_1670830).sum := by decide
  have hdescent : baseEnd_1670830 < baseStart_1670830 := by decide
  rcases family_descends (prefixWord ++ tailWord_1670830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1670852 : List Nat := [2, 3, 3, 1, 1, 1, 4, 1, 1, 5]
def baseStart_1670852 : Nat := 118140960795 + 1670852 * 2 ^ 59
def prefixEnd_1670852 : Nat := 4983230072969 + 3 ^ 40 * 1670852 * 2
def baseEnd_1670852 : Nat := 571966785684134678377265

theorem tailTrace_1670852 : CollatzResearch.WordTrace tailWord_1670852 prefixEnd_1670852 571966785684134678377265 := by
  unfold tailWord_1670852
  simp only [CollatzResearch.WordTrace]
  refine ⟨30470489471398018824067405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40627319295197358432089873 30470489471398018824067405)
  ·
    refine ⟨11426433551774257059025277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30470489471398018824067405 11426433551774257059025277)
    ·
      refine ⟨4284912581915346397134479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11426433551774257059025277 4284912581915346397134479)
      ·
        refine ⟨6427368872873019595701719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4284912581915346397134479 6427368872873019595701719)
        ·
          refine ⟨9641053309309529393552579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6427368872873019595701719 9641053309309529393552579)
          ·
            refine ⟨14461579963964294090328869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9641053309309529393552579 14461579963964294090328869)
            ·
              refine ⟨2711546243243305141936663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14461579963964294090328869 2711546243243305141936663)
              ·
                refine ⟨4067319364864957712904995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2711546243243305141936663 4067319364864957712904995)
                ·
                  refine ⟨6100979047297436569357493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4067319364864957712904995 6100979047297436569357493)
                  ·
                    refine ⟨571966785684134678377265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6100979047297436569357493 571966785684134678377265)
                    ·
                      rfl

theorem cell22_1670852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_1670852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1670852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1670852 prefixEnd_1670852 := by exact prefixLift 1670852
  have htrace : WordTrace (prefixWord ++ tailWord_1670852) baseStart_1670852 baseEnd_1670852 := by
    simpa [prefixWord, tailWord_1670852, baseEnd_1670852] using wordTrace_append hprefix tailTrace_1670852
  have hstable : (prefixWord ++ tailWord_1670852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1670852).length < 2 ^ (prefixWord ++ tailWord_1670852).sum := by decide
  have hdescent : baseEnd_1670852 < baseStart_1670852 := by decide
  rcases family_descends (prefixWord ++ tailWord_1670852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1670854 : List Nat := [6, 1, 2, 1, 1, 1, 1, 1, 8]
def baseStart_1670854 : Nat := 118140960795 + 1670854 * 2 ^ 59
def prefixEnd_1670854 : Nat := 4983230072969 + 3 ^ 40 * 1670854 * 2
def baseEnd_1670854 : Nat := 190655823441669113275753

theorem tailTrace_1670854 : CollatzResearch.WordTrace tailWord_1670854 prefixEnd_1670854 190655823441669113275753 := by
  unfold tailWord_1670854
  simp only [CollatzResearch.WordTrace]
  refine ⟨1904407871524649749678363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 40627367925859194659805077 1904407871524649749678363)
  ·
    refine ⟨2856611807286974624517545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1904407871524649749678363 2856611807286974624517545)
    ·
      refine ⟨2142458855465230968388159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2856611807286974624517545 2142458855465230968388159)
      ·
        refine ⟨3213688283197846452582239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2142458855465230968388159 3213688283197846452582239)
        ·
          refine ⟨4820532424796769678873359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3213688283197846452582239 4820532424796769678873359)
          ·
            refine ⟨7230798637195154518310039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4820532424796769678873359 7230798637195154518310039)
            ·
              refine ⟨10846197955792731777465059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7230798637195154518310039 10846197955792731777465059)
              ·
                refine ⟨16269296933689097666197589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10846197955792731777465059 16269296933689097666197589)
                ·
                  refine ⟨190655823441669113275753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16269296933689097666197589 190655823441669113275753)
                  ·
                    rfl

theorem cell22_1670854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 1, 8].length) (baseStart_1670854 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1670854 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1670854 prefixEnd_1670854 := by exact prefixLift 1670854
  have htrace : WordTrace (prefixWord ++ tailWord_1670854) baseStart_1670854 baseEnd_1670854 := by
    simpa [prefixWord, tailWord_1670854, baseEnd_1670854] using wordTrace_append hprefix tailTrace_1670854
  have hstable : (prefixWord ++ tailWord_1670854).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1670854).length < 2 ^ (prefixWord ++ tailWord_1670854).sum := by decide
  have hdescent : baseEnd_1670854 < baseStart_1670854 := by decide
  rcases family_descends (prefixWord ++ tailWord_1670854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1670897 : List Nat := [1, 2, 2, 2, 2, 3, 1, 3, 3, 3]
def baseStart_1670897 : Nat := 118140960795 + 1670897 * 2 ^ 59
def prefixEnd_1670897 : Nat := 4983230072969 + 3 ^ 40 * 1670897 * 2
def baseEnd_1670897 : Nat := 571982190103769561002127

theorem tailTrace_1670897 : CollatzResearch.WordTrace tailWord_1670897 prefixEnd_1670897 571982190103769561002127 := by
  unfold tailWord_1670897
  simp only [CollatzResearch.WordTrace]
  refine ⟨60942620227633010333522945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40628413485088673555681963 60942620227633010333522945)
  ·
    refine ⟨45706965170724757750142209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60942620227633010333522945 45706965170724757750142209)
    ·
      refine ⟨34280223878043568312606657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45706965170724757750142209 34280223878043568312606657)
      ·
        refine ⟨25710167908532676234454993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34280223878043568312606657 25710167908532676234454993)
        ·
          refine ⟨19282625931399507175841245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25710167908532676234454993 19282625931399507175841245)
          ·
            refine ⟨7230984724274815190940467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19282625931399507175841245 7230984724274815190940467)
            ·
              refine ⟨10846477086412222786410701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7230984724274815190940467 10846477086412222786410701)
              ·
                refine ⟨4067428907404583544904013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10846477086412222786410701 4067428907404583544904013)
                ·
                  refine ⟨1525285840276718829339005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4067428907404583544904013 1525285840276718829339005)
                  ·
                    refine ⟨571982190103769561002127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1525285840276718829339005 571982190103769561002127)
                    ·
                      rfl

theorem cell22_1670897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 3, 3, 3].length) (baseStart_1670897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1670897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1670897 prefixEnd_1670897 := by exact prefixLift 1670897
  have htrace : WordTrace (prefixWord ++ tailWord_1670897) baseStart_1670897 baseEnd_1670897 := by
    simpa [prefixWord, tailWord_1670897, baseEnd_1670897] using wordTrace_append hprefix tailTrace_1670897
  have hstable : (prefixWord ++ tailWord_1670897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1670897).length < 2 ^ (prefixWord ++ tailWord_1670897).sum := by decide
  have hdescent : baseEnd_1670897 < baseStart_1670897 := by decide
  rcases family_descends (prefixWord ++ tailWord_1670897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1670914 : List Nat := [3, 4, 1, 1, 1, 1, 1, 4, 3, 3]
def baseStart_1670914 : Nat := 118140960795 + 1670914 * 2 ^ 59
def prefixEnd_1670914 : Nat := 4983230072969 + 3 ^ 40 * 1670914 * 2
def baseEnd_1670914 : Nat := 571988009551187183327075

theorem tailTrace_1670914 : CollatzResearch.WordTrace tailWord_1670914 prefixEnd_1670914 571988009551187183327075 := by
  unfold tailWord_1670914
  simp only [CollatzResearch.WordTrace]
  refine ⟨15235810067142855559222949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40628826845714281491261197 15235810067142855559222949)
  ·
    refine ⟨2856714387589285417354303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15235810067142855559222949 2856714387589285417354303)
    ·
      refine ⟨4285071581383928126031455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2856714387589285417354303 4285071581383928126031455)
      ·
        refine ⟨6427607372075892189047183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4285071581383928126031455 6427607372075892189047183)
        ·
          refine ⟨9641411058113838283570775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6427607372075892189047183 9641411058113838283570775)
          ·
            refine ⟨14462116587170757425356163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9641411058113838283570775 14462116587170757425356163)
            ·
              refine ⟨21693174880756136138034245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14462116587170757425356163 21693174880756136138034245)
              ·
                refine ⟨4067470290141775525881421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21693174880756136138034245 4067470290141775525881421)
                ·
                  refine ⟨1525301358803165822205533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4067470290141775525881421 1525301358803165822205533)
                  ·
                    refine ⟨571988009551187183327075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1525301358803165822205533 571988009551187183327075)
                    ·
                      rfl

theorem cell22_1670914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 4, 3, 3].length) (baseStart_1670914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1670914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1670914 prefixEnd_1670914 := by exact prefixLift 1670914
  have htrace : WordTrace (prefixWord ++ tailWord_1670914) baseStart_1670914 baseEnd_1670914 := by
    simpa [prefixWord, tailWord_1670914, baseEnd_1670914] using wordTrace_append hprefix tailTrace_1670914
  have hstable : (prefixWord ++ tailWord_1670914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1670914).length < 2 ^ (prefixWord ++ tailWord_1670914).sum := by decide
  have hdescent : baseEnd_1670914 < baseStart_1670914 := by decide
  rcases family_descends (prefixWord ++ tailWord_1670914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1670948 : List Nat := [2, 3, 1, 3, 2, 2, 3, 2, 1, 3]
def baseStart_1670948 : Nat := 118140960795 + 1670948 * 2 ^ 59
def prefixEnd_1670948 : Nat := 4983230072969 + 3 ^ 40 * 1670948 * 2
def baseEnd_1670948 : Nat := 571999648446022427976971

theorem tailTrace_1670948 : CollatzResearch.WordTrace tailWord_1670948 prefixEnd_1670948 571999648446022427976971 := by
  unfold tailWord_1670948
  simp only [CollatzResearch.WordTrace]
  refine ⟨30472240175224123021814749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40629653566965497362419665 30472240175224123021814749)
  ·
    refine ⟨11427090065709046133180531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30472240175224123021814749 11427090065709046133180531)
    ·
      refine ⟨17140635098563569199770797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11427090065709046133180531 17140635098563569199770797)
      ·
        refine ⟨6427738161961338449914049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17140635098563569199770797 6427738161961338449914049)
        ·
          refine ⟨4820803621471003837435537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6427738161961338449914049 4820803621471003837435537)
          ·
            refine ⟨3615602716103252878076653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4820803621471003837435537 3615602716103252878076653)
            ·
              refine ⟨1355851018538719829278745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3615602716103252878076653 1355851018538719829278745)
              ·
                refine ⟨1016888263904039871959059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1355851018538719829278745 1016888263904039871959059)
                ·
                  refine ⟨1525332395856059807938589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1016888263904039871959059 1525332395856059807938589)
                  ·
                    refine ⟨571999648446022427976971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1525332395856059807938589 571999648446022427976971)
                    ·
                      rfl

theorem cell22_1670948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 3, 2, 1, 3].length) (baseStart_1670948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1670948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1670948 prefixEnd_1670948 := by exact prefixLift 1670948
  have htrace : WordTrace (prefixWord ++ tailWord_1670948) baseStart_1670948 baseEnd_1670948 := by
    simpa [prefixWord, tailWord_1670948, baseEnd_1670948] using wordTrace_append hprefix tailTrace_1670948
  have hstable : (prefixWord ++ tailWord_1670948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1670948).length < 2 ^ (prefixWord ++ tailWord_1670948).sum := by decide
  have hdescent : baseEnd_1670948 < baseStart_1670948 := by decide
  rcases family_descends (prefixWord ++ tailWord_1670948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1670974 : List Nat := [4, 2, 1, 2, 2, 2, 1, 1, 3, 4]
def baseStart_1670974 : Nat := 118140960795 + 1670974 * 2 ^ 59
def prefixEnd_1670974 : Nat := 4983230072969 + 3 ^ 40 * 1670974 * 2
def baseEnd_1670974 : Nat := 572008548777367026826891

theorem tailTrace_1670974 : CollatzResearch.WordTrace tailWord_1670974 prefixEnd_1670974 572008548777367026826891 := by
  unfold tailWord_1670974
  simp only [CollatzResearch.WordTrace]
  refine ⟨7618178581044256560509497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40630285765569368322717317 7618178581044256560509497)
  ·
    refine ⟨5713633935783192420382123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7618178581044256560509497 5713633935783192420382123)
    ·
      refine ⟨8570450903674788630573185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5713633935783192420382123 8570450903674788630573185)
      ·
        refine ⟨6427838177756091472929889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8570450903674788630573185 6427838177756091472929889)
        ·
          refine ⟨4820878633317068604697417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6427838177756091472929889 4820878633317068604697417)
          ·
            refine ⟨3615658974987801453523063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4820878633317068604697417 3615658974987801453523063)
            ·
              refine ⟨5423488462481702180284595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3615658974987801453523063 5423488462481702180284595)
              ·
                refine ⟨8135232693722553270426893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5423488462481702180284595 8135232693722553270426893)
                ·
                  refine ⟨3050712260145957476410085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8135232693722553270426893 3050712260145957476410085)
                  ·
                    refine ⟨572008548777367026826891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3050712260145957476410085 572008548777367026826891)
                    ·
                      rfl

theorem cell22_1670974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 1, 3, 4].length) (baseStart_1670974 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1670974 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1670974 prefixEnd_1670974 := by exact prefixLift 1670974
  have htrace : WordTrace (prefixWord ++ tailWord_1670974) baseStart_1670974 baseEnd_1670974 := by
    simpa [prefixWord, tailWord_1670974, baseEnd_1670974] using wordTrace_append hprefix tailTrace_1670974
  have hstable : (prefixWord ++ tailWord_1670974).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1670974).length < 2 ^ (prefixWord ++ tailWord_1670974).sum := by decide
  have hdescent : baseEnd_1670974 < baseStart_1670974 := by decide
  rcases family_descends (prefixWord ++ tailWord_1670974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1671002 : List Nat := [3, 1, 1, 2, 1, 3, 1, 4, 2, 4]
def baseStart_1671002 : Nat := 118140960795 + 1671002 * 2 ^ 59
def prefixEnd_1671002 : Nat := 4983230072969 + 3 ^ 40 * 1671002 * 2
def baseEnd_1671002 : Nat := 572018133749584287126805

theorem tailTrace_1671002 : CollatzResearch.WordTrace tailWord_1671002 prefixEnd_1671002 572018133749584287126805 := by
  unfold tailWord_1671002
  simp only [CollatzResearch.WordTrace]
  refine ⟨15236612473063153316523815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40630966594835075510730173 15236612473063153316523815)
  ·
    refine ⟨22854918709594729974785723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15236612473063153316523815 22854918709594729974785723)
    ·
      refine ⟨34282378064392094962178585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22854918709594729974785723 34282378064392094962178585)
      ·
        refine ⟨25711783548294071221633939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34282378064392094962178585 25711783548294071221633939)
        ·
          refine ⟨38567675322441106832450909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25711783548294071221633939 38567675322441106832450909)
          ·
            refine ⟨14462878245915415062169091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38567675322441106832450909 14462878245915415062169091)
            ·
              refine ⟨21694317368873122593253637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14462878245915415062169091 21694317368873122593253637)
              ·
                refine ⟨4067684506663710486235057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21694317368873122593253637 4067684506663710486235057)
                ·
                  refine ⟨3050763379997782864676293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4067684506663710486235057 3050763379997782864676293)
                  ·
                    refine ⟨572018133749584287126805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3050763379997782864676293 572018133749584287126805)
                    ·
                      rfl

theorem cell22_1671002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 4, 2, 4].length) (baseStart_1671002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1671002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1671002 prefixEnd_1671002 := by exact prefixLift 1671002
  have htrace : WordTrace (prefixWord ++ tailWord_1671002) baseStart_1671002 baseEnd_1671002 := by
    simpa [prefixWord, tailWord_1671002, baseEnd_1671002] using wordTrace_append hprefix tailTrace_1671002
  have hstable : (prefixWord ++ tailWord_1671002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1671002).length < 2 ^ (prefixWord ++ tailWord_1671002).sum := by decide
  have hdescent : baseEnd_1671002 < baseStart_1671002 := by decide
  rcases family_descends (prefixWord ++ tailWord_1671002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1671066 : List Nat := [3, 1, 1, 4, 2, 2, 2, 1, 3, 3]
def baseStart_1671066 : Nat := 118140960795 + 1671066 * 2 ^ 59
def prefixEnd_1671066 : Nat := 4983230072969 + 3 ^ 40 * 1671066 * 2
def baseEnd_1671066 : Nat := 572040042257509453526609

theorem tailTrace_1671066 : CollatzResearch.WordTrace tailWord_1671066 prefixEnd_1671066 572040042257509453526609 := by
  unfold tailWord_1671066
  simp only [CollatzResearch.WordTrace]
  refine ⟨15237196041005188049106263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40632522776013834797616701 15237196041005188049106263)
  ·
    refine ⟨22855794061507782073659395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15237196041005188049106263 22855794061507782073659395)
    ·
      refine ⟨34283691092261673110489093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22855794061507782073659395 34283691092261673110489093)
      ·
        refine ⟨6428192079799063708216705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34283691092261673110489093 6428192079799063708216705)
        ·
          refine ⟨4821144059849297781162529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6428192079799063708216705 4821144059849297781162529)
          ·
            refine ⟨3615858044886973335871897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4821144059849297781162529 3615858044886973335871897)
            ·
              refine ⟨2711893533665230001903923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3615858044886973335871897 2711893533665230001903923)
              ·
                refine ⟨4067840300497845002855885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2711893533665230001903923 4067840300497845002855885)
                ·
                  refine ⟨1525440112686691876070957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4067840300497845002855885 1525440112686691876070957)
                  ·
                    refine ⟨572040042257509453526609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1525440112686691876070957 572040042257509453526609)
                    ·
                      rfl

theorem cell22_1671066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 2, 1, 3, 3].length) (baseStart_1671066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1671066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1671066 prefixEnd_1671066 := by exact prefixLift 1671066
  have htrace : WordTrace (prefixWord ++ tailWord_1671066) baseStart_1671066 baseEnd_1671066 := by
    simpa [prefixWord, tailWord_1671066, baseEnd_1671066] using wordTrace_append hprefix tailTrace_1671066
  have hstable : (prefixWord ++ tailWord_1671066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1671066).length < 2 ^ (prefixWord ++ tailWord_1671066).sum := by decide
  have hdescent : baseEnd_1671066 < baseStart_1671066 := by decide
  rcases family_descends (prefixWord ++ tailWord_1671066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1671137 : List Nat := [1, 2, 3, 1, 2, 1, 2, 1, 3, 6]
def baseStart_1671137 : Nat := 118140960795 + 1671137 * 2 ^ 59
def prefixEnd_1671137 : Nat := 4983230072969 + 3 ^ 40 * 1671137 * 2
def baseEnd_1671137 : Nat := 572064347008488935001391

theorem tailTrace_1671137 : CollatzResearch.WordTrace tailWord_1671137 prefixEnd_1671137 572064347008488935001391 := by
  unfold tailWord_1671137
  simp only [CollatzResearch.WordTrace]
  refine ⟨60951373746763531322259665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40634249164509020881506443 60951373746763531322259665)
  ·
    refine ⟨45713530310072648491694749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60951373746763531322259665 45713530310072648491694749)
    ·
      refine ⟨17142573866277243184385531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45713530310072648491694749 17142573866277243184385531)
      ·
        refine ⟨25713860799415864776578297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17142573866277243184385531 25713860799415864776578297)
        ·
          refine ⟨19285395599561898582433723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25713860799415864776578297 19285395599561898582433723)
          ·
            refine ⟨28928093399342847873650585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19285395599561898582433723 28928093399342847873650585)
            ·
              refine ⟨21696070049507135905237939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28928093399342847873650585 21696070049507135905237939)
              ·
                refine ⟨32544105074260703857856909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21696070049507135905237939 32544105074260703857856909)
                ·
                  refine ⟨12204039402847763946696341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32544105074260703857856909 12204039402847763946696341)
                  ·
                    refine ⟨572064347008488935001391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12204039402847763946696341 572064347008488935001391)
                    ·
                      rfl

theorem cell22_1671137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 1, 3, 6].length) (baseStart_1671137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1671137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1671137 prefixEnd_1671137 := by exact prefixLift 1671137
  have htrace : WordTrace (prefixWord ++ tailWord_1671137) baseStart_1671137 baseEnd_1671137 := by
    simpa [prefixWord, tailWord_1671137, baseEnd_1671137] using wordTrace_append hprefix tailTrace_1671137
  have hstable : (prefixWord ++ tailWord_1671137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1671137).length < 2 ^ (prefixWord ++ tailWord_1671137).sum := by decide
  have hdescent : baseEnd_1671137 < baseStart_1671137 := by decide
  rcases family_descends (prefixWord ++ tailWord_1671137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1671143 : List Nat := [1, 1, 5, 2, 3, 2, 1, 2, 1, 4]
def baseStart_1671143 : Nat := 118140960795 + 1671143 * 2 ^ 59
def prefixEnd_1671143 : Nat := 4983230072969 + 3 ^ 40 * 1671143 * 2
def baseEnd_1671143 : Nat := 572066400931106919351373

theorem tailTrace_1671143 : CollatzResearch.WordTrace tailWord_1671143 prefixEnd_1671143 572066400931106919351373 := by
  unfold tailWord_1671143
  simp only [CollatzResearch.WordTrace]
  refine ⟨60951592584741794346978083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40634395056494529564652055 60951592584741794346978083)
  ·
    refine ⟨91427388877112691520467125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60951592584741794346978083 91427388877112691520467125)
    ·
      refine ⟨8571317707229314830043793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 91427388877112691520467125 8571317707229314830043793)
      ·
        refine ⟨6428488280421986122532845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8571317707229314830043793 6428488280421986122532845)
        ·
          refine ⟨2410683105158244795949817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6428488280421986122532845 2410683105158244795949817)
          ·
            refine ⟨1808012328868683596962363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2410683105158244795949817 1808012328868683596962363)
            ·
              refine ⟨2712018493303025395443545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1808012328868683596962363 2712018493303025395443545)
              ·
                refine ⟨2034013869977269046582659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2712018493303025395443545 2034013869977269046582659)
                ·
                  refine ⟨3051020804965903569873989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2034013869977269046582659 3051020804965903569873989)
                  ·
                    refine ⟨572066400931106919351373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3051020804965903569873989 572066400931106919351373)
                    ·
                      rfl

theorem cell22_1671143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 1, 2, 1, 4].length) (baseStart_1671143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1671143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1671143 prefixEnd_1671143 := by exact prefixLift 1671143
  have htrace : WordTrace (prefixWord ++ tailWord_1671143) baseStart_1671143 baseEnd_1671143 := by
    simpa [prefixWord, tailWord_1671143, baseEnd_1671143] using wordTrace_append hprefix tailTrace_1671143
  have hstable : (prefixWord ++ tailWord_1671143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1671143).length < 2 ^ (prefixWord ++ tailWord_1671143).sum := by decide
  have hdescent : baseEnd_1671143 < baseStart_1671143 := by decide
  rcases family_descends (prefixWord ++ tailWord_1671143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1671152 : List Nat := [2, 1, 1, 1, 3, 2, 4, 8]
def baseStart_1671152 : Nat := 118140960795 + 1671152 * 2 ^ 59
def prefixEnd_1671152 : Nat := 4983230072969 + 3 ^ 40 * 1671152 * 2
def baseEnd_1671152 : Nat := 63563275757225988430705

theorem tailTrace_1671152 : CollatzResearch.WordTrace tailWord_1671152 prefixEnd_1671152 63563275757225988430705 := by
  unfold tailWord_1671152
  simp only [CollatzResearch.WordTrace]
  refine ⟨30475960420854594442027855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40634613894472792589370473 30475960420854594442027855)
  ·
    refine ⟨45713940631281891663041783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30475960420854594442027855 45713940631281891663041783)
    ·
      refine ⟨68570910946922837494562675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45713940631281891663041783 68570910946922837494562675)
      ·
        refine ⟨102856366420384256241844013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68570910946922837494562675 102856366420384256241844013)
        ·
          refine ⟨38571137407644096090691505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102856366420384256241844013 38571137407644096090691505)
          ·
            refine ⟨28928353055733072068018629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38571137407644096090691505 28928353055733072068018629)
            ·
              refine ⟨5424066197949951012753493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28928353055733072068018629 5424066197949951012753493)
              ·
                refine ⟨63563275757225988430705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5424066197949951012753493 63563275757225988430705)
                ·
                  rfl

theorem cell22_1671152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 8].length) (baseStart_1671152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1671152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1671152 prefixEnd_1671152 := by exact prefixLift 1671152
  have htrace : WordTrace (prefixWord ++ tailWord_1671152) baseStart_1671152 baseEnd_1671152 := by
    simpa [prefixWord, tailWord_1671152, baseEnd_1671152] using wordTrace_append hprefix tailTrace_1671152
  have hstable : (prefixWord ++ tailWord_1671152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1671152).length < 2 ^ (prefixWord ++ tailWord_1671152).sum := by decide
  have hdescent : baseEnd_1671152 < baseStart_1671152 := by decide
  rcases family_descends (prefixWord ++ tailWord_1671152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1671218 : List Nat := [3, 2, 1, 1, 2, 3, 1, 5, 1, 3]
def baseStart_1671218 : Nat := 118140960795 + 1671218 * 2 ^ 59
def prefixEnd_1671218 : Nat := 4983230072969 + 3 ^ 40 * 1671218 * 2
def baseEnd_1671218 : Nat := 572092074963831723726143

theorem tailTrace_1671218 : CollatzResearch.WordTrace tailWord_1671218 prefixEnd_1671218 572092074963831723726143 := by
  unfold tailWord_1671218
  simp only [CollatzResearch.WordTrace]
  refine ⟨15238582014867520538989577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40636218706313388103972205 15238582014867520538989577)
  ·
    refine ⟨11428936511150640404242183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15238582014867520538989577 11428936511150640404242183)
    ·
      refine ⟨17143404766725960606363275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11428936511150640404242183 17143404766725960606363275)
      ·
        refine ⟨25715107150088940909544913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17143404766725960606363275 25715107150088940909544913)
        ·
          refine ⟨19286330362566705682158685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25715107150088940909544913 19286330362566705682158685)
          ·
            refine ⟨7232373885962514630809507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19286330362566705682158685 7232373885962514630809507)
            ·
              refine ⟨10848560828943771946214261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7232373885962514630809507 10848560828943771946214261)
              ·
                refine ⟨1017052577713478619957587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10848560828943771946214261 1017052577713478619957587)
                ·
                  refine ⟨1525578866570217929936381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1017052577713478619957587 1525578866570217929936381)
                  ·
                    refine ⟨572092074963831723726143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1525578866570217929936381 572092074963831723726143)
                    ·
                      rfl

theorem cell22_1671218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 5, 1, 3].length) (baseStart_1671218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1671218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1671218 prefixEnd_1671218 := by exact prefixLift 1671218
  have htrace : WordTrace (prefixWord ++ tailWord_1671218) baseStart_1671218 baseEnd_1671218 := by
    simpa [prefixWord, tailWord_1671218, baseEnd_1671218] using wordTrace_append hprefix tailTrace_1671218
  have hstable : (prefixWord ++ tailWord_1671218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1671218).length < 2 ^ (prefixWord ++ tailWord_1671218).sum := by decide
  have hdescent : baseEnd_1671218 < baseStart_1671218 := by decide
  rcases family_descends (prefixWord ++ tailWord_1671218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1671229 : List Nat := [1, 4, 1, 3, 1, 1, 1, 1, 4, 5]
def baseStart_1671229 : Nat := 118140960795 + 1671229 * 2 ^ 59
def prefixEnd_1671229 : Nat := 4983230072969 + 3 ^ 40 * 1671229 * 2
def baseEnd_1671229 : Nat := 572095840488631361701109

theorem tailTrace_1671229 : CollatzResearch.WordTrace tailWord_1671229 prefixEnd_1671229 572095840488631361701109 := by
  unfold tailWord_1671229
  simp only [CollatzResearch.WordTrace]
  refine ⟨60954729262430231034608741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40636486174953487356405827 60954729262430231034608741)
  ·
    refine ⟨11429011736705668318989139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60954729262430231034608741 11429011736705668318989139)
    ·
      refine ⟨17143517605058502478483709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11429011736705668318989139 17143517605058502478483709)
      ·
        refine ⟨6428819101896938429431391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17143517605058502478483709 6428819101896938429431391)
        ·
          refine ⟨9643228652845407644147087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6428819101896938429431391 9643228652845407644147087)
          ·
            refine ⟨14464842979268111466220631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9643228652845407644147087 14464842979268111466220631)
            ·
              refine ⟨21697264468902167199330947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14464842979268111466220631 21697264468902167199330947)
              ·
                refine ⟨32545896703353250798996421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21697264468902167199330947 32545896703353250798996421)
                ·
                  refine ⟨6102355631878734524811829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32545896703353250798996421 6102355631878734524811829)
                  ·
                    refine ⟨572095840488631361701109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6102355631878734524811829 572095840488631361701109)
                    ·
                      rfl

theorem cell22_1671229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 1, 4, 5].length) (baseStart_1671229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1671229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1671229 prefixEnd_1671229 := by exact prefixLift 1671229
  have htrace : WordTrace (prefixWord ++ tailWord_1671229) baseStart_1671229 baseEnd_1671229 := by
    simpa [prefixWord, tailWord_1671229, baseEnd_1671229] using wordTrace_append hprefix tailTrace_1671229
  have hstable : (prefixWord ++ tailWord_1671229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1671229).length < 2 ^ (prefixWord ++ tailWord_1671229).sum := by decide
  have hdescent : baseEnd_1671229 < baseStart_1671229 := by decide
  rcases family_descends (prefixWord ++ tailWord_1671229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1671244 : List Nat := [2, 2, 1, 3, 1, 1, 2, 1, 5, 4]
def baseStart_1671244 : Nat := 118140960795 + 1671244 * 2 ^ 59
def prefixEnd_1671244 : Nat := 4983230072969 + 3 ^ 40 * 1671244 * 2
def baseEnd_1671244 : Nat := 572100975295176322576063

theorem tailTrace_1671244 : CollatzResearch.WordTrace tailWord_1671244 prefixEnd_1671244 572100975295176322576063 := by
  unfold tailWord_1671244
  simp only [CollatzResearch.WordTrace]
  refine ⟨30477638178687944298202393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40636850904917259064269857 30477638178687944298202393)
  ·
    refine ⟨22858228634015958223651795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30477638178687944298202393 22858228634015958223651795)
    ·
      refine ⟨34287342951023937335477693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22858228634015958223651795 34287342951023937335477693)
      ·
        refine ⟨12857753606633976500804135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34287342951023937335477693 12857753606633976500804135)
        ·
          refine ⟨19286630409950964751206203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12857753606633976500804135 19286630409950964751206203)
          ·
            refine ⟨28929945614926447126809305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19286630409950964751206203 28929945614926447126809305)
            ·
              refine ⟨21697459211194835345106979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28929945614926447126809305 21697459211194835345106979)
              ·
                refine ⟨32546188816792253017660469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21697459211194835345106979 32546188816792253017660469)
                ·
                  refine ⟨3051205201574273720405669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32546188816792253017660469 3051205201574273720405669)
                  ·
                    refine ⟨572100975295176322576063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3051205201574273720405669 572100975295176322576063)
                    ·
                      rfl

theorem cell22_1671244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 1, 5, 4].length) (baseStart_1671244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1671244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1671244 prefixEnd_1671244 := by exact prefixLift 1671244
  have htrace : WordTrace (prefixWord ++ tailWord_1671244) baseStart_1671244 baseEnd_1671244 := by
    simpa [prefixWord, tailWord_1671244, baseEnd_1671244] using wordTrace_append hprefix tailTrace_1671244
  have hstable : (prefixWord ++ tailWord_1671244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1671244).length < 2 ^ (prefixWord ++ tailWord_1671244).sum := by decide
  have hdescent : baseEnd_1671244 < baseStart_1671244 := by decide
  rcases family_descends (prefixWord ++ tailWord_1671244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1671338 : List Nat := [3, 1, 5, 1, 3, 9]
def baseStart_1671338 : Nat := 118140960795 + 1671338 * 2 ^ 59
def prefixEnd_1671338 : Nat := 4983230072969 + 3 ^ 40 * 1671338 * 2
def baseEnd_1671338 : Nat := 7063372264397424823775

theorem tailTrace_1671338 : CollatzResearch.WordTrace tailWord_1671338 prefixEnd_1671338 7063372264397424823775 := by
  unfold tailWord_1671338
  simp only [CollatzResearch.WordTrace]
  refine ⟨15239676204758835662581667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40639136546023561766884445 15239676204758835662581667)
  ·
    refine ⟨22859514307138253493872501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15239676204758835662581667 22859514307138253493872501)
    ·
      refine ⟨2143079466294211265050547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22859514307138253493872501 2143079466294211265050547)
      ·
        refine ⟨3214619199441316897575821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2143079466294211265050547 3214619199441316897575821)
        ·
          refine ⟨1205482199790493836590933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3214619199441316897575821 1205482199790493836590933)
          ·
            refine ⟨7063372264397424823775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1205482199790493836590933 7063372264397424823775)
            ·
              rfl

theorem cell22_1671338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 9].length) (baseStart_1671338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1671338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1671338 prefixEnd_1671338 := by exact prefixLift 1671338
  have htrace : WordTrace (prefixWord ++ tailWord_1671338) baseStart_1671338 baseEnd_1671338 := by
    simpa [prefixWord, tailWord_1671338, baseEnd_1671338] using wordTrace_append hprefix tailTrace_1671338
  have hstable : (prefixWord ++ tailWord_1671338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1671338).length < 2 ^ (prefixWord ++ tailWord_1671338).sum := by decide
  have hdescent : baseEnd_1671338 < baseStart_1671338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1671338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1671411 : List Nat := [1, 1, 1, 2, 2, 4, 4, 1, 6]
def baseStart_1671411 : Nat := 118140960795 + 1671411 * 2 ^ 59
def prefixEnd_1671411 : Nat := 4983230072969 + 3 ^ 40 * 1671411 * 2
def baseEnd_1671411 : Nat := 190719380936014517883517

theorem tailTrace_1671411 : CollatzResearch.WordTrace tailWord_1671411 prefixEnd_1671411 190719380936014517883517 := by
  unfold tailWord_1671411
  simp only [CollatzResearch.WordTrace]
  refine ⟨60961367347770876117734087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40640911565180584078489391 60961367347770876117734087)
  ·
    refine ⟨91442051021656314176601131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60961367347770876117734087 91442051021656314176601131)
    ·
      refine ⟨137163076532484471264901697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91442051021656314176601131 137163076532484471264901697)
      ·
        refine ⟨102872307399363353448676273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137163076532484471264901697 102872307399363353448676273)
        ·
          refine ⟨77154230549522515086507205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102872307399363353448676273 77154230549522515086507205)
          ·
            refine ⟨14466418228035471578720101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77154230549522515086507205 14466418228035471578720101)
            ·
              refine ⟨2712453417756650921010019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14466418228035471578720101 2712453417756650921010019)
              ·
                refine ⟨4068680126634976381515029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2712453417756650921010019 4068680126634976381515029)
                ·
                  refine ⟨190719380936014517883517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4068680126634976381515029 190719380936014517883517)
                  ·
                    rfl

theorem cell22_1671411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 4, 1, 6].length) (baseStart_1671411 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1671411 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1671411 prefixEnd_1671411 := by exact prefixLift 1671411
  have htrace : WordTrace (prefixWord ++ tailWord_1671411) baseStart_1671411 baseEnd_1671411 := by
    simpa [prefixWord, tailWord_1671411, baseEnd_1671411] using wordTrace_append hprefix tailTrace_1671411
  have hstable : (prefixWord ++ tailWord_1671411).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1671411).length < 2 ^ (prefixWord ++ tailWord_1671411).sum := by decide
  have hdescent : baseEnd_1671411 < baseStart_1671411 := by decide
  rcases family_descends (prefixWord ++ tailWord_1671411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1671441 : List Nat := [1, 2, 2, 1, 1, 5, 2, 1, 1, 6]
def baseStart_1671441 : Nat := 118140960795 + 1671441 * 2 ^ 59
def prefixEnd_1671441 : Nat := 4983230072969 + 3 ^ 40 * 1671441 * 2
def baseEnd_1671441 : Nat := 572168412421133475400459

theorem tailTrace_1671441 : CollatzResearch.WordTrace tailWord_1671441 prefixEnd_1671441 572168412421133475400459 := by
  unfold tailWord_1671441
  simp only [CollatzResearch.WordTrace]
  refine ⟨60962461537662191241326177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40641641025108127494217451 60962461537662191241326177)
  ·
    refine ⟨45721846153246643430994633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60962461537662191241326177 45721846153246643430994633)
    ·
      refine ⟨34291384614934982573245975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45721846153246643430994633 34291384614934982573245975)
      ·
        refine ⟨51437076922402473859868963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34291384614934982573245975 51437076922402473859868963)
        ·
          refine ⟨77155615383603710789803445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51437076922402473859868963 77155615383603710789803445)
          ·
            refine ⟨7233338942212847886544073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 77155615383603710789803445 7233338942212847886544073)
            ·
              refine ⟨5425004206659635914908055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7233338942212847886544073 5425004206659635914908055)
              ·
                refine ⟨8137506309989453872362083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5425004206659635914908055 8137506309989453872362083)
                ·
                  refine ⟨12206259464984180808543125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8137506309989453872362083 12206259464984180808543125)
                  ·
                    refine ⟨572168412421133475400459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12206259464984180808543125 572168412421133475400459)
                    ·
                      rfl

theorem cell22_1671441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 6].length) (baseStart_1671441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1671441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1671441 prefixEnd_1671441 := by exact prefixLift 1671441
  have htrace : WordTrace (prefixWord ++ tailWord_1671441) baseStart_1671441 baseEnd_1671441 := by
    simpa [prefixWord, tailWord_1671441, baseEnd_1671441] using wordTrace_append hprefix tailTrace_1671441
  have hstable : (prefixWord ++ tailWord_1671441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1671441).length < 2 ^ (prefixWord ++ tailWord_1671441).sum := by decide
  have hdescent : baseEnd_1671441 < baseStart_1671441 := by decide
  rcases family_descends (prefixWord ++ tailWord_1671441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1671456 : List Nat := [2, 1, 1, 5, 2, 1, 10]
def baseStart_1671456 : Nat := 118140960795 + 1671456 * 2 ^ 59
def prefixEnd_1671456 : Nat := 4983230072969 + 3 ^ 40 * 1671456 * 2
def baseEnd_1671456 : Nat := 21191612860284386528719

theorem tailTrace_1671456 : CollatzResearch.WordTrace tailWord_1671456 prefixEnd_1671456 21191612860284386528719 := by
  unfold tailWord_1671456
  simp only [CollatzResearch.WordTrace]
  refine ⟨30481504316303924401561111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40642005755071899202081481 30481504316303924401561111)
  ·
    refine ⟨45722256474455886602341667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30481504316303924401561111 45722256474455886602341667)
    ·
      refine ⟨68583384711683829903512501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45722256474455886602341667 68583384711683829903512501)
      ·
        refine ⟨6429692316720359053454297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 68583384711683829903512501 6429692316720359053454297)
        ·
          refine ⟨4822269237540269290090723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6429692316720359053454297 4822269237540269290090723)
          ·
            refine ⟨7233403856310403935136085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4822269237540269290090723 7233403856310403935136085)
            ·
              refine ⟨21191612860284386528719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 7233403856310403935136085 21191612860284386528719)
              ·
                rfl

theorem cell22_1671456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 10].length) (baseStart_1671456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1671456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1671456 prefixEnd_1671456 := by exact prefixLift 1671456
  have htrace : WordTrace (prefixWord ++ tailWord_1671456) baseStart_1671456 baseEnd_1671456 := by
    simpa [prefixWord, tailWord_1671456, baseEnd_1671456] using wordTrace_append hprefix tailTrace_1671456
  have hstable : (prefixWord ++ tailWord_1671456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1671456).length < 2 ^ (prefixWord ++ tailWord_1671456).sum := by decide
  have hdescent : baseEnd_1671456 < baseStart_1671456 := by decide
  rcases family_descends (prefixWord ++ tailWord_1671456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1671458 : List Nat := [3, 3, 1, 1, 3, 1, 1, 1, 4, 4]
def baseStart_1671458 : Nat := 118140960795 + 1671458 * 2 ^ 59
def prefixEnd_1671458 : Nat := 4983230072969 + 3 ^ 40 * 1671458 * 2
def baseEnd_1671458 : Nat := 572174231868551097725407

theorem tailTrace_1671458 : CollatzResearch.WordTrace tailWord_1671458 prefixEnd_1671458 572174231868551097725407 := by
  unfold tailWord_1671458
  simp only [CollatzResearch.WordTrace]
  refine ⟨15240770394650150786173757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40642054385733735429796685 15240770394650150786173757)
  ·
    refine ⟨5715288897993806544815159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15240770394650150786173757 5715288897993806544815159)
    ·
      refine ⟨8572933346990709817222739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5715288897993806544815159 8572933346990709817222739)
      ·
        refine ⟨12859400020486064725834109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8572933346990709817222739 12859400020486064725834109)
        ·
          refine ⟨4822275007682274272187791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12859400020486064725834109 4822275007682274272187791)
          ·
            refine ⟨7233412511523411408281687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4822275007682274272187791 7233412511523411408281687)
            ·
              refine ⟨10850118767285117112422531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7233412511523411408281687 10850118767285117112422531)
              ·
                refine ⟨16275178150927675668633797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10850118767285117112422531 16275178150927675668633797)
                ·
                  refine ⟨3051595903298939187868837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16275178150927675668633797 3051595903298939187868837)
                  ·
                    refine ⟨572174231868551097725407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3051595903298939187868837 572174231868551097725407)
                    ·
                      rfl

theorem cell22_1671458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 1, 4, 4].length) (baseStart_1671458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1671458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1671458 prefixEnd_1671458 := by exact prefixLift 1671458
  have htrace : WordTrace (prefixWord ++ tailWord_1671458) baseStart_1671458 baseEnd_1671458 := by
    simpa [prefixWord, tailWord_1671458, baseEnd_1671458] using wordTrace_append hprefix tailTrace_1671458
  have hstable : (prefixWord ++ tailWord_1671458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1671458).length < 2 ^ (prefixWord ++ tailWord_1671458).sum := by decide
  have hdescent : baseEnd_1671458 < baseStart_1671458 := by decide
  rcases family_descends (prefixWord ++ tailWord_1671458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1671473 : List Nat := [1, 2, 2, 3, 4, 1, 2, 7]
def baseStart_1671473 : Nat := 118140960795 + 1671473 * 2 ^ 59
def prefixEnd_1671473 : Nat := 4983230072969 + 3 ^ 40 * 1671473 * 2
def baseEnd_1671473 : Nat := 63575485186121784288929

theorem tailTrace_1671473 : CollatzResearch.WordTrace tailWord_1671473 prefixEnd_1671473 63575485186121784288929 := by
  unfold tailWord_1671473
  simp only [CollatzResearch.WordTrace]
  refine ⟨60963628673546260706491073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40642419115697507137660715 60963628673546260706491073)
  ·
    refine ⟨45722721505159695529868305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60963628673546260706491073 45722721505159695529868305)
    ·
      refine ⟨34292041128869771647401229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45722721505159695529868305 34292041128869771647401229)
      ·
        refine ⟨12859515423326164367775461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34292041128869771647401229 12859515423326164367775461)
        ·
          refine ⟨2411159141873655818957899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12859515423326164367775461 2411159141873655818957899)
          ·
            refine ⟨3616738712810483728436849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2411159141873655818957899 3616738712810483728436849)
            ·
              refine ⟨2712554034607862796327637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3616738712810483728436849 2712554034607862796327637)
              ·
                refine ⟨63575485186121784288929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2712554034607862796327637 63575485186121784288929)
                ·
                  rfl

theorem cell22_1671473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 2, 7].length) (baseStart_1671473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1671473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1671473 prefixEnd_1671473 := by exact prefixLift 1671473
  have htrace : WordTrace (prefixWord ++ tailWord_1671473) baseStart_1671473 baseEnd_1671473 := by
    simpa [prefixWord, tailWord_1671473, baseEnd_1671473] using wordTrace_append hprefix tailTrace_1671473
  have hstable : (prefixWord ++ tailWord_1671473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1671473).length < 2 ^ (prefixWord ++ tailWord_1671473).sum := by decide
  have hdescent : baseEnd_1671473 < baseStart_1671473 := by decide
  rcases family_descends (prefixWord ++ tailWord_1671473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1671492 : List Nat := [2, 3, 4, 1, 2, 1, 2, 1, 2, 4]
def baseStart_1671492 : Nat := 118140960795 + 1671492 * 2 ^ 59
def prefixEnd_1671492 : Nat := 4983230072969 + 3 ^ 40 * 1671492 * 2
def baseEnd_1671492 : Nat := 572185870763386342375303

theorem tailTrace_1671492 : CollatzResearch.WordTrace tailWord_1671492 prefixEnd_1671492 572185870763386342375303 := by
  unfold tailWord_1671492
  simp only [CollatzResearch.WordTrace]
  refine ⟨30482160830238713475716365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40642881106984951300955153 30482160830238713475716365)
  ·
    refine ⟨11430810311339517553393637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30482160830238713475716365 11430810311339517553393637)
    ·
      refine ⟨2143276933376159541261307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11430810311339517553393637 2143276933376159541261307)
      ·
        refine ⟨3214915400064239311891961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2143276933376159541261307 3214915400064239311891961)
        ·
          refine ⟨2411186550048179483918971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3214915400064239311891961 2411186550048179483918971)
          ·
            refine ⟨3616779825072269225878457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2411186550048179483918971 3616779825072269225878457)
            ·
              refine ⟨2712584868804201919408843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3616779825072269225878457 2712584868804201919408843)
              ·
                refine ⟨4068877303206302879113265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2712584868804201919408843 4068877303206302879113265)
                ·
                  refine ⟨3051657977404727159334949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4068877303206302879113265 3051657977404727159334949)
                  ·
                    refine ⟨572185870763386342375303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3051657977404727159334949 572185870763386342375303)
                    ·
                      rfl

theorem cell22_1671492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_1671492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1671492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1671492 prefixEnd_1671492 := by exact prefixLift 1671492
  have htrace : WordTrace (prefixWord ++ tailWord_1671492) baseStart_1671492 baseEnd_1671492 := by
    simpa [prefixWord, tailWord_1671492, baseEnd_1671492] using wordTrace_append hprefix tailTrace_1671492
  have hstable : (prefixWord ++ tailWord_1671492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1671492).length < 2 ^ (prefixWord ++ tailWord_1671492).sum := by decide
  have hdescent : baseEnd_1671492 < baseStart_1671492 := by decide
  rcases family_descends (prefixWord ++ tailWord_1671492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1671533 : List Nat := [1, 5, 1, 1, 1, 2, 3, 1, 2, 5]
def baseStart_1671533 : Nat := 118140960795 + 1671533 * 2 ^ 59
def prefixEnd_1671533 : Nat := 4983230072969 + 3 ^ 40 * 1671533 * 2
def baseEnd_1671533 : Nat := 572199905901275902100177

theorem tailTrace_1671533 : CollatzResearch.WordTrace tailWord_1671533 prefixEnd_1671533 572199905901275902100177 := by
  unfold tailWord_1671533
  simp only [CollatzResearch.WordTrace]
  refine ⟨60965817053328890953675253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40643878035552593969116835 60965817053328890953675253)
  ·
    refine ⟨5715545348749583526907055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 60965817053328890953675253 5715545348749583526907055)
    ·
      refine ⟨8573318023124375290360583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5715545348749583526907055 8573318023124375290360583)
      ·
        refine ⟨12859977034686562935540875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8573318023124375290360583 12859977034686562935540875)
        ·
          refine ⟨19289965552029844403311313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12859977034686562935540875 19289965552029844403311313)
          ·
            refine ⟨14467474164022383302483485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19289965552029844403311313 14467474164022383302483485)
            ·
              refine ⟨5425302811508393738431307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14467474164022383302483485 5425302811508393738431307)
              ·
                refine ⟨8137954217262590607646961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5425302811508393738431307 8137954217262590607646961)
                ·
                  refine ⟨6103465662946942955735221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8137954217262590607646961 6103465662946942955735221)
                  ·
                    refine ⟨572199905901275902100177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6103465662946942955735221 572199905901275902100177)
                    ·
                      rfl

theorem cell22_1671533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 1, 2, 5].length) (baseStart_1671533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1671533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1671533 prefixEnd_1671533 := by exact prefixLift 1671533
  have htrace : WordTrace (prefixWord ++ tailWord_1671533) baseStart_1671533 baseEnd_1671533 := by
    simpa [prefixWord, tailWord_1671533, baseEnd_1671533] using wordTrace_append hprefix tailTrace_1671533
  have hstable : (prefixWord ++ tailWord_1671533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1671533).length < 2 ^ (prefixWord ++ tailWord_1671533).sum := by decide
  have hdescent : baseEnd_1671533 < baseStart_1671533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1671533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1671687 : List Nat := [1, 1, 4, 3, 3, 1, 2, 2, 5]
def baseStart_1671687 : Nat := 118140960795 + 1671687 * 2 ^ 59
def prefixEnd_1671687 : Nat := 4983230072969 + 3 ^ 40 * 1671687 * 2
def baseEnd_1671687 : Nat := 190750874416156944583235

theorem tailTrace_1671687 : CollatzResearch.WordTrace tailWord_1671687 prefixEnd_1671687 190750874416156944583235 := by
  unfold tailWord_1671687
  simp only [CollatzResearch.WordTrace]
  refine ⟨60971433894770975254781315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40647622596513983503187543 60971433894770975254781315)
  ·
    refine ⟨91457150842156462882171973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60971433894770975254781315 91457150842156462882171973)
    ·
      refine ⟨17148215782904336790407245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91457150842156462882171973 17148215782904336790407245)
      ·
        refine ⟨6430580918589126296402717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17148215782904336790407245 6430580918589126296402717)
        ·
          refine ⟨2411467844470922361151019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6430580918589126296402717 2411467844470922361151019)
          ·
            refine ⟨3617201766706383541726529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2411467844470922361151019 3617201766706383541726529)
            ·
              refine ⟨2712901325029787656294897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3617201766706383541726529 2712901325029787656294897)
              ·
                refine ⟨2034675993772340742221173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2712901325029787656294897 2034675993772340742221173)
                ·
                  refine ⟨190750874416156944583235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2034675993772340742221173 190750874416156944583235)
                  ·
                    rfl

theorem cell22_1671687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 2, 2, 5].length) (baseStart_1671687 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1671687 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1671687 prefixEnd_1671687 := by exact prefixLift 1671687
  have htrace : WordTrace (prefixWord ++ tailWord_1671687) baseStart_1671687 baseEnd_1671687 := by
    simpa [prefixWord, tailWord_1671687, baseEnd_1671687] using wordTrace_append hprefix tailTrace_1671687
  have hstable : (prefixWord ++ tailWord_1671687).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1671687).length < 2 ^ (prefixWord ++ tailWord_1671687).sum := by decide
  have hdescent : baseEnd_1671687 < baseStart_1671687 := by decide
  rcases family_descends (prefixWord ++ tailWord_1671687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1671691 : List Nat := [1, 1, 1, 1, 7, 3, 2, 2, 1, 3]
def baseStart_1671691 : Nat := 118140960795 + 1671691 * 2 ^ 59
def prefixEnd_1671691 : Nat := 4983230072969 + 3 ^ 40 * 1671691 * 2
def baseEnd_1671691 : Nat := 572253992530216156649693

theorem tailTrace_1671691 : CollatzResearch.WordTrace tailWord_1671691 prefixEnd_1671691 572253992530216156649693 := by
  unfold tailWord_1671691
  simp only [CollatzResearch.WordTrace]
  refine ⟨60971579786756483937926927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40647719857837655958617951 60971579786756483937926927)
  ·
    refine ⟨91457369680134725906890391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60971579786756483937926927 91457369680134725906890391)
    ·
      refine ⟨137186054520202088860335587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91457369680134725906890391 137186054520202088860335587)
      ·
        refine ⟨205779081780303133290503381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137186054520202088860335587 205779081780303133290503381)
        ·
          refine ⟨4822947229225854686496173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 205779081780303133290503381 4822947229225854686496173)
          ·
            refine ⟨1808605210959695507436065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4822947229225854686496173 1808605210959695507436065)
            ·
              refine ⟨1356453908219771630577049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1808605210959695507436065 1356453908219771630577049)
              ·
                refine ⟨1017340431164828722932787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1356453908219771630577049 1017340431164828722932787)
                ·
                  refine ⟨1526010646747243084399181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1017340431164828722932787 1526010646747243084399181)
                  ·
                    refine ⟨572253992530216156649693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1526010646747243084399181 572253992530216156649693)
                    ·
                      rfl

theorem cell22_1671691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 2, 2, 1, 3].length) (baseStart_1671691 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1671691 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1671691 prefixEnd_1671691 := by exact prefixLift 1671691
  have htrace : WordTrace (prefixWord ++ tailWord_1671691) baseStart_1671691 baseEnd_1671691 := by
    simpa [prefixWord, tailWord_1671691, baseEnd_1671691] using wordTrace_append hprefix tailTrace_1671691
  have hstable : (prefixWord ++ tailWord_1671691).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1671691).length < 2 ^ (prefixWord ++ tailWord_1671691).sum := by decide
  have hdescent : baseEnd_1671691 < baseStart_1671691 := by decide
  rcases family_descends (prefixWord ++ tailWord_1671691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1671715 : List Nat := [1, 1, 1, 4, 4, 2, 1, 2, 6]
def baseStart_1671715 : Nat := 118140960795 + 1671715 * 2 ^ 59
def prefixEnd_1671715 : Nat := 4983230072969 + 3 ^ 40 * 1671715 * 2
def baseEnd_1671715 : Nat := 190754069406896031349873

theorem tailTrace_1671715 : CollatzResearch.WordTrace tailWord_1671715 prefixEnd_1671715 190754069406896031349873 := by
  unfold tailWord_1671715
  simp only [CollatzResearch.WordTrace]
  refine ⟨60972455138669536036800599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40648303425779690691200399 60972455138669536036800599)
  ·
    refine ⟨91458682708004304055200899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60972455138669536036800599 91458682708004304055200899)
    ·
      refine ⟨137188024062006456082801349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91458682708004304055200899 137188024062006456082801349)
      ·
        refine ⟨25722754511626210515525253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 137188024062006456082801349 25722754511626210515525253)
        ·
          refine ⟨4823016470929914471660985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25722754511626210515525253 4823016470929914471660985)
          ·
            refine ⟨3617262353197435853745739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4823016470929914471660985 3617262353197435853745739)
            ·
              refine ⟨5425893529796153780618609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3617262353197435853745739 5425893529796153780618609)
              ·
                refine ⟨4069420147347115335463957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5425893529796153780618609 4069420147347115335463957)
                ·
                  refine ⟨190754069406896031349873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4069420147347115335463957 190754069406896031349873)
                  ·
                    rfl

theorem cell22_1671715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 2, 6].length) (baseStart_1671715 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1671715 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1671715 prefixEnd_1671715 := by exact prefixLift 1671715
  have htrace : WordTrace (prefixWord ++ tailWord_1671715) baseStart_1671715 baseEnd_1671715 := by
    simpa [prefixWord, tailWord_1671715, baseEnd_1671715] using wordTrace_append hprefix tailTrace_1671715
  have hstable : (prefixWord ++ tailWord_1671715).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1671715).length < 2 ^ (prefixWord ++ tailWord_1671715).sum := by decide
  have hdescent : baseEnd_1671715 < baseStart_1671715 := by decide
  rcases family_descends (prefixWord ++ tailWord_1671715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1671725 : List Nat := [1, 5, 4, 1, 1, 1, 2, 3, 1, 3]
def baseStart_1671725 : Nat := 118140960795 + 1671725 * 2 ^ 59
def prefixEnd_1671725 : Nat := 4983230072969 + 3 ^ 40 * 1671725 * 2
def baseEnd_1671725 : Nat := 572265631425051401299589

theorem tailTrace_1671725 : CollatzResearch.WordTrace tailWord_1671725 prefixEnd_1671725 572265631425051401299589 := by
  unfold tailWord_1671725
  simp only [CollatzResearch.WordTrace]
  refine ⟨60972819868633307744664629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40648546579088871829776419 60972819868633307744664629)
  ·
    refine ⟨5716201862684372601062309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 60972819868633307744664629 5716201862684372601062309)
    ·
      refine ⟨1071787849253319862699183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5716201862684372601062309 1071787849253319862699183)
      ·
        refine ⟨1607681773879979794048775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1071787849253319862699183 1607681773879979794048775)
        ·
          refine ⟨2411522660819969691073163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1607681773879979794048775 2411522660819969691073163)
          ·
            refine ⟨3617283991229954536609745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2411522660819969691073163 3617283991229954536609745)
            ·
              refine ⟨2712962993422465902457309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3617283991229954536609745 2712962993422465902457309)
              ·
                refine ⟨1017361122533424713421491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2712962993422465902457309 1017361122533424713421491)
                ·
                  refine ⟨1526041683800137070132237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1017361122533424713421491 1526041683800137070132237)
                  ·
                    refine ⟨572265631425051401299589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1526041683800137070132237 572265631425051401299589)
                    ·
                      rfl

theorem cell22_1671725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_1671725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1671725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1671725 prefixEnd_1671725 := by exact prefixLift 1671725
  have htrace : WordTrace (prefixWord ++ tailWord_1671725) baseStart_1671725 baseEnd_1671725 := by
    simpa [prefixWord, tailWord_1671725, baseEnd_1671725] using wordTrace_append hprefix tailTrace_1671725
  have hstable : (prefixWord ++ tailWord_1671725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1671725).length < 2 ^ (prefixWord ++ tailWord_1671725).sum := by decide
  have hdescent : baseEnd_1671725 < baseStart_1671725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1671725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1671730 : List Nat := [3, 2, 1, 1, 2, 1, 4, 2, 1, 5]
def baseStart_1671730 : Nat := 118140960795 + 1671730 * 2 ^ 59
def prefixEnd_1671730 : Nat := 4983230072969 + 3 ^ 40 * 1671730 * 2
def baseEnd_1671730 : Nat := 572267343027233054924573

theorem tailTrace_1671730 : CollatzResearch.WordTrace tailWord_1671730 prefixEnd_1671730 572267343027233054924573 := by
  unfold tailWord_1671730
  simp only [CollatzResearch.WordTrace]
  refine ⟨15243250558403798399649161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40648668155743462399064429 15243250558403798399649161)
  ·
    refine ⟨11432437918802848799736871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15243250558403798399649161 11432437918802848799736871)
    ·
      refine ⟨17148656878204273199605307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11432437918802848799736871 17148656878204273199605307)
      ·
        refine ⟨25722985317306409799407961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17148656878204273199605307 25722985317306409799407961)
        ·
          refine ⟨19292238987979807349555971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25722985317306409799407961 19292238987979807349555971)
          ·
            refine ⟨28938358481969711024333957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19292238987979807349555971 28938358481969711024333957)
            ·
              refine ⟨5425942215369320817062617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28938358481969711024333957 5425942215369320817062617)
              ·
                refine ⟨4069456661526990612796963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5425942215369320817062617 4069456661526990612796963)
                ·
                  refine ⟨6104184992290485919195445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4069456661526990612796963 6104184992290485919195445)
                  ·
                    refine ⟨572267343027233054924573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6104184992290485919195445 572267343027233054924573)
                    ·
                      rfl

theorem cell22_1671730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 2, 1, 5].length) (baseStart_1671730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1671730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1671730 prefixEnd_1671730 := by exact prefixLift 1671730
  have htrace : WordTrace (prefixWord ++ tailWord_1671730) baseStart_1671730 baseEnd_1671730 := by
    simpa [prefixWord, tailWord_1671730, baseEnd_1671730] using wordTrace_append hprefix tailTrace_1671730
  have hstable : (prefixWord ++ tailWord_1671730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1671730).length < 2 ^ (prefixWord ++ tailWord_1671730).sum := by decide
  have hdescent : baseEnd_1671730 < baseStart_1671730 := by decide
  rcases family_descends (prefixWord ++ tailWord_1671730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1671734 : List Nat := [5, 1, 2, 1, 2, 2, 1, 3, 1, 4]
def baseStart_1671734 : Nat := 118140960795 + 1671734 * 2 ^ 59
def prefixEnd_1671734 : Nat := 4983230072969 + 3 ^ 40 * 1671734 * 2
def baseEnd_1671734 : Nat := 572268712308978377824561

theorem tailTrace_1671734 : CollatzResearch.WordTrace tailWord_1671734 prefixEnd_1671734 572268712308978377824561 := by
  unfold tailWord_1671734
  simp only [CollatzResearch.WordTrace]
  refine ⟨3810821757850043892608891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40648765417067134854494837 3810821757850043892608891)
  ·
    refine ⟨5716232636775065838913337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3810821757850043892608891 5716232636775065838913337)
    ·
      refine ⟨4287174477581299379185003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5716232636775065838913337 4287174477581299379185003)
      ·
        refine ⟨6430761716371949068777505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4287174477581299379185003 6430761716371949068777505)
        ·
          refine ⟨4823071287278961801583129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6430761716371949068777505 4823071287278961801583129)
          ·
            refine ⟨3617303465459221351187347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4823071287278961801583129 3617303465459221351187347)
            ·
              refine ⟨5425955198188832026781021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3617303465459221351187347 5425955198188832026781021)
              ·
                refine ⟨2034733199320812010042883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5425955198188832026781021 2034733199320812010042883)
                ·
                  refine ⟨3052099798981218015064325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2034733199320812010042883 3052099798981218015064325)
                  ·
                    refine ⟨572268712308978377824561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3052099798981218015064325 572268712308978377824561)
                    ·
                      rfl

theorem cell22_1671734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_1671734 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1671734 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1671734 prefixEnd_1671734 := by exact prefixLift 1671734
  have htrace : WordTrace (prefixWord ++ tailWord_1671734) baseStart_1671734 baseEnd_1671734 := by
    simpa [prefixWord, tailWord_1671734, baseEnd_1671734] using wordTrace_append hprefix tailTrace_1671734
  have hstable : (prefixWord ++ tailWord_1671734).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1671734).length < 2 ^ (prefixWord ++ tailWord_1671734).sum := by decide
  have hdescent : baseEnd_1671734 < baseStart_1671734 := by decide
  rcases family_descends (prefixWord ++ tailWord_1671734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1671743 : List Nat := [1, 1, 2, 2, 3, 2, 11]
def baseStart_1671743 : Nat := 118140960795 + 1671743 * 2 ^ 59
def prefixEnd_1671743 : Nat := 4983230072969 + 3 ^ 40 * 1671743 * 2
def baseEnd_1671743 : Nat := 21195251599737235346279

theorem tailTrace_1671743 : CollatzResearch.WordTrace tailWord_1671743 prefixEnd_1671743 21195251599737235346279 := by
  unfold tailWord_1671743
  simp only [CollatzResearch.WordTrace]
  refine ⟨60973476382568096818819883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40648984255045397879213255 60973476382568096818819883)
  ·
    refine ⟨91460214573852145228229825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60973476382568096818819883 91460214573852145228229825)
    ·
      refine ⟨68595160930389108921172369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91460214573852145228229825 68595160930389108921172369)
      ·
        refine ⟨51446370697791831690879277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68595160930389108921172369 51446370697791831690879277)
        ·
          refine ⟨19292389011671936884079729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51446370697791831690879277 19292389011671936884079729)
          ·
            refine ⟨14469291758753952663059797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19292389011671936884079729 14469291758753952663059797)
            ·
              refine ⟨21195251599737235346279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 14469291758753952663059797 21195251599737235346279)
              ·
                rfl

theorem cell22_1671743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 11].length) (baseStart_1671743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1671743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1671743 prefixEnd_1671743 := by exact prefixLift 1671743
  have htrace : WordTrace (prefixWord ++ tailWord_1671743) baseStart_1671743 baseEnd_1671743 := by
    simpa [prefixWord, tailWord_1671743, baseEnd_1671743] using wordTrace_append hprefix tailTrace_1671743
  have hstable : (prefixWord ++ tailWord_1671743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1671743).length < 2 ^ (prefixWord ++ tailWord_1671743).sum := by decide
  have hdescent : baseEnd_1671743 < baseStart_1671743 := by decide
  rcases family_descends (prefixWord ++ tailWord_1671743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1671777 : List Nat := [1, 2, 3, 1, 1, 6, 2, 6]
def baseStart_1671777 : Nat := 118140960795 + 1671777 * 2 ^ 59
def prefixEnd_1671777 : Nat := 4983230072969 + 3 ^ 40 * 1671777 * 2
def baseEnd_1671777 : Nat := 63587048009748955444381

theorem tailTrace_1671777 : CollatzResearch.WordTrace tailWord_1671777 prefixEnd_1671777 63587048009748955444381 := by
  unfold tailWord_1671777
  simp only [CollatzResearch.WordTrace]
  refine ⟨60974716464444920625557585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40649810976296613750371723 60974716464444920625557585)
  ·
    refine ⟨45731037348333690469168189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60974716464444920625557585 45731037348333690469168189)
    ·
      refine ⟨17149139005625133925938071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45731037348333690469168189 17149139005625133925938071)
      ·
        refine ⟨25723708508437700888907107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17149139005625133925938071 25723708508437700888907107)
        ·
          refine ⟨38585562762656551333360661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25723708508437700888907107 38585562762656551333360661)
          ·
            refine ⟨1808698254499525843751281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 38585562762656551333360661 1808698254499525843751281)
            ·
              refine ⟨1356523690874644382813461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1808698254499525843751281 1356523690874644382813461)
              ·
                refine ⟨63587048009748955444381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1356523690874644382813461 63587048009748955444381)
                ·
                  rfl

theorem cell22_1671777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 2, 6].length) (baseStart_1671777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1671777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1671777 prefixEnd_1671777 := by exact prefixLift 1671777
  have htrace : WordTrace (prefixWord ++ tailWord_1671777) baseStart_1671777 baseEnd_1671777 := by
    simpa [prefixWord, tailWord_1671777, baseEnd_1671777] using wordTrace_append hprefix tailTrace_1671777
  have hstable : (prefixWord ++ tailWord_1671777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1671777).length < 2 ^ (prefixWord ++ tailWord_1671777).sum := by decide
  have hdescent : baseEnd_1671777 < baseStart_1671777 := by decide
  rcases family_descends (prefixWord ++ tailWord_1671777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1671822 : List Nat := [4, 1, 1, 3, 1, 1, 3, 3, 5]
def baseStart_1671822 : Nat := 118140960795 + 1671822 * 2 ^ 59
def prefixEnd_1671822 : Nat := 4983230072969 + 3 ^ 40 * 1671822 * 2
def baseEnd_1671822 : Nat := 190766278835791827208097

theorem tailTrace_1671822 : CollatzResearch.WordTrace tailWord_1671822 prefixEnd_1671822 190766278835791827208097 := by
  unfold tailWord_1671822
  simp only [CollatzResearch.WordTrace]
  refine ⟨7622044718660236663868215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40650905166187928873963813 7622044718660236663868215)
  ·
    refine ⟨11433067077990354995802323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7622044718660236663868215 11433067077990354995802323)
    ·
      refine ⟨17149600616985532493703485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11433067077990354995802323 17149600616985532493703485)
      ·
        refine ⟨6431100231369574685138807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17149600616985532493703485 6431100231369574685138807)
        ·
          refine ⟨9646650347054362027708211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6431100231369574685138807 9646650347054362027708211)
          ·
            refine ⟨14469975520581543041562317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9646650347054362027708211 14469975520581543041562317)
            ·
              refine ⟨5426240820218078640585869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14469975520581543041562317 5426240820218078640585869)
              ·
                refine ⟨2034840307581779490219701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5426240820218078640585869 2034840307581779490219701)
                ·
                  refine ⟨190766278835791827208097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2034840307581779490219701 190766278835791827208097)
                  ·
                    rfl

theorem cell22_1671822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 3, 5].length) (baseStart_1671822 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1671822 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1671822 prefixEnd_1671822 := by exact prefixLift 1671822
  have htrace : WordTrace (prefixWord ++ tailWord_1671822) baseStart_1671822 baseEnd_1671822 := by
    simpa [prefixWord, tailWord_1671822, baseEnd_1671822] using wordTrace_append hprefix tailTrace_1671822
  have hstable : (prefixWord ++ tailWord_1671822).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1671822).length < 2 ^ (prefixWord ++ tailWord_1671822).sum := by decide
  have hdescent : baseEnd_1671822 < baseStart_1671822 := by decide
  rcases family_descends (prefixWord ++ tailWord_1671822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1671865 : List Nat := [1, 2, 1, 4, 1, 1, 1, 1, 5, 5]
def baseStart_1671865 : Nat := 118140960795 + 1671865 * 2 ^ 59
def prefixEnd_1671865 : Nat := 4983230072969 + 3 ^ 40 * 1671865 * 2
def baseEnd_1671865 : Nat := 572313556286137702799159

theorem tailTrace_1671865 : CollatzResearch.WordTrace tailWord_1671865 prefixEnd_1671865 572313556286137702799159 := by
  unfold tailWord_1671865
  simp only [CollatzResearch.WordTrace]
  refine ⟨60977926088126111654761049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40651950725417407769840699 60977926088126111654761049)
  ·
    refine ⟨45733444566094583741070787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60977926088126111654761049 45733444566094583741070787)
    ·
      refine ⟨68600166849141875611606181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45733444566094583741070787 68600166849141875611606181)
      ·
        refine ⟨12862531284214101677176159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68600166849141875611606181 12862531284214101677176159)
        ·
          refine ⟨19293796926321152515764239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12862531284214101677176159 19293796926321152515764239)
          ·
            refine ⟨28940695389481728773646359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19293796926321152515764239 28940695389481728773646359)
            ·
              refine ⟨43411043084222593160469539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28940695389481728773646359 43411043084222593160469539)
              ·
                refine ⟨65116564626333889740704309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43411043084222593160469539 65116564626333889740704309)
                ·
                  refine ⟨6104677933718802163191029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 65116564626333889740704309 6104677933718802163191029)
                  ·
                    refine ⟨572313556286137702799159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6104677933718802163191029 572313556286137702799159)
                    ·
                      rfl

theorem cell22_1671865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 5, 5].length) (baseStart_1671865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1671865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1671865 prefixEnd_1671865 := by exact prefixLift 1671865
  have htrace : WordTrace (prefixWord ++ tailWord_1671865) baseStart_1671865 baseEnd_1671865 := by
    simpa [prefixWord, tailWord_1671865, baseEnd_1671865] using wordTrace_append hprefix tailTrace_1671865
  have hstable : (prefixWord ++ tailWord_1671865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1671865).length < 2 ^ (prefixWord ++ tailWord_1671865).sum := by decide
  have hdescent : baseEnd_1671865 < baseStart_1671865 := by decide
  rcases family_descends (prefixWord ++ tailWord_1671865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1671882 : List Nat := [3, 1, 2, 1, 4, 1, 1, 3, 1, 5]
def baseStart_1671882 : Nat := 118140960795 + 1671882 * 2 ^ 59
def prefixEnd_1671882 : Nat := 4983230072969 + 3 ^ 40 * 1671882 * 2
def baseEnd_1671882 : Nat := 572319375733555325124107

theorem tailTrace_1671882 : CollatzResearch.WordTrace tailWord_1671882 prefixEnd_1671882 572319375733555325124107 := by
  unfold tailWord_1671882
  simp only [CollatzResearch.WordTrace]
  refine ⟨15244636532266130889532475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40652364086043015705419933 15244636532266130889532475)
  ·
    refine ⟨22866954798399196334298713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15244636532266130889532475 22866954798399196334298713)
    ·
      refine ⟨17150216098799397250724035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22866954798399196334298713 17150216098799397250724035)
      ·
        refine ⟨25725324148199095876086053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17150216098799397250724035 25725324148199095876086053)
        ·
          refine ⟨4823498277787330476766135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25725324148199095876086053 4823498277787330476766135)
          ·
            refine ⟨7235247416680995715149203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4823498277787330476766135 7235247416680995715149203)
            ·
              refine ⟨10852871125021493572723805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7235247416680995715149203 10852871125021493572723805)
              ·
                refine ⟨4069826671883060089771427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10852871125021493572723805 4069826671883060089771427)
                ·
                  refine ⟨6104740007824590134657141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4069826671883060089771427 6104740007824590134657141)
                  ·
                    refine ⟨572319375733555325124107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6104740007824590134657141 572319375733555325124107)
                    ·
                      rfl

theorem cell22_1671882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 3, 1, 5].length) (baseStart_1671882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1671882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1671882 prefixEnd_1671882 := by exact prefixLift 1671882
  have htrace : WordTrace (prefixWord ++ tailWord_1671882) baseStart_1671882 baseEnd_1671882 := by
    simpa [prefixWord, tailWord_1671882, baseEnd_1671882] using wordTrace_append hprefix tailTrace_1671882
  have hstable : (prefixWord ++ tailWord_1671882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1671882).length < 2 ^ (prefixWord ++ tailWord_1671882).sum := by decide
  have hdescent : baseEnd_1671882 < baseStart_1671882 := by decide
  rcases family_descends (prefixWord ++ tailWord_1671882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1671912 : List Nat := [2, 1, 4, 1, 4, 1, 9]
def baseStart_1671912 : Nat := 118140960795 + 1671912 * 2 ^ 59
def prefixEnd_1671912 : Nat := 4983230072969 + 3 ^ 40 * 1671912 * 2
def baseEnd_1671912 : Nat := 21197394272097972106445

theorem tailTrace_1671912 : CollatzResearch.WordTrace tailWord_1671912 prefixEnd_1671912 21197394272097972106445 := by
  unfold tailWord_1671912
  simp only [CollatzResearch.WordTrace]
  refine ⟨30489820159477919340860995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40653093545970559121147993 30489820159477919340860995)
  ·
    refine ⟨45734730239216879011291493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30489820159477919340860995 45734730239216879011291493)
    ·
      refine ⟨8575261919853164814617155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45734730239216879011291493 8575261919853164814617155)
      ·
        refine ⟨12862892879779747221925733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8575261919853164814617155 12862892879779747221925733)
        ·
          refine ⟨2411792414958702604111075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12862892879779747221925733 2411792414958702604111075)
          ·
            refine ⟨3617688622438053906166613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2411792414958702604111075 3617688622438053906166613)
            ·
              refine ⟨21197394272097972106445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3617688622438053906166613 21197394272097972106445)
              ·
                rfl

theorem cell22_1671912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 9].length) (baseStart_1671912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1671912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1671912 prefixEnd_1671912 := by exact prefixLift 1671912
  have htrace : WordTrace (prefixWord ++ tailWord_1671912) baseStart_1671912 baseEnd_1671912 := by
    simpa [prefixWord, tailWord_1671912, baseEnd_1671912] using wordTrace_append hprefix tailTrace_1671912
  have hstable : (prefixWord ++ tailWord_1671912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1671912).length < 2 ^ (prefixWord ++ tailWord_1671912).sum := by decide
  have hdescent : baseEnd_1671912 < baseStart_1671912 := by decide
  rcases family_descends (prefixWord ++ tailWord_1671912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1671944 : List Nat := [2, 1, 3, 2, 2, 2, 2, 2, 3, 3]
def baseStart_1671944 : Nat := 118140960795 + 1671944 * 2 ^ 59
def prefixEnd_1671944 : Nat := 4983230072969 + 3 ^ 40 * 1671944 * 2
def baseEnd_1671944 : Nat := 572340599600607830073917

theorem tailTrace_1671944 : CollatzResearch.WordTrace tailWord_1671944 prefixEnd_1671944 572340599600607830073917 := by
  unfold tailWord_1671944
  simp only [CollatzResearch.WordTrace]
  refine ⟨30490403727419954073443443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40653871636559938764591257 30490403727419954073443443)
  ·
    refine ⟨45735605591129931110165165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30490403727419954073443443 45735605591129931110165165)
    ·
      refine ⟨17150852096673724166311937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45735605591129931110165165 17150852096673724166311937)
      ·
        refine ⟨12863139072505293124733953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17150852096673724166311937 12863139072505293124733953)
        ·
          refine ⟨9647354304378969843550465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12863139072505293124733953 9647354304378969843550465)
          ·
            refine ⟨7235515728284227382662849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9647354304378969843550465 7235515728284227382662849)
            ·
              refine ⟨5426636796213170536997137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7235515728284227382662849 5426636796213170536997137)
              ·
                refine ⟨4069977597159877902747853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5426636796213170536997137 4069977597159877902747853)
                ·
                  refine ⟨1526241598934954213530445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4069977597159877902747853 1526241598934954213530445)
                  ·
                    refine ⟨572340599600607830073917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1526241598934954213530445 572340599600607830073917)
                    ·
                      rfl

theorem cell22_1671944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 2, 3, 3].length) (baseStart_1671944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1671944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1671944 prefixEnd_1671944 := by exact prefixLift 1671944
  have htrace : WordTrace (prefixWord ++ tailWord_1671944) baseStart_1671944 baseEnd_1671944 := by
    simpa [prefixWord, tailWord_1671944, baseEnd_1671944] using wordTrace_append hprefix tailTrace_1671944
  have hstable : (prefixWord ++ tailWord_1671944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1671944).length < 2 ^ (prefixWord ++ tailWord_1671944).sum := by decide
  have hdescent : baseEnd_1671944 < baseStart_1671944 := by decide
  rcases family_descends (prefixWord ++ tailWord_1671944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1672021 : List Nat := [1, 3, 2, 2, 2, 1, 5, 1, 1, 4]
def baseStart_1672021 : Nat := 118140960795 + 1672021 * 2 ^ 59
def prefixEnd_1672021 : Nat := 4983230072969 + 3 ^ 40 * 1672021 * 2
def baseEnd_1672021 : Nat := 572366958274205295898681

theorem tailTrace_1672021 : CollatzResearch.WordTrace tailWord_1672021 prefixEnd_1672021 572366958274205295898681 := by
  unfold tailWord_1672021
  simp only [CollatzResearch.WordTrace]
  refine ⟨60983615875560950297439917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40655743917040633531626611 60983615875560950297439917)
  ·
    refine ⟨22868855953335356361539969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60983615875560950297439917 22868855953335356361539969)
    ·
      refine ⟨17151641965001517271154977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22868855953335356361539969 17151641965001517271154977)
      ·
        refine ⟨12863731473751137953366233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17151641965001517271154977 12863731473751137953366233)
        ·
          refine ⟨9647798605313353465024675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12863731473751137953366233 9647798605313353465024675)
          ·
            refine ⟨14471697907970030197537013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9647798605313353465024675 14471697907970030197537013)
            ·
              refine ⟨1356721678872190331019095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14471697907970030197537013 1356721678872190331019095)
              ·
                refine ⟨2035082518308285496528643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1356721678872190331019095 2035082518308285496528643)
                ·
                  refine ⟨3052623777462428244792965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2035082518308285496528643 3052623777462428244792965)
                  ·
                    refine ⟨572366958274205295898681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3052623777462428244792965 572366958274205295898681)
                    ·
                      rfl

theorem cell22_1672021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 5, 1, 1, 4].length) (baseStart_1672021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1672021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1672021 prefixEnd_1672021 := by exact prefixLift 1672021
  have htrace : WordTrace (prefixWord ++ tailWord_1672021) baseStart_1672021 baseEnd_1672021 := by
    simpa [prefixWord, tailWord_1672021, baseEnd_1672021] using wordTrace_append hprefix tailTrace_1672021
  have hstable : (prefixWord ++ tailWord_1672021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1672021).length < 2 ^ (prefixWord ++ tailWord_1672021).sum := by decide
  have hdescent : baseEnd_1672021 < baseStart_1672021 := by decide
  rcases family_descends (prefixWord ++ tailWord_1672021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1672036 : List Nat := [2, 3, 1, 1, 4, 2, 1, 4, 4]
def baseStart_1672036 : Nat := 118140960795 + 1672036 * 2 ^ 59
def prefixEnd_1672036 : Nat := 4983230072969 + 3 ^ 40 * 1672036 * 2
def baseEnd_1672036 : Nat := 190790697693583418924545

theorem tailTrace_1672036 : CollatzResearch.WordTrace tailWord_1672036 prefixEnd_1672036 190790697693583418924545 := by
  unfold tailWord_1672036
  simp only [CollatzResearch.WordTrace]
  refine ⟨30492081485253303929617981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40656108647004405239490641 30492081485253303929617981)
  ·
    refine ⟨11434530556969988973606743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30492081485253303929617981 11434530556969988973606743)
    ·
      refine ⟨17151795835454983460410115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11434530556969988973606743 17151795835454983460410115)
      ·
        refine ⟨25727693753182475190615173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17151795835454983460410115 25727693753182475190615173)
        ·
          refine ⟨4823942578721714098240345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25727693753182475190615173 4823942578721714098240345)
          ·
            refine ⟨3617956934041285573680259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4823942578721714098240345 3617956934041285573680259)
            ·
              refine ⟨5426935401061928360520389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3617956934041285573680259 5426935401061928360520389)
              ·
                refine ⟨1017550387699111567597573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5426935401061928360520389 1017550387699111567597573)
                ·
                  refine ⟨190790697693583418924545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1017550387699111567597573 190790697693583418924545)
                  ·
                    rfl

theorem cell22_1672036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 4, 4].length) (baseStart_1672036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1672036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1672036 prefixEnd_1672036 := by exact prefixLift 1672036
  have htrace : WordTrace (prefixWord ++ tailWord_1672036) baseStart_1672036 baseEnd_1672036 := by
    simpa [prefixWord, tailWord_1672036, baseEnd_1672036] using wordTrace_append hprefix tailTrace_1672036
  have hstable : (prefixWord ++ tailWord_1672036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1672036).length < 2 ^ (prefixWord ++ tailWord_1672036).sum := by decide
  have hdescent : baseEnd_1672036 < baseStart_1672036 := by decide
  rcases family_descends (prefixWord ++ tailWord_1672036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1672203 : List Nat := [1, 1, 1, 1, 6, 3, 2, 2, 2, 3]
def baseStart_1672203 : Nat := 118140960795 + 1672203 * 2 ^ 59
def prefixEnd_1672203 : Nat := 4983230072969 + 3 ^ 40 * 1672203 * 2
def baseEnd_1672203 : Nat := 572429260593617487848123

theorem tailTrace_1672203 : CollatzResearch.WordTrace tailWord_1672203 prefixEnd_1672203 572429260593617487848123 := by
  unfold tailWord_1672203
  simp only [CollatzResearch.WordTrace]
  refine ⟨60990253960901595380565263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40660169307267730253710175 60990253960901595380565263)
  ·
    refine ⟨91485380941352393070847895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60990253960901595380565263 91485380941352393070847895)
    ·
      refine ⟨137228071412028589606271843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91485380941352393070847895 137228071412028589606271843)
      ·
        refine ⟨205842107118042884409407765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137228071412028589606271843 205842107118042884409407765)
        ·
          refine ⟨9648848771158260206690989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 205842107118042884409407765 9648848771158260206690989)
          ·
            refine ⟨3618318289184347577509121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9648848771158260206690989 3618318289184347577509121)
            ·
              refine ⟨2713738716888260683131841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3618318289184347577509121 2713738716888260683131841)
              ·
                refine ⟨2035304037666195512348881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2713738716888260683131841 2035304037666195512348881)
                ·
                  refine ⟨1526478028249646634261661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2035304037666195512348881 1526478028249646634261661)
                  ·
                    refine ⟨572429260593617487848123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1526478028249646634261661 572429260593617487848123)
                    ·
                      rfl

theorem cell22_1672203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 2, 2, 2, 3].length) (baseStart_1672203 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1672203 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1672203 prefixEnd_1672203 := by exact prefixLift 1672203
  have htrace : WordTrace (prefixWord ++ tailWord_1672203) baseStart_1672203 baseEnd_1672203 := by
    simpa [prefixWord, tailWord_1672203, baseEnd_1672203] using wordTrace_append hprefix tailTrace_1672203
  have hstable : (prefixWord ++ tailWord_1672203).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1672203).length < 2 ^ (prefixWord ++ tailWord_1672203).sum := by decide
  have hdescent : baseEnd_1672203 < baseStart_1672203 := by decide
  rcases family_descends (prefixWord ++ tailWord_1672203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1672216 : List Nat := [2, 1, 2, 3, 2, 4, 1, 7]
def baseStart_1672216 : Nat := 118140960795 + 1672216 * 2 ^ 59
def prefixEnd_1672216 : Nat := 4983230072969 + 3 ^ 40 * 1672216 * 2
def baseEnd_1672216 : Nat := 63603745639921087474787

theorem tailTrace_1672216 : CollatzResearch.WordTrace tailWord_1672216 prefixEnd_1672216 63603745639921087474787 := by
  unfold tailWord_1672216
  simp only [CollatzResearch.WordTrace]
  refine ⟨30495364054927249300394251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40660485406569665733859001 30495364054927249300394251)
  ·
    refine ⟨45743046082390873950591377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30495364054927249300394251 45743046082390873950591377)
    ·
      refine ⟨34307284561793155462943533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45743046082390873950591377 34307284561793155462943533)
      ·
        refine ⟨12865231710672433298603825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34307284561793155462943533 12865231710672433298603825)
        ·
          refine ⟨9648923783004324973952869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12865231710672433298603825 9648923783004324973952869)
          ·
            refine ⟨1809173209313310932616163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9648923783004324973952869 1809173209313310932616163)
            ·
              refine ⟨2713759813969966398924245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1809173209313310932616163 2713759813969966398924245)
              ·
                refine ⟨63603745639921087474787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2713759813969966398924245 63603745639921087474787)
                ·
                  rfl

theorem cell22_1672216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 1, 7].length) (baseStart_1672216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1672216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1672216 prefixEnd_1672216 := by exact prefixLift 1672216
  have htrace : WordTrace (prefixWord ++ tailWord_1672216) baseStart_1672216 baseEnd_1672216 := by
    simpa [prefixWord, tailWord_1672216, baseEnd_1672216] using wordTrace_append hprefix tailTrace_1672216
  have hstable : (prefixWord ++ tailWord_1672216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1672216).length < 2 ^ (prefixWord ++ tailWord_1672216).sum := by decide
  have hdescent : baseEnd_1672216 < baseStart_1672216 := by decide
  rcases family_descends (prefixWord ++ tailWord_1672216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1672229 : List Nat := [1, 3, 1, 2, 2, 2, 1, 2, 2, 6]
def baseStart_1672229 : Nat := 118140960795 + 1672229 * 2 ^ 59
def prefixEnd_1672229 : Nat := 4983230072969 + 3 ^ 40 * 1672229 * 2
def baseEnd_1672229 : Nat := 572438160924962086698043

theorem tailTrace_1672229 : CollatzResearch.WordTrace tailWord_1672229 prefixEnd_1672229 572438160924962086698043 := by
  unfold tailWord_1672229
  simp only [CollatzResearch.WordTrace]
  refine ⟨60991202258807401821011741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40660801505871601214007827 60991202258807401821011741)
  ·
    refine ⟨22871700847052775682879403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60991202258807401821011741 22871700847052775682879403)
    ·
      refine ⟨34307551270579163524319105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22871700847052775682879403 34307551270579163524319105)
      ·
        refine ⟨25730663452934372643239329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34307551270579163524319105 25730663452934372643239329)
        ·
          refine ⟨19297997589700779482429497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25730663452934372643239329 19297997589700779482429497)
          ·
            refine ⟨14473498192275584611822123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19297997589700779482429497 14473498192275584611822123)
            ·
              refine ⟨21710247288413376917733185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14473498192275584611822123 21710247288413376917733185)
              ·
                refine ⟨16282685466310032688299889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21710247288413376917733185 16282685466310032688299889)
                ·
                  refine ⟨12212014099732524516224917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16282685466310032688299889 12212014099732524516224917)
                  ·
                    refine ⟨572438160924962086698043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12212014099732524516224917 572438160924962086698043)
                    ·
                      rfl

theorem cell22_1672229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 2, 2, 6].length) (baseStart_1672229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1672229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1672229 prefixEnd_1672229 := by exact prefixLift 1672229
  have htrace : WordTrace (prefixWord ++ tailWord_1672229) baseStart_1672229 baseEnd_1672229 := by
    simpa [prefixWord, tailWord_1672229, baseEnd_1672229] using wordTrace_append hprefix tailTrace_1672229
  have hstable : (prefixWord ++ tailWord_1672229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1672229).length < 2 ^ (prefixWord ++ tailWord_1672229).sum := by decide
  have hdescent : baseEnd_1672229 < baseStart_1672229 := by decide
  rcases family_descends (prefixWord ++ tailWord_1672229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1672259 : List Nat := [1, 1, 1, 3, 1, 2, 3, 1, 4, 5]
def baseStart_1672259 : Nat := 118140960795 + 1672259 * 2 ^ 59
def prefixEnd_1672259 : Nat := 4983230072969 + 3 ^ 40 * 1672259 * 2
def baseEnd_1672259 : Nat := 572448430538052008447951

theorem tailTrace_1672259 : CollatzResearch.WordTrace tailWord_1672259 prefixEnd_1672259 572448430538052008447951 := by
  unfold tailWord_1672259
  simp only [CollatzResearch.WordTrace]
  refine ⟨60992296448698716944603831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40661530965799144629735887 60992296448698716944603831)
  ·
    refine ⟨91488444673048075416905747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60992296448698716944603831 91488444673048075416905747)
    ·
      refine ⟨137232667009572113125358621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91488444673048075416905747 137232667009572113125358621)
      ·
        refine ⟨51462250128589542422009483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137232667009572113125358621 51462250128589542422009483)
        ·
          refine ⟨77193375192884313633014225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51462250128589542422009483 77193375192884313633014225)
          ·
            refine ⟨57895031394663235224760669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77193375192884313633014225 57895031394663235224760669)
            ·
              refine ⟨21710636772998713209285251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57895031394663235224760669 21710636772998713209285251)
              ·
                refine ⟨32565955159498069813927877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21710636772998713209285251 32565955159498069813927877)
                ·
                  refine ⟨6106116592405888090111477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32565955159498069813927877 6106116592405888090111477)
                  ·
                    refine ⟨572448430538052008447951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6106116592405888090111477 572448430538052008447951)
                    ·
                      rfl

theorem cell22_1672259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 1, 4, 5].length) (baseStart_1672259 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1672259 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1672259 prefixEnd_1672259 := by exact prefixLift 1672259
  have htrace : WordTrace (prefixWord ++ tailWord_1672259) baseStart_1672259 baseEnd_1672259 := by
    simpa [prefixWord, tailWord_1672259, baseEnd_1672259] using wordTrace_append hprefix tailTrace_1672259
  have hstable : (prefixWord ++ tailWord_1672259).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1672259).length < 2 ^ (prefixWord ++ tailWord_1672259).sum := by decide
  have hdescent : baseEnd_1672259 < baseStart_1672259 := by decide
  rcases family_descends (prefixWord ++ tailWord_1672259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1672261 : List Nat := [1, 3, 1, 1, 1, 3, 5, 2, 5]
def baseStart_1672261 : Nat := 118140960795 + 1672261 * 2 ^ 59
def prefixEnd_1672261 : Nat := 4983230072969 + 3 ^ 40 * 1672261 * 2
def baseEnd_1672261 : Nat := 190816371726308223299315

theorem tailTrace_1672261 : CollatzResearch.WordTrace tailWord_1672261 prefixEnd_1672261 190816371726308223299315 := by
  unfold tailWord_1672261
  simp only [CollatzResearch.WordTrace]
  refine ⟨60992369394691471286176637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40661579596460980857451091 60992369394691471286176637)
  ·
    refine ⟨22872138523009301732316239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60992369394691471286176637 22872138523009301732316239)
    ·
      refine ⟨34308207784513952598474359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22872138523009301732316239 34308207784513952598474359)
      ·
        refine ⟨51462311676770928897711539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34308207784513952598474359 51462311676770928897711539)
        ·
          refine ⟨77193467515156393346567309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51462311676770928897711539 77193467515156393346567309)
          ·
            refine ⟨28947550318183647504962741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77193467515156393346567309 28947550318183647504962741)
            ·
              refine ⟨2713832842329716953590257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28947550318183647504962741 2713832842329716953590257)
              ·
                refine ⟨2035374631747287715192693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2713832842329716953590257 2035374631747287715192693)
                ·
                  refine ⟨190816371726308223299315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2035374631747287715192693 190816371726308223299315)
                  ·
                    rfl

theorem cell22_1672261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 5, 2, 5].length) (baseStart_1672261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1672261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1672261 prefixEnd_1672261 := by exact prefixLift 1672261
  have htrace : WordTrace (prefixWord ++ tailWord_1672261) baseStart_1672261 baseEnd_1672261 := by
    simpa [prefixWord, tailWord_1672261, baseEnd_1672261] using wordTrace_append hprefix tailTrace_1672261
  have hstable : (prefixWord ++ tailWord_1672261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1672261).length < 2 ^ (prefixWord ++ tailWord_1672261).sum := by decide
  have hdescent : baseEnd_1672261 < baseStart_1672261 := by decide
  rcases family_descends (prefixWord ++ tailWord_1672261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1672276 : List Nat := [2, 4, 1, 1, 1, 1, 4, 1, 2, 5]
def baseStart_1672276 : Nat := 118140960795 + 1672276 * 2 ^ 59
def prefixEnd_1672276 : Nat := 4983230072969 + 3 ^ 40 * 1672276 * 2
def baseEnd_1672276 : Nat := 572454249985469630772899

theorem tailTrace_1672276 : CollatzResearch.WordTrace tailWord_1672276 prefixEnd_1672276 572454249985469630772899 := by
  unfold tailWord_1672276
  simp only [CollatzResearch.WordTrace]
  refine ⟨30496458244818564423986341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40661944326424752565315121 30496458244818564423986341)
  ·
    refine ⟨5718085920903480829497439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30496458244818564423986341 5718085920903480829497439)
    ·
      refine ⟨8577128881355221244246159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5718085920903480829497439 8577128881355221244246159)
      ·
        refine ⟨12865693322032831866369239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8577128881355221244246159 12865693322032831866369239)
        ·
          refine ⟨19298539983049247799553859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12865693322032831866369239 19298539983049247799553859)
          ·
            refine ⟨28947809974573871699330789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19298539983049247799553859 28947809974573871699330789)
            ·
              refine ⟨5427714370232600943624523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28947809974573871699330789 5427714370232600943624523)
              ·
                refine ⟨8141571555348901415436785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5427714370232600943624523 8141571555348901415436785)
                ·
                  refine ⟨6106178666511676061577589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8141571555348901415436785 6106178666511676061577589)
                  ·
                    refine ⟨572454249985469630772899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6106178666511676061577589 572454249985469630772899)
                    ·
                      rfl

theorem cell22_1672276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 1, 2, 5].length) (baseStart_1672276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1672276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1672276 prefixEnd_1672276 := by exact prefixLift 1672276
  have htrace : WordTrace (prefixWord ++ tailWord_1672276) baseStart_1672276 baseEnd_1672276 := by
    simpa [prefixWord, tailWord_1672276, baseEnd_1672276] using wordTrace_append hprefix tailTrace_1672276
  have hstable : (prefixWord ++ tailWord_1672276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1672276).length < 2 ^ (prefixWord ++ tailWord_1672276).sum := by decide
  have hdescent : baseEnd_1672276 < baseStart_1672276 := by decide
  rcases family_descends (prefixWord ++ tailWord_1672276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1672319 : List Nat := [1, 1, 2, 2, 1, 1, 1, 1, 2, 10]
def baseStart_1672319 : Nat := 118140960795 + 1672319 * 2 ^ 59
def prefixEnd_1672319 : Nat := 4983230072969 + 3 ^ 40 * 1672319 * 2
def baseEnd_1672319 : Nat := 572468969764231851947767

theorem tailTrace_1672319 : CollatzResearch.WordTrace tailWord_1672319 prefixEnd_1672319 572468969764231851947767 := by
  unfold tailWord_1672319
  simp only [CollatzResearch.WordTrace]
  refine ⟨60994484828481347191788011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40662989885654231461192007 60994484828481347191788011)
  ·
    refine ⟨91491727242722020787682017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60994484828481347191788011 91491727242722020787682017)
    ·
      refine ⟨68618795432041515590761513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91491727242722020787682017 68618795432041515590761513)
      ·
        refine ⟨51464096574031136693071135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68618795432041515590761513 51464096574031136693071135)
        ·
          refine ⟨77196144861046705039606703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51464096574031136693071135 77196144861046705039606703)
          ·
            refine ⟨115794217291570057559410055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77196144861046705039606703 115794217291570057559410055)
            ·
              refine ⟨173691325937355086339115083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115794217291570057559410055 173691325937355086339115083)
              ·
                refine ⟨260536988906032629508672625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 173691325937355086339115083 260536988906032629508672625)
                ·
                  refine ⟨195402741679524472131504469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 260536988906032629508672625 195402741679524472131504469)
                  ·
                    refine ⟨572468969764231851947767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 195402741679524472131504469 572468969764231851947767)
                    ·
                      rfl

theorem cell22_1672319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 10].length) (baseStart_1672319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1672319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1672319 prefixEnd_1672319 := by exact prefixLift 1672319
  have htrace : WordTrace (prefixWord ++ tailWord_1672319) baseStart_1672319 baseEnd_1672319 := by
    simpa [prefixWord, tailWord_1672319, baseEnd_1672319] using wordTrace_append hprefix tailTrace_1672319
  have hstable : (prefixWord ++ tailWord_1672319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1672319).length < 2 ^ (prefixWord ++ tailWord_1672319).sum := by decide
  have hdescent : baseEnd_1672319 < baseStart_1672319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1672319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1672353 : List Nat := [1, 2, 3, 3, 1, 1, 4, 1, 2, 4]
def baseStart_1672353 : Nat := 118140960795 + 1672353 * 2 ^ 59
def prefixEnd_1672353 : Nat := 4983230072969 + 3 ^ 40 * 1672353 * 2
def baseEnd_1672353 : Nat := 572480608659067096597663

theorem tailTrace_1672353 : CollatzResearch.WordTrace tailWord_1672353 prefixEnd_1672353 572480608659067096597663 := by
  unfold tailWord_1672353
  simp only [CollatzResearch.WordTrace]
  refine ⟨60995724910358170998525713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40663816606905447332350475 60995724910358170998525713)
  ·
    refine ⟨45746793682768628248894285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60995724910358170998525713 45746793682768628248894285)
    ·
      refine ⟨17155047631038235593335357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45746793682768628248894285 17155047631038235593335357)
      ·
        refine ⟨6433142861639338347500759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17155047631038235593335357 6433142861639338347500759)
        ·
          refine ⟨9649714292459007521251139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6433142861639338347500759 9649714292459007521251139)
          ·
            refine ⟨14474571438688511281876709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9649714292459007521251139 14474571438688511281876709)
            ·
              refine ⟨2713982144754095865351883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14474571438688511281876709 2713982144754095865351883)
              ·
                refine ⟨4070973217131143798027825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2713982144754095865351883 4070973217131143798027825)
                ·
                  refine ⟨3053229912848357848520869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4070973217131143798027825 3053229912848357848520869)
                  ·
                    refine ⟨572480608659067096597663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3053229912848357848520869 572480608659067096597663)
                    ·
                      rfl

theorem cell22_1672353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 4, 1, 2, 4].length) (baseStart_1672353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1672353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1672353 prefixEnd_1672353 := by exact prefixLift 1672353
  have htrace : WordTrace (prefixWord ++ tailWord_1672353) baseStart_1672353 baseEnd_1672353 := by
    simpa [prefixWord, tailWord_1672353, baseEnd_1672353] using wordTrace_append hprefix tailTrace_1672353
  have hstable : (prefixWord ++ tailWord_1672353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1672353).length < 2 ^ (prefixWord ++ tailWord_1672353).sum := by decide
  have hdescent : baseEnd_1672353 < baseStart_1672353 := by decide
  rcases family_descends (prefixWord ++ tailWord_1672353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1672374 : List Nat := [5, 1, 3, 2, 1, 1, 1, 4, 4]
def baseStart_1672374 : Nat := 118140960795 + 1672374 * 2 ^ 59
def prefixEnd_1672374 : Nat := 4983230072969 + 3 ^ 40 * 1672374 * 2
def baseEnd_1672374 : Nat := 190829265796076680607533

theorem tailTrace_1672374 : CollatzResearch.WordTrace tailWord_1672374 prefixEnd_1672374 190829265796076680607533 := by
  unfold tailWord_1672374
  simp only [CollatzResearch.WordTrace]
  refine ⟨3812280677705130724065011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40664327228854727723360117 3812280677705130724065011)
  ·
    refine ⟨5718421016557696086097517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3812280677705130724065011 5718421016557696086097517)
    ·
      refine ⟨2144407881209136032286569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5718421016557696086097517 2144407881209136032286569)
      ·
        refine ⟨1608305910906852024214927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2144407881209136032286569 1608305910906852024214927)
        ·
          refine ⟨2412458866360278036322391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1608305910906852024214927 2412458866360278036322391)
          ·
            refine ⟨3618688299540417054483587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2412458866360278036322391 3618688299540417054483587)
            ·
              refine ⟨5428032449310625581725381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3618688299540417054483587 5428032449310625581725381)
              ·
                refine ⟨1017756084245742296573509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5428032449310625581725381 1017756084245742296573509)
                ·
                  refine ⟨190829265796076680607533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1017756084245742296573509 190829265796076680607533)
                  ·
                    rfl

theorem cell22_1672374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 4, 4].length) (baseStart_1672374 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1672374 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1672374 prefixEnd_1672374 := by exact prefixLift 1672374
  have htrace : WordTrace (prefixWord ++ tailWord_1672374) baseStart_1672374 baseEnd_1672374 := by
    simpa [prefixWord, tailWord_1672374, baseEnd_1672374] using wordTrace_append hprefix tailTrace_1672374
  have hstable : (prefixWord ++ tailWord_1672374).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1672374).length < 2 ^ (prefixWord ++ tailWord_1672374).sum := by decide
  have hdescent : baseEnd_1672374 < baseStart_1672374 := by decide
  rcases family_descends (prefixWord ++ tailWord_1672374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1672381 : List Nat := [1, 4, 1, 2, 1, 1, 3, 1, 2, 6]
def baseStart_1672381 : Nat := 118140960795 + 1672381 * 2 ^ 59
def prefixEnd_1672381 : Nat := 4983230072969 + 3 ^ 40 * 1672381 * 2
def baseEnd_1672381 : Nat := 572490193631284356897577

theorem tailTrace_1672381 : CollatzResearch.WordTrace tailWord_1672381 prefixEnd_1672381 572490193631284356897577 := by
  unfold tailWord_1672381
  simp only [CollatzResearch.WordTrace]
  refine ⟨60996746154256731780544997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40664497436171154520363331 60996746154256731780544997)
  ·
    refine ⟨11436889903923137208852187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60996746154256731780544997 11436889903923137208852187)
    ·
      refine ⟨17155334855884705813278281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11436889903923137208852187 17155334855884705813278281)
      ·
        refine ⟨12866501141913529359958711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17155334855884705813278281 12866501141913529359958711)
        ·
          refine ⟨19299751712870294039938067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12866501141913529359958711 19299751712870294039938067)
          ·
            refine ⟨28949627569305441059907101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19299751712870294039938067 28949627569305441059907101)
            ·
              refine ⟨10856110338489540397465163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28949627569305441059907101 10856110338489540397465163)
              ·
                refine ⟨16284165507734310596197745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10856110338489540397465163 16284165507734310596197745)
                ·
                  refine ⟨12213124130800732947148309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16284165507734310596197745 12213124130800732947148309)
                  ·
                    refine ⟨572490193631284356897577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12213124130800732947148309 572490193631284356897577)
                    ·
                      rfl

theorem cell22_1672381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 1, 2, 6].length) (baseStart_1672381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1672381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1672381 prefixEnd_1672381 := by exact prefixLift 1672381
  have htrace : WordTrace (prefixWord ++ tailWord_1672381) baseStart_1672381 baseEnd_1672381 := by
    simpa [prefixWord, tailWord_1672381, baseEnd_1672381] using wordTrace_append hprefix tailTrace_1672381
  have hstable : (prefixWord ++ tailWord_1672381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1672381).length < 2 ^ (prefixWord ++ tailWord_1672381).sum := by decide
  have hdescent : baseEnd_1672381 < baseStart_1672381 := by decide
  rcases family_descends (prefixWord ++ tailWord_1672381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1672385 : List Nat := [1, 2, 6, 1, 1, 3, 1, 7]
def baseStart_1672385 : Nat := 118140960795 + 1672385 * 2 ^ 59
def prefixEnd_1672385 : Nat := 4983230072969 + 3 ^ 40 * 1672385 * 2
def baseEnd_1672385 : Nat := 63610173657003297755285

theorem tailTrace_1672385 : CollatzResearch.WordTrace tailWord_1672385 prefixEnd_1672385 63610173657003297755285 := by
  unfold tailWord_1672385
  simp only [CollatzResearch.WordTrace]
  refine ⟨60996892046242240463690609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40664594697494826975793739 60996892046242240463690609)
  ·
    refine ⟨45747669034681680347767957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60996892046242240463690609 45747669034681680347767957)
    ·
      refine ⟨2144421986000703766301623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 45747669034681680347767957 2144421986000703766301623)
      ·
        refine ⟨3216632979001055649452435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2144421986000703766301623 3216632979001055649452435)
        ·
          refine ⟨4824949468501583474178653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3216632979001055649452435 4824949468501583474178653)
          ·
            refine ⟨1809356050688093802816995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4824949468501583474178653 1809356050688093802816995)
            ·
              refine ⟨2714034076032140704225493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1809356050688093802816995 2714034076032140704225493)
              ·
                refine ⟨63610173657003297755285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2714034076032140704225493 63610173657003297755285)
                ·
                  rfl

theorem cell22_1672385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 1, 7].length) (baseStart_1672385 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1672385 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1672385 prefixEnd_1672385 := by exact prefixLift 1672385
  have htrace : WordTrace (prefixWord ++ tailWord_1672385) baseStart_1672385 baseEnd_1672385 := by
    simpa [prefixWord, tailWord_1672385, baseEnd_1672385] using wordTrace_append hprefix tailTrace_1672385
  have hstable : (prefixWord ++ tailWord_1672385).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1672385).length < 2 ^ (prefixWord ++ tailWord_1672385).sum := by decide
  have hdescent : baseEnd_1672385 < baseStart_1672385 := by decide
  rcases family_descends (prefixWord ++ tailWord_1672385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1672404 : List Nat := [2, 4, 1, 4, 2, 1, 1, 1, 2, 4]
def baseStart_1672404 : Nat := 118140960795 + 1672404 * 2 ^ 59
def prefixEnd_1672404 : Nat := 4983230072969 + 3 ^ 40 * 1672404 * 2
def baseEnd_1672404 : Nat := 572498067001319963572507

theorem tailTrace_1672404 : CollatzResearch.WordTrace tailWord_1672404 prefixEnd_1672404 572498067001319963572507 := by
  unfold tailWord_1672404
  simp only [CollatzResearch.WordTrace]
  refine ⟨30498792516586703354316133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40665056688782271139088177 30498792516586703354316133)
  ·
    refine ⟨5718523596860006878934275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30498792516586703354316133 5718523596860006878934275)
    ·
      refine ⟨8577785395290010318401413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5718523596860006878934275 8577785395290010318401413)
      ·
        refine ⟨1608334761616876934700265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8577785395290010318401413 1608334761616876934700265)
        ·
          refine ⟨1206251071212657701025199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1608334761616876934700265 1206251071212657701025199)
          ·
            refine ⟨1809376606818986551537799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1206251071212657701025199 1809376606818986551537799)
            ·
              refine ⟨2714064910228479827306699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1809376606818986551537799 2714064910228479827306699)
              ·
                refine ⟨4071097365342719740960049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2714064910228479827306699 4071097365342719740960049)
                ·
                  refine ⟨3053323024007039805720037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4071097365342719740960049 3053323024007039805720037)
                  ·
                    refine ⟨572498067001319963572507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3053323024007039805720037 572498067001319963572507)
                    ·
                      rfl

theorem cell22_1672404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 1, 1, 2, 4].length) (baseStart_1672404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1672404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1672404 prefixEnd_1672404 := by exact prefixLift 1672404
  have htrace : WordTrace (prefixWord ++ tailWord_1672404) baseStart_1672404 baseEnd_1672404 := by
    simpa [prefixWord, tailWord_1672404, baseEnd_1672404] using wordTrace_append hprefix tailTrace_1672404
  have hstable : (prefixWord ++ tailWord_1672404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1672404).length < 2 ^ (prefixWord ++ tailWord_1672404).sum := by decide
  have hdescent : baseEnd_1672404 < baseStart_1672404 := by decide
  rcases family_descends (prefixWord ++ tailWord_1672404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1672417 : List Nat := [1, 2, 3, 1, 3, 3, 2, 3, 1, 3]
def baseStart_1672417 : Nat := 118140960795 + 1672417 * 2 ^ 59
def prefixEnd_1672417 : Nat := 4983230072969 + 3 ^ 40 * 1672417 * 2
def baseEnd_1672417 : Nat := 572502517166992262997467

theorem tailTrace_1672417 : CollatzResearch.WordTrace tailWord_1672417 prefixEnd_1672417 572502517166992262997467 := by
  unfold tailWord_1672417
  simp only [CollatzResearch.WordTrace]
  refine ⟨60998059182126309928855505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40665372788084206619237003 60998059182126309928855505)
  ·
    refine ⟨45748544386594732446641629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60998059182126309928855505 45748544386594732446641629)
    ·
      refine ⟨17155704144973024667490611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45748544386594732446641629 17155704144973024667490611)
      ·
        refine ⟨25733556217459537001235917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17155704144973024667490611 25733556217459537001235917)
        ·
          refine ⟨9650083581547326375463469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25733556217459537001235917 9650083581547326375463469)
          ·
            refine ⟨3618781343080247390798801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9650083581547326375463469 3618781343080247390798801)
            ·
              refine ⟨2714086007310185543099101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3618781343080247390798801 2714086007310185543099101)
              ·
                refine ⟨1017782252741319578662163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2714086007310185543099101 1017782252741319578662163)
                ·
                  refine ⟨1526673379111979367993245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1017782252741319578662163 1526673379111979367993245)
                  ·
                    refine ⟨572502517166992262997467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1526673379111979367993245 572502517166992262997467)
                    ·
                      rfl

theorem cell22_1672417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 2, 3, 1, 3].length) (baseStart_1672417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1672417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1672417 prefixEnd_1672417 := by exact prefixLift 1672417
  have htrace : WordTrace (prefixWord ++ tailWord_1672417) baseStart_1672417 baseEnd_1672417 := by
    simpa [prefixWord, tailWord_1672417, baseEnd_1672417] using wordTrace_append hprefix tailTrace_1672417
  have hstable : (prefixWord ++ tailWord_1672417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1672417).length < 2 ^ (prefixWord ++ tailWord_1672417).sum := by decide
  have hdescent : baseEnd_1672417 < baseStart_1672417 := by decide
  rcases family_descends (prefixWord ++ tailWord_1672417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1672460 : List Nat := [2, 2, 1, 2, 2, 4, 2, 2, 1, 4]
def baseStart_1672460 : Nat := 118140960795 + 1672460 * 2 ^ 59
def prefixEnd_1672460 : Nat := 4983230072969 + 3 ^ 40 * 1672460 * 2
def baseEnd_1672460 : Nat := 572517236945754484172335

theorem tailTrace_1672460 : CollatzResearch.WordTrace tailWord_1672460 prefixEnd_1672460 572517236945754484172335 := by
  unfold tailWord_1672460
  simp only [CollatzResearch.WordTrace]
  refine ⟨30499813760485264136335417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40666418347313685515113889 30499813760485264136335417)
  ·
    refine ⟨22874860320363948102251563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30499813760485264136335417 22874860320363948102251563)
    ·
      refine ⟨34312290480545922153377345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22874860320363948102251563 34312290480545922153377345)
      ·
        refine ⟨25734217860409441615033009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34312290480545922153377345 25734217860409441615033009)
        ·
          refine ⟨19300663395307081211274757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25734217860409441615033009 19300663395307081211274757)
          ·
            refine ⟨3618874386620077727114017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19300663395307081211274757 3618874386620077727114017)
            ·
              refine ⟨2714155789965058295335513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3618874386620077727114017 2714155789965058295335513)
              ·
                refine ⟨2035616842473793721501635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2714155789965058295335513 2035616842473793721501635)
                ·
                  refine ⟨3053425263710690582252453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2035616842473793721501635 3053425263710690582252453)
                  ·
                    refine ⟨572517236945754484172335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3053425263710690582252453 572517236945754484172335)
                    ·
                      rfl

theorem cell22_1672460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 2, 2, 1, 4].length) (baseStart_1672460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1672460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1672460 prefixEnd_1672460 := by exact prefixLift 1672460
  have htrace : WordTrace (prefixWord ++ tailWord_1672460) baseStart_1672460 baseEnd_1672460 := by
    simpa [prefixWord, tailWord_1672460, baseEnd_1672460] using wordTrace_append hprefix tailTrace_1672460
  have hstable : (prefixWord ++ tailWord_1672460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1672460).length < 2 ^ (prefixWord ++ tailWord_1672460).sum := by decide
  have hdescent : baseEnd_1672460 < baseStart_1672460 := by decide
  rcases family_descends (prefixWord ++ tailWord_1672460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1672610 : List Nat := [3, 3, 1, 2, 1, 2, 1, 3, 6]
def baseStart_1672610 : Nat := 118140960795 + 1672610 * 2 ^ 59
def prefixEnd_1672610 : Nat := 4983230072969 + 3 ^ 40 * 1672610 * 2
def baseEnd_1672610 : Nat := 190856195003734697640625

theorem tailTrace_1672610 : CollatzResearch.WordTrace tailWord_1672610 prefixEnd_1672610 190856195003734697640625 := by
  unfold tailWord_1672610
  simp only [CollatzResearch.WordTrace]
  refine ⟨15251274617606775972657821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40670065646951402593754189 15251274617606775972657821)
  ·
    refine ⟨5719227981602540989746683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15251274617606775972657821 5719227981602540989746683)
    ·
      refine ⟨8578841972403811484620025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5719227981602540989746683 8578841972403811484620025)
      ·
        refine ⟨6434131479302858613465019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8578841972403811484620025 6434131479302858613465019)
        ·
          refine ⟨9651197218954287920197529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6434131479302858613465019 9651197218954287920197529)
          ·
            refine ⟨7238397914215715940148147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9651197218954287920197529 7238397914215715940148147)
            ·
              refine ⟨10857596871323573910222221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7238397914215715940148147 10857596871323573910222221)
              ·
                refine ⟨4071598826746340216333333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10857596871323573910222221 4071598826746340216333333)
                ·
                  refine ⟨190856195003734697640625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4071598826746340216333333 190856195003734697640625)
                  ·
                    rfl

theorem cell22_1672610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 3, 6].length) (baseStart_1672610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1672610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1672610 prefixEnd_1672610 := by exact prefixLift 1672610
  have htrace : WordTrace (prefixWord ++ tailWord_1672610) baseStart_1672610 baseEnd_1672610 := by
    simpa [prefixWord, tailWord_1672610, baseEnd_1672610] using wordTrace_append hprefix tailTrace_1672610
  have hstable : (prefixWord ++ tailWord_1672610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1672610).length < 2 ^ (prefixWord ++ tailWord_1672610).sum := by decide
  have hdescent : baseEnd_1672610 < baseStart_1672610 := by decide
  rcases family_descends (prefixWord ++ tailWord_1672610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1672644 : List Nat := [2, 3, 3, 2, 1, 1, 3, 3, 4]
def baseStart_1672644 : Nat := 118140960795 + 1672644 * 2 ^ 59
def prefixEnd_1672644 : Nat := 4983230072969 + 3 ^ 40 * 1672644 * 2
def baseEnd_1672644 : Nat := 190860074635346445857257

theorem tailTrace_1672644 : CollatzResearch.WordTrace tailWord_1672644 prefixEnd_1672644 190860074635346445857257 := by
  unfold tailWord_1672644
  simp only [CollatzResearch.WordTrace]
  refine ⟨30503169276151963848684493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40670892368202618464912657 30503169276151963848684493)
  ·
    refine ⟨11438688478556986443256685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30503169276151963848684493 11438688478556986443256685)
    ·
      refine ⟨4289508179458869916221257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11438688478556986443256685 4289508179458869916221257)
      ·
        refine ⟨3217131134594152437165943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4289508179458869916221257 3217131134594152437165943)
        ·
          refine ⟨4825696701891228655748915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3217131134594152437165943 4825696701891228655748915)
          ·
            refine ⟨7238545052836842983623373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4825696701891228655748915 7238545052836842983623373)
            ·
              refine ⟨2714454394813816118858765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7238545052836842983623373 2714454394813816118858765)
              ·
                refine ⟨1017920398055181044572037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2714454394813816118858765 1017920398055181044572037)
                ·
                  refine ⟨190860074635346445857257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1017920398055181044572037 190860074635346445857257)
                  ·
                    rfl

theorem cell22_1672644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 3, 3, 4].length) (baseStart_1672644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1672644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1672644 prefixEnd_1672644 := by exact prefixLift 1672644
  have htrace : WordTrace (prefixWord ++ tailWord_1672644) baseStart_1672644 baseEnd_1672644 := by
    simpa [prefixWord, tailWord_1672644, baseEnd_1672644] using wordTrace_append hprefix tailTrace_1672644
  have hstable : (prefixWord ++ tailWord_1672644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1672644).length < 2 ^ (prefixWord ++ tailWord_1672644).sum := by decide
  have hdescent : baseEnd_1672644 < baseStart_1672644 := by decide
  rcases family_descends (prefixWord ++ tailWord_1672644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1672683 : List Nat := [1, 1, 1, 1, 2, 3, 2, 2, 9]
def baseStart_1672683 : Nat := 118140960795 + 1672683 * 2 ^ 59
def prefixEnd_1672683 : Nat := 4983230072969 + 3 ^ 40 * 1672683 * 2
def baseEnd_1672683 : Nat := 190864524801018745282217

theorem tailTrace_1672683 : CollatzResearch.WordTrace tailWord_1672683 prefixEnd_1672683 190864524801018745282217 := by
  unfold tailWord_1672683
  simp only [CollatzResearch.WordTrace]
  refine ⟨61007760999162637358038703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40671840666108424905359135 61007760999162637358038703)
  ·
    refine ⟨91511641498743956037058055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61007760999162637358038703 91511641498743956037058055)
    ·
      refine ⟨137267462248115934055587083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91511641498743956037058055 137267462248115934055587083)
      ·
        refine ⟨205901193372173901083380625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137267462248115934055587083 205901193372173901083380625)
        ·
          refine ⟨154425895029130425812535469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 205901193372173901083380625 154425895029130425812535469)
          ·
            refine ⟨57909710635923909679700801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 154425895029130425812535469 57909710635923909679700801)
            ·
              refine ⟨43432282976942932259775601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57909710635923909679700801 43432282976942932259775601)
              ·
                refine ⟨32574212232707199194831701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43432282976942932259775601 32574212232707199194831701)
                ·
                  refine ⟨190864524801018745282217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 32574212232707199194831701 190864524801018745282217)
                  ·
                    rfl

theorem cell22_1672683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 2, 9].length) (baseStart_1672683 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1672683 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1672683 prefixEnd_1672683 := by exact prefixLift 1672683
  have htrace : WordTrace (prefixWord ++ tailWord_1672683) baseStart_1672683 baseEnd_1672683 := by
    simpa [prefixWord, tailWord_1672683, baseEnd_1672683] using wordTrace_append hprefix tailTrace_1672683
  have hstable : (prefixWord ++ tailWord_1672683).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1672683).length < 2 ^ (prefixWord ++ tailWord_1672683).sum := by decide
  have hdescent : baseEnd_1672683 < baseStart_1672683 := by decide
  rcases family_descends (prefixWord ++ tailWord_1672683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1672710 : List Nat := [6, 2, 1, 1, 2, 1, 2, 2, 2, 3]
def baseStart_1672710 : Nat := 118140960795 + 1672710 * 2 ^ 59
def prefixEnd_1672710 : Nat := 4983230072969 + 3 ^ 40 * 1672710 * 2
def baseEnd_1672710 : Nat := 572602817054837165421569

theorem tailTrace_1672710 : CollatzResearch.WordTrace tailWord_1672710 prefixEnd_1672710 572602817054837165421569 := by
  unfold tailWord_1672710
  simp only [CollatzResearch.WordTrace]
  refine ⟨1906523305314525655289737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 40672497180043213979514389 1906523305314525655289737)
  ·
    refine ⟨1429892478985894241467303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1906523305314525655289737 1429892478985894241467303)
    ·
      refine ⟨2144838718478841362200955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1429892478985894241467303 2144838718478841362200955)
      ·
        refine ⟨3217258077718262043301433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2144838718478841362200955 3217258077718262043301433)
        ·
          refine ⟨2412943558288696532476075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3217258077718262043301433 2412943558288696532476075)
          ·
            refine ⟨3619415337433044798714113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2412943558288696532476075 3619415337433044798714113)
            ·
              refine ⟨2714561503074783599035585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3619415337433044798714113 2714561503074783599035585)
              ·
                refine ⟨2035921127306087699276689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2714561503074783599035585 2035921127306087699276689)
                ·
                  refine ⟨1526940845479565774457517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2035921127306087699276689 1526940845479565774457517)
                  ·
                    refine ⟨572602817054837165421569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1526940845479565774457517 572602817054837165421569)
                    ·
                      rfl

theorem cell22_1672710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_1672710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1672710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1672710 prefixEnd_1672710 := by exact prefixLift 1672710
  have htrace : WordTrace (prefixWord ++ tailWord_1672710) baseStart_1672710 baseEnd_1672710 := by
    simpa [prefixWord, tailWord_1672710, baseEnd_1672710] using wordTrace_append hprefix tailTrace_1672710
  have hstable : (prefixWord ++ tailWord_1672710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1672710).length < 2 ^ (prefixWord ++ tailWord_1672710).sum := by decide
  have hdescent : baseEnd_1672710 < baseStart_1672710 := by decide
  rcases family_descends (prefixWord ++ tailWord_1672710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1672764 : List Nat := [2, 2, 2, 2, 4, 1, 1, 3, 1, 4]
def baseStart_1672764 : Nat := 118140960795 + 1672764 * 2 ^ 59
def prefixEnd_1672764 : Nat := 4983230072969 + 3 ^ 40 * 1672764 * 2
def baseEnd_1672764 : Nat := 572621302358399024571403

theorem tailTrace_1672764 : CollatzResearch.WordTrace tailWord_1672764 prefixEnd_1672764 572621302358399024571403 := by
  unfold tailWord_1672764
  simp only [CollatzResearch.WordTrace]
  refine ⟨30505357655934594095868673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40673810207912792127824897 30505357655934594095868673)
  ·
    refine ⟨22879018241950945571901505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30505357655934594095868673 22879018241950945571901505)
    ·
      refine ⟨17159263681463209178926129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22879018241950945571901505 17159263681463209178926129)
      ·
        refine ⟨12869447761097406884194597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17159263681463209178926129 12869447761097406884194597)
        ·
          refine ⟨2413021455205763790786487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12869447761097406884194597 2413021455205763790786487)
          ·
            refine ⟨3619532182808645686179731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2413021455205763790786487 3619532182808645686179731)
            ·
              refine ⟨5429298274212968529269597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3619532182808645686179731 5429298274212968529269597)
              ·
                refine ⟨2035986852829863198476099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5429298274212968529269597 2035986852829863198476099)
                ·
                  refine ⟨3053980279244794797714149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2035986852829863198476099 3053980279244794797714149)
                  ·
                    refine ⟨572621302358399024571403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3053980279244794797714149 572621302358399024571403)
                    ·
                      rfl

theorem cell22_1672764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 3, 1, 4].length) (baseStart_1672764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1672764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1672764 prefixEnd_1672764 := by exact prefixLift 1672764
  have htrace : WordTrace (prefixWord ++ tailWord_1672764) baseStart_1672764 baseEnd_1672764 := by
    simpa [prefixWord, tailWord_1672764, baseEnd_1672764] using wordTrace_append hprefix tailTrace_1672764
  have hstable : (prefixWord ++ tailWord_1672764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1672764).length < 2 ^ (prefixWord ++ tailWord_1672764).sum := by decide
  have hdescent : baseEnd_1672764 < baseStart_1672764 := by decide
  rcases family_descends (prefixWord ++ tailWord_1672764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1672807 : List Nat := [1, 1, 5, 1, 1, 1, 6, 6]
def baseStart_1672807 : Nat := 118140960795 + 1672807 * 2 ^ 59
def prefixEnd_1672807 : Nat := 4983230072969 + 3 ^ 40 * 1672807 * 2
def baseEnd_1672807 : Nat := 63626224681906805082919

theorem tailTrace_1672807 : CollatzResearch.WordTrace tailWord_1672807 prefixEnd_1672807 63626224681906805082919 := by
  unfold tailWord_1672807
  simp only [CollatzResearch.WordTrace]
  refine ⟨61012283650713406535552675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40674855767142271023701783 61012283650713406535552675)
  ·
    refine ⟨91518425476070109803329013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61012283650713406535552675 91518425476070109803329013)
    ·
      refine ⟨8579852388381572794062095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 91518425476070109803329013 8579852388381572794062095)
      ·
        refine ⟨12869778582572359191093143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8579852388381572794062095 12869778582572359191093143)
        ·
          refine ⟨19304667873858538786639715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12869778582572359191093143 19304667873858538786639715)
          ·
            refine ⟨28957001810787808179959573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19304667873858538786639715 28957001810787808179959573)
            ·
              refine ⟨1357359459880678508435605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 28957001810787808179959573 1357359459880678508435605)
              ·
                refine ⟨63626224681906805082919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1357359459880678508435605 63626224681906805082919)
                ·
                  rfl

theorem cell22_1672807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 6, 6].length) (baseStart_1672807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1672807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1672807 prefixEnd_1672807 := by exact prefixLift 1672807
  have htrace : WordTrace (prefixWord ++ tailWord_1672807) baseStart_1672807 baseEnd_1672807 := by
    simpa [prefixWord, tailWord_1672807, baseEnd_1672807] using wordTrace_append hprefix tailTrace_1672807
  have hstable : (prefixWord ++ tailWord_1672807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1672807).length < 2 ^ (prefixWord ++ tailWord_1672807).sum := by decide
  have hdescent : baseEnd_1672807 < baseStart_1672807 := by decide
  rcases family_descends (prefixWord ++ tailWord_1672807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1672813 : List Nat := [1, 5, 1, 1, 5, 1, 1, 3, 4]
def baseStart_1672813 : Nat := 118140960795 + 1672813 * 2 ^ 59
def prefixEnd_1672813 : Nat := 4983230072969 + 3 ^ 40 * 1672813 * 2
def baseEnd_1672813 : Nat := 190879358686593076698751

theorem tailTrace_1672813 : CollatzResearch.WordTrace tailWord_1672813 prefixEnd_1672813 190879358686593076698751 := by
  unfold tailWord_1672813
  simp only [CollatzResearch.WordTrace]
  refine ⟨61012502488691669560271093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40675001659127779706847395 61012502488691669560271093)
  ·
    refine ⟨5719922108314844021275415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 61012502488691669560271093 5719922108314844021275415)
    ·
      refine ⟨8579883162472266031913123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5719922108314844021275415 8579883162472266031913123)
      ·
        refine ⟨12869824743708399047869685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8579883162472266031913123 12869824743708399047869685)
        ·
          refine ⟨1206546069722662410737783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12869824743708399047869685 1206546069722662410737783)
          ·
            refine ⟨1809819104583993616106675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1206546069722662410737783 1809819104583993616106675)
            ·
              refine ⟨2714728656875990424160013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1809819104583993616106675 2714728656875990424160013)
              ·
                refine ⟨1018023246328496409060005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2714728656875990424160013 1018023246328496409060005)
                ·
                  refine ⟨190879358686593076698751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1018023246328496409060005 190879358686593076698751)
                  ·
                    rfl

theorem cell22_1672813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 1, 3, 4].length) (baseStart_1672813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1672813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1672813 prefixEnd_1672813 := by exact prefixLift 1672813
  have htrace : WordTrace (prefixWord ++ tailWord_1672813) baseStart_1672813 baseEnd_1672813 := by
    simpa [prefixWord, tailWord_1672813, baseEnd_1672813] using wordTrace_append hprefix tailTrace_1672813
  have hstable : (prefixWord ++ tailWord_1672813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1672813).length < 2 ^ (prefixWord ++ tailWord_1672813).sum := by decide
  have hdescent : baseEnd_1672813 < baseStart_1672813 := by decide
  rcases family_descends (prefixWord ++ tailWord_1672813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1672839 : List Nat := [1, 1, 4, 2, 1, 3, 3, 1, 3, 3]
def baseStart_1672839 : Nat := 118140960795 + 1672839 * 2 ^ 59
def prefixEnd_1672839 : Nat := 4983230072969 + 3 ^ 40 * 1672839 * 2
def baseEnd_1672839 : Nat := 572646976391123828946173

theorem tailTrace_1672839 : CollatzResearch.WordTrace tailWord_1672839 prefixEnd_1672839 572646976391123828946173 := by
  unfold tailWord_1672839
  simp only [CollatzResearch.WordTrace]
  refine ⟨61013450786597476000717571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40675633857731650667145047 61013450786597476000717571)
  ·
    refine ⟨91520176179896214001076357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61013450786597476000717571 91520176179896214001076357)
    ·
      refine ⟨17160033033730540125201817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91520176179896214001076357 17160033033730540125201817)
      ·
        refine ⟨12870024775297905093901363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17160033033730540125201817 12870024775297905093901363)
        ·
          refine ⟨19305037162946857640852045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12870024775297905093901363 19305037162946857640852045)
          ·
            refine ⟨7239388936105071615319517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19305037162946857640852045 7239388936105071615319517)
            ·
              refine ⟨2714770851039401855744819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7239388936105071615319517 2714770851039401855744819)
              ·
                refine ⟨4072156276559102783617229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2714770851039401855744819 4072156276559102783617229)
                ·
                  refine ⟨1527058603709663543856461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4072156276559102783617229 1527058603709663543856461)
                  ·
                    refine ⟨572646976391123828946173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1527058603709663543856461 572646976391123828946173)
                    ·
                      rfl

theorem cell22_1672839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 3, 1, 3, 3].length) (baseStart_1672839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1672839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1672839 prefixEnd_1672839 := by exact prefixLift 1672839
  have htrace : WordTrace (prefixWord ++ tailWord_1672839) baseStart_1672839 baseEnd_1672839 := by
    simpa [prefixWord, tailWord_1672839, baseEnd_1672839] using wordTrace_append hprefix tailTrace_1672839
  have hstable : (prefixWord ++ tailWord_1672839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1672839).length < 2 ^ (prefixWord ++ tailWord_1672839).sum := by decide
  have hdescent : baseEnd_1672839 < baseStart_1672839 := by decide
  rcases family_descends (prefixWord ++ tailWord_1672839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1672886 : List Nat := [5, 1, 3, 1, 1, 1, 1, 4, 5]
def baseStart_1672886 : Nat := 118140960795 + 1672886 * 2 ^ 59
def prefixEnd_1672886 : Nat := 4983230072969 + 3 ^ 40 * 1672886 * 2
def baseEnd_1672886 : Nat := 190887688483877124340343

theorem tailTrace_1672886 : CollatzResearch.WordTrace tailWord_1672886 prefixEnd_1672886 190887688483877124340343 := by
  unfold tailWord_1672886
  simp only [CollatzResearch.WordTrace]
  refine ⟨3813447813589200189229907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40676776678284802018452341 3813447813589200189229907)
  ·
    refine ⟨5720171720383800283844861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3813447813589200189229907 5720171720383800283844861)
    ·
      refine ⟨2145064395143925106441823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5720171720383800283844861 2145064395143925106441823)
      ·
        refine ⟨3217596592715887659662735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2145064395143925106441823 3217596592715887659662735)
        ·
          refine ⟨4826394889073831489494103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3217596592715887659662735 4826394889073831489494103)
          ·
            refine ⟨7239592333610747234241155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4826394889073831489494103 7239592333610747234241155)
            ·
              refine ⟨10859388500416120851361733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7239592333610747234241155 10859388500416120851361733)
              ·
                refine ⟨2036135343828022659630325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10859388500416120851361733 2036135343828022659630325)
                ·
                  refine ⟨190887688483877124340343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2036135343828022659630325 190887688483877124340343)
                  ·
                    rfl

theorem cell22_1672886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 4, 5].length) (baseStart_1672886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1672886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1672886 prefixEnd_1672886 := by exact prefixLift 1672886
  have htrace : WordTrace (prefixWord ++ tailWord_1672886) baseStart_1672886 baseEnd_1672886 := by
    simpa [prefixWord, tailWord_1672886, baseEnd_1672886] using wordTrace_append hprefix tailTrace_1672886
  have hstable : (prefixWord ++ tailWord_1672886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1672886).length < 2 ^ (prefixWord ++ tailWord_1672886).sum := by decide
  have hdescent : baseEnd_1672886 < baseStart_1672886 := by decide
  rcases family_descends (prefixWord ++ tailWord_1672886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1672914 : List Nat := [3, 2, 2, 2, 2, 2, 1, 2, 6]
def baseStart_1672914 : Nat := 118140960795 + 1672914 * 2 ^ 59
def prefixEnd_1672914 : Nat := 4983230072969 + 3 ^ 40 * 1672914 * 2
def baseEnd_1672914 : Nat := 190890883474616211106981

theorem tailTrace_1672914 : CollatzResearch.WordTrace tailWord_1672914 prefixEnd_1672914 190890883474616211106981 := by
  unfold tailWord_1672914
  simp only [CollatzResearch.WordTrace]
  refine ⟨15254046565331440952424449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40677457507550509206465197 15254046565331440952424449)
  ·
    refine ⟨11440534923998580714318337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15254046565331440952424449 11440534923998580714318337)
    ·
      refine ⟨8580401192998935535738753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11440534923998580714318337 8580401192998935535738753)
      ·
        refine ⟨6435300894749201651804065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8580401192998935535738753 6435300894749201651804065)
        ·
          refine ⟨4826475671061901238853049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6435300894749201651804065 4826475671061901238853049)
          ·
            refine ⟨3619856753296425929139787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4826475671061901238853049 3619856753296425929139787)
            ·
              refine ⟨5429785129944638893709681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3619856753296425929139787 5429785129944638893709681)
              ·
                refine ⟨4072338847458479170282261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5429785129944638893709681 4072338847458479170282261)
                ·
                  refine ⟨190890883474616211106981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4072338847458479170282261 190890883474616211106981)
                  ·
                    rfl

theorem cell22_1672914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 2, 6].length) (baseStart_1672914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1672914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1672914 prefixEnd_1672914 := by exact prefixLift 1672914
  have htrace : WordTrace (prefixWord ++ tailWord_1672914) baseStart_1672914 baseEnd_1672914 := by
    simpa [prefixWord, tailWord_1672914, baseEnd_1672914] using wordTrace_append hprefix tailTrace_1672914
  have hstable : (prefixWord ++ tailWord_1672914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1672914).length < 2 ^ (prefixWord ++ tailWord_1672914).sum := by decide
  have hdescent : baseEnd_1672914 < baseStart_1672914 := by decide
  rcases family_descends (prefixWord ++ tailWord_1672914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1672927 : List Nat := [1, 1, 2, 3, 2, 2, 3, 1, 1, 6]
def baseStart_1672927 : Nat := 118140960795 + 1672927 * 2 ^ 59
def prefixEnd_1672927 : Nat := 4983230072969 + 3 ^ 40 * 1672927 * 2
def baseEnd_1672927 : Nat := 572677100589520932745903

theorem tailTrace_1672927 : CollatzResearch.WordTrace tailWord_1672927 prefixEnd_1672927 572677100589520932745903 := by
  unfold tailWord_1672927
  simp only [CollatzResearch.WordTrace]
  refine ⟨61016660410278667029921035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40677773606852444686614023 61016660410278667029921035)
  ·
    refine ⟨91524990615418000544881553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61016660410278667029921035 91524990615418000544881553)
    ·
      refine ⟨68643742961563500408661165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91524990615418000544881553 68643742961563500408661165)
      ·
        refine ⟨25741403610586312653247937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68643742961563500408661165 25741403610586312653247937)
        ·
          refine ⟨19306052707939734489935953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25741403610586312653247937 19306052707939734489935953)
          ·
            refine ⟨14479539530954800867451965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19306052707939734489935953 14479539530954800867451965)
            ·
              refine ⟨5429827324108050325294487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14479539530954800867451965 5429827324108050325294487)
              ·
                refine ⟨8144740986162075487941731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5429827324108050325294487 8144740986162075487941731)
                ·
                  refine ⟨12217111479243113231912597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8144740986162075487941731 12217111479243113231912597)
                  ·
                    refine ⟨572677100589520932745903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12217111479243113231912597 572677100589520932745903)
                    ·
                      rfl

theorem cell22_1672927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 1, 1, 6].length) (baseStart_1672927 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1672927 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1672927 prefixEnd_1672927 := by exact prefixLift 1672927
  have htrace : WordTrace (prefixWord ++ tailWord_1672927) baseStart_1672927 baseEnd_1672927 := by
    simpa [prefixWord, tailWord_1672927, baseEnd_1672927] using wordTrace_append hprefix tailTrace_1672927
  have hstable : (prefixWord ++ tailWord_1672927).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1672927).length < 2 ^ (prefixWord ++ tailWord_1672927).sum := by decide
  have hdescent : baseEnd_1672927 < baseStart_1672927 := by decide
  rcases family_descends (prefixWord ++ tailWord_1672927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1672942 : List Nat := [4, 1, 2, 1, 1, 2, 11]
def baseStart_1672942 : Nat := 118140960795 + 1672942 * 2 ^ 59
def prefixEnd_1672942 : Nat := 4983230072969 + 3 ^ 40 * 1672942 * 2
def baseEnd_1672942 : Nat := 21210453162817255319291

theorem tailTrace_1672942 : CollatzResearch.WordTrace tailWord_1672942 prefixEnd_1672942 21210453162817255319291 := by
  unfold tailWord_1672942
  simp only [CollatzResearch.WordTrace]
  refine ⟨7627150938153040573964635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40678138336816216394478053 7627150938153040573964635)
  ·
    refine ⟨11440726407229560860946953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7627150938153040573964635 11440726407229560860946953)
    ·
      refine ⟨8580544805422170645710215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11440726407229560860946953 8580544805422170645710215)
      ·
        refine ⟨12870817208133255968565323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8580544805422170645710215 12870817208133255968565323)
        ·
          refine ⟨19306225812199883952847985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12870817208133255968565323 19306225812199883952847985)
          ·
            refine ⟨14479669359149912964635989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19306225812199883952847985 14479669359149912964635989)
            ·
              refine ⟨21210453162817255319291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 14479669359149912964635989 21210453162817255319291)
              ·
                rfl

theorem cell22_1672942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 11].length) (baseStart_1672942 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1672942 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1672942 prefixEnd_1672942 := by exact prefixLift 1672942
  have htrace : WordTrace (prefixWord ++ tailWord_1672942) baseStart_1672942 baseEnd_1672942 := by
    simpa [prefixWord, tailWord_1672942, baseEnd_1672942] using wordTrace_append hprefix tailTrace_1672942
  have hstable : (prefixWord ++ tailWord_1672942).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1672942).length < 2 ^ (prefixWord ++ tailWord_1672942).sum := by decide
  have hdescent : baseEnd_1672942 < baseStart_1672942 := by decide
  rcases family_descends (prefixWord ++ tailWord_1672942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1672948 : List Nat := [2, 6, 1, 1, 1, 2, 2, 1, 6]
def baseStart_1672948 : Nat := 118140960795 + 1672948 * 2 ^ 59
def prefixEnd_1672948 : Nat := 4983230072969 + 3 ^ 40 * 1672948 * 2
def baseEnd_1672948 : Nat := 190894763106227959323613

theorem tailTrace_1672948 : CollatzResearch.WordTrace tailWord_1672948 prefixEnd_1672948 190894763106227959323613 := by
  unfold tailWord_1672948
  simp only [CollatzResearch.WordTrace]
  refine ⟨30508713171601293808217749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40678284228801725077623665 30508713171601293808217749)
  ·
    refine ⟨1430095929918810647260207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 30508713171601293808217749 1430095929918810647260207)
    ·
      refine ⟨2145143894878215970890311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1430095929918810647260207 2145143894878215970890311)
      ·
        refine ⟨3217715842317323956335467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2145143894878215970890311 3217715842317323956335467)
        ·
          refine ⟨4826573763475985934503201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3217715842317323956335467 4826573763475985934503201)
          ·
            refine ⟨3619930322606989450877401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4826573763475985934503201 3619930322606989450877401)
            ·
              refine ⟨2714947741955242088158051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3619930322606989450877401 2714947741955242088158051)
              ·
                refine ⟨4072421612932863132237077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2714947741955242088158051 4072421612932863132237077)
                ·
                  refine ⟨190894763106227959323613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4072421612932863132237077 190894763106227959323613)
                  ·
                    rfl

theorem cell22_1672948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_1672948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1672948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1672948 prefixEnd_1672948 := by exact prefixLift 1672948
  have htrace : WordTrace (prefixWord ++ tailWord_1672948) baseStart_1672948 baseEnd_1672948 := by
    simpa [prefixWord, tailWord_1672948, baseEnd_1672948] using wordTrace_append hprefix tailTrace_1672948
  have hstable : (prefixWord ++ tailWord_1672948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1672948).length < 2 ^ (prefixWord ++ tailWord_1672948).sum := by decide
  have hdescent : baseEnd_1672948 < baseStart_1672948 := by decide
  rcases family_descends (prefixWord ++ tailWord_1672948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1672972 : List Nat := [2, 2, 1, 2, 2, 1, 2, 2, 2, 6]
def baseStart_1672972 : Nat := 118140960795 + 1672972 * 2 ^ 59
def prefixEnd_1672972 : Nat := 4983230072969 + 3 ^ 40 * 1672972 * 2
def baseEnd_1672972 : Nat := 572692505009155815370765

theorem tailTrace_1672972 : CollatzResearch.WordTrace tailWord_1672972 prefixEnd_1672972 572692505009155815370765 := by
  unfold tailWord_1672972
  simp only [CollatzResearch.WordTrace]
  refine ⟨30509150847557819857654585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40678867796743759810206113 30509150847557819857654585)
  ·
    refine ⟨22881863135668364893240939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30509150847557819857654585 22881863135668364893240939)
    ·
      refine ⟨34322794703502547339861409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22881863135668364893240939 34322794703502547339861409)
      ·
        refine ⟨25742096027626910504896057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34322794703502547339861409 25742096027626910504896057)
        ·
          refine ⟨19306572020720182878672043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25742096027626910504896057 19306572020720182878672043)
          ·
            refine ⟨28959858031080274318008065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19306572020720182878672043 28959858031080274318008065)
            ·
              refine ⟨21719893523310205738506049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28959858031080274318008065 21719893523310205738506049)
              ·
                refine ⟨16289920142482654303879537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21719893523310205738506049 16289920142482654303879537)
                ·
                  refine ⟨12217440106861990727909653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16289920142482654303879537 12217440106861990727909653)
                  ·
                    refine ⟨572692505009155815370765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12217440106861990727909653 572692505009155815370765)
                    ·
                      rfl

theorem cell22_1672972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 2, 2, 6].length) (baseStart_1672972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1672972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1672972 prefixEnd_1672972 := by exact prefixLift 1672972
  have htrace : WordTrace (prefixWord ++ tailWord_1672972) baseStart_1672972 baseEnd_1672972 := by
    simpa [prefixWord, tailWord_1672972, baseEnd_1672972] using wordTrace_append hprefix tailTrace_1672972
  have hstable : (prefixWord ++ tailWord_1672972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1672972).length < 2 ^ (prefixWord ++ tailWord_1672972).sum := by decide
  have hdescent : baseEnd_1672972 < baseStart_1672972 := by decide
  rcases family_descends (prefixWord ++ tailWord_1672972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1673021 : List Nat := [1, 4, 1, 4, 1, 2, 1, 3, 5]
def baseStart_1673021 : Nat := 118140960795 + 1673021 * 2 ^ 59
def prefixEnd_1673021 : Nat := 4983230072969 + 3 ^ 40 * 1673021 * 2
def baseEnd_1673021 : Nat := 190903092903512006965205

theorem tailTrace_1673021 : CollatzResearch.WordTrace tailWord_1673021 prefixEnd_1673021 190903092903512006965205 := by
  unfold tailWord_1673021
  simp only [CollatzResearch.WordTrace]
  refine ⟨61020088871938121083842917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40680059247958747389228611 61020088871938121083842917)
  ·
    refine ⟨11441266663488397703220547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61020088871938121083842917 11441266663488397703220547)
    ·
      refine ⟨17161899995232596554830821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11441266663488397703220547 17161899995232596554830821)
      ·
        refine ⟨3217856249106111854030779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17161899995232596554830821 3217856249106111854030779)
        ·
          refine ⟨4826784373659167781046169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3217856249106111854030779 4826784373659167781046169)
          ·
            refine ⟨3620088280244375835784627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4826784373659167781046169 3620088280244375835784627)
            ·
              refine ⟨5430132420366563753676941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3620088280244375835784627 5430132420366563753676941)
              ·
                refine ⟨2036299657637461407628853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5430132420366563753676941 2036299657637461407628853)
                ·
                  refine ⟨190903092903512006965205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2036299657637461407628853 190903092903512006965205)
                  ·
                    rfl

theorem cell22_1673021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 3, 5].length) (baseStart_1673021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1673021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1673021 prefixEnd_1673021 := by exact prefixLift 1673021
  have htrace : WordTrace (prefixWord ++ tailWord_1673021) baseStart_1673021 baseEnd_1673021 := by
    simpa [prefixWord, tailWord_1673021, baseEnd_1673021] using wordTrace_append hprefix tailTrace_1673021
  have hstable : (prefixWord ++ tailWord_1673021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1673021).length < 2 ^ (prefixWord ++ tailWord_1673021).sum := by decide
  have hdescent : baseEnd_1673021 < baseStart_1673021 := by decide
  rcases family_descends (prefixWord ++ tailWord_1673021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1673034 : List Nat := [3, 1, 2, 1, 1, 1, 5, 1, 3, 4]
def baseStart_1673034 : Nat := 118140960795 + 1673034 * 2 ^ 59
def prefixEnd_1673034 : Nat := 4983230072969 + 3 ^ 40 * 1673034 * 2
def baseEnd_1673034 : Nat := 572713728876208320320575

theorem tailTrace_1673034 : CollatzResearch.WordTrace tailWord_1673034 prefixEnd_1673034 572713728876208320320575 := by
  unfold tailWord_1673034
  simp only [CollatzResearch.WordTrace]
  refine ⟨15255140755222756076016539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40680375347260682869377437 15255140755222756076016539)
  ·
    refine ⟨22882711132834134114024809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15255140755222756076016539 22882711132834134114024809)
    ·
      refine ⟨17162033349625600585518607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22882711132834134114024809 17162033349625600585518607)
      ·
        refine ⟨25743050024438400878277911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17162033349625600585518607 25743050024438400878277911)
        ·
          refine ⟨38614575036657601317416867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25743050024438400878277911 38614575036657601317416867)
          ·
            refine ⟨57921862554986401976125301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38614575036657601317416867 57921862554986401976125301)
            ·
              refine ⟨5430174614529975185261747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57921862554986401976125301 5430174614529975185261747)
              ·
                refine ⟨8145261921794962777892621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5430174614529975185261747 8145261921794962777892621)
                ·
                  refine ⟨3054473220673111041709733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8145261921794962777892621 3054473220673111041709733)
                  ·
                    refine ⟨572713728876208320320575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3054473220673111041709733 572713728876208320320575)
                    ·
                      rfl

theorem cell22_1673034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 1, 3, 4].length) (baseStart_1673034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1673034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1673034 prefixEnd_1673034 := by exact prefixLift 1673034
  have htrace : WordTrace (prefixWord ++ tailWord_1673034) baseStart_1673034 baseEnd_1673034 := by
    simpa [prefixWord, tailWord_1673034, baseEnd_1673034] using wordTrace_append hprefix tailTrace_1673034
  have hstable : (prefixWord ++ tailWord_1673034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1673034).length < 2 ^ (prefixWord ++ tailWord_1673034).sum := by decide
  have hdescent : baseEnd_1673034 < baseStart_1673034 := by decide
  rcases family_descends (prefixWord ++ tailWord_1673034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1673064 : List Nat := [2, 1, 4, 2, 1, 1, 1, 2, 3, 5]
def baseStart_1673064 : Nat := 118140960795 + 1673064 * 2 ^ 59
def prefixEnd_1673064 : Nat := 4983230072969 + 3 ^ 40 * 1673064 * 2
def baseEnd_1673064 : Nat := 572723998489298242070483

theorem tailTrace_1673064 : CollatzResearch.WordTrace tailWord_1673064 prefixEnd_1673064 572723998489298242070483 := by
  unfold tailWord_1673064
  simp only [CollatzResearch.WordTrace]
  refine ⟨30510828605391169713829123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40681104807188226285105497 30510828605391169713829123)
  ·
    refine ⟨45766242908086754570743685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30510828605391169713829123 45766242908086754570743685)
    ·
      refine ⟨8581170545266266482014441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45766242908086754570743685 8581170545266266482014441)
      ·
        refine ⟨6435877908949699861510831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8581170545266266482014441 6435877908949699861510831)
        ·
          refine ⟨9653816863424549792266247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6435877908949699861510831 9653816863424549792266247)
          ·
            refine ⟨14480725295136824688399371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9653816863424549792266247 14480725295136824688399371)
            ·
              refine ⟨21721087942705237032599057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14480725295136824688399371 21721087942705237032599057)
              ·
                refine ⟨16290815957028927774449293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21721087942705237032599057 16290815957028927774449293)
                ·
                  refine ⟨6109055983885847915418485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16290815957028927774449293 6109055983885847915418485)
                  ·
                    refine ⟨572723998489298242070483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6109055983885847915418485 572723998489298242070483)
                    ·
                      rfl

theorem cell22_1673064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 2, 3, 5].length) (baseStart_1673064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1673064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1673064 prefixEnd_1673064 := by exact prefixLift 1673064
  have htrace : WordTrace (prefixWord ++ tailWord_1673064) baseStart_1673064 baseEnd_1673064 := by
    simpa [prefixWord, tailWord_1673064, baseEnd_1673064] using wordTrace_append hprefix tailTrace_1673064
  have hstable : (prefixWord ++ tailWord_1673064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1673064).length < 2 ^ (prefixWord ++ tailWord_1673064).sum := by decide
  have hdescent : baseEnd_1673064 < baseStart_1673064 := by decide
  rcases family_descends (prefixWord ++ tailWord_1673064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1673081 : List Nat := [1, 2, 1, 3, 2, 2, 1, 5, 2, 3]
def baseStart_1673081 : Nat := 118140960795 + 1673081 * 2 ^ 59
def prefixEnd_1673081 : Nat := 4983230072969 + 3 ^ 40 * 1673081 * 2
def baseEnd_1673081 : Nat := 572729817936715864395431

theorem tailTrace_1673081 : CollatzResearch.WordTrace tailWord_1673081 prefixEnd_1673081 572729817936715864395431 := by
  unfold tailWord_1673081
  simp only [CollatzResearch.WordTrace]
  refine ⟨61022277251720751331027097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40681518167813834220684731 61022277251720751331027097)
  ·
    refine ⟨45766707938790563498270323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61022277251720751331027097 45766707938790563498270323)
    ·
      refine ⟨68650061908185845247405485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45766707938790563498270323 68650061908185845247405485)
      ·
        refine ⟨25743773215569691967777057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68650061908185845247405485 25743773215569691967777057)
        ·
          refine ⟨19307829911677268975832793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25743773215569691967777057 19307829911677268975832793)
          ·
            refine ⟨14480872433757951731874595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19307829911677268975832793 14480872433757951731874595)
            ·
              refine ⟨21721308650636927597811893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14480872433757951731874595 21721308650636927597811893)
              ·
                refine ⟨2036372685997211962294865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21721308650636927597811893 2036372685997211962294865)
                ·
                  refine ⟨1527279514497908971721149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2036372685997211962294865 1527279514497908971721149)
                  ·
                    refine ⟨572729817936715864395431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1527279514497908971721149 572729817936715864395431)
                    ·
                      rfl

theorem cell22_1673081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 5, 2, 3].length) (baseStart_1673081 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1673081 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1673081 prefixEnd_1673081 := by exact prefixLift 1673081
  have htrace : WordTrace (prefixWord ++ tailWord_1673081) baseStart_1673081 baseEnd_1673081 := by
    simpa [prefixWord, tailWord_1673081, baseEnd_1673081] using wordTrace_append hprefix tailTrace_1673081
  have hstable : (prefixWord ++ tailWord_1673081).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1673081).length < 2 ^ (prefixWord ++ tailWord_1673081).sum := by decide
  have hdescent : baseEnd_1673081 < baseStart_1673081 := by decide
  rcases family_descends (prefixWord ++ tailWord_1673081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1673096 : List Nat := [2, 1, 3, 3, 3, 1, 1, 1, 1, 6]
def baseStart_1673096 : Nat := 118140960795 + 1673096 * 2 ^ 59
def prefixEnd_1673096 : Nat := 4983230072969 + 3 ^ 40 * 1673096 * 2
def baseEnd_1673096 : Nat := 572734952743260825270385

theorem tailTrace_1673096 : CollatzResearch.WordTrace tailWord_1673096 prefixEnd_1673096 572734952743260825270385 := by
  unfold tailWord_1673096
  simp only [CollatzResearch.WordTrace]
  refine ⟨30511412173333204446411571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40681882897777605928548761 30511412173333204446411571)
  ·
    refine ⟨45767118259999806669617357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30511412173333204446411571 45767118259999806669617357)
    ·
      refine ⟨17162669347499927501106509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45767118259999806669617357 17162669347499927501106509)
      ·
        refine ⟨6436001005312472812914941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17162669347499927501106509 6436001005312472812914941)
        ·
          refine ⟨2413500376992177304843103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6436001005312472812914941 2413500376992177304843103)
          ·
            refine ⟨3620250565488265957264655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2413500376992177304843103 3620250565488265957264655)
            ·
              refine ⟨5430375848232398935896983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3620250565488265957264655 5430375848232398935896983)
              ·
                refine ⟨8145563772348598403845475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5430375848232398935896983 8145563772348598403845475)
                ·
                  refine ⟨12218345658522897605768213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8145563772348598403845475 12218345658522897605768213)
                  ·
                    refine ⟨572734952743260825270385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12218345658522897605768213 572734952743260825270385)
                    ·
                      rfl

theorem cell22_1673096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 1, 1, 6].length) (baseStart_1673096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1673096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1673096 prefixEnd_1673096 := by exact prefixLift 1673096
  have htrace : WordTrace (prefixWord ++ tailWord_1673096) baseStart_1673096 baseEnd_1673096 := by
    simpa [prefixWord, tailWord_1673096, baseEnd_1673096] using wordTrace_append hprefix tailTrace_1673096
  have hstable : (prefixWord ++ tailWord_1673096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1673096).length < 2 ^ (prefixWord ++ tailWord_1673096).sum := by decide
  have hdescent : baseEnd_1673096 < baseStart_1673096 := by decide
  rcases family_descends (prefixWord ++ tailWord_1673096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1673102 : List Nat := [4, 1, 1, 5, 1, 2, 2, 1, 1, 4]
def baseStart_1673102 : Nat := 118140960795 + 1673102 * 2 ^ 59
def prefixEnd_1673102 : Nat := 4983230072969 + 3 ^ 40 * 1673102 * 2
def baseEnd_1673102 : Nat := 572737006665878809620367

theorem tailTrace_1673102 : CollatzResearch.WordTrace tailWord_1673102 prefixEnd_1673102 572737006665878809620367 := by
  unfold tailWord_1673102
  simp only [CollatzResearch.WordTrace]
  refine ⟨7627880398080583989692695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40682028789763114611694373 7627880398080583989692695)
  ·
    refine ⟨11441820597120875984539043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7627880398080583989692695 11441820597120875984539043)
    ·
      refine ⟨17162730895681313976808565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11441820597120875984539043 17162730895681313976808565)
      ·
        refine ⟨1609006021470123185325803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17162730895681313976808565 1609006021470123185325803)
        ·
          refine ⟨2413509032205184777988705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1609006021470123185325803 2413509032205184777988705)
          ·
            refine ⟨1810131774153888583491529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2413509032205184777988705 1810131774153888583491529)
            ·
              refine ⟨1357598830615416437618647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1810131774153888583491529 1357598830615416437618647)
              ·
                refine ⟨2036398245923124656427971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1357598830615416437618647 2036398245923124656427971)
                ·
                  refine ⟨3054597368884686984641957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2036398245923124656427971 3054597368884686984641957)
                  ·
                    refine ⟨572737006665878809620367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3054597368884686984641957 572737006665878809620367)
                    ·
                      rfl

theorem cell22_1673102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 2, 1, 1, 4].length) (baseStart_1673102 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1673102 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1673102 prefixEnd_1673102 := by exact prefixLift 1673102
  have htrace : WordTrace (prefixWord ++ tailWord_1673102) baseStart_1673102 baseEnd_1673102 := by
    simpa [prefixWord, tailWord_1673102, baseEnd_1673102] using wordTrace_append hprefix tailTrace_1673102
  have hstable : (prefixWord ++ tailWord_1673102).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1673102).length < 2 ^ (prefixWord ++ tailWord_1673102).sum := by decide
  have hdescent : baseEnd_1673102 < baseStart_1673102 := by decide
  rcases family_descends (prefixWord ++ tailWord_1673102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1673160 : List Nat := [2, 1, 3, 1, 4, 1, 3, 3, 1, 3]
def baseStart_1673160 : Nat := 118140960795 + 1673160 * 2 ^ 59
def prefixEnd_1673160 : Nat := 4983230072969 + 3 ^ 40 * 1673160 * 2
def baseEnd_1673160 : Nat := 572756861251185991670189

theorem tailTrace_1673160 : CollatzResearch.WordTrace tailWord_1673160 prefixEnd_1673160 572756861251185991670189 := by
  unfold tailWord_1673160
  simp only [CollatzResearch.WordTrace]
  refine ⟨30512579309217273911576467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40683439078956365215435289 30512579309217273911576467)
  ·
    refine ⟨45768868963825910867364701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30512579309217273911576467 45768868963825910867364701)
    ·
      refine ⟨17163325861434716575261763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45768868963825910867364701 17163325861434716575261763)
      ·
        refine ⟨25744988792152074862892645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17163325861434716575261763 25744988792152074862892645)
        ·
          refine ⟨4827185398528514036792371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25744988792152074862892645 4827185398528514036792371)
          ·
            refine ⟨7240778097792771055188557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4827185398528514036792371 7240778097792771055188557)
            ·
              refine ⟨2715291786672289145695709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7240778097792771055188557 2715291786672289145695709)
              ·
                refine ⟨1018234420002108429635891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2715291786672289145695709 1018234420002108429635891)
                ·
                  refine ⟨1527351630003162644453837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1018234420002108429635891 1527351630003162644453837)
                  ·
                    refine ⟨572756861251185991670189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1527351630003162644453837 572756861251185991670189)
                    ·
                      rfl

theorem cell22_1673160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 3, 3, 1, 3].length) (baseStart_1673160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1673160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1673160 prefixEnd_1673160 := by exact prefixLift 1673160
  have htrace : WordTrace (prefixWord ++ tailWord_1673160) baseStart_1673160 baseEnd_1673160 := by
    simpa [prefixWord, tailWord_1673160, baseEnd_1673160] using wordTrace_append hprefix tailTrace_1673160
  have hstable : (prefixWord ++ tailWord_1673160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1673160).length < 2 ^ (prefixWord ++ tailWord_1673160).sum := by decide
  have hdescent : baseEnd_1673160 < baseStart_1673160 := by decide
  rcases family_descends (prefixWord ++ tailWord_1673160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1673177 : List Nat := [1, 2, 1, 2, 6, 1, 3, 2, 1, 3]
def baseStart_1673177 : Nat := 118140960795 + 1673177 * 2 ^ 59
def prefixEnd_1673177 : Nat := 4983230072969 + 3 ^ 40 * 1673177 * 2
def baseEnd_1673177 : Nat := 572762680698603613995137

theorem tailTrace_1673177 : CollatzResearch.WordTrace tailWord_1673177 prefixEnd_1673177 572762680698603613995137 := by
  unfold tailWord_1673177
  simp only [CollatzResearch.WordTrace]
  refine ⟨61025778659372959726521785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40683852439581973151014523 61025778659372959726521785)
  ·
    refine ⟨45769333994529719794891339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61025778659372959726521785 45769333994529719794891339)
    ·
      refine ⟨68654000991794579692337009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45769333994529719794891339 68654000991794579692337009)
      ·
        refine ⟨51490500743845934769252757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68654000991794579692337009 51490500743845934769252757)
        ·
          refine ⟨2413617222367778192308723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 51490500743845934769252757 2413617222367778192308723)
          ·
            refine ⟨3620425833551667288463085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2413617222367778192308723 3620425833551667288463085)
            ·
              refine ⟨1357659687581875233173657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3620425833551667288463085 1357659687581875233173657)
              ·
                refine ⟨1018244765686406424880243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1357659687581875233173657 1018244765686406424880243)
                ·
                  refine ⟨1527367148529609637320365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1018244765686406424880243 1527367148529609637320365)
                  ·
                    refine ⟨572762680698603613995137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1527367148529609637320365 572762680698603613995137)
                    ·
                      rfl

theorem cell22_1673177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 3, 2, 1, 3].length) (baseStart_1673177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1673177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1673177 prefixEnd_1673177 := by exact prefixLift 1673177
  have htrace : WordTrace (prefixWord ++ tailWord_1673177) baseStart_1673177 baseEnd_1673177 := by
    simpa [prefixWord, tailWord_1673177, baseEnd_1673177] using wordTrace_append hprefix tailTrace_1673177
  have hstable : (prefixWord ++ tailWord_1673177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1673177).length < 2 ^ (prefixWord ++ tailWord_1673177).sum := by decide
  have hdescent : baseEnd_1673177 < baseStart_1673177 := by decide
  rcases family_descends (prefixWord ++ tailWord_1673177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1673216 : List Nat := [2, 1, 1, 2, 1, 1, 1, 6, 4, 3]
def baseStart_1673216 : Nat := 118140960795 + 1673216 * 2 ^ 59
def prefixEnd_1673216 : Nat := 4983230072969 + 3 ^ 40 * 1673216 * 2
def baseEnd_1673216 : Nat := 572776031195620512270017

theorem tailTrace_1673216 : CollatzResearch.WordTrace tailWord_1673216 prefixEnd_1673216 572776031195620512270017 := by
  unfold tailWord_1673216
  simp only [CollatzResearch.WordTrace]
  refine ⟨30513600553115834693595751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40684800737487779591461001 30513600553115834693595751)
  ·
    refine ⟨45770400829673752040393627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30513600553115834693595751 45770400829673752040393627)
    ·
      refine ⟨68655601244510628060590441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45770400829673752040393627 68655601244510628060590441)
      ·
        refine ⟨51491700933382971045442831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68655601244510628060590441 51491700933382971045442831)
        ·
          refine ⟨77237551400074456568164247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51491700933382971045442831 77237551400074456568164247)
          ·
            refine ⟨115856327100111684852246371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77237551400074456568164247 115856327100111684852246371)
            ·
              refine ⟨173784490650167527278369557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115856327100111684852246371 173784490650167527278369557)
              ·
                refine ⟨8146147999226602841173573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 173784490650167527278369557 8146147999226602841173573)
                ·
                  refine ⟨1527402749854988032720045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8146147999226602841173573 1527402749854988032720045)
                  ·
                    refine ⟨572776031195620512270017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1527402749854988032720045 572776031195620512270017)
                    ·
                      rfl

theorem cell22_1673216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 6, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 6, 4, 3].length) (baseStart_1673216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1673216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1673216 prefixEnd_1673216 := by exact prefixLift 1673216
  have htrace : WordTrace (prefixWord ++ tailWord_1673216) baseStart_1673216 baseEnd_1673216 := by
    simpa [prefixWord, tailWord_1673216, baseEnd_1673216] using wordTrace_append hprefix tailTrace_1673216
  have hstable : (prefixWord ++ tailWord_1673216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1673216).length < 2 ^ (prefixWord ++ tailWord_1673216).sum := by decide
  have hdescent : baseEnd_1673216 < baseStart_1673216 := by decide
  rcases family_descends (prefixWord ++ tailWord_1673216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1673306 : List Nat := [3, 1, 1, 2, 1, 1, 3, 3, 2, 5]
def baseStart_1673306 : Nat := 118140960795 + 1673306 * 2 ^ 59
def prefixEnd_1673306 : Nat := 4983230072969 + 3 ^ 40 * 1673306 * 2
def baseEnd_1673306 : Nat := 572806840034890277519741

theorem tailTrace_1673306 : CollatzResearch.WordTrace tailWord_1673306 prefixEnd_1673306 572806840034890277519741 := by
  unfold tailWord_1673306
  simp only [CollatzResearch.WordTrace]
  refine ⟨15257620918976403689491943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40686989117270409838645181 15257620918976403689491943)
  ·
    refine ⟨22886431378464605534237915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15257620918976403689491943 22886431378464605534237915)
    ·
      refine ⟨34329647067696908301356873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22886431378464605534237915 34329647067696908301356873)
      ·
        refine ⟨25747235300772681226017655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34329647067696908301356873 25747235300772681226017655)
        ·
          refine ⟨38620852951159021839026483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25747235300772681226017655 38620852951159021839026483)
          ·
            refine ⟨57931279426738532758539725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38620852951159021839026483 57931279426738532758539725)
            ·
              refine ⟨21724229785026949784452397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57931279426738532758539725 21724229785026949784452397)
              ·
                refine ⟨8146586169385106169169649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21724229785026949784452397 8146586169385106169169649)
                ·
                  refine ⟨6109939627038829626877237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8146586169385106169169649 6109939627038829626877237)
                  ·
                    refine ⟨572806840034890277519741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6109939627038829626877237 572806840034890277519741)
                    ·
                      rfl

theorem cell22_1673306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 3, 2, 5].length) (baseStart_1673306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1673306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1673306 prefixEnd_1673306 := by exact prefixLift 1673306
  have htrace : WordTrace (prefixWord ++ tailWord_1673306) baseStart_1673306 baseEnd_1673306 := by
    simpa [prefixWord, tailWord_1673306, baseEnd_1673306] using wordTrace_append hprefix tailTrace_1673306
  have hstable : (prefixWord ++ tailWord_1673306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1673306).length < 2 ^ (prefixWord ++ tailWord_1673306).sum := by decide
  have hdescent : baseEnd_1673306 < baseStart_1673306 := by decide
  rcases family_descends (prefixWord ++ tailWord_1673306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1673381 : List Nat := [1, 3, 1, 2, 1, 3, 1, 10]
def baseStart_1673381 : Nat := 118140960795 + 1673381 * 2 ^ 59
def prefixEnd_1673381 : Nat := 4983230072969 + 3 ^ 40 * 1673381 * 2
def baseEnd_1673381 : Nat := 63648057118623897988279

theorem tailTrace_1673381 : CollatzResearch.WordTrace tailWord_1673381 prefixEnd_1673381 63648057118623897988279 := by
  unfold tailWord_1673381
  simp only [CollatzResearch.WordTrace]
  refine ⟨61033219150633902566947997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40688812767089268377965331 61033219150633902566947997)
  ·
    refine ⟨22887457181487713462605499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61033219150633902566947997 22887457181487713462605499)
    ·
      refine ⟨34331185772231570193908249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22887457181487713462605499 34331185772231570193908249)
      ·
        refine ⟨25748389329173677645431187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34331185772231570193908249 25748389329173677645431187)
        ·
          refine ⟨38622583993760516468146781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25748389329173677645431187 38622583993760516468146781)
          ·
            refine ⟨14483468997660193675555043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38622583993760516468146781 14483468997660193675555043)
            ·
              refine ⟨21725203496490290513332565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14483468997660193675555043 21725203496490290513332565)
              ·
                refine ⟨63648057118623897988279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 21725203496490290513332565 63648057118623897988279)
                ·
                  rfl

theorem cell22_1673381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 10].length) (baseStart_1673381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1673381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1673381 prefixEnd_1673381 := by exact prefixLift 1673381
  have htrace : WordTrace (prefixWord ++ tailWord_1673381) baseStart_1673381 baseEnd_1673381 := by
    simpa [prefixWord, tailWord_1673381, baseEnd_1673381] using wordTrace_append hprefix tailTrace_1673381
  have hstable : (prefixWord ++ tailWord_1673381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1673381).length < 2 ^ (prefixWord ++ tailWord_1673381).sum := by decide
  have hdescent : baseEnd_1673381 < baseStart_1673381 := by decide
  rcases family_descends (prefixWord ++ tailWord_1673381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1673398 : List Nat := [5, 1, 3, 13]
def baseStart_1673398 : Nat := 118140960795 + 1673398 * 2 ^ 59
def prefixEnd_1673398 : Nat := 4983230072969 + 3 ^ 40 * 1673398 * 2
def baseEnd_1673398 : Nat := 785786465727068181371

theorem tailTrace_1673398 : CollatzResearch.WordTrace tailWord_1673398 prefixEnd_1673398 785786465727068181371 := by
  unfold tailWord_1673398
  simp only [CollatzResearch.WordTrace]
  refine ⟨3814614949473269654394803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40689226127714876313544565 3814614949473269654394803)
  ·
    refine ⟨5721922424209904481592205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3814614949473269654394803 5721922424209904481592205)
    ·
      refine ⟨2145720909078714180597077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5721922424209904481592205 2145720909078714180597077)
      ·
        refine ⟨785786465727068181371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 13 2145720909078714180597077 785786465727068181371)
        ·
          rfl

theorem cell22_1673398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 13].length) (baseStart_1673398 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1673398 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1673398 prefixEnd_1673398 := by exact prefixLift 1673398
  have htrace : WordTrace (prefixWord ++ tailWord_1673398) baseStart_1673398 baseEnd_1673398 := by
    simpa [prefixWord, tailWord_1673398, baseEnd_1673398] using wordTrace_append hprefix tailTrace_1673398
  have hstable : (prefixWord ++ tailWord_1673398).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1673398).length < 2 ^ (prefixWord ++ tailWord_1673398).sum := by decide
  have hdescent : baseEnd_1673398 < baseStart_1673398 := by decide
  rcases family_descends (prefixWord ++ tailWord_1673398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1673404 : List Nat := [2, 2, 2, 3, 3, 2, 2, 2, 4]
def baseStart_1673404 : Nat := 118140960795 + 1673404 * 2 ^ 59
def prefixEnd_1673404 : Nat := 4983230072969 + 3 ^ 40 * 1673404 * 2
def baseEnd_1673404 : Nat := 190946795812550229523147

theorem tailTrace_1673404 : CollatzResearch.WordTrace tailWord_1673404 prefixEnd_1673404 190946795812550229523147 := by
  unfold tailWord_1673404
  simp only [CollatzResearch.WordTrace]
  refine ⟨30517029014775288747517633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40689372019700384996690177 30517029014775288747517633)
  ·
    refine ⟨22887771761081466560638225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30517029014775288747517633 22887771761081466560638225)
    ·
      refine ⟨17165828820811099920478669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22887771761081466560638225 17165828820811099920478669)
      ·
        refine ⟨6437185807804162470179501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17165828820811099920478669 6437185807804162470179501)
        ·
          refine ⟨2413944677926560926317313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6437185807804162470179501 2413944677926560926317313)
          ·
            refine ⟨1810458508444920694737985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2413944677926560926317313 1810458508444920694737985)
            ·
              refine ⟨1357843881333690521053489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1810458508444920694737985 1357843881333690521053489)
              ·
                refine ⟨1018382911000267890790117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1357843881333690521053489 1018382911000267890790117)
                ·
                  refine ⟨190946795812550229523147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1018382911000267890790117 190946795812550229523147)
                  ·
                    rfl

theorem cell22_1673404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 2, 2, 4].length) (baseStart_1673404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1673404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1673404 prefixEnd_1673404 := by exact prefixLift 1673404
  have htrace : WordTrace (prefixWord ++ tailWord_1673404) baseStart_1673404 baseEnd_1673404 := by
    simpa [prefixWord, tailWord_1673404, baseEnd_1673404] using wordTrace_append hprefix tailTrace_1673404
  have hstable : (prefixWord ++ tailWord_1673404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1673404).length < 2 ^ (prefixWord ++ tailWord_1673404).sum := by decide
  have hdescent : baseEnd_1673404 < baseStart_1673404 := by decide
  rcases family_descends (prefixWord ++ tailWord_1673404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1673522 : List Nat := [3, 2, 1, 1, 5, 2, 1, 1, 6]
def baseStart_1673522 : Nat := 118140960795 + 1673522 * 2 ^ 59
def prefixEnd_1673522 : Nat := 4983230072969 + 3 ^ 40 * 1673522 * 2
def baseEnd_1673522 : Nat := 190960260416379238039693

theorem tailTrace_1673522 : CollatzResearch.WordTrace tailWord_1673522 prefixEnd_1673522 190960260416379238039693 := by
  unfold tailWord_1673522
  simp only [CollatzResearch.WordTrace]
  refine ⟨15259590460780770911957705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40692241228748722431887213 15259590460780770911957705)
  ·
    refine ⟨11444692845585578183968279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15259590460780770911957705 11444692845585578183968279)
    ·
      refine ⟨17167039268378367275952419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11444692845585578183968279 17167039268378367275952419)
      ·
        refine ⟨25750558902567550913928629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17167039268378367275952419 25750558902567550913928629)
        ·
          refine ⟨2414114897115707898180809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25750558902567550913928629 2414114897115707898180809)
          ·
            refine ⟨1810586172836780923635607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2414114897115707898180809 1810586172836780923635607)
            ·
              refine ⟨2715879259255171385453411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1810586172836780923635607 2715879259255171385453411)
              ·
                refine ⟨4073818888882757078180117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2715879259255171385453411 4073818888882757078180117)
                ·
                  refine ⟨190960260416379238039693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4073818888882757078180117 190960260416379238039693)
                  ·
                    rfl

theorem cell22_1673522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 1, 1, 6].length) (baseStart_1673522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1673522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1673522 prefixEnd_1673522 := by exact prefixLift 1673522
  have htrace : WordTrace (prefixWord ++ tailWord_1673522) baseStart_1673522 baseEnd_1673522 := by
    simpa [prefixWord, tailWord_1673522, baseEnd_1673522] using wordTrace_append hprefix tailTrace_1673522
  have hstable : (prefixWord ++ tailWord_1673522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1673522).length < 2 ^ (prefixWord ++ tailWord_1673522).sum := by decide
  have hdescent : baseEnd_1673522 < baseStart_1673522 := by decide
  rcases family_descends (prefixWord ++ tailWord_1673522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1673595 : List Nat := [1, 1, 1, 1, 1, 7, 2, 3, 5]
def baseStart_1673595 : Nat := 118140960795 + 1673595 * 2 ^ 59
def prefixEnd_1673595 : Nat := 4983230072969 + 3 ^ 40 * 1673595 * 2
def baseEnd_1673595 : Nat := 190968590213663285681285

theorem tailTrace_1673595 : CollatzResearch.WordTrace tailWord_1673595 prefixEnd_1673595 190968590213663285681285 := by
  unfold tailWord_1673595
  simp only [CollatzResearch.WordTrace]
  refine ⟨61041024371858617115238239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40694016247905744743492159 61041024371858617115238239)
  ·
    refine ⟨91561536557787925672857359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61041024371858617115238239 91561536557787925672857359)
    ·
      refine ⟨137342304836681888509286039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91561536557787925672857359 137342304836681888509286039)
      ·
        refine ⟨206013457255022832763929059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137342304836681888509286039 206013457255022832763929059)
        ·
          refine ⟨309020185882534249145893589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206013457255022832763929059 309020185882534249145893589)
          ·
            refine ⟨7242660606621896464356881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 309020185882534249145893589 7242660606621896464356881)
            ·
              refine ⟨5431995454966422348267661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7242660606621896464356881 5431995454966422348267661)
              ·
                refine ⟨2036998295612408380600373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5431995454966422348267661 2036998295612408380600373)
                ·
                  refine ⟨190968590213663285681285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2036998295612408380600373 190968590213663285681285)
                  ·
                    rfl

theorem cell22_1673595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 3, 5].length) (baseStart_1673595 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1673595 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1673595 prefixEnd_1673595 := by exact prefixLift 1673595
  have htrace : WordTrace (prefixWord ++ tailWord_1673595) baseStart_1673595 baseEnd_1673595 := by
    simpa [prefixWord, tailWord_1673595, baseEnd_1673595] using wordTrace_append hprefix tailTrace_1673595
  have hstable : (prefixWord ++ tailWord_1673595).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1673595).length < 2 ^ (prefixWord ++ tailWord_1673595).sum := by decide
  have hdescent : baseEnd_1673595 < baseStart_1673595 := by decide
  rcases family_descends (prefixWord ++ tailWord_1673595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1673622 : List Nat := [5, 3, 1, 2, 2, 1, 1, 2, 2, 3]
def baseStart_1673622 : Nat := 118140960795 + 1673622 * 2 ^ 59
def prefixEnd_1673622 : Nat := 4983230072969 + 3 ^ 40 * 1673622 * 2
def baseEnd_1673622 : Nat := 572915013292770786618773

theorem tailTrace_1673622 : CollatzResearch.WordTrace tailWord_1673622 prefixEnd_1673622 572915013292770786618773 := by
  unfold tailWord_1673622
  simp only [CollatzResearch.WordTrace]
  refine ⟨3815125571422550045404445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40694672761840533817647413 3815125571422550045404445)
  ·
    refine ⟨1430672089283456267026667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3815125571422550045404445 1430672089283456267026667)
    ·
      refine ⟨2146008133925184400540001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1430672089283456267026667 2146008133925184400540001)
      ·
        refine ⟨1609506100443888300405001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2146008133925184400540001 1609506100443888300405001)
        ·
          refine ⟨1207129575332916225303751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1609506100443888300405001 1207129575332916225303751)
          ·
            refine ⟨1810694362999374337955627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1207129575332916225303751 1810694362999374337955627)
            ·
              refine ⟨2716041544499061506933441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1810694362999374337955627 2716041544499061506933441)
              ·
                refine ⟨2037031158374296130200081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2716041544499061506933441 2037031158374296130200081)
                ·
                  refine ⟨1527773368780722097650061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2037031158374296130200081 1527773368780722097650061)
                  ·
                    refine ⟨572915013292770786618773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1527773368780722097650061 572915013292770786618773)
                    ·
                      rfl

theorem cell22_1673622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_1673622 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1673622 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1673622 prefixEnd_1673622 := by exact prefixLift 1673622
  have htrace : WordTrace (prefixWord ++ tailWord_1673622) baseStart_1673622 baseEnd_1673622 := by
    simpa [prefixWord, tailWord_1673622, baseEnd_1673622] using wordTrace_append hprefix tailTrace_1673622
  have hstable : (prefixWord ++ tailWord_1673622).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1673622).length < 2 ^ (prefixWord ++ tailWord_1673622).sum := by decide
  have hdescent : baseEnd_1673622 < baseStart_1673622 := by decide
  rcases family_descends (prefixWord ++ tailWord_1673622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1673629 : List Nat := [1, 4, 2, 1, 4, 2, 1, 2, 5]
def baseStart_1673629 : Nat := 118140960795 + 1673629 * 2 ^ 59
def prefixEnd_1673629 : Nat := 4983230072969 + 3 ^ 40 * 1673629 * 2
def baseEnd_1673629 : Nat := 190972469845275033897917

theorem tailTrace_1673629 : CollatzResearch.WordTrace tailWord_1673629 prefixEnd_1673629 190972469845275033897917 := by
  unfold tailWord_1673629
  simp only [CollatzResearch.WordTrace]
  refine ⟨61042264453735440921975941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40694842969156960614650627 61042264453735440921975941)
  ·
    refine ⟨11445424585075395172870489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61042264453735440921975941 11445424585075395172870489)
    ·
      refine ⟨8584068438806546379652867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11445424585075395172870489 8584068438806546379652867)
      ·
        refine ⟨12876102658209819569479301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8584068438806546379652867 12876102658209819569479301)
        ·
          refine ⟨2414269248414341169277369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12876102658209819569479301 2414269248414341169277369)
          ·
            refine ⟨1810701936310755876958027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2414269248414341169277369 1810701936310755876958027)
            ·
              refine ⟨2716052904466133815437041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1810701936310755876958027 2716052904466133815437041)
              ·
                refine ⟨2037039678349600361577781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2716052904466133815437041 2037039678349600361577781)
                ·
                  refine ⟨190972469845275033897917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2037039678349600361577781 190972469845275033897917)
                  ·
                    rfl

theorem cell22_1673629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 1, 2, 5].length) (baseStart_1673629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1673629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1673629 prefixEnd_1673629 := by exact prefixLift 1673629
  have htrace : WordTrace (prefixWord ++ tailWord_1673629) baseStart_1673629 baseEnd_1673629 := by
    simpa [prefixWord, tailWord_1673629, baseEnd_1673629] using wordTrace_append hprefix tailTrace_1673629
  have hstable : (prefixWord ++ tailWord_1673629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1673629).length < 2 ^ (prefixWord ++ tailWord_1673629).sum := by decide
  have hdescent : baseEnd_1673629 < baseStart_1673629 := by decide
  rcases family_descends (prefixWord ++ tailWord_1673629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1673672 : List Nat := [2, 1, 3, 1, 3, 2, 1, 2, 4, 3]
def baseStart_1673672 : Nat := 118140960795 + 1673672 * 2 ^ 59
def prefixEnd_1673672 : Nat := 4983230072969 + 3 ^ 40 * 1673672 * 2
def baseEnd_1673672 : Nat := 572932129314587322868619

theorem tailTrace_1673672 : CollatzResearch.WordTrace tailWord_1673672 prefixEnd_1673672 572932129314587322868619 := by
  unfold tailWord_1673672
  simp only [CollatzResearch.WordTrace]
  refine ⟨30521916396289829632895635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40695888528386439510527513 30521916396289829632895635)
  ·
    refine ⟨45782874594434744449343453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30521916396289829632895635 45782874594434744449343453)
    ·
      refine ⟨17168577972913029168503795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45782874594434744449343453 17168577972913029168503795)
      ·
        refine ⟨25752866959369543752755693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17168577972913029168503795 25752866959369543752755693)
        ·
          refine ⟨9657325109763578907283385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25752866959369543752755693 9657325109763578907283385)
          ·
            refine ⟨7242993832322684180462539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9657325109763578907283385 7242993832322684180462539)
            ·
              refine ⟨10864490748484026270693809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7242993832322684180462539 10864490748484026270693809)
              ·
                refine ⟨8148368061363019703020357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10864490748484026270693809 8148368061363019703020357)
                ·
                  refine ⟨1527819011505566194316317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8148368061363019703020357 1527819011505566194316317)
                  ·
                    refine ⟨572932129314587322868619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1527819011505566194316317 572932129314587322868619)
                    ·
                      rfl

theorem cell22_1673672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 2, 4, 3].length) (baseStart_1673672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1673672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1673672 prefixEnd_1673672 := by exact prefixLift 1673672
  have htrace : WordTrace (prefixWord ++ tailWord_1673672) baseStart_1673672 baseEnd_1673672 := by
    simpa [prefixWord, tailWord_1673672, baseEnd_1673672] using wordTrace_append hprefix tailTrace_1673672
  have hstable : (prefixWord ++ tailWord_1673672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1673672).length < 2 ^ (prefixWord ++ tailWord_1673672).sum := by decide
  have hdescent : baseEnd_1673672 < baseStart_1673672 := by decide
  rcases family_descends (prefixWord ++ tailWord_1673672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1673685 : List Nat := [1, 3, 2, 3, 1, 2, 10]
def baseStart_1673685 : Nat := 118140960795 + 1673685 * 2 ^ 59
def prefixEnd_1673685 : Nat := 4983230072969 + 3 ^ 40 * 1673685 * 2
def baseEnd_1673685 : Nat := 21219873314083689714577

theorem tailTrace_1673685 : CollatzResearch.WordTrace tailWord_1673685 prefixEnd_1673685 21219873314083689714577 := by
  unfold tailWord_1673685
  simp only [CollatzResearch.WordTrace]
  refine ⟨61044306941532562486014509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40696204627688374990676339 61044306941532562486014509)
  ·
    refine ⟨22891615103074710932255441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61044306941532562486014509 22891615103074710932255441)
    ·
      refine ⟨17168711327306033199191581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22891615103074710932255441 17168711327306033199191581)
      ·
        refine ⟨6438266747739762449696843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17168711327306033199191581 6438266747739762449696843)
        ·
          refine ⟨9657400121609643674545265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6438266747739762449696843 9657400121609643674545265)
          ·
            refine ⟨7243050091207232755908949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9657400121609643674545265 7243050091207232755908949)
            ·
              refine ⟨21219873314083689714577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 7243050091207232755908949 21219873314083689714577)
              ·
                rfl

theorem cell22_1673685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 10].length) (baseStart_1673685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1673685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1673685 prefixEnd_1673685 := by exact prefixLift 1673685
  have htrace : WordTrace (prefixWord ++ tailWord_1673685) baseStart_1673685 baseEnd_1673685 := by
    simpa [prefixWord, tailWord_1673685, baseEnd_1673685] using wordTrace_append hprefix tailTrace_1673685
  have hstable : (prefixWord ++ tailWord_1673685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1673685).length < 2 ^ (prefixWord ++ tailWord_1673685).sum := by decide
  have hdescent : baseEnd_1673685 < baseStart_1673685 := by decide
  rcases family_descends (prefixWord ++ tailWord_1673685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1673706 : List Nat := [3, 1, 3, 1, 3, 1, 4, 1, 2, 3]
def baseStart_1673706 : Nat := 118140960795 + 1673706 * 2 ^ 59
def prefixEnd_1673706 : Nat := 4983230072969 + 3 ^ 40 * 1673706 * 2
def baseEnd_1673706 : Nat := 572943768209422567518515

theorem tailTrace_1673706 : CollatzResearch.WordTrace tailWord_1673706 prefixEnd_1673706 572943768209422567518515 := by
  unfold tailWord_1673706
  simp only [CollatzResearch.WordTrace]
  refine ⟨15261268218614120768132243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40696715249637655381685981 15261268218614120768132243)
  ·
    refine ⟨22891902327921181152198365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15261268218614120768132243 22891902327921181152198365)
    ·
      refine ⟨8584463372970442932074387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22891902327921181152198365 8584463372970442932074387)
      ·
        refine ⟨12876695059455664398111581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8584463372970442932074387 12876695059455664398111581)
        ·
          refine ⟨4828760647295874149291843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12876695059455664398111581 4828760647295874149291843)
          ·
            refine ⟨7243140970943811223937765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4828760647295874149291843 7243140970943811223937765)
            ·
              refine ⟨1358088932051964604488331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7243140970943811223937765 1358088932051964604488331)
              ·
                refine ⟨2037133398077946906732497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1358088932051964604488331 2037133398077946906732497)
                ·
                  refine ⟨1527850048558460180049373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2037133398077946906732497 1527850048558460180049373)
                  ·
                    refine ⟨572943768209422567518515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1527850048558460180049373 572943768209422567518515)
                    ·
                      rfl

theorem cell22_1673706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 4, 1, 2, 3].length) (baseStart_1673706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1673706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1673706 prefixEnd_1673706 := by exact prefixLift 1673706
  have htrace : WordTrace (prefixWord ++ tailWord_1673706) baseStart_1673706 baseEnd_1673706 := by
    simpa [prefixWord, tailWord_1673706, baseEnd_1673706] using wordTrace_append hprefix tailTrace_1673706
  have hstable : (prefixWord ++ tailWord_1673706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1673706).length < 2 ^ (prefixWord ++ tailWord_1673706).sum := by decide
  have hdescent : baseEnd_1673706 < baseStart_1673706 := by decide
  rcases family_descends (prefixWord ++ tailWord_1673706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1673747 : List Nat := [1, 1, 1, 2, 1, 5, 4, 2, 5]
def baseStart_1673747 : Nat := 118140960795 + 1673747 * 2 ^ 59
def prefixEnd_1673747 : Nat := 4983230072969 + 3 ^ 40 * 1673747 * 2
def baseEnd_1673747 : Nat := 190985934449104042414463

theorem tailTrace_1673747 : CollatzResearch.WordTrace tailWord_1673747 prefixEnd_1673747 190985934449104042414463 := by
  unfold tailWord_1673747
  simp only [CollatzResearch.WordTrace]
  refine ⟨61046568267307947074771495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40697712178205298049847663 61046568267307947074771495)
  ·
    refine ⟨91569852400961920612157243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61046568267307947074771495 91569852400961920612157243)
    ·
      refine ⟨137354778601442880918235865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91569852400961920612157243 137354778601442880918235865)
      ·
        refine ⟨103016083951082160688676899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137354778601442880918235865 103016083951082160688676899)
        ·
          refine ⟨154524125926623241033015349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103016083951082160688676899 154524125926623241033015349)
          ·
            refine ⟨14486636805620928846845189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 154524125926623241033015349 14486636805620928846845189)
            ·
              refine ⟨2716244401053924158783473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14486636805620928846845189 2716244401053924158783473)
              ·
                refine ⟨2037183300790443119087605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2716244401053924158783473 2037183300790443119087605)
                ·
                  refine ⟨190985934449104042414463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2037183300790443119087605 190985934449104042414463)
                  ·
                    rfl

theorem cell22_1673747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 4, 2, 5].length) (baseStart_1673747 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1673747 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1673747 prefixEnd_1673747 := by exact prefixLift 1673747
  have htrace : WordTrace (prefixWord ++ tailWord_1673747) baseStart_1673747 baseEnd_1673747 := by
    simpa [prefixWord, tailWord_1673747, baseEnd_1673747] using wordTrace_append hprefix tailTrace_1673747
  have hstable : (prefixWord ++ tailWord_1673747).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1673747).length < 2 ^ (prefixWord ++ tailWord_1673747).sum := by decide
  have hdescent : baseEnd_1673747 < baseStart_1673747 := by decide
  rcases family_descends (prefixWord ++ tailWord_1673747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1673777 : List Nat := [1, 2, 2, 3, 1, 1, 4, 1, 3, 4]
def baseStart_1673777 : Nat := 118140960795 + 1673777 * 2 ^ 59
def prefixEnd_1673777 : Nat := 4983230072969 + 3 ^ 40 * 1673777 * 2
def baseEnd_1673777 : Nat := 572968072960402048993297

theorem tailTrace_1673777 : CollatzResearch.WordTrace tailWord_1673777 prefixEnd_1673777 572968072960402048993297 := by
  unfold tailWord_1673777
  simp only [CollatzResearch.WordTrace]
  refine ⟨61047662457199262198363585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40698441638132841465575723 61047662457199262198363585)
  ·
    refine ⟨45785746842899446648772689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61047662457199262198363585 45785746842899446648772689)
    ·
      refine ⟨34339310132174584986579517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45785746842899446648772689 34339310132174584986579517)
      ·
        refine ⟨12877241299565469369967319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34339310132174584986579517 12877241299565469369967319)
        ·
          refine ⟨19315861949348204054950979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12877241299565469369967319 19315861949348204054950979)
          ·
            refine ⟨28973792924022306082426469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19315861949348204054950979 28973792924022306082426469)
            ·
              refine ⟨5432586173254182390454963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28973792924022306082426469 5432586173254182390454963)
              ·
                refine ⟨8148879259881273585682445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5432586173254182390454963 8148879259881273585682445)
                ·
                  refine ⟨3055829722455477594630917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8148879259881273585682445 3055829722455477594630917)
                  ·
                    refine ⟨572968072960402048993297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3055829722455477594630917 572968072960402048993297)
                    ·
                      rfl

theorem cell22_1673777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 1, 3, 4].length) (baseStart_1673777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1673777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1673777 prefixEnd_1673777 := by exact prefixLift 1673777
  have htrace : WordTrace (prefixWord ++ tailWord_1673777) baseStart_1673777 baseEnd_1673777 := by
    simpa [prefixWord, tailWord_1673777, baseEnd_1673777] using wordTrace_append hprefix tailTrace_1673777
  have hstable : (prefixWord ++ tailWord_1673777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1673777).length < 2 ^ (prefixWord ++ tailWord_1673777).sum := by decide
  have hdescent : baseEnd_1673777 < baseStart_1673777 := by decide
  rcases family_descends (prefixWord ++ tailWord_1673777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1673798 : List Nat := [6, 1, 1, 1, 2, 3, 1, 2, 5]
def baseStart_1673798 : Nat := 118140960795 + 1673798 * 2 ^ 59
def prefixEnd_1673798 : Nat := 4983230072969 + 3 ^ 40 * 1673798 * 2
def baseEnd_1673798 : Nat := 190991753896521664739411

theorem tailTrace_1673798 : CollatzResearch.WordTrace tailWord_1673798 prefixEnd_1673798 190991753896521664739411 := by
  unfold tailWord_1673798
  simp only [CollatzResearch.WordTrace]
  refine ⟨1907763387191349462027439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 40698952260082121856585365 1907763387191349462027439)
  ·
    refine ⟨2861645080787024193041159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1907763387191349462027439 2861645080787024193041159)
    ·
      refine ⟨4292467621180536289561739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2861645080787024193041159 4292467621180536289561739)
      ·
        refine ⟨6438701431770804434342609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4292467621180536289561739 6438701431770804434342609)
        ·
          refine ⟨4829026073828103325756957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6438701431770804434342609 4829026073828103325756957)
          ·
            refine ⟨1810884777685538747158859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4829026073828103325756957 1810884777685538747158859)
            ·
              refine ⟨2716327166528308120738289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1810884777685538747158859 2716327166528308120738289)
              ·
                refine ⟨2037245374896231090553717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2716327166528308120738289 2037245374896231090553717)
                ·
                  refine ⟨190991753896521664739411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2037245374896231090553717 190991753896521664739411)
                  ·
                    rfl

theorem cell22_1673798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 1, 2, 5].length) (baseStart_1673798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1673798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1673798 prefixEnd_1673798 := by exact prefixLift 1673798
  have htrace : WordTrace (prefixWord ++ tailWord_1673798) baseStart_1673798 baseEnd_1673798 := by
    simpa [prefixWord, tailWord_1673798, baseEnd_1673798] using wordTrace_append hprefix tailTrace_1673798
  have hstable : (prefixWord ++ tailWord_1673798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1673798).length < 2 ^ (prefixWord ++ tailWord_1673798).sum := by decide
  have hdescent : baseEnd_1673798 < baseStart_1673798 := by decide
  rcases family_descends (prefixWord ++ tailWord_1673798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1673809 : List Nat := [1, 2, 2, 1, 3, 3, 2, 4, 4]
def baseStart_1673809 : Nat := 118140960795 + 1673809 * 2 ^ 59
def prefixEnd_1673809 : Nat := 4983230072969 + 3 ^ 40 * 1673809 * 2
def baseEnd_1673809 : Nat := 190993009071454877397733

theorem tailTrace_1673809 : CollatzResearch.WordTrace tailWord_1673809 prefixEnd_1673809 190993009071454877397733 := by
  unfold tailWord_1673809
  simp only [CollatzResearch.WordTrace]
  refine ⟨61048829593083331663528481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40699219728722221109018987 61048829593083331663528481)
  ·
    refine ⟨45786622194812498747646361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61048829593083331663528481 45786622194812498747646361)
    ·
      refine ⟨34339966646109374060734771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45786622194812498747646361 34339966646109374060734771)
      ·
        refine ⟨51509949969164061091102157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34339966646109374060734771 51509949969164061091102157)
        ·
          refine ⟨19316231238436522909163309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51509949969164061091102157 19316231238436522909163309)
          ·
            refine ⟨7243586714413696090936241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19316231238436522909163309 7243586714413696090936241)
            ·
              refine ⟨5432690035810272068202181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7243586714413696090936241 5432690035810272068202181)
              ·
                refine ⟨1018629381714426012787909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5432690035810272068202181 1018629381714426012787909)
                ·
                  refine ⟨190993009071454877397733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1018629381714426012787909 190993009071454877397733)
                  ·
                    rfl

theorem cell22_1673809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 4, 4].length) (baseStart_1673809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1673809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1673809 prefixEnd_1673809 := by exact prefixLift 1673809
  have htrace : WordTrace (prefixWord ++ tailWord_1673809) baseStart_1673809 baseEnd_1673809 := by
    simpa [prefixWord, tailWord_1673809, baseEnd_1673809] using wordTrace_append hprefix tailTrace_1673809
  have hstable : (prefixWord ++ tailWord_1673809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1673809).length < 2 ^ (prefixWord ++ tailWord_1673809).sum := by decide
  have hdescent : baseEnd_1673809 < baseStart_1673809 := by decide
  rcases family_descends (prefixWord ++ tailWord_1673809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1673824 : List Nat := [2, 1, 1, 3, 2, 1, 2, 5, 2, 3]
def baseStart_1673824 : Nat := 118140960795 + 1673824 * 2 ^ 59
def prefixEnd_1673824 : Nat := 4983230072969 + 3 ^ 40 * 1673824 * 2
def baseEnd_1673824 : Nat := 572984162020909593068153

theorem tailTrace_1673824 : CollatzResearch.WordTrace tailWord_1673824 prefixEnd_1673824 572984162020909593068153 := by
  unfold tailWord_1673824
  simp only [CollatzResearch.WordTrace]
  refine ⟨30524688344014494612662263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40699584458685992816883017 30524688344014494612662263)
  ·
    refine ⟨45787032516021741918993395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30524688344014494612662263 45787032516021741918993395)
    ·
      refine ⟨68680548774032612878490093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45787032516021741918993395 68680548774032612878490093)
      ·
        refine ⟨25755205790262229829433785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68680548774032612878490093 25755205790262229829433785)
        ·
          refine ⟨19316404342696672372075339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25755205790262229829433785 19316404342696672372075339)
          ·
            refine ⟨28974606514045008558113009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19316404342696672372075339 28974606514045008558113009)
            ·
              refine ⟨21730954885533756418584757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28974606514045008558113009 21730954885533756418584757)
              ·
                refine ⟨2037277020518789664242321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21730954885533756418584757 2037277020518789664242321)
                ·
                  refine ⟨1527957765389092248181741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2037277020518789664242321 1527957765389092248181741)
                  ·
                    refine ⟨572984162020909593068153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1527957765389092248181741 572984162020909593068153)
                    ·
                      rfl

theorem cell22_1673824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 5, 2, 3].length) (baseStart_1673824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1673824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1673824 prefixEnd_1673824 := by exact prefixLift 1673824
  have htrace : WordTrace (prefixWord ++ tailWord_1673824) baseStart_1673824 baseEnd_1673824 := by
    simpa [prefixWord, tailWord_1673824, baseEnd_1673824] using wordTrace_append hprefix tailTrace_1673824
  have hstable : (prefixWord ++ tailWord_1673824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1673824).length < 2 ^ (prefixWord ++ tailWord_1673824).sum := by decide
  have hdescent : baseEnd_1673824 < baseStart_1673824 := by decide
  rcases family_descends (prefixWord ++ tailWord_1673824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1673886 : List Nat := [4, 3, 1, 1, 1, 1, 2, 1, 5, 3]
def baseStart_1673886 : Nat := 118140960795 + 1673886 * 2 ^ 59
def prefixEnd_1673886 : Nat := 4983230072969 + 3 ^ 40 * 1673886 * 2
def baseEnd_1673886 : Nat := 573005385887962098017963

theorem tailTrace_1673886 : CollatzResearch.WordTrace tailWord_1673886 prefixEnd_1673886 573005385887962098017963 := by
  unfold tailWord_1673886
  simp only [CollatzResearch.WordTrace]
  refine ⟨7631454751725546726760189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40701092009202915876054341 7631454751725546726760189)
  ·
    refine ⟨2861795531897080022535071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7631454751725546726760189 2861795531897080022535071)
    ·
      refine ⟨4292693297845620033802607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2861795531897080022535071 4292693297845620033802607)
      ·
        refine ⟨6439039946768430050703911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4292693297845620033802607 6439039946768430050703911)
        ·
          refine ⟨9658559920152645076055867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6439039946768430050703911 9658559920152645076055867)
          ·
            refine ⟨14487839880228967614083801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9658559920152645076055867 14487839880228967614083801)
            ·
              refine ⟨10865879910171725710562851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14487839880228967614083801 10865879910171725710562851)
              ·
                refine ⟨16298819865257588565844277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10865879910171725710562851 16298819865257588565844277)
                ·
                  refine ⟨1528014362367898928047901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16298819865257588565844277 1528014362367898928047901)
                  ·
                    refine ⟨573005385887962098017963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1528014362367898928047901 573005385887962098017963)
                    ·
                      rfl

theorem cell22_1673886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 1, 5, 3].length) (baseStart_1673886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1673886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1673886 prefixEnd_1673886 := by exact prefixLift 1673886
  have htrace : WordTrace (prefixWord ++ tailWord_1673886) baseStart_1673886 baseEnd_1673886 := by
    simpa [prefixWord, tailWord_1673886, baseEnd_1673886] using wordTrace_append hprefix tailTrace_1673886
  have hstable : (prefixWord ++ tailWord_1673886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1673886).length < 2 ^ (prefixWord ++ tailWord_1673886).sum := by decide
  have hdescent : baseEnd_1673886 < baseStart_1673886 := by decide
  rcases family_descends (prefixWord ++ tailWord_1673886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1673920 : List Nat := [2, 1, 1, 2, 4, 4, 2, 2, 1, 3]
def baseStart_1673920 : Nat := 118140960795 + 1673920 * 2 ^ 59
def prefixEnd_1673920 : Nat := 4983230072969 + 3 ^ 40 * 1673920 * 2
def baseEnd_1673920 : Nat := 573017024782797342667859

theorem tailTrace_1673920 : CollatzResearch.WordTrace tailWord_1673920 prefixEnd_1673920 573017024782797342667859 := by
  unfold tailWord_1673920
  simp only [CollatzResearch.WordTrace]
  refine ⟨30526439047840598810409607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40701918730454131747212809 30526439047840598810409607)
  ·
    refine ⟨45789658571760898215614411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30526439047840598810409607 45789658571760898215614411)
    ·
      refine ⟨68684487857641347323421617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45789658571760898215614411 68684487857641347323421617)
      ·
        refine ⟨51513365893231010492566213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68684487857641347323421617 51513365893231010492566213)
        ·
          refine ⟨9658756104980814467356165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51513365893231010492566213 9658756104980814467356165)
          ·
            refine ⟨1811016769683902712629281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9658756104980814467356165 1811016769683902712629281)
            ·
              refine ⟨1358262577262927034471961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1811016769683902712629281 1358262577262927034471961)
              ·
                refine ⟨1018696932947195275853971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1358262577262927034471961 1018696932947195275853971)
                ·
                  refine ⟨1528045399420792913780957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1018696932947195275853971 1528045399420792913780957)
                  ·
                    refine ⟨573017024782797342667859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1528045399420792913780957 573017024782797342667859)
                    ·
                      rfl

theorem cell22_1673920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 2, 2, 1, 3].length) (baseStart_1673920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1673920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1673920 prefixEnd_1673920 := by exact prefixLift 1673920
  have htrace : WordTrace (prefixWord ++ tailWord_1673920) baseStart_1673920 baseEnd_1673920 := by
    simpa [prefixWord, tailWord_1673920, baseEnd_1673920] using wordTrace_append hprefix tailTrace_1673920
  have hstable : (prefixWord ++ tailWord_1673920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1673920).length < 2 ^ (prefixWord ++ tailWord_1673920).sum := by decide
  have hdescent : baseEnd_1673920 < baseStart_1673920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1673920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1673944 : List Nat := [2, 1, 2, 2, 3, 3, 1, 2, 6]
def baseStart_1673944 : Nat := 118140960795 + 1673944 * 2 ^ 59
def prefixEnd_1673944 : Nat := 4983230072969 + 3 ^ 40 * 1673944 * 2
def baseEnd_1673944 : Nat := 191008413491089760022595

theorem tailTrace_1673944 : CollatzResearch.WordTrace tailWord_1673944 prefixEnd_1673944 191008413491089760022595 := by
  unfold tailWord_1673944
  simp only [CollatzResearch.WordTrace]
  refine ⟨30526876723797124859846443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40702502298396166479795257 30526876723797124859846443)
  ·
    refine ⟨45790315085695687289769665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30526876723797124859846443 45790315085695687289769665)
    ·
      refine ⟨34342736314271765467327249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45790315085695687289769665 34342736314271765467327249)
      ·
        refine ⟨25757052235703824100495437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34342736314271765467327249 25757052235703824100495437)
        ·
          refine ⟨9658894588388934037685789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25757052235703824100495437 9658894588388934037685789)
          ·
            refine ⟨3622085470645850264132171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9658894588388934037685789 3622085470645850264132171)
            ·
              refine ⟨5433128205968775396198257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3622085470645850264132171 5433128205968775396198257)
              ·
                refine ⟨4074846154476581547148693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5433128205968775396198257 4074846154476581547148693)
                ·
                  refine ⟨191008413491089760022595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4074846154476581547148693 191008413491089760022595)
                  ·
                    rfl

theorem cell22_1673944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 2, 6].length) (baseStart_1673944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1673944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1673944 prefixEnd_1673944 := by exact prefixLift 1673944
  have htrace : WordTrace (prefixWord ++ tailWord_1673944) baseStart_1673944 baseEnd_1673944 := by
    simpa [prefixWord, tailWord_1673944, baseEnd_1673944] using wordTrace_append hprefix tailTrace_1673944
  have hstable : (prefixWord ++ tailWord_1673944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1673944).length < 2 ^ (prefixWord ++ tailWord_1673944).sum := by decide
  have hdescent : baseEnd_1673944 < baseStart_1673944 := by decide
  rcases family_descends (prefixWord ++ tailWord_1673944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1674034 : List Nat := [3, 2, 1, 1, 3, 1, 1, 3, 7]
def baseStart_1674034 : Nat := 118140960795 + 1674034 * 2 ^ 59
def prefixEnd_1674034 : Nat := 4983230072969 + 3 ^ 40 * 1674034 * 2
def baseEnd_1674034 : Nat := 191018683104179681772503

theorem tailTrace_1674034 : CollatzResearch.WordTrace tailWord_1674034 prefixEnd_1674034 191018683104179681772503 := by
  unfold tailWord_1674034
  simp only [CollatzResearch.WordTrace]
  refine ⟨15264259004317048772617289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40704690678178796726979437 15264259004317048772617289)
  ·
    refine ⟨11448194253237786579462967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15264259004317048772617289 11448194253237786579462967)
    ·
      refine ⟨17172291379856679869194451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11448194253237786579462967 17172291379856679869194451)
      ·
        refine ⟨25758437069785019803791677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17172291379856679869194451 25758437069785019803791677)
        ·
          refine ⟨9659413901169382426421879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25758437069785019803791677 9659413901169382426421879)
          ·
            refine ⟨14489120851754073639632819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9659413901169382426421879 14489120851754073639632819)
            ·
              refine ⟨21733681277631110459449229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14489120851754073639632819 21733681277631110459449229)
              ·
                refine ⟨8150130479111666422293461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21733681277631110459449229 8150130479111666422293461)
                ·
                  refine ⟨191018683104179681772503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8150130479111666422293461 191018683104179681772503)
                  ·
                    rfl

theorem cell22_1674034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 3, 7].length) (baseStart_1674034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1674034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1674034 prefixEnd_1674034 := by exact prefixLift 1674034
  have htrace : WordTrace (prefixWord ++ tailWord_1674034) baseStart_1674034 baseEnd_1674034 := by
    simpa [prefixWord, tailWord_1674034, baseEnd_1674034] using wordTrace_append hprefix tailTrace_1674034
  have hstable : (prefixWord ++ tailWord_1674034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1674034).length < 2 ^ (prefixWord ++ tailWord_1674034).sum := by decide
  have hdescent : baseEnd_1674034 < baseStart_1674034 := by decide
  rcases family_descends (prefixWord ++ tailWord_1674034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1674124 : List Nat := [2, 2, 1, 2, 1, 2, 2, 10]
def baseStart_1674124 : Nat := 118140960795 + 1674124 * 2 ^ 59
def prefixEnd_1674124 : Nat := 4983230072969 + 3 ^ 40 * 1674124 * 2
def baseEnd_1674124 : Nat := 63676317572423201174137

theorem tailTrace_1674124 : CollatzResearch.WordTrace tailWord_1674124 prefixEnd_1674124 63676317572423201174137 := by
  unfold tailWord_1674124
  simp only [CollatzResearch.WordTrace]
  refine ⟨30530159293471070230622713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40706879057961426974163617 30530159293471070230622713)
  ·
    refine ⟨22897619470103302672967035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30530159293471070230622713 22897619470103302672967035)
    ·
      refine ⟨34346429205154954009450553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22897619470103302672967035 34346429205154954009450553)
      ·
        refine ⟨25759821903866215507087915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34346429205154954009450553 25759821903866215507087915)
        ·
          refine ⟨38639732855799323260631873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25759821903866215507087915 38639732855799323260631873)
          ·
            refine ⟨28979799641849492445473905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38639732855799323260631873 28979799641849492445473905)
            ·
              refine ⟨21734849731387119334105429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28979799641849492445473905 21734849731387119334105429)
              ·
                refine ⟨63676317572423201174137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 21734849731387119334105429 63676317572423201174137)
                ·
                  rfl

theorem cell22_1674124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 10].length) (baseStart_1674124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1674124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1674124 prefixEnd_1674124 := by exact prefixLift 1674124
  have htrace : WordTrace (prefixWord ++ tailWord_1674124) baseStart_1674124 baseEnd_1674124 := by
    simpa [prefixWord, tailWord_1674124, baseEnd_1674124] using wordTrace_append hprefix tailTrace_1674124
  have hstable : (prefixWord ++ tailWord_1674124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1674124).length < 2 ^ (prefixWord ++ tailWord_1674124).sum := by decide
  have hdescent : baseEnd_1674124 < baseStart_1674124 := by decide
  rcases family_descends (prefixWord ++ tailWord_1674124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1674145 : List Nat := [1, 2, 3, 4, 1, 1, 3, 2, 2, 3]
def baseStart_1674145 : Nat := 118140960795 + 1674145 * 2 ^ 59
def prefixEnd_1674145 : Nat := 4983230072969 + 3 ^ 40 * 1674145 * 2
def baseEnd_1674145 : Nat := 573094046880971755792169

theorem tailTrace_1674145 : CollatzResearch.WordTrace tailWord_1674145 prefixEnd_1674145 573094046880971755792169 := by
  unfold tailWord_1674145
  simp only [CollatzResearch.WordTrace]
  refine ⟨61061084519866061047759889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40707389679910707365173259 61061084519866061047759889)
  ·
    refine ⟨45795813389899545785819917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61061084519866061047759889 45795813389899545785819917)
    ·
      refine ⟨17173430021212329669682469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45795813389899545785819917 17173430021212329669682469)
      ·
        refine ⟨3220018128977311813065463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17173430021212329669682469 3220018128977311813065463)
        ·
          refine ⟨4830027193465967719598195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3220018128977311813065463 4830027193465967719598195)
          ·
            refine ⟨7245040790198951579397293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4830027193465967719598195 7245040790198951579397293)
            ·
              refine ⟨2716890296324606842273985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7245040790198951579397293 2716890296324606842273985)
              ·
                refine ⟨2037667722243455131705489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2716890296324606842273985 2037667722243455131705489)
                ·
                  refine ⟨1528250791682591348779117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2037667722243455131705489 1528250791682591348779117)
                  ·
                    refine ⟨573094046880971755792169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1528250791682591348779117 573094046880971755792169)
                    ·
                      rfl

theorem cell22_1674145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 3, 2, 2, 3].length) (baseStart_1674145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1674145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1674145 prefixEnd_1674145 := by exact prefixLift 1674145
  have htrace : WordTrace (prefixWord ++ tailWord_1674145) baseStart_1674145 baseEnd_1674145 := by
    simpa [prefixWord, tailWord_1674145, baseEnd_1674145] using wordTrace_append hprefix tailTrace_1674145
  have hstable : (prefixWord ++ tailWord_1674145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1674145).length < 2 ^ (prefixWord ++ tailWord_1674145).sum := by decide
  have hdescent : baseEnd_1674145 < baseStart_1674145 := by decide
  rcases family_descends (prefixWord ++ tailWord_1674145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1674156 : List Nat := [2, 2, 1, 1, 1, 1, 2, 2, 7, 3]
def baseStart_1674156 : Nat := 118140960795 + 1674156 * 2 ^ 59
def prefixEnd_1674156 : Nat := 4983230072969 + 3 ^ 40 * 1674156 * 2
def baseEnd_1674156 : Nat := 573097812405771393767135

theorem tailTrace_1674156 : CollatzResearch.WordTrace tailWord_1674156 prefixEnd_1674156 573097812405771393767135 := by
  unfold tailWord_1674156
  simp only [CollatzResearch.WordTrace]
  refine ⟨30530742861413104963205161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40707657148550806617606881 30530742861413104963205161)
  ·
    refine ⟨22898057146059828722403871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30530742861413104963205161 22898057146059828722403871)
    ·
      refine ⟨34347085719089743083605807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22898057146059828722403871 34347085719089743083605807)
      ·
        refine ⟨51520628578634614625408711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34347085719089743083605807 51520628578634614625408711)
        ·
          refine ⟨77280942867951921938113067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51520628578634614625408711 77280942867951921938113067)
          ·
            refine ⟨115921414301927882907169601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77280942867951921938113067 115921414301927882907169601)
            ·
              refine ⟨86941060726445912180377201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115921414301927882907169601 86941060726445912180377201)
              ·
                refine ⟨65205795544834434135282901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86941060726445912180377201 65205795544834434135282901)
                ·
                  refine ⟨1528260833082057050045693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 65205795544834434135282901 1528260833082057050045693)
                  ·
                    refine ⟨573097812405771393767135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1528260833082057050045693 573097812405771393767135)
                    ·
                      rfl

theorem cell22_1674156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 3].length) (baseStart_1674156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1674156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1674156 prefixEnd_1674156 := by exact prefixLift 1674156
  have htrace : WordTrace (prefixWord ++ tailWord_1674156) baseStart_1674156 baseEnd_1674156 := by
    simpa [prefixWord, tailWord_1674156, baseEnd_1674156] using wordTrace_append hprefix tailTrace_1674156
  have hstable : (prefixWord ++ tailWord_1674156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1674156).length < 2 ^ (prefixWord ++ tailWord_1674156).sum := by decide
  have hdescent : baseEnd_1674156 < baseStart_1674156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1674156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1674207 : List Nat := [1, 1, 2, 3, 6, 1, 1, 1, 3, 3]
def baseStart_1674207 : Nat := 118140960795 + 1674207 * 2 ^ 59
def prefixEnd_1674207 : Nat := 4983230072969 + 3 ^ 40 * 1674207 * 2
def baseEnd_1674207 : Nat := 573115270748024260741979

theorem tailTrace_1674207 : CollatzResearch.WordTrace tailWord_1674207 prefixEnd_1674207 573115270748024260741979 := by
  unfold tailWord_1674207
  simp only [CollatzResearch.WordTrace]
  refine ⟨61063345845641445636516875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40708897230427630424344583 61063345845641445636516875)
  ·
    refine ⟨91595018768462168454775313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61063345845641445636516875 91595018768462168454775313)
    ·
      refine ⟨68696264076346626341081485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91595018768462168454775313 68696264076346626341081485)
      ·
        refine ⟨25761099028629984877905557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68696264076346626341081485 25761099028629984877905557)
        ·
          refine ⟨1207551516967030541151823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 25761099028629984877905557 1207551516967030541151823)
          ·
            refine ⟨1811327275450545811727735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1207551516967030541151823 1811327275450545811727735)
            ·
              refine ⟨2716990913175818717591603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1811327275450545811727735 2716990913175818717591603)
              ·
                refine ⟨4075486369763728076387405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2716990913175818717591603 4075486369763728076387405)
                ·
                  refine ⟨1528307388661398028645277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4075486369763728076387405 1528307388661398028645277)
                  ·
                    refine ⟨573115270748024260741979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1528307388661398028645277 573115270748024260741979)
                    ·
                      rfl

theorem cell22_1674207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 1, 1, 3, 3].length) (baseStart_1674207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1674207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1674207 prefixEnd_1674207 := by exact prefixLift 1674207
  have htrace : WordTrace (prefixWord ++ tailWord_1674207) baseStart_1674207 baseEnd_1674207 := by
    simpa [prefixWord, tailWord_1674207, baseEnd_1674207] using wordTrace_append hprefix tailTrace_1674207
  have hstable : (prefixWord ++ tailWord_1674207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1674207).length < 2 ^ (prefixWord ++ tailWord_1674207).sum := by decide
  have hdescent : baseEnd_1674207 < baseStart_1674207 := by decide
  rcases family_descends (prefixWord ++ tailWord_1674207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1674265 : List Nat := [1, 2, 1, 2, 1, 1, 8, 2, 4]
def baseStart_1674265 : Nat := 118140960795 + 1674265 * 2 ^ 59
def prefixEnd_1674265 : Nat := 4983230072969 + 3 ^ 40 * 1674265 * 2
def baseEnd_1674265 : Nat := 191045041777777147597267

theorem tailTrace_1674265 : CollatzResearch.WordTrace tailWord_1674265 prefixEnd_1674265 191045041777777147597267 := by
  unfold tailWord_1674265
  simp only [CollatzResearch.WordTrace]
  refine ⟨61065461279431321542128249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40710307519620881028085499 61065461279431321542128249)
  ·
    refine ⟨45799095959573491156596187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61065461279431321542128249 45799095959573491156596187)
    ·
      refine ⟨68698643939360236734894281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45799095959573491156596187 68698643939360236734894281)
      ·
        refine ⟨51523982954520177551170711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68698643939360236734894281 51523982954520177551170711)
        ·
          refine ⟨77285974431780266326756067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51523982954520177551170711 77285974431780266326756067)
          ·
            refine ⟨115928961647670399490134101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77285974431780266326756067 115928961647670399490134101)
            ·
              refine ⟨1358542519308637494025009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 115928961647670399490134101 1358542519308637494025009)
              ·
                refine ⟨1018906889481478120518757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1358542519308637494025009 1018906889481478120518757)
                ·
                  refine ⟨191045041777777147597267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1018906889481478120518757 191045041777777147597267)
                  ·
                    rfl

theorem cell22_1674265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 8, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 8, 2, 4].length) (baseStart_1674265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1674265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1674265 prefixEnd_1674265 := by exact prefixLift 1674265
  have htrace : WordTrace (prefixWord ++ tailWord_1674265) baseStart_1674265 baseEnd_1674265 := by
    simpa [prefixWord, tailWord_1674265, baseEnd_1674265] using wordTrace_append hprefix tailTrace_1674265
  have hstable : (prefixWord ++ tailWord_1674265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1674265).length < 2 ^ (prefixWord ++ tailWord_1674265).sum := by decide
  have hdescent : baseEnd_1674265 < baseStart_1674265 := by decide
  rcases family_descends (prefixWord ++ tailWord_1674265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1674310 : List Nat := [6, 1, 1, 1, 1, 3, 9]
def baseStart_1674310 : Nat := 118140960795 + 1674310 * 2 ^ 59
def prefixEnd_1674310 : Nat := 4983230072969 + 3 ^ 40 * 1674310 * 2
def baseEnd_1674310 : Nat := 21227797398258012052469

theorem tailTrace_1674310 : CollatzResearch.WordTrace tailWord_1674310 prefixEnd_1674310 21227797398258012052469 := by
  unfold tailWord_1674310
  simp only [CollatzResearch.WordTrace]
  refine ⟨1908346955133384194609887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 40711401709512196151677589 1908346955133384194609887)
  ·
    refine ⟨2862520432700076291914831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1908346955133384194609887 2862520432700076291914831)
    ·
      refine ⟨4293780649050114437872247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2862520432700076291914831 4293780649050114437872247)
      ·
        refine ⟨6440670973575171656808371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4293780649050114437872247 6440670973575171656808371)
        ·
          refine ⟨9661006460362757485212557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6440670973575171656808371 9661006460362757485212557)
          ·
            refine ⟨3622877422636034056954709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9661006460362757485212557 3622877422636034056954709)
            ·
              refine ⟨21227797398258012052469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3622877422636034056954709 21227797398258012052469)
              ·
                rfl

theorem cell22_1674310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 9].length) (baseStart_1674310 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1674310 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1674310 prefixEnd_1674310 := by exact prefixLift 1674310
  have htrace : WordTrace (prefixWord ++ tailWord_1674310) baseStart_1674310 baseEnd_1674310 := by
    simpa [prefixWord, tailWord_1674310, baseEnd_1674310] using wordTrace_append hprefix tailTrace_1674310
  have hstable : (prefixWord ++ tailWord_1674310).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1674310).length < 2 ^ (prefixWord ++ tailWord_1674310).sum := by decide
  have hdescent : baseEnd_1674310 < baseStart_1674310 := by decide
  rcases family_descends (prefixWord ++ tailWord_1674310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1674325 : List Nat := [1, 3, 2, 2, 1, 2, 4, 1, 3, 3]
def baseStart_1674325 : Nat := 118140960795 + 1674325 * 2 ^ 59
def prefixEnd_1674325 : Nat := 4983230072969 + 3 ^ 40 * 1674325 * 2
def baseEnd_1674325 : Nat := 573155664559511286291617

theorem tailTrace_1674325 : CollatzResearch.WordTrace tailWord_1674325 prefixEnd_1674325 573155664559511286291617 := by
  unfold tailWord_1674325
  simp only [CollatzResearch.WordTrace]
  refine ⟨61067649659213951789312429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40711766439475967859541619 61067649659213951789312429)
  ·
    refine ⟨22900368622205231920992161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61067649659213951789312429 22900368622205231920992161)
    ·
      refine ⟨17175276466653923940744121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22900368622205231920992161 17175276466653923940744121)
      ·
        refine ⟨12881457349990442955558091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17175276466653923940744121 12881457349990442955558091)
        ·
          refine ⟨19322186024985664433337137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12881457349990442955558091 19322186024985664433337137)
          ·
            refine ⟨14491639518739248325002853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19322186024985664433337137 14491639518739248325002853)
            ·
              refine ⟨2717182409763609060938035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14491639518739248325002853 2717182409763609060938035)
              ·
                refine ⟨4075773614645413591407053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2717182409763609060938035 4075773614645413591407053)
                ·
                  refine ⟨1528415105492030096777645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4075773614645413591407053 1528415105492030096777645)
                  ·
                    refine ⟨573155664559511286291617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1528415105492030096777645 573155664559511286291617)
                    ·
                      rfl

theorem cell22_1674325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 4, 1, 3, 3].length) (baseStart_1674325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1674325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1674325 prefixEnd_1674325 := by exact prefixLift 1674325
  have htrace : WordTrace (prefixWord ++ tailWord_1674325) baseStart_1674325 baseEnd_1674325 := by
    simpa [prefixWord, tailWord_1674325, baseEnd_1674325] using wordTrace_append hprefix tailTrace_1674325
  have hstable : (prefixWord ++ tailWord_1674325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1674325).length < 2 ^ (prefixWord ++ tailWord_1674325).sum := by decide
  have hdescent : baseEnd_1674325 < baseStart_1674325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1674325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1674344 : List Nat := [2, 1, 4, 4, 2, 1, 2, 6]
def baseStart_1674344 : Nat := 118140960795 + 1674344 * 2 ^ 59
def prefixEnd_1674344 : Nat := 4983230072969 + 3 ^ 40 * 1674344 * 2
def baseEnd_1674344 : Nat := 63684685405311285562951

theorem tailTrace_1674344 : CollatzResearch.WordTrace tailWord_1674344 prefixEnd_1674344 63684685405311285562951 := by
  unfold tailWord_1674344
  simp only [CollatzResearch.WordTrace]
  refine ⟨30534171323072559017127043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40712228430763412022836057 30534171323072559017127043)
  ·
    refine ⟨45801256984608838525690565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30534171323072559017127043 45801256984608838525690565)
    ·
      refine ⟨8587735684614157223566981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45801256984608838525690565 8587735684614157223566981)
      ·
        refine ⟨1610200440865154479418809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8587735684614157223566981 1610200440865154479418809)
        ·
          refine ⟨1207650330648865859564107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1610200440865154479418809 1207650330648865859564107)
          ·
            refine ⟨1811475495973298789346161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1207650330648865859564107 1811475495973298789346161)
            ·
              refine ⟨1358606621979974092009621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1811475495973298789346161 1358606621979974092009621)
              ·
                refine ⟨63684685405311285562951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1358606621979974092009621 63684685405311285562951)
                ·
                  rfl

theorem cell22_1674344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 2, 6].length) (baseStart_1674344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1674344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1674344 prefixEnd_1674344 := by exact prefixLift 1674344
  have htrace : WordTrace (prefixWord ++ tailWord_1674344) baseStart_1674344 baseEnd_1674344 := by
    simpa [prefixWord, tailWord_1674344, baseEnd_1674344] using wordTrace_append hprefix tailTrace_1674344
  have hstable : (prefixWord ++ tailWord_1674344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1674344).length < 2 ^ (prefixWord ++ tailWord_1674344).sum := by decide
  have hdescent : baseEnd_1674344 < baseStart_1674344 := by decide
  rcases family_descends (prefixWord ++ tailWord_1674344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1674376 : List Nat := [2, 1, 3, 4, 2, 1, 3, 2, 1, 3]
def baseStart_1674376 : Nat := 118140960795 + 1674376 * 2 ^ 59
def prefixEnd_1674376 : Nat := 4983230072969 + 3 ^ 40 * 1674376 * 2
def baseEnd_1674376 : Nat := 573173122901764153266461

theorem tailTrace_1674376 : CollatzResearch.WordTrace tailWord_1674376 prefixEnd_1674376 573173122901764153266461 := by
  unfold tailWord_1674376
  simp only [CollatzResearch.WordTrace]
  refine ⟨30534754891014593749709491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40713006521352791666279321 30534754891014593749709491)
  ·
    refine ⟨45802132336521890624564237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30534754891014593749709491 45802132336521890624564237)
    ·
      refine ⟨17175799626195708984211589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45802132336521890624564237 17175799626195708984211589)
      ·
        refine ⟨3220462429911695434539673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17175799626195708984211589 3220462429911695434539673)
        ·
          refine ⟨2415346822433771575904755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3220462429911695434539673 2415346822433771575904755)
          ·
            refine ⟨3623020233650657363857133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2415346822433771575904755 3623020233650657363857133)
            ·
              refine ⟨1358632587618996511446425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3623020233650657363857133 1358632587618996511446425)
              ·
                refine ⟨1018974440714247383584819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1358632587618996511446425 1018974440714247383584819)
                ·
                  refine ⟨1528461661071371075377229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1018974440714247383584819 1528461661071371075377229)
                  ·
                    refine ⟨573173122901764153266461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1528461661071371075377229 573173122901764153266461)
                    ·
                      rfl

theorem cell22_1674376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 3, 2, 1, 3].length) (baseStart_1674376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1674376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1674376 prefixEnd_1674376 := by exact prefixLift 1674376
  have htrace : WordTrace (prefixWord ++ tailWord_1674376) baseStart_1674376 baseEnd_1674376 := by
    simpa [prefixWord, tailWord_1674376, baseEnd_1674376] using wordTrace_append hprefix tailTrace_1674376
  have hstable : (prefixWord ++ tailWord_1674376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1674376).length < 2 ^ (prefixWord ++ tailWord_1674376).sum := by decide
  have hdescent : baseEnd_1674376 < baseStart_1674376 := by decide
  rcases family_descends (prefixWord ++ tailWord_1674376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1674402 : List Nat := [3, 3, 1, 3, 2, 1, 1, 1, 3, 4]
def baseStart_1674402 : Nat := 118140960795 + 1674402 * 2 ^ 59
def prefixEnd_1674402 : Nat := 4983230072969 + 3 ^ 40 * 1674402 * 2
def baseEnd_1674402 : Nat := 573182023233108752116381

theorem tailTrace_1674402 : CollatzResearch.WordTrace tailWord_1674402 prefixEnd_1674402 573182023233108752116381 := by
  unfold tailWord_1674402
  simp only [CollatzResearch.WordTrace]
  refine ⟨15267614519983748484966365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40713638719956662626576973 15267614519983748484966365)
  ·
    refine ⟨5725355444993905681862387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15267614519983748484966365 5725355444993905681862387)
    ·
      refine ⟨8588033167490858522793581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5725355444993905681862387 8588033167490858522793581)
      ·
        refine ⟨3220512437809071946047593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8588033167490858522793581 3220512437809071946047593)
        ·
          refine ⟨2415384328356803959535695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3220512437809071946047593 2415384328356803959535695)
          ·
            refine ⟨3623076492535205939303543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2415384328356803959535695 3623076492535205939303543)
            ·
              refine ⟨5434614738802808908955315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3623076492535205939303543 5434614738802808908955315)
              ·
                refine ⟨8151922108204213363432973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5434614738802808908955315 8151922108204213363432973)
                ·
                  refine ⟨3056970790576580011287365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8151922108204213363432973 3056970790576580011287365)
                  ·
                    refine ⟨573182023233108752116381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3056970790576580011287365 573182023233108752116381)
                    ·
                      rfl

theorem cell22_1674402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 1, 3, 4].length) (baseStart_1674402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1674402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1674402 prefixEnd_1674402 := by exact prefixLift 1674402
  have htrace : WordTrace (prefixWord ++ tailWord_1674402) baseStart_1674402 baseEnd_1674402 := by
    simpa [prefixWord, tailWord_1674402, baseEnd_1674402] using wordTrace_append hprefix tailTrace_1674402
  have hstable : (prefixWord ++ tailWord_1674402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1674402).length < 2 ^ (prefixWord ++ tailWord_1674402).sum := by decide
  have hdescent : baseEnd_1674402 < baseStart_1674402 := by decide
  rcases family_descends (prefixWord ++ tailWord_1674402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1674428 : List Nat := [2, 2, 2, 3, 2, 11]
def baseStart_1674428 : Nat := 118140960795 + 1674428 * 2 ^ 59
def prefixEnd_1674428 : Nat := 4983230072969 + 3 ^ 40 * 1674428 * 2
def baseEnd_1674428 : Nat := 7076431155116708036621

theorem tailTrace_1674428 : CollatzResearch.WordTrace tailWord_1674428 prefixEnd_1674428 7076431155116708036621 := by
  unfold tailWord_1674428
  simp only [CollatzResearch.WordTrace]
  refine ⟨30535703188920400190155969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40714270918560533586874625 30535703188920400190155969)
  ·
    refine ⟨22901777391690300142616977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30535703188920400190155969 22901777391690300142616977)
    ·
      refine ⟨17176333043767725106962733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22901777391690300142616977 17176333043767725106962733)
      ·
        refine ⟨6441124891412896915111025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17176333043767725106962733 6441124891412896915111025)
        ·
          refine ⟨4830843668559672686333269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6441124891412896915111025 4830843668559672686333269)
          ·
            refine ⟨7076431155116708036621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 4830843668559672686333269 7076431155116708036621)
            ·
              rfl

theorem cell22_1674428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 11].length) (baseStart_1674428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1674428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1674428 prefixEnd_1674428 := by exact prefixLift 1674428
  have htrace : WordTrace (prefixWord ++ tailWord_1674428) baseStart_1674428 baseEnd_1674428 := by
    simpa [prefixWord, tailWord_1674428, baseEnd_1674428] using wordTrace_append hprefix tailTrace_1674428
  have hstable : (prefixWord ++ tailWord_1674428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1674428).length < 2 ^ (prefixWord ++ tailWord_1674428).sum := by decide
  have hdescent : baseEnd_1674428 < baseStart_1674428 := by decide
  rcases family_descends (prefixWord ++ tailWord_1674428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1674458 : List Nat := [3, 1, 1, 2, 2, 1, 1, 1, 4, 6]
def baseStart_1674458 : Nat := 118140960795 + 1674458 * 2 ^ 59
def prefixEnd_1674458 : Nat := 4983230072969 + 3 ^ 40 * 1674458 * 2
def baseEnd_1674458 : Nat := 573201193177543272716209

theorem tailTrace_1674458 : CollatzResearch.WordTrace tailWord_1674458 prefixEnd_1674458 573201193177543272716209 := by
  unfold tailWord_1674458
  simp only [CollatzResearch.WordTrace]
  refine ⟨15268125141933028875976007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40715000378488077002602685 15268125141933028875976007)
  ·
    refine ⟨22902187712899543313964011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15268125141933028875976007 22902187712899543313964011)
    ·
      refine ⟨34353281569349314970946017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22902187712899543313964011 34353281569349314970946017)
      ·
        refine ⟨25764961177011986228209513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34353281569349314970946017 25764961177011986228209513)
        ·
          refine ⟨19323720882758989671157135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25764961177011986228209513 19323720882758989671157135)
          ·
            refine ⟨28985581324138484506735703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19323720882758989671157135 28985581324138484506735703)
            ·
              refine ⟨43478371986207726760103555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28985581324138484506735703 43478371986207726760103555)
              ·
                refine ⟨65217557979311590140155333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43478371986207726760103555 65217557979311590140155333)
                ·
                  refine ⟨12228292121120923151279125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65217557979311590140155333 12228292121120923151279125)
                  ·
                    refine ⟨573201193177543272716209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12228292121120923151279125 573201193177543272716209)
                    ·
                      rfl

theorem cell22_1674458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 4, 6].length) (baseStart_1674458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1674458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1674458 prefixEnd_1674458 := by exact prefixLift 1674458
  have htrace : WordTrace (prefixWord ++ tailWord_1674458) baseStart_1674458 baseEnd_1674458 := by
    simpa [prefixWord, tailWord_1674458, baseEnd_1674458] using wordTrace_append hprefix tailTrace_1674458
  have hstable : (prefixWord ++ tailWord_1674458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1674458).length < 2 ^ (prefixWord ++ tailWord_1674458).sum := by decide
  have hdescent : baseEnd_1674458 < baseStart_1674458 := by decide
  rcases family_descends (prefixWord ++ tailWord_1674458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1674494 : List Nat := [4, 2, 2, 1, 1, 3, 2, 1, 3, 3]
def baseStart_1674494 : Nat := 118140960795 + 1674494 * 2 ^ 59
def prefixEnd_1674494 : Nat := 4983230072969 + 3 ^ 40 * 1674494 * 2
def baseEnd_1674494 : Nat := 573213516713251178816099

theorem tailTrace_1674494 : CollatzResearch.WordTrace tailWord_1674494 prefixEnd_1674494 573213516713251178816099 := by
  unfold tailWord_1674494
  simp only [CollatzResearch.WordTrace]
  refine ⟨7634226699450211706526817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40715875730401129101476357 7634226699450211706526817)
  ·
    refine ⟨5725670024587658779895113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7634226699450211706526817 5725670024587658779895113)
    ·
      refine ⟨4294252518440744084921335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5725670024587658779895113 4294252518440744084921335)
      ·
        refine ⟨6441378777661116127382003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4294252518440744084921335 6441378777661116127382003)
        ·
          refine ⟨9662068166491674191073005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6441378777661116127382003 9662068166491674191073005)
          ·
            refine ⟨3623275562434377821652377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9662068166491674191073005 3623275562434377821652377)
            ·
              refine ⟨2717456671825783366239283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3623275562434377821652377 2717456671825783366239283)
              ·
                refine ⟨4076185007738675049358925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2717456671825783366239283 4076185007738675049358925)
                ·
                  refine ⟨1528569377902003143509597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4076185007738675049358925 1528569377902003143509597)
                  ·
                    refine ⟨573213516713251178816099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1528569377902003143509597 573213516713251178816099)
                    ·
                      rfl

theorem cell22_1674494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 2, 1, 3, 3].length) (baseStart_1674494 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1674494 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1674494 prefixEnd_1674494 := by exact prefixLift 1674494
  have htrace : WordTrace (prefixWord ++ tailWord_1674494) baseStart_1674494 baseEnd_1674494 := by
    simpa [prefixWord, tailWord_1674494, baseEnd_1674494] using wordTrace_append hprefix tailTrace_1674494
  have hstable : (prefixWord ++ tailWord_1674494).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1674494).length < 2 ^ (prefixWord ++ tailWord_1674494).sum := by decide
  have hdescent : baseEnd_1674494 < baseStart_1674494 := by decide
  rcases family_descends (prefixWord ++ tailWord_1674494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1674507 : List Nat := [1, 1, 1, 1, 5, 4, 3, 1, 5]
def baseStart_1674507 : Nat := 118140960795 + 1674507 * 2 ^ 59
def prefixEnd_1674507 : Nat := 4983230072969 + 3 ^ 40 * 1674507 * 2
def baseEnd_1674507 : Nat := 191072655626307826080353

theorem tailTrace_1674507 : CollatzResearch.WordTrace tailWord_1674507 prefixEnd_1674507 191072655626307826080353 := by
  unfold tailWord_1674507
  simp only [CollatzResearch.WordTrace]
  refine ⟨61074287744554596872437775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40716191829703064581625183 61074287744554596872437775)
  ·
    refine ⟨91611431616831895308656663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61074287744554596872437775 91611431616831895308656663)
    ·
      refine ⟨137417147425247842962984995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91611431616831895308656663 137417147425247842962984995)
      ·
        refine ⟨206125721137871764444477493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137417147425247842962984995 206125721137871764444477493)
        ·
          refine ⟨19324286356675477916669765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 206125721137871764444477493 19324286356675477916669765)
          ·
            refine ⟨3623303691876652109375581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19324286356675477916669765 3623303691876652109375581)
            ·
              refine ⟨1358738884453744541015843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3623303691876652109375581 1358738884453744541015843)
              ·
                refine ⟨2038108326680616811523765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1358738884453744541015843 2038108326680616811523765)
                ·
                  refine ⟨191072655626307826080353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2038108326680616811523765 191072655626307826080353)
                  ·
                    rfl

theorem cell22_1674507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 3, 1, 5].length) (baseStart_1674507 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1674507 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1674507 prefixEnd_1674507 := by exact prefixLift 1674507
  have htrace : WordTrace (prefixWord ++ tailWord_1674507) baseStart_1674507 baseEnd_1674507 := by
    simpa [prefixWord, tailWord_1674507, baseEnd_1674507] using wordTrace_append hprefix tailTrace_1674507
  have hstable : (prefixWord ++ tailWord_1674507).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1674507).length < 2 ^ (prefixWord ++ tailWord_1674507).sum := by decide
  have hdescent : baseEnd_1674507 < baseStart_1674507 := by decide
  rcases family_descends (prefixWord ++ tailWord_1674507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1674528 : List Nat := [2, 1, 1, 5, 4, 1, 1, 3, 1, 3]
def baseStart_1674528 : Nat := 118140960795 + 1674528 * 2 ^ 59
def prefixEnd_1674528 : Nat := 4983230072969 + 3 ^ 40 * 1674528 * 2
def baseEnd_1674528 : Nat := 573225155608086423465995

theorem tailTrace_1674528 : CollatzResearch.WordTrace tailWord_1674528 prefixEnd_1674528 573225155608086423465995 := by
  unfold tailWord_1674528
  simp only [CollatzResearch.WordTrace]
  refine ⟨30537526838739258729476119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40716702451652344972634825 30537526838739258729476119)
  ·
    refine ⟨45806290258108888094214179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30537526838739258729476119 45806290258108888094214179)
    ·
      refine ⟨68709435387163332141321269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45806290258108888094214179 68709435387163332141321269)
      ·
        refine ⟨6441509567546562388248869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 68709435387163332141321269 6441509567546562388248869)
        ·
          refine ⟨1207783043914980447796663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6441509567546562388248869 1207783043914980447796663)
          ·
            refine ⟨1811674565872470671694995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1207783043914980447796663 1811674565872470671694995)
            ·
              refine ⟨2717511848808706007542493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1811674565872470671694995 2717511848808706007542493)
              ·
                refine ⟨1019066943303264752828435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2717511848808706007542493 1019066943303264752828435)
                ·
                  refine ⟨1528600414954897129242653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1019066943303264752828435 1528600414954897129242653)
                  ·
                    refine ⟨573225155608086423465995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1528600414954897129242653 573225155608086423465995)
                    ·
                      rfl

theorem cell22_1674528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 1, 3, 1, 3].length) (baseStart_1674528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1674528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1674528 prefixEnd_1674528 := by exact prefixLift 1674528
  have htrace : WordTrace (prefixWord ++ tailWord_1674528) baseStart_1674528 baseEnd_1674528 := by
    simpa [prefixWord, tailWord_1674528, baseEnd_1674528] using wordTrace_append hprefix tailTrace_1674528
  have hstable : (prefixWord ++ tailWord_1674528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1674528).length < 2 ^ (prefixWord ++ tailWord_1674528).sum := by decide
  have hdescent : baseEnd_1674528 < baseStart_1674528 := by decide
  rcases family_descends (prefixWord ++ tailWord_1674528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1674580 : List Nat := [2, 4, 1, 1, 2, 1, 1, 10]
def baseStart_1674580 : Nat := 118140960795 + 1674580 * 2 ^ 59
def prefixEnd_1674580 : Nat := 4983230072969 + 3 ^ 40 * 1674580 * 2
def baseEnd_1674580 : Nat := 63693661807863957907315

theorem tailTrace_1674580 : CollatzResearch.WordTrace tailWord_1674580 prefixEnd_1674580 63693661807863957907315 := by
  unfold tailWord_1674580
  simp only [CollatzResearch.WordTrace]
  refine ⟨30538475136645065169922597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40717966848860086893230129 30538475136645065169922597)
  ·
    refine ⟨5725964088120949719360487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30538475136645065169922597 5725964088120949719360487)
    ·
      refine ⟨8588946132181424579040731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5725964088120949719360487 8588946132181424579040731)
      ·
        refine ⟨12883419198272136868561097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8588946132181424579040731 12883419198272136868561097)
        ·
          refine ⟨9662564398704102651420823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12883419198272136868561097 9662564398704102651420823)
          ·
            refine ⟨14493846598056153977131235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9662564398704102651420823 14493846598056153977131235)
            ·
              refine ⟨21740769897084230965696853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14493846598056153977131235 21740769897084230965696853)
              ·
                refine ⟨63693661807863957907315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 21740769897084230965696853 63693661807863957907315)
                ·
                  rfl

theorem cell22_1674580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 10].length) (baseStart_1674580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1674580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1674580 prefixEnd_1674580 := by exact prefixLift 1674580
  have htrace : WordTrace (prefixWord ++ tailWord_1674580) baseStart_1674580 baseEnd_1674580 := by
    simpa [prefixWord, tailWord_1674580, baseEnd_1674580] using wordTrace_append hprefix tailTrace_1674580
  have hstable : (prefixWord ++ tailWord_1674580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1674580).length < 2 ^ (prefixWord ++ tailWord_1674580).sum := by decide
  have hdescent : baseEnd_1674580 < baseStart_1674580 := by decide
  rcases family_descends (prefixWord ++ tailWord_1674580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1674610 : List Nat := [3, 2, 1, 2, 1, 2, 1, 1, 1, 8]
def baseStart_1674610 : Nat := 118140960795 + 1674610 * 2 ^ 59
def prefixEnd_1674610 : Nat := 4983230072969 + 3 ^ 40 * 1674610 * 2
def baseEnd_1674610 : Nat := 573253225883865542915743

theorem tailTrace_1674610 : CollatzResearch.WordTrace tailWord_1674610 prefixEnd_1674610 573253225883865542915743 := by
  unfold tailWord_1674610
  simp only [CollatzResearch.WordTrace]
  refine ⟨15269511115795361365859321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40718696308787630308958189 15269511115795361365859321)
  ·
    refine ⟨11452133336846521024394491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15269511115795361365859321 11452133336846521024394491)
    ·
      refine ⟨17178200005269781536591737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11452133336846521024394491 17178200005269781536591737)
      ·
        refine ⟨12883650003952336152443803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17178200005269781536591737 12883650003952336152443803)
        ·
          refine ⟨19325475005928504228665705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12883650003952336152443803 19325475005928504228665705)
          ·
            refine ⟨14494106254446378171499279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19325475005928504228665705 14494106254446378171499279)
            ·
              refine ⟨21741159381669567257248919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14494106254446378171499279 21741159381669567257248919)
              ·
                refine ⟨32611739072504350885873379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21741159381669567257248919 32611739072504350885873379)
                ·
                  refine ⟨48917608608756526328810069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32611739072504350885873379 48917608608756526328810069)
                  ·
                    refine ⟨573253225883865542915743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 48917608608756526328810069 573253225883865542915743)
                    ·
                      rfl

theorem cell22_1674610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 1, 1, 8].length) (baseStart_1674610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1674610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1674610 prefixEnd_1674610 := by exact prefixLift 1674610
  have htrace : WordTrace (prefixWord ++ tailWord_1674610) baseStart_1674610 baseEnd_1674610 := by
    simpa [prefixWord, tailWord_1674610, baseEnd_1674610] using wordTrace_append hprefix tailTrace_1674610
  have hstable : (prefixWord ++ tailWord_1674610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1674610).length < 2 ^ (prefixWord ++ tailWord_1674610).sum := by decide
  have hdescent : baseEnd_1674610 < baseStart_1674610 := by decide
  rcases family_descends (prefixWord ++ tailWord_1674610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1674702 : List Nat := [4, 1, 1, 1, 2, 1, 2, 4, 1, 5]
def baseStart_1674702 : Nat := 118140960795 + 1674702 * 2 ^ 59
def prefixEnd_1674702 : Nat := 4983230072969 + 3 ^ 40 * 1674702 * 2
def baseEnd_1674702 : Nat := 573284719364007969615461

theorem tailTrace_1674702 : CollatzResearch.WordTrace tailWord_1674702 prefixEnd_1674702 573284719364007969615461 := by
  unfold tailWord_1674702
  simp only [CollatzResearch.WordTrace]
  refine ⟨7635174997356018146973295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40720933319232096783857573 7635174997356018146973295)
  ·
    refine ⟨11452762496034027220459943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7635174997356018146973295 11452762496034027220459943)
    ·
      refine ⟨17179143744051040830689915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11452762496034027220459943 17179143744051040830689915)
      ·
        refine ⟨25768715616076561246034873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17179143744051040830689915 25768715616076561246034873)
        ·
          refine ⟨19326536712057420934526155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25768715616076561246034873 19326536712057420934526155)
          ·
            refine ⟨28989805068086131401789233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19326536712057420934526155 28989805068086131401789233)
            ·
              refine ⟨21742353801064598551341925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28989805068086131401789233 21742353801064598551341925)
              ·
                refine ⟨4076691337699612228376611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21742353801064598551341925 4076691337699612228376611)
                ·
                  refine ⟨6115037006549418342564917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4076691337699612228376611 6115037006549418342564917)
                  ·
                    refine ⟨573284719364007969615461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6115037006549418342564917 573284719364007969615461)
                    ·
                      rfl

theorem cell22_1674702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 4, 1, 5].length) (baseStart_1674702 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1674702 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1674702 prefixEnd_1674702 := by exact prefixLift 1674702
  have htrace : WordTrace (prefixWord ++ tailWord_1674702) baseStart_1674702 baseEnd_1674702 := by
    simpa [prefixWord, tailWord_1674702, baseEnd_1674702] using wordTrace_append hprefix tailTrace_1674702
  have hstable : (prefixWord ++ tailWord_1674702).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1674702).length < 2 ^ (prefixWord ++ tailWord_1674702).sum := by decide
  have hdescent : baseEnd_1674702 < baseStart_1674702 := by decide
  rcases family_descends (prefixWord ++ tailWord_1674702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1674719 : List Nat := [1, 1, 2, 3, 3, 1, 2, 4, 2, 3]
def baseStart_1674719 : Nat := 118140960795 + 1674719 * 2 ^ 59
def prefixEnd_1674719 : Nat := 4983230072969 + 3 ^ 40 * 1674719 * 2
def baseEnd_1674719 : Nat := 573290538811425591940409

theorem tailTrace_1674719 : CollatzResearch.WordTrace tailWord_1674719 prefixEnd_1674719 573290538811425591940409 := by
  unfold tailWord_1674719
  simp only [CollatzResearch.WordTrace]
  refine ⟨61082020019786557079155211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40721346679857704719436807 61082020019786557079155211)
  ·
    refine ⟨91623030029679835618732817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61082020019786557079155211 91623030029679835618732817)
    ·
      refine ⟨68717272522259876714049613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91623030029679835618732817 68717272522259876714049613)
      ·
        refine ⟨25768977195847453767768605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68717272522259876714049613 25768977195847453767768605)
        ·
          refine ⟨9663366448442795162913227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25768977195847453767768605 9663366448442795162913227)
          ·
            refine ⟨14495049672664192744369841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9663366448442795162913227 14495049672664192744369841)
            ·
              refine ⟨10871287254498144558277381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14495049672664192744369841 10871287254498144558277381)
              ·
                refine ⟨2038366360218402104677009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10871287254498144558277381 2038366360218402104677009)
                ·
                  refine ⟨1528774770163801578507757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2038366360218402104677009 1528774770163801578507757)
                  ·
                    refine ⟨573290538811425591940409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1528774770163801578507757 573290538811425591940409)
                    ·
                      rfl

theorem cell22_1674719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 4, 2, 3].length) (baseStart_1674719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1674719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1674719 prefixEnd_1674719 := by exact prefixLift 1674719
  have htrace : WordTrace (prefixWord ++ tailWord_1674719) baseStart_1674719 baseEnd_1674719 := by
    simpa [prefixWord, tailWord_1674719, baseEnd_1674719] using wordTrace_append hprefix tailTrace_1674719
  have hstable : (prefixWord ++ tailWord_1674719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1674719).length < 2 ^ (prefixWord ++ tailWord_1674719).sum := by decide
  have hdescent : baseEnd_1674719 < baseStart_1674719 := by decide
  rcases family_descends (prefixWord ++ tailWord_1674719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1674721 : List Nat := [1, 2, 3, 1, 2, 4, 3, 2, 4]
def baseStart_1674721 : Nat := 118140960795 + 1674721 * 2 ^ 59
def prefixEnd_1674721 : Nat := 4983230072969 + 3 ^ 40 * 1674721 * 2
def baseEnd_1674721 : Nat := 191097074484099417796801

theorem tailTrace_1674721 : CollatzResearch.WordTrace tailWord_1674721 prefixEnd_1674721 191097074484099417796801 := by
  unfold tailWord_1674721
  simp only [CollatzResearch.WordTrace]
  refine ⟨61082092965779311420728017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40721395310519540947152011 61082092965779311420728017)
  ·
    refine ⟨45811569724334483565546013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61082092965779311420728017 45811569724334483565546013)
    ·
      refine ⟨17179338646625431337079755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45811569724334483565546013 17179338646625431337079755)
      ·
        refine ⟨25769007969938147005619633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17179338646625431337079755 25769007969938147005619633)
        ·
          refine ⟨19326755977453610254214725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25769007969938147005619633 19326755977453610254214725)
          ·
            refine ⟨3623766745772551922665261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19326755977453610254214725 3623766745772551922665261)
            ·
              refine ⟨1358912529664706970999473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3623766745772551922665261 1358912529664706970999473)
              ·
                refine ⟨1019184397248530228249605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1358912529664706970999473 1019184397248530228249605)
                ·
                  refine ⟨191097074484099417796801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1019184397248530228249605 191097074484099417796801)
                  ·
                    rfl

theorem cell22_1674721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 3, 2, 4].length) (baseStart_1674721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1674721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1674721 prefixEnd_1674721 := by exact prefixLift 1674721
  have htrace : WordTrace (prefixWord ++ tailWord_1674721) baseStart_1674721 baseEnd_1674721 := by
    simpa [prefixWord, tailWord_1674721, baseEnd_1674721] using wordTrace_append hprefix tailTrace_1674721
  have hstable : (prefixWord ++ tailWord_1674721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1674721).length < 2 ^ (prefixWord ++ tailWord_1674721).sum := by decide
  have hdescent : baseEnd_1674721 < baseStart_1674721 := by decide
  rcases family_descends (prefixWord ++ tailWord_1674721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1674736 : List Nat := [2, 1, 1, 1, 3, 4, 4, 1, 2, 3]
def baseStart_1674736 : Nat := 118140960795 + 1674736 * 2 ^ 59
def prefixEnd_1674736 : Nat := 4983230072969 + 3 ^ 40 * 1674736 * 2
def baseEnd_1674736 : Nat := 573296358258843214265357

theorem tailTrace_1674736 : CollatzResearch.WordTrace tailWord_1674736 prefixEnd_1674736 573296358258843214265357 := by
  unfold tailWord_1674736
  simp only [CollatzResearch.WordTrace]
  refine ⟨30541320030362484491262031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40721760040483312655016041 30541320030362484491262031)
  ·
    refine ⟨45811980045543726736893047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30541320030362484491262031 45811980045543726736893047)
    ·
      refine ⟨68717970068315590105339571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45811980045543726736893047 68717970068315590105339571)
      ·
        refine ⟨103076955102473385158009357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68717970068315590105339571 103076955102473385158009357)
        ·
          refine ⟨38653858163427519434253509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103076955102473385158009357 38653858163427519434253509)
          ·
            refine ⟨7247598405642659893922533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38653858163427519434253509 7247598405642659893922533)
            ·
              refine ⟨1358924701057998730110475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7247598405642659893922533 1358924701057998730110475)
              ·
                refine ⟨2038387051586998095165713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1358924701057998730110475 2038387051586998095165713)
                ·
                  refine ⟨1528790288690248571374285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2038387051586998095165713 1528790288690248571374285)
                  ·
                    refine ⟨573296358258843214265357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1528790288690248571374285 573296358258843214265357)
                    ·
                      rfl

theorem cell22_1674736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 4, 1, 2, 3].length) (baseStart_1674736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1674736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1674736 prefixEnd_1674736 := by exact prefixLift 1674736
  have htrace : WordTrace (prefixWord ++ tailWord_1674736) baseStart_1674736 baseEnd_1674736 := by
    simpa [prefixWord, tailWord_1674736, baseEnd_1674736] using wordTrace_append hprefix tailTrace_1674736
  have hstable : (prefixWord ++ tailWord_1674736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1674736).length < 2 ^ (prefixWord ++ tailWord_1674736).sum := by decide
  have hdescent : baseEnd_1674736 < baseStart_1674736 := by decide
  rcases family_descends (prefixWord ++ tailWord_1674736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1674772 : List Nat := [2, 4, 3, 1, 3, 1, 2, 2, 4]
def baseStart_1674772 : Nat := 118140960795 + 1674772 * 2 ^ 59
def prefixEnd_1674772 : Nat := 4983230072969 + 3 ^ 40 * 1674772 * 2
def baseEnd_1674772 : Nat := 191102893931517040121749

theorem tailTrace_1674772 : CollatzResearch.WordTrace tailWord_1674772 prefixEnd_1674772 191102893931517040121749 := by
  unfold tailWord_1674772
  simp only [CollatzResearch.WordTrace]
  refine ⟨30541976544297273565417285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40722635392396364753889713 30541976544297273565417285)
  ·
    refine ⟨5726620602055738793515741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30541976544297273565417285 5726620602055738793515741)
    ·
      refine ⟨2147482725770902047568403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5726620602055738793515741 2147482725770902047568403)
      ·
        refine ⟨3221224088656353071352605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2147482725770902047568403 3221224088656353071352605)
        ·
          refine ⟨1207959033246132401757227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3221224088656353071352605 1207959033246132401757227)
          ·
            refine ⟨1811938549869198602635841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1207959033246132401757227 1811938549869198602635841)
            ·
              refine ⟨1358953912401898951976881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1811938549869198602635841 1358953912401898951976881)
              ·
                refine ⟨1019215434301424213982661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1358953912401898951976881 1019215434301424213982661)
                ·
                  refine ⟨191102893931517040121749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1019215434301424213982661 191102893931517040121749)
                  ·
                    rfl

theorem cell22_1674772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 2, 2, 4].length) (baseStart_1674772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1674772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1674772 prefixEnd_1674772 := by exact prefixLift 1674772
  have htrace : WordTrace (prefixWord ++ tailWord_1674772) baseStart_1674772 baseEnd_1674772 := by
    simpa [prefixWord, tailWord_1674772, baseEnd_1674772] using wordTrace_append hprefix tailTrace_1674772
  have hstable : (prefixWord ++ tailWord_1674772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1674772).length < 2 ^ (prefixWord ++ tailWord_1674772).sum := by decide
  have hdescent : baseEnd_1674772 < baseStart_1674772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1674772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1674794 : List Nat := [3, 1, 4, 1, 1, 1, 1, 5, 5]
def baseStart_1674794 : Nat := 118140960795 + 1674794 * 2 ^ 59
def prefixEnd_1674794 : Nat := 4983230072969 + 3 ^ 40 * 1674794 * 2
def baseEnd_1674794 : Nat := 191105404281383465438393

theorem tailTrace_1674794 : CollatzResearch.WordTrace tailWord_1674794 prefixEnd_1674794 191105404281383465438393 := by
  unfold tailWord_1674794
  simp only [CollatzResearch.WordTrace]
  refine ⟨15271188873628711222033859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40723170329676563258756957 15271188873628711222033859)
  ·
    refine ⟨22906783310443066833050789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15271188873628711222033859 22906783310443066833050789)
    ·
      refine ⟨4295021870708075031197023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22906783310443066833050789 4295021870708075031197023)
      ·
        refine ⟨6442532806062112546795535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4295021870708075031197023 6442532806062112546795535)
        ·
          refine ⟨9663799209093168820193303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6442532806062112546795535 9663799209093168820193303)
          ·
            refine ⟨14495698813639753230289955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9663799209093168820193303 14495698813639753230289955)
            ·
              refine ⟨21743548220459629845434933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14495698813639753230289955 21743548220459629845434933)
              ·
                refine ⟨2038457645668090298009525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21743548220459629845434933 2038457645668090298009525)
                ·
                  refine ⟨191105404281383465438393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2038457645668090298009525 191105404281383465438393)
                  ·
                    rfl

theorem cell22_1674794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 5, 5].length) (baseStart_1674794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1674794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1674794 prefixEnd_1674794 := by exact prefixLift 1674794
  have htrace : WordTrace (prefixWord ++ tailWord_1674794) baseStart_1674794 baseEnd_1674794 := by
    simpa [prefixWord, tailWord_1674794, baseEnd_1674794] using wordTrace_append hprefix tailTrace_1674794
  have hstable : (prefixWord ++ tailWord_1674794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1674794).length < 2 ^ (prefixWord ++ tailWord_1674794).sum := by decide
  have hdescent : baseEnd_1674794 < baseStart_1674794 := by decide
  rcases family_descends (prefixWord ++ tailWord_1674794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1674839 : List Nat := [1, 1, 3, 2, 2, 4, 2, 1, 6]
def baseStart_1674839 : Nat := 118140960795 + 1674839 * 2 ^ 59
def prefixEnd_1674839 : Nat := 4983230072969 + 3 ^ 40 * 1674839 * 2
def baseEnd_1674839 : Nat := 191110539087928426313347

theorem tailTrace_1674839 : CollatzResearch.WordTrace tailWord_1674839 prefixEnd_1674839 191110539087928426313347 := by
  unfold tailWord_1674839
  simp only [CollatzResearch.WordTrace]
  refine ⟨61086396779351817573523571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40724264519567878382349047 61086396779351817573523571)
  ·
    refine ⟨91629595169027726360285357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61086396779351817573523571 91629595169027726360285357)
    ·
      refine ⟨34361098188385397385107009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91629595169027726360285357 34361098188385397385107009)
      ·
        refine ⟨25770823641289048038830257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34361098188385397385107009 25770823641289048038830257)
        ·
          refine ⟨19328117730966786029122693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25770823641289048038830257 19328117730966786029122693)
          ·
            refine ⟨3624022074556272380460505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19328117730966786029122693 3624022074556272380460505)
            ·
              refine ⟨2718016555917204285345379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3624022074556272380460505 2718016555917204285345379)
              ·
                refine ⟨4077024833875806428018069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2718016555917204285345379 4077024833875806428018069)
                ·
                  refine ⟨191110539087928426313347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4077024833875806428018069 191110539087928426313347)
                  ·
                    rfl

theorem cell22_1674839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 2, 1, 6].length) (baseStart_1674839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1674839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1674839 prefixEnd_1674839 := by exact prefixLift 1674839
  have htrace : WordTrace (prefixWord ++ tailWord_1674839) baseStart_1674839 baseEnd_1674839 := by
    simpa [prefixWord, tailWord_1674839, baseEnd_1674839] using wordTrace_append hprefix tailTrace_1674839
  have hstable : (prefixWord ++ tailWord_1674839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1674839).length < 2 ^ (prefixWord ++ tailWord_1674839).sum := by decide
  have hdescent : baseEnd_1674839 < baseStart_1674839 := by decide
  rcases family_descends (prefixWord ++ tailWord_1674839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1674845 : List Nat := [1, 4, 4, 2, 1, 1, 3, 1, 5]
def baseStart_1674845 : Nat := 118140960795 + 1674845 * 2 ^ 59
def prefixEnd_1674845 : Nat := 4983230072969 + 3 ^ 40 * 1674845 * 2
def baseEnd_1674845 : Nat := 191111223728801087763341

theorem tailTrace_1674845 : CollatzResearch.WordTrace tailWord_1674845 prefixEnd_1674845 191111223728801087763341 := by
  unfold tailWord_1674845
  simp only [CollatzResearch.WordTrace]
  refine ⟨61086615617330080598241989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40724410411553387065494659 61086615617330080598241989)
  ·
    refine ⟨11453740428249390112170373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61086615617330080598241989 11453740428249390112170373)
    ·
      refine ⟨2147576330296760646031945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11453740428249390112170373 2147576330296760646031945)
      ·
        refine ⟨1610682247722570484523959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2147576330296760646031945 1610682247722570484523959)
        ·
          refine ⟨2416023371583855726785939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1610682247722570484523959 2416023371583855726785939)
          ·
            refine ⟨3624035057375783590178909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2416023371583855726785939 3624035057375783590178909)
            ·
              refine ⟨1359013146515918846317091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3624035057375783590178909 1359013146515918846317091)
              ·
                refine ⟨2038519719773878269475637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1359013146515918846317091 2038519719773878269475637)
                ·
                  refine ⟨191111223728801087763341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2038519719773878269475637 191111223728801087763341)
                  ·
                    rfl

theorem cell22_1674845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 3, 1, 5].length) (baseStart_1674845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1674845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1674845 prefixEnd_1674845 := by exact prefixLift 1674845
  have htrace : WordTrace (prefixWord ++ tailWord_1674845) baseStart_1674845 baseEnd_1674845 := by
    simpa [prefixWord, tailWord_1674845, baseEnd_1674845] using wordTrace_append hprefix tailTrace_1674845
  have hstable : (prefixWord ++ tailWord_1674845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1674845).length < 2 ^ (prefixWord ++ tailWord_1674845).sum := by decide
  have hdescent : baseEnd_1674845 < baseStart_1674845 := by decide
  rcases family_descends (prefixWord ++ tailWord_1674845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1674944 : List Nat := [2, 1, 1, 2, 4, 1, 2, 2, 2, 5]
def baseStart_1674944 : Nat := 118140960795 + 1674944 * 2 ^ 59
def prefixEnd_1674944 : Nat := 4983230072969 + 3 ^ 40 * 1674944 * 2
def baseEnd_1674944 : Nat := 573367560909600005064719

theorem tailTrace_1674944 : CollatzResearch.WordTrace tailWord_1674944 prefixEnd_1674944 573367560909600005064719 := by
  unfold tailWord_1674944
  simp only [CollatzResearch.WordTrace]
  refine ⟨30545113221985710253047943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40726817629314280337397257 30545113221985710253047943)
  ·
    refine ⟨45817669832978565379571915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30545113221985710253047943 45817669832978565379571915)
    ·
      refine ⟨68726504749467848069357873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45817669832978565379571915 68726504749467848069357873)
      ·
        refine ⟨51544878562100886052018405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68726504749467848069357873 51544878562100886052018405)
        ·
          refine ⟨9664664730393916134753451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51544878562100886052018405 9664664730393916134753451)
          ·
            refine ⟨14496997095590874202130177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9664664730393916134753451 14496997095590874202130177)
            ·
              refine ⟨10872747821693155651597633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14496997095590874202130177 10872747821693155651597633)
              ·
                refine ⟨8154560866269866738698225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10872747821693155651597633 8154560866269866738698225)
                ·
                  refine ⟨6115920649702400054023669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8154560866269866738698225 6115920649702400054023669)
                  ·
                    refine ⟨573367560909600005064719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6115920649702400054023669 573367560909600005064719)
                    ·
                      rfl

theorem cell22_1674944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 2, 2, 5].length) (baseStart_1674944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1674944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1674944 prefixEnd_1674944 := by exact prefixLift 1674944
  have htrace : WordTrace (prefixWord ++ tailWord_1674944) baseStart_1674944 baseEnd_1674944 := by
    simpa [prefixWord, tailWord_1674944, baseEnd_1674944] using wordTrace_append hprefix tailTrace_1674944
  have hstable : (prefixWord ++ tailWord_1674944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1674944).length < 2 ^ (prefixWord ++ tailWord_1674944).sum := by decide
  have hdescent : baseEnd_1674944 < baseStart_1674944 := by decide
  rcases family_descends (prefixWord ++ tailWord_1674944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1674993 : List Nat := [1, 2, 2, 2, 2, 3, 4, 1, 1, 4]
def baseStart_1674993 : Nat := 118140960795 + 1674993 * 2 ^ 59
def prefixEnd_1674993 : Nat := 4983230072969 + 3 ^ 40 * 1674993 * 2
def baseEnd_1674993 : Nat := 573384334610980210589569

theorem tailTrace_1674993 : CollatzResearch.WordTrace tailWord_1674993 prefixEnd_1674993 573384334610980210589569 := by
  unfold tailWord_1674993
  simp only [CollatzResearch.WordTrace]
  refine ⟨61092013620793901874629633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40728009080529267916419755 61092013620793901874629633)
  ·
    refine ⟨45819010215595426405972225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61092013620793901874629633 45819010215595426405972225)
    ·
      refine ⟨34364257661696569804479169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45819010215595426405972225 34364257661696569804479169)
      ·
        refine ⟨25773193246272427353359377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34364257661696569804479169 25773193246272427353359377)
        ·
          refine ⟨19329894934704320515019533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25773193246272427353359377 19329894934704320515019533)
          ·
            refine ⟨7248710600514120193132325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19329894934704320515019533 7248710600514120193132325)
            ·
              refine ⟨1359133237596397536212311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7248710600514120193132325 1359133237596397536212311)
              ·
                refine ⟨2038699856394596304318467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1359133237596397536212311 2038699856394596304318467)
                ·
                  refine ⟨3058049784591894456477701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2038699856394596304318467 3058049784591894456477701)
                  ·
                    refine ⟨573384334610980210589569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3058049784591894456477701 573384334610980210589569)
                    ·
                      rfl

theorem cell22_1674993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 4, 1, 1, 4].length) (baseStart_1674993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1674993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1674993 prefixEnd_1674993 := by exact prefixLift 1674993
  have htrace : WordTrace (prefixWord ++ tailWord_1674993) baseStart_1674993 baseEnd_1674993 := by
    simpa [prefixWord, tailWord_1674993, baseEnd_1674993] using wordTrace_append hprefix tailTrace_1674993
  have hstable : (prefixWord ++ tailWord_1674993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1674993).length < 2 ^ (prefixWord ++ tailWord_1674993).sum := by decide
  have hdescent : baseEnd_1674993 < baseStart_1674993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1674993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1675068 : List Nat := [2, 2, 2, 2, 1, 1, 5, 1, 3, 3]
def baseStart_1675068 : Nat := 118140960795 + 1675068 * 2 ^ 59
def prefixEnd_1675068 : Nat := 4983230072969 + 3 ^ 40 * 1675068 * 2
def baseEnd_1675068 : Nat := 573410008643705014964339

theorem tailTrace_1675068 : CollatzResearch.WordTrace tailWord_1675068 prefixEnd_1675068 573410008643705014964339 := by
  unfold tailWord_1675068
  simp only [CollatzResearch.WordTrace]
  refine ⟨30547374547761094841804929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40729832730348126455739905 30547374547761094841804929)
  ·
    refine ⟨22910530910820821131353697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30547374547761094841804929 22910530910820821131353697)
    ·
      refine ⟨17182898183115615848515273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22910530910820821131353697 17182898183115615848515273)
      ·
        refine ⟨12887173637336711886386455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17182898183115615848515273 12887173637336711886386455)
        ·
          refine ⟨19330760456005067829579683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12887173637336711886386455 19330760456005067829579683)
          ·
            refine ⟨28996140684007601744369525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19330760456005067829579683 28996140684007601744369525)
            ·
              refine ⟨2718388189125712663534643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28996140684007601744369525 2718388189125712663534643)
              ·
                refine ⟨4077582283688568995301965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2718388189125712663534643 4077582283688568995301965)
                ·
                  refine ⟨1529093356383213373238237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4077582283688568995301965 1529093356383213373238237)
                  ·
                    refine ⟨573410008643705014964339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1529093356383213373238237 573410008643705014964339)
                    ·
                      rfl

theorem cell22_1675068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 5, 1, 3, 3].length) (baseStart_1675068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1675068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1675068 prefixEnd_1675068 := by exact prefixLift 1675068
  have htrace : WordTrace (prefixWord ++ tailWord_1675068) baseStart_1675068 baseEnd_1675068 := by
    simpa [prefixWord, tailWord_1675068, baseEnd_1675068] using wordTrace_append hprefix tailTrace_1675068
  have hstable : (prefixWord ++ tailWord_1675068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1675068).length < 2 ^ (prefixWord ++ tailWord_1675068).sum := by decide
  have hdescent : baseEnd_1675068 < baseStart_1675068 := by decide
  rcases family_descends (prefixWord ++ tailWord_1675068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1675081 : List Nat := [1, 2, 1, 1, 2, 4, 3, 3, 5]
def baseStart_1675081 : Nat := 118140960795 + 1675081 * 2 ^ 59
def prefixEnd_1675081 : Nat := 4983230072969 + 3 ^ 40 * 1675081 * 2
def baseEnd_1675081 : Nat := 191138152936459104796433

theorem tailTrace_1675081 : CollatzResearch.WordTrace tailWord_1675081 prefixEnd_1675081 191138152936459104796433 := by
  unfold tailWord_1675081
  simp only [CollatzResearch.WordTrace]
  refine ⟨61095223244475092903833097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40730148829650061935888731 61095223244475092903833097)
  ·
    refine ⟨45821417433356319677874823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61095223244475092903833097 45821417433356319677874823)
    ·
      refine ⟨68732126150034479516812235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45821417433356319677874823 68732126150034479516812235)
      ·
        refine ⟨103098189225051719275218353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68732126150034479516812235 103098189225051719275218353)
        ·
          refine ⟨77323641918788789456413765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103098189225051719275218353 77323641918788789456413765)
          ·
            refine ⟨14498182859772898023077581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77323641918788789456413765 14498182859772898023077581)
            ·
              refine ⟨5436818572414836758654093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14498182859772898023077581 5436818572414836758654093)
              ·
                refine ⟨2038806964655563784495285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5436818572414836758654093 2038806964655563784495285)
                ·
                  refine ⟨191138152936459104796433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2038806964655563784495285 191138152936459104796433)
                  ·
                    rfl

theorem cell22_1675081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 3, 5].length) (baseStart_1675081 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1675081 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1675081 prefixEnd_1675081 := by exact prefixLift 1675081
  have htrace : WordTrace (prefixWord ++ tailWord_1675081) baseStart_1675081 baseEnd_1675081 := by
    simpa [prefixWord, tailWord_1675081, baseEnd_1675081] using wordTrace_append hprefix tailTrace_1675081
  have hstable : (prefixWord ++ tailWord_1675081).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1675081).length < 2 ^ (prefixWord ++ tailWord_1675081).sum := by decide
  have hdescent : baseEnd_1675081 < baseStart_1675081 := by decide
  rcases family_descends (prefixWord ++ tailWord_1675081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1675143 : List Nat := [1, 1, 4, 2, 4, 1, 1, 2, 6]
def baseStart_1675143 : Nat := 118140960795 + 1675143 * 2 ^ 59
def prefixEnd_1675143 : Nat := 4983230072969 + 3 ^ 40 * 1675143 * 2
def baseEnd_1675143 : Nat := 191145227558809939779703

theorem tailTrace_1675143 : CollatzResearch.WordTrace tailWord_1675143 prefixEnd_1675143 191145227558809939779703 := by
  unfold tailWord_1675143
  simp only [CollatzResearch.WordTrace]
  refine ⟨61097484570250477492590083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40731656380166984995060055 61097484570250477492590083)
  ·
    refine ⟨91646226855375716238885125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61097484570250477492590083 91646226855375716238885125)
    ·
      refine ⟨17183667535382946794790961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91646226855375716238885125 17183667535382946794790961)
      ·
        refine ⟨12887750651537210096093221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17183667535382946794790961 12887750651537210096093221)
        ·
          refine ⟨2416453247163226893017479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12887750651537210096093221 2416453247163226893017479)
          ·
            refine ⟨3624679870744840339526219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2416453247163226893017479 3624679870744840339526219)
            ·
              refine ⟨5437019806117260509289329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3624679870744840339526219 5437019806117260509289329)
              ·
                refine ⟨4077764854587945381966997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5437019806117260509289329 4077764854587945381966997)
                ·
                  refine ⟨191145227558809939779703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4077764854587945381966997 191145227558809939779703)
                  ·
                    rfl

theorem cell22_1675143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 2, 6].length) (baseStart_1675143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1675143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1675143 prefixEnd_1675143 := by exact prefixLift 1675143
  have htrace : WordTrace (prefixWord ++ tailWord_1675143) baseStart_1675143 baseEnd_1675143 := by
    simpa [prefixWord, tailWord_1675143, baseEnd_1675143] using wordTrace_append hprefix tailTrace_1675143
  have hstable : (prefixWord ++ tailWord_1675143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1675143).length < 2 ^ (prefixWord ++ tailWord_1675143).sum := by decide
  have hdescent : baseEnd_1675143 < baseStart_1675143 := by decide
  rcases family_descends (prefixWord ++ tailWord_1675143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1675162 : List Nat := [3, 1, 1, 4, 2, 3, 2, 1, 1, 4]
def baseStart_1675162 : Nat := 118140960795 + 1675162 * 2 ^ 59
def prefixEnd_1675162 : Nat := 4983230072969 + 3 ^ 40 * 1675162 * 2
def baseEnd_1675162 : Nat := 573442186764720103114051

theorem tailTrace_1675162 : CollatzResearch.WordTrace tailWord_1675162 prefixEnd_1675162 573442186764720103114051 := by
  unfold tailWord_1675162
  simp only [CollatzResearch.WordTrace]
  refine ⟨15274544389295410934382935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40732118371454429158354493 15274544389295410934382935)
  ·
    refine ⟨22911816583943116401574403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15274544389295410934382935 22911816583943116401574403)
    ·
      refine ⟨34367724875914674602361605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22911816583943116401574403 34367724875914674602361605)
      ·
        refine ⟨6443948414234001487942801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34367724875914674602361605 6443948414234001487942801)
        ·
          refine ⟨4832961310675501115957101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6443948414234001487942801 4832961310675501115957101)
          ·
            refine ⟨1812360491503312918483913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4832961310675501115957101 1812360491503312918483913)
            ·
              refine ⟨1359270368627484688862935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1812360491503312918483913 1359270368627484688862935)
              ·
                refine ⟨2038905552941227033294403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1359270368627484688862935 2038905552941227033294403)
                ·
                  refine ⟨3058358329411840549941605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2038905552941227033294403 3058358329411840549941605)
                  ·
                    refine ⟨573442186764720103114051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3058358329411840549941605 573442186764720103114051)
                    ·
                      rfl

theorem cell22_1675162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 2, 1, 1, 4].length) (baseStart_1675162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1675162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1675162 prefixEnd_1675162 := by exact prefixLift 1675162
  have htrace : WordTrace (prefixWord ++ tailWord_1675162) baseStart_1675162 baseEnd_1675162 := by
    simpa [prefixWord, tailWord_1675162, baseEnd_1675162] using wordTrace_append hprefix tailTrace_1675162
  have hstable : (prefixWord ++ tailWord_1675162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1675162).length < 2 ^ (prefixWord ++ tailWord_1675162).sum := by decide
  have hdescent : baseEnd_1675162 < baseStart_1675162 := by decide
  rcases family_descends (prefixWord ++ tailWord_1675162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1675175 : List Nat := [1, 1, 6, 1, 2, 2, 1, 1, 4, 3]
def baseStart_1675175 : Nat := 118140960795 + 1675175 * 2 ^ 59
def prefixEnd_1675175 : Nat := 4983230072969 + 3 ^ 40 * 1675175 * 2
def baseEnd_1675175 : Nat := 573446636930392402539011

theorem tailTrace_1675175 : CollatzResearch.WordTrace tailWord_1675175 prefixEnd_1675175 573446636930392402539011 := by
  unfold tailWord_1675175
  simp only [CollatzResearch.WordTrace]
  refine ⟨61098651706134546957754979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40732434470756364638503319 61098651706134546957754979)
  ·
    refine ⟨91647977559201820436632469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61098651706134546957754979 91647977559201820436632469)
    ·
      refine ⟨4295998948087585332967147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 91647977559201820436632469 4295998948087585332967147)
      ·
        refine ⟨6443998422131377999450721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4295998948087585332967147 6443998422131377999450721)
        ·
          refine ⟨4832998816598533499588041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6443998422131377999450721 4832998816598533499588041)
          ·
            refine ⟨3624749112448900124691031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4832998816598533499588041 3624749112448900124691031)
            ·
              refine ⟨5437123668673350187036547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3624749112448900124691031 5437123668673350187036547)
              ·
                refine ⟨8155685503010025280554821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5437123668673350187036547 8155685503010025280554821)
                ·
                  refine ⟨1529191031814379740104029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8155685503010025280554821 1529191031814379740104029)
                  ·
                    refine ⟨573446636930392402539011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1529191031814379740104029 573446636930392402539011)
                    ·
                      rfl

theorem cell22_1675175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 1, 4, 3].length) (baseStart_1675175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1675175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1675175 prefixEnd_1675175 := by exact prefixLift 1675175
  have htrace : WordTrace (prefixWord ++ tailWord_1675175) baseStart_1675175 baseEnd_1675175 := by
    simpa [prefixWord, tailWord_1675175, baseEnd_1675175] using wordTrace_append hprefix tailTrace_1675175
  have hstable : (prefixWord ++ tailWord_1675175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1675175).length < 2 ^ (prefixWord ++ tailWord_1675175).sum := by decide
  have hdescent : baseEnd_1675175 < baseStart_1675175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1675175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1675216 : List Nat := [2, 1, 1, 1, 1, 2, 5, 2, 7]
def baseStart_1675216 : Nat := 118140960795 + 1675216 * 2 ^ 59
def prefixEnd_1675216 : Nat := 4983230072969 + 3 ^ 40 * 1675216 * 2
def baseEnd_1675216 : Nat := 191153557356093987421295

theorem tailTrace_1675216 : CollatzResearch.WordTrace tailWord_1675216 prefixEnd_1675216 191153557356093987421295 := by
  unfold tailWord_1675216
  simp only [CollatzResearch.WordTrace]
  refine ⟨30550073549493005479998751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40733431399324007306665001 30550073549493005479998751)
  ·
    refine ⟨45825110324239508219998127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30550073549493005479998751 45825110324239508219998127)
    ·
      refine ⟨68737665486359262329997191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45825110324239508219998127 68737665486359262329997191)
      ·
        refine ⟨103106498229538893494995787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68737665486359262329997191 103106498229538893494995787)
        ·
          refine ⟨154659747344308340242493681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103106498229538893494995787 154659747344308340242493681)
          ·
            refine ⟨115994810508231255181870261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154659747344308340242493681 115994810508231255181870261)
            ·
              refine ⟨10874513485146680173300337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 115994810508231255181870261 10874513485146680173300337)
              ·
                refine ⟨8155885113860010129975253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10874513485146680173300337 8155885113860010129975253)
                ·
                  refine ⟨191153557356093987421295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8155885113860010129975253 191153557356093987421295)
                  ·
                    rfl

theorem cell22_1675216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 2, 7].length) (baseStart_1675216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1675216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1675216 prefixEnd_1675216 := by exact prefixLift 1675216
  have htrace : WordTrace (prefixWord ++ tailWord_1675216) baseStart_1675216 baseEnd_1675216 := by
    simpa [prefixWord, tailWord_1675216, baseEnd_1675216] using wordTrace_append hprefix tailTrace_1675216
  have hstable : (prefixWord ++ tailWord_1675216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1675216).length < 2 ^ (prefixWord ++ tailWord_1675216).sum := by decide
  have hdescent : baseEnd_1675216 < baseStart_1675216 := by decide
  rcases family_descends (prefixWord ++ tailWord_1675216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1675222 : List Nat := [5, 2, 1, 1, 4, 1, 8]
def baseStart_1675222 : Nat := 118140960795 + 1675222 * 2 ^ 59
def prefixEnd_1675222 : Nat := 4983230072969 + 3 ^ 40 * 1675222 * 2
def baseEnd_1675222 : Nat := 21239360221885183207921

theorem tailTrace_1675222 : CollatzResearch.WordTrace tailWord_1675222 prefixEnd_1675222 21239360221885183207921 := by
  unfold tailWord_1675222
  simp only [CollatzResearch.WordTrace]
  refine ⟨3818772871060267124044745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40733577291309515989810613 3818772871060267124044745)
  ·
    refine ⟨2864079653295200343033559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3818772871060267124044745 2864079653295200343033559)
    ·
      refine ⟨4296119479942800514550339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2864079653295200343033559 4296119479942800514550339)
      ·
        refine ⟨6444179219914200771825509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4296119479942800514550339 6444179219914200771825509)
        ·
          refine ⟨1208283603733912644717283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6444179219914200771825509 1208283603733912644717283)
          ·
            refine ⟨1812425405600868967075925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1208283603733912644717283 1812425405600868967075925)
            ·
              refine ⟨21239360221885183207921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1812425405600868967075925 21239360221885183207921)
              ·
                rfl

theorem cell22_1675222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 8].length) (baseStart_1675222 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1675222 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1675222 prefixEnd_1675222 := by exact prefixLift 1675222
  have htrace : WordTrace (prefixWord ++ tailWord_1675222) baseStart_1675222 baseEnd_1675222 := by
    simpa [prefixWord, tailWord_1675222, baseEnd_1675222] using wordTrace_append hprefix tailTrace_1675222
  have hstable : (prefixWord ++ tailWord_1675222).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1675222).length < 2 ^ (prefixWord ++ tailWord_1675222).sum := by decide
  have hdescent : baseEnd_1675222 < baseStart_1675222 := by decide
  rcases family_descends (prefixWord ++ tailWord_1675222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1675284 : List Nat := [2, 4, 3, 2, 1, 1, 2, 2, 5]
def baseStart_1675284 : Nat := 118140960795 + 1675284 * 2 ^ 59
def prefixEnd_1675284 : Nat := 4983230072969 + 3 ^ 40 * 1675284 * 2
def baseEnd_1675284 : Nat := 191161316619317483854559

theorem tailTrace_1675284 : CollatzResearch.WordTrace tailWord_1675284 prefixEnd_1675284 191161316619317483854559 := by
  unfold tailWord_1675284
  simp only [CollatzResearch.WordTrace]
  refine ⟨30551313631369829286736453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40735084841826439048981937 30551313631369829286736453)
  ·
    refine ⟨5728371305881842991263085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30551313631369829286736453 5728371305881842991263085)
    ·
      refine ⟨2148139239705691121723657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5728371305881842991263085 2148139239705691121723657)
      ·
        refine ⟨1611104429779268341292743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2148139239705691121723657 1611104429779268341292743)
        ·
          refine ⟨2416656644668902511939115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1611104429779268341292743 2416656644668902511939115)
          ·
            refine ⟨3624984967003353767908673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2416656644668902511939115 3624984967003353767908673)
            ·
              refine ⟨2718738725252515325931505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3624984967003353767908673 2718738725252515325931505)
              ·
                refine ⟨2039054043939386494448629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2718738725252515325931505 2039054043939386494448629)
                ·
                  refine ⟨191161316619317483854559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2039054043939386494448629 191161316619317483854559)
                  ·
                    rfl

theorem cell22_1675284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 2, 2, 5].length) (baseStart_1675284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1675284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1675284 prefixEnd_1675284 := by exact prefixLift 1675284
  have htrace : WordTrace (prefixWord ++ tailWord_1675284) baseStart_1675284 baseEnd_1675284 := by
    simpa [prefixWord, tailWord_1675284, baseEnd_1675284] using wordTrace_append hprefix tailTrace_1675284
  have hstable : (prefixWord ++ tailWord_1675284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1675284).length < 2 ^ (prefixWord ++ tailWord_1675284).sum := by decide
  have hdescent : baseEnd_1675284 < baseStart_1675284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1675284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1675295 : List Nat := [1, 1, 2, 4, 1, 2, 3, 4, 4]
def baseStart_1675295 : Nat := 118140960795 + 1675295 * 2 ^ 59
def prefixEnd_1675295 : Nat := 4983230072969 + 3 ^ 40 * 1675295 * 2
def baseEnd_1675295 : Nat := 191162571794250696512881

theorem tailTrace_1675295 : CollatzResearch.WordTrace tailWord_1675295 prefixEnd_1675295 191162571794250696512881 := by
  unfold tailWord_1675295
  simp only [CollatzResearch.WordTrace]
  refine ⟨61103028465699807452123339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40735352310466538301415559 61103028465699807452123339)
  ·
    refine ⟨91654542698549711178185009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61103028465699807452123339 91654542698549711178185009)
    ·
      refine ⟨68740907023912283383638757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91654542698549711178185009 68740907023912283383638757)
      ·
        refine ⟨12888920066983553134432267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68740907023912283383638757 12888920066983553134432267)
        ·
          refine ⟨19333380100475329701648401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12888920066983553134432267 19333380100475329701648401)
          ·
            refine ⟨14500035075356497276236301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19333380100475329701648401 14500035075356497276236301)
            ·
              refine ⟨5437513153258686478588613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14500035075356497276236301 5437513153258686478588613)
              ·
                refine ⟨1019533716236003714735365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5437513153258686478588613 1019533716236003714735365)
                ·
                  refine ⟨191162571794250696512881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1019533716236003714735365 191162571794250696512881)
                  ·
                    rfl

theorem cell22_1675295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 4, 4].length) (baseStart_1675295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1675295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1675295 prefixEnd_1675295 := by exact prefixLift 1675295
  have htrace : WordTrace (prefixWord ++ tailWord_1675295) baseStart_1675295 baseEnd_1675295 := by
    simpa [prefixWord, tailWord_1675295, baseEnd_1675295] using wordTrace_append hprefix tailTrace_1675295
  have hstable : (prefixWord ++ tailWord_1675295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1675295).length < 2 ^ (prefixWord ++ tailWord_1675295).sum := by decide
  have hdescent : baseEnd_1675295 < baseStart_1675295 := by decide
  rcases family_descends (prefixWord ++ tailWord_1675295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1675310 : List Nat := [4, 1, 3, 1, 1, 2, 1, 3, 1, 5]
def baseStart_1675310 : Nat := 118140960795 + 1675310 * 2 ^ 59
def prefixEnd_1675310 : Nat := 4983230072969 + 3 ^ 40 * 1675310 * 2
def baseEnd_1675310 : Nat := 573492850189297050413597

theorem tailTrace_1675310 : CollatzResearch.WordTrace tailWord_1675310 prefixEnd_1675310 573492850189297050413597 := by
  unfold tailWord_1675310
  simp only [CollatzResearch.WordTrace]
  refine ⟨7637946945080683126739923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40735717040430310009279589 7637946945080683126739923)
  ·
    refine ⟨11456920417621024690109885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7637946945080683126739923 11456920417621024690109885)
    ·
      refine ⟨4296345156607884258791207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11456920417621024690109885 4296345156607884258791207)
      ·
        refine ⟨6444517734911826388186811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4296345156607884258791207 6444517734911826388186811)
        ·
          refine ⟨9666776602367739582280217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6444517734911826388186811 9666776602367739582280217)
          ·
            refine ⟨7250082451775804686710163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9666776602367739582280217 7250082451775804686710163)
            ·
              refine ⟨10875123677663707030065245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7250082451775804686710163 10875123677663707030065245)
              ·
                refine ⟨4078171379123890136274467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10875123677663707030065245 4078171379123890136274467)
                ·
                  refine ⟨6117257068685835204411701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4078171379123890136274467 6117257068685835204411701)
                  ·
                    refine ⟨573492850189297050413597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6117257068685835204411701 573492850189297050413597)
                    ·
                      rfl

theorem cell22_1675310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_1675310 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1675310 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1675310 prefixEnd_1675310 := by exact prefixLift 1675310
  have htrace : WordTrace (prefixWord ++ tailWord_1675310) baseStart_1675310 baseEnd_1675310 := by
    simpa [prefixWord, tailWord_1675310, baseEnd_1675310] using wordTrace_append hprefix tailTrace_1675310
  have hstable : (prefixWord ++ tailWord_1675310).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1675310).length < 2 ^ (prefixWord ++ tailWord_1675310).sum := by decide
  have hdescent : baseEnd_1675310 < baseStart_1675310 := by decide
  rcases family_descends (prefixWord ++ tailWord_1675310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1675389 : List Nat := [1, 4, 1, 1, 3, 2, 3, 3, 1, 3]
def baseStart_1675389 : Nat := 118140960795 + 1675389 * 2 ^ 59
def prefixEnd_1675389 : Nat := 4983230072969 + 3 ^ 40 * 1675389 * 2
def baseEnd_1675389 : Nat := 573519893503767177688355

theorem tailTrace_1675389 : CollatzResearch.WordTrace tailWord_1675389 prefixEnd_1675389 573519893503767177688355 := by
  unfold tailWord_1675389
  simp only [CollatzResearch.WordTrace]
  refine ⟨61106456927359261506045221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40737637951572841004030147 61106456927359261506045221)
  ·
    refine ⟨11457460673879861532383479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61106456927359261506045221 11457460673879861532383479)
    ·
      refine ⟨17186191010819792298575219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11457460673879861532383479 17186191010819792298575219)
      ·
        refine ⟨25779286516229688447862829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17186191010819792298575219 25779286516229688447862829)
        ·
          refine ⟨9667232443586133167948561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25779286516229688447862829 9667232443586133167948561)
          ·
            refine ⟨7250424332689599875961421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9667232443586133167948561 7250424332689599875961421)
            ·
              refine ⟨2718909124758599953485533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7250424332689599875961421 2718909124758599953485533)
              ·
                refine ⟨1019590921784474982557075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2718909124758599953485533 1019590921784474982557075)
                ·
                  refine ⟨1529386382676712473835613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1019590921784474982557075 1529386382676712473835613)
                  ·
                    refine ⟨573519893503767177688355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1529386382676712473835613 573519893503767177688355)
                    ·
                      rfl

theorem cell22_1675389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 3, 3, 1, 3].length) (baseStart_1675389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1675389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1675389 prefixEnd_1675389 := by exact prefixLift 1675389
  have htrace : WordTrace (prefixWord ++ tailWord_1675389) baseStart_1675389 baseEnd_1675389 := by
    simpa [prefixWord, tailWord_1675389, baseEnd_1675389] using wordTrace_append hprefix tailTrace_1675389
  have hstable : (prefixWord ++ tailWord_1675389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1675389).length < 2 ^ (prefixWord ++ tailWord_1675389).sum := by decide
  have hdescent : baseEnd_1675389 < baseStart_1675389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1675389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1675406 : List Nat := [4, 1, 1, 3, 4, 1, 1, 1, 3, 3]
def baseStart_1675406 : Nat := 118140960795 + 1675406 * 2 ^ 59
def prefixEnd_1675406 : Nat := 4983230072969 + 3 ^ 40 * 1675406 * 2
def baseEnd_1675406 : Nat := 573525712951184800013303

theorem tailTrace_1675406 : CollatzResearch.WordTrace tailWord_1675406 prefixEnd_1675406 573525712951184800013303 := by
  unfold tailWord_1675406
  simp only [CollatzResearch.WordTrace]
  refine ⟨7638384621037209176176759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40738051312198448939609381 7638384621037209176176759)
  ·
    refine ⟨11457576931555813764265139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7638384621037209176176759 11457576931555813764265139)
    ·
      refine ⟨17186365397333720646397709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11457576931555813764265139 17186365397333720646397709)
      ·
        refine ⟨6444887024000145242399141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17186365397333720646397709 6444887024000145242399141)
        ·
          refine ⟨1208416317000027232949839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6444887024000145242399141 1208416317000027232949839)
          ·
            refine ⟨1812624475500040849424759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1208416317000027232949839 1812624475500040849424759)
            ·
              refine ⟨2718936713250061274137139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1812624475500040849424759 2718936713250061274137139)
              ·
                refine ⟨4078405069875091911205709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2718936713250061274137139 4078405069875091911205709)
                ·
                  refine ⟨1529401901203159466702141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4078405069875091911205709 1529401901203159466702141)
                  ·
                    refine ⟨573525712951184800013303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1529401901203159466702141 573525712951184800013303)
                    ·
                      rfl

theorem cell22_1675406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 1, 1, 3, 3].length) (baseStart_1675406 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1675406 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1675406 prefixEnd_1675406 := by exact prefixLift 1675406
  have htrace : WordTrace (prefixWord ++ tailWord_1675406) baseStart_1675406 baseEnd_1675406 := by
    simpa [prefixWord, tailWord_1675406, baseEnd_1675406] using wordTrace_append hprefix tailTrace_1675406
  have hstable : (prefixWord ++ tailWord_1675406).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1675406).length < 2 ^ (prefixWord ++ tailWord_1675406).sum := by decide
  have hdescent : baseEnd_1675406 < baseStart_1675406 := by decide
  rcases family_descends (prefixWord ++ tailWord_1675406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1675567 : List Nat := [1, 1, 2, 1, 2, 1, 6, 3, 1, 4]
def baseStart_1675567 : Nat := 118140960795 + 1675567 * 2 ^ 59
def prefixEnd_1675567 : Nat := 4983230072969 + 3 ^ 40 * 1675567 * 2
def baseEnd_1675567 : Nat := 573580826541434046737809

theorem tailTrace_1675567 : CollatzResearch.WordTrace tailWord_1675567 prefixEnd_1675567 573580826541434046737809 := by
  unfold tailWord_1675567
  simp only [CollatzResearch.WordTrace]
  refine ⟨61112949120714397906024955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40741966080476265270683303 61112949120714397906024955)
  ·
    refine ⟨91669423681071596859037433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61112949120714397906024955 91669423681071596859037433)
    ·
      refine ⟨68752067760803697644278075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91669423681071596859037433 68752067760803697644278075)
      ·
        refine ⟨103128101641205546466417113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68752067760803697644278075 103128101641205546466417113)
        ·
          refine ⟨77346076230904159849812835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103128101641205546466417113 77346076230904159849812835)
          ·
            refine ⟨116019114346356239774719253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77346076230904159849812835 116019114346356239774719253)
            ·
              refine ⟨5438395984985448739439965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 116019114346356239774719253 5438395984985448739439965)
              ·
                refine ⟨2039398494369543277289987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5438395984985448739439965 2039398494369543277289987)
                ·
                  refine ⟨3059097741554314915934981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2039398494369543277289987 3059097741554314915934981)
                  ·
                    refine ⟨573580826541434046737809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3059097741554314915934981 573580826541434046737809)
                    ·
                      rfl

theorem cell22_1675567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 3, 1, 4].length) (baseStart_1675567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1675567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1675567 prefixEnd_1675567 := by exact prefixLift 1675567
  have htrace : WordTrace (prefixWord ++ tailWord_1675567) baseStart_1675567 baseEnd_1675567 := by
    simpa [prefixWord, tailWord_1675567, baseEnd_1675567] using wordTrace_append hprefix tailTrace_1675567
  have hstable : (prefixWord ++ tailWord_1675567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1675567).length < 2 ^ (prefixWord ++ tailWord_1675567).sum := by decide
  have hdescent : baseEnd_1675567 < baseStart_1675567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1675567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1675588 : List Nat := [2, 3, 4, 1, 2, 2, 2, 1, 5]
def baseStart_1675588 : Nat := 118140960795 + 1675588 * 2 ^ 59
def prefixEnd_1675588 : Nat := 4983230072969 + 3 ^ 40 * 1675588 * 2
def baseEnd_1675588 : Nat := 191196005090198997320915

theorem tailTrace_1675588 : CollatzResearch.WordTrace tailWord_1675588 prefixEnd_1675588 191196005090198997320915 := by
  unfold tailWord_1675588
  simp only [CollatzResearch.WordTrace]
  refine ⟨30556857526819159246269709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40742476702425545661692945 30556857526819159246269709)
  ·
    refine ⟨11458821572557184717351141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30556857526819159246269709 11458821572557184717351141)
    ·
      refine ⟨2148529044854472134503339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11458821572557184717351141 2148529044854472134503339)
      ·
        refine ⟨3222793567281708201755009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2148529044854472134503339 3222793567281708201755009)
        ·
          refine ⟨2417095175461281151316257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3222793567281708201755009 2417095175461281151316257)
          ·
            refine ⟨1812821381595960863487193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2417095175461281151316257 1812821381595960863487193)
            ·
              refine ⟨1359616036196970647615395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1812821381595960863487193 1359616036196970647615395)
              ·
                refine ⟨2039424054295455971423093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1359616036196970647615395 2039424054295455971423093)
                ·
                  refine ⟨191196005090198997320915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2039424054295455971423093 191196005090198997320915)
                  ·
                    rfl

theorem cell22_1675588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 2, 1, 5].length) (baseStart_1675588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1675588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1675588 prefixEnd_1675588 := by exact prefixLift 1675588
  have htrace : WordTrace (prefixWord ++ tailWord_1675588) baseStart_1675588 baseEnd_1675588 := by
    simpa [prefixWord, tailWord_1675588, baseEnd_1675588] using wordTrace_append hprefix tailTrace_1675588
  have hstable : (prefixWord ++ tailWord_1675588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1675588).length < 2 ^ (prefixWord ++ tailWord_1675588).sum := by decide
  have hdescent : baseEnd_1675588 < baseStart_1675588 := by decide
  rcases family_descends (prefixWord ++ tailWord_1675588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1675595 : List Nat := [1, 1, 1, 1, 3, 1, 1, 6, 1, 6]
def baseStart_1675595 : Nat := 118140960795 + 1675595 * 2 ^ 59
def prefixEnd_1675595 : Nat := 4983230072969 + 3 ^ 40 * 1675595 * 2
def baseEnd_1675595 : Nat := 573590411513651307037723

theorem tailTrace_1675595 : CollatzResearch.WordTrace tailWord_1675595 prefixEnd_1675595 573590411513651307037723 := by
  unfold tailWord_1675595
  simp only [CollatzResearch.WordTrace]
  refine ⟨61113970364612958688044239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40742646909741972458696159 61113970364612958688044239)
  ·
    refine ⟨91670955546919438032066359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61113970364612958688044239 91670955546919438032066359)
    ·
      refine ⟨137506433320379157048099539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91670955546919438032066359 137506433320379157048099539)
      ·
        refine ⟨206259649980568735572149309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137506433320379157048099539 206259649980568735572149309)
        ·
          refine ⟨77347368742713275839555991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 206259649980568735572149309 77347368742713275839555991)
          ·
            refine ⟨116021053114069913759333987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77347368742713275839555991 116021053114069913759333987)
            ·
              refine ⟨174031579671104870639000981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116021053114069913759333987 174031579671104870639000981)
              ·
                refine ⟨8157730297083040811203171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 174031579671104870639000981 8157730297083040811203171)
                ·
                  refine ⟨12236595445624561216804757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8157730297083040811203171 12236595445624561216804757)
                  ·
                    refine ⟨573590411513651307037723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12236595445624561216804757 573590411513651307037723)
                    ·
                      rfl

theorem cell22_1675595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 6, 1, 6].length) (baseStart_1675595 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1675595 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1675595 prefixEnd_1675595 := by exact prefixLift 1675595
  have htrace : WordTrace (prefixWord ++ tailWord_1675595) baseStart_1675595 baseEnd_1675595 := by
    simpa [prefixWord, tailWord_1675595, baseEnd_1675595] using wordTrace_append hprefix tailTrace_1675595
  have hstable : (prefixWord ++ tailWord_1675595).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1675595).length < 2 ^ (prefixWord ++ tailWord_1675595).sum := by decide
  have hdescent : baseEnd_1675595 < baseStart_1675595 := by decide
  rcases family_descends (prefixWord ++ tailWord_1675595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1675659 : List Nat := [1, 1, 1, 1, 4, 5, 1, 2, 3, 3]
def baseStart_1675659 : Nat := 118140960795 + 1675659 * 2 ^ 59
def prefixEnd_1675659 : Nat := 4983230072969 + 3 ^ 40 * 1675659 * 2
def baseEnd_1675659 : Nat := 573612320021576473437527

theorem tailTrace_1675659 : CollatzResearch.WordTrace tailWord_1675659 prefixEnd_1675659 573612320021576473437527 := by
  unfold tailWord_1675659
  simp only [CollatzResearch.WordTrace]
  refine ⟨61116304636381097618374031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40744203090920731745582687 61116304636381097618374031)
  ·
    refine ⟨91674456954571646427561047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61116304636381097618374031 91674456954571646427561047)
    ·
      refine ⟨137511685431857469641341571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91674456954571646427561047 137511685431857469641341571)
      ·
        refine ⟨206267528147786204462012357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137511685431857469641341571 206267528147786204462012357)
        ·
          refine ⟨38675161527709913336627317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 206267528147786204462012357 38675161527709913336627317)
          ·
            refine ⟨3625796393222804375308811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38675161527709913336627317 3625796393222804375308811)
            ·
              refine ⟨5438694589834206562963217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3625796393222804375308811 5438694589834206562963217)
              ·
                refine ⟨4079020942375654922222413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5438694589834206562963217 4079020942375654922222413)
                ·
                  refine ⟨1529632853390870595833405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4079020942375654922222413 1529632853390870595833405)
                  ·
                    refine ⟨573612320021576473437527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1529632853390870595833405 573612320021576473437527)
                    ·
                      rfl

theorem cell22_1675659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 2, 3, 3].length) (baseStart_1675659 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1675659 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1675659 prefixEnd_1675659 := by exact prefixLift 1675659
  have htrace : WordTrace (prefixWord ++ tailWord_1675659) baseStart_1675659 baseEnd_1675659 := by
    simpa [prefixWord, tailWord_1675659, baseEnd_1675659] using wordTrace_append hprefix tailTrace_1675659
  have hstable : (prefixWord ++ tailWord_1675659).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1675659).length < 2 ^ (prefixWord ++ tailWord_1675659).sum := by decide
  have hdescent : baseEnd_1675659 < baseStart_1675659 := by decide
  rcases family_descends (prefixWord ++ tailWord_1675659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1675693 : List Nat := [1, 5, 2, 2, 2, 1, 2, 1, 3, 3]
def baseStart_1675693 : Nat := 118140960795 + 1675693 * 2 ^ 59
def prefixEnd_1675693 : Nat := 4983230072969 + 3 ^ 40 * 1675693 * 2
def baseEnd_1675693 : Nat := 573623958916411718087423

theorem tailTrace_1675693 : CollatzResearch.WordTrace tailWord_1675693 prefixEnd_1675693 573623958916411718087423 := by
  unfold tailWord_1675693
  simp only [CollatzResearch.WordTrace]
  refine ⟨61117544718257921425111733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40745029812171947616741155 61117544718257921425111733)
  ·
    refine ⟨5729769817336680133604225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 61117544718257921425111733 5729769817336680133604225)
    ·
      refine ⟨4297327363002510100203169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5729769817336680133604225 4297327363002510100203169)
      ·
        refine ⟨3222995522251882575152377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4297327363002510100203169 3222995522251882575152377)
        ·
          refine ⟨2417246641688911931364283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3222995522251882575152377 2417246641688911931364283)
          ·
            refine ⟨3625869962533367897046425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2417246641688911931364283 3625869962533367897046425)
            ·
              refine ⟨2719402471900025922784819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3625869962533367897046425 2719402471900025922784819)
              ·
                refine ⟨4079103707850038884177229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2719402471900025922784819 4079103707850038884177229)
                ·
                  refine ⟨1529663890443764581566461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4079103707850038884177229 1529663890443764581566461)
                  ·
                    refine ⟨573623958916411718087423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1529663890443764581566461 573623958916411718087423)
                    ·
                      rfl

theorem cell22_1675693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 2, 1, 3, 3].length) (baseStart_1675693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1675693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1675693 prefixEnd_1675693 := by exact prefixLift 1675693
  have htrace : WordTrace (prefixWord ++ tailWord_1675693) baseStart_1675693 baseEnd_1675693 := by
    simpa [prefixWord, tailWord_1675693, baseEnd_1675693] using wordTrace_append hprefix tailTrace_1675693
  have hstable : (prefixWord ++ tailWord_1675693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1675693).length < 2 ^ (prefixWord ++ tailWord_1675693).sum := by decide
  have hdescent : baseEnd_1675693 < baseStart_1675693 := by decide
  rcases family_descends (prefixWord ++ tailWord_1675693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1675719 : List Nat := [1, 1, 4, 1, 1, 4, 1, 4, 1, 4]
def baseStart_1675719 : Nat := 118140960795 + 1675719 * 2 ^ 59
def prefixEnd_1675719 : Nat := 4983230072969 + 3 ^ 40 * 1675719 * 2
def baseEnd_1675719 : Nat := 573632859247756316937343

theorem tailTrace_1675719 : CollatzResearch.WordTrace tailWord_1675719 prefixEnd_1675719 573632859247756316937343 := by
  unfold tailWord_1675719
  simp only [CollatzResearch.WordTrace]
  refine ⟨61118493016163727865558211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40745662010775818577038807 61118493016163727865558211)
  ·
    refine ⟨91677739524245591798337317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61118493016163727865558211 91677739524245591798337317)
    ·
      refine ⟨17189576160796048462188247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91677739524245591798337317 17189576160796048462188247)
      ·
        refine ⟨25784364241194072693282371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17189576160796048462188247 25784364241194072693282371)
        ·
          refine ⟨38676546361791109039923557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25784364241194072693282371 38676546361791109039923557)
          ·
            refine ⟨7251852442835832944985667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38676546361791109039923557 7251852442835832944985667)
            ·
              refine ⟨10877778664253749417478501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7251852442835832944985667 10877778664253749417478501)
              ·
                refine ⟨2039583499547578015777219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10877778664253749417478501 2039583499547578015777219)
                ·
                  refine ⟨3059375249321367023665829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2039583499547578015777219 3059375249321367023665829)
                  ·
                    refine ⟨573632859247756316937343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3059375249321367023665829 573632859247756316937343)
                    ·
                      rfl

theorem cell22_1675719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 4, 1, 4].length) (baseStart_1675719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1675719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1675719 prefixEnd_1675719 := by exact prefixLift 1675719
  have htrace : WordTrace (prefixWord ++ tailWord_1675719) baseStart_1675719 baseEnd_1675719 := by
    simpa [prefixWord, tailWord_1675719, baseEnd_1675719] using wordTrace_append hprefix tailTrace_1675719
  have hstable : (prefixWord ++ tailWord_1675719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1675719).length < 2 ^ (prefixWord ++ tailWord_1675719).sum := by decide
  have hdescent : baseEnd_1675719 < baseStart_1675719 := by decide
  rcases family_descends (prefixWord ++ tailWord_1675719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1675824 : List Nat := [2, 1, 1, 1, 2, 3, 4, 3, 5]
def baseStart_1675824 : Nat := 118140960795 + 1675824 * 2 ^ 59
def prefixEnd_1675824 : Nat := 4983230072969 + 3 ^ 40 * 1675824 * 2
def baseEnd_1675824 : Nat := 191222934297857014354007

theorem tailTrace_1675824 : CollatzResearch.WordTrace tailWord_1675824 prefixEnd_1675824 191222934297857014354007 := by
  unfold tailWord_1675824
  simp only [CollatzResearch.WordTrace]
  refine ⟨30561161340391665399065263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40748215120522220532087017 30561161340391665399065263)
  ·
    refine ⟨45841742010587498098597895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30561161340391665399065263 45841742010587498098597895)
    ·
      refine ⟨68762613015881247147896843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45841742010587498098597895 68762613015881247147896843)
      ·
        refine ⟨103143919523821870721845265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68762613015881247147896843 103143919523821870721845265)
        ·
          refine ⟨77357939642866403041383949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103143919523821870721845265 77357939642866403041383949)
          ·
            refine ⟨29009227366074901140518981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77357939642866403041383949 29009227366074901140518981)
            ·
              refine ⟨5439230131139043963847309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29009227366074901140518981 5439230131139043963847309)
              ·
                refine ⟨2039711299177141486442741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5439230131139043963847309 2039711299177141486442741)
                ·
                  refine ⟨191222934297857014354007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2039711299177141486442741 191222934297857014354007)
                  ·
                    rfl

theorem cell22_1675824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 3, 5].length) (baseStart_1675824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1675824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1675824 prefixEnd_1675824 := by exact prefixLift 1675824
  have htrace : WordTrace (prefixWord ++ tailWord_1675824) baseStart_1675824 baseEnd_1675824 := by
    simpa [prefixWord, tailWord_1675824, baseEnd_1675824] using wordTrace_append hprefix tailTrace_1675824
  have hstable : (prefixWord ++ tailWord_1675824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1675824).length < 2 ^ (prefixWord ++ tailWord_1675824).sum := by decide
  have hdescent : baseEnd_1675824 < baseStart_1675824 := by decide
  rcases family_descends (prefixWord ++ tailWord_1675824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1675886 : List Nat := [4, 1, 2, 2, 2, 1, 2, 2, 6]
def baseStart_1675886 : Nat := 118140960795 + 1675886 * 2 ^ 59
def prefixEnd_1675886 : Nat := 4983230072969 + 3 ^ 40 * 1675886 * 2
def baseEnd_1675886 : Nat := 191230008920207849337277

theorem tailTrace_1675886 : CollatzResearch.WordTrace tailWord_1675886 prefixEnd_1675886 191230008920207849337277 := by
  unfold tailWord_1675886
  simp only [CollatzResearch.WordTrace]
  refine ⟨7640573000819839423360939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40749722671039143591258341 7640573000819839423360939)
  ·
    refine ⟨11460859501229759135041409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7640573000819839423360939 11460859501229759135041409)
    ·
      refine ⟨8595644625922319351281057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11460859501229759135041409 8595644625922319351281057)
      ·
        refine ⟨6446733469441739513460793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8595644625922319351281057 6446733469441739513460793)
        ·
          refine ⟨4835050102081304635095595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6446733469441739513460793 4835050102081304635095595)
          ·
            refine ⟨7252575153121956952643393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4835050102081304635095595 7252575153121956952643393)
            ·
              refine ⟨5439431364841467714482545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7252575153121956952643393 5439431364841467714482545)
              ·
                refine ⟨4079573523631100785861909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5439431364841467714482545 4079573523631100785861909)
                ·
                  refine ⟨191230008920207849337277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4079573523631100785861909 191230008920207849337277)
                  ·
                    rfl

theorem cell22_1675886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 2, 6].length) (baseStart_1675886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1675886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1675886 prefixEnd_1675886 := by exact prefixLift 1675886
  have htrace : WordTrace (prefixWord ++ tailWord_1675886) baseStart_1675886 baseEnd_1675886 := by
    simpa [prefixWord, tailWord_1675886, baseEnd_1675886] using wordTrace_append hprefix tailTrace_1675886
  have hstable : (prefixWord ++ tailWord_1675886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1675886).length < 2 ^ (prefixWord ++ tailWord_1675886).sum := by decide
  have hdescent : baseEnd_1675886 < baseStart_1675886 := by decide
  rcases family_descends (prefixWord ++ tailWord_1675886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1675888 : List Nat := [2, 1, 1, 1, 7, 1, 2, 2, 1, 4]
def baseStart_1675888 : Nat := 118140960795 + 1675888 * 2 ^ 59
def prefixEnd_1675888 : Nat := 4983230072969 + 3 ^ 40 * 1675888 * 2
def baseEnd_1675888 : Nat := 573690711401496209461825

theorem tailTrace_1675888 : CollatzResearch.WordTrace tailWord_1675888 prefixEnd_1675888 573690711401496209461825 := by
  unfold tailWord_1675888
  simp only [CollatzResearch.WordTrace]
  refine ⟨30562328476275734864230159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40749771301700979818973545 30562328476275734864230159)
  ·
    refine ⟨45843492714413602296345239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30562328476275734864230159 45843492714413602296345239)
    ·
      refine ⟨68765239071620403444517859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45843492714413602296345239 68765239071620403444517859)
      ·
        refine ⟨103147858607430605166776789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68765239071620403444517859 103147858607430605166776789)
        ·
          refine ⟨2417527936111654808596331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 103147858607430605166776789 2417527936111654808596331)
          ·
            refine ⟨3626291904167482212894497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2417527936111654808596331 3626291904167482212894497)
            ·
              refine ⟨2719718928125611659670873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3626291904167482212894497 2719718928125611659670873)
              ·
                refine ⟨2039789196094208744753155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2719718928125611659670873 2039789196094208744753155)
                ·
                  refine ⟨3059683794141313117129733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2039789196094208744753155 3059683794141313117129733)
                  ·
                    refine ⟨573690711401496209461825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3059683794141313117129733 573690711401496209461825)
                    ·
                      rfl

theorem cell22_1675888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 2, 2, 1, 4].length) (baseStart_1675888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1675888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1675888 prefixEnd_1675888 := by exact prefixLift 1675888
  have htrace : WordTrace (prefixWord ++ tailWord_1675888) baseStart_1675888 baseEnd_1675888 := by
    simpa [prefixWord, tailWord_1675888, baseEnd_1675888] using wordTrace_append hprefix tailTrace_1675888
  have hstable : (prefixWord ++ tailWord_1675888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1675888).length < 2 ^ (prefixWord ++ tailWord_1675888).sum := by decide
  have hdescent : baseEnd_1675888 < baseStart_1675888 := by decide
  rcases family_descends (prefixWord ++ tailWord_1675888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1675918 : List Nat := [4, 1, 1, 3, 1, 1, 2, 4, 2, 3]
def baseStart_1675918 : Nat := 118140960795 + 1675918 * 2 ^ 59
def prefixEnd_1675918 : Nat := 4983230072969 + 3 ^ 40 * 1675918 * 2
def baseEnd_1675918 : Nat := 573700981014586131211733

theorem tailTrace_1675918 : CollatzResearch.WordTrace tailWord_1675918 prefixEnd_1675918 573700981014586131211733 := by
  unfold tailWord_1675918
  simp only [CollatzResearch.WordTrace]
  refine ⟨7640718892805348106506551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40750500761628523234701605 7640718892805348106506551)
  ·
    refine ⟨11461078339208022159759827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7640718892805348106506551 11461078339208022159759827)
    ·
      refine ⟨17191617508812033239639741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11461078339208022159759827 17191617508812033239639741)
      ·
        refine ⟨6446856565804512464864903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17191617508812033239639741 6446856565804512464864903)
        ·
          refine ⟨9670284848706768697297355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6446856565804512464864903 9670284848706768697297355)
          ·
            refine ⟨14505427273060153045946033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9670284848706768697297355 14505427273060153045946033)
            ·
              refine ⟨10879070454795114784459525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14505427273060153045946033 10879070454795114784459525)
              ·
                refine ⟨2039825710274084022086161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10879070454795114784459525 2039825710274084022086161)
                ·
                  refine ⟨1529869282705563016564621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2039825710274084022086161 1529869282705563016564621)
                  ·
                    refine ⟨573700981014586131211733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1529869282705563016564621 573700981014586131211733)
                    ·
                      rfl

theorem cell22_1675918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 4, 2, 3].length) (baseStart_1675918 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1675918 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1675918 prefixEnd_1675918 := by exact prefixLift 1675918
  have htrace : WordTrace (prefixWord ++ tailWord_1675918) baseStart_1675918 baseEnd_1675918 := by
    simpa [prefixWord, tailWord_1675918, baseEnd_1675918] using wordTrace_append hprefix tailTrace_1675918
  have hstable : (prefixWord ++ tailWord_1675918).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1675918).length < 2 ^ (prefixWord ++ tailWord_1675918).sum := by decide
  have hdescent : baseEnd_1675918 < baseStart_1675918 := by decide
  rcases family_descends (prefixWord ++ tailWord_1675918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1675950 : List Nat := [4, 1, 4, 1, 1, 2, 2, 1, 2, 4]
def baseStart_1675950 : Nat := 118140960795 + 1675950 * 2 ^ 59
def prefixEnd_1675950 : Nat := 4983230072969 + 3 ^ 40 * 1675950 * 2
def baseEnd_1675950 : Nat := 573711935268548714411635

theorem tailTrace_1675950 : CollatzResearch.WordTrace tailWord_1675950 prefixEnd_1675950 573711935268548714411635 := by
  unfold tailWord_1675950
  simp only [CollatzResearch.WordTrace]
  refine ⟨7640864784790856789652163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40751278852217902878144869 7640864784790856789652163)
  ·
    refine ⟨11461297177186285184478245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7640864784790856789652163 11461297177186285184478245)
    ·
      refine ⟨2148993220722428472089671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11461297177186285184478245 2148993220722428472089671)
      ·
        refine ⟨3223489831083642708134507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2148993220722428472089671 3223489831083642708134507)
        ·
          refine ⟨4835234746625464062201761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3223489831083642708134507 4835234746625464062201761)
          ·
            refine ⟨3626426059969098046651321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4835234746625464062201761 3626426059969098046651321)
            ·
              refine ⟨2719819544976823534988491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3626426059969098046651321 2719819544976823534988491)
              ·
                refine ⟨4079729317465235302482737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2719819544976823534988491 4079729317465235302482737)
                ·
                  refine ⟨3059796988098926476862053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4079729317465235302482737 3059796988098926476862053)
                  ·
                    refine ⟨573711935268548714411635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3059796988098926476862053 573711935268548714411635)
                    ·
                      rfl

theorem cell22_1675950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_1675950 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1675950 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1675950 prefixEnd_1675950 := by exact prefixLift 1675950
  have htrace : WordTrace (prefixWord ++ tailWord_1675950) baseStart_1675950 baseEnd_1675950 := by
    simpa [prefixWord, tailWord_1675950, baseEnd_1675950] using wordTrace_append hprefix tailTrace_1675950
  have hstable : (prefixWord ++ tailWord_1675950).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1675950).length < 2 ^ (prefixWord ++ tailWord_1675950).sum := by decide
  have hdescent : baseEnd_1675950 < baseStart_1675950 := by decide
  rcases family_descends (prefixWord ++ tailWord_1675950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1675976 : List Nat := [2, 1, 3, 1, 2, 3, 1, 4, 5]
def baseStart_1675976 : Nat := 118140960795 + 1675976 * 2 ^ 59
def prefixEnd_1675976 : Nat := 4983230072969 + 3 ^ 40 * 1675976 * 2
def baseEnd_1675976 : Nat := 191240278533297771087185

theorem tailTrace_1675976 : CollatzResearch.WordTrace tailWord_1675976 prefixEnd_1675976 191240278533297771087185 := by
  unfold tailWord_1675976
  simp only [CollatzResearch.WordTrace]
  refine ⟨30563933288116330378831891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40751911050821773838442521 30563933288116330378831891)
  ·
    refine ⟨45845899932174495568247837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30563933288116330378831891 45845899932174495568247837)
    ·
      refine ⟨17192212474565435838092939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45845899932174495568247837 17192212474565435838092939)
      ·
        refine ⟨25788318711848153757139409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17192212474565435838092939 25788318711848153757139409)
        ·
          refine ⟨19341239033886115317854557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25788318711848153757139409 19341239033886115317854557)
          ·
            refine ⟨7252964637707293244195459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19341239033886115317854557 7252964637707293244195459)
            ·
              refine ⟨10879446956560939866293189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7252964637707293244195459 10879446956560939866293189)
              ·
                refine ⟨2039896304355176224929973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10879446956560939866293189 2039896304355176224929973)
                ·
                  refine ⟨191240278533297771087185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2039896304355176224929973 191240278533297771087185)
                  ·
                    rfl

theorem cell22_1675976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 4, 5].length) (baseStart_1675976 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1675976 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1675976 prefixEnd_1675976 := by exact prefixLift 1675976
  have htrace : WordTrace (prefixWord ++ tailWord_1675976) baseStart_1675976 baseEnd_1675976 := by
    simpa [prefixWord, tailWord_1675976, baseEnd_1675976] using wordTrace_append hprefix tailTrace_1675976
  have hstable : (prefixWord ++ tailWord_1675976).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1675976).length < 2 ^ (prefixWord ++ tailWord_1675976).sum := by decide
  have hdescent : baseEnd_1675976 < baseStart_1675976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1675976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1675991 : List Nat := [1, 1, 3, 2, 1, 5, 1, 1, 2, 5]
def baseStart_1675991 : Nat := 118140960795 + 1675991 * 2 ^ 59
def prefixEnd_1675991 : Nat := 4983230072969 + 3 ^ 40 * 1675991 * 2
def baseEnd_1675991 : Nat := 573725970406438274136509

theorem tailTrace_1675991 : CollatzResearch.WordTrace tailWord_1675991 prefixEnd_1675991 573725970406438274136509 := by
  unfold tailWord_1675991
  simp only [CollatzResearch.WordTrace]
  refine ⟨61128413671178318319459827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40752275780785545546306551 61128413671178318319459827)
  ·
    refine ⟨91692620506767477479189741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61128413671178318319459827 91692620506767477479189741)
    ·
      refine ⟨34384732690037804054696153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91692620506767477479189741 34384732690037804054696153)
      ·
        refine ⟨25788549517528353041022115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34384732690037804054696153 25788549517528353041022115)
        ·
          refine ⟨38682824276292529561533173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25788549517528353041022115 38682824276292529561533173)
          ·
            refine ⟨3626514775902424646393735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38682824276292529561533173 3626514775902424646393735)
            ·
              refine ⟨5439772163853636969590603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3626514775902424646393735 5439772163853636969590603)
              ·
                refine ⟨8159658245780455454385905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5439772163853636969590603 8159658245780455454385905)
                ·
                  refine ⟨6119743684335341590789429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8159658245780455454385905 6119743684335341590789429)
                  ·
                    refine ⟨573725970406438274136509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6119743684335341590789429 573725970406438274136509)
                    ·
                      rfl

theorem cell22_1675991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 1, 2, 5].length) (baseStart_1675991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1675991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1675991 prefixEnd_1675991 := by exact prefixLift 1675991
  have htrace : WordTrace (prefixWord ++ tailWord_1675991) baseStart_1675991 baseEnd_1675991 := by
    simpa [prefixWord, tailWord_1675991, baseEnd_1675991] using wordTrace_append hprefix tailTrace_1675991
  have hstable : (prefixWord ++ tailWord_1675991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1675991).length < 2 ^ (prefixWord ++ tailWord_1675991).sum := by decide
  have hdescent : baseEnd_1675991 < baseStart_1675991 := by decide
  rcases family_descends (prefixWord ++ tailWord_1675991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1676149 : List Nat := [1, 3, 4, 1, 1, 2, 4, 2, 1, 3]
def baseStart_1676149 : Nat := 118140960795 + 1676149 * 2 ^ 59
def prefixEnd_1676149 : Nat := 4983230072969 + 3 ^ 40 * 1676149 * 2
def baseEnd_1676149 : Nat := 573780057035378528686025

theorem tailTrace_1676149 : CollatzResearch.WordTrace tailWord_1676149 prefixEnd_1676149 573780057035378528686025 := by
  unfold tailWord_1676149
  simp only [CollatzResearch.WordTrace]
  refine ⟨61134176404605911303711501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40756117603070607535807667 61134176404605911303711501)
  ·
    refine ⟨22925316151727216738891813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61134176404605911303711501 22925316151727216738891813)
    ·
      refine ⟨4298496778448853138542215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22925316151727216738891813 4298496778448853138542215)
      ·
        refine ⟨6447745167673279707813323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4298496778448853138542215 6447745167673279707813323)
        ·
          refine ⟨9671617751509919561719985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6447745167673279707813323 9671617751509919561719985)
          ·
            refine ⟨7253713313632439671289989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9671617751509919561719985 7253713313632439671289989)
            ·
              refine ⟨1360071246306082438366873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7253713313632439671289989 1360071246306082438366873)
              ·
                refine ⟨1020053434729561828775155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1360071246306082438366873 1020053434729561828775155)
                ·
                  refine ⟨1530080152094342743162733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1020053434729561828775155 1530080152094342743162733)
                  ·
                    refine ⟨573780057035378528686025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1530080152094342743162733 573780057035378528686025)
                    ·
                      rfl

theorem cell22_1676149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 4, 2, 1, 3].length) (baseStart_1676149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1676149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1676149 prefixEnd_1676149 := by exact prefixLift 1676149
  have htrace : WordTrace (prefixWord ++ tailWord_1676149) baseStart_1676149 baseEnd_1676149 := by
    simpa [prefixWord, tailWord_1676149, baseEnd_1676149] using wordTrace_append hprefix tailTrace_1676149
  have hstable : (prefixWord ++ tailWord_1676149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1676149).length < 2 ^ (prefixWord ++ tailWord_1676149).sum := by decide
  have hdescent : baseEnd_1676149 < baseStart_1676149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1676149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1676156 : List Nat := [2, 2, 2, 1, 1, 1, 1, 2, 10]
def baseStart_1676156 : Nat := 118140960795 + 1676156 * 2 ^ 59
def prefixEnd_1676156 : Nat := 4983230072969 + 3 ^ 40 * 1676156 * 2
def baseEnd_1676156 : Nat := 191260817759477614587001

theorem tailTrace_1676156 : CollatzResearch.WordTrace tailWord_1676156 prefixEnd_1676156 191260817759477614587001 := by
  unfold tailWord_1676156
  simp only [CollatzResearch.WordTrace]
  refine ⟨30567215857790275749608161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40756287810387034332810881 30567215857790275749608161)
  ·
    refine ⟨22925411893342706812206121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30567215857790275749608161 22925411893342706812206121)
    ·
      refine ⟨17194058920007030109154591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22925411893342706812206121 17194058920007030109154591)
      ·
        refine ⟨25791088380010545163731887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17194058920007030109154591 25791088380010545163731887)
        ·
          refine ⟨38686632570015817745597831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25791088380010545163731887 38686632570015817745597831)
          ·
            refine ⟨58029948855023726618396747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38686632570015817745597831 58029948855023726618396747)
            ·
              refine ⟨87044923282535589927595121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58029948855023726618396747 87044923282535589927595121)
              ·
                refine ⟨65283692461901692445696341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87044923282535589927595121 65283692461901692445696341)
                ·
                  refine ⟨191260817759477614587001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 65283692461901692445696341 191260817759477614587001)
                  ·
                    rfl

theorem cell22_1676156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 10].length) (baseStart_1676156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1676156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1676156 prefixEnd_1676156 := by exact prefixLift 1676156
  have htrace : WordTrace (prefixWord ++ tailWord_1676156) baseStart_1676156 baseEnd_1676156 := by
    simpa [prefixWord, tailWord_1676156, baseEnd_1676156] using wordTrace_append hprefix tailTrace_1676156
  have hstable : (prefixWord ++ tailWord_1676156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1676156).length < 2 ^ (prefixWord ++ tailWord_1676156).sum := by decide
  have hdescent : baseEnd_1676156 < baseStart_1676156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1676156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1676201 : List Nat := [1, 2, 1, 1, 1, 1, 15]
def baseStart_1676201 : Nat := 118140960795 + 1676201 * 2 ^ 59
def prefixEnd_1676201 : Nat := 4983230072969 + 3 ^ 40 * 1676201 * 2
def baseEnd_1676201 : Nat := 21251772507335841717995

theorem tailTrace_1676201 : CollatzResearch.WordTrace tailWord_1676201 prefixEnd_1676201 21251772507335841717995 := by
  unfold tailWord_1676201
  simp only [CollatzResearch.WordTrace]
  refine ⟨61136073000417524184604457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40757382000278349456402971 61136073000417524184604457)
  ·
    refine ⟨45852054750313143138453343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61136073000417524184604457 45852054750313143138453343)
    ·
      refine ⟨68778082125469714707680015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45852054750313143138453343 68778082125469714707680015)
      ·
        refine ⟨103167123188204572061520023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68778082125469714707680015 103167123188204572061520023)
        ·
          refine ⟨154750684782306858092280035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103167123188204572061520023 154750684782306858092280035)
          ·
            refine ⟨232126027173460287138420053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154750684782306858092280035 232126027173460287138420053)
            ·
              refine ⟨21251772507335841717995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 15 232126027173460287138420053 21251772507335841717995)
              ·
                rfl

theorem cell22_1676201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 15].length) (baseStart_1676201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1676201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1676201 prefixEnd_1676201 := by exact prefixLift 1676201
  have htrace : WordTrace (prefixWord ++ tailWord_1676201) baseStart_1676201 baseEnd_1676201 := by
    simpa [prefixWord, tailWord_1676201, baseEnd_1676201] using wordTrace_append hprefix tailTrace_1676201
  have hstable : (prefixWord ++ tailWord_1676201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1676201).length < 2 ^ (prefixWord ++ tailWord_1676201).sum := by decide
  have hdescent : baseEnd_1676201 < baseStart_1676201 := by decide
  rcases family_descends (prefixWord ++ tailWord_1676201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1676235 : List Nat := [1, 1, 1, 1, 3, 7, 2, 6]
def baseStart_1676235 : Nat := 118140960795 + 1676235 * 2 ^ 59
def prefixEnd_1676235 : Nat := 4983230072969 + 3 ^ 40 * 1676235 * 2
def baseEnd_1676235 : Nat := 63756610732544774559529

theorem tailTrace_1676235 : CollatzResearch.WordTrace tailWord_1676235 prefixEnd_1676235 63756610732544774559529 := by
  unfold tailWord_1676235
  simp only [CollatzResearch.WordTrace]
  refine ⟨61137313082294347991342159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40758208721529565327561439 61137313082294347991342159)
  ·
    refine ⟨91705969623441521987013239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61137313082294347991342159 91705969623441521987013239)
    ·
      refine ⟨137558954435162282980519859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91705969623441521987013239 137558954435162282980519859)
      ·
        refine ⟨206338431652743424470779789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137558954435162282980519859 206338431652743424470779789)
        ·
          refine ⟨77376911869778784176542421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 206338431652743424470779789 77376911869778784176542421)
          ·
            refine ⟨1813521371947940254137713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 77376911869778784176542421 1813521371947940254137713)
            ·
              refine ⟨1360141028960955190603285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1813521371947940254137713 1360141028960955190603285)
              ·
                refine ⟨63756610732544774559529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1360141028960955190603285 63756610732544774559529)
                ·
                  rfl

theorem cell22_1676235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 2, 6].length) (baseStart_1676235 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1676235 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1676235 prefixEnd_1676235 := by exact prefixLift 1676235
  have htrace : WordTrace (prefixWord ++ tailWord_1676235) baseStart_1676235 baseEnd_1676235 := by
    simpa [prefixWord, tailWord_1676235, baseEnd_1676235] using wordTrace_append hprefix tailTrace_1676235
  have hstable : (prefixWord ++ tailWord_1676235).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1676235).length < 2 ^ (prefixWord ++ tailWord_1676235).sum := by decide
  have hdescent : baseEnd_1676235 < baseStart_1676235 := by decide
  rcases family_descends (prefixWord ++ tailWord_1676235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1676327 : List Nat := [1, 1, 7, 1, 1, 1, 1, 2, 3, 4]
def baseStart_1676327 : Nat := 118140960795 + 1676327 * 2 ^ 59
def prefixEnd_1676327 : Nat := 4983230072969 + 3 ^ 40 * 1676327 * 2
def baseEnd_1676327 : Nat := 573840990073045397735479

theorem tailTrace_1676327 : CollatzResearch.WordTrace tailWord_1676327 prefixEnd_1676327 573840990073045397735479 := by
  unfold tailWord_1676327
  simp only [CollatzResearch.WordTrace]
  refine ⟨61140668597961047703691235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40760445731974031802460823 61140668597961047703691235)
  ·
    refine ⟨91711002896941571555536853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61140668597961047703691235 91711002896941571555536853)
    ·
      refine ⟨2149476630397068083332895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 91711002896941571555536853 2149476630397068083332895)
      ·
        refine ⟨3224214945595602124999343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2149476630397068083332895 3224214945595602124999343)
        ·
          refine ⟨4836322418393403187499015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3224214945595602124999343 4836322418393403187499015)
          ·
            refine ⟨7254483627590104781248523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4836322418393403187499015 7254483627590104781248523)
            ·
              refine ⟨10881725441385157171872785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7254483627590104781248523 10881725441385157171872785)
              ·
                refine ⟨8161294081038867878904589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10881725441385157171872785 8161294081038867878904589)
                ·
                  refine ⟨3060485280389575454589221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8161294081038867878904589 3060485280389575454589221)
                  ·
                    refine ⟨573840990073045397735479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3060485280389575454589221 573840990073045397735479)
                    ·
                      rfl

theorem cell22_1676327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_1676327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1676327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1676327 prefixEnd_1676327 := by exact prefixLift 1676327
  have htrace : WordTrace (prefixWord ++ tailWord_1676327) baseStart_1676327 baseEnd_1676327 := by
    simpa [prefixWord, tailWord_1676327, baseEnd_1676327] using wordTrace_append hprefix tailTrace_1676327
  have hstable : (prefixWord ++ tailWord_1676327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1676327).length < 2 ^ (prefixWord ++ tailWord_1676327).sum := by decide
  have hdescent : baseEnd_1676327 < baseStart_1676327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1676327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1676342 : List Nat := [5, 1, 2, 1, 1, 3, 1, 2, 6]
def baseStart_1676342 : Nat := 118140960795 + 1676342 * 2 ^ 59
def prefixEnd_1676342 : Nat := 4983230072969 + 3 ^ 40 * 1676342 * 2
def baseEnd_1676342 : Nat := 191282041626530119536811

theorem tailTrace_1676342 : CollatzResearch.WordTrace tailWord_1676342 prefixEnd_1676342 191282041626530119536811 := by
  unfold tailWord_1676342
  simp only [CollatzResearch.WordTrace]
  refine ⟨3821325980806669079092955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40760810461937803510324853 3821325980806669079092955)
  ·
    refine ⟨5731988971210003618639433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3821325980806669079092955 5731988971210003618639433)
    ·
      refine ⟨4298991728407502713979575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5731988971210003618639433 4298991728407502713979575)
      ·
        refine ⟨6448487592611254070969363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4298991728407502713979575 6448487592611254070969363)
        ·
          refine ⟨9672731388916881106454045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6448487592611254070969363 9672731388916881106454045)
          ·
            refine ⟨3627274270843830414920267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9672731388916881106454045 3627274270843830414920267)
            ·
              refine ⟨5440911406265745622380401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3627274270843830414920267 5440911406265745622380401)
              ·
                refine ⟨4080683554699309216785301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5440911406265745622380401 4080683554699309216785301)
                ·
                  refine ⟨191282041626530119536811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4080683554699309216785301 191282041626530119536811)
                  ·
                    rfl

theorem cell22_1676342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 2, 6].length) (baseStart_1676342 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1676342 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1676342 prefixEnd_1676342 := by exact prefixLift 1676342
  have htrace : WordTrace (prefixWord ++ tailWord_1676342) baseStart_1676342 baseEnd_1676342 := by
    simpa [prefixWord, tailWord_1676342, baseEnd_1676342] using wordTrace_append hprefix tailTrace_1676342
  have hstable : (prefixWord ++ tailWord_1676342).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1676342).length < 2 ^ (prefixWord ++ tailWord_1676342).sum := by decide
  have hdescent : baseEnd_1676342 < baseStart_1676342 := by decide
  rcases family_descends (prefixWord ++ tailWord_1676342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1676368 : List Nat := [2, 1, 1, 1, 1, 3, 1, 2, 1, 9]
def baseStart_1676368 : Nat := 118140960795 + 1676368 * 2 ^ 59
def prefixEnd_1676368 : Nat := 4983230072969 + 3 ^ 40 * 1676368 * 2
def baseEnd_1676368 : Nat := 573855025210934957460353

theorem tailTrace_1676368 : CollatzResearch.WordTrace tailWord_1676368 prefixEnd_1676368 573855025210934957460353 := by
  unfold tailWord_1676368
  simp only [CollatzResearch.WordTrace]
  refine ⟨30571081995406255852966879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40761442660541674470622505 30571081995406255852966879)
  ·
    refine ⟨45856622993109383779450319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30571081995406255852966879 45856622993109383779450319)
    ·
      refine ⟨68784934489664075669175479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45856622993109383779450319 68784934489664075669175479)
      ·
        refine ⟨103177401734496113503763219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68784934489664075669175479 103177401734496113503763219)
        ·
          refine ⟨154766102601744170255644829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103177401734496113503763219 154766102601744170255644829)
          ·
            refine ⟨58037288475654063845866811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 154766102601744170255644829 58037288475654063845866811)
            ·
              refine ⟨87055932713481095768800217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58037288475654063845866811 87055932713481095768800217)
              ·
                refine ⟨65291949535110821826600163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87055932713481095768800217 65291949535110821826600163)
                ·
                  refine ⟨97937924302666232739900245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65291949535110821826600163 97937924302666232739900245)
                  ·
                    refine ⟨573855025210934957460353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 97937924302666232739900245 573855025210934957460353)
                    ·
                      rfl

theorem cell22_1676368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 1, 9].length) (baseStart_1676368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1676368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1676368 prefixEnd_1676368 := by exact prefixLift 1676368
  have htrace : WordTrace (prefixWord ++ tailWord_1676368) baseStart_1676368 baseEnd_1676368 := by
    simpa [prefixWord, tailWord_1676368, baseEnd_1676368] using wordTrace_append hprefix tailTrace_1676368
  have hstable : (prefixWord ++ tailWord_1676368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1676368).length < 2 ^ (prefixWord ++ tailWord_1676368).sum := by decide
  have hdescent : baseEnd_1676368 < baseStart_1676368 := by decide
  rcases family_descends (prefixWord ++ tailWord_1676368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1676370 : List Nat := [3, 2, 2, 1, 3, 2, 9]
def baseStart_1676370 : Nat := 118140960795 + 1676370 * 2 ^ 59
def prefixEnd_1676370 : Nat := 4983230072969 + 3 ^ 40 * 1676370 * 2
def baseEnd_1676370 : Nat := 21253915179696578478161

theorem tailTrace_1676370 : CollatzResearch.WordTrace tailWord_1676370 prefixEnd_1676370 21253915179696578478161 := by
  unfold tailWord_1676370
  simp only [CollatzResearch.WordTrace]
  refine ⟨15285559234201316511876641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40761491291203510698337709 15285559234201316511876641)
  ·
    refine ⟨11464169425650987383907481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15285559234201316511876641 11464169425650987383907481)
    ·
      refine ⟨8598127069238240537930611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11464169425650987383907481 8598127069238240537930611)
      ·
        refine ⟨12897190603857360806895917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8598127069238240537930611 12897190603857360806895917)
        ·
          refine ⟨4836446476446510302585969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12897190603857360806895917 4836446476446510302585969)
          ·
            refine ⟨3627334857334882726939477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4836446476446510302585969 3627334857334882726939477)
            ·
              refine ⟨21253915179696578478161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3627334857334882726939477 21253915179696578478161)
              ·
                rfl

theorem cell22_1676370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 9].length) (baseStart_1676370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1676370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1676370 prefixEnd_1676370 := by exact prefixLift 1676370
  have htrace : WordTrace (prefixWord ++ tailWord_1676370) baseStart_1676370 baseEnd_1676370 := by
    simpa [prefixWord, tailWord_1676370, baseEnd_1676370] using wordTrace_append hprefix tailTrace_1676370
  have hstable : (prefixWord ++ tailWord_1676370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1676370).length < 2 ^ (prefixWord ++ tailWord_1676370).sum := by decide
  have hdescent : baseEnd_1676370 < baseStart_1676370 := by decide
  rcases family_descends (prefixWord ++ tailWord_1676370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1676402 : List Nat := [3, 2, 1, 2, 2, 1, 1, 4, 3, 3]
def baseStart_1676402 : Nat := 118140960795 + 1676402 * 2 ^ 59
def prefixEnd_1676402 : Nat := 4983230072969 + 3 ^ 40 * 1676402 * 2
def baseEnd_1676402 : Nat := 573866664105770202110249

theorem tailTrace_1676402 : CollatzResearch.WordTrace tailWord_1676402 prefixEnd_1676402 573866664105770202110249 := by
  unfold tailWord_1676402
  simp only [CollatzResearch.WordTrace]
  refine ⟨15285851018172333878167865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40762269381792890341780973 15285851018172333878167865)
  ·
    refine ⟨11464388263629250408625899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15285851018172333878167865 11464388263629250408625899)
    ·
      refine ⟨17196582395443875612938849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11464388263629250408625899 17196582395443875612938849)
      ·
        refine ⟨12897436796582906709704137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17196582395443875612938849 12897436796582906709704137)
        ·
          refine ⟨9673077597437180032278103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12897436796582906709704137 9673077597437180032278103)
          ·
            refine ⟨14509616396155770048417155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9673077597437180032278103 14509616396155770048417155)
            ·
              refine ⟨21764424594233655072625733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14509616396155770048417155 21764424594233655072625733)
              ·
                refine ⟨4080829611418810326117325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21764424594233655072625733 4080829611418810326117325)
                ·
                  refine ⟨1530311104282053872293997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4080829611418810326117325 1530311104282053872293997)
                  ·
                    refine ⟨573866664105770202110249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1530311104282053872293997 573866664105770202110249)
                    ·
                      rfl

theorem cell22_1676402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 4, 3, 3].length) (baseStart_1676402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1676402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1676402 prefixEnd_1676402 := by exact prefixLift 1676402
  have htrace : WordTrace (prefixWord ++ tailWord_1676402) baseStart_1676402 baseEnd_1676402 := by
    simpa [prefixWord, tailWord_1676402, baseEnd_1676402] using wordTrace_append hprefix tailTrace_1676402
  have hstable : (prefixWord ++ tailWord_1676402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1676402).length < 2 ^ (prefixWord ++ tailWord_1676402).sum := by decide
  have hdescent : baseEnd_1676402 < baseStart_1676402 := by decide
  rcases family_descends (prefixWord ++ tailWord_1676402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1676524 : List Nat := [2, 2, 1, 1, 2, 6, 1, 1, 2, 4]
def baseStart_1676524 : Nat := 118140960795 + 1676524 * 2 ^ 59
def prefixEnd_1676524 : Nat := 4983230072969 + 3 ^ 40 * 1676524 * 2
def baseEnd_1676524 : Nat := 573908427199002550559875

theorem tailTrace_1676524 : CollatzResearch.WordTrace tailWord_1676524 prefixEnd_1676524 573908427199002550559875 := by
  unfold tailWord_1676524
  simp only [CollatzResearch.WordTrace]
  refine ⟨30573926889123675174306313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40765235852164900232408417 30573926889123675174306313)
  ·
    refine ⟨22930445166842756380729735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30573926889123675174306313 22930445166842756380729735)
    ·
      refine ⟨34395667750264134571094603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22930445166842756380729735 34395667750264134571094603)
      ·
        refine ⟨51593501625396201856641905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34395667750264134571094603 51593501625396201856641905)
        ·
          refine ⟨38695126219047151392481429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51593501625396201856641905 38695126219047151392481429)
          ·
            refine ⟨1813834041517835221522567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 38695126219047151392481429 1813834041517835221522567)
            ·
              refine ⟨2720751062276752832283851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1813834041517835221522567 2720751062276752832283851)
              ·
                refine ⟨4081126593415129248425777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2720751062276752832283851 4081126593415129248425777)
                ·
                  refine ⟨3060844945061346936319333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4081126593415129248425777 3060844945061346936319333)
                  ·
                    refine ⟨573908427199002550559875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3060844945061346936319333 573908427199002550559875)
                    ·
                      rfl

theorem cell22_1676524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 4].length) (baseStart_1676524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1676524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1676524 prefixEnd_1676524 := by exact prefixLift 1676524
  have htrace : WordTrace (prefixWord ++ tailWord_1676524) baseStart_1676524 baseEnd_1676524 := by
    simpa [prefixWord, tailWord_1676524, baseEnd_1676524] using wordTrace_append hprefix tailTrace_1676524
  have hstable : (prefixWord ++ tailWord_1676524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1676524).length < 2 ^ (prefixWord ++ tailWord_1676524).sum := by decide
  have hdescent : baseEnd_1676524 < baseStart_1676524 := by decide
  rcases family_descends (prefixWord ++ tailWord_1676524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1676535 : List Nat := [1, 1, 3, 1, 1, 1, 2, 2, 4, 6]
def baseStart_1676535 : Nat := 118140960795 + 1676535 * 2 ^ 59
def prefixEnd_1676535 : Nat := 4983230072969 + 3 ^ 40 * 1676535 * 2
def baseEnd_1676535 : Nat := 573912192723802188534841

theorem tailTrace_1676535 : CollatzResearch.WordTrace tailWord_1676535 prefixEnd_1676535 573912192723802188534841 := by
  unfold tailWord_1676535
  simp only [CollatzResearch.WordTrace]
  refine ⟨61148254981207499227263059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40765503320804999484842039 61148254981207499227263059)
  ·
    refine ⟨91722382471811248840894589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61148254981207499227263059 91722382471811248840894589)
    ·
      refine ⟨34395893426929218315335471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91722382471811248840894589 34395893426929218315335471)
      ·
        refine ⟨51593840140393827473003207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34395893426929218315335471 51593840140393827473003207)
        ·
          refine ⟨77390760210590741209504811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51593840140393827473003207 77390760210590741209504811)
          ·
            refine ⟨116086140315886111814257217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77390760210590741209504811 116086140315886111814257217)
            ·
              refine ⟨87064605236914583860692913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116086140315886111814257217 87064605236914583860692913)
              ·
                refine ⟨65298453927685937895519685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87064605236914583860692913 65298453927685937895519685)
                ·
                  refine ⟨12243460111441113355409941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65298453927685937895519685 12243460111441113355409941)
                  ·
                    refine ⟨573912192723802188534841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12243460111441113355409941 573912192723802188534841)
                    ·
                      rfl

theorem cell22_1676535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 4, 6].length) (baseStart_1676535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1676535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1676535 prefixEnd_1676535 := by exact prefixLift 1676535
  have htrace : WordTrace (prefixWord ++ tailWord_1676535) baseStart_1676535 baseEnd_1676535 := by
    simpa [prefixWord, tailWord_1676535, baseEnd_1676535] using wordTrace_append hprefix tailTrace_1676535
  have hstable : (prefixWord ++ tailWord_1676535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1676535).length < 2 ^ (prefixWord ++ tailWord_1676535).sum := by decide
  have hdescent : baseEnd_1676535 < baseStart_1676535 := by decide
  rcases family_descends (prefixWord ++ tailWord_1676535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1676537 : List Nat := [1, 2, 1, 3, 1, 1, 3, 2, 5, 3]
def baseStart_1676537 : Nat := 118140960795 + 1676537 * 2 ^ 59
def prefixEnd_1676537 : Nat := 4983230072969 + 3 ^ 40 * 1676537 * 2
def baseEnd_1676537 : Nat := 573912877364674849984835

theorem tailTrace_1676537 : CollatzResearch.WordTrace tailWord_1676537 prefixEnd_1676537 573912877364674849984835 := by
  unfold tailWord_1676537
  simp only [CollatzResearch.WordTrace]
  refine ⟨61148327927200253568835865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40765551951466835712557243 61148327927200253568835865)
  ·
    refine ⟨45861245945400190176626899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61148327927200253568835865 45861245945400190176626899)
    ·
      refine ⟨68791868918100285264940349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45861245945400190176626899 68791868918100285264940349)
      ·
        refine ⟨25796950844287606974352631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68791868918100285264940349 25796950844287606974352631)
        ·
          refine ⟨38695426266431410461528947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25796950844287606974352631 38695426266431410461528947)
          ·
            refine ⟨58043139399647115692293421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38695426266431410461528947 58043139399647115692293421)
            ·
              refine ⟨21766177274867668384610033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58043139399647115692293421 21766177274867668384610033)
              ·
                refine ⟨16324632956150751288457525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21766177274867668384610033 16324632956150751288457525)
                ·
                  refine ⟨1530434339639132933292893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16324632956150751288457525 1530434339639132933292893)
                  ·
                    refine ⟨573912877364674849984835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1530434339639132933292893 573912877364674849984835)
                    ·
                      rfl

theorem cell22_1676537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 2, 5, 3].length) (baseStart_1676537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1676537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1676537 prefixEnd_1676537 := by exact prefixLift 1676537
  have htrace : WordTrace (prefixWord ++ tailWord_1676537) baseStart_1676537 baseEnd_1676537 := by
    simpa [prefixWord, tailWord_1676537, baseEnd_1676537] using wordTrace_append hprefix tailTrace_1676537
  have hstable : (prefixWord ++ tailWord_1676537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1676537).length < 2 ^ (prefixWord ++ tailWord_1676537).sum := by decide
  have hdescent : baseEnd_1676537 < baseStart_1676537 := by decide
  rcases family_descends (prefixWord ++ tailWord_1676537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1676605 : List Nat := [1, 4, 1, 5, 2, 1, 1, 1, 3, 3]
def baseStart_1676605 : Nat := 118140960795 + 1676605 * 2 ^ 59
def prefixEnd_1676605 : Nat := 4983230072969 + 3 ^ 40 * 1676605 * 2
def baseEnd_1676605 : Nat := 573936155154345339284627

theorem tailTrace_1676605 : CollatzResearch.WordTrace tailWord_1676605 prefixEnd_1676605 573936155154345339284627 := by
  unfold tailWord_1676605
  simp only [CollatzResearch.WordTrace]
  refine ⟨61150808090953901182311269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40767205393969267454874179 61150808090953901182311269)
  ·
    refine ⟨11465776517053856471683363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61150808090953901182311269 11465776517053856471683363)
    ·
      refine ⟨17198664775580784707525045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11465776517053856471683363 17198664775580784707525045)
      ·
        refine ⟨1612374822710698566330473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17198664775580784707525045 1612374822710698566330473)
        ·
          refine ⟨1209281117033023924747855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1612374822710698566330473 1209281117033023924747855)
          ·
            refine ⟨1813921675549535887121783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1209281117033023924747855 1813921675549535887121783)
            ·
              refine ⟨2720882513324303830682675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1813921675549535887121783 2720882513324303830682675)
              ·
                refine ⟨4081323769986455746024013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2720882513324303830682675 4081323769986455746024013)
                ·
                  refine ⟨1530496413744920904759005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4081323769986455746024013 1530496413744920904759005)
                  ·
                    refine ⟨573936155154345339284627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1530496413744920904759005 573936155154345339284627)
                    ·
                      rfl

theorem cell22_1676605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 1, 1, 3, 3].length) (baseStart_1676605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1676605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1676605 prefixEnd_1676605 := by exact prefixLift 1676605
  have htrace : WordTrace (prefixWord ++ tailWord_1676605) baseStart_1676605 baseEnd_1676605 := by
    simpa [prefixWord, tailWord_1676605, baseEnd_1676605] using wordTrace_append hprefix tailTrace_1676605
  have hstable : (prefixWord ++ tailWord_1676605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1676605).length < 2 ^ (prefixWord ++ tailWord_1676605).sum := by decide
  have hdescent : baseEnd_1676605 < baseStart_1676605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1676605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1676627 : List Nat := [1, 1, 1, 2, 1, 1, 6, 3, 1, 5]
def baseStart_1676627 : Nat := 118140960795 + 1676627 * 2 ^ 59
def prefixEnd_1676627 : Nat := 4983230072969 + 3 ^ 40 * 1676627 * 2
def baseEnd_1676627 : Nat := 573943686203944615234559

theorem tailTrace_1676627 : CollatzResearch.WordTrace tailWord_1676627 prefixEnd_1676627 573943686203944615234559 := by
  unfold tailWord_1676627
  simp only [CollatzResearch.WordTrace]
  refine ⟨61151610496874198939612135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40767740331249465959741423 61151610496874198939612135)
  ·
    refine ⟨91727415745311298409418203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61151610496874198939612135 91727415745311298409418203)
    ·
      refine ⟨137591123617966947614127305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91727415745311298409418203 137591123617966947614127305)
      ·
        refine ⟨103193342713475210710595479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137591123617966947614127305 103193342713475210710595479)
        ·
          refine ⟨154790014070212816065893219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103193342713475210710595479 154790014070212816065893219)
          ·
            refine ⟨232185021105319224098839829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154790014070212816065893219 232185021105319224098839829)
            ·
              refine ⟨10883672864311838629633117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 232185021105319224098839829 10883672864311838629633117)
              ·
                refine ⟨4081377324116939486112419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10883672864311838629633117 4081377324116939486112419)
                ·
                  refine ⟨6122065986175409229168629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4081377324116939486112419 6122065986175409229168629)
                  ·
                    refine ⟨573943686203944615234559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6122065986175409229168629 573943686203944615234559)
                    ·
                      rfl

theorem cell22_1676627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 3, 1, 5].length) (baseStart_1676627 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1676627 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1676627 prefixEnd_1676627 := by exact prefixLift 1676627
  have htrace : WordTrace (prefixWord ++ tailWord_1676627) baseStart_1676627 baseEnd_1676627 := by
    simpa [prefixWord, tailWord_1676627, baseEnd_1676627] using wordTrace_append hprefix tailTrace_1676627
  have hstable : (prefixWord ++ tailWord_1676627).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1676627).length < 2 ^ (prefixWord ++ tailWord_1676627).sum := by decide
  have hdescent : baseEnd_1676627 < baseStart_1676627 := by decide
  rcases family_descends (prefixWord ++ tailWord_1676627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1676631 : List Nat := [1, 1, 3, 2, 3, 4, 1, 2, 1, 4]
def baseStart_1676631 : Nat := 118140960795 + 1676631 * 2 ^ 59
def prefixEnd_1676631 : Nat := 4983230072969 + 3 ^ 40 * 1676631 * 2
def baseEnd_1676631 : Nat := 573945055485689938134547

theorem tailTrace_1676631 : CollatzResearch.WordTrace tailWord_1676631 prefixEnd_1676631 573945055485689938134547 := by
  unfold tailWord_1676631
  simp only [CollatzResearch.WordTrace]
  refine ⟨61151756388859707622757747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40767837592573138415171831 61151756388859707622757747)
  ·
    refine ⟨91727634583289561434136621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61151756388859707622757747 91727634583289561434136621)
    ·
      refine ⟨34397862968733585537801233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91727634583289561434136621 34397862968733585537801233)
      ·
        refine ⟨25798397226550189153350925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34397862968733585537801233 25798397226550189153350925)
        ·
          refine ⟨9674398959956320932506597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25798397226550189153350925 9674398959956320932506597)
          ·
            refine ⟨1813949804991810174844987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9674398959956320932506597 1813949804991810174844987)
            ·
              refine ⟨2720924707487715262267481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1813949804991810174844987 2720924707487715262267481)
              ·
                refine ⟨2040693530615786446700611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2720924707487715262267481 2040693530615786446700611)
                ·
                  refine ⟨3061040295923679670050917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2040693530615786446700611 3061040295923679670050917)
                  ·
                    refine ⟨573945055485689938134547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3061040295923679670050917 573945055485689938134547)
                    ·
                      rfl

theorem cell22_1676631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 1, 2, 1, 4].length) (baseStart_1676631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1676631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1676631 prefixEnd_1676631 := by exact prefixLift 1676631
  have htrace : WordTrace (prefixWord ++ tailWord_1676631) baseStart_1676631 baseEnd_1676631 := by
    simpa [prefixWord, tailWord_1676631, baseEnd_1676631] using wordTrace_append hprefix tailTrace_1676631
  have hstable : (prefixWord ++ tailWord_1676631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1676631).length < 2 ^ (prefixWord ++ tailWord_1676631).sum := by decide
  have hdescent : baseEnd_1676631 < baseStart_1676631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1676631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1676644 : List Nat := [2, 3, 1, 1, 3, 3, 1, 2, 1, 5]
def baseStart_1676644 : Nat := 118140960795 + 1676644 * 2 ^ 59
def prefixEnd_1676644 : Nat := 4983230072969 + 3 ^ 40 * 1676644 * 2
def baseEnd_1676644 : Nat := 573949505651362237559507

theorem tailTrace_1676644 : CollatzResearch.WordTrace tailWord_1676644 prefixEnd_1676644 573949505651362237559507 := by
  unfold tailWord_1676644
  simp only [CollatzResearch.WordTrace]
  refine ⟨30576115268906305421490493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40768153691875073895320657 30576115268906305421490493)
  ·
    refine ⟨11466043225839864533058935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30576115268906305421490493 11466043225839864533058935)
    ·
      refine ⟨17199064838759796799588403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11466043225839864533058935 17199064838759796799588403)
      ·
        refine ⟨25798597258139695199382605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17199064838759796799588403 25798597258139695199382605)
        ·
          refine ⟨9674473971802385699768477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25798597258139695199382605 9674473971802385699768477)
          ·
            refine ⟨3627927739425894637413179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9674473971802385699768477 3627927739425894637413179)
            ·
              refine ⟨5441891609138841956119769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3627927739425894637413179 5441891609138841956119769)
              ·
                refine ⟨4081418706854131467089827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5441891609138841956119769 4081418706854131467089827)
                ·
                  refine ⟨6122128060281197200634741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4081418706854131467089827 6122128060281197200634741)
                  ·
                    refine ⟨573949505651362237559507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6122128060281197200634741 573949505651362237559507)
                    ·
                      rfl

theorem cell22_1676644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 2, 1, 5].length) (baseStart_1676644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1676644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1676644 prefixEnd_1676644 := by exact prefixLift 1676644
  have htrace : WordTrace (prefixWord ++ tailWord_1676644) baseStart_1676644 baseEnd_1676644 := by
    simpa [prefixWord, tailWord_1676644, baseEnd_1676644] using wordTrace_append hprefix tailTrace_1676644
  have hstable : (prefixWord ++ tailWord_1676644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1676644).length < 2 ^ (prefixWord ++ tailWord_1676644).sum := by decide
  have hdescent : baseEnd_1676644 < baseStart_1676644 := by decide
  rcases family_descends (prefixWord ++ tailWord_1676644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1676648 : List Nat := [2, 1, 4, 2, 3, 1, 3, 1, 1, 4]
def baseStart_1676648 : Nat := 118140960795 + 1676648 * 2 ^ 59
def prefixEnd_1676648 : Nat := 4983230072969 + 3 ^ 40 * 1676648 * 2
def baseEnd_1676648 : Nat := 573950874933107560459495

theorem tailTrace_1676648 : CollatzResearch.WordTrace tailWord_1676648 prefixEnd_1676648 573950874933107560459495 := by
  unfold tailWord_1676648
  simp only [CollatzResearch.WordTrace]
  refine ⟨30576188214899059763063299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40768250953198746350751065 30576188214899059763063299)
  ·
    refine ⟨45864282322348589644594949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30576188214899059763063299 45864282322348589644594949)
    ·
      refine ⟨8599552935440360558361553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45864282322348589644594949 8599552935440360558361553)
      ·
        refine ⟨6449664701580270418771165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8599552935440360558361553 6449664701580270418771165)
        ·
          refine ⟨2418624263092601407039187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6449664701580270418771165 2418624263092601407039187)
          ·
            refine ⟨3627936394638902110558781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2418624263092601407039187 3627936394638902110558781)
            ·
              refine ⟨1360476147989588291459543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3627936394638902110558781 1360476147989588291459543)
              ·
                refine ⟨2040714221984382437189315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1360476147989588291459543 2040714221984382437189315)
                ·
                  refine ⟨3061071332976573655783973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2040714221984382437189315 3061071332976573655783973)
                  ·
                    refine ⟨573950874933107560459495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3061071332976573655783973 573950874933107560459495)
                    ·
                      rfl

theorem cell22_1676648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 3, 1, 1, 4].length) (baseStart_1676648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1676648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1676648 prefixEnd_1676648 := by exact prefixLift 1676648
  have htrace : WordTrace (prefixWord ++ tailWord_1676648) baseStart_1676648 baseEnd_1676648 := by
    simpa [prefixWord, tailWord_1676648, baseEnd_1676648] using wordTrace_append hprefix tailTrace_1676648
  have hstable : (prefixWord ++ tailWord_1676648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1676648).length < 2 ^ (prefixWord ++ tailWord_1676648).sum := by decide
  have hdescent : baseEnd_1676648 < baseStart_1676648 := by decide
  rcases family_descends (prefixWord ++ tailWord_1676648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1676689 : List Nat := [1, 2, 2, 1, 1, 1, 2, 6, 3, 3]
def baseStart_1676689 : Nat := 118140960795 + 1676689 * 2 ^ 59
def prefixEnd_1676689 : Nat := 4983230072969 + 3 ^ 40 * 1676689 * 2
def baseEnd_1676689 : Nat := 573964910070997120184369

theorem tailTrace_1676689 : CollatzResearch.WordTrace tailWord_1676689 prefixEnd_1676689 573964910070997120184369 := by
  unfold tailWord_1676689
  simp only [CollatzResearch.WordTrace]
  refine ⟨61153871822649583528369121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40769247881766389018912747 61153871822649583528369121)
  ·
    refine ⟨45865403866987187646276841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61153871822649583528369121 45865403866987187646276841)
    ·
      refine ⟨34399052900240390734707631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45865403866987187646276841 34399052900240390734707631)
      ·
        refine ⟨51598579350360586102061447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34399052900240390734707631 51598579350360586102061447)
        ·
          refine ⟨77397869025540879153092171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51598579350360586102061447 77397869025540879153092171)
          ·
            refine ⟨116096803538311318729638257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77397869025540879153092171 116096803538311318729638257)
            ·
              refine ⟨87072602653733489047228693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116096803538311318729638257 87072602653733489047228693)
              ·
                refine ⟨4081528249393757299088845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 87072602653733489047228693 4081528249393757299088845)
                ·
                  refine ⟨1530573093522658987158317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4081528249393757299088845 1530573093522658987158317)
                  ·
                    refine ⟨573964910070997120184369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1530573093522658987158317 573964910070997120184369)
                    ·
                      rfl

theorem cell22_1676689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 6, 3, 3].length) (baseStart_1676689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1676689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1676689 prefixEnd_1676689 := by exact prefixLift 1676689
  have htrace : WordTrace (prefixWord ++ tailWord_1676689) baseStart_1676689 baseEnd_1676689 := by
    simpa [prefixWord, tailWord_1676689, baseEnd_1676689] using wordTrace_append hprefix tailTrace_1676689
  have hstable : (prefixWord ++ tailWord_1676689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1676689).length < 2 ^ (prefixWord ++ tailWord_1676689).sum := by decide
  have hdescent : baseEnd_1676689 < baseStart_1676689 := by decide
  rcases family_descends (prefixWord ++ tailWord_1676689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1676712 : List Nat := [2, 1, 6, 1, 3, 1, 1, 2, 2, 3]
def baseStart_1676712 : Nat := 118140960795 + 1676712 * 2 ^ 59
def prefixEnd_1676712 : Nat := 4983230072969 + 3 ^ 40 * 1676712 * 2
def baseEnd_1676712 : Nat := 573972783441032726859299

theorem tailTrace_1676712 : CollatzResearch.WordTrace tailWord_1676712 prefixEnd_1676712 573972783441032726859299 := by
  unfold tailWord_1676712
  simp only [CollatzResearch.WordTrace]
  refine ⟨30577355350783129228228195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40769807134377505637637593 30577355350783129228228195)
  ·
    refine ⟨45866033026174693842342293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30577355350783129228228195 45866033026174693842342293)
    ·
      refine ⟨2149970298101938773859795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 45866033026174693842342293 2149970298101938773859795)
      ·
        refine ⟨3224955447152908160789693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2149970298101938773859795 3224955447152908160789693)
        ·
          refine ⟨1209358292682340560296135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3224955447152908160789693 1209358292682340560296135)
          ·
            refine ⟨1814037439023510840444203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1209358292682340560296135 1814037439023510840444203)
            ·
              refine ⟨2721056158535266260666305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1814037439023510840444203 2721056158535266260666305)
              ·
                refine ⟨2040792118901449695499729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2721056158535266260666305 2040792118901449695499729)
                ·
                  refine ⟨1530594089176087271624797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2040792118901449695499729 1530594089176087271624797)
                  ·
                    refine ⟨573972783441032726859299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1530594089176087271624797 573972783441032726859299)
                    ·
                      rfl

theorem cell22_1676712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_1676712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1676712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1676712 prefixEnd_1676712 := by exact prefixLift 1676712
  have htrace : WordTrace (prefixWord ++ tailWord_1676712) baseStart_1676712 baseEnd_1676712 := by
    simpa [prefixWord, tailWord_1676712, baseEnd_1676712] using wordTrace_append hprefix tailTrace_1676712
  have hstable : (prefixWord ++ tailWord_1676712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1676712).length < 2 ^ (prefixWord ++ tailWord_1676712).sum := by decide
  have hdescent : baseEnd_1676712 < baseStart_1676712 := by decide
  rcases family_descends (prefixWord ++ tailWord_1676712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1676794 : List Nat := [3, 1, 1, 1, 1, 2, 3, 2, 4, 4]
def baseStart_1676794 : Nat := 118140960795 + 1676794 * 2 ^ 59
def prefixEnd_1676794 : Nat := 4983230072969 + 3 ^ 40 * 1676794 * 2
def baseEnd_1676794 : Nat := 574000853716811846309047

theorem tailTrace_1676794 : CollatzResearch.WordTrace tailWord_1676794 prefixEnd_1676794 574000853716811846309047 := by
  unfold tailWord_1676794
  simp only [CollatzResearch.WordTrace]
  refine ⟨15289425371817296615235359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40771800991512790973960957 15289425371817296615235359)
  ·
    refine ⟨22934138057725944922853039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15289425371817296615235359 22934138057725944922853039)
    ·
      refine ⟨34401207086588917384279559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22934138057725944922853039 34401207086588917384279559)
      ·
        refine ⟨51601810629883376076419339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34401207086588917384279559 51601810629883376076419339)
        ·
          refine ⟨77402715944825064114629009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51601810629883376076419339 77402715944825064114629009)
          ·
            refine ⟨58052036958618798085971757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77402715944825064114629009 58052036958618798085971757)
            ·
              refine ⟨21769513859482049282239409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58052036958618798085971757 21769513859482049282239409)
              ·
                refine ⟨16327135394611536961679557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21769513859482049282239409 16327135394611536961679557)
                ·
                  refine ⟨3061337886489663180314917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16327135394611536961679557 3061337886489663180314917)
                  ·
                    refine ⟨574000853716811846309047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3061337886489663180314917 574000853716811846309047)
                    ·
                      rfl

theorem cell22_1676794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 2, 4, 4].length) (baseStart_1676794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1676794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1676794 prefixEnd_1676794 := by exact prefixLift 1676794
  have htrace : WordTrace (prefixWord ++ tailWord_1676794) baseStart_1676794 baseEnd_1676794 := by
    simpa [prefixWord, tailWord_1676794, baseEnd_1676794] using wordTrace_append hprefix tailTrace_1676794
  have hstable : (prefixWord ++ tailWord_1676794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1676794).length < 2 ^ (prefixWord ++ tailWord_1676794).sum := by decide
  have hdescent : baseEnd_1676794 < baseStart_1676794 := by decide
  rcases family_descends (prefixWord ++ tailWord_1676794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1676869 : List Nat := [1, 3, 1, 1, 1, 4, 1, 2, 1, 7]
def baseStart_1676869 : Nat := 118140960795 + 1676869 * 2 ^ 59
def prefixEnd_1676869 : Nat := 4983230072969 + 3 ^ 40 * 1676869 * 2
def baseEnd_1676869 : Nat := 574026527749536650683817

theorem tailTrace_1676869 : CollatzResearch.WordTrace tailWord_1676869 prefixEnd_1676869 574026527749536650683817 := by
  unfold tailWord_1676869
  simp only [CollatzResearch.WordTrace]
  refine ⟨61160436961997474269921661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40773624641331649513281107 61160436961997474269921661)
  ·
    refine ⟨22935163860749052851220623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61160436961997474269921661 22935163860749052851220623)
    ·
      refine ⟨34402745791123579276830935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22935163860749052851220623 34402745791123579276830935)
      ·
        refine ⟨51604118686685368915246403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34402745791123579276830935 51604118686685368915246403)
        ·
          refine ⟨77406178030028053372869605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51604118686685368915246403 77406178030028053372869605)
          ·
            refine ⟨14513658380630260007413051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77406178030028053372869605 14513658380630260007413051)
            ·
              refine ⟨21770487570945390011119577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14513658380630260007413051 21770487570945390011119577)
              ·
                refine ⟨16327865678209042508339683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21770487570945390011119577 16327865678209042508339683)
                ·
                  refine ⟨24491798517313563762509525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16327865678209042508339683 24491798517313563762509525)
                  ·
                    refine ⟨574026527749536650683817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24491798517313563762509525 574026527749536650683817)
                    ·
                      rfl

theorem cell22_1676869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 2, 1, 7].length) (baseStart_1676869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1676869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1676869 prefixEnd_1676869 := by exact prefixLift 1676869
  have htrace : WordTrace (prefixWord ++ tailWord_1676869) baseStart_1676869 baseEnd_1676869 := by
    simpa [prefixWord, tailWord_1676869, baseEnd_1676869] using wordTrace_append hprefix tailTrace_1676869
  have hstable : (prefixWord ++ tailWord_1676869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1676869).length < 2 ^ (prefixWord ++ tailWord_1676869).sum := by decide
  have hdescent : baseEnd_1676869 < baseStart_1676869 := by decide
  rcases family_descends (prefixWord ++ tailWord_1676869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1676961 : List Nat := [1, 2, 3, 3, 2, 1, 1, 9]
def baseStart_1676961 : Nat := 118140960795 + 1676961 * 2 ^ 59
def prefixEnd_1676961 : Nat := 4983230072969 + 3 ^ 40 * 1676961 * 2
def baseEnd_1676961 : Nat := 63784224581075453042615

theorem tailTrace_1676961 : CollatzResearch.WordTrace tailWord_1676961 prefixEnd_1676961 63784224581075453042615 := by
  unfold tailWord_1676961
  simp only [CollatzResearch.WordTrace]
  refine ⟨61163792477664173982270737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40775861651776115988180491 61163792477664173982270737)
  ·
    refine ⟨45872844358248130486703053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61163792477664173982270737 45872844358248130486703053)
    ·
      refine ⟨17202316634343048932513645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45872844358248130486703053 17202316634343048932513645)
      ·
        refine ⟨6450868737878643349692617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17202316634343048932513645 6450868737878643349692617)
        ·
          refine ⟨4838151553408982512269463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6450868737878643349692617 4838151553408982512269463)
          ·
            refine ⟨7257227330113473768404195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4838151553408982512269463 7257227330113473768404195)
            ·
              refine ⟨10885840995170210652606293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7257227330113473768404195 10885840995170210652606293)
              ·
                refine ⟨63784224581075453042615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10885840995170210652606293 63784224581075453042615)
                ·
                  rfl

theorem cell22_1676961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 9].length) (baseStart_1676961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1676961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1676961 prefixEnd_1676961 := by exact prefixLift 1676961
  have htrace : WordTrace (prefixWord ++ tailWord_1676961) baseStart_1676961 baseEnd_1676961 := by
    simpa [prefixWord, tailWord_1676961, baseEnd_1676961] using wordTrace_append hprefix tailTrace_1676961
  have hstable : (prefixWord ++ tailWord_1676961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1676961).length < 2 ^ (prefixWord ++ tailWord_1676961).sum := by decide
  have hdescent : baseEnd_1676961 < baseStart_1676961 := by decide
  rcases family_descends (prefixWord ++ tailWord_1676961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1676965 : List Nat := [1, 3, 1, 2, 1, 2, 6, 1, 2, 3]
def baseStart_1676965 : Nat := 118140960795 + 1676965 * 2 ^ 59
def prefixEnd_1676965 : Nat := 4983230072969 + 3 ^ 40 * 1676965 * 2
def baseEnd_1676965 : Nat := 574059390511424400283523

theorem tailTrace_1676965 : CollatzResearch.WordTrace tailWord_1676965 prefixEnd_1676965 574059390511424400283523 := by
  unfold tailWord_1676965
  simp only [CollatzResearch.WordTrace]
  refine ⟨61163938369649682665416349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40775958913099788443610899 61163938369649682665416349)
  ·
    refine ⟨22936476888618630999531131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61163938369649682665416349 22936476888618630999531131)
    ·
      refine ⟨34404715332927946499296697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22936476888618630999531131 34404715332927946499296697)
      ·
        refine ⟨25803536499695959874472523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34404715332927946499296697 25803536499695959874472523)
        ·
          refine ⟨38705304749543939811708785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25803536499695959874472523 38705304749543939811708785)
          ·
            refine ⟨29028978562157954858781589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38705304749543939811708785 29028978562157954858781589)
            ·
              refine ⟨1360733370101154134005387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 29028978562157954858781589 1360733370101154134005387)
              ·
                refine ⟨2041100055151731201008081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1360733370101154134005387 2041100055151731201008081)
                ·
                  refine ⟨1530825041363798400756061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2041100055151731201008081 1530825041363798400756061)
                  ·
                    refine ⟨574059390511424400283523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1530825041363798400756061 574059390511424400283523)
                    ·
                      rfl

theorem cell22_1676965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 6, 1, 2, 3].length) (baseStart_1676965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1676965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1676965 prefixEnd_1676965 := by exact prefixLift 1676965
  have htrace : WordTrace (prefixWord ++ tailWord_1676965) baseStart_1676965 baseEnd_1676965 := by
    simpa [prefixWord, tailWord_1676965, baseEnd_1676965] using wordTrace_append hprefix tailTrace_1676965
  have hstable : (prefixWord ++ tailWord_1676965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1676965).length < 2 ^ (prefixWord ++ tailWord_1676965).sum := by decide
  have hdescent : baseEnd_1676965 < baseStart_1676965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1676965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1677205 : List Nat := [1, 3, 2, 1, 1, 3, 2, 4, 1, 4]
def baseStart_1677205 : Nat := 118140960795 + 1677205 * 2 ^ 59
def prefixEnd_1677205 : Nat := 4983230072969 + 3 ^ 40 * 1677205 * 2
def baseEnd_1677205 : Nat := 574141547416143774282787

theorem tailTrace_1677205 : CollatzResearch.WordTrace tailWord_1677205 prefixEnd_1677205 574141547416143774282787 := by
  unfold tailWord_1677205
  simp only [CollatzResearch.WordTrace]
  refine ⟨61172691888780203654153069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40781794592520135769435379 61172691888780203654153069)
  ·
    refine ⟨22939759458292576370307401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61172691888780203654153069 22939759458292576370307401)
    ·
      refine ⟨17204819593719432277730551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22939759458292576370307401 17204819593719432277730551)
      ·
        refine ⟨25807229390579148416595827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17204819593719432277730551 25807229390579148416595827)
        ·
          refine ⟨38710844085868722624893741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25807229390579148416595827 38710844085868722624893741)
          ·
            refine ⟨14516566532200770984335153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38710844085868722624893741 14516566532200770984335153)
            ·
              refine ⟨10887424899150578238251365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14516566532200770984335153 10887424899150578238251365)
              ·
                refine ⟨2041392168590733419672131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10887424899150578238251365 2041392168590733419672131)
                ·
                  refine ⟨3062088252886100129508197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2041392168590733419672131 3062088252886100129508197)
                  ·
                    refine ⟨574141547416143774282787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3062088252886100129508197 574141547416143774282787)
                    ·
                      rfl

theorem cell22_1677205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 4, 1, 4].length) (baseStart_1677205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1677205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1677205 prefixEnd_1677205 := by exact prefixLift 1677205
  have htrace : WordTrace (prefixWord ++ tailWord_1677205) baseStart_1677205 baseEnd_1677205 := by
    simpa [prefixWord, tailWord_1677205, baseEnd_1677205] using wordTrace_append hprefix tailTrace_1677205
  have hstable : (prefixWord ++ tailWord_1677205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1677205).length < 2 ^ (prefixWord ++ tailWord_1677205).sum := by decide
  have hdescent : baseEnd_1677205 < baseStart_1677205 := by decide
  rcases family_descends (prefixWord ++ tailWord_1677205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1677235 : List Nat := [1, 1, 1, 2, 3, 1, 5, 1, 4, 3]
def baseStart_1677235 : Nat := 118140960795 + 1677235 * 2 ^ 59
def prefixEnd_1677235 : Nat := 4983230072969 + 3 ^ 40 * 1677235 * 2
def baseEnd_1677235 : Nat := 574151817029233696032695

theorem tailTrace_1677235 : CollatzResearch.WordTrace tailWord_1677235 prefixEnd_1677235 574151817029233696032695 := by
  unfold tailWord_1677235
  simp only [CollatzResearch.WordTrace]
  refine ⟨61173786078671518777745159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40782524052447679185163439 61173786078671518777745159)
  ·
    refine ⟨91760679118007278166617739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61173786078671518777745159 91760679118007278166617739)
    ·
      refine ⟨137641018677010917249926609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91760679118007278166617739 137641018677010917249926609)
      ·
        refine ⟨103230764007758187937444957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137641018677010917249926609 103230764007758187937444957)
        ·
          refine ⟨38711536502909320476541859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103230764007758187937444957 38711536502909320476541859)
          ·
            refine ⟨58067304754363980714812789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38711536502909320476541859 58067304754363980714812789)
            ·
              refine ⟨5443809820721623192013699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 58067304754363980714812789 5443809820721623192013699)
              ·
                refine ⟨8165714731082434788020549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5443809820721623192013699 8165714731082434788020549)
                ·
                  refine ⟨1531071512077956522753853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8165714731082434788020549 1531071512077956522753853)
                  ·
                    refine ⟨574151817029233696032695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1531071512077956522753853 574151817029233696032695)
                    ·
                      rfl

theorem cell22_1677235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 1, 4, 3].length) (baseStart_1677235 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1677235 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1677235 prefixEnd_1677235 := by exact prefixLift 1677235
  have htrace : WordTrace (prefixWord ++ tailWord_1677235) baseStart_1677235 baseEnd_1677235 := by
    simpa [prefixWord, tailWord_1677235, baseEnd_1677235] using wordTrace_append hprefix tailTrace_1677235
  have hstable : (prefixWord ++ tailWord_1677235).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1677235).length < 2 ^ (prefixWord ++ tailWord_1677235).sum := by decide
  have hdescent : baseEnd_1677235 < baseStart_1677235 := by decide
  rcases family_descends (prefixWord ++ tailWord_1677235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1677237 : List Nat := [1, 3, 3, 2, 1, 2, 2, 4, 4]
def baseStart_1677237 : Nat := 118140960795 + 1677237 * 2 ^ 59
def prefixEnd_1677237 : Nat := 4983230072969 + 3 ^ 40 * 1677237 * 2
def baseEnd_1677237 : Nat := 191384167223368785827563

theorem tailTrace_1677237 : CollatzResearch.WordTrace tailWord_1677237 prefixEnd_1677237 191384167223368785827563 := by
  unfold tailWord_1677237
  simp only [CollatzResearch.WordTrace]
  refine ⟨61173859024664273119317965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40782572683109515412878643 61173859024664273119317965)
  ·
    refine ⟨22940197134249102419744237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61173859024664273119317965 22940197134249102419744237)
    ·
      refine ⟨8602573925343413407404089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22940197134249102419744237 8602573925343413407404089)
      ·
        refine ⟨6451930444007560055553067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8602573925343413407404089 6451930444007560055553067)
        ·
          refine ⟨9677895666011340083329601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6451930444007560055553067 9677895666011340083329601)
          ·
            refine ⟨7258421749508505062497201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9677895666011340083329601 7258421749508505062497201)
            ·
              refine ⟨5443816312131378796872901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7258421749508505062497201 5443816312131378796872901)
              ·
                refine ⟨1020715558524633524413669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5443816312131378796872901 1020715558524633524413669)
                ·
                  refine ⟨191384167223368785827563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1020715558524633524413669 191384167223368785827563)
                  ·
                    rfl

theorem cell22_1677237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 4, 4].length) (baseStart_1677237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1677237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1677237 prefixEnd_1677237 := by exact prefixLift 1677237
  have htrace : WordTrace (prefixWord ++ tailWord_1677237) baseStart_1677237 baseEnd_1677237 := by
    simpa [prefixWord, tailWord_1677237, baseEnd_1677237] using wordTrace_append hprefix tailTrace_1677237
  have hstable : (prefixWord ++ tailWord_1677237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1677237).length < 2 ^ (prefixWord ++ tailWord_1677237).sum := by decide
  have hdescent : baseEnd_1677237 < baseStart_1677237 := by decide
  rcases family_descends (prefixWord ++ tailWord_1677237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1677248 : List Nat := [2, 1, 1, 2, 3, 2, 2, 9]
def baseStart_1677248 : Nat := 118140960795 + 1677248 * 2 ^ 59
def prefixEnd_1677248 : Nat := 4983230072969 + 3 ^ 40 * 1677248 * 2
def baseEnd_1677248 : Nat := 63795140799433999495295

theorem tailTrace_1677248 : CollatzResearch.WordTrace tailWord_1677248 prefixEnd_1677248 63795140799433999495295 := by
  unfold tailWord_1677248
  simp only [CollatzResearch.WordTrace]
  refine ⟨30587130113812210998984199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40782840151749614665312265 30587130113812210998984199)
  ·
    refine ⟨45880695170718316498476299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30587130113812210998984199 45880695170718316498476299)
    ·
      refine ⟨68821042756077474747714449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45880695170718316498476299 68821042756077474747714449)
      ·
        refine ⟨51615782067058106060785837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68821042756077474747714449 51615782067058106060785837)
        ·
          refine ⟨19355918275146789772794689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51615782067058106060785837 19355918275146789772794689)
          ·
            refine ⟨14516938706360092329596017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19355918275146789772794689 14516938706360092329596017)
            ·
              refine ⟨10887704029770069247197013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14516938706360092329596017 10887704029770069247197013)
              ·
                refine ⟨63795140799433999495295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10887704029770069247197013 63795140799433999495295)
                ·
                  rfl

theorem cell22_1677248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 9].length) (baseStart_1677248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1677248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1677248 prefixEnd_1677248 := by exact prefixLift 1677248
  have htrace : WordTrace (prefixWord ++ tailWord_1677248) baseStart_1677248 baseEnd_1677248 := by
    simpa [prefixWord, tailWord_1677248, baseEnd_1677248] using wordTrace_append hprefix tailTrace_1677248
  have hstable : (prefixWord ++ tailWord_1677248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1677248).length < 2 ^ (prefixWord ++ tailWord_1677248).sum := by decide
  have hdescent : baseEnd_1677248 < baseStart_1677248 := by decide
  rcases family_descends (prefixWord ++ tailWord_1677248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1677263 : List Nat := [1, 1, 2, 1, 1, 5, 1, 1, 2, 7]
def baseStart_1677263 : Nat := 118140960795 + 1677263 * 2 ^ 59
def prefixEnd_1677263 : Nat := 4983230072969 + 3 ^ 40 * 1677263 * 2
def baseEnd_1677263 : Nat := 574161402001450956332609

theorem tailTrace_1677263 : CollatzResearch.WordTrace tailWord_1677263 prefixEnd_1677263 574161402001450956332609 := by
  unfold tailWord_1677263
  simp only [CollatzResearch.WordTrace]
  refine ⟨61174807322570079559764443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40783204881713386373176295 61174807322570079559764443)
  ·
    refine ⟨91762210983855119339646665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61174807322570079559764443 91762210983855119339646665)
    ·
      refine ⟨68821658237891339504734999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91762210983855119339646665 68821658237891339504734999)
      ·
        refine ⟨103232487356837009257102499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68821658237891339504734999 103232487356837009257102499)
        ·
          refine ⟨154848731035255513885653749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103232487356837009257102499 154848731035255513885653749)
          ·
            refine ⟨14517068534555204426780039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 154848731035255513885653749 14517068534555204426780039)
            ·
              refine ⟨21775602801832806640170059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14517068534555204426780039 21775602801832806640170059)
              ·
                refine ⟨32663404202749209960255089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21775602801832806640170059 32663404202749209960255089)
                ·
                  refine ⟨24497553152061907470191317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32663404202749209960255089 24497553152061907470191317)
                  ·
                    refine ⟨574161402001450956332609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24497553152061907470191317 574161402001450956332609)
                    ·
                      rfl

theorem cell22_1677263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 1, 2, 7].length) (baseStart_1677263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1677263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1677263 prefixEnd_1677263 := by exact prefixLift 1677263
  have htrace : WordTrace (prefixWord ++ tailWord_1677263) baseStart_1677263 baseEnd_1677263 := by
    simpa [prefixWord, tailWord_1677263, baseEnd_1677263] using wordTrace_append hprefix tailTrace_1677263
  have hstable : (prefixWord ++ tailWord_1677263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1677263).length < 2 ^ (prefixWord ++ tailWord_1677263).sum := by decide
  have hdescent : baseEnd_1677263 < baseStart_1677263 := by decide
  rcases family_descends (prefixWord ++ tailWord_1677263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1677280 : List Nat := [2, 1, 1, 3, 1, 1, 1, 4, 5, 3]
def baseStart_1677280 : Nat := 118140960795 + 1677280 * 2 ^ 59
def prefixEnd_1677280 : Nat := 4983230072969 + 3 ^ 40 * 1677280 * 2
def baseEnd_1677280 : Nat := 574167221448868578657557

theorem tailTrace_1677280 : CollatzResearch.WordTrace tailWord_1677280 prefixEnd_1677280 574167221448868578657557 := by
  unfold tailWord_1677280
  simp only [CollatzResearch.WordTrace]
  refine ⟨30587713681754245731566647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40783618242338994308755529 30587713681754245731566647)
  ·
    refine ⟨45881570522631368597349971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30587713681754245731566647 45881570522631368597349971)
    ·
      refine ⟨68822355783947052896024957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45881570522631368597349971 68822355783947052896024957)
      ·
        refine ⟨25808383418980144836009359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68822355783947052896024957 25808383418980144836009359)
        ·
          refine ⟨38712575128470217254014039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25808383418980144836009359 38712575128470217254014039)
          ·
            refine ⟨58068862692705325881021059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38712575128470217254014039 58068862692705325881021059)
            ·
              refine ⟨87103294039057988821531589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58068862692705325881021059 87103294039057988821531589)
              ·
                refine ⟨16331867632323372904037173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87103294039057988821531589 16331867632323372904037173)
                ·
                  refine ⟨1531112590530316209753485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16331867632323372904037173 1531112590530316209753485)
                  ·
                    refine ⟨574167221448868578657557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1531112590530316209753485 574167221448868578657557)
                    ·
                      rfl

theorem cell22_1677280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 4, 5, 3].length) (baseStart_1677280 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1677280 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1677280 prefixEnd_1677280 := by exact prefixLift 1677280
  have htrace : WordTrace (prefixWord ++ tailWord_1677280) baseStart_1677280 baseEnd_1677280 := by
    simpa [prefixWord, tailWord_1677280, baseEnd_1677280] using wordTrace_append hprefix tailTrace_1677280
  have hstable : (prefixWord ++ tailWord_1677280).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1677280).length < 2 ^ (prefixWord ++ tailWord_1677280).sum := by decide
  have hdescent : baseEnd_1677280 < baseStart_1677280 := by decide
  rcases family_descends (prefixWord ++ tailWord_1677280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
