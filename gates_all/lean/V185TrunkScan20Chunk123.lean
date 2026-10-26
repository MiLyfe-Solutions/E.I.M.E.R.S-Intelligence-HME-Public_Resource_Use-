import V185TrunkScan20Chunk122

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_747027 : List Nat := [1, 1, 1, 2, 1, 7, 2, 5]
def baseStart_747027 : Nat := 118140960795 + 747027 * 2 ^ 59
def prefixEnd_747027 : Nat := 4983230072969 + 3 ^ 40 * 747027 * 2
def baseEnd_747027 : Nat := 113654492707067848037627

theorem tailTrace_747027 : CollatzResearch.WordTrace tailWord_747027 prefixEnd_747027 113654492707067848037627 := by
  unfold tailWord_747027
  simp only [CollatzResearch.WordTrace]
  refine ⟨27246313064656235899383335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18164208709770823932922223 27246313064656235899383335)
  ·
    refine ⟨40869469596984353849075003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27246313064656235899383335 40869469596984353849075003)
    ·
      refine ⟨61304204395476530773612505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40869469596984353849075003 61304204395476530773612505)
      ·
        refine ⟨45978153296607398080209379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61304204395476530773612505 45978153296607398080209379)
        ·
          refine ⟨68967229944911097120314069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45978153296607398080209379 68967229944911097120314069)
          ·
            refine ⟨1616419451833853838757361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 68967229944911097120314069 1616419451833853838757361)
            ·
              refine ⟨1212314588875390379068021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1616419451833853838757361 1212314588875390379068021)
              ·
                refine ⟨113654492707067848037627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1212314588875390379068021 113654492707067848037627)
                ·
                  rfl

theorem cell20_747027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 2, 5].length) (baseStart_747027 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_747027 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_747027 prefixEnd_747027 := by exact prefixLift 747027
  have htrace : WordTrace (prefixWord ++ tailWord_747027) baseStart_747027 baseEnd_747027 := by
    simpa [prefixWord, tailWord_747027, baseEnd_747027] using wordTrace_append hprefix tailTrace_747027
  have hstable : (prefixWord ++ tailWord_747027).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747027).length < 2 ^ (prefixWord ++ tailWord_747027).sum := by decide
  have hdescent : baseEnd_747027 < baseStart_747027 := by decide
  rcases family_descends (prefixWord ++ tailWord_747027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747068 : List Nat := [2, 2, 2, 2, 4, 1, 2, 2, 3]
def baseStart_747068 : Nat := 118140960795 + 747068 * 2 ^ 59
def prefixEnd_747068 : Nat := 4983230072969 + 3 ^ 40 * 747068 * 2
def baseEnd_747068 : Nat := 340982191638389623746047

theorem tailTrace_747068 : CollatzResearch.WordTrace tailWord_747068 prefixEnd_747068 340982191638389623746047 := by
  unfold tailWord_747068
  simp only [CollatzResearch.WordTrace]
  refine ⟨13623904228753849950812929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18165205638338466601083905 13623904228753849950812929)
  ·
    refine ⟨10217928171565387463109697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13623904228753849950812929 10217928171565387463109697)
    ·
      refine ⟨7663446128674040597332273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10217928171565387463109697 7663446128674040597332273)
      ·
        refine ⟨5747584596505530447999205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7663446128674040597332273 5747584596505530447999205)
        ·
          refine ⟨1077672111844786958999851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5747584596505530447999205 1077672111844786958999851)
          ·
            refine ⟨1616508167767180438499777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1077672111844786958999851 1616508167767180438499777)
            ·
              refine ⟨1212381125825385328874833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1616508167767180438499777 1212381125825385328874833)
              ·
                refine ⟨909285844369038996656125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1212381125825385328874833 909285844369038996656125)
                ·
                  refine ⟨340982191638389623746047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 909285844369038996656125 340982191638389623746047)
                  ·
                    rfl

theorem cell20_747068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 2, 2, 3].length) (baseStart_747068 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_747068 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_747068 prefixEnd_747068 := by exact prefixLift 747068
  have htrace : WordTrace (prefixWord ++ tailWord_747068) baseStart_747068 baseEnd_747068 := by
    simpa [prefixWord, tailWord_747068, baseEnd_747068] using wordTrace_append hprefix tailTrace_747068
  have hstable : (prefixWord ++ tailWord_747068).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747068).length < 2 ^ (prefixWord ++ tailWord_747068).sum := by decide
  have hdescent : baseEnd_747068 < baseStart_747068 := by decide
  rcases family_descends (prefixWord ++ tailWord_747068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747078 : List Nat := [6, 1, 1, 1, 3, 2, 1, 5]
def baseStart_747078 : Nat := 118140960795 + 747078 * 2 ^ 59
def prefixEnd_747078 : Nat := 4983230072969 + 3 ^ 40 * 747078 * 2
def baseEnd_747078 : Nat := 113662251970291344470891

theorem tailTrace_747078 : CollatzResearch.WordTrace tailWord_747078 prefixEnd_747078 113662251970291344470891 := by
  unfold tailWord_747078
  simp only [CollatzResearch.WordTrace]
  refine ⟨851505412108483487796559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 18165448791647647739659925 851505412108483487796559)
  ·
    refine ⟨1277258118162725231694839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 851505412108483487796559 1277258118162725231694839)
    ·
      refine ⟨1915887177244087847542259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1277258118162725231694839 1915887177244087847542259)
      ·
        refine ⟨2873830765866131771313389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1915887177244087847542259 2873830765866131771313389)
        ·
          refine ⟨1077686537199799414242521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2873830765866131771313389 1077686537199799414242521)
          ·
            refine ⟨808264902899849560681891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1077686537199799414242521 808264902899849560681891)
            ·
              refine ⟨1212397354349774341022837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 808264902899849560681891 1212397354349774341022837)
              ·
                refine ⟨113662251970291344470891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1212397354349774341022837 113662251970291344470891)
                ·
                  rfl

theorem cell20_747078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_747078 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_747078 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_747078 prefixEnd_747078 := by exact prefixLift 747078
  have htrace : WordTrace (prefixWord ++ tailWord_747078) baseStart_747078 baseEnd_747078 := by
    simpa [prefixWord, tailWord_747078, baseEnd_747078] using wordTrace_append hprefix tailTrace_747078
  have hstable : (prefixWord ++ tailWord_747078).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747078).length < 2 ^ (prefixWord ++ tailWord_747078).sum := by decide
  have hdescent : baseEnd_747078 < baseStart_747078 := by decide
  rcases family_descends (prefixWord ++ tailWord_747078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747154 : List Nat := [3, 2, 3, 1, 4, 1, 2, 4]
def baseStart_747154 : Nat := 118140960795 + 747154 * 2 ^ 59
def prefixEnd_747154 : Nat := 4983230072969 + 3 ^ 40 * 747154 * 2
def baseEnd_747154 : Nat := 113673814793918515626343

theorem tailTrace_747154 : CollatzResearch.WordTrace tailWord_747154 prefixEnd_747154 113673814793918515626343 := by
  unfold tailWord_747154
  simp only [CollatzResearch.WordTrace]
  refine ⟨6812736283799034147314129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18167296756797424392837677 6812736283799034147314129)
  ·
    refine ⟨5109552212849275610485597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6812736283799034147314129 5109552212849275610485597)
    ·
      refine ⟨1916082079818478353932099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5109552212849275610485597 1916082079818478353932099)
      ·
        refine ⟨2874123119727717530898149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1916082079818478353932099 2874123119727717530898149)
        ·
          refine ⟨538898084948947037043403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2874123119727717530898149 538898084948947037043403)
          ·
            refine ⟨808347127423420555565105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 538898084948947037043403 808347127423420555565105)
            ·
              refine ⟨606260345567565416673829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 808347127423420555565105 606260345567565416673829)
              ·
                refine ⟨113673814793918515626343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 606260345567565416673829 113673814793918515626343)
                ·
                  rfl

theorem cell20_747154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 2, 4].length) (baseStart_747154 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_747154 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_747154 prefixEnd_747154 := by exact prefixLift 747154
  have htrace : WordTrace (prefixWord ++ tailWord_747154) baseStart_747154 baseEnd_747154 := by
    simpa [prefixWord, tailWord_747154, baseEnd_747154] using wordTrace_append hprefix tailTrace_747154
  have hstable : (prefixWord ++ tailWord_747154).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747154).length < 2 ^ (prefixWord ++ tailWord_747154).sum := by decide
  have hdescent : baseEnd_747154 < baseStart_747154 := by decide
  rcases family_descends (prefixWord ++ tailWord_747154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747168 : List Nat := [2, 1, 1, 4, 3, 3, 1, 3, 2]
def baseStart_747168 : Nat := 118140960795 + 747168 * 2 ^ 59
def prefixEnd_747168 : Nat := 4983230072969 + 3 ^ 40 * 747168 * 2
def baseEnd_747168 : Nat := 341027834363233720412305

theorem tailTrace_747168 : CollatzResearch.WordTrace tailWord_747168 prefixEnd_747168 341027834363233720412305 := by
  unfold tailWord_747168
  simp only [CollatzResearch.WordTrace]
  refine ⟨13625727878572708490133079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18167637171430277986844105 13625727878572708490133079)
  ·
    refine ⟨20438591817859062735199619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13625727878572708490133079 20438591817859062735199619)
    ·
      refine ⟨30657887726788594102799429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20438591817859062735199619 30657887726788594102799429)
      ·
        refine ⟨5748353948772861394274893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30657887726788594102799429 5748353948772861394274893)
        ·
          refine ⟨2155632730789823022853085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5748353948772861394274893 2155632730789823022853085)
          ·
            refine ⟨808362274046183633569907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2155632730789823022853085 808362274046183633569907)
            ·
              refine ⟨1212543411069275450354861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 808362274046183633569907 1212543411069275450354861)
              ·
                refine ⟨454703779150978293883073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1212543411069275450354861 454703779150978293883073)
                ·
                  refine ⟨341027834363233720412305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 454703779150978293883073 341027834363233720412305)
                  ·
                    rfl

theorem cell20_747168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 1, 3, 2].length) (baseStart_747168 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_747168 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_747168 prefixEnd_747168 := by exact prefixLift 747168
  have htrace : WordTrace (prefixWord ++ tailWord_747168) baseStart_747168 baseEnd_747168 := by
    simpa [prefixWord, tailWord_747168, baseEnd_747168] using wordTrace_append hprefix tailTrace_747168
  have hstable : (prefixWord ++ tailWord_747168).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747168).length < 2 ^ (prefixWord ++ tailWord_747168).sum := by decide
  have hdescent : baseEnd_747168 < baseStart_747168 := by decide
  rcases family_descends (prefixWord ++ tailWord_747168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747186 : List Nat := [3, 2, 1, 1, 1, 2, 4, 1, 5]
def baseStart_747186 : Nat := 118140960795 + 747186 * 2 ^ 59
def prefixEnd_747186 : Nat := 4983230072969 + 3 ^ 40 * 747186 * 2
def baseEnd_747186 : Nat := 341036050053705657812231

theorem tailTrace_747186 : CollatzResearch.WordTrace tailWord_747186 prefixEnd_747186 341036050053705657812231 := by
  unfold tailWord_747186
  simp only [CollatzResearch.WordTrace]
  refine ⟨6813028067770051513605353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18168074847386804036280941 6813028067770051513605353)
  ·
    refine ⟨5109771050827538635204015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6813028067770051513605353 5109771050827538635204015)
    ·
      refine ⟨7664656576241307952806023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5109771050827538635204015 7664656576241307952806023)
      ·
        refine ⟨11496984864361961929209035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7664656576241307952806023 11496984864361961929209035)
        ·
          refine ⟨17245477296542942893813553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11496984864361961929209035 17245477296542942893813553)
          ·
            refine ⟨12934107972407207170360165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17245477296542942893813553 12934107972407207170360165)
            ·
              refine ⟨2425145244826351344442531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12934107972407207170360165 2425145244826351344442531)
              ·
                refine ⟨3637717867239527016663797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2425145244826351344442531 3637717867239527016663797)
                ·
                  refine ⟨341036050053705657812231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3637717867239527016663797 341036050053705657812231)
                  ·
                    rfl

theorem cell20_747186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 1, 5].length) (baseStart_747186 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_747186 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_747186 prefixEnd_747186 := by exact prefixLift 747186
  have htrace : WordTrace (prefixWord ++ tailWord_747186) baseStart_747186 baseEnd_747186 := by
    simpa [prefixWord, tailWord_747186, baseEnd_747186] using wordTrace_append hprefix tailTrace_747186
  have hstable : (prefixWord ++ tailWord_747186).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747186).length < 2 ^ (prefixWord ++ tailWord_747186).sum := by decide
  have hdescent : baseEnd_747186 < baseStart_747186 := by decide
  rcases family_descends (prefixWord ++ tailWord_747186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747276 : List Nat := [2, 2, 1, 2, 2, 1, 2, 8]
def baseStart_747276 : Nat := 118140960795 + 747276 * 2 ^ 59
def prefixEnd_747276 : Nat := 4983230072969 + 3 ^ 40 * 747276 * 2
def baseEnd_747276 : Nat := 113692376168688448270621

theorem tailTrace_747276 : CollatzResearch.WordTrace tailWord_747276 prefixEnd_747276 113692376168688448270621 := by
  unfold tailWord_747276
  simp only [CollatzResearch.WordTrace]
  refine ⟨13627697420377075712598841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18170263227169434283465121 13627697420377075712598841)
  ·
    refine ⟨10220773065282806784449131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13627697420377075712598841 10220773065282806784449131)
    ·
      refine ⟨15331159597924210176673697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10220773065282806784449131 15331159597924210176673697)
      ·
        refine ⟨11498369698443157632505273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15331159597924210176673697 11498369698443157632505273)
        ·
          refine ⟨8623777273832368224378955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11498369698443157632505273 8623777273832368224378955)
          ·
            refine ⟨12935665910748552336568433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8623777273832368224378955 12935665910748552336568433)
            ·
              refine ⟨9701749433061414252426325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12935665910748552336568433 9701749433061414252426325)
              ·
                refine ⟨113692376168688448270621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9701749433061414252426325 113692376168688448270621)
                ·
                  rfl

theorem cell20_747276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 8].length) (baseStart_747276 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_747276 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_747276 prefixEnd_747276 := by exact prefixLift 747276
  have htrace : WordTrace (prefixWord ++ tailWord_747276) baseStart_747276 baseEnd_747276 := by
    simpa [prefixWord, tailWord_747276, baseEnd_747276] using wordTrace_append hprefix tailTrace_747276
  have hstable : (prefixWord ++ tailWord_747276).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747276).length < 2 ^ (prefixWord ++ tailWord_747276).sum := by decide
  have hdescent : baseEnd_747276 < baseStart_747276 := by decide
  rcases family_descends (prefixWord ++ tailWord_747276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747282 : List Nat := [3, 2, 4, 1, 1, 1, 1, 5, 2]
def baseStart_747282 : Nat := 118140960795 + 747282 * 2 ^ 59
def prefixEnd_747282 : Nat := 4983230072969 + 3 ^ 40 * 747282 * 2
def baseEnd_747282 : Nat := 341079867069555990611839

theorem tailTrace_747282 : CollatzResearch.WordTrace tailWord_747282 prefixEnd_747282 341079867069555990611839 := by
  unfold tailWord_747282
  simp only [CollatzResearch.WordTrace]
  refine ⟨6813903419683103612479025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18170409119154942966610733 6813903419683103612479025)
  ·
    refine ⟨5110427564762327709359269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6813903419683103612479025 5110427564762327709359269)
    ·
      refine ⟨958205168392936445504863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5110427564762327709359269 958205168392936445504863)
      ·
        refine ⟨1437307752589404668257295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 958205168392936445504863 1437307752589404668257295)
        ·
          refine ⟨2155961628884107002385943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1437307752589404668257295 2155961628884107002385943)
          ·
            refine ⟨3233942443326160503578915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2155961628884107002385943 3233942443326160503578915)
            ·
              refine ⟨4850913664989240755368373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3233942443326160503578915 4850913664989240755368373)
              ·
                refine ⟨454773156092741320815785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4850913664989240755368373 454773156092741320815785)
                ·
                  refine ⟨341079867069555990611839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 454773156092741320815785 341079867069555990611839)
                  ·
                    rfl

theorem cell20_747282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 5, 2].length) (baseStart_747282 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_747282 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_747282 prefixEnd_747282 := by exact prefixLift 747282
  have htrace : WordTrace (prefixWord ++ tailWord_747282) baseStart_747282 baseEnd_747282 := by
    simpa [prefixWord, tailWord_747282, baseEnd_747282] using wordTrace_append hprefix tailTrace_747282
  have hstable : (prefixWord ++ tailWord_747282).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747282).length < 2 ^ (prefixWord ++ tailWord_747282).sum := by decide
  have hdescent : baseEnd_747282 < baseStart_747282 := by decide
  rcases family_descends (prefixWord ++ tailWord_747282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747327 : List Nat := [1, 1, 2, 2, 7, 1, 2, 4]
def baseStart_747327 : Nat := 118140960795 + 747327 * 2 ^ 59
def prefixEnd_747327 : Nat := 4983230072969 + 3 ^ 40 * 747327 * 2
def baseEnd_747327 : Nat := 113700135431911944703885

theorem tailTrace_747327 : CollatzResearch.WordTrace tailWord_747327 prefixEnd_747327 113700135431911944703885 := by
  unfold tailWord_747327
  simp only [CollatzResearch.WordTrace]
  refine ⟨27257254963569387135304235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18171503309046258090202823 27257254963569387135304235)
  ·
    refine ⟨40885882445354080702956353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27257254963569387135304235 40885882445354080702956353)
    ·
      refine ⟨30664411834015560527217265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40885882445354080702956353 30664411834015560527217265)
      ·
        refine ⟨22998308875511670395412949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30664411834015560527217265 22998308875511670395412949)
        ·
          refine ⟨539022864269804774892491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 22998308875511670395412949 539022864269804774892491)
          ·
            refine ⟨808534296404707162338737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 539022864269804774892491 808534296404707162338737)
            ·
              refine ⟨606400722303530371754053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 808534296404707162338737 606400722303530371754053)
              ·
                refine ⟨113700135431911944703885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 606400722303530371754053 113700135431911944703885)
                ·
                  rfl

theorem cell20_747327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 2, 4].length) (baseStart_747327 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_747327 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_747327 prefixEnd_747327 := by exact prefixLift 747327
  have htrace : WordTrace (prefixWord ++ tailWord_747327) baseStart_747327 baseEnd_747327 := by
    simpa [prefixWord, tailWord_747327, baseEnd_747327] using wordTrace_append hprefix tailTrace_747327
  have hstable : (prefixWord ++ tailWord_747327).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747327).length < 2 ^ (prefixWord ++ tailWord_747327).sum := by decide
  have hdescent : baseEnd_747327 < baseStart_747327 := by decide
  rcases family_descends (prefixWord ++ tailWord_747327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747331 : List Nat := [1, 1, 1, 3, 1, 5, 4, 4]
def baseStart_747331 : Nat := 118140960795 + 747331 * 2 ^ 59
def prefixEnd_747331 : Nat := 4983230072969 + 3 ^ 40 * 747331 * 2
def baseEnd_747331 : Nat := 113700744001576532659435

theorem tailTrace_747331 : CollatzResearch.WordTrace tailWord_747331 prefixEnd_747331 113700744001576532659435 := by
  unfold tailWord_747331
  simp only [CollatzResearch.WordTrace]
  refine ⟨27257400855554895818449847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18171600570369930545633231 27257400855554895818449847)
  ·
    refine ⟨40886101283332343727674771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27257400855554895818449847 40886101283332343727674771)
    ·
      refine ⟨61329151924998515591512157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40886101283332343727674771 61329151924998515591512157)
      ·
        refine ⟨22998431971874443346817059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61329151924998515591512157 22998431971874443346817059)
        ·
          refine ⟨34497647957811665020225589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22998431971874443346817059 34497647957811665020225589)
          ·
            refine ⟨3234154496044843595646149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34497647957811665020225589 3234154496044843595646149)
            ·
              refine ⟨606403968008408174183653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3234154496044843595646149 606403968008408174183653)
              ·
                refine ⟨113700744001576532659435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 606403968008408174183653 113700744001576532659435)
                ·
                  rfl

theorem cell20_747331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 4, 4].length) (baseStart_747331 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_747331 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_747331 prefixEnd_747331 := by exact prefixLift 747331
  have htrace : WordTrace (prefixWord ++ tailWord_747331) baseStart_747331 baseEnd_747331 := by
    simpa [prefixWord, tailWord_747331, baseEnd_747331] using wordTrace_append hprefix tailTrace_747331
  have hstable : (prefixWord ++ tailWord_747331).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747331).length < 2 ^ (prefixWord ++ tailWord_747331).sum := by decide
  have hdescent : baseEnd_747331 < baseStart_747331 := by decide
  rcases family_descends (prefixWord ++ tailWord_747331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747334 : List Nat := [6, 1, 1, 2, 1, 1, 1, 2, 5]
def baseStart_747334 : Nat := 118140960795 + 747334 * 2 ^ 59
def prefixEnd_747334 : Nat := 4983230072969 + 3 ^ 40 * 747334 * 2
def baseEnd_747334 : Nat := 341103601286474920878293

theorem tailTrace_747334 : CollatzResearch.WordTrace tailWord_747334 prefixEnd_747334 341103601286474920878293 := by
  unfold tailWord_747334
  simp only [CollatzResearch.WordTrace]
  refine ⟨851797196079500854087783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 18171673516362684887206037 851797196079500854087783)
  ·
    refine ⟨1277695794119251281131675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 851797196079500854087783 1277695794119251281131675)
    ·
      refine ⟨1916543691178876921697513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1277695794119251281131675 1916543691178876921697513)
      ·
        refine ⟨1437407768384157691273135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1916543691178876921697513 1437407768384157691273135)
        ·
          refine ⟨2156111652576236536909703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1437407768384157691273135 2156111652576236536909703)
          ·
            refine ⟨3234167478864354805364555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2156111652576236536909703 3234167478864354805364555)
            ·
              refine ⟨4851251218296532208046833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3234167478864354805364555 4851251218296532208046833)
              ·
                refine ⟨3638438413722399156035125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4851251218296532208046833 3638438413722399156035125)
                ·
                  refine ⟨341103601286474920878293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3638438413722399156035125 341103601286474920878293)
                  ·
                    rfl

theorem cell20_747334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_747334 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_747334 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_747334 prefixEnd_747334 := by exact prefixLift 747334
  have htrace : WordTrace (prefixWord ++ tailWord_747334) baseStart_747334 baseEnd_747334 := by
    simpa [prefixWord, tailWord_747334, baseEnd_747334] using wordTrace_append hprefix tailTrace_747334
  have hstable : (prefixWord ++ tailWord_747334).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747334).length < 2 ^ (prefixWord ++ tailWord_747334).sum := by decide
  have hdescent : baseEnd_747334 < baseStart_747334 := by decide
  rcases family_descends (prefixWord ++ tailWord_747334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747372 : List Nat := [2, 2, 1, 1, 4, 4, 2, 1, 3]
def baseStart_747372 : Nat := 118140960795 + 747372 * 2 ^ 59
def prefixEnd_747372 : Nat := 4983230072969 + 3 ^ 40 * 747372 * 2
def baseEnd_747372 : Nat := 341120945521915677611471

theorem tailTrace_747372 : CollatzResearch.WordTrace tailWord_747372 prefixEnd_747372 341120945521915677611471 := by
  unfold tailWord_747372
  simp only [CollatzResearch.WordTrace]
  refine ⟨13629448124203179910346185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18172597498937573213794913 13629448124203179910346185)
  ·
    refine ⟨10222086093152384932759639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13629448124203179910346185 10222086093152384932759639)
    ·
      refine ⟨15333129139728577399139459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10222086093152384932759639 15333129139728577399139459)
      ·
        refine ⟨22999693709592866098709189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15333129139728577399139459 22999693709592866098709189)
        ·
          refine ⟨4312442570548662393507973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22999693709592866098709189 4312442570548662393507973)
          ·
            refine ⟨808582981977874198782745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4312442570548662393507973 808582981977874198782745)
            ·
              refine ⟨606437236483405649087059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 808582981977874198782745 606437236483405649087059)
              ·
                refine ⟨909655854725108473630589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 606437236483405649087059 909655854725108473630589)
                ·
                  refine ⟨341120945521915677611471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 909655854725108473630589 341120945521915677611471)
                  ·
                    rfl

theorem cell20_747372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 3].length) (baseStart_747372 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_747372 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_747372 prefixEnd_747372 := by exact prefixLift 747372
  have htrace : WordTrace (prefixWord ++ tailWord_747372) baseStart_747372 baseEnd_747372 := by
    simpa [prefixWord, tailWord_747372, baseEnd_747372] using wordTrace_append hprefix tailTrace_747372
  have hstable : (prefixWord ++ tailWord_747372).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747372).length < 2 ^ (prefixWord ++ tailWord_747372).sum := by decide
  have hdescent : baseEnd_747372 < baseStart_747372 := by decide
  rcases family_descends (prefixWord ++ tailWord_747372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747410 : List Nat := [3, 2, 3, 2, 1, 2, 2, 2, 3]
def baseStart_747410 : Nat := 118140960795 + 747410 * 2 ^ 59
def prefixEnd_747410 : Nat := 4983230072969 + 3 ^ 40 * 747410 * 2
def baseEnd_747410 : Nat := 341138289757356434344649

theorem tailTrace_747410 : CollatzResearch.WordTrace tailWord_747410 prefixEnd_747410 341138289757356434344649 := by
  unfold tailWord_747410
  simp only [CollatzResearch.WordTrace]
  refine ⟨6815070555567173077643921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18173521481512461540383789 6815070555567173077643921)
  ·
    refine ⟨5111302916675379808232941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6815070555567173077643921 5111302916675379808232941)
    ·
      refine ⟨1916738593753267428087353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5111302916675379808232941 1916738593753267428087353)
      ·
        refine ⟨1437553945314950571065515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1916738593753267428087353 1437553945314950571065515)
        ·
          refine ⟨2156330917972425856598273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1437553945314950571065515 2156330917972425856598273)
          ·
            refine ⟨1617248188479319392448705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2156330917972425856598273 1617248188479319392448705)
            ·
              refine ⟨1212936141359489544336529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1617248188479319392448705 1212936141359489544336529)
              ·
                refine ⟨909702106019617158252397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1212936141359489544336529 909702106019617158252397)
                ·
                  refine ⟨341138289757356434344649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 909702106019617158252397 341138289757356434344649)
                  ·
                    rfl

theorem cell20_747410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 2, 2, 3].length) (baseStart_747410 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_747410 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_747410 prefixEnd_747410 := by exact prefixLift 747410
  have htrace : WordTrace (prefixWord ++ tailWord_747410) baseStart_747410 baseEnd_747410 := by
    simpa [prefixWord, tailWord_747410, baseEnd_747410] using wordTrace_append hprefix tailTrace_747410
  have hstable : (prefixWord ++ tailWord_747410).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747410).length < 2 ^ (prefixWord ++ tailWord_747410).sum := by decide
  have hdescent : baseEnd_747410 < baseStart_747410 := by decide
  rcases family_descends (prefixWord ++ tailWord_747410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747417 : List Nat := [1, 2, 1, 2, 1, 3, 6, 2, 2]
def baseStart_747417 : Nat := 118140960795 + 747417 * 2 ^ 59
def prefixEnd_747417 : Nat := 4983230072969 + 3 ^ 40 * 747417 * 2
def baseEnd_747417 : Nat := 341141484748095521111287

theorem tailTrace_747417 : CollatzResearch.WordTrace tailWord_747417 prefixEnd_747417 341141484748095521111287 := by
  unfold tailWord_747417
  simp only [CollatzResearch.WordTrace]
  refine ⟨27260537533243332506080505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18173691688828888337387003 27260537533243332506080505)
  ·
    refine ⟨20445403149932499379560379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27260537533243332506080505 20445403149932499379560379)
    ·
      refine ⟨30668104724898749069340569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20445403149932499379560379 30668104724898749069340569)
      ·
        refine ⟨23001078543674061802005427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30668104724898749069340569 23001078543674061802005427)
        ·
          refine ⟨34501617815511092703008141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23001078543674061802005427 34501617815511092703008141)
          ·
            refine ⟨12938106680816659763628053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34501617815511092703008141 12938106680816659763628053)
            ·
              refine ⟨606473750663280926420065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 12938106680816659763628053 606473750663280926420065)
              ·
                refine ⟨454855312997460694815049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 606473750663280926420065 454855312997460694815049)
                ·
                  refine ⟨341141484748095521111287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 454855312997460694815049 341141484748095521111287)
                  ·
                    rfl

theorem cell20_747417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 6, 2, 2].length) (baseStart_747417 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_747417 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_747417 prefixEnd_747417 := by exact prefixLift 747417
  have htrace : WordTrace (prefixWord ++ tailWord_747417) baseStart_747417 baseEnd_747417 := by
    simpa [prefixWord, tailWord_747417, baseEnd_747417] using wordTrace_append hprefix tailTrace_747417
  have hstable : (prefixWord ++ tailWord_747417).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747417).length < 2 ^ (prefixWord ++ tailWord_747417).sum := by decide
  have hdescent : baseEnd_747417 < baseStart_747417 := by decide
  rcases family_descends (prefixWord ++ tailWord_747417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747431 : List Nat := [1, 1, 6, 1, 2, 1, 2, 3, 3]
def baseStart_747431 : Nat := 118140960795 + 747431 * 2 ^ 59
def prefixEnd_747431 : Nat := 4983230072969 + 3 ^ 40 * 747431 * 2
def baseEnd_747431 : Nat := 341147874729573694644563

theorem tailTrace_747431 : CollatzResearch.WordTrace tailWord_747431 prefixEnd_747431 341147874729573694644563 := by
  unfold tailWord_747431
  simp only [CollatzResearch.WordTrace]
  refine ⟨27261048155192612897090147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18174032103461741931393431 27261048155192612897090147)
  ·
    refine ⟨40891572232788919345635221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27261048155192612897090147 40891572232788919345635221)
    ·
      refine ⟨1916792448411980594326651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 40891572232788919345635221 1916792448411980594326651)
      ·
        refine ⟨2875188672617970891489977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1916792448411980594326651 2875188672617970891489977)
        ·
          refine ⟨2156391504463478168617483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2875188672617970891489977 2156391504463478168617483)
          ·
            refine ⟨3234587256695217252926225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2156391504463478168617483 3234587256695217252926225)
            ·
              refine ⟨2425940442521412939694669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3234587256695217252926225 2425940442521412939694669)
              ·
                refine ⟨909727665945529852385501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2425940442521412939694669 909727665945529852385501)
                ·
                  refine ⟨341147874729573694644563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 909727665945529852385501 341147874729573694644563)
                  ·
                    rfl

theorem cell20_747431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 3, 3].length) (baseStart_747431 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_747431 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_747431 prefixEnd_747431 := by exact prefixLift 747431
  have htrace : WordTrace (prefixWord ++ tailWord_747431) baseStart_747431 baseEnd_747431 := by
    simpa [prefixWord, tailWord_747431, baseEnd_747431] using wordTrace_append hprefix tailTrace_747431
  have hstable : (prefixWord ++ tailWord_747431).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747431).length < 2 ^ (prefixWord ++ tailWord_747431).sum := by decide
  have hdescent : baseEnd_747431 < baseStart_747431 := by decide
  rcases family_descends (prefixWord ++ tailWord_747431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747476 : List Nat := [2, 4, 1, 2, 1, 1, 4, 1, 4]
def baseStart_747476 : Nat := 118140960795 + 747476 * 2 ^ 59
def prefixEnd_747476 : Nat := 4983230072969 + 3 ^ 40 * 747476 * 2
def baseEnd_747476 : Nat := 341168413955753538144379

theorem tailTrace_747476 : CollatzResearch.WordTrace tailWord_747476 prefixEnd_747476 341168413955753538144379 := by
  unfold tailWord_747476
  simp only [CollatzResearch.WordTrace]
  refine ⟨13631344720014792791239141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18175126293353057054985521 13631344720014792791239141)
  ·
    refine ⟨2555877135002773648357339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13631344720014792791239141 2555877135002773648357339)
    ·
      refine ⟨3833815702504160472536009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2555877135002773648357339 3833815702504160472536009)
      ·
        refine ⟨2875361776878120354402007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3833815702504160472536009 2875361776878120354402007)
        ·
          refine ⟨4313042665317180531603011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2875361776878120354402007 4313042665317180531603011)
          ·
            refine ⟨6469563997975770797404517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4313042665317180531603011 6469563997975770797404517)
            ·
              refine ⟨1213043249620457024513347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6469563997975770797404517 1213043249620457024513347)
              ·
                refine ⟨1819564874430685536770021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1213043249620457024513347 1819564874430685536770021)
                ·
                  refine ⟨341168413955753538144379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1819564874430685536770021 341168413955753538144379)
                  ·
                    rfl

theorem cell20_747476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_747476 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_747476 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_747476 prefixEnd_747476 := by exact prefixLift 747476
  have htrace : WordTrace (prefixWord ++ tailWord_747476) baseStart_747476 baseEnd_747476 := by
    simpa [prefixWord, tailWord_747476, baseEnd_747476] using wordTrace_append hprefix tailTrace_747476
  have hstable : (prefixWord ++ tailWord_747476).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747476).length < 2 ^ (prefixWord ++ tailWord_747476).sum := by decide
  have hdescent : baseEnd_747476 < baseStart_747476 := by decide
  rcases family_descends (prefixWord ++ tailWord_747476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747528 : List Nat := [2, 1, 3, 2, 1, 2, 2, 4, 3]
def baseStart_747528 : Nat := 118140960795 + 747528 * 2 ^ 59
def prefixEnd_747528 : Nat := 4983230072969 + 3 ^ 40 * 747528 * 2
def baseEnd_747528 : Nat := 341192148172672468410833

theorem tailTrace_747528 : CollatzResearch.WordTrace tailWord_747528 prefixEnd_747528 341192148172672468410833 := by
  unfold tailWord_747528
  simp only [CollatzResearch.WordTrace]
  refine ⟨13632293017920599231685619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18176390690560798975580825 13632293017920599231685619)
  ·
    refine ⟨20448439526880898847528429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13632293017920599231685619 20448439526880898847528429)
    ·
      refine ⟨7668164822580337067823161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20448439526880898847528429 7668164822580337067823161)
      ·
        refine ⟨5751123616935252800867371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7668164822580337067823161 5751123616935252800867371)
        ·
          refine ⟨8626685425402879201301057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5751123616935252800867371 8626685425402879201301057)
          ·
            refine ⟨6470014069052159400975793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8626685425402879201301057 6470014069052159400975793)
            ·
              refine ⟨4852510551789119550731845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6470014069052159400975793 4852510551789119550731845)
              ·
                refine ⟨909845728460459915762221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4852510551789119550731845 909845728460459915762221)
                ·
                  refine ⟨341192148172672468410833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 909845728460459915762221 341192148172672468410833)
                  ·
                    rfl

theorem cell20_747528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 4, 3].length) (baseStart_747528 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_747528 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_747528 prefixEnd_747528 := by exact prefixLift 747528
  have htrace : WordTrace (prefixWord ++ tailWord_747528) baseStart_747528 baseEnd_747528 := by
    simpa [prefixWord, tailWord_747528, baseEnd_747528] using wordTrace_append hprefix tailTrace_747528
  have hstable : (prefixWord ++ tailWord_747528).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747528).length < 2 ^ (prefixWord ++ tailWord_747528).sum := by decide
  have hdescent : baseEnd_747528 < baseStart_747528 := by decide
  rcases family_descends (prefixWord ++ tailWord_747528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747531 : List Nat := [1, 1, 1, 1, 6, 1, 5, 2, 2]
def baseStart_747531 : Nat := 118140960795 + 747531 * 2 ^ 59
def prefixEnd_747531 : Nat := 4983230072969 + 3 ^ 40 * 747531 * 2
def baseEnd_747531 : Nat := 341193517454417791310821

theorem tailTrace_747531 : CollatzResearch.WordTrace tailWord_747531 prefixEnd_747531 341193517454417791310821 := by
  unfold tailWord_747531
  simp only [CollatzResearch.WordTrace]
  refine ⟨27264695454830329975730447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18176463636553553317153631 27264695454830329975730447)
  ·
    refine ⟨40897043182245494963595671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27264695454830329975730447 40897043182245494963595671)
    ·
      refine ⟨61345564773368242445393507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40897043182245494963595671 61345564773368242445393507)
      ·
        refine ⟨92018347160052363668090261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61345564773368242445393507 92018347160052363668090261)
        ·
          refine ⟨4313360023127454546941731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 92018347160052363668090261 4313360023127454546941731)
          ·
            refine ⟨6470040034691181820412597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4313360023127454546941731 6470040034691181820412597)
            ·
              refine ⟨606566253252298295663681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6470040034691181820412597 606566253252298295663681)
              ·
                refine ⟨454924689939223721747761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 606566253252298295663681 454924689939223721747761)
                ·
                  refine ⟨341193517454417791310821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 454924689939223721747761 341193517454417791310821)
                  ·
                    rfl

theorem cell20_747531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 5, 2, 2].length) (baseStart_747531 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_747531 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_747531 prefixEnd_747531 := by exact prefixLift 747531
  have htrace : WordTrace (prefixWord ++ tailWord_747531) baseStart_747531 baseEnd_747531 := by
    simpa [prefixWord, tailWord_747531, baseEnd_747531] using wordTrace_append hprefix tailTrace_747531
  have hstable : (prefixWord ++ tailWord_747531).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747531).length < 2 ^ (prefixWord ++ tailWord_747531).sum := by decide
  have hdescent : baseEnd_747531 < baseStart_747531 := by decide
  rcases family_descends (prefixWord ++ tailWord_747531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747541 : List Nat := [1, 3, 2, 1, 6, 1, 2, 1, 3]
def baseStart_747541 : Nat := 118140960795 + 747541 * 2 ^ 59
def prefixEnd_747541 : Nat := 4983230072969 + 3 ^ 40 * 747541 * 2
def baseEnd_747541 : Nat := 341198081726902200977447

theorem tailTrace_747541 : CollatzResearch.WordTrace tailWord_747541 prefixEnd_747541 341198081726902200977447 := by
  unfold tailWord_747541
  simp only [CollatzResearch.WordTrace]
  refine ⟨27265060184794101683594477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18176706789862734455729651 27265060184794101683594477)
  ·
    refine ⟨10224397569297788131347929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27265060184794101683594477 10224397569297788131347929)
    ·
      refine ⟨7668298176973341098510947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10224397569297788131347929 7668298176973341098510947)
      ·
        refine ⟨11502447265460011647766421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7668298176973341098510947 11502447265460011647766421)
        ·
          refine ⟨539177215568438045989051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 11502447265460011647766421 539177215568438045989051)
          ·
            refine ⟨808765823352657068983577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 539177215568438045989051 808765823352657068983577)
            ·
              refine ⟨606574367514492801737683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 808765823352657068983577 606574367514492801737683)
              ·
                refine ⟨909861551271739202606525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 606574367514492801737683 909861551271739202606525)
                ·
                  refine ⟨341198081726902200977447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 909861551271739202606525 341198081726902200977447)
                  ·
                    rfl

theorem cell20_747541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 2, 1, 3].length) (baseStart_747541 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_747541 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_747541 prefixEnd_747541 := by exact prefixLift 747541
  have htrace : WordTrace (prefixWord ++ tailWord_747541) baseStart_747541 baseEnd_747541 := by
    simpa [prefixWord, tailWord_747541, baseEnd_747541] using wordTrace_append hprefix tailTrace_747541
  have hstable : (prefixWord ++ tailWord_747541).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747541).length < 2 ^ (prefixWord ++ tailWord_747541).sum := by decide
  have hdescent : baseEnd_747541 < baseStart_747541 := by decide
  rcases family_descends (prefixWord ++ tailWord_747541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747582 : List Nat := [4, 2, 1, 3, 3, 1, 2, 2, 2]
def baseStart_747582 : Nat := 118140960795 + 747582 * 2 ^ 59
def prefixEnd_747582 : Nat := 4983230072969 + 3 ^ 40 * 747582 * 2
def baseEnd_747582 : Nat := 341216795244088280610613

theorem tailTrace_747582 : CollatzResearch.WordTrace tailWord_747582 prefixEnd_747582 341216795244088280610613 := by
  unfold tailWord_747582
  simp only [CollatzResearch.WordTrace]
  refine ⟨3408319447205695710729625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18177703718430377123891333 3408319447205695710729625)
  ·
    refine ⟨2556239585404271783047219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3408319447205695710729625 2556239585404271783047219)
    ·
      refine ⟨3834359378106407674570829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2556239585404271783047219 3834359378106407674570829)
      ·
        refine ⟨1437884766789902877964061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3834359378106407674570829 1437884766789902877964061)
        ·
          refine ⟨539206787546213579236523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1437884766789902877964061 539206787546213579236523)
          ·
            refine ⟨808810181319320368854785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 539206787546213579236523 808810181319320368854785)
            ·
              refine ⟨606607635989490276641089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 808810181319320368854785 606607635989490276641089)
              ·
                refine ⟨454955726992117707480817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 606607635989490276641089 454955726992117707480817)
                ·
                  refine ⟨341216795244088280610613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 454955726992117707480817 341216795244088280610613)
                  ·
                    rfl

theorem cell20_747582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 2, 2, 2].length) (baseStart_747582 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_747582 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_747582 prefixEnd_747582 := by exact prefixLift 747582
  have htrace : WordTrace (prefixWord ++ tailWord_747582) baseStart_747582 baseEnd_747582 := by
    simpa [prefixWord, tailWord_747582, baseEnd_747582] using wordTrace_append hprefix tailTrace_747582
  have hstable : (prefixWord ++ tailWord_747582).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747582).length < 2 ^ (prefixWord ++ tailWord_747582).sum := by decide
  have hdescent : baseEnd_747582 < baseStart_747582 := by decide
  rcases family_descends (prefixWord ++ tailWord_747582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747625 : List Nat := [1, 2, 1, 1, 1, 5, 2, 2, 5]
def baseStart_747625 : Nat := 118140960795 + 747625 * 2 ^ 59
def prefixEnd_747625 : Nat := 4983230072969 + 3 ^ 40 * 747625 * 2
def baseEnd_747625 : Nat := 341236421615771242177103

theorem tailTrace_747625 : CollatzResearch.WordTrace tailWord_747625 prefixEnd_747625 341236421615771242177103 := by
  unfold tailWord_747625
  simp only [CollatzResearch.WordTrace]
  refine ⟨27268123916489784029652329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18178749277659856019768219 27268123916489784029652329)
  ·
    refine ⟨20451092937367338022239247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27268123916489784029652329 20451092937367338022239247)
    ·
      refine ⟨30676639406051007033358871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20451092937367338022239247 30676639406051007033358871)
      ·
        refine ⟨46014959109076510550038307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30676639406051007033358871 46014959109076510550038307)
        ·
          refine ⟨69022438663614765825057461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46014959109076510550038307 69022438663614765825057461)
          ·
            refine ⟨6470853624713884296099137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 69022438663614765825057461 6470853624713884296099137)
            ·
              refine ⟨4853140218535413222074353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6470853624713884296099137 4853140218535413222074353)
              ·
                refine ⟨3639855163901559916555765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4853140218535413222074353 3639855163901559916555765)
                ·
                  refine ⟨341236421615771242177103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3639855163901559916555765 341236421615771242177103)
                  ·
                    rfl

theorem cell20_747625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 2, 5].length) (baseStart_747625 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_747625 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_747625 prefixEnd_747625 := by exact prefixLift 747625
  have htrace : WordTrace (prefixWord ++ tailWord_747625) baseStart_747625 baseEnd_747625 := by
    simpa [prefixWord, tailWord_747625, baseEnd_747625] using wordTrace_append hprefix tailTrace_747625
  have hstable : (prefixWord ++ tailWord_747625).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747625).length < 2 ^ (prefixWord ++ tailWord_747625).sum := by decide
  have hdescent : baseEnd_747625 < baseStart_747625 := by decide
  rcases family_descends (prefixWord ++ tailWord_747625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747628 : List Nat := [2, 2, 1, 1, 3, 3, 1, 5, 2]
def baseStart_747628 : Nat := 118140960795 + 747628 * 2 ^ 59
def prefixEnd_747628 : Nat := 4983230072969 + 3 ^ 40 * 747628 * 2
def baseEnd_747628 : Nat := 341237790897516565077091

theorem tailTrace_747628 : CollatzResearch.WordTrace tailWord_747628 prefixEnd_747628 341237790897516565077091 := by
  unfold tailWord_747628
  simp only [CollatzResearch.WordTrace]
  refine ⟨13634116667739457771005769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18178822223652610361341025 13634116667739457771005769)
  ·
    refine ⟨10225587500804593328254327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13634116667739457771005769 10225587500804593328254327)
    ·
      refine ⟨15338381251206889992381491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10225587500804593328254327 15338381251206889992381491)
      ·
        refine ⟨23007571876810334988572237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15338381251206889992381491 23007571876810334988572237)
        ·
          refine ⟨8627839453803875620714589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23007571876810334988572237 8627839453803875620714589)
          ·
            refine ⟨3235439795176453357767971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8627839453803875620714589 3235439795176453357767971)
            ·
              refine ⟨4853159692764680036651957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3235439795176453357767971 4853159692764680036651957)
              ·
                refine ⟨454983721196688753436121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4853159692764680036651957 454983721196688753436121)
                ·
                  refine ⟨341237790897516565077091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 454983721196688753436121 341237790897516565077091)
                  ·
                    rfl

theorem cell20_747628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 5, 2].length) (baseStart_747628 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_747628 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_747628 prefixEnd_747628 := by exact prefixLift 747628
  have htrace : WordTrace (prefixWord ++ tailWord_747628) baseStart_747628 baseEnd_747628 := by
    simpa [prefixWord, tailWord_747628, baseEnd_747628] using wordTrace_append hprefix tailTrace_747628
  have hstable : (prefixWord ++ tailWord_747628).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747628).length < 2 ^ (prefixWord ++ tailWord_747628).sum := by decide
  have hdescent : baseEnd_747628 < baseStart_747628 := by decide
  rcases family_descends (prefixWord ++ tailWord_747628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747638 : List Nat := [5, 1, 1, 2, 1, 4, 1, 2, 3]
def baseStart_747638 : Nat := 118140960795 + 747638 * 2 ^ 59
def prefixEnd_747638 : Nat := 4983230072969 + 3 ^ 40 * 747638 * 2
def baseEnd_747638 : Nat := 341242355170000974743717

theorem tailTrace_747638 : CollatzResearch.WordTrace tailWord_747638 prefixEnd_747638 341242355170000974743717 := by
  unfold tailWord_747638
  simp only [CollatzResearch.WordTrace]
  refine ⟨1704287379090167953117223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18179065376961791499917045 1704287379090167953117223)
  ·
    refine ⟨2556431068635251929675835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1704287379090167953117223 2556431068635251929675835)
    ·
      refine ⟨3834646602952877894513753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2556431068635251929675835 3834646602952877894513753)
      ·
        refine ⟨2875984952214658420885315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3834646602952877894513753 2875984952214658420885315)
        ·
          refine ⟨4313977428321987631327973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2875984952214658420885315 4313977428321987631327973)
          ·
            refine ⟨808870767810372680873995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4313977428321987631327973 808870767810372680873995)
            ·
              refine ⟨1213306151715559021310993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 808870767810372680873995 1213306151715559021310993)
              ·
                refine ⟨909979613786669265983245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1213306151715559021310993 909979613786669265983245)
                ·
                  refine ⟨341242355170000974743717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 909979613786669265983245 341242355170000974743717)
                  ·
                    rfl

theorem cell20_747638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 1, 2, 3].length) (baseStart_747638 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_747638 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_747638 prefixEnd_747638 := by exact prefixLift 747638
  have htrace : WordTrace (prefixWord ++ tailWord_747638) baseStart_747638 baseEnd_747638 := by
    simpa [prefixWord, tailWord_747638, baseEnd_747638] using wordTrace_append hprefix tailTrace_747638
  have hstable : (prefixWord ++ tailWord_747638).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747638).length < 2 ^ (prefixWord ++ tailWord_747638).sum := by decide
  have hdescent : baseEnd_747638 < baseStart_747638 := by decide
  rcases family_descends (prefixWord ++ tailWord_747638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747690 : List Nat := [3, 1, 5, 1, 2, 2, 6]
def baseStart_747690 : Nat := 118140960795 + 747690 * 2 ^ 59
def prefixEnd_747690 : Nat := 4983230072969 + 3 ^ 40 * 747690 * 2
def baseEnd_747690 : Nat := 37918454376324433890019

theorem tailTrace_747690 : CollatzResearch.WordTrace tailWord_747690 prefixEnd_747690 37918454376324433890019 := by
  unfold tailWord_747690
  simp only [CollatzResearch.WordTrace]
  refine ⟨6817623665313575032692131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18180329774169533420512349 6817623665313575032692131)
  ·
    refine ⟨10226435497970362549038197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6817623665313575032692131 10226435497970362549038197)
    ·
      refine ⟨958728327934721488972331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10226435497970362549038197 958728327934721488972331)
      ·
        refine ⟨1438092491902082233458497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 958728327934721488972331 1438092491902082233458497)
        ·
          refine ⟨1078569368926561675093873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1438092491902082233458497 1078569368926561675093873)
          ·
            refine ⟨808927026694921256320405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1078569368926561675093873 808927026694921256320405)
            ·
              refine ⟨37918454376324433890019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 808927026694921256320405 37918454376324433890019)
              ·
                rfl

theorem cell20_747690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 6].length) (baseStart_747690 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_747690 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_747690 prefixEnd_747690 := by exact prefixLift 747690
  have htrace : WordTrace (prefixWord ++ tailWord_747690) baseStart_747690 baseEnd_747690 := by
    simpa [prefixWord, tailWord_747690, baseEnd_747690] using wordTrace_append hprefix tailTrace_747690
  have hstable : (prefixWord ++ tailWord_747690).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747690).length < 2 ^ (prefixWord ++ tailWord_747690).sum := by decide
  have hdescent : baseEnd_747690 < baseStart_747690 := by decide
  rcases family_descends (prefixWord ++ tailWord_747690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747756 : List Nat := [2, 2, 1, 1, 2, 3, 4, 2, 3]
def baseStart_747756 : Nat := 118140960795 + 747756 * 2 ^ 59
def prefixEnd_747756 : Nat := 4983230072969 + 3 ^ 40 * 747756 * 2
def baseEnd_747756 : Nat := 341296213585317008809901

theorem tailTrace_747756 : CollatzResearch.WordTrace tailWord_747756 prefixEnd_747756 341296213585317008809901 := by
  unfold tailWord_747756
  simp only [CollatzResearch.WordTrace]
  refine ⟨13636450939507596701335561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18181934586010128935114081 13636450939507596701335561)
  ·
    refine ⟨10227338204630697526001671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13636450939507596701335561 10227338204630697526001671)
    ·
      refine ⟨15341007306946046289002507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10227338204630697526001671 15341007306946046289002507)
      ·
        refine ⟨23011510960419069433503761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15341007306946046289002507 23011510960419069433503761)
        ·
          refine ⟨17258633220314302075127821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23011510960419069433503761 17258633220314302075127821)
          ·
            refine ⟨6471987457617863278172933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17258633220314302075127821 6471987457617863278172933)
            ·
              refine ⟨1213497648303349364657425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6471987457617863278172933 1213497648303349364657425)
              ·
                refine ⟨910123236227512023493069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1213497648303349364657425 910123236227512023493069)
                ·
                  refine ⟨341296213585317008809901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 910123236227512023493069 341296213585317008809901)
                  ·
                    rfl

theorem cell20_747756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 3].length) (baseStart_747756 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_747756 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_747756 prefixEnd_747756 := by exact prefixLift 747756
  have htrace : WordTrace (prefixWord ++ tailWord_747756) baseStart_747756 baseEnd_747756 := by
    simpa [prefixWord, tailWord_747756, baseEnd_747756] using wordTrace_append hprefix tailTrace_747756
  have hstable : (prefixWord ++ tailWord_747756).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747756).length < 2 ^ (prefixWord ++ tailWord_747756).sum := by decide
  have hdescent : baseEnd_747756 < baseStart_747756 := by decide
  rcases family_descends (prefixWord ++ tailWord_747756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747759 : List Nat := [1, 1, 2, 1, 6, 1, 4, 2, 2]
def baseStart_747759 : Nat := 118140960795 + 747759 * 2 ^ 59
def prefixEnd_747759 : Nat := 4983230072969 + 3 ^ 40 * 747759 * 2
def baseEnd_747759 : Nat := 341297582867062331709889

theorem tailTrace_747759 : CollatzResearch.WordTrace tailWord_747759 prefixEnd_747759 341297582867062331709889 := by
  unfold tailWord_747759
  simp only [CollatzResearch.WordTrace]
  refine ⟨27273011298004324915030331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18182007532002883276686887 27273011298004324915030331)
  ·
    refine ⟨40909516947006487372545497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27273011298004324915030331 40909516947006487372545497)
    ·
      refine ⟨30682137710254865529409123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40909516947006487372545497 30682137710254865529409123)
      ·
        refine ⟨46023206565382298294113685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30682137710254865529409123 46023206565382298294113685)
        ·
          refine ⟨2157337807752295232536579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 46023206565382298294113685 2157337807752295232536579)
          ·
            refine ⟨3236006711628442848804869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2157337807752295232536579 3236006711628442848804869)
            ·
              refine ⟨606751258430333034150913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3236006711628442848804869 606751258430333034150913)
              ·
                refine ⟨455063443822749775613185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 606751258430333034150913 455063443822749775613185)
                ·
                  refine ⟨341297582867062331709889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 455063443822749775613185 341297582867062331709889)
                  ·
                    rfl

theorem cell20_747759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 4, 2, 2].length) (baseStart_747759 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_747759 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_747759 prefixEnd_747759 := by exact prefixLift 747759
  have htrace : WordTrace (prefixWord ++ tailWord_747759) baseStart_747759 baseEnd_747759 := by
    simpa [prefixWord, tailWord_747759, baseEnd_747759] using wordTrace_append hprefix tailTrace_747759
  have hstable : (prefixWord ++ tailWord_747759).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747759).length < 2 ^ (prefixWord ++ tailWord_747759).sum := by decide
  have hdescent : baseEnd_747759 < baseStart_747759 := by decide
  rcases family_descends (prefixWord ++ tailWord_747759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747770 : List Nat := [3, 1, 1, 1, 1, 5, 3, 5]
def baseStart_747770 : Nat := 118140960795 + 747770 * 2 ^ 59
def prefixEnd_747770 : Nat := 4983230072969 + 3 ^ 40 * 747770 * 2
def baseEnd_747770 : Nat := 113767534522265060781059

theorem tailTrace_747770 : CollatzResearch.WordTrace tailWord_747770 prefixEnd_747770 113767534522265060781059 := by
  unfold tailWord_747770
  simp only [CollatzResearch.WordTrace]
  refine ⟨6818353125241118448420191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18182275000642982529120509 6818353125241118448420191)
  ·
    refine ⟨10227529687861677672630287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6818353125241118448420191 10227529687861677672630287)
    ·
      refine ⟨15341294531792516508945431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10227529687861677672630287 15341294531792516508945431)
      ·
        refine ⟨23011941797688774763418147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15341294531792516508945431 23011941797688774763418147)
        ·
          refine ⟨34517912696533162145127221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23011941797688774763418147 34517912696533162145127221)
          ·
            refine ⟨3236054315299983951105677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34517912696533162145127221 3236054315299983951105677)
            ·
              refine ⟨1213520368237493981664629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3236054315299983951105677 1213520368237493981664629)
              ·
                refine ⟨113767534522265060781059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1213520368237493981664629 113767534522265060781059)
                ·
                  rfl

theorem cell20_747770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 3, 5].length) (baseStart_747770 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_747770 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_747770 prefixEnd_747770 := by exact prefixLift 747770
  have htrace : WordTrace (prefixWord ++ tailWord_747770) baseStart_747770 baseEnd_747770 := by
    simpa [prefixWord, tailWord_747770, baseEnd_747770] using wordTrace_append hprefix tailTrace_747770
  have hstable : (prefixWord ++ tailWord_747770).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747770).length < 2 ^ (prefixWord ++ tailWord_747770).sum := by decide
  have hdescent : baseEnd_747770 < baseStart_747770 := by decide
  rcases family_descends (prefixWord ++ tailWord_747770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747780 : List Nat := [2, 3, 2, 2, 3, 1, 1, 2, 4]
def baseStart_747780 : Nat := 118140960795 + 747780 * 2 ^ 59
def prefixEnd_747780 : Nat := 4983230072969 + 3 ^ 40 * 747780 * 2
def baseEnd_747780 : Nat := 341307167839279592009803

theorem tailTrace_747780 : CollatzResearch.WordTrace tailWord_747780 prefixEnd_747780 341307167839279592009803 := by
  unfold tailWord_747780
  simp only [CollatzResearch.WordTrace]
  refine ⟨13636888615464122750772397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18182518153952163667696529 13636888615464122750772397)
  ·
    refine ⟨5113833230799046031539649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13636888615464122750772397 5113833230799046031539649)
    ·
      refine ⟨3835374923099284523654737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5113833230799046031539649 3835374923099284523654737)
      ·
        refine ⟨2876531192324463392741053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3835374923099284523654737 2876531192324463392741053)
        ·
          refine ⟨1078699197121673772277895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2876531192324463392741053 1078699197121673772277895)
          ·
            refine ⟨1618048795682510658416843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1078699197121673772277895 1618048795682510658416843)
            ·
              refine ⟨2427073193523765987625265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1618048795682510658416843 2427073193523765987625265)
              ·
                refine ⟨1820304895142824490718949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2427073193523765987625265 1820304895142824490718949)
                ·
                  refine ⟨341307167839279592009803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1820304895142824490718949 341307167839279592009803)
                  ·
                    rfl

theorem cell20_747780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 2, 4].length) (baseStart_747780 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_747780 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_747780 prefixEnd_747780 := by exact prefixLift 747780
  have htrace : WordTrace (prefixWord ++ tailWord_747780) baseStart_747780 baseEnd_747780 := by
    simpa [prefixWord, tailWord_747780, baseEnd_747780] using wordTrace_append hprefix tailTrace_747780
  have hstable : (prefixWord ++ tailWord_747780).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747780).length < 2 ^ (prefixWord ++ tailWord_747780).sum := by decide
  have hdescent : baseEnd_747780 < baseStart_747780 := by decide
  rcases family_descends (prefixWord ++ tailWord_747780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747791 : List Nat := [1, 1, 2, 1, 1, 1, 3, 10]
def baseStart_747791 : Nat := 118140960795 + 747791 * 2 ^ 59
def prefixEnd_747791 : Nat := 4983230072969 + 3 ^ 40 * 747791 * 2
def baseEnd_747791 : Nat := 113770729513004147547697

theorem tailTrace_747791 : CollatzResearch.WordTrace tailWord_747791 prefixEnd_747791 113770729513004147547697 := by
  unfold tailWord_747791
  simp only [CollatzResearch.WordTrace]
  refine ⟨27274178433888394380195227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18182785622592262920130151 27274178433888394380195227)
  ·
    refine ⟨40911267650832591570292841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27274178433888394380195227 40911267650832591570292841)
    ·
      refine ⟨30683450738124443677719631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40911267650832591570292841 30683450738124443677719631)
      ·
        refine ⟨46025176107186665516579447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30683450738124443677719631 46025176107186665516579447)
        ·
          refine ⟨69037764160779998274869171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46025176107186665516579447 69037764160779998274869171)
          ·
            refine ⟨103556646241169997412303757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69037764160779998274869171 103556646241169997412303757)
            ·
              refine ⟨38833742340438749029613909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103556646241169997412303757 38833742340438749029613909)
              ·
                refine ⟨113770729513004147547697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 38833742340438749029613909 113770729513004147547697)
                ·
                  rfl

theorem cell20_747791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 10].length) (baseStart_747791 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_747791 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_747791 prefixEnd_747791 := by exact prefixLift 747791
  have htrace : WordTrace (prefixWord ++ tailWord_747791) baseStart_747791 baseEnd_747791 := by
    simpa [prefixWord, tailWord_747791, baseEnd_747791] using wordTrace_append hprefix tailTrace_747791
  have hstable : (prefixWord ++ tailWord_747791).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747791).length < 2 ^ (prefixWord ++ tailWord_747791).sum := by decide
  have hdescent : baseEnd_747791 < baseStart_747791 := by decide
  rcases family_descends (prefixWord ++ tailWord_747791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747808 : List Nat := [2, 1, 1, 5, 2, 2, 7]
def baseStart_747808 : Nat := 118140960795 + 747808 * 2 ^ 59
def prefixEnd_747808 : Nat := 4983230072969 + 3 ^ 40 * 747808 * 2
def baseEnd_747808 : Nat := 37924438644692882119595

theorem tailTrace_747808 : CollatzResearch.WordTrace tailWord_747808 prefixEnd_747808 37924438644692882119595 := by
  unfold tailWord_747808
  simp only [CollatzResearch.WordTrace]
  refine ⟨13637399237413403141782039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18183198983217870855709385 13637399237413403141782039)
  ·
    refine ⟨20456098856120104712673059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13637399237413403141782039 20456098856120104712673059)
    ·
      refine ⟨30684148284180157069009589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20456098856120104712673059 30684148284180157069009589)
      ·
        refine ⟨2876638901641889725219649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30684148284180157069009589 2876638901641889725219649)
        ·
          refine ⟨2157479176231417293914737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2876638901641889725219649 2157479176231417293914737)
          ·
            refine ⟨1618109382173562970436053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2157479176231417293914737 1618109382173562970436053)
            ·
              refine ⟨37924438644692882119595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1618109382173562970436053 37924438644692882119595)
              ·
                rfl

theorem cell20_747808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 7].length) (baseStart_747808 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_747808 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_747808 prefixEnd_747808 := by exact prefixLift 747808
  have htrace : WordTrace (prefixWord ++ tailWord_747808) baseStart_747808 baseEnd_747808 := by
    simpa [prefixWord, tailWord_747808, baseEnd_747808] using wordTrace_append hprefix tailTrace_747808
  have hstable : (prefixWord ++ tailWord_747808).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747808).length < 2 ^ (prefixWord ++ tailWord_747808).sum := by decide
  have hdescent : baseEnd_747808 < baseStart_747808 := by decide
  rcases family_descends (prefixWord ++ tailWord_747808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747828 : List Nat := [2, 5, 1, 1, 1, 3, 3, 1, 3]
def baseStart_747828 : Nat := 118140960795 + 747828 * 2 ^ 59
def prefixEnd_747828 : Nat := 4983230072969 + 3 ^ 40 * 747828 * 2
def baseEnd_747828 : Nat := 341329076347204758409607

theorem tailTrace_747828 : CollatzResearch.WordTrace tailWord_747828 prefixEnd_747828 341329076347204758409607 := by
  unfold tailWord_747828
  simp only [CollatzResearch.WordTrace]
  refine ⟨13637763967377174849646069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18183685289836233132861425 13637763967377174849646069)
  ·
    refine ⟨1278540371941610142154319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13637763967377174849646069 1278540371941610142154319)
    ·
      refine ⟨1917810557912415213231479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1278540371941610142154319 1917810557912415213231479)
      ·
        refine ⟨2876715836868622819847219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1917810557912415213231479 2876715836868622819847219)
        ·
          refine ⟨4315073755302934229770829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2876715836868622819847219 4315073755302934229770829)
          ·
            refine ⟨1618152658238600336164061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4315073755302934229770829 1618152658238600336164061)
            ·
              refine ⟨606807246839475126061523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1618152658238600336164061 606807246839475126061523)
              ·
                refine ⟨910210870259212689092285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 606807246839475126061523 910210870259212689092285)
                ·
                  refine ⟨341329076347204758409607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 910210870259212689092285 341329076347204758409607)
                  ·
                    rfl

theorem cell20_747828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_747828 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_747828 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_747828 prefixEnd_747828 := by exact prefixLift 747828
  have htrace : WordTrace (prefixWord ++ tailWord_747828) baseStart_747828 baseEnd_747828 := by
    simpa [prefixWord, tailWord_747828, baseEnd_747828] using wordTrace_append hprefix tailTrace_747828
  have hstable : (prefixWord ++ tailWord_747828).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747828).length < 2 ^ (prefixWord ++ tailWord_747828).sum := by decide
  have hdescent : baseEnd_747828 < baseStart_747828 := by decide
  rcases family_descends (prefixWord ++ tailWord_747828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747856 : List Nat := [2, 1, 1, 1, 1, 6, 3, 3, 2]
def baseStart_747856 : Nat := 118140960795 + 747856 * 2 ^ 59
def prefixEnd_747856 : Nat := 4983230072969 + 3 ^ 40 * 747856 * 2
def baseEnd_747856 : Nat := 341341856310161105476159

theorem tailTrace_747856 : CollatzResearch.WordTrace tailWord_747856 prefixEnd_747856 341341856310161105476159 := by
  unfold tailWord_747856
  simp only [CollatzResearch.WordTrace]
  refine ⟨13638274589326455240655711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18184366119101940320874281 13638274589326455240655711)
  ·
    refine ⟨20457411883989682860983567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13638274589326455240655711 20457411883989682860983567)
    ·
      refine ⟨30686117825984524291475351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20457411883989682860983567 30686117825984524291475351)
      ·
        refine ⟨46029176738976786437213027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30686117825984524291475351 46029176738976786437213027)
        ·
          refine ⟨69043765108465179655819541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46029176738976786437213027 69043765108465179655819541)
          ·
            refine ⟨3236426489459305296366541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 69043765108465179655819541 3236426489459305296366541)
            ·
              refine ⟨1213659933547239486137453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3236426489459305296366541 1213659933547239486137453)
              ·
                refine ⟨455122475080214807301545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1213659933547239486137453 455122475080214807301545)
                ·
                  refine ⟨341341856310161105476159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 455122475080214807301545 341341856310161105476159)
                  ·
                    rfl

theorem cell20_747856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 3, 3, 2].length) (baseStart_747856 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_747856 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_747856 prefixEnd_747856 := by exact prefixLift 747856
  have htrace : WordTrace (prefixWord ++ tailWord_747856) baseStart_747856 baseEnd_747856 := by
    simpa [prefixWord, tailWord_747856, baseEnd_747856] using wordTrace_append hprefix tailTrace_747856
  have hstable : (prefixWord ++ tailWord_747856).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747856).length < 2 ^ (prefixWord ++ tailWord_747856).sum := by decide
  have hdescent : baseEnd_747856 < baseStart_747856 := by decide
  rcases family_descends (prefixWord ++ tailWord_747856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747877 : List Nat := [1, 3, 1, 3, 1, 3, 3, 1, 4]
def baseStart_747877 : Nat := 118140960795 + 747877 * 2 ^ 59
def prefixEnd_747877 : Nat := 4983230072969 + 3 ^ 40 * 747877 * 2
def baseEnd_747877 : Nat := 341351441282378365776073

theorem tailTrace_747877 : CollatzResearch.WordTrace tailWord_747877 prefixEnd_747877 341351441282378365776073 := by
  unfold tailWord_747877
  simp only [CollatzResearch.WordTrace]
  refine ⟨27277315111576831067825885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18184876741051220711883923 27277315111576831067825885)
  ·
    refine ⟨10228993166841311650434707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27277315111576831067825885 10228993166841311650434707)
    ·
      refine ⟨15343489750261967475652061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10228993166841311650434707 15343489750261967475652061)
      ·
        refine ⟨5753808656348237803369523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15343489750261967475652061 5753808656348237803369523)
        ·
          refine ⟨8630712984522356705054285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5753808656348237803369523 8630712984522356705054285)
          ·
            refine ⟨3236517369195883764395357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8630712984522356705054285 3236517369195883764395357)
            ·
              refine ⟨1213694013448456411648259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3236517369195883764395357 1213694013448456411648259)
              ·
                refine ⟨1820541020172684617472389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1213694013448456411648259 1820541020172684617472389)
                ·
                  refine ⟨341351441282378365776073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1820541020172684617472389 341351441282378365776073)
                  ·
                    rfl

theorem cell20_747877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 3, 1, 4].length) (baseStart_747877 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_747877 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_747877 prefixEnd_747877 := by exact prefixLift 747877
  have htrace : WordTrace (prefixWord ++ tailWord_747877) baseStart_747877 baseEnd_747877 := by
    simpa [prefixWord, tailWord_747877, baseEnd_747877] using wordTrace_append hprefix tailTrace_747877
  have hstable : (prefixWord ++ tailWord_747877).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747877).length < 2 ^ (prefixWord ++ tailWord_747877).sum := by decide
  have hdescent : baseEnd_747877 < baseStart_747877 := by decide
  rcases family_descends (prefixWord ++ tailWord_747877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747891 : List Nat := [1, 1, 1, 2, 2, 1, 2, 7, 3]
def baseStart_747891 : Nat := 118140960795 + 747891 * 2 ^ 59
def prefixEnd_747891 : Nat := 4983230072969 + 3 ^ 40 * 747891 * 2
def baseEnd_747891 : Nat := 341357831263856539309349

theorem tailTrace_747891 : CollatzResearch.WordTrace tailWord_747891 prefixEnd_747891 341357831263856539309349 := by
  unfold tailWord_747891
  simp only [CollatzResearch.WordTrace]
  refine ⟨27277825733526111458835527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18185217155684074305890351 27277825733526111458835527)
  ·
    refine ⟨40916738600289167188253291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27277825733526111458835527 40916738600289167188253291)
    ·
      refine ⟨61375107900433750782379937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40916738600289167188253291 61375107900433750782379937)
      ·
        refine ⟨46031330925325313086784953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61375107900433750782379937 46031330925325313086784953)
        ·
          refine ⟨34523498193993984815088715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46031330925325313086784953 34523498193993984815088715)
          ·
            refine ⟨51785247290990977222633073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34523498193993984815088715 51785247290990977222633073)
            ·
              refine ⟨38838935468243232916974805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51785247290990977222633073 38838935468243232916974805)
              ·
                refine ⟨910287550036950771491597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 38838935468243232916974805 910287550036950771491597)
                ·
                  refine ⟨341357831263856539309349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 910287550036950771491597 341357831263856539309349)
                  ·
                    rfl

theorem cell20_747891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 7, 3].length) (baseStart_747891 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_747891 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_747891 prefixEnd_747891 := by exact prefixLift 747891
  have htrace : WordTrace (prefixWord ++ tailWord_747891) baseStart_747891 baseEnd_747891 := by
    simpa [prefixWord, tailWord_747891, baseEnd_747891] using wordTrace_append hprefix tailTrace_747891
  have hstable : (prefixWord ++ tailWord_747891).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747891).length < 2 ^ (prefixWord ++ tailWord_747891).sum := by decide
  have hdescent : baseEnd_747891 < baseStart_747891 := by decide
  rcases family_descends (prefixWord ++ tailWord_747891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747928 : List Nat := [2, 1, 2, 5, 1, 3, 2, 2, 2]
def baseStart_747928 : Nat := 118140960795 + 747928 * 2 ^ 59
def prefixEnd_747928 : Nat := 4983230072969 + 3 ^ 40 * 747928 * 2
def baseEnd_747928 : Nat := 341374719072048855075865

theorem tailTrace_747928 : CollatzResearch.WordTrace tailWord_747928 prefixEnd_747928 341374719072048855075865 := by
  unfold tailWord_747928
  simp only [CollatzResearch.WordTrace]
  refine ⟨13639587617196033388966219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18186116822928044518621625 13639587617196033388966219)
  ·
    refine ⟨20459381425794050083449329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13639587617196033388966219 20459381425794050083449329)
    ·
      refine ⟨15344536069345537562586997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20459381425794050083449329 15344536069345537562586997)
      ·
        refine ⟨1438550256501144146492531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15344536069345537562586997 1438550256501144146492531)
        ·
          refine ⟨2157825384751716219738797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1438550256501144146492531 2157825384751716219738797)
          ·
            refine ⟨809184519281893582402049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2157825384751716219738797 809184519281893582402049)
            ·
              refine ⟨606888389461420186801537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 809184519281893582402049 606888389461420186801537)
              ·
                refine ⟨455166292096065140101153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 606888389461420186801537 455166292096065140101153)
                ·
                  refine ⟨341374719072048855075865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 455166292096065140101153 341374719072048855075865)
                  ·
                    rfl

theorem cell20_747928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 2, 2, 2].length) (baseStart_747928 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_747928 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_747928 prefixEnd_747928 := by exact prefixLift 747928
  have htrace : WordTrace (prefixWord ++ tailWord_747928) baseStart_747928 baseEnd_747928 := by
    simpa [prefixWord, tailWord_747928, baseEnd_747928] using wordTrace_append hprefix tailTrace_747928
  have hstable : (prefixWord ++ tailWord_747928).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747928).length < 2 ^ (prefixWord ++ tailWord_747928).sum := by decide
  have hdescent : baseEnd_747928 < baseStart_747928 := by decide
  rcases family_descends (prefixWord ++ tailWord_747928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747953 : List Nat := [1, 2, 2, 4, 1, 3, 1, 2, 4]
def baseStart_747953 : Nat := 118140960795 + 747953 * 2 ^ 59
def prefixEnd_747953 : Nat := 4983230072969 + 3 ^ 40 * 747953 * 2
def baseEnd_747953 : Nat := 341386129753259879242429

theorem tailTrace_747953 : CollatzResearch.WordTrace tailWord_747953 prefixEnd_747953 341386129753259879242429 := by
  unfold tailWord_747953
  simp only [CollatzResearch.WordTrace]
  refine ⟨27280087059301496047592513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18186724706200997365061675 27280087059301496047592513)
  ·
    refine ⟨20460065294476122035694385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27280087059301496047592513 20460065294476122035694385)
    ·
      refine ⟨15345048970857091526770789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20460065294476122035694385 15345048970857091526770789)
      ·
        refine ⟨2877196682035704661269523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15345048970857091526770789 2877196682035704661269523)
        ·
          refine ⟨4315795023053556991904285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2877196682035704661269523 4315795023053556991904285)
          ·
            refine ⟨1618423133645083871964107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4315795023053556991904285 1618423133645083871964107)
            ·
              refine ⟨2427634700467625807946161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1618423133645083871964107 2427634700467625807946161)
              ·
                refine ⟨1820726025350719355959621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2427634700467625807946161 1820726025350719355959621)
                ·
                  refine ⟨341386129753259879242429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1820726025350719355959621 341386129753259879242429)
                  ·
                    rfl

theorem cell20_747953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 2, 4].length) (baseStart_747953 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_747953 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_747953 prefixEnd_747953 := by exact prefixLift 747953
  have htrace : WordTrace (prefixWord ++ tailWord_747953) baseStart_747953 baseEnd_747953 := by
    simpa [prefixWord, tailWord_747953, baseEnd_747953] using wordTrace_append hprefix tailTrace_747953
  have hstable : (prefixWord ++ tailWord_747953).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747953).length < 2 ^ (prefixWord ++ tailWord_747953).sum := by decide
  have hdescent : baseEnd_747953 < baseStart_747953 := by decide
  rcases family_descends (prefixWord ++ tailWord_747953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747980 : List Nat := [2, 2, 1, 4, 4, 1, 1, 2, 3]
def baseStart_747980 : Nat := 118140960795 + 747980 * 2 ^ 59
def prefixEnd_747980 : Nat := 4983230072969 + 3 ^ 40 * 747980 * 2
def baseEnd_747980 : Nat := 341398453288967785342319

theorem tailTrace_747980 : CollatzResearch.WordTrace tailWord_747980 prefixEnd_747980 341398453288967785342319 := by
  unfold tailWord_747980
  simp only [CollatzResearch.WordTrace]
  refine ⟨13640535915101839829412697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18187381220135786439216929 13640535915101839829412697)
  ·
    refine ⟨10230401936326379872059523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13640535915101839829412697 10230401936326379872059523)
    ·
      refine ⟨15345602904489569808089285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10230401936326379872059523 15345602904489569808089285)
      ·
        refine ⟨2877300544591794339016741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15345602904489569808089285 2877300544591794339016741)
        ·
          refine ⟨539493852110961438565639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2877300544591794339016741 539493852110961438565639)
          ·
            refine ⟨809240778166442157848459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 539493852110961438565639 809240778166442157848459)
            ·
              refine ⟨1213861167249663236772689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 809240778166442157848459 1213861167249663236772689)
              ·
                refine ⟨910395875437247427579517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1213861167249663236772689 910395875437247427579517)
                ·
                  refine ⟨341398453288967785342319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 910395875437247427579517 341398453288967785342319)
                  ·
                    rfl

theorem cell20_747980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 1, 2, 3].length) (baseStart_747980 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_747980 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_747980 prefixEnd_747980 := by exact prefixLift 747980
  have htrace : WordTrace (prefixWord ++ tailWord_747980) baseStart_747980 baseEnd_747980 := by
    simpa [prefixWord, tailWord_747980, baseEnd_747980] using wordTrace_append hprefix tailTrace_747980
  have hstable : (prefixWord ++ tailWord_747980).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747980).length < 2 ^ (prefixWord ++ tailWord_747980).sum := by decide
  have hdescent : baseEnd_747980 < baseStart_747980 := by decide
  rcases family_descends (prefixWord ++ tailWord_747980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748012 : List Nat := [2, 2, 1, 1, 2, 1, 3, 4, 4]
def baseStart_748012 : Nat := 118140960795 + 748012 * 2 ^ 59
def prefixEnd_748012 : Nat := 4983230072969 + 3 ^ 40 * 748012 * 2
def baseEnd_748012 : Nat := 341413058960917896275521

theorem tailTrace_748012 : CollatzResearch.WordTrace tailWord_748012 prefixEnd_748012 341413058960917896275521 := by
  unfold tailWord_748012
  simp only [CollatzResearch.WordTrace]
  refine ⟨13641119483043874561995145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18188159310725166082660193 13641119483043874561995145)
  ·
    refine ⟨10230839612282905921496359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13641119483043874561995145 10230839612282905921496359)
    ·
      refine ⟨15346259418424358882244539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10230839612282905921496359 15346259418424358882244539)
      ·
        refine ⟨23019389127636538323366809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15346259418424358882244539 23019389127636538323366809)
        ·
          refine ⟨17264541845727403742525107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23019389127636538323366809 17264541845727403742525107)
          ·
            refine ⟨25896812768591105613787661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17264541845727403742525107 25896812768591105613787661)
            ·
              refine ⟨9711304788221664605170373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25896812768591105613787661 9711304788221664605170373)
              ·
                refine ⟨1820869647791562113469445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9711304788221664605170373 1820869647791562113469445)
                ·
                  refine ⟨341413058960917896275521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1820869647791562113469445 341413058960917896275521)
                  ·
                    rfl

theorem cell20_748012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 4].length) (baseStart_748012 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_748012 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_748012 prefixEnd_748012 := by exact prefixLift 748012
  have htrace : WordTrace (prefixWord ++ tailWord_748012) baseStart_748012 baseEnd_748012 := by
    simpa [prefixWord, tailWord_748012, baseEnd_748012] using wordTrace_append hprefix tailTrace_748012
  have hstable : (prefixWord ++ tailWord_748012).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748012).length < 2 ^ (prefixWord ++ tailWord_748012).sum := by decide
  have hdescent : baseEnd_748012 < baseStart_748012 := by decide
  rcases family_descends (prefixWord ++ tailWord_748012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748019 : List Nat := [1, 1, 1, 2, 2, 2, 5, 6]
def baseStart_748019 : Nat := 118140960795 + 748019 * 2 ^ 59
def prefixEnd_748019 : Nat := 4983230072969 + 3 ^ 40 * 748019 * 2
def baseEnd_748019 : Nat := 113805417983885661014053

theorem tailTrace_748019 : CollatzResearch.WordTrace tailWord_748019 prefixEnd_748019 113805417983885661014053 := by
  unfold tailWord_748019
  simp only [CollatzResearch.WordTrace]
  refine ⟨27282494277062389319495111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18188329518041592879663407 27282494277062389319495111)
  ·
    refine ⟨40923741415593583979242667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27282494277062389319495111 40923741415593583979242667)
    ·
      refine ⟨61385612123390375968864001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40923741415593583979242667 61385612123390375968864001)
      ·
        refine ⟨46039209092542781976648001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61385612123390375968864001 46039209092542781976648001)
        ·
          refine ⟨34529406819407086482486001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46039209092542781976648001 34529406819407086482486001)
          ·
            refine ⟨25897055114555314861864501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34529406819407086482486001 25897055114555314861864501)
            ·
              refine ⟨2427848916989560768299797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25897055114555314861864501 2427848916989560768299797)
              ·
                refine ⟨113805417983885661014053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2427848916989560768299797 113805417983885661014053)
                ·
                  rfl

theorem cell20_748019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 6].length) (baseStart_748019 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_748019 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_748019 prefixEnd_748019 := by exact prefixLift 748019
  have htrace : WordTrace (prefixWord ++ tailWord_748019) baseStart_748019 baseEnd_748019 := by
    simpa [prefixWord, tailWord_748019, baseEnd_748019] using wordTrace_append hprefix tailTrace_748019
  have hstable : (prefixWord ++ tailWord_748019).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748019).length < 2 ^ (prefixWord ++ tailWord_748019).sum := by decide
  have hdescent : baseEnd_748019 < baseStart_748019 := by decide
  rcases family_descends (prefixWord ++ tailWord_748019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748021 : List Nat := [1, 3, 5, 1, 3, 1, 1, 3, 2]
def baseStart_748021 : Nat := 118140960795 + 748021 * 2 ^ 59
def prefixEnd_748021 : Nat := 4983230072969 + 3 ^ 40 * 748021 * 2
def baseEnd_748021 : Nat := 341417166806153864975485

theorem tailTrace_748021 : CollatzResearch.WordTrace tailWord_748021 prefixEnd_748021 341417166806153864975485 := by
  unfold tailWord_748021
  simp only [CollatzResearch.WordTrace]
  refine ⟨27282567223055143661067917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18188378148703429107378611 27282567223055143661067917)
  ·
    refine ⟨10230962708645678872900469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27282567223055143661067917 10230962708645678872900469)
    ·
      refine ⟨959152753935532394334419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10230962708645678872900469 959152753935532394334419)
      ·
        refine ⟨1438729130903298591501629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 959152753935532394334419 1438729130903298591501629)
        ·
          refine ⟨539523424088736971813111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1438729130903298591501629 539523424088736971813111)
          ·
            refine ⟨809285136133105457719667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 539523424088736971813111 809285136133105457719667)
            ·
              refine ⟨1213927704199658186579501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 809285136133105457719667 1213927704199658186579501)
              ·
                refine ⟨455222889074871819967313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1213927704199658186579501 455222889074871819967313)
                ·
                  refine ⟨341417166806153864975485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 455222889074871819967313 341417166806153864975485)
                  ·
                    rfl

theorem cell20_748021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 1, 3, 2].length) (baseStart_748021 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_748021 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_748021 prefixEnd_748021 := by exact prefixLift 748021
  have htrace : WordTrace (prefixWord ++ tailWord_748021) baseStart_748021 baseEnd_748021 := by
    simpa [prefixWord, tailWord_748021, baseEnd_748021] using wordTrace_append hprefix tailTrace_748021
  have hstable : (prefixWord ++ tailWord_748021).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748021).length < 2 ^ (prefixWord ++ tailWord_748021).sum := by decide
  have hdescent : baseEnd_748021 < baseStart_748021 := by decide
  rcases family_descends (prefixWord ++ tailWord_748021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748036 : List Nat := [2, 3, 2, 3, 1, 1, 8]
def baseStart_748036 : Nat := 118140960795 + 748036 * 2 ^ 59
def prefixEnd_748036 : Nat := 4983230072969 + 3 ^ 40 * 748036 * 2
def baseEnd_748036 : Nat := 37936001468320053275047

theorem tailTrace_748036 : CollatzResearch.WordTrace tailWord_748036 prefixEnd_748036 37936001468320053275047 := by
  unfold tailWord_748036
  simp only [CollatzResearch.WordTrace]
  refine ⟨13641557159000400611431981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18188742878667200815242641 13641557159000400611431981)
  ·
    refine ⟨5115583934625150229286993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13641557159000400611431981 5115583934625150229286993)
    ·
      refine ⟨3836687950968862671965245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5115583934625150229286993 3836687950968862671965245)
      ·
        refine ⟨1438757981613323501986967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3836687950968862671965245 1438757981613323501986967)
        ·
          refine ⟨2158136972419985252980451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1438757981613323501986967 2158136972419985252980451)
          ·
            refine ⟨3237205458629977879470677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2158136972419985252980451 3237205458629977879470677)
            ·
              refine ⟨37936001468320053275047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3237205458629977879470677 37936001468320053275047)
              ·
                rfl

theorem cell20_748036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 8].length) (baseStart_748036 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_748036 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_748036 prefixEnd_748036 := by exact prefixLift 748036
  have htrace : WordTrace (prefixWord ++ tailWord_748036) baseStart_748036 baseEnd_748036 := by
    simpa [prefixWord, tailWord_748036, baseEnd_748036] using wordTrace_append hprefix tailTrace_748036
  have hstable : (prefixWord ++ tailWord_748036).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748036).length < 2 ^ (prefixWord ++ tailWord_748036).sum := by decide
  have hdescent : baseEnd_748036 < baseStart_748036 := by decide
  rcases family_descends (prefixWord ++ tailWord_748036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748038 : List Nat := [6, 2, 1, 1, 1, 2, 3, 2, 2]
def baseStart_748038 : Nat := 118140960795 + 748038 * 2 ^ 59
def prefixEnd_748038 : Nat := 4983230072969 + 3 ^ 40 * 748038 * 2
def baseEnd_748038 : Nat := 341424926069377361408749

theorem tailTrace_748038 : CollatzResearch.WordTrace tailWord_748038 prefixEnd_748038 341424926069377361408749 := by
  unfold tailWord_748038
  simp only [CollatzResearch.WordTrace]
  refine ⟨852599601999798611388649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 18188791509329037042957845 852599601999798611388649)
  ·
    refine ⟨639449701499848958541487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 852599601999798611388649 639449701499848958541487)
    ·
      refine ⟨959174552249773437812231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 639449701499848958541487 959174552249773437812231)
      ·
        refine ⟨1438761828374660156718347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 959174552249773437812231 1438761828374660156718347)
        ·
          refine ⟨2158142742561990235077521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1438761828374660156718347 2158142742561990235077521)
          ·
            refine ⟨1618607056921492676308141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2158142742561990235077521 1618607056921492676308141)
            ·
              refine ⟨606977646345559753615553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1618607056921492676308141 606977646345559753615553)
              ·
                refine ⟨455233234759169815211665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 606977646345559753615553 455233234759169815211665)
                ·
                  refine ⟨341424926069377361408749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 455233234759169815211665 341424926069377361408749)
                  ·
                    rfl

theorem cell20_748038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_748038 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_748038 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_748038 prefixEnd_748038 := by exact prefixLift 748038
  have htrace : WordTrace (prefixWord ++ tailWord_748038) baseStart_748038 baseEnd_748038 := by
    simpa [prefixWord, tailWord_748038, baseEnd_748038] using wordTrace_append hprefix tailTrace_748038
  have hstable : (prefixWord ++ tailWord_748038).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748038).length < 2 ^ (prefixWord ++ tailWord_748038).sum := by decide
  have hdescent : baseEnd_748038 < baseStart_748038 := by decide
  rcases family_descends (prefixWord ++ tailWord_748038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748043 : List Nat := [1, 1, 1, 1, 7, 1, 2, 1, 5]
def baseStart_748043 : Nat := 118140960795 + 748043 * 2 ^ 59
def prefixEnd_748043 : Nat := 4983230072969 + 3 ^ 40 * 748043 * 2
def baseEnd_748043 : Nat := 341427208205619566242061

theorem tailTrace_748043 : CollatzResearch.WordTrace tailWord_748043 prefixEnd_748043 341427208205619566242061 := by
  unfold tailWord_748043
  simp only [CollatzResearch.WordTrace]
  refine ⟨27283369628975441418368783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18188913085983627612245855 27283369628975441418368783)
  ·
    refine ⟨40925054443463162127553175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27283369628975441418368783 40925054443463162127553175)
    ·
      refine ⟨61387581665194743191329763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40925054443463162127553175 61387581665194743191329763)
      ·
        refine ⟨92081372497792114786994645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61387581665194743191329763 92081372497792114786994645)
        ·
          refine ⟨2158157167917002690320187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 92081372497792114786994645 2158157167917002690320187)
          ·
            refine ⟨3237235751875504035480281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2158157167917002690320187 3237235751875504035480281)
            ·
              refine ⟨2427926813906628026610211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3237235751875504035480281 2427926813906628026610211)
              ·
                refine ⟨3641890220859942039915317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2427926813906628026610211 3641890220859942039915317)
                ·
                  refine ⟨341427208205619566242061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3641890220859942039915317 341427208205619566242061)
                  ·
                    rfl

theorem cell20_748043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 1, 5].length) (baseStart_748043 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_748043 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_748043 prefixEnd_748043 := by exact prefixLift 748043
  have htrace : WordTrace (prefixWord ++ tailWord_748043) baseStart_748043 baseEnd_748043 := by
    simpa [prefixWord, tailWord_748043, baseEnd_748043] using wordTrace_append hprefix tailTrace_748043
  have hstable : (prefixWord ++ tailWord_748043).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748043).length < 2 ^ (prefixWord ++ tailWord_748043).sum := by decide
  have hdescent : baseEnd_748043 < baseStart_748043 := by decide
  rcases family_descends (prefixWord ++ tailWord_748043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748046 : List Nat := [4, 1, 1, 2, 3, 3, 1, 1, 4]
def baseStart_748046 : Nat := 118140960795 + 748046 * 2 ^ 59
def prefixEnd_748046 : Nat := 4983230072969 + 3 ^ 40 * 748046 * 2
def baseEnd_748046 : Nat := 341428577487364889142049

theorem tailTrace_748046 : CollatzResearch.WordTrace tailWord_748046 prefixEnd_748046 341428577487364889142049 := by
  unfold tailWord_748046
  simp only [CollatzResearch.WordTrace]
  refine ⟨3410434880995571616340999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18188986031976381953818661 3410434880995571616340999)
  ·
    refine ⟨5115652321493357424511499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3410434880995571616340999 5115652321493357424511499)
    ·
      refine ⟨7673478482240036136767249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5115652321493357424511499 7673478482240036136767249)
      ·
        refine ⟨5755108861680027102575437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7673478482240036136767249 5755108861680027102575437)
        ·
          refine ⟨2158165823130010163465789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5755108861680027102575437 2158165823130010163465789)
          ·
            refine ⟨809312183673753811299671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2158165823130010163465789 809312183673753811299671)
            ·
              refine ⟨1213968275510630716949507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 809312183673753811299671 1213968275510630716949507)
              ·
                refine ⟨1820952413265946075424261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1213968275510630716949507 1820952413265946075424261)
                ·
                  refine ⟨341428577487364889142049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1820952413265946075424261 341428577487364889142049)
                  ·
                    rfl

theorem cell20_748046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 1, 1, 4].length) (baseStart_748046 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_748046 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_748046 prefixEnd_748046 := by exact prefixLift 748046
  have htrace : WordTrace (prefixWord ++ tailWord_748046) baseStart_748046 baseEnd_748046 := by
    simpa [prefixWord, tailWord_748046, baseEnd_748046] using wordTrace_append hprefix tailTrace_748046
  have hstable : (prefixWord ++ tailWord_748046).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748046).length < 2 ^ (prefixWord ++ tailWord_748046).sum := by decide
  have hdescent : baseEnd_748046 < baseStart_748046 := by decide
  rcases family_descends (prefixWord ++ tailWord_748046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748060 : List Nat := [2, 2, 3, 1, 2, 3, 1, 3, 3]
def baseStart_748060 : Nat := 118140960795 + 748060 * 2 ^ 59
def prefixEnd_748060 : Nat := 4983230072969 + 3 ^ 40 * 748060 * 2
def baseEnd_748060 : Nat := 341434967468843062675325

theorem tailTrace_748060 : CollatzResearch.WordTrace tailWord_748060 prefixEnd_748060 341434967468843062675325 := by
  unfold tailWord_748060
  simp only [CollatzResearch.WordTrace]
  refine ⟨13641994834956926660868817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18189326446609235547825089 13641994834956926660868817)
  ·
    refine ⟨10231496126217694995651613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13641994834956926660868817 10231496126217694995651613)
    ·
      refine ⟨3836811047331635623369355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10231496126217694995651613 3836811047331635623369355)
      ·
        refine ⟨5755216570997453435054033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3836811047331635623369355 5755216570997453435054033)
        ·
          refine ⟨4316412428248090076290525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5755216570997453435054033 4316412428248090076290525)
          ·
            refine ⟨1618654660593033778608947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4316412428248090076290525 1618654660593033778608947)
            ·
              refine ⟨2427981990889550667913421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1618654660593033778608947 2427981990889550667913421)
              ·
                refine ⟨910493246583581500467533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2427981990889550667913421 910493246583581500467533)
                ·
                  refine ⟨341434967468843062675325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 910493246583581500467533 341434967468843062675325)
                  ·
                    rfl

theorem cell20_748060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 3, 3].length) (baseStart_748060 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_748060 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_748060 prefixEnd_748060 := by exact prefixLift 748060
  have htrace : WordTrace (prefixWord ++ tailWord_748060) baseStart_748060 baseEnd_748060 := by
    simpa [prefixWord, tailWord_748060, baseEnd_748060] using wordTrace_append hprefix tailTrace_748060
  have hstable : (prefixWord ++ tailWord_748060).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748060).length < 2 ^ (prefixWord ++ tailWord_748060).sum := by decide
  have hdescent : baseEnd_748060 < baseStart_748060 := by decide
  rcases family_descends (prefixWord ++ tailWord_748060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748074 : List Nat := [3, 1, 4, 1, 1, 2, 2, 6]
def baseStart_748074 : Nat := 118140960795 + 748074 * 2 ^ 59
def prefixEnd_748074 : Nat := 4983230072969 + 3 ^ 40 * 748074 * 2
def baseEnd_748074 : Nat := 113813785816773745402867

theorem tailTrace_748074 : CollatzResearch.WordTrace tailWord_748074 prefixEnd_748074 113813785816773745402867 := by
  unfold tailWord_748074
  simp only [CollatzResearch.WordTrace]
  refine ⟨6821125072965783428186819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18189666861242089141831517 6821125072965783428186819)
  ·
    refine ⟨10231687609448675142280229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6821125072965783428186819 10231687609448675142280229)
    ·
      refine ⟨1918441426771626589177543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10231687609448675142280229 1918441426771626589177543)
      ·
        refine ⟨2877662140157439883766315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1918441426771626589177543 2877662140157439883766315)
        ·
          refine ⟨4316493210236159825649473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2877662140157439883766315 4316493210236159825649473)
          ·
            refine ⟨3237369907677119869237105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4316493210236159825649473 3237369907677119869237105)
            ·
              refine ⟨2428027430757839901927829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3237369907677119869237105 2428027430757839901927829)
              ·
                refine ⟨113813785816773745402867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2428027430757839901927829 113813785816773745402867)
                ·
                  rfl

theorem cell20_748074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 6].length) (baseStart_748074 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_748074 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_748074 prefixEnd_748074 := by exact prefixLift 748074
  have htrace : WordTrace (prefixWord ++ tailWord_748074) baseStart_748074 baseEnd_748074 := by
    simpa [prefixWord, tailWord_748074, baseEnd_748074] using wordTrace_append hprefix tailTrace_748074
  have hstable : (prefixWord ++ tailWord_748074).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748074).length < 2 ^ (prefixWord ++ tailWord_748074).sum := by decide
  have hdescent : baseEnd_748074 < baseStart_748074 := by decide
  rcases family_descends (prefixWord ++ tailWord_748074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748094 : List Nat := [4, 2, 1, 4, 1, 1, 2, 2, 3]
def baseStart_748094 : Nat := 118140960795 + 748094 * 2 ^ 59
def prefixEnd_748094 : Nat := 4983230072969 + 3 ^ 40 * 748094 * 2
def baseEnd_748094 : Nat := 341450485995290055541853

theorem tailTrace_748094 : CollatzResearch.WordTrace tailWord_748094 prefixEnd_748094 341450485995290055541853 := by
  unfold tailWord_748094
  simp only [CollatzResearch.WordTrace]
  refine ⟨3410653718973834641059417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18190153167860451418983557 3410653718973834641059417)
  ·
    refine ⟨2557990289230375980794563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3410653718973834641059417 2557990289230375980794563)
    ·
      refine ⟨3836985433845563971191845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2557990289230375980794563 3836985433845563971191845)
      ·
        refine ⟨719434768846043244598471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3836985433845563971191845 719434768846043244598471)
        ·
          refine ⟨1079152153269064866897707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 719434768846043244598471 1079152153269064866897707)
          ·
            refine ⟨1618728229903597300346561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1079152153269064866897707 1618728229903597300346561)
            ·
              refine ⟨1214046172427697975259921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1618728229903597300346561 1214046172427697975259921)
              ·
                refine ⟨910534629320773481444941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1214046172427697975259921 910534629320773481444941)
                ·
                  refine ⟨341450485995290055541853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 910534629320773481444941 341450485995290055541853)
                  ·
                    rfl

theorem cell20_748094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 2, 2, 3].length) (baseStart_748094 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_748094 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_748094 prefixEnd_748094 := by exact prefixLift 748094
  have htrace : WordTrace (prefixWord ++ tailWord_748094) baseStart_748094 baseEnd_748094 := by
    simpa [prefixWord, tailWord_748094, baseEnd_748094] using wordTrace_append hprefix tailTrace_748094
  have hstable : (prefixWord ++ tailWord_748094).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748094).length < 2 ^ (prefixWord ++ tailWord_748094).sum := by decide
  have hdescent : baseEnd_748094 < baseStart_748094 := by decide
  rcases family_descends (prefixWord ++ tailWord_748094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748101 : List Nat := [1, 3, 1, 1, 1, 7, 2, 2, 2]
def baseStart_748101 : Nat := 118140960795 + 748101 * 2 ^ 59
def prefixEnd_748101 : Nat := 4983230072969 + 3 ^ 40 * 748101 * 2
def baseEnd_748101 : Nat := 341453680986029142308491

theorem tailTrace_748101 : CollatzResearch.WordTrace tailWord_748101 prefixEnd_748101 341453680986029142308491 := by
  unfold tailWord_748101
  simp only [CollatzResearch.WordTrace]
  refine ⟨27285485062765317323980157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18190323375176878215986771 27285485062765317323980157)
  ·
    refine ⟨10232056898536993996492559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27285485062765317323980157 10232056898536993996492559)
    ·
      refine ⟨15348085347805490994738839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10232056898536993996492559 15348085347805490994738839)
      ·
        refine ⟨23022128021708236492108259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15348085347805490994738839 23022128021708236492108259)
        ·
          refine ⟨34533192032562354738162389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23022128021708236492108259 34533192032562354738162389)
          ·
            refine ⟨809371688263180189175681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 34533192032562354738162389 809371688263180189175681)
            ·
              refine ⟨607028766197385141881761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 809371688263180189175681 607028766197385141881761)
              ·
                refine ⟨455271574648038856411321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 607028766197385141881761 455271574648038856411321)
                ·
                  refine ⟨341453680986029142308491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 455271574648038856411321 341453680986029142308491)
                  ·
                    rfl

theorem cell20_748101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 2, 2, 2].length) (baseStart_748101 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_748101 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_748101 prefixEnd_748101 := by exact prefixLift 748101
  have htrace : WordTrace (prefixWord ++ tailWord_748101) baseStart_748101 baseEnd_748101 := by
    simpa [prefixWord, tailWord_748101, baseEnd_748101] using wordTrace_append hprefix tailTrace_748101
  have hstable : (prefixWord ++ tailWord_748101).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748101).length < 2 ^ (prefixWord ++ tailWord_748101).sum := by decide
  have hdescent : baseEnd_748101 < baseStart_748101 := by decide
  rcases family_descends (prefixWord ++ tailWord_748101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748119 : List Nat := [1, 1, 3, 2, 2, 2, 1, 5, 3]
def baseStart_748119 : Nat := 118140960795 + 748119 * 2 ^ 59
def prefixEnd_748119 : Nat := 4983230072969 + 3 ^ 40 * 748119 * 2
def baseEnd_748119 : Nat := 341461896676501079708417

theorem tailTrace_748119 : CollatzResearch.WordTrace tailWord_748119 prefixEnd_748119 341461896676501079708417 := by
  unfold tailWord_748119
  simp only [CollatzResearch.WordTrace]
  refine ⟨27286141576700106398135411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18190761051133404265423607 27286141576700106398135411)
  ·
    refine ⟨40929212365050159597203117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27286141576700106398135411 40929212365050159597203117)
    ·
      refine ⟨15348454636893809848951169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40929212365050159597203117 15348454636893809848951169)
      ·
        refine ⟨11511340977670357386713377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15348454636893809848951169 11511340977670357386713377)
        ·
          refine ⟨8633505733252768040035033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11511340977670357386713377 8633505733252768040035033)
          ·
            refine ⟨6475129299939576030026275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8633505733252768040035033 6475129299939576030026275)
            ·
              refine ⟨9712693949909364045039413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6475129299939576030026275 9712693949909364045039413)
              ·
                refine ⟨910565057804002879222445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9712693949909364045039413 910565057804002879222445)
                ·
                  refine ⟨341461896676501079708417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 910565057804002879222445 341461896676501079708417)
                  ·
                    rfl

theorem cell20_748119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 5, 3].length) (baseStart_748119 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_748119 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_748119 prefixEnd_748119 := by exact prefixLift 748119
  have htrace : WordTrace (prefixWord ++ tailWord_748119) baseStart_748119 baseEnd_748119 := by
    simpa [prefixWord, tailWord_748119, baseEnd_748119] using wordTrace_append hprefix tailTrace_748119
  have hstable : (prefixWord ++ tailWord_748119).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748119).length < 2 ^ (prefixWord ++ tailWord_748119).sum := by decide
  have hdescent : baseEnd_748119 < baseStart_748119 := by decide
  rcases family_descends (prefixWord ++ tailWord_748119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748143 : List Nat := [1, 1, 2, 1, 3, 2, 3, 5, 2]
def baseStart_748143 : Nat := 118140960795 + 748143 * 2 ^ 59
def prefixEnd_748143 : Nat := 4983230072969 + 3 ^ 40 * 748143 * 2
def baseEnd_748143 : Nat := 341472850930463662908319

theorem tailTrace_748143 : CollatzResearch.WordTrace tailWord_748143 prefixEnd_748143 341472850930463662908319 := by
  unfold tailWord_748143
  simp only [CollatzResearch.WordTrace]
  refine ⟨27287016928613158497009083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18191344619075438998006055 27287016928613158497009083)
  ·
    refine ⟨40930525392919737745513625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27287016928613158497009083 40930525392919737745513625)
    ·
      refine ⟨30697894044689803309135219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40930525392919737745513625 30697894044689803309135219)
      ·
        refine ⟨46046841067034704963702829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30697894044689803309135219 46046841067034704963702829)
        ·
          refine ⟨17267565400138014361388561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46046841067034704963702829 17267565400138014361388561)
          ·
            refine ⟨12950674050103510771041421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17267565400138014361388561 12950674050103510771041421)
            ·
              refine ⟨4856502768788816539140533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12950674050103510771041421 4856502768788816539140533)
              ·
                refine ⟨455297134573951550544425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4856502768788816539140533 455297134573951550544425)
                ·
                  refine ⟨341472850930463662908319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 455297134573951550544425 341472850930463662908319)
                  ·
                    rfl

theorem cell20_748143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 5, 2].length) (baseStart_748143 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_748143 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_748143 prefixEnd_748143 := by exact prefixLift 748143
  have htrace : WordTrace (prefixWord ++ tailWord_748143) baseStart_748143 baseEnd_748143 := by
    simpa [prefixWord, tailWord_748143, baseEnd_748143] using wordTrace_append hprefix tailTrace_748143
  have hstable : (prefixWord ++ tailWord_748143).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748143).length < 2 ^ (prefixWord ++ tailWord_748143).sum := by decide
  have hdescent : baseEnd_748143 < baseStart_748143 := by decide
  rcases family_descends (prefixWord ++ tailWord_748143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748188 : List Nat := [2, 2, 3, 2, 2, 2, 1, 6]
def baseStart_748188 : Nat := 118140960795 + 748188 * 2 ^ 59
def prefixEnd_748188 : Nat := 4983230072969 + 3 ^ 40 * 748188 * 2
def baseEnd_748188 : Nat := 113831130052214502136045

theorem tailTrace_748188 : CollatzResearch.WordTrace tailWord_748188 prefixEnd_748188 113831130052214502136045 := by
  unfold tailWord_748188
  simp only [CollatzResearch.WordTrace]
  refine ⟨13644329106725065591198609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18192438808966754121598145 13644329106725065591198609)
  ·
    refine ⟨10233246830043799193398957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13644329106725065591198609 10233246830043799193398957)
    ·
      refine ⟨3837467561266424697524609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10233246830043799193398957 3837467561266424697524609)
      ·
        refine ⟨2878100670949818523143457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3837467561266424697524609 2878100670949818523143457)
        ·
          refine ⟨2158575503212363892357593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2878100670949818523143457 2158575503212363892357593)
          ·
            refine ⟨1618931627409272919268195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2158575503212363892357593 1618931627409272919268195)
            ·
              refine ⟨2428397441113909378902293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1618931627409272919268195 2428397441113909378902293)
              ·
                refine ⟨113831130052214502136045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2428397441113909378902293 113831130052214502136045)
                ·
                  rfl

theorem cell20_748188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 6].length) (baseStart_748188 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_748188 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_748188 prefixEnd_748188 := by exact prefixLift 748188
  have htrace : WordTrace (prefixWord ++ tailWord_748188) baseStart_748188 baseEnd_748188 := by
    simpa [prefixWord, tailWord_748188, baseEnd_748188] using wordTrace_append hprefix tailTrace_748188
  have hstable : (prefixWord ++ tailWord_748188).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748188).length < 2 ^ (prefixWord ++ tailWord_748188).sum := by decide
  have hdescent : baseEnd_748188 < baseStart_748188 := by decide
  rcases family_descends (prefixWord ++ tailWord_748188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748215 : List Nat := [1, 1, 3, 1, 6, 1, 3, 2, 2]
def baseStart_748215 : Nat := 118140960795 + 748215 * 2 ^ 59
def prefixEnd_748215 : Nat := 4983230072969 + 3 ^ 40 * 748215 * 2
def baseEnd_748215 : Nat := 341505713692351412508025

theorem tailTrace_748215 : CollatzResearch.WordTrace tailWord_748215 prefixEnd_748215 341505713692351412508025 := by
  unfold tailWord_748215
  simp only [CollatzResearch.WordTrace]
  refine ⟨27289642984352314793630099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18193095322901543195753399 27289642984352314793630099)
  ·
    refine ⟨40934464476528472190445149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27289642984352314793630099 40934464476528472190445149)
    ·
      refine ⟨15350424178698177071416931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40934464476528472190445149 15350424178698177071416931)
      ·
        refine ⟨23025636268047265607125397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15350424178698177071416931 23025636268047265607125397)
        ·
          refine ⟨1079326700064715575334003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 23025636268047265607125397 1079326700064715575334003)
          ·
            refine ⟨1618990050097073363001005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1079326700064715575334003 1618990050097073363001005)
            ·
              refine ⟨607121268786402511125377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1618990050097073363001005 607121268786402511125377)
              ·
                refine ⟨455340951589801883344033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 607121268786402511125377 455340951589801883344033)
                ·
                  refine ⟨341505713692351412508025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 455340951589801883344033 341505713692351412508025)
                  ·
                    rfl

theorem cell20_748215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 3, 2, 2].length) (baseStart_748215 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_748215 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_748215 prefixEnd_748215 := by exact prefixLift 748215
  have htrace : WordTrace (prefixWord ++ tailWord_748215) baseStart_748215 baseEnd_748215 := by
    simpa [prefixWord, tailWord_748215, baseEnd_748215] using wordTrace_append hprefix tailTrace_748215
  have hstable : (prefixWord ++ tailWord_748215).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748215).length < 2 ^ (prefixWord ++ tailWord_748215).sum := by decide
  have hdescent : baseEnd_748215 < baseStart_748215 := by decide
  rcases family_descends (prefixWord ++ tailWord_748215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748225 : List Nat := [1, 2, 6, 2, 1, 2, 2, 1, 3]
def baseStart_748225 : Nat := 118140960795 + 748225 * 2 ^ 59
def prefixEnd_748225 : Nat := 4983230072969 + 3 ^ 40 * 748225 * 2
def baseEnd_748225 : Nat := 341510277964835822174651

theorem tailTrace_748225 : CollatzResearch.WordTrace tailWord_748225 prefixEnd_748225 341510277964835822174651 := by
  unfold tailWord_748225
  simp only [CollatzResearch.WordTrace]
  refine ⟨27290007714316086501494129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18193338476210724334329419 27290007714316086501494129)
  ·
    refine ⟨20467505785737064876120597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27290007714316086501494129 20467505785737064876120597)
    ·
      refine ⟨959414333706424916068153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 20467505785737064876120597 959414333706424916068153)
      ·
        refine ⟨719560750279818687051115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 959414333706424916068153 719560750279818687051115)
        ·
          refine ⟨1079341125419728030576673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 719560750279818687051115 1079341125419728030576673)
          ·
            refine ⟨809505844064796022932505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1079341125419728030576673 809505844064796022932505)
            ·
              refine ⟨607129383048597017199379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 809505844064796022932505 607129383048597017199379)
              ·
                refine ⟨910694074572895525799069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 607129383048597017199379 910694074572895525799069)
                ·
                  refine ⟨341510277964835822174651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 910694074572895525799069 341510277964835822174651)
                  ·
                    rfl

theorem cell20_748225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 2, 1, 3].length) (baseStart_748225 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_748225 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_748225 prefixEnd_748225 := by exact prefixLift 748225
  have htrace : WordTrace (prefixWord ++ tailWord_748225) baseStart_748225 baseEnd_748225 := by
    simpa [prefixWord, tailWord_748225, baseEnd_748225] using wordTrace_append hprefix tailTrace_748225
  have hstable : (prefixWord ++ tailWord_748225).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748225).length < 2 ^ (prefixWord ++ tailWord_748225).sum := by decide
  have hdescent : baseEnd_748225 < baseStart_748225 := by decide
  rcases family_descends (prefixWord ++ tailWord_748225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748247 : List Nat := [1, 1, 3, 2, 1, 4, 2, 6]
def baseStart_748247 : Nat := 118140960795 + 748247 * 2 ^ 59
def prefixEnd_748247 : Nat := 4983230072969 + 3 ^ 40 * 748247 * 2
def baseEnd_748247 : Nat := 113840106454767174480409

theorem tailTrace_748247 : CollatzResearch.WordTrace tailWord_748247 prefixEnd_748247 113840106454767174480409 := by
  unfold tailWord_748247
  simp only [CollatzResearch.WordTrace]
  refine ⟨27290810120236384258794995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18193873413490922839196663 27290810120236384258794995)
  ·
    refine ⟨40936215180354576388192493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27290810120236384258794995 40936215180354576388192493)
    ·
      refine ⟨15351080692632966145572185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40936215180354576388192493 15351080692632966145572185)
      ·
        refine ⟨11513310519474724609179139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15351080692632966145572185 11513310519474724609179139)
        ·
          refine ⟨17269965779212086913768709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11513310519474724609179139 17269965779212086913768709)
          ·
            refine ⟨3238118583602266296331633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17269965779212086913768709 3238118583602266296331633)
            ·
              refine ⟨2428588937701699722248725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3238118583602266296331633 2428588937701699722248725)
              ·
                refine ⟨113840106454767174480409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2428588937701699722248725 113840106454767174480409)
                ·
                  rfl

theorem cell20_748247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 6].length) (baseStart_748247 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_748247 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_748247 prefixEnd_748247 := by exact prefixLift 748247
  have htrace : WordTrace (prefixWord ++ tailWord_748247) baseStart_748247 baseEnd_748247 := by
    simpa [prefixWord, tailWord_748247, baseEnd_748247] using wordTrace_append hprefix tailTrace_748247
  have hstable : (prefixWord ++ tailWord_748247).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748247).length < 2 ^ (prefixWord ++ tailWord_748247).sum := by decide
  have hdescent : baseEnd_748247 < baseStart_748247 := by decide
  rcases family_descends (prefixWord ++ tailWord_748247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748264 : List Nat := [2, 1, 4, 1, 5, 7]
def baseStart_748264 : Nat := 118140960795 + 748264 * 2 ^ 59
def prefixEnd_748264 : Nat := 4983230072969 + 3 ^ 40 * 748264 * 2
def baseEnd_748264 : Nat := 12649188097315741476833

theorem tailTrace_748264 : CollatzResearch.WordTrace tailWord_748264 prefixEnd_748264 12649188097315741476833 := by
  unfold tailWord_748264
  simp only [CollatzResearch.WordTrace]
  refine ⟨13645715080587398081081923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18194286774116530774775897 13645715080587398081081923)
  ·
    refine ⟨20468572620881097121622885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13645715080587398081081923 20468572620881097121622885)
    ·
      refine ⟨3837857366415205710304291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20468572620881097121622885 3837857366415205710304291)
      ·
        refine ⟨5756786049622808565456437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3837857366415205710304291 5756786049622808565456437)
        ·
          refine ⟨539698692152138303011541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5756786049622808565456437 539698692152138303011541)
          ·
            refine ⟨12649188097315741476833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 539698692152138303011541 12649188097315741476833)
            ·
              rfl

theorem cell20_748264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 7].length) (baseStart_748264 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_748264 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_748264 prefixEnd_748264 := by exact prefixLift 748264
  have htrace : WordTrace (prefixWord ++ tailWord_748264) baseStart_748264 baseEnd_748264 := by
    simpa [prefixWord, tailWord_748264, baseEnd_748264] using wordTrace_append hprefix tailTrace_748264
  have hstable : (prefixWord ++ tailWord_748264).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748264).length < 2 ^ (prefixWord ++ tailWord_748264).sum := by decide
  have hdescent : baseEnd_748264 < baseStart_748264 := by decide
  rcases family_descends (prefixWord ++ tailWord_748264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748271 : List Nat := [1, 1, 2, 1, 5, 2, 1, 4, 3]
def baseStart_748271 : Nat := 118140960795 + 748271 * 2 ^ 59
def prefixEnd_748271 : Nat := 4983230072969 + 3 ^ 40 * 748271 * 2
def baseEnd_748271 : Nat := 341531273618264106641129

theorem tailTrace_748271 : CollatzResearch.WordTrace tailWord_748271 prefixEnd_748271 341531273618264106641129 := by
  unfold tailWord_748271
  simp only [CollatzResearch.WordTrace]
  refine ⟨27291685472149436357668667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18194456981432957571779111 27291685472149436357668667)
  ·
    refine ⟨40937528208224154536503001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27291685472149436357668667 40937528208224154536503001)
    ·
      refine ⟨30703146156168115902377251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40937528208224154536503001 30703146156168115902377251)
      ·
        refine ⟨46054719234252173853565877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30703146156168115902377251 46054719234252173853565877)
        ·
          refine ⟨4317629928211141298771801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 46054719234252173853565877 4317629928211141298771801)
          ·
            refine ⟨3238222446158355974078851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4317629928211141298771801 3238222446158355974078851)
            ·
              refine ⟨4857333669237533961118277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3238222446158355974078851 4857333669237533961118277)
              ·
                refine ⟨910750062982037617709677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4857333669237533961118277 910750062982037617709677)
                ·
                  refine ⟨341531273618264106641129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 910750062982037617709677 341531273618264106641129)
                  ·
                    rfl

theorem cell20_748271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 4, 3].length) (baseStart_748271 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_748271 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_748271 prefixEnd_748271 := by exact prefixLift 748271
  have htrace : WordTrace (prefixWord ++ tailWord_748271) baseStart_748271 baseEnd_748271 := by
    simpa [prefixWord, tailWord_748271, baseEnd_748271] using wordTrace_append hprefix tailTrace_748271
  have hstable : (prefixWord ++ tailWord_748271).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748271).length < 2 ^ (prefixWord ++ tailWord_748271).sum := by decide
  have hdescent : baseEnd_748271 < baseStart_748271 := by decide
  rcases family_descends (prefixWord ++ tailWord_748271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748274 : List Nat := [3, 2, 1, 3, 1, 3, 1, 4, 2]
def baseStart_748274 : Nat := 118140960795 + 748274 * 2 ^ 59
def prefixEnd_748274 : Nat := 4983230072969 + 3 ^ 40 * 748274 * 2
def baseEnd_748274 : Nat := 341532642900009429541117

theorem tailTrace_748274 : CollatzResearch.WordTrace tailWord_748274 prefixEnd_748274 341532642900009429541117 := by
  unfold tailWord_748274
  simp only [CollatzResearch.WordTrace]
  refine ⟨6822948722784641967506969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18194529927425711913351917 6822948722784641967506969)
  ·
    refine ⟨5117211542088481475630227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6822948722784641967506969 5117211542088481475630227)
    ·
      refine ⟨7675817313132722213445341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5117211542088481475630227 7675817313132722213445341)
      ·
        refine ⟨2878431492424770830042003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7675817313132722213445341 2878431492424770830042003)
        ·
          refine ⟨4317647238637156245063005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2878431492424770830042003 4317647238637156245063005)
          ·
            refine ⟨1619117714488933591898627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4317647238637156245063005 1619117714488933591898627)
            ·
              refine ⟨2428676571733400387847941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1619117714488933591898627 2428676571733400387847941)
              ·
                refine ⟨455376857200012572721489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2428676571733400387847941 455376857200012572721489)
                ·
                  refine ⟨341532642900009429541117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 455376857200012572721489 341532642900009429541117)
                  ·
                    rfl

theorem cell20_748274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 4, 2].length) (baseStart_748274 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_748274 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_748274 prefixEnd_748274 := by exact prefixLift 748274
  have htrace : WordTrace (prefixWord ++ tailWord_748274) baseStart_748274 baseEnd_748274 := by
    simpa [prefixWord, tailWord_748274, baseEnd_748274] using wordTrace_append hprefix tailTrace_748274
  have hstable : (prefixWord ++ tailWord_748274).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748274).length < 2 ^ (prefixWord ++ tailWord_748274).sum := by decide
  have hdescent : baseEnd_748274 < baseStart_748274 := by decide
  rcases family_descends (prefixWord ++ tailWord_748274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748277 : List Nat := [1, 3, 6, 1, 1, 2, 1, 5]
def baseStart_748277 : Nat := 118140960795 + 748277 * 2 ^ 59
def prefixEnd_748277 : Nat := 4983230072969 + 3 ^ 40 * 748277 * 2
def baseEnd_748277 : Nat := 113844670727251584147035

theorem tailTrace_748277 : CollatzResearch.WordTrace tailWord_748277 prefixEnd_748277 113844670727251584147035 := by
  unfold tailWord_748277
  simp only [CollatzResearch.WordTrace]
  refine ⟨27291904310127699382387085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18194602873418466254924723 27291904310127699382387085)
  ·
    refine ⟨10234464116297887268395157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27291904310127699382387085 10234464116297887268395157)
    ·
      refine ⟨479740505451463465706023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 10234464116297887268395157 479740505451463465706023)
      ·
        refine ⟨719610758177195198559035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 479740505451463465706023 719610758177195198559035)
        ·
          refine ⟨1079416137265792797838553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 719610758177195198559035 1079416137265792797838553)
          ·
            refine ⟨809562102949344598378915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1079416137265792797838553 809562102949344598378915)
            ·
              refine ⟨1214343154424016897568373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 809562102949344598378915 1214343154424016897568373)
              ·
                refine ⟨113844670727251584147035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1214343154424016897568373 113844670727251584147035)
                ·
                  rfl

theorem cell20_748277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 1, 5].length) (baseStart_748277 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_748277 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_748277 prefixEnd_748277 := by exact prefixLift 748277
  have htrace : WordTrace (prefixWord ++ tailWord_748277) baseStart_748277 baseEnd_748277 := by
    simpa [prefixWord, tailWord_748277, baseEnd_748277] using wordTrace_append hprefix tailTrace_748277
  have hstable : (prefixWord ++ tailWord_748277).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748277).length < 2 ^ (prefixWord ++ tailWord_748277).sum := by decide
  have hdescent : baseEnd_748277 < baseStart_748277 := by decide
  rcases family_descends (prefixWord ++ tailWord_748277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748295 : List Nat := [1, 1, 4, 4, 1, 2, 1, 2, 4]
def baseStart_748295 : Nat := 118140960795 + 748295 * 2 ^ 59
def prefixEnd_748295 : Nat := 4983230072969 + 3 ^ 40 * 748295 * 2
def baseEnd_748295 : Nat := 341542227872226689841031

theorem tailTrace_748295 : CollatzResearch.WordTrace tailWord_748295 prefixEnd_748295 341542227872226689841031 := by
  unfold tailWord_748295
  simp only [CollatzResearch.WordTrace]
  refine ⟨27292560824062488456542339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18195040549374992304361559 27292560824062488456542339)
  ·
    refine ⟨40938841236093732684813509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27292560824062488456542339 40938841236093732684813509)
    ·
      refine ⟨7676032731767574878402533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40938841236093732684813509 7676032731767574878402533)
      ·
        refine ⟨1439256137206420289700475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7676032731767574878402533 1439256137206420289700475)
        ·
          refine ⟨2158884205809630434550713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1439256137206420289700475 2158884205809630434550713)
          ·
            refine ⟨1619163154357222825913035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2158884205809630434550713 1619163154357222825913035)
            ·
              refine ⟨2428744731535834238869553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1619163154357222825913035 2428744731535834238869553)
              ·
                refine ⟨1821558548651875679152165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2428744731535834238869553 1821558548651875679152165)
                ·
                  refine ⟨341542227872226689841031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1821558548651875679152165 341542227872226689841031)
                  ·
                    rfl

theorem cell20_748295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 2, 4].length) (baseStart_748295 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_748295 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_748295 prefixEnd_748295 := by exact prefixLift 748295
  have htrace : WordTrace (prefixWord ++ tailWord_748295) baseStart_748295 baseEnd_748295 := by
    simpa [prefixWord, tailWord_748295, baseEnd_748295] using wordTrace_append hprefix tailTrace_748295
  have hstable : (prefixWord ++ tailWord_748295).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748295).length < 2 ^ (prefixWord ++ tailWord_748295).sum := by decide
  have hdescent : baseEnd_748295 < baseStart_748295 := by decide
  rcases family_descends (prefixWord ++ tailWord_748295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748353 : List Nat := [1, 2, 5, 3, 2, 1, 2, 4]
def baseStart_748353 : Nat := 118140960795 + 748353 * 2 ^ 59
def prefixEnd_748353 : Nat := 4983230072969 + 3 ^ 40 * 748353 * 2
def baseEnd_748353 : Nat := 113856233550878755302487

theorem tailTrace_748353 : CollatzResearch.WordTrace tailWord_748353 prefixEnd_748353 113856233550878755302487 := by
  unfold tailWord_748353
  simp only [CollatzResearch.WordTrace]
  refine ⟨27294676257852364362153713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18196450838568242908102475 27294676257852364362153713)
  ·
    refine ⟨20471007193389273271615285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27294676257852364362153713 20471007193389273271615285)
    ·
      refine ⟨1919156924380244369213933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20471007193389273271615285 1919156924380244369213933)
      ·
        refine ⟨719683846642591638455225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1919156924380244369213933 719683846642591638455225)
        ·
          refine ⟨539762884981943728841419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 719683846642591638455225 539762884981943728841419)
          ·
            refine ⟨809644327472915593262129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 539762884981943728841419 809644327472915593262129)
            ·
              refine ⟨607233245604686694946597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 809644327472915593262129 607233245604686694946597)
              ·
                refine ⟨113856233550878755302487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 607233245604686694946597 113856233550878755302487)
                ·
                  rfl

theorem cell20_748353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 2, 4].length) (baseStart_748353 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_748353 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_748353 prefixEnd_748353 := by exact prefixLift 748353
  have htrace : WordTrace (prefixWord ++ tailWord_748353) baseStart_748353 baseEnd_748353 := by
    simpa [prefixWord, tailWord_748353, baseEnd_748353] using wordTrace_append hprefix tailTrace_748353
  have hstable : (prefixWord ++ tailWord_748353).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748353).length < 2 ^ (prefixWord ++ tailWord_748353).sum := by decide
  have hdescent : baseEnd_748353 < baseStart_748353 := by decide
  rcases family_descends (prefixWord ++ tailWord_748353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748361 : List Nat := [1, 2, 1, 1, 2, 6, 1, 6]
def baseStart_748361 : Nat := 118140960795 + 748361 * 2 ^ 59
def prefixEnd_748361 : Nat := 4983230072969 + 3 ^ 40 * 748361 * 2
def baseEnd_748361 : Nat := 113857450690207931213587

theorem tailTrace_748361 : CollatzResearch.WordTrace tailWord_748361 prefixEnd_748361 113857450690207931213587 := by
  unfold tailWord_748361
  simp only [CollatzResearch.WordTrace]
  refine ⟨27294968041823381728444937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18196645361215587818963291 27294968041823381728444937)
  ·
    refine ⟨20471226031367536296333703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27294968041823381728444937 20471226031367536296333703)
    ·
      refine ⟨30706839047051304444500555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20471226031367536296333703 30706839047051304444500555)
      ·
        refine ⟨46060258570576956666750833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30706839047051304444500555 46060258570576956666750833)
        ·
          refine ⟨34545193927932717500063125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46060258570576956666750833 34545193927932717500063125)
          ·
            refine ⟨1619305965371846132815459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 34545193927932717500063125 1619305965371846132815459)
            ·
              refine ⟨2428958948057769199223189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1619305965371846132815459 2428958948057769199223189)
              ·
                refine ⟨113857450690207931213587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2428958948057769199223189 113857450690207931213587)
                ·
                  rfl

theorem cell20_748361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 6].length) (baseStart_748361 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_748361 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_748361 prefixEnd_748361 := by exact prefixLift 748361
  have htrace : WordTrace (prefixWord ++ tailWord_748361) baseStart_748361 baseEnd_748361 := by
    simpa [prefixWord, tailWord_748361, baseEnd_748361] using wordTrace_append hprefix tailTrace_748361
  have hstable : (prefixWord ++ tailWord_748361).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748361).length < 2 ^ (prefixWord ++ tailWord_748361).sum := by decide
  have hdescent : baseEnd_748361 < baseStart_748361 := by decide
  rcases family_descends (prefixWord ++ tailWord_748361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748368 : List Nat := [2, 1, 1, 1, 1, 4, 3, 2, 5]
def baseStart_748368 : Nat := 118140960795 + 748368 * 2 ^ 59
def prefixEnd_748368 : Nat := 4983230072969 + 3 ^ 40 * 748368 * 2
def baseEnd_748368 : Nat := 341575547061362880407399

theorem tailTrace_748368 : CollatzResearch.WordTrace tailWord_748368 prefixEnd_748368 341575547061362880407399 := by
  unfold tailWord_748368
  simp only [CollatzResearch.WordTrace]
  refine ⟨13647611676399010961974879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18196815568532014615966505 13647611676399010961974879)
  ·
    refine ⟨20471417514598516442962319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13647611676399010961974879 20471417514598516442962319)
    ·
      refine ⟨30707126271897774664443479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20471417514598516442962319 30707126271897774664443479)
      ·
        refine ⟨46060689407846661996665219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30707126271897774664443479 46060689407846661996665219)
        ·
          refine ⟨69091034111769992994997829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46060689407846661996665219 69091034111769992994997829)
          ·
            refine ⟨12954568895956873686562093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69091034111769992994997829 12954568895956873686562093)
            ·
              refine ⟨4857963335983827632460785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12954568895956873686562093 4857963335983827632460785)
              ·
                refine ⟨3643472501987870724345589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4857963335983827632460785 3643472501987870724345589)
                ·
                  refine ⟨341575547061362880407399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3643472501987870724345589 341575547061362880407399)
                  ·
                    rfl

theorem cell20_748368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 2, 5].length) (baseStart_748368 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_748368 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_748368 prefixEnd_748368 := by exact prefixLift 748368
  have htrace : WordTrace (prefixWord ++ tailWord_748368) baseStart_748368 baseEnd_748368 := by
    simpa [prefixWord, tailWord_748368, baseEnd_748368] using wordTrace_append hprefix tailTrace_748368
  have hstable : (prefixWord ++ tailWord_748368).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748368).length < 2 ^ (prefixWord ++ tailWord_748368).sum := by decide
  have hdescent : baseEnd_748368 < baseStart_748368 := by decide
  rcases family_descends (prefixWord ++ tailWord_748368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748398 : List Nat := [4, 1, 2, 3, 2, 2, 2, 1, 3]
def baseStart_748398 : Nat := 118140960795 + 748398 * 2 ^ 59
def prefixEnd_748398 : Nat := 4983230072969 + 3 ^ 40 * 748398 * 2
def baseEnd_748398 : Nat := 341589239878816109407277

theorem tailTrace_748398 : CollatzResearch.WordTrace tailWord_748398 prefixEnd_748398 341589239878816109407277 := by
  unfold tailWord_748398
  simp only [CollatzResearch.WordTrace]
  refine ⟨3412039692836167130942731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18197545028459558031694565 3412039692836167130942731)
  ·
    refine ⟨5118059539254250696414097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3412039692836167130942731 5118059539254250696414097)
    ·
      refine ⟨3838544654440688022310573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5118059539254250696414097 3838544654440688022310573)
      ·
        refine ⟨1439454245415258008366465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3838544654440688022310573 1439454245415258008366465)
        ·
          refine ⟨1079590684061443506274849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1439454245415258008366465 1079590684061443506274849)
          ·
            refine ⟨809693013046082629706137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1079590684061443506274849 809693013046082629706137)
            ·
              refine ⟨607269759784561972279603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 809693013046082629706137 607269759784561972279603)
              ·
                refine ⟨910904639676842958419405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 607269759784561972279603 910904639676842958419405)
                ·
                  refine ⟨341589239878816109407277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 910904639676842958419405 341589239878816109407277)
                  ·
                    rfl

theorem cell20_748398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 2, 1, 3].length) (baseStart_748398 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_748398 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_748398 prefixEnd_748398 := by exact prefixLift 748398
  have htrace : WordTrace (prefixWord ++ tailWord_748398) baseStart_748398 baseEnd_748398 := by
    simpa [prefixWord, tailWord_748398, baseEnd_748398] using wordTrace_append hprefix tailTrace_748398
  have hstable : (prefixWord ++ tailWord_748398).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748398).length < 2 ^ (prefixWord ++ tailWord_748398).sum := by decide
  have hdescent : baseEnd_748398 < baseStart_748398 := by decide
  rcases family_descends (prefixWord ++ tailWord_748398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748402 : List Nat := [3, 2, 1, 2, 1, 1, 6, 1, 3]
def baseStart_748402 : Nat := 118140960795 + 748402 * 2 ^ 59
def prefixEnd_748402 : Nat := 4983230072969 + 3 ^ 40 * 748402 * 2
def baseEnd_748402 : Nat := 341591065587809873273927

theorem tailTrace_748402 : CollatzResearch.WordTrace tailWord_748402 prefixEnd_748402 341591065587809873273927 := by
  unfold tailWord_748402
  simp only [CollatzResearch.WordTrace]
  refine ⟨6824115858668711432671865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18197642289783230487124973 6824115858668711432671865)
  ·
    refine ⟨5118086894001533574503899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6824115858668711432671865 5118086894001533574503899)
    ·
      refine ⟨7677130341002300361755849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5118086894001533574503899 7677130341002300361755849)
      ·
        refine ⟨5757847755751725271316887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7677130341002300361755849 5757847755751725271316887)
        ·
          refine ⟨8636771633627587906975331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5757847755751725271316887 8636771633627587906975331)
          ·
            refine ⟨12955157450441381860462997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8636771633627587906975331 12955157450441381860462997)
            ·
              refine ⟨607273005489439774709203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 12955157450441381860462997 607273005489439774709203)
              ·
                refine ⟨910909508234159662063805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 607273005489439774709203 910909508234159662063805)
                ·
                  refine ⟨341591065587809873273927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 910909508234159662063805 341591065587809873273927)
                  ·
                    rfl

theorem cell20_748402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 6, 1, 3].length) (baseStart_748402 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_748402 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_748402 prefixEnd_748402 := by exact prefixLift 748402
  have htrace : WordTrace (prefixWord ++ tailWord_748402) baseStart_748402 baseEnd_748402 := by
    simpa [prefixWord, tailWord_748402, baseEnd_748402] using wordTrace_append hprefix tailTrace_748402
  have hstable : (prefixWord ++ tailWord_748402).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748402).length < 2 ^ (prefixWord ++ tailWord_748402).sum := by decide
  have hdescent : baseEnd_748402 < baseStart_748402 := by decide
  rcases family_descends (prefixWord ++ tailWord_748402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748502 : List Nat := [5, 2, 1, 1, 2, 2, 2, 1, 4]
def baseStart_748502 : Nat := 118140960795 + 748502 * 2 ^ 59
def prefixEnd_748502 : Nat := 4983230072969 + 3 ^ 40 * 748502 * 2
def baseEnd_748502 : Nat := 341636708312653969940185

theorem tailTrace_748502 : CollatzResearch.WordTrace tailWord_748502 prefixEnd_748502 341636708312653969940185 := by
  unfold tailWord_748502
  simp only [CollatzResearch.WordTrace]
  refine ⟨1706256920894535175582985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18200073822875041872885173 1706256920894535175582985)
  ·
    refine ⟨1279692690670901381687239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1706256920894535175582985 1279692690670901381687239)
    ·
      refine ⟨1919539036006352072530859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1279692690670901381687239 1919539036006352072530859)
      ·
        refine ⟨2879308554009528108796289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1919539036006352072530859 2879308554009528108796289)
        ·
          refine ⟨2159481415507146081597217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2879308554009528108796289 2159481415507146081597217)
          ·
            refine ⟨1619611061630359561197913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2159481415507146081597217 1619611061630359561197913)
            ·
              refine ⟨1214708296222769670898435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1619611061630359561197913 1214708296222769670898435)
              ·
                refine ⟨1822062444334154506347653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1214708296222769670898435 1822062444334154506347653)
                ·
                  refine ⟨341636708312653969940185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1822062444334154506347653 341636708312653969940185)
                  ·
                    rfl

theorem cell20_748502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_748502 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_748502 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_748502 prefixEnd_748502 := by exact prefixLift 748502
  have htrace : WordTrace (prefixWord ++ tailWord_748502) baseStart_748502 baseEnd_748502 := by
    simpa [prefixWord, tailWord_748502, baseEnd_748502] using wordTrace_append hprefix tailTrace_748502
  have hstable : (prefixWord ++ tailWord_748502).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748502).length < 2 ^ (prefixWord ++ tailWord_748502).sum := by decide
  have hdescent : baseEnd_748502 < baseStart_748502 := by decide
  rcases family_descends (prefixWord ++ tailWord_748502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748506 : List Nat := [3, 1, 1, 2, 4, 1, 1, 3, 4]
def baseStart_748506 : Nat := 118140960795 + 748506 * 2 ^ 59
def prefixEnd_748506 : Nat := 4983230072969 + 3 ^ 40 * 748506 * 2
def baseEnd_748506 : Nat := 341638534021647733806835

theorem tailTrace_748506 : CollatzResearch.WordTrace tailWord_748506 prefixEnd_748506 341638534021647733806835 := by
  unfold tailWord_748506
  simp only [CollatzResearch.WordTrace]
  refine ⟨6825064156574517873118343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18200171084198714328315581 6825064156574517873118343)
  ·
    refine ⟨10237596234861776809677515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6825064156574517873118343 10237596234861776809677515)
    ·
      refine ⟨15356394352292665214516273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10237596234861776809677515 15356394352292665214516273)
      ·
        refine ⟨11517295764219498910887205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15356394352292665214516273 11517295764219498910887205)
        ·
          refine ⟨2159492955791156045791351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11517295764219498910887205 2159492955791156045791351)
          ·
            refine ⟨3239239433686734068687027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2159492955791156045791351 3239239433686734068687027)
            ·
              refine ⟨4858859150530101103030541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3239239433686734068687027 4858859150530101103030541)
              ·
                refine ⟨1822072181448787913636453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4858859150530101103030541 1822072181448787913636453)
                ·
                  refine ⟨341638534021647733806835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1822072181448787913636453 341638534021647733806835)
                  ·
                    rfl

theorem cell20_748506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 3, 4].length) (baseStart_748506 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_748506 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_748506 prefixEnd_748506 := by exact prefixLift 748506
  have htrace : WordTrace (prefixWord ++ tailWord_748506) baseStart_748506 baseEnd_748506 := by
    simpa [prefixWord, tailWord_748506, baseEnd_748506] using wordTrace_append hprefix tailTrace_748506
  have hstable : (prefixWord ++ tailWord_748506).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748506).length < 2 ^ (prefixWord ++ tailWord_748506).sum := by decide
  have hdescent : baseEnd_748506 < baseStart_748506 := by decide
  rcases family_descends (prefixWord ++ tailWord_748506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748526 : List Nat := [4, 1, 2, 1, 5, 1, 2, 4]
def baseStart_748526 : Nat := 118140960795 + 748526 * 2 ^ 59
def prefixEnd_748526 : Nat := 4983230072969 + 3 ^ 40 * 748526 * 2
def baseEnd_748526 : Nat := 113882554188872184380029

theorem tailTrace_748526 : CollatzResearch.WordTrace tailWord_748526 prefixEnd_748526 113882554188872184380029 := by
  unfold tailWord_748526
  simp only [CollatzResearch.WordTrace]
  refine ⟨3412623260778201863525179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18200657390817076605467621 3412623260778201863525179)
  ·
    refine ⟨5118934891167302795287769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3412623260778201863525179 5118934891167302795287769)
    ·
      refine ⟨3839201168375477096465827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5118934891167302795287769 3839201168375477096465827)
      ·
        refine ⟨5758801752563215644698741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3839201168375477096465827 5758801752563215644698741)
        ·
          refine ⟨539887664302801466690507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5758801752563215644698741 539887664302801466690507)
          ·
            refine ⟨809831496454202200035761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 539887664302801466690507 809831496454202200035761)
            ·
              refine ⟨607373622340651650026821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 809831496454202200035761 607373622340651650026821)
              ·
                refine ⟨113882554188872184380029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 607373622340651650026821 113882554188872184380029)
                ·
                  rfl

theorem cell20_748526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 2, 4].length) (baseStart_748526 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_748526 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_748526 prefixEnd_748526 := by exact prefixLift 748526
  have htrace : WordTrace (prefixWord ++ tailWord_748526) baseStart_748526 baseEnd_748526 := by
    simpa [prefixWord, tailWord_748526, baseEnd_748526] using wordTrace_append hprefix tailTrace_748526
  have hstable : (prefixWord ++ tailWord_748526).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748526).length < 2 ^ (prefixWord ++ tailWord_748526).sum := by decide
  have hdescent : baseEnd_748526 < baseStart_748526 := by decide
  rcases family_descends (prefixWord ++ tailWord_748526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748532 : List Nat := [2, 6, 2, 1, 1, 2, 1, 3, 2]
def baseStart_748532 : Nat := 118140960795 + 748532 * 2 ^ 59
def prefixEnd_748532 : Nat := 4983230072969 + 3 ^ 40 * 748532 * 2
def baseEnd_748532 : Nat := 341650401130107198940063

theorem tailTrace_748532 : CollatzResearch.WordTrace tailWord_748532 prefixEnd_748532 341650401130107198940063 := by
  unfold tailWord_748532
  simp only [CollatzResearch.WordTrace]
  refine ⟨13650602462101938966459925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18200803282802585288613233 13650602462101938966459925)
  ·
    refine ⟨639871990411028389052809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 13650602462101938966459925 639871990411028389052809)
    ·
      refine ⟨479903992808271291789607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 639871990411028389052809 479903992808271291789607)
      ·
        refine ⟨719855989212406937684411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 479903992808271291789607 719855989212406937684411)
        ·
          refine ⟨1079783983818610406526617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 719855989212406937684411 1079783983818610406526617)
          ·
            refine ⟨809837987863957804894963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1079783983818610406526617 809837987863957804894963)
            ·
              refine ⟨1214756981795936707342445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 809837987863957804894963 1214756981795936707342445)
              ·
                refine ⟨455533868173476265253417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1214756981795936707342445 455533868173476265253417)
                ·
                  refine ⟨341650401130107198940063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 455533868173476265253417 341650401130107198940063)
                  ·
                    rfl

theorem cell20_748532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_748532 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_748532 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_748532 prefixEnd_748532 := by exact prefixLift 748532
  have htrace : WordTrace (prefixWord ++ tailWord_748532) baseStart_748532 baseEnd_748532 := by
    simpa [prefixWord, tailWord_748532, baseEnd_748532] using wordTrace_append hprefix tailTrace_748532
  have hstable : (prefixWord ++ tailWord_748532).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748532).length < 2 ^ (prefixWord ++ tailWord_748532).sum := by decide
  have hdescent : baseEnd_748532 < baseStart_748532 := by decide
  rcases family_descends (prefixWord ++ tailWord_748532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748540 : List Nat := [2, 2, 2, 1, 2, 5, 1, 3, 2]
def baseStart_748540 : Nat := 118140960795 + 748540 * 2 ^ 59
def prefixEnd_748540 : Nat := 4983230072969 + 3 ^ 40 * 748540 * 2
def baseEnd_748540 : Nat := 341654052548094726673363

theorem tailTrace_748540 : CollatzResearch.WordTrace tailWord_748540 prefixEnd_748540 341654052548094726673363 := by
  unfold tailWord_748540
  simp only [CollatzResearch.WordTrace]
  refine ⟨13650748354087447649605537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18200997805449930199474049 13650748354087447649605537)
  ·
    refine ⟨10238061265565585737204153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13650748354087447649605537 10238061265565585737204153)
    ·
      refine ⟨7678545949174189302903115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10238061265565585737204153 7678545949174189302903115)
      ·
        refine ⟨11517818923761283954354673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7678545949174189302903115 11517818923761283954354673)
        ·
          refine ⟨8638364192820962965766005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11517818923761283954354673 8638364192820962965766005)
          ·
            refine ⟨809846643076965278040563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8638364192820962965766005 809846643076965278040563)
            ·
              refine ⟨1214769964615447917060845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 809846643076965278040563 1214769964615447917060845)
              ·
                refine ⟨455538736730792968897817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1214769964615447917060845 455538736730792968897817)
                ·
                  refine ⟨341654052548094726673363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 455538736730792968897817 341654052548094726673363)
                  ·
                    rfl

theorem cell20_748540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 1, 3, 2].length) (baseStart_748540 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_748540 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_748540 prefixEnd_748540 := by exact prefixLift 748540
  have htrace : WordTrace (prefixWord ++ tailWord_748540) baseStart_748540 baseEnd_748540 := by
    simpa [prefixWord, tailWord_748540, baseEnd_748540] using wordTrace_append hprefix tailTrace_748540
  have hstable : (prefixWord ++ tailWord_748540).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748540).length < 2 ^ (prefixWord ++ tailWord_748540).sum := by decide
  have hdescent : baseEnd_748540 < baseStart_748540 := by decide
  rcases family_descends (prefixWord ++ tailWord_748540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748575 : List Nat := [1, 1, 2, 4, 1, 4, 1, 3, 3]
def baseStart_748575 : Nat := 118140960795 + 748575 * 2 ^ 59
def prefixEnd_748575 : Nat := 4983230072969 + 3 ^ 40 * 748575 * 2
def baseEnd_748575 : Nat := 341670027501790160506553

theorem tailTrace_748575 : CollatzResearch.WordTrace tailWord_748575 prefixEnd_748575 341670027501790160506553 := by
  unfold tailWord_748575
  simp only [CollatzResearch.WordTrace]
  refine ⟨27302773263048096276735179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18201848842032064184490119 27302773263048096276735179)
  ·
    refine ⟨40954159894572144415102769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27302773263048096276735179 40954159894572144415102769)
    ·
      refine ⟨30715619920929108311327077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40954159894572144415102769 30715619920929108311327077)
      ·
        refine ⟨5759178735174207808373827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30715619920929108311327077 5759178735174207808373827)
        ·
          refine ⟨8638768102761311712560741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5759178735174207808373827 8638768102761311712560741)
          ·
            refine ⟨1619769019267745946105139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8638768102761311712560741 1619769019267745946105139)
            ·
              refine ⟨2429653528901618919157709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1619769019267745946105139 2429653528901618919157709)
              ·
                refine ⟨911120073338107094684141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2429653528901618919157709 911120073338107094684141)
                ·
                  refine ⟨341670027501790160506553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 911120073338107094684141 341670027501790160506553)
                  ·
                    rfl

theorem cell20_748575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 3, 3].length) (baseStart_748575 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_748575 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_748575 prefixEnd_748575 := by exact prefixLift 748575
  have htrace : WordTrace (prefixWord ++ tailWord_748575) baseStart_748575 baseEnd_748575 := by
    simpa [prefixWord, tailWord_748575, baseEnd_748575] using wordTrace_append hprefix tailTrace_748575
  have hstable : (prefixWord ++ tailWord_748575).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748575).length < 2 ^ (prefixWord ++ tailWord_748575).sum := by decide
  have hdescent : baseEnd_748575 < baseStart_748575 := by decide
  rcases family_descends (prefixWord ++ tailWord_748575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748641 : List Nat := [1, 2, 3, 1, 1, 2, 3, 1, 6]
def baseStart_748641 : Nat := 118140960795 + 748641 * 2 ^ 59
def prefixEnd_748641 : Nat := 4983230072969 + 3 ^ 40 * 748641 * 2
def baseEnd_748641 : Nat := 341700151700187264306283

theorem tailTrace_748641 : CollatzResearch.WordTrace tailWord_748641 prefixEnd_748641 341700151700187264306283 := by
  unfold tailWord_748641
  simp only [CollatzResearch.WordTrace]
  refine ⟨27305180480808989548637777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18203453653872659699091851 27305180480808989548637777)
  ·
    refine ⟨20478885360606742161478333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27305180480808989548637777 20478885360606742161478333)
    ·
      refine ⟨7679582010227528310554375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20478885360606742161478333 7679582010227528310554375)
      ·
        refine ⟨11519373015341292465831563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7679582010227528310554375 11519373015341292465831563)
        ·
          refine ⟨17279059523011938698747345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11519373015341292465831563 17279059523011938698747345)
          ·
            refine ⟨12959294642258954024060509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17279059523011938698747345 12959294642258954024060509)
            ·
              refine ⟨4859735490847107759022691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12959294642258954024060509 4859735490847107759022691)
              ·
                refine ⟨7289603236270661638534037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4859735490847107759022691 7289603236270661638534037)
                ·
                  refine ⟨341700151700187264306283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7289603236270661638534037 341700151700187264306283)
                  ·
                    rfl

theorem cell20_748641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 1, 6].length) (baseStart_748641 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_748641 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_748641 prefixEnd_748641 := by exact prefixLift 748641
  have htrace : WordTrace (prefixWord ++ tailWord_748641) baseStart_748641 baseEnd_748641 := by
    simpa [prefixWord, tailWord_748641, baseEnd_748641] using wordTrace_append hprefix tailTrace_748641
  have hstable : (prefixWord ++ tailWord_748641).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748641).length < 2 ^ (prefixWord ++ tailWord_748641).sum := by decide
  have hdescent : baseEnd_748641 < baseStart_748641 := by decide
  rcases family_descends (prefixWord ++ tailWord_748641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748654 : List Nat := [4, 1, 2, 2, 1, 3, 2, 3, 2]
def baseStart_748654 : Nat := 118140960795 + 748654 * 2 ^ 59
def prefixEnd_748654 : Nat := 4983230072969 + 3 ^ 40 * 748654 * 2
def baseEnd_748654 : Nat := 341706085254416996872897

theorem tailTrace_748654 : CollatzResearch.WordTrace tailWord_748654 prefixEnd_748654 341706085254416996872897 := by
  unfold tailWord_748654
  simp only [CollatzResearch.WordTrace]
  refine ⟨3413206828720236596107627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18203769753174595179240677 3413206828720236596107627)
  ·
    refine ⟨5119810243080354894161441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3413206828720236596107627 5119810243080354894161441)
    ·
      refine ⟨3839857682310266170621081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5119810243080354894161441 3839857682310266170621081)
      ·
        refine ⟨2879893261732699627965811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3839857682310266170621081 2879893261732699627965811)
        ·
          refine ⟨4319839892599049441948717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2879893261732699627965811 4319839892599049441948717)
          ·
            refine ⟨1619939959724643540730769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4319839892599049441948717 1619939959724643540730769)
            ·
              refine ⟨1214954969793482655548077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1619939959724643540730769 1214954969793482655548077)
              ·
                refine ⟨455608113672555995830529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1214954969793482655548077 455608113672555995830529)
                ·
                  refine ⟨341706085254416996872897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 455608113672555995830529 341706085254416996872897)
                  ·
                    rfl

theorem cell20_748654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 2, 3, 2].length) (baseStart_748654 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_748654 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_748654 prefixEnd_748654 := by exact prefixLift 748654
  have htrace : WordTrace (prefixWord ++ tailWord_748654) baseStart_748654 baseEnd_748654 := by
    simpa [prefixWord, tailWord_748654, baseEnd_748654] using wordTrace_append hprefix tailTrace_748654
  have hstable : (prefixWord ++ tailWord_748654).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748654).length < 2 ^ (prefixWord ++ tailWord_748654).sum := by decide
  have hdescent : baseEnd_748654 < baseStart_748654 := by decide
  rcases family_descends (prefixWord ++ tailWord_748654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748665 : List Nat := [1, 2, 1, 3, 5, 1, 7]
def baseStart_748665 : Nat := 118140960795 + 748665 * 2 ^ 59
def prefixEnd_748665 : Nat := 4983230072969 + 3 ^ 40 * 748665 * 2
def baseEnd_748665 : Nat := 37967900661572205278465

theorem tailTrace_748665 : CollatzResearch.WordTrace tailWord_748665 prefixEnd_748665 37967900661572205278465 := by
  unfold tailWord_748665
  simp only [CollatzResearch.WordTrace]
  refine ⟨27306055832722041647511449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18204037221814694431674299 27306055832722041647511449)
  ·
    refine ⟨20479541874541531235633587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27306055832722041647511449 20479541874541531235633587)
    ·
      refine ⟨30719312811812296853450381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20479541874541531235633587 30719312811812296853450381)
      ·
        refine ⟨11519742304429611320043893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30719312811812296853450381 11519742304429611320043893)
        ·
          refine ⟨1079975841040276061254115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11519742304429611320043893 1079975841040276061254115)
          ·
            refine ⟨1619963761560414091881173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1079975841040276061254115 1619963761560414091881173)
            ·
              refine ⟨37967900661572205278465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1619963761560414091881173 37967900661572205278465)
              ·
                rfl

theorem cell20_748665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 7].length) (baseStart_748665 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_748665 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_748665 prefixEnd_748665 := by exact prefixLift 748665
  have htrace : WordTrace (prefixWord ++ tailWord_748665) baseStart_748665 baseEnd_748665 := by
    simpa [prefixWord, tailWord_748665, baseEnd_748665] using wordTrace_append hprefix tailTrace_748665
  have hstable : (prefixWord ++ tailWord_748665).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748665).length < 2 ^ (prefixWord ++ tailWord_748665).sum := by decide
  have hdescent : baseEnd_748665 < baseStart_748665 := by decide
  rcases family_descends (prefixWord ++ tailWord_748665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748696 : List Nat := [2, 1, 2, 4, 2, 1, 2, 2, 4]
def baseStart_748696 : Nat := 118140960795 + 748696 * 2 ^ 59
def prefixEnd_748696 : Nat := 4983230072969 + 3 ^ 40 * 748696 * 2
def baseEnd_748696 : Nat := 341725255198851517472725

theorem tailTrace_748696 : CollatzResearch.WordTrace tailWord_748696 prefixEnd_748696 341725255198851517472725 := by
  unfold tailWord_748696
  simp only [CollatzResearch.WordTrace]
  refine ⟨13653593247804866970944971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18204790997073155961259961 13653593247804866970944971)
  ·
    refine ⟨20480389871707300456417457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13653593247804866970944971 20480389871707300456417457)
    ·
      refine ⟨15360292403780475342313093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20480389871707300456417457 15360292403780475342313093)
      ·
        refine ⟨2880054825708839126683705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15360292403780475342313093 2880054825708839126683705)
        ·
          refine ⟨2160041119281629345012779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2880054825708839126683705 2160041119281629345012779)
          ·
            refine ⟨3240061678922444017519169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2160041119281629345012779 3240061678922444017519169)
            ·
              refine ⟨2430046259191833013139377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3240061678922444017519169 2430046259191833013139377)
              ·
                refine ⟨1822534694393874759854533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2430046259191833013139377 1822534694393874759854533)
                ·
                  refine ⟨341725255198851517472725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1822534694393874759854533 341725255198851517472725)
                  ·
                    rfl

theorem cell20_748696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 2, 4].length) (baseStart_748696 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_748696 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_748696 prefixEnd_748696 := by exact prefixLift 748696
  have htrace : WordTrace (prefixWord ++ tailWord_748696) baseStart_748696 baseEnd_748696 := by
    simpa [prefixWord, tailWord_748696, baseEnd_748696] using wordTrace_append hprefix tailTrace_748696
  have hstable : (prefixWord ++ tailWord_748696).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748696).length < 2 ^ (prefixWord ++ tailWord_748696).sum := by decide
  have hdescent : baseEnd_748696 < baseStart_748696 := by decide
  rcases family_descends (prefixWord ++ tailWord_748696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748726 : List Nat := [5, 1, 3, 2, 2, 1, 1, 1, 4]
def baseStart_748726 : Nat := 118140960795 + 748726 * 2 ^ 59
def prefixEnd_748726 : Nat := 4983230072969 + 3 ^ 40 * 748726 * 2
def baseEnd_748726 : Nat := 341738948016304746472603

theorem tailTrace_748726 : CollatzResearch.WordTrace tailWord_748726 prefixEnd_748726 341738948016304746472603 := by
  unfold tailWord_748726
  simp only [CollatzResearch.WordTrace]
  refine ⟨1706767542843815566592627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18205520457000699376988021 1706767542843815566592627)
  ·
    refine ⟨2560151314265723349888941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1706767542843815566592627 2560151314265723349888941)
    ·
      refine ⟨960056742849646256208353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2560151314265723349888941 960056742849646256208353)
      ·
        refine ⟨720042557137234692156265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 960056742849646256208353 720042557137234692156265)
        ·
          refine ⟨540031917852926019117199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 720042557137234692156265 540031917852926019117199)
          ·
            refine ⟨810047876779389028675799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 540031917852926019117199 810047876779389028675799)
            ·
              refine ⟨1215071815169083543013699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 810047876779389028675799 1215071815169083543013699)
              ·
                refine ⟨1822607722753625314520549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1215071815169083543013699 1822607722753625314520549)
                ·
                  refine ⟨341738948016304746472603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1822607722753625314520549 341738948016304746472603)
                  ·
                    rfl

theorem cell20_748726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 1, 1, 4].length) (baseStart_748726 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_748726 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_748726 prefixEnd_748726 := by exact prefixLift 748726
  have htrace : WordTrace (prefixWord ++ tailWord_748726) baseStart_748726 baseEnd_748726 := by
    simpa [prefixWord, tailWord_748726, baseEnd_748726] using wordTrace_append hprefix tailTrace_748726
  have hstable : (prefixWord ++ tailWord_748726).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748726).length < 2 ^ (prefixWord ++ tailWord_748726).sum := by decide
  have hdescent : baseEnd_748726 < baseStart_748726 := by decide
  rcases family_descends (prefixWord ++ tailWord_748726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748740 : List Nat := [2, 3, 3, 1, 4, 1, 2, 1, 3]
def baseStart_748740 : Nat := 118140960795 + 748740 * 2 ^ 59
def prefixEnd_748740 : Nat := 4983230072969 + 3 ^ 40 * 748740 * 2
def baseEnd_748740 : Nat := 341745337997782920005879

theorem tailTrace_748740 : CollatzResearch.WordTrace tailWord_748740 prefixEnd_748740 341745337997782920005879 := by
  unfold tailWord_748740
  simp only [CollatzResearch.WordTrace]
  refine ⟨13654395653725164728245837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18205860871633552970994449 13654395653725164728245837)
  ·
    refine ⟨5120398370146936773092189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13654395653725164728245837 5120398370146936773092189)
    ·
      refine ⟨1920149388805101289909571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5120398370146936773092189 1920149388805101289909571)
      ·
        refine ⟨2880224083207651934864357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1920149388805101289909571 2880224083207651934864357)
        ·
          refine ⟨540042015601434737787067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2880224083207651934864357 540042015601434737787067)
          ·
            refine ⟨810063023402152106680601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 540042015601434737787067 810063023402152106680601)
            ·
              refine ⟨607547267551614080010451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 810063023402152106680601 607547267551614080010451)
              ·
                refine ⟨911320901327421120015677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 607547267551614080010451 911320901327421120015677)
                ·
                  refine ⟨341745337997782920005879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 911320901327421120015677 341745337997782920005879)
                  ·
                    rfl

theorem cell20_748740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 2, 1, 3].length) (baseStart_748740 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_748740 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_748740 prefixEnd_748740 := by exact prefixLift 748740
  have htrace : WordTrace (prefixWord ++ tailWord_748740) baseStart_748740 baseEnd_748740 := by
    simpa [prefixWord, tailWord_748740, baseEnd_748740] using wordTrace_append hprefix tailTrace_748740
  have hstable : (prefixWord ++ tailWord_748740).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748740).length < 2 ^ (prefixWord ++ tailWord_748740).sum := by decide
  have hdescent : baseEnd_748740 < baseStart_748740 := by decide
  rcases family_descends (prefixWord ++ tailWord_748740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748793 : List Nat := [1, 2, 1, 3, 1, 1, 4, 3, 4]
def baseStart_748793 : Nat := 118140960795 + 748793 * 2 ^ 59
def prefixEnd_748793 : Nat := 4983230072969 + 3 ^ 40 * 748793 * 2
def baseEnd_748793 : Nat := 341769528641950291238995

theorem tailTrace_748793 : CollatzResearch.WordTrace tailWord_748793 prefixEnd_748793 341769528641950291238995 := by
  unfold tailWord_748793
  simp only [CollatzResearch.WordTrace]
  refine ⟨27310724376258319508171033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18207149584172213005447355 27310724376258319508171033)
  ·
    refine ⟨20483043282193739631128275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27310724376258319508171033 20483043282193739631128275)
    ·
      refine ⟨30724564923290609446692413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20483043282193739631128275 30724564923290609446692413)
      ·
        refine ⟨11521711846233978542509655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30724564923290609446692413 11521711846233978542509655)
        ·
          refine ⟨17282567769350967813764483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11521711846233978542509655 17282567769350967813764483)
          ·
            refine ⟨25923851654026451720646725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17282567769350967813764483 25923851654026451720646725)
            ·
              refine ⟨4860722185129959697621261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25923851654026451720646725 4860722185129959697621261)
              ·
                refine ⟨1822770819423734886607973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4860722185129959697621261 1822770819423734886607973)
                ·
                  refine ⟨341769528641950291238995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1822770819423734886607973 341769528641950291238995)
                  ·
                    rfl

theorem cell20_748793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 3, 4].length) (baseStart_748793 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_748793 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_748793 prefixEnd_748793 := by exact prefixLift 748793
  have htrace : WordTrace (prefixWord ++ tailWord_748793) baseStart_748793 baseEnd_748793 := by
    simpa [prefixWord, tailWord_748793, baseEnd_748793] using wordTrace_append hprefix tailTrace_748793
  have hstable : (prefixWord ++ tailWord_748793).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748793).length < 2 ^ (prefixWord ++ tailWord_748793).sum := by decide
  have hdescent : baseEnd_748793 < baseStart_748793 := by decide
  rcases family_descends (prefixWord ++ tailWord_748793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748796 : List Nat := [2, 2, 2, 1, 5, 2, 1, 5]
def baseStart_748796 : Nat := 118140960795 + 748796 * 2 ^ 59
def prefixEnd_748796 : Nat := 4983230072969 + 3 ^ 40 * 748796 * 2
def baseEnd_748796 : Nat := 113923632641231871379661

theorem tailTrace_748796 : CollatzResearch.WordTrace tailWord_748796 prefixEnd_748796 113923632641231871379661 := by
  unfold tailWord_748796
  simp only [CollatzResearch.WordTrace]
  refine ⟨13655416897623725510265121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18207222530164967347020161 13655416897623725510265121)
  ·
    refine ⟨10241562673217794132698841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13655416897623725510265121 10241562673217794132698841)
    ·
      refine ⟨7681172004913345599524131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10241562673217794132698841 7681172004913345599524131)
      ·
        refine ⟨11521758007370018399286197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7681172004913345599524131 11521758007370018399286197)
        ·
          refine ⟨1080164813190939224933081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11521758007370018399286197 1080164813190939224933081)
          ·
            refine ⟨810123609893204418699811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1080164813190939224933081 810123609893204418699811)
            ·
              refine ⟨1215185414839806628049717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 810123609893204418699811 1215185414839806628049717)
              ·
                refine ⟨113923632641231871379661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1215185414839806628049717 113923632641231871379661)
                ·
                  rfl

theorem cell20_748796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 1, 5].length) (baseStart_748796 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_748796 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_748796 prefixEnd_748796 := by exact prefixLift 748796
  have htrace : WordTrace (prefixWord ++ tailWord_748796) baseStart_748796 baseEnd_748796 := by
    simpa [prefixWord, tailWord_748796, baseEnd_748796] using wordTrace_append hprefix tailTrace_748796
  have hstable : (prefixWord ++ tailWord_748796).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748796).length < 2 ^ (prefixWord ++ tailWord_748796).sum := by decide
  have hdescent : baseEnd_748796 < baseStart_748796 := by decide
  rcases family_descends (prefixWord ++ tailWord_748796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748817 : List Nat := [1, 2, 2, 1, 1, 4, 5, 4]
def baseStart_748817 : Nat := 118140960795 + 748817 * 2 ^ 59
def prefixEnd_748817 : Nat := 4983230072969 + 3 ^ 40 * 748817 * 2
def baseEnd_748817 : Nat := 113926827631970958146299

theorem tailTrace_748817 : CollatzResearch.WordTrace tailWord_748817 prefixEnd_748817 113926827631970958146299 := by
  unfold tailWord_748817
  simp only [CollatzResearch.WordTrace]
  refine ⟨27311599728171371607044705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18207733152114247738029803 27311599728171371607044705)
  ·
    refine ⟨20483699796128528705283529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27311599728171371607044705 20483699796128528705283529)
    ·
      refine ⟨15362774847096396528962647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20483699796128528705283529 15362774847096396528962647)
      ·
        refine ⟨23044162270644594793443971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15362774847096396528962647 23044162270644594793443971)
        ·
          refine ⟨34566243405966892190165957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23044162270644594793443971 34566243405966892190165957)
          ·
            refine ⟨6481170638618792285656117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34566243405966892190165957 6481170638618792285656117)
            ·
              refine ⟨607609747370511776780261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6481170638618792285656117 607609747370511776780261)
              ·
                refine ⟨113926827631970958146299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 607609747370511776780261 113926827631970958146299)
                ·
                  rfl

theorem cell20_748817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 5, 4].length) (baseStart_748817 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_748817 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_748817 prefixEnd_748817 := by exact prefixLift 748817
  have htrace : WordTrace (prefixWord ++ tailWord_748817) baseStart_748817 baseEnd_748817 := by
    simpa [prefixWord, tailWord_748817, baseEnd_748817] using wordTrace_append hprefix tailTrace_748817
  have hstable : (prefixWord ++ tailWord_748817).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748817).length < 2 ^ (prefixWord ++ tailWord_748817).sum := by decide
  have hdescent : baseEnd_748817 < baseStart_748817 := by decide
  rcases family_descends (prefixWord ++ tailWord_748817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748848 : List Nat := [2, 1, 1, 1, 2, 2, 3, 6, 2]
def baseStart_748848 : Nat := 118140960795 + 748848 * 2 ^ 59
def prefixEnd_748848 : Nat := 4983230072969 + 3 ^ 40 * 748848 * 2
def baseEnd_748848 : Nat := 341794632140614544405437

theorem tailTrace_748848 : CollatzResearch.WordTrace tailWord_748848 prefixEnd_748848 341794632140614544405437 := by
  unfold tailWord_748848
  simp only [CollatzResearch.WordTrace]
  refine ⟨13656365195529531950711599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18208486927372709267615465 13656365195529531950711599)
  ·
    refine ⟨20484547793294297926067399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13656365195529531950711599 20484547793294297926067399)
    ·
      refine ⟨30726821689941446889101099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20484547793294297926067399 30726821689941446889101099)
      ·
        refine ⟨46090232534912170333651649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30726821689941446889101099 46090232534912170333651649)
        ·
          refine ⟨34567674401184127750238737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46090232534912170333651649 34567674401184127750238737)
          ·
            refine ⟨25925755800888095812679053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34567674401184127750238737 25925755800888095812679053)
            ·
              refine ⟨9722158425333035929754645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25925755800888095812679053 9722158425333035929754645)
              ·
                refine ⟨455726176187486059207249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9722158425333035929754645 455726176187486059207249)
                ·
                  refine ⟨341794632140614544405437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 455726176187486059207249 341794632140614544405437)
                  ·
                    rfl

theorem cell20_748848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 6, 2].length) (baseStart_748848 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_748848 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_748848 prefixEnd_748848 := by exact prefixLift 748848
  have htrace : WordTrace (prefixWord ++ tailWord_748848) baseStart_748848 baseEnd_748848 := by
    simpa [prefixWord, tailWord_748848, baseEnd_748848] using wordTrace_append hprefix tailTrace_748848
  have hstable : (prefixWord ++ tailWord_748848).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748848).length < 2 ^ (prefixWord ++ tailWord_748848).sum := by decide
  have hdescent : baseEnd_748848 < baseStart_748848 := by decide
  rcases family_descends (prefixWord ++ tailWord_748848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748854 : List Nat := [5, 1, 2, 3, 1, 1, 3, 1, 3]
def baseStart_748854 : Nat := 118140960795 + 748854 * 2 ^ 59
def prefixEnd_748854 : Nat := 4983230072969 + 3 ^ 40 * 748854 * 2
def baseEnd_748854 : Nat := 341797370704105190205413

theorem tailTrace_748854 : CollatzResearch.WordTrace tailWord_748854 prefixEnd_748854 341797370704105190205413 := by
  unfold tailWord_748854
  simp only [CollatzResearch.WordTrace]
  refine ⟨1707059326814832932883851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18208632819358217950761077 1707059326814832932883851)
  ·
    refine ⟨2560588990222249399325777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1707059326814832932883851 2560588990222249399325777)
    ·
      refine ⟨1920441742666687049494333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2560588990222249399325777 1920441742666687049494333)
      ·
        refine ⟨720165653500007643560375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1920441742666687049494333 720165653500007643560375)
        ·
          refine ⟨1080248480250011465340563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 720165653500007643560375 1080248480250011465340563)
          ·
            refine ⟨1620372720375017198010845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1080248480250011465340563 1620372720375017198010845)
            ·
              refine ⟨607639770140631449254067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1620372720375017198010845 607639770140631449254067)
              ·
                refine ⟨911459655210947173881101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 607639770140631449254067 911459655210947173881101)
                ·
                  refine ⟨341797370704105190205413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 911459655210947173881101 341797370704105190205413)
                  ·
                    rfl

theorem cell20_748854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 3, 1, 3].length) (baseStart_748854 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_748854 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_748854 prefixEnd_748854 := by exact prefixLift 748854
  have htrace : WordTrace (prefixWord ++ tailWord_748854) baseStart_748854 baseEnd_748854 := by
    simpa [prefixWord, tailWord_748854, baseEnd_748854] using wordTrace_append hprefix tailTrace_748854
  have hstable : (prefixWord ++ tailWord_748854).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748854).length < 2 ^ (prefixWord ++ tailWord_748854).sum := by decide
  have hdescent : baseEnd_748854 < baseStart_748854 := by decide
  rcases family_descends (prefixWord ++ tailWord_748854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748883 : List Nat := [1, 1, 1, 2, 1, 1, 5, 1, 7]
def baseStart_748883 : Nat := 118140960795 + 748883 * 2 ^ 59
def prefixEnd_748883 : Nat := 4983230072969 + 3 ^ 40 * 748883 * 2
def baseEnd_748883 : Nat := 341810607094309978238627

theorem tailTrace_748883 : CollatzResearch.WordTrace tailWord_748883 prefixEnd_748883 341810607094309978238627 := by
  unfold tailWord_748883
  simp only [CollatzResearch.WordTrace]
  refine ⟨27314006945932264878947303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18209337963954843252631535 27314006945932264878947303)
  ·
    refine ⟨40971010418898397318420955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27314006945932264878947303 40971010418898397318420955)
    ·
      refine ⟨61456515628347595977631433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40971010418898397318420955 61456515628347595977631433)
      ·
        refine ⟨46092386721260696983223575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61456515628347595977631433 46092386721260696983223575)
        ·
          refine ⟨69138580081891045474835363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46092386721260696983223575 69138580081891045474835363)
          ·
            refine ⟨103707870122836568212253045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69138580081891045474835363 103707870122836568212253045)
            ·
              refine ⟨9722612824015928269898723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 103707870122836568212253045 9722612824015928269898723)
              ·
                refine ⟨14583919236023892404848085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9722612824015928269898723 14583919236023892404848085)
                ·
                  refine ⟨341810607094309978238627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14583919236023892404848085 341810607094309978238627)
                  ·
                    rfl

theorem cell20_748883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 1, 7].length) (baseStart_748883 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_748883 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_748883 prefixEnd_748883 := by exact prefixLift 748883
  have htrace : WordTrace (prefixWord ++ tailWord_748883) baseStart_748883 baseEnd_748883 := by
    simpa [prefixWord, tailWord_748883, baseEnd_748883] using wordTrace_append hprefix tailTrace_748883
  have hstable : (prefixWord ++ tailWord_748883).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748883).length < 2 ^ (prefixWord ++ tailWord_748883).sum := by decide
  have hdescent : baseEnd_748883 < baseStart_748883 := by decide
  rcases family_descends (prefixWord ++ tailWord_748883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748900 : List Nat := [2, 3, 1, 1, 3, 2, 2, 1, 5]
def baseStart_748900 : Nat := 118140960795 + 748900 * 2 ^ 59
def prefixEnd_748900 : Nat := 4983230072969 + 3 ^ 40 * 748900 * 2
def baseEnd_748900 : Nat := 341818366357533474671891

theorem tailTrace_748900 : CollatzResearch.WordTrace tailWord_748900 prefixEnd_748900 341818366357533474671891 := by
  unfold tailWord_748900
  simp only [CollatzResearch.WordTrace]
  refine ⟨13657313493435338391158077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18209751324580451188210769 13657313493435338391158077)
  ·
    refine ⟨5121492560038251896684279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13657313493435338391158077 5121492560038251896684279)
    ·
      refine ⟨7682238840057377845026419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5121492560038251896684279 7682238840057377845026419)
      ·
        refine ⟨11523358260086066767539629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7682238840057377845026419 11523358260086066767539629)
        ·
          refine ⟨4321259347532275037827361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11523358260086066767539629 4321259347532275037827361)
          ·
            refine ⟨3240944510649206278370521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4321259347532275037827361 3240944510649206278370521)
            ·
              refine ⟨2430708382986904708777891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3240944510649206278370521 2430708382986904708777891)
              ·
                refine ⟨3646062574480357063166837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2430708382986904708777891 3646062574480357063166837)
                ·
                  refine ⟨341818366357533474671891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3646062574480357063166837 341818366357533474671891)
                  ·
                    rfl

theorem cell20_748900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 1, 5].length) (baseStart_748900 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_748900 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_748900 prefixEnd_748900 := by exact prefixLift 748900
  have htrace : WordTrace (prefixWord ++ tailWord_748900) baseStart_748900 baseEnd_748900 := by
    simpa [prefixWord, tailWord_748900, baseEnd_748900] using wordTrace_append hprefix tailTrace_748900
  have hstable : (prefixWord ++ tailWord_748900).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748900).length < 2 ^ (prefixWord ++ tailWord_748900).sum := by decide
  have hdescent : baseEnd_748900 < baseStart_748900 := by decide
  rcases family_descends (prefixWord ++ tailWord_748900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748903 : List Nat := [1, 1, 5, 1, 4, 2, 1, 1, 4]
def baseStart_748903 : Nat := 118140960795 + 748903 * 2 ^ 59
def prefixEnd_748903 : Nat := 4983230072969 + 3 ^ 40 * 748903 * 2
def baseEnd_748903 : Nat := 341819735639278797571879

theorem tailTrace_748903 : CollatzResearch.WordTrace tailWord_748903 prefixEnd_748903 341819735639278797571879 := by
  unfold tailWord_748903
  simp only [CollatzResearch.WordTrace]
  refine ⟨27314736405859808294675363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18209824270573205529783575 27314736405859808294675363)
  ·
    refine ⟨40972104608789712442013045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27314736405859808294675363 40972104608789712442013045)
    ·
      refine ⟨3841134807074035541438723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 40972104608789712442013045 3841134807074035541438723)
      ·
        refine ⟨5761702210611053312158085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3841134807074035541438723 5761702210611053312158085)
        ·
          refine ⟨1080319164489572496029641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5761702210611053312158085 1080319164489572496029641)
          ·
            refine ⟨810239373367179372022231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1080319164489572496029641 810239373367179372022231)
            ·
              refine ⟨1215359060050769058033347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 810239373367179372022231 1215359060050769058033347)
              ·
                refine ⟨1823038590076153587050021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1215359060050769058033347 1823038590076153587050021)
                ·
                  refine ⟨341819735639278797571879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1823038590076153587050021 341819735639278797571879)
                  ·
                    rfl

theorem cell20_748903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 1, 1, 4].length) (baseStart_748903 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_748903 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_748903 prefixEnd_748903 := by exact prefixLift 748903
  have htrace : WordTrace (prefixWord ++ tailWord_748903) baseStart_748903 baseEnd_748903 := by
    simpa [prefixWord, tailWord_748903, baseEnd_748903] using wordTrace_append hprefix tailTrace_748903
  have hstable : (prefixWord ++ tailWord_748903).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748903).length < 2 ^ (prefixWord ++ tailWord_748903).sum := by decide
  have hdescent : baseEnd_748903 < baseStart_748903 := by decide
  rcases family_descends (prefixWord ++ tailWord_748903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748952 : List Nat := [2, 1, 2, 5, 10]
def baseStart_748952 : Nat := 118140960795 + 748952 * 2 ^ 59
def prefixEnd_748952 : Nat := 4983230072969 + 3 ^ 40 * 748952 * 2
def baseEnd_748952 : Nat := 4220272846598177838745

theorem tailTrace_748952 : CollatzResearch.WordTrace tailWord_748952 prefixEnd_748952 4220272846598177838745 := by
  unfold tailWord_748952
  simp only [CollatzResearch.WordTrace]
  refine ⟨13658261791341144831604555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18211015721788193108806073 13658261791341144831604555)
  ·
    refine ⟨20487392687011717247406833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13658261791341144831604555 20487392687011717247406833)
    ·
      refine ⟨15365544515258787935555125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20487392687011717247406833 15365544515258787935555125)
      ·
        refine ⟨1440519798305511368958293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15365544515258787935555125 1440519798305511368958293)
        ·
          refine ⟨4220272846598177838745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1440519798305511368958293 4220272846598177838745)
          ·
            rfl

theorem cell20_748952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 10].length) (baseStart_748952 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_748952 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_748952 prefixEnd_748952 := by exact prefixLift 748952
  have htrace : WordTrace (prefixWord ++ tailWord_748952) baseStart_748952 baseEnd_748952 := by
    simpa [prefixWord, tailWord_748952, baseEnd_748952] using wordTrace_append hprefix tailTrace_748952
  have hstable : (prefixWord ++ tailWord_748952).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748952).length < 2 ^ (prefixWord ++ tailWord_748952).sum := by decide
  have hdescent : baseEnd_748952 < baseStart_748952 := by decide
  rcases family_descends (prefixWord ++ tailWord_748952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748983 : List Nat := [1, 1, 3, 1, 3, 2, 3, 2, 4]
def baseStart_748983 : Nat := 118140960795 + 748983 * 2 ^ 59
def prefixEnd_748983 : Nat := 4983230072969 + 3 ^ 40 * 748983 * 2
def baseEnd_748983 : Nat := 341856249819154074904885

theorem tailTrace_748983 : CollatzResearch.WordTrace tailWord_748983 prefixEnd_748983 341856249819154074904885 := by
  unfold tailWord_748983
  simp only [CollatzResearch.WordTrace]
  refine ⟨27317654245569981957587603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18211769497046654638391735 27317654245569981957587603)
  ·
    refine ⟨40976481368354972936381405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27317654245569981957587603 40976481368354972936381405)
    ·
      refine ⟨15366180513133114851143027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40976481368354972936381405 15366180513133114851143027)
      ·
        refine ⟨23049270769699672276714541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15366180513133114851143027 23049270769699672276714541)
        ·
          refine ⟨8643476538637377103767953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23049270769699672276714541 8643476538637377103767953)
          ·
            refine ⟨6482607403978032827825965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8643476538637377103767953 6482607403978032827825965)
            ·
              refine ⟨2430977776491762310434737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6482607403978032827825965 2430977776491762310434737)
              ·
                refine ⟨1823233332368821732826053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2430977776491762310434737 1823233332368821732826053)
                ·
                  refine ⟨341856249819154074904885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1823233332368821732826053 341856249819154074904885)
                  ·
                    rfl

theorem cell20_748983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 4].length) (baseStart_748983 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_748983 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_748983 prefixEnd_748983 := by exact prefixLift 748983
  have htrace : WordTrace (prefixWord ++ tailWord_748983) baseStart_748983 baseEnd_748983 := by
    simpa [prefixWord, tailWord_748983, baseEnd_748983] using wordTrace_append hprefix tailTrace_748983
  have hstable : (prefixWord ++ tailWord_748983).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748983).length < 2 ^ (prefixWord ++ tailWord_748983).sum := by decide
  have hdescent : baseEnd_748983 < baseStart_748983 := by decide
  rcases family_descends (prefixWord ++ tailWord_748983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748996 : List Nat := [2, 3, 3, 2, 1, 2, 2, 3, 2]
def baseStart_748996 : Nat := 118140960795 + 748996 * 2 ^ 59
def prefixEnd_748996 : Nat := 4983230072969 + 3 ^ 40 * 748996 * 2
def baseEnd_748996 : Nat := 341862183373383807471499

theorem tailTrace_748996 : CollatzResearch.WordTrace tailWord_748996 prefixEnd_748996 341862183373383807471499 := by
  unfold tailWord_748996
  simp only [CollatzResearch.WordTrace]
  refine ⟨13659064197261442588905421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18212085596348590118540561 13659064197261442588905421)
  ·
    refine ⟨5122149073973040970839533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13659064197261442588905421 5122149073973040970839533)
    ·
      refine ⟨1920805902739890364064825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5122149073973040970839533 1920805902739890364064825)
      ·
        refine ⟨1440604427054917773048619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1920805902739890364064825 1440604427054917773048619)
        ·
          refine ⟨2160906640582376659572929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1440604427054917773048619 2160906640582376659572929)
          ·
            refine ⟨1620679980436782494679697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2160906640582376659572929 1620679980436782494679697)
            ·
              refine ⟨1215509985327586871009773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1620679980436782494679697 1215509985327586871009773)
              ·
                refine ⟨455816244497845076628665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1215509985327586871009773 455816244497845076628665)
                ·
                  refine ⟨341862183373383807471499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 455816244497845076628665 341862183373383807471499)
                  ·
                    rfl

theorem cell20_748996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 2, 3, 2].length) (baseStart_748996 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_748996 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_748996 prefixEnd_748996 := by exact prefixLift 748996
  have htrace : WordTrace (prefixWord ++ tailWord_748996) baseStart_748996 baseEnd_748996 := by
    simpa [prefixWord, tailWord_748996, baseEnd_748996] using wordTrace_append hprefix tailTrace_748996
  have hstable : (prefixWord ++ tailWord_748996).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748996).length < 2 ^ (prefixWord ++ tailWord_748996).sum := by decide
  have hdescent : baseEnd_748996 < baseStart_748996 := by decide
  rcases family_descends (prefixWord ++ tailWord_748996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749066 : List Nat := [3, 1, 2, 2, 2, 2, 8]
def baseStart_749066 : Nat := 118140960795 + 749066 * 2 ^ 59
def prefixEnd_749066 : Nat := 4983230072969 + 3 ^ 40 * 749066 * 2
def baseEnd_749066 : Nat := 37988237031197186126431

theorem tailTrace_749066 : CollatzResearch.WordTrace tailWord_749066 prefixEnd_749066 37988237031197186126431 := by
  unfold tailWord_749066
  simp only [CollatzResearch.WordTrace]
  refine ⟨6830170376067321783214763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18213787669512858088572701 6830170376067321783214763)
  ·
    refine ⟨10245255564100982674822145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6830170376067321783214763 10245255564100982674822145)
    ·
      refine ⟨7683941673075737006116609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10245255564100982674822145 7683941673075737006116609)
      ·
        refine ⟨5762956254806802754587457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7683941673075737006116609 5762956254806802754587457)
        ·
          refine ⟨4322217191105102065940593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5762956254806802754587457 4322217191105102065940593)
          ·
            refine ⟨3241662893328826549455445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4322217191105102065940593 3241662893328826549455445)
            ·
              refine ⟨37988237031197186126431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3241662893328826549455445 37988237031197186126431)
              ·
                rfl

theorem cell20_749066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 8].length) (baseStart_749066 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_749066 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_749066 prefixEnd_749066 := by exact prefixLift 749066
  have htrace : WordTrace (prefixWord ++ tailWord_749066) baseStart_749066 baseEnd_749066 := by
    simpa [prefixWord, tailWord_749066, baseEnd_749066] using wordTrace_append hprefix tailTrace_749066
  have hstable : (prefixWord ++ tailWord_749066).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749066).length < 2 ^ (prefixWord ++ tailWord_749066).sum := by decide
  have hdescent : baseEnd_749066 < baseStart_749066 := by decide
  rcases family_descends (prefixWord ++ tailWord_749066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749073 : List Nat := [1, 2, 2, 1, 1, 2, 3, 3, 5]
def baseStart_749073 : Nat := 118140960795 + 749073 * 2 ^ 59
def prefixEnd_749073 : Nat := 4983230072969 + 3 ^ 40 * 749073 * 2
def baseEnd_749073 : Nat := 341897328271513761904517

theorem tailTrace_749073 : CollatzResearch.WordTrace tailWord_749073 prefixEnd_749073 341897328271513761904517 := by
  unfold tailWord_749073
  simp only [CollatzResearch.WordTrace]
  refine ⟨27320936815243927328363873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18213957876829284885575915 27320936815243927328363873)
  ·
    refine ⟨20490702611432945496272905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27320936815243927328363873 20490702611432945496272905)
    ·
      refine ⟨15368026958574709122204679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20490702611432945496272905 15368026958574709122204679)
      ·
        refine ⟨23052040437862063683307019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15368026958574709122204679 23052040437862063683307019)
        ·
          refine ⟨34578060656793095524960529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23052040437862063683307019 34578060656793095524960529)
          ·
            refine ⟨25933545492594821643720397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34578060656793095524960529 25933545492594821643720397)
            ·
              refine ⟨9725079559723058116395149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25933545492594821643720397 9725079559723058116395149)
              ·
                refine ⟨3646904834896146793648181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9725079559723058116395149 3646904834896146793648181)
                ·
                  refine ⟨341897328271513761904517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3646904834896146793648181 341897328271513761904517)
                  ·
                    rfl

theorem cell20_749073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 3, 5].length) (baseStart_749073 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_749073 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_749073 prefixEnd_749073 := by exact prefixLift 749073
  have htrace : WordTrace (prefixWord ++ tailWord_749073) baseStart_749073 baseEnd_749073 := by
    simpa [prefixWord, tailWord_749073, baseEnd_749073] using wordTrace_append hprefix tailTrace_749073
  have hstable : (prefixWord ++ tailWord_749073).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749073).length < 2 ^ (prefixWord ++ tailWord_749073).sum := by decide
  have hdescent : baseEnd_749073 < baseStart_749073 := by decide
  rcases family_descends (prefixWord ++ tailWord_749073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749114 : List Nat := [3, 1, 1, 1, 3, 2, 2, 5, 2]
def baseStart_749114 : Nat := 118140960795 + 749114 * 2 ^ 59
def prefixEnd_749114 : Nat := 4983230072969 + 3 ^ 40 * 749114 * 2
def baseEnd_749114 : Nat := 341916041788699841537683

theorem tailTrace_749114 : CollatzResearch.WordTrace tailWord_749114 prefixEnd_749114 341916041788699841537683 := by
  unfold tailWord_749114
  simp only [CollatzResearch.WordTrace]
  refine ⟨6830608052023847832651599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18214954805396927553737597 6830608052023847832651599)
  ·
    refine ⟨10245912078035771748977399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6830608052023847832651599 10245912078035771748977399)
    ·
      refine ⟨15368868117053657623466099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10245912078035771748977399 15368868117053657623466099)
      ·
        refine ⟨23053302175580486435199149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15368868117053657623466099 23053302175580486435199149)
        ·
          refine ⟨8644988315842682413199681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23053302175580486435199149 8644988315842682413199681)
          ·
            refine ⟨6483741236882011809899761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8644988315842682413199681 6483741236882011809899761)
            ·
              refine ⟨4862805927661508857424821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6483741236882011809899761 4862805927661508857424821)
              ·
                refine ⟨455888055718266455383577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4862805927661508857424821 455888055718266455383577)
                ·
                  refine ⟨341916041788699841537683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 455888055718266455383577 341916041788699841537683)
                  ·
                    rfl

theorem cell20_749114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 5, 2].length) (baseStart_749114 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_749114 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_749114 prefixEnd_749114 := by exact prefixLift 749114
  have htrace : WordTrace (prefixWord ++ tailWord_749114) baseStart_749114 baseEnd_749114 := by
    simpa [prefixWord, tailWord_749114, baseEnd_749114] using wordTrace_append hprefix tailTrace_749114
  have hstable : (prefixWord ++ tailWord_749114).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749114).length < 2 ^ (prefixWord ++ tailWord_749114).sum := by decide
  have hdescent : baseEnd_749114 < baseStart_749114 := by decide
  rcases family_descends (prefixWord ++ tailWord_749114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749127 : List Nat := [1, 1, 4, 1, 6, 1, 2, 2, 2]
def baseStart_749127 : Nat := 118140960795 + 749127 * 2 ^ 59
def prefixEnd_749127 : Nat := 4983230072969 + 3 ^ 40 * 749127 * 2
def baseEnd_749127 : Nat := 341921975342929574104297

theorem tailTrace_749127 : CollatzResearch.WordTrace tailWord_749127 prefixEnd_749127 341921975342929574104297 := by
  unfold tailWord_749127
  simp only [CollatzResearch.WordTrace]
  refine ⟨27322906357048294550829635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18215270904698863033886423 27322906357048294550829635)
  ·
    refine ⟨40984359535572441826244453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27322906357048294550829635 40984359535572441826244453)
    ·
      refine ⟨7684567412919832842420835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40984359535572441826244453 7684567412919832842420835)
      ·
        refine ⟨11526851119379749263631253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7684567412919832842420835 11526851119379749263631253)
        ·
          refine ⟨540321146220925746732715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 11526851119379749263631253 540321146220925746732715)
          ·
            refine ⟨810481719331388620099073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 540321146220925746732715 810481719331388620099073)
            ·
              refine ⟨607861289498541465074305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 810481719331388620099073 607861289498541465074305)
              ·
                refine ⟨455895967123906098805729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 607861289498541465074305 455895967123906098805729)
                ·
                  refine ⟨341921975342929574104297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 455895967123906098805729 341921975342929574104297)
                  ·
                    rfl

theorem cell20_749127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 2, 2, 2].length) (baseStart_749127 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_749127 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_749127 prefixEnd_749127 := by exact prefixLift 749127
  have htrace : WordTrace (prefixWord ++ tailWord_749127) baseStart_749127 baseEnd_749127 := by
    simpa [prefixWord, tailWord_749127, baseEnd_749127] using wordTrace_append hprefix tailTrace_749127
  have hstable : (prefixWord ++ tailWord_749127).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749127).length < 2 ^ (prefixWord ++ tailWord_749127).sum := by decide
  have hdescent : baseEnd_749127 < baseStart_749127 := by decide
  rcases family_descends (prefixWord ++ tailWord_749127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749214 : List Nat := [4, 3, 1, 1, 1, 2, 4, 4]
def baseStart_749214 : Nat := 118140960795 + 749214 * 2 ^ 59
def prefixEnd_749214 : Nat := 4983230072969 + 3 ^ 40 * 749214 * 2
def baseEnd_749214 : Nat := 113987228171181312734647

theorem tailTrace_749214 : CollatzResearch.WordTrace tailWord_749214 prefixEnd_749214 113987228171181312734647 := by
  unfold tailWord_749214
  simp only [CollatzResearch.WordTrace]
  refine ⟨3415759938466638551155837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18217386338488738939497797 3415759938466638551155837)
  ·
    refine ⟨1280909976924989456683439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3415759938466638551155837 1280909976924989456683439)
    ·
      refine ⟨1921364965387484185025159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1280909976924989456683439 1921364965387484185025159)
      ·
        refine ⟨2882047448081226277537739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1921364965387484185025159 2882047448081226277537739)
        ·
          refine ⟨4323071172121839416306609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2882047448081226277537739 4323071172121839416306609)
          ·
            refine ⟨3242303379091379562229957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4323071172121839416306609 3242303379091379562229957)
            ·
              refine ⟨607931883579633667918117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3242303379091379562229957 607931883579633667918117)
              ·
                refine ⟨113987228171181312734647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 607931883579633667918117 113987228171181312734647)
                ·
                  rfl

theorem cell20_749214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 4, 4].length) (baseStart_749214 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_749214 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_749214 prefixEnd_749214 := by exact prefixLift 749214
  have htrace : WordTrace (prefixWord ++ tailWord_749214) baseStart_749214 baseEnd_749214 := by
    simpa [prefixWord, tailWord_749214, baseEnd_749214] using wordTrace_append hprefix tailTrace_749214
  have hstable : (prefixWord ++ tailWord_749214).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749214).length < 2 ^ (prefixWord ++ tailWord_749214).sum := by decide
  have hdescent : baseEnd_749214 < baseStart_749214 := by decide
  rcases family_descends (prefixWord ++ tailWord_749214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749232 : List Nat := [2, 1, 1, 1, 2, 1, 4, 2, 6]
def baseStart_749232 : Nat := 118140960795 + 749232 * 2 ^ 59
def prefixEnd_749232 : Nat := 4983230072969 + 3 ^ 40 * 749232 * 2
def baseEnd_749232 : Nat := 341969900204015875603867

theorem tailTrace_749232 : CollatzResearch.WordTrace tailWord_749232 prefixEnd_749232 341969900204015875603867 := by
  unfold tailWord_749232
  simp only [CollatzResearch.WordTrace]
  refine ⟨13663368010833948741700975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18217824014445264988934633 13663368010833948741700975)
  ·
    refine ⟨20495052016250923112551463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13663368010833948741700975 20495052016250923112551463)
    ·
      refine ⟨30742578024376384668827195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20495052016250923112551463 30742578024376384668827195)
      ·
        refine ⟨46113867036564577003240793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30742578024376384668827195 46113867036564577003240793)
        ·
          refine ⟨34585400277423432752430595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46113867036564577003240793 34585400277423432752430595)
          ·
            refine ⟨51878100416135149128645893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34585400277423432752430595 51878100416135149128645893)
            ·
              refine ⟨9727143828025340461621105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51878100416135149128645893 9727143828025340461621105)
              ·
                refine ⟨7295357871019005346215829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9727143828025340461621105 7295357871019005346215829)
                ·
                  refine ⟨341969900204015875603867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7295357871019005346215829 341969900204015875603867)
                  ·
                    rfl

theorem cell20_749232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 2, 6].length) (baseStart_749232 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_749232 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_749232 prefixEnd_749232 := by exact prefixLift 749232
  have htrace : WordTrace (prefixWord ++ tailWord_749232) baseStart_749232 baseEnd_749232 := by
    simpa [prefixWord, tailWord_749232, baseEnd_749232] using wordTrace_append hprefix tailTrace_749232
  have hstable : (prefixWord ++ tailWord_749232).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749232).length < 2 ^ (prefixWord ++ tailWord_749232).sum := by decide
  have hdescent : baseEnd_749232 < baseStart_749232 := by decide
  rcases family_descends (prefixWord ++ tailWord_749232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749245 : List Nat := [1, 4, 1, 2, 1, 2, 5, 2, 2]
def baseStart_749245 : Nat := 118140960795 + 749245 * 2 ^ 59
def prefixEnd_749245 : Nat := 4983230072969 + 3 ^ 40 * 749245 * 2
def baseEnd_749245 : Nat := 341975833758245608170481

theorem tailTrace_749245 : CollatzResearch.WordTrace tailWord_749245 prefixEnd_749245 341975833758245608170481 := by
  unfold tailWord_749245
  simp only [CollatzResearch.WordTrace]
  refine ⟨27327210170620800703625189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18218140113747200469083459 27327210170620800703625189)
  ·
    refine ⟨5123851906991400131929723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27327210170620800703625189 5123851906991400131929723)
    ·
      refine ⟨7685777860487100197894585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5123851906991400131929723 7685777860487100197894585)
      ·
        refine ⟨5764333395365325148420939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7685777860487100197894585 5764333395365325148420939)
        ·
          refine ⟨8646500093047987722631409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5764333395365325148420939 8646500093047987722631409)
          ·
            refine ⟨6484875069785990791973557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8646500093047987722631409 6484875069785990791973557)
            ·
              refine ⟨607957037792436636747521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6484875069785990791973557 607957037792436636747521)
              ·
                refine ⟨455967778344327477560641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 607957037792436636747521 455967778344327477560641)
                ·
                  refine ⟨341975833758245608170481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 455967778344327477560641 341975833758245608170481)
                  ·
                    rfl

theorem cell20_749245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 5, 2, 2].length) (baseStart_749245 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_749245 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_749245 prefixEnd_749245 := by exact prefixLift 749245
  have htrace : WordTrace (prefixWord ++ tailWord_749245) baseStart_749245 baseEnd_749245 := by
    simpa [prefixWord, tailWord_749245, baseEnd_749245] using wordTrace_append hprefix tailTrace_749245
  have hstable : (prefixWord ++ tailWord_749245).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749245).length < 2 ^ (prefixWord ++ tailWord_749245).sum := by decide
  have hdescent : baseEnd_749245 < baseStart_749245 := by decide
  rcases family_descends (prefixWord ++ tailWord_749245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749256 : List Nat := [2, 1, 3, 1, 2, 2, 4, 5]
def baseStart_749256 : Nat := 118140960795 + 749256 * 2 ^ 59
def prefixEnd_749256 : Nat := 4983230072969 + 3 ^ 40 * 749256 * 2
def baseEnd_749256 : Nat := 113993618152659486267923

theorem tailTrace_749256 : CollatzResearch.WordTrace tailWord_749256 prefixEnd_749256 113993618152659486267923 := by
  unfold tailWord_749256
  simp only [CollatzResearch.WordTrace]
  refine ⟨13663805686790474791137811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18218407582387299721517081 13663805686790474791137811)
  ·
    refine ⟨20495708530185712186706717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13663805686790474791137811 20495708530185712186706717)
    ·
      refine ⟨7685890698819642070015019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20495708530185712186706717 7685890698819642070015019)
      ·
        refine ⟨11528836048229463105022529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7685890698819642070015019 11528836048229463105022529)
        ·
          refine ⟨8646627036172097328766897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11528836048229463105022529 8646627036172097328766897)
          ·
            refine ⟨6484970277129072996575173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8646627036172097328766897 6484970277129072996575173)
            ·
              refine ⟨1215931926961701186857845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6484970277129072996575173 1215931926961701186857845)
              ·
                refine ⟨113993618152659486267923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1215931926961701186857845 113993618152659486267923)
                ·
                  rfl

theorem cell20_749256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 4, 5].length) (baseStart_749256 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_749256 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_749256 prefixEnd_749256 := by exact prefixLift 749256
  have htrace : WordTrace (prefixWord ++ tailWord_749256) baseStart_749256 baseEnd_749256 := by
    simpa [prefixWord, tailWord_749256, baseEnd_749256] using wordTrace_append hprefix tailTrace_749256
  have hstable : (prefixWord ++ tailWord_749256).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749256).length < 2 ^ (prefixWord ++ tailWord_749256).sum := by decide
  have hdescent : baseEnd_749256 < baseStart_749256 := by decide
  rcases family_descends (prefixWord ++ tailWord_749256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749356 : List Nat := [2, 2, 1, 1, 1, 5, 3, 2, 3]
def baseStart_749356 : Nat := 118140960795 + 749356 * 2 ^ 59
def prefixEnd_749356 : Nat := 4983230072969 + 3 ^ 40 * 749356 * 2
def baseEnd_749356 : Nat := 342026497182822555470027

theorem tailTrace_749356 : CollatzResearch.WordTrace tailWord_749356 prefixEnd_749356 342026497182822555470027 := by
  unfold tailWord_749356
  simp only [CollatzResearch.WordTrace]
  refine ⟨13665629336609333330457961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18220839115479111107277281 13665629336609333330457961)
  ·
    refine ⟨10249222002456999997843471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13665629336609333330457961 10249222002456999997843471)
    ·
      refine ⟨15373833003685499996765207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10249222002456999997843471 15373833003685499996765207)
      ·
        refine ⟨23060749505528249995147811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15373833003685499996765207 23060749505528249995147811)
        ·
          refine ⟨34591124258292374992721717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23060749505528249995147811 34591124258292374992721717)
          ·
            refine ⟨3242917899214910155567661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34591124258292374992721717 3242917899214910155567661)
            ·
              refine ⟨1216094212205591308337873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3242917899214910155567661 1216094212205591308337873)
              ·
                refine ⟨912070659154193481253405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1216094212205591308337873 912070659154193481253405)
                ·
                  refine ⟨342026497182822555470027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 912070659154193481253405 342026497182822555470027)
                  ·
                    rfl

theorem cell20_749356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 3].length) (baseStart_749356 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_749356 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_749356 prefixEnd_749356 := by exact prefixLift 749356
  have htrace : WordTrace (prefixWord ++ tailWord_749356) baseStart_749356 baseEnd_749356 := by
    simpa [prefixWord, tailWord_749356, baseEnd_749356] using wordTrace_append hprefix tailTrace_749356
  have hstable : (prefixWord ++ tailWord_749356).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749356).length < 2 ^ (prefixWord ++ tailWord_749356).sum := by decide
  have hdescent : baseEnd_749356 < baseStart_749356 := by decide
  rcases family_descends (prefixWord ++ tailWord_749356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749397 : List Nat := [1, 3, 2, 2, 2, 4, 1, 3, 2]
def baseStart_749397 : Nat := 118140960795 + 749397 * 2 ^ 59
def prefixEnd_749397 : Nat := 4983230072969 + 3 ^ 40 * 749397 * 2
def baseEnd_749397 : Nat := 342045210700008635103193

theorem tailTrace_749397 : CollatzResearch.WordTrace tailWord_749397 prefixEnd_749397 342045210700008635103193 := by
  unfold tailWord_749397
  simp only [CollatzResearch.WordTrace]
  refine ⟨27332754066070130663158445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18221836044046753775438963 27332754066070130663158445)
  ·
    refine ⟨10249782774776298998684417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27332754066070130663158445 10249782774776298998684417)
    ·
      refine ⟨7687337081082224249013313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10249782774776298998684417 7687337081082224249013313)
      ·
        refine ⟨5765502810811668186759985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7687337081082224249013313 5765502810811668186759985)
        ·
          refine ⟨4324127108108751140069989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5765502810811668186759985 4324127108108751140069989)
          ·
            refine ⟨810773832770390838763123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4324127108108751140069989 810773832770390838763123)
            ·
              refine ⟨1216160749155586258144685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 810773832770390838763123 1216160749155586258144685)
              ·
                refine ⟨456060280933344846804257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1216160749155586258144685 456060280933344846804257)
                ·
                  refine ⟨342045210700008635103193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 456060280933344846804257 342045210700008635103193)
                  ·
                    rfl

theorem cell20_749397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 1, 3, 2].length) (baseStart_749397 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_749397 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_749397 prefixEnd_749397 := by exact prefixLift 749397
  have htrace : WordTrace (prefixWord ++ tailWord_749397) baseStart_749397 baseEnd_749397 := by
    simpa [prefixWord, tailWord_749397, baseEnd_749397] using wordTrace_append hprefix tailTrace_749397
  have hstable : (prefixWord ++ tailWord_749397).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749397).length < 2 ^ (prefixWord ++ tailWord_749397).sum := by decide
  have hdescent : baseEnd_749397 < baseStart_749397 := by decide
  rcases family_descends (prefixWord ++ tailWord_749397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749404 : List Nat := [2, 2, 4, 2, 3, 1, 6]
def baseStart_749404 : Nat := 118140960795 + 749404 * 2 ^ 59
def prefixEnd_749404 : Nat := 4983230072969 + 3 ^ 40 * 749404 * 2
def baseEnd_749404 : Nat := 38005378410083080207759

theorem tailTrace_749404 : CollatzResearch.WordTrace tailWord_749404 prefixEnd_749404 38005378410083080207759 := by
  unfold tailWord_749404
  simp only [CollatzResearch.WordTrace]
  refine ⟨13666504688522385429331633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18222006251363180572442177 13666504688522385429331633)
  ·
    refine ⟨10249878516391789071998725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13666504688522385429331633 10249878516391789071998725)
    ·
      refine ⟨1921852221823460450999761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10249878516391789071998725 1921852221823460450999761)
      ·
        refine ⟨1441389166367595338249821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1921852221823460450999761 1441389166367595338249821)
        ·
          refine ⟨540520937387848251843683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1441389166367595338249821 540520937387848251843683)
          ·
            refine ⟨810781406081772377765525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 540520937387848251843683 810781406081772377765525)
            ·
              refine ⟨38005378410083080207759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 810781406081772377765525 38005378410083080207759)
              ·
                rfl

theorem cell20_749404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 6].length) (baseStart_749404 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_749404 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_749404 prefixEnd_749404 := by exact prefixLift 749404
  have htrace : WordTrace (prefixWord ++ tailWord_749404) baseStart_749404 baseEnd_749404 := by
    simpa [prefixWord, tailWord_749404, baseEnd_749404] using wordTrace_append hprefix tailTrace_749404
  have hstable : (prefixWord ++ tailWord_749404).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749404).length < 2 ^ (prefixWord ++ tailWord_749404).sum := by decide
  have hdescent : baseEnd_749404 < baseStart_749404 := by decide
  rcases family_descends (prefixWord ++ tailWord_749404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749408 : List Nat := [2, 1, 1, 3, 3, 4, 6]
def baseStart_749408 : Nat := 118140960795 + 749408 * 2 ^ 59
def prefixEnd_749408 : Nat := 4983230072969 + 3 ^ 40 * 749408 * 2
def baseEnd_749408 : Nat := 38005581266637942859609

theorem tailTrace_749408 : CollatzResearch.WordTrace tailWord_749408 prefixEnd_749408 38005581266637942859609 := by
  unfold tailWord_749408
  simp only [CollatzResearch.WordTrace]
  refine ⟨13666577634515139770904439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18222103512686853027872585 13666577634515139770904439)
  ·
    refine ⟨20499866451772709656356659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13666577634515139770904439 20499866451772709656356659)
    ·
      refine ⟨30749799677659064484534989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20499866451772709656356659 30749799677659064484534989)
      ·
        refine ⟨11531174879122149181700621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30749799677659064484534989 11531174879122149181700621)
        ·
          refine ⟨4324190579670805943137733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11531174879122149181700621 4324190579670805943137733)
          ·
            refine ⟨810785733688276114338325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4324190579670805943137733 810785733688276114338325)
            ·
              refine ⟨38005581266637942859609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 810785733688276114338325 38005581266637942859609)
              ·
                rfl

theorem cell20_749408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 6].length) (baseStart_749408 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_749408 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_749408 prefixEnd_749408 := by exact prefixLift 749408
  have htrace : WordTrace (prefixWord ++ tailWord_749408) baseStart_749408 baseEnd_749408 := by
    simpa [prefixWord, tailWord_749408, baseEnd_749408] using wordTrace_append hprefix tailTrace_749408
  have hstable : (prefixWord ++ tailWord_749408).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749408).length < 2 ^ (prefixWord ++ tailWord_749408).sum := by decide
  have hdescent : baseEnd_749408 < baseStart_749408 := by decide
  rcases family_descends (prefixWord ++ tailWord_749408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749415 : List Nat := [1, 1, 5, 1, 2, 1, 1, 3, 5]
def baseStart_749415 : Nat := 118140960795 + 749415 * 2 ^ 59
def prefixEnd_749415 : Nat := 4983230072969 + 3 ^ 40 * 749415 * 2
def baseEnd_749415 : Nat := 342053426390480572503119

theorem tailTrace_749415 : CollatzResearch.WordTrace tailWord_749415 prefixEnd_749415 342053426390480572503119 := by
  unfold tailWord_749415
  simp only [CollatzResearch.WordTrace]
  refine ⟨27333410580004919737313699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18222273720003279824875799 27333410580004919737313699)
  ·
    refine ⟨41000115870007379605970549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27333410580004919737313699 41000115870007379605970549)
    ·
      refine ⟨3843760862813191838059739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 41000115870007379605970549 3843760862813191838059739)
      ·
        refine ⟨5765641294219787757089609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3843760862813191838059739 5765641294219787757089609)
        ·
          refine ⟨4324230970664840817817207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5765641294219787757089609 4324230970664840817817207)
          ·
            refine ⟨6486346455997261226725811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4324230970664840817817207 6486346455997261226725811)
            ·
              refine ⟨9729519683995891840088717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6486346455997261226725811 9729519683995891840088717)
              ·
                refine ⟨3648569881498459440033269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9729519683995891840088717 3648569881498459440033269)
                ·
                  refine ⟨342053426390480572503119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3648569881498459440033269 342053426390480572503119)
                  ·
                    rfl

theorem cell20_749415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 3, 5].length) (baseStart_749415 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_749415 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_749415 prefixEnd_749415 := by exact prefixLift 749415
  have htrace : WordTrace (prefixWord ++ tailWord_749415) baseStart_749415 baseEnd_749415 := by
    simpa [prefixWord, tailWord_749415, baseEnd_749415] using wordTrace_append hprefix tailTrace_749415
  have hstable : (prefixWord ++ tailWord_749415).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749415).length < 2 ^ (prefixWord ++ tailWord_749415).sum := by decide
  have hdescent : baseEnd_749415 < baseStart_749415 := by decide
  rcases family_descends (prefixWord ++ tailWord_749415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749473 : List Nat := [1, 2, 3, 4, 2, 1, 1, 4, 2]
def baseStart_749473 : Nat := 118140960795 + 749473 * 2 ^ 59
def prefixEnd_749473 : Nat := 4983230072969 + 3 ^ 40 * 749473 * 2
def baseEnd_749473 : Nat := 342079899170890148569549

theorem tailTrace_749473 : CollatzResearch.WordTrace tailWord_749473 prefixEnd_749473 342079899170890148569549 := by
  unfold tailWord_749473
  simp only [CollatzResearch.WordTrace]
  refine ⟨27335526013794795642925073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18223684009196530428616715 27335526013794795642925073)
  ·
    refine ⟨20501644510346096732193805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27335526013794795642925073 20501644510346096732193805)
    ·
      refine ⟨7688116691379786274572677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20501644510346096732193805 7688116691379786274572677)
      ·
        refine ⟨1441521879633709926482377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7688116691379786274572677 1441521879633709926482377)
        ·
          refine ⟨1081141409725282444861783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1441521879633709926482377 1081141409725282444861783)
          ·
            refine ⟨1621712114587923667292675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1081141409725282444861783 1621712114587923667292675)
            ·
              refine ⟨2432568171881885500939013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1621712114587923667292675 2432568171881885500939013)
              ·
                refine ⟨456106532227853531426065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2432568171881885500939013 456106532227853531426065)
                ·
                  refine ⟨342079899170890148569549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 456106532227853531426065 342079899170890148569549)
                  ·
                    rfl

theorem cell20_749473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 4, 2].length) (baseStart_749473 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_749473 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_749473 prefixEnd_749473 := by exact prefixLift 749473
  have htrace : WordTrace (prefixWord ++ tailWord_749473) baseStart_749473 baseEnd_749473 := by
    simpa [prefixWord, tailWord_749473, baseEnd_749473] using wordTrace_append hprefix tailTrace_749473
  have hstable : (prefixWord ++ tailWord_749473).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749473).length < 2 ^ (prefixWord ++ tailWord_749473).sum := by decide
  have hdescent : baseEnd_749473 < baseStart_749473 := by decide
  rcases family_descends (prefixWord ++ tailWord_749473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749491 : List Nat := [1, 1, 1, 2, 3, 1, 3, 5, 3]
def baseStart_749491 : Nat := 118140960795 + 749491 * 2 ^ 59
def prefixEnd_749491 : Nat := 4983230072969 + 3 ^ 40 * 749491 * 2
def baseEnd_749491 : Nat := 342088114861362085969475

theorem tailTrace_749491 : CollatzResearch.WordTrace tailWord_749491 prefixEnd_749491 342088114861362085969475 := by
  unfold tailWord_749491
  simp only [CollatzResearch.WordTrace]
  refine ⟨27336182527729584717080327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18224121685153056478053551 27336182527729584717080327)
  ·
    refine ⟨41004273791594377075620491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27336182527729584717080327 41004273791594377075620491)
    ·
      refine ⟨61506410687391565613430737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41004273791594377075620491 61506410687391565613430737)
      ·
        refine ⟨46129808015543674210073053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61506410687391565613430737 46129808015543674210073053)
        ·
          refine ⟨17298678005828877828777395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46129808015543674210073053 17298678005828877828777395)
          ·
            refine ⟨25948017008743316743166093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17298678005828877828777395 25948017008743316743166093)
            ·
              refine ⟨9730506378278743778687285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25948017008743316743166093 9730506378278743778687285)
              ·
                refine ⟨912234972963632229251933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9730506378278743778687285 912234972963632229251933)
                ·
                  refine ⟨342088114861362085969475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 912234972963632229251933 342088114861362085969475)
                  ·
                    rfl

theorem cell20_749491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 5, 3].length) (baseStart_749491 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_749491 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_749491 prefixEnd_749491 := by exact prefixLift 749491
  have htrace : WordTrace (prefixWord ++ tailWord_749491) baseStart_749491 baseEnd_749491 := by
    simpa [prefixWord, tailWord_749491, baseEnd_749491] using wordTrace_append hprefix tailTrace_749491
  have hstable : (prefixWord ++ tailWord_749491).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749491).length < 2 ^ (prefixWord ++ tailWord_749491).sum := by decide
  have hdescent : baseEnd_749491 < baseStart_749491 := by decide
  rcases family_descends (prefixWord ++ tailWord_749491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749501 : List Nat := [1, 4, 1, 2, 3, 2, 3, 4]
def baseStart_749501 : Nat := 118140960795 + 749501 * 2 ^ 59
def prefixEnd_749501 : Nat := 4983230072969 + 3 ^ 40 * 749501 * 2
def baseEnd_749501 : Nat := 114030893044615498545367

theorem tailTrace_749501 : CollatzResearch.WordTrace tailWord_749501 prefixEnd_749501 114030893044615498545367 := by
  unfold tailWord_749501
  simp only [CollatzResearch.WordTrace]
  refine ⟨27336547257693356424944357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18224364838462237616629571 27336547257693356424944357)
  ·
    refine ⟨5125602610817504329677067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27336547257693356424944357 5125602610817504329677067)
    ·
      refine ⟨7688403916226256494515601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5125602610817504329677067 7688403916226256494515601)
      ·
        refine ⟨5766302937169692370886701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7688403916226256494515601 5766302937169692370886701)
        ·
          refine ⟨2162363601438634639082513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5766302937169692370886701 2162363601438634639082513)
          ·
            refine ⟨1621772701078975979311885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2162363601438634639082513 1621772701078975979311885)
            ·
              refine ⟨608164762904615992241957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1621772701078975979311885 608164762904615992241957)
              ·
                refine ⟨114030893044615498545367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 608164762904615992241957 114030893044615498545367)
                ·
                  rfl

theorem cell20_749501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 3, 4].length) (baseStart_749501 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_749501 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_749501 prefixEnd_749501 := by exact prefixLift 749501
  have htrace : WordTrace (prefixWord ++ tailWord_749501) baseStart_749501 baseEnd_749501 := by
    simpa [prefixWord, tailWord_749501, baseEnd_749501] using wordTrace_append hprefix tailTrace_749501
  have hstable : (prefixWord ++ tailWord_749501).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749501).length < 2 ^ (prefixWord ++ tailWord_749501).sum := by decide
  have hdescent : baseEnd_749501 < baseStart_749501 := by decide
  rcases family_descends (prefixWord ++ tailWord_749501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749525 : List Nat := [1, 3, 2, 3, 2, 3, 1, 2, 3]
def baseStart_749525 : Nat := 118140960795 + 749525 * 2 ^ 59
def prefixEnd_749525 : Nat := 4983230072969 + 3 ^ 40 * 749525 * 2
def baseEnd_749525 : Nat := 342103633387809078836003

theorem tailTrace_749525 : CollatzResearch.WordTrace tailWord_749525 prefixEnd_749525 342103633387809078836003 := by
  unfold tailWord_749525
  simp only [CollatzResearch.WordTrace]
  refine ⟨27337422609606408523818029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18224948406404272349212019 27337422609606408523818029)
  ·
    refine ⟨10251533478602403196431761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27337422609606408523818029 10251533478602403196431761)
    ·
      refine ⟨7688650108951802397323821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10251533478602403196431761 7688650108951802397323821)
      ·
        refine ⟨2883243790856925898996433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7688650108951802397323821 2883243790856925898996433)
        ·
          refine ⟨2162432843142694424247325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2883243790856925898996433 2162432843142694424247325)
          ·
            refine ⟨810912316178510409092747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2162432843142694424247325 810912316178510409092747)
            ·
              refine ⟨1216368474267765613639121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 810912316178510409092747 1216368474267765613639121)
              ·
                refine ⟨912276355700824210229341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1216368474267765613639121 912276355700824210229341)
                ·
                  refine ⟨342103633387809078836003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 912276355700824210229341 342103633387809078836003)
                  ·
                    rfl

theorem cell20_749525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 1, 2, 3].length) (baseStart_749525 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_749525 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_749525 prefixEnd_749525 := by exact prefixLift 749525
  have htrace : WordTrace (prefixWord ++ tailWord_749525) baseStart_749525 baseEnd_749525 := by
    simpa [prefixWord, tailWord_749525, baseEnd_749525] using wordTrace_append hprefix tailTrace_749525
  have hstable : (prefixWord ++ tailWord_749525).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749525).length < 2 ^ (prefixWord ++ tailWord_749525).sum := by decide
  have hdescent : baseEnd_749525 < baseStart_749525 := by decide
  rcases family_descends (prefixWord ++ tailWord_749525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749560 : List Nat := [2, 1, 2, 1, 1, 3, 6, 4]
def baseStart_749560 : Nat := 118140960795 + 749560 * 2 ^ 59
def prefixEnd_749560 : Nat := 4983230072969 + 3 ^ 40 * 749560 * 2
def baseEnd_749560 : Nat := 114039869447168170889731

theorem tailTrace_749560 : CollatzResearch.WordTrace tailWord_749560 prefixEnd_749560 114039869447168170889731 := by
  unfold tailWord_749560
  simp only [CollatzResearch.WordTrace]
  refine ⟨13669349582239804750671067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18225799442986406334228089 13669349582239804750671067)
  ·
    refine ⟨20504024373359707126006601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13669349582239804750671067 20504024373359707126006601)
    ·
      refine ⟨15378018280019780344504951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20504024373359707126006601 15378018280019780344504951)
      ·
        refine ⟨23067027420029670516757427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15378018280019780344504951 23067027420029670516757427)
        ·
          refine ⟨34600541130044505775136141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23067027420029670516757427 34600541130044505775136141)
          ·
            refine ⟨12975202923766689665676053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34600541130044505775136141 12975202923766689665676053)
            ·
              refine ⟨608212637051563578078565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 12975202923766689665676053 608212637051563578078565)
              ·
                refine ⟨114039869447168170889731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 608212637051563578078565 114039869447168170889731)
                ·
                  rfl

theorem cell20_749560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 6, 4].length) (baseStart_749560 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_749560 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_749560 prefixEnd_749560 := by exact prefixLift 749560
  have htrace : WordTrace (prefixWord ++ tailWord_749560) baseStart_749560 baseEnd_749560 := by
    simpa [prefixWord, tailWord_749560, baseEnd_749560] using wordTrace_append hprefix tailTrace_749560
  have hstable : (prefixWord ++ tailWord_749560).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749560).length < 2 ^ (prefixWord ++ tailWord_749560).sum := by decide
  have hdescent : baseEnd_749560 < baseStart_749560 := by decide
  rcases family_descends (prefixWord ++ tailWord_749560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749566 : List Nat := [4, 2, 2, 2, 1, 3, 1, 3, 2]
def baseStart_749566 : Nat := 118140960795 + 749566 * 2 ^ 59
def prefixEnd_749566 : Nat := 4983230072969 + 3 ^ 40 * 749566 * 2
def baseEnd_749566 : Nat := 342122346904995158469169

theorem tailTrace_749566 : CollatzResearch.WordTrace tailWord_749566 prefixEnd_749566 342122346904995158469169 := by
  unfold tailWord_749566
  simp only [CollatzResearch.WordTrace]
  refine ⟨3417364750307234065757569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18225945334971915017373701 3417364750307234065757569)
  ·
    refine ⟨2563023562730425549318177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3417364750307234065757569 2563023562730425549318177)
    ·
      refine ⟨1922267672047819161988633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2563023562730425549318177 1922267672047819161988633)
      ·
        refine ⟨1441700754035864371491475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1922267672047819161988633 1441700754035864371491475)
        ·
          refine ⟨2162551131053796557237213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1441700754035864371491475 2162551131053796557237213)
          ·
            refine ⟨810956674145173708963955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2162551131053796557237213 810956674145173708963955)
            ·
              refine ⟨1216435011217760563445933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 810956674145173708963955 1216435011217760563445933)
              ·
                refine ⟨456163129206660211292225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1216435011217760563445933 456163129206660211292225)
                ·
                  refine ⟨342122346904995158469169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 456163129206660211292225 342122346904995158469169)
                  ·
                    rfl

theorem cell20_749566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 1, 3, 2].length) (baseStart_749566 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_749566 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_749566 prefixEnd_749566 := by exact prefixLift 749566
  have htrace : WordTrace (prefixWord ++ tailWord_749566) baseStart_749566 baseEnd_749566 := by
    simpa [prefixWord, tailWord_749566, baseEnd_749566] using wordTrace_append hprefix tailTrace_749566
  have hstable : (prefixWord ++ tailWord_749566).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749566).length < 2 ^ (prefixWord ++ tailWord_749566).sum := by decide
  have hdescent : baseEnd_749566 < baseStart_749566 := by decide
  rcases family_descends (prefixWord ++ tailWord_749566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749619 : List Nat := [1, 1, 1, 2, 4, 1, 4, 6]
def baseStart_749619 : Nat := 118140960795 + 749619 * 2 ^ 59
def prefixEnd_749619 : Nat := 4983230072969 + 3 ^ 40 * 749619 * 2
def baseEnd_749619 : Nat := 114048845849720843234095

theorem tailTrace_749619 : CollatzResearch.WordTrace tailWord_749619 prefixEnd_749619 114048845849720843234095 := by
  unfold tailWord_749619
  simp only [CollatzResearch.WordTrace]
  refine ⟨27340851071265862577739911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18227234047510575051826607 27340851071265862577739911)
  ·
    refine ⟨41011276606898793866609867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27340851071265862577739911 41011276606898793866609867)
    ·
      refine ⟨61516914910348190799914801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41011276606898793866609867 61516914910348190799914801)
      ·
        refine ⟨46137686182761143099936101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61516914910348190799914801 46137686182761143099936101)
        ·
          refine ⟨8650816159267714331238019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46137686182761143099936101 8650816159267714331238019)
          ·
            refine ⟨12976224238901571496857029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8650816159267714331238019 12976224238901571496857029)
            ·
              refine ⟨2433042044794044655660693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12976224238901571496857029 2433042044794044655660693)
              ·
                refine ⟨114048845849720843234095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2433042044794044655660693 114048845849720843234095)
                ·
                  rfl

theorem cell20_749619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 6].length) (baseStart_749619 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_749619 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_749619 prefixEnd_749619 := by exact prefixLift 749619
  have htrace : WordTrace (prefixWord ++ tailWord_749619) baseStart_749619 baseEnd_749619 := by
    simpa [prefixWord, tailWord_749619, baseEnd_749619] using wordTrace_append hprefix tailTrace_749619
  have hstable : (prefixWord ++ tailWord_749619).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749619).length < 2 ^ (prefixWord ++ tailWord_749619).sum := by decide
  have hdescent : baseEnd_749619 < baseStart_749619 := by decide
  rcases family_descends (prefixWord ++ tailWord_749619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749646 : List Nat := [4, 1, 1, 1, 1, 5, 1, 4, 2]
def baseStart_749646 : Nat := 118140960795 + 749646 * 2 ^ 59
def prefixEnd_749646 : Nat := 4983230072969 + 3 ^ 40 * 749646 * 2
def baseEnd_749646 : Nat := 342158861084870435802175

theorem tailTrace_749646 : CollatzResearch.WordTrace tailWord_749646 prefixEnd_749646 342158861084870435802175 := by
  unfold tailWord_749646
  simp only [CollatzResearch.WordTrace]
  refine ⟨3417729480271005773621599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18227890561445364125981861 3417729480271005773621599)
  ·
    refine ⟨5126594220406508660432399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3417729480271005773621599 5126594220406508660432399)
    ·
      refine ⟨7689891330609762990648599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5126594220406508660432399 7689891330609762990648599)
      ·
        refine ⟨11534836995914644485972899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7689891330609762990648599 11534836995914644485972899)
        ·
          refine ⟨17302255493871966728959349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11534836995914644485972899 17302255493871966728959349)
          ·
            refine ⟨1622086452550496880839939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17302255493871966728959349 1622086452550496880839939)
            ·
              refine ⟨2433129678825745321259909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1622086452550496880839939 2433129678825745321259909)
              ·
                refine ⟨456211814779827247736233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2433129678825745321259909 456211814779827247736233)
                ·
                  refine ⟨342158861084870435802175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 456211814779827247736233 342158861084870435802175)
                  ·
                    rfl

theorem cell20_749646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 4, 2].length) (baseStart_749646 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_749646 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_749646 prefixEnd_749646 := by exact prefixLift 749646
  have htrace : WordTrace (prefixWord ++ tailWord_749646) baseStart_749646 baseEnd_749646 := by
    simpa [prefixWord, tailWord_749646, baseEnd_749646] using wordTrace_append hprefix tailTrace_749646
  have hstable : (prefixWord ++ tailWord_749646).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749646).length < 2 ^ (prefixWord ++ tailWord_749646).sum := by decide
  have hdescent : baseEnd_749646 < baseStart_749646 := by decide
  rcases family_descends (prefixWord ++ tailWord_749646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749660 : List Nat := [2, 2, 4, 1, 1, 2, 2, 3, 3]
def baseStart_749660 : Nat := 118140960795 + 749660 * 2 ^ 59
def prefixEnd_749660 : Nat := 4983230072969 + 3 ^ 40 * 749660 * 2
def baseEnd_749660 : Nat := 342165251066348609335451

theorem tailTrace_749660 : CollatzResearch.WordTrace tailWord_749660 prefixEnd_749660 342165251066348609335451 := by
  unfold tailWord_749660
  simp only [CollatzResearch.WordTrace]
  refine ⟨13671173232058663289991217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18228230976078217719988289 13671173232058663289991217)
  ·
    refine ⟨10253379924043997467493413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13671173232058663289991217 10253379924043997467493413)
    ·
      refine ⟨1922508735758249525155015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10253379924043997467493413 1922508735758249525155015)
      ·
        refine ⟨2883763103637374287732523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1922508735758249525155015 2883763103637374287732523)
        ·
          refine ⟨4325644655456061431598785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2883763103637374287732523 4325644655456061431598785)
          ·
            refine ⟨3244233491592046073699089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4325644655456061431598785 3244233491592046073699089)
            ·
              refine ⟨2433175118694034555274317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3244233491592046073699089 2433175118694034555274317)
              ·
                refine ⟨912440669510262958227869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2433175118694034555274317 912440669510262958227869)
                ·
                  refine ⟨342165251066348609335451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 912440669510262958227869 342165251066348609335451)
                  ·
                    rfl

theorem cell20_749660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 3, 3].length) (baseStart_749660 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_749660 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_749660 prefixEnd_749660 := by exact prefixLift 749660
  have htrace : WordTrace (prefixWord ++ tailWord_749660) baseStart_749660 baseEnd_749660 := by
    simpa [prefixWord, tailWord_749660, baseEnd_749660] using wordTrace_append hprefix tailTrace_749660
  have hstable : (prefixWord ++ tailWord_749660).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749660).length < 2 ^ (prefixWord ++ tailWord_749660).sum := by decide
  have hdescent : baseEnd_749660 < baseStart_749660 := by decide
  rcases family_descends (prefixWord ++ tailWord_749660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749705 : List Nat := [1, 2, 1, 1, 4, 2, 1, 6, 2]
def baseStart_749705 : Nat := 118140960795 + 749705 * 2 ^ 59
def prefixEnd_749705 : Nat := 4983230072969 + 3 ^ 40 * 749705 * 2
def baseEnd_749705 : Nat := 342185790292528452835267

theorem tailTrace_749705 : CollatzResearch.WordTrace tailWord_749705 prefixEnd_749705 342185790292528452835267 := by
  unfold tailWord_749705
  simp only [CollatzResearch.WordTrace]
  refine ⟨27343987748954299265370569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18229325165969532843580379 27343987748954299265370569)
  ·
    refine ⟨20507990811715724449027927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27343987748954299265370569 20507990811715724449027927)
    ·
      refine ⟨30761986217573586673541891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20507990811715724449027927 30761986217573586673541891)
      ·
        refine ⟨46142979326360380010312837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30761986217573586673541891 46142979326360380010312837)
        ·
          refine ⟨8651808623692571251933657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46142979326360380010312837 8651808623692571251933657)
          ·
            refine ⟨6488856467769428438950243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8651808623692571251933657 6488856467769428438950243)
            ·
              refine ⟨9733284701654142658425365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6488856467769428438950243 9733284701654142658425365)
              ·
                refine ⟨456247720390037937113689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9733284701654142658425365 456247720390037937113689)
                ·
                  refine ⟨342185790292528452835267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 456247720390037937113689 342185790292528452835267)
                  ·
                    rfl

theorem cell20_749705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 6, 2].length) (baseStart_749705 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_749705 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_749705 prefixEnd_749705 := by exact prefixLift 749705
  have htrace : WordTrace (prefixWord ++ tailWord_749705) baseStart_749705 baseEnd_749705 := by
    simpa [prefixWord, tailWord_749705, baseEnd_749705] using wordTrace_append hprefix tailTrace_749705
  have hstable : (prefixWord ++ tailWord_749705).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749705).length < 2 ^ (prefixWord ++ tailWord_749705).sum := by decide
  have hdescent : baseEnd_749705 < baseStart_749705 := by decide
  rcases family_descends (prefixWord ++ tailWord_749705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749729 : List Nat := [1, 2, 3, 3, 1, 4, 2, 4]
def baseStart_749729 : Nat := 118140960795 + 749729 * 2 ^ 59
def prefixEnd_749729 : Nat := 4983230072969 + 3 ^ 40 * 749729 * 2
def baseEnd_749729 : Nat := 114065581515497012011723

theorem tailTrace_749729 : CollatzResearch.WordTrace tailWord_749729 prefixEnd_749729 114065581515497012011723 := by
  unfold tailWord_749729
  simp only [CollatzResearch.WordTrace]
  refine ⟨27344863100867351364244241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18229908733911567576162827 27344863100867351364244241)
  ·
    refine ⟨20508647325650513523183181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27344863100867351364244241 20508647325650513523183181)
    ·
      refine ⟨7690742747118942571193693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20508647325650513523183181 7690742747118942571193693)
      ·
        refine ⟨2884028530169603464197635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7690742747118942571193693 2884028530169603464197635)
        ·
          refine ⟨4326042795254405196296453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2884028530169603464197635 4326042795254405196296453)
          ·
            refine ⟨811133024110200974305585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4326042795254405196296453 811133024110200974305585)
            ·
              refine ⟨608349768082650730729189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 811133024110200974305585 608349768082650730729189)
              ·
                refine ⟨114065581515497012011723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 608349768082650730729189 114065581515497012011723)
                ·
                  rfl

theorem cell20_749729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 2, 4].length) (baseStart_749729 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_749729 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_749729 prefixEnd_749729 := by exact prefixLift 749729
  have htrace : WordTrace (prefixWord ++ tailWord_749729) baseStart_749729 baseEnd_749729 := by
    simpa [prefixWord, tailWord_749729, baseEnd_749729] using wordTrace_append hprefix tailTrace_749729
  have hstable : (prefixWord ++ tailWord_749729).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749729).length < 2 ^ (prefixWord ++ tailWord_749729).sum := by decide
  have hdescent : baseEnd_749729 < baseStart_749729 := by decide
  rcases family_descends (prefixWord ++ tailWord_749729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749733 : List Nat := [1, 3, 1, 2, 1, 3, 3, 6]
def baseStart_749733 : Nat := 118140960795 + 749733 * 2 ^ 59
def prefixEnd_749733 : Nat := 4983230072969 + 3 ^ 40 * 749733 * 2
def baseEnd_749733 : Nat := 114066190085161599967273

theorem tailTrace_749733 : CollatzResearch.WordTrace tailWord_749733 prefixEnd_749733 114066190085161599967273 := by
  unfold tailWord_749733
  simp only [CollatzResearch.WordTrace]
  refine ⟨27345008992852860047389853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18230005995235240031593235 27345008992852860047389853)
  ·
    refine ⟨10254378372319822517771195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27345008992852860047389853 10254378372319822517771195)
    ·
      refine ⟨15381567558479733776656793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10254378372319822517771195 15381567558479733776656793)
      ·
        refine ⟨11536175668859800332492595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15381567558479733776656793 11536175668859800332492595)
        ·
          refine ⟨17304263503289700498738893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11536175668859800332492595 17304263503289700498738893)
          ·
            refine ⟨6489098813733637687027085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17304263503289700498738893 6489098813733637687027085)
            ·
              refine ⟨2433412055150114132635157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6489098813733637687027085 2433412055150114132635157)
              ·
                refine ⟨114066190085161599967273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2433412055150114132635157 114066190085161599967273)
                ·
                  rfl

theorem cell20_749733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 6].length) (baseStart_749733 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_749733 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_749733 prefixEnd_749733 := by exact prefixLift 749733
  have htrace : WordTrace (prefixWord ++ tailWord_749733) baseStart_749733 baseEnd_749733 := by
    simpa [prefixWord, tailWord_749733, baseEnd_749733] using wordTrace_append hprefix tailTrace_749733
  have hstable : (prefixWord ++ tailWord_749733).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749733).length < 2 ^ (prefixWord ++ tailWord_749733).sum := by decide
  have hdescent : baseEnd_749733 < baseStart_749733 := by decide
  rcases family_descends (prefixWord ++ tailWord_749733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749757 : List Nat := [1, 4, 1, 2, 1, 1, 1, 6, 3]
def baseStart_749757 : Nat := 118140960795 + 749757 * 2 ^ 59
def prefixEnd_749757 : Nat := 4983230072969 + 3 ^ 40 * 749757 * 2
def baseEnd_749757 : Nat := 342209524509447383101721

theorem tailTrace_749757 : CollatzResearch.WordTrace tailWord_749757 prefixEnd_749757 342209524509447383101721 := by
  unfold tailWord_749757
  simp only [CollatzResearch.WordTrace]
  refine ⟨27345884344765912146263525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18230589563177274764175683 27345884344765912146263525)
  ·
    refine ⟨5127353314643608527424411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27345884344765912146263525 5127353314643608527424411)
    ·
      refine ⟨7691029971965412791136617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5127353314643608527424411 7691029971965412791136617)
      ·
        refine ⟨5768272478974059593352463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7691029971965412791136617 5768272478974059593352463)
        ·
          refine ⟨8652408718461089390028695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5768272478974059593352463 8652408718461089390028695)
          ·
            refine ⟨12978613077691634085043043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8652408718461089390028695 12978613077691634085043043)
            ·
              refine ⟨19467919616537451127564565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12978613077691634085043043 19467919616537451127564565)
              ·
                refine ⟨912558732025193021604589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 19467919616537451127564565 912558732025193021604589)
                ·
                  refine ⟨342209524509447383101721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 912558732025193021604589 342209524509447383101721)
                  ·
                    rfl

theorem cell20_749757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 6, 3].length) (baseStart_749757 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_749757 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_749757 prefixEnd_749757 := by exact prefixLift 749757
  have htrace : WordTrace (prefixWord ++ tailWord_749757) baseStart_749757 baseEnd_749757 := by
    simpa [prefixWord, tailWord_749757, baseEnd_749757] using wordTrace_append hprefix tailTrace_749757
  have hstable : (prefixWord ++ tailWord_749757).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749757).length < 2 ^ (prefixWord ++ tailWord_749757).sum := by decide
  have hdescent : baseEnd_749757 < baseStart_749757 := by decide
  rcases family_descends (prefixWord ++ tailWord_749757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749771 : List Nat := [1, 1, 1, 1, 3, 2, 6, 5]
def baseStart_749771 : Nat := 118140960795 + 749771 * 2 ^ 59
def prefixEnd_749771 : Nat := 4983230072969 + 3 ^ 40 * 749771 * 2
def baseEnd_749771 : Nat := 114071971496975185544999

theorem tailTrace_749771 : CollatzResearch.WordTrace tailWord_749771 prefixEnd_749771 114071971496975185544999 := by
  unfold tailWord_749771
  simp only [CollatzResearch.WordTrace]
  refine ⟨27346394966715192537273167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18230929977810128358182111 27346394966715192537273167)
  ·
    refine ⟨41019592450072788805909751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27346394966715192537273167 41019592450072788805909751)
    ·
      refine ⟨61529388675109183208864627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41019592450072788805909751 61529388675109183208864627)
      ·
        refine ⟨92294083012663774813296941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61529388675109183208864627 92294083012663774813296941)
        ·
          refine ⟨34610281129748915554986353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92294083012663774813296941 34610281129748915554986353)
          ·
            refine ⟨25957710847311686666239765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34610281129748915554986353 25957710847311686666239765)
            ·
              refine ⟨1216767695967735312479989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 25957710847311686666239765 1216767695967735312479989)
              ·
                refine ⟨114071971496975185544999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1216767695967735312479989 114071971496975185544999)
                ·
                  rfl

theorem cell20_749771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 6, 5].length) (baseStart_749771 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_749771 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_749771 prefixEnd_749771 := by exact prefixLift 749771
  have htrace : WordTrace (prefixWord ++ tailWord_749771) baseStart_749771 baseEnd_749771 := by
    simpa [prefixWord, tailWord_749771, baseEnd_749771] using wordTrace_append hprefix tailTrace_749771
  have hstable : (prefixWord ++ tailWord_749771).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749771).length < 2 ^ (prefixWord ++ tailWord_749771).sum := by decide
  have hdescent : baseEnd_749771 < baseStart_749771 := by decide
  rcases family_descends (prefixWord ++ tailWord_749771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749774 : List Nat := [4, 1, 1, 1, 4, 2, 1, 3, 3]
def baseStart_749774 : Nat := 118140960795 + 749774 * 2 ^ 59
def prefixEnd_749774 : Nat := 4983230072969 + 3 ^ 40 * 749774 * 2
def baseEnd_749774 : Nat := 342217283772670879534985

theorem tailTrace_749774 : CollatzResearch.WordTrace tailWord_749774 prefixEnd_749774 342217283772670879534985 := by
  unfold tailWord_749774
  simp only [CollatzResearch.WordTrace]
  refine ⟨3418313048213040506204047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18231002923802882699754917 3418313048213040506204047)
  ·
    refine ⟨5127469572319560759306071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3418313048213040506204047 5127469572319560759306071)
    ·
      refine ⟨7691204358479341138959107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5127469572319560759306071 7691204358479341138959107)
      ·
        refine ⟨11536806537719011708438661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7691204358479341138959107 11536806537719011708438661)
        ·
          refine ⟨2163151225822314695332249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11536806537719011708438661 2163151225822314695332249)
          ·
            refine ⟨1622363419366736021499187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2163151225822314695332249 1622363419366736021499187)
            ·
              refine ⟨2433545129050104032248781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1622363419366736021499187 2433545129050104032248781)
              ·
                refine ⟨912579423393789012093293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2433545129050104032248781 912579423393789012093293)
                ·
                  refine ⟨342217283772670879534985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 912579423393789012093293 342217283772670879534985)
                  ·
                    rfl

theorem cell20_749774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 3, 3].length) (baseStart_749774 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_749774 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_749774 prefixEnd_749774 := by exact prefixLift 749774
  have htrace : WordTrace (prefixWord ++ tailWord_749774) baseStart_749774 baseEnd_749774 := by
    simpa [prefixWord, tailWord_749774, baseEnd_749774] using wordTrace_append hprefix tailTrace_749774
  have hstable : (prefixWord ++ tailWord_749774).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749774).length < 2 ^ (prefixWord ++ tailWord_749774).sum := by decide
  have hdescent : baseEnd_749774 < baseStart_749774 := by decide
  rcases family_descends (prefixWord ++ tailWord_749774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749816 : List Nat := [2, 1, 2, 1, 1, 2, 1, 5, 5]
def baseStart_749816 : Nat := 118140960795 + 749816 * 2 ^ 59
def prefixEnd_749816 : Nat := 4983230072969 + 3 ^ 40 * 749816 * 2
def baseEnd_749816 : Nat := 342236453717105400134813

theorem tailTrace_749816 : CollatzResearch.WordTrace tailWord_749816 prefixEnd_749816 342236453717105400134813 := by
  unfold tailWord_749816
  simp only [CollatzResearch.WordTrace]
  refine ⟨13674018125776082611330651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18232024167701443481774201 13674018125776082611330651)
  ·
    refine ⟨20511027188664123916995977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13674018125776082611330651 20511027188664123916995977)
    ·
      refine ⟨15383270391498092937746983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20511027188664123916995977 15383270391498092937746983)
      ·
        refine ⟨23074905587247139406620475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15383270391498092937746983 23074905587247139406620475)
        ·
          refine ⟨34612358380870709109930713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23074905587247139406620475 34612358380870709109930713)
          ·
            refine ⟨25959268785653031832448035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34612358380870709109930713 25959268785653031832448035)
            ·
              refine ⟨38938903178479547748672053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25959268785653031832448035 38938903178479547748672053)
              ·
                refine ⟨3650522172982457601438005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38938903178479547748672053 3650522172982457601438005)
                ·
                  refine ⟨342236453717105400134813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3650522172982457601438005 342236453717105400134813)
                  ·
                    rfl

theorem cell20_749816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 5, 5].length) (baseStart_749816 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_749816 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_749816 prefixEnd_749816 := by exact prefixLift 749816
  have htrace : WordTrace (prefixWord ++ tailWord_749816) baseStart_749816 baseEnd_749816 := by
    simpa [prefixWord, tailWord_749816, baseEnd_749816] using wordTrace_append hprefix tailTrace_749816
  have hstable : (prefixWord ++ tailWord_749816).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749816).length < 2 ^ (prefixWord ++ tailWord_749816).sum := by decide
  have hdescent : baseEnd_749816 < baseStart_749816 := by decide
  rcases family_descends (prefixWord ++ tailWord_749816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749833 : List Nat := [1, 2, 1, 1, 3, 4, 2, 3, 3]
def baseStart_749833 : Nat := 118140960795 + 749833 * 2 ^ 59
def prefixEnd_749833 : Nat := 4983230072969 + 3 ^ 40 * 749833 * 2
def baseEnd_749833 : Nat := 342244212980328896568077

theorem tailTrace_749833 : CollatzResearch.WordTrace tailWord_749833 prefixEnd_749833 342244212980328896568077 := by
  unfold tailWord_749833
  simp only [CollatzResearch.WordTrace]
  refine ⟨27348656292490577126030153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18232437528327051417353435 27348656292490577126030153)
  ·
    refine ⟨20511492219367932844522615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27348656292490577126030153 20511492219367932844522615)
    ·
      refine ⟨30767238329051899266783923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20511492219367932844522615 30767238329051899266783923)
      ·
        refine ⟨46150857493577848900175885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30767238329051899266783923 46150857493577848900175885)
        ·
          refine ⟨17306571560091693337565957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46150857493577848900175885 17306571560091693337565957)
          ·
            refine ⟨3244982167517192500793617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17306571560091693337565957 3244982167517192500793617)
            ·
              refine ⟨2433736625637894375595213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3244982167517192500793617 2433736625637894375595213)
              ·
                refine ⟨912651234614210390848205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2433736625637894375595213 912651234614210390848205)
                ·
                  refine ⟨342244212980328896568077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 912651234614210390848205 342244212980328896568077)
                  ·
                    rfl

theorem cell20_749833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 3, 3].length) (baseStart_749833 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_749833 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_749833 prefixEnd_749833 := by exact prefixLift 749833
  have htrace : WordTrace (prefixWord ++ tailWord_749833) baseStart_749833 baseEnd_749833 := by
    simpa [prefixWord, tailWord_749833, baseEnd_749833] using wordTrace_append hprefix tailTrace_749833
  have hstable : (prefixWord ++ tailWord_749833).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749833).length < 2 ^ (prefixWord ++ tailWord_749833).sum := by decide
  have hdescent : baseEnd_749833 < baseStart_749833 := by decide
  rcases family_descends (prefixWord ++ tailWord_749833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749853 : List Nat := [1, 4, 2, 3, 2, 1, 2, 3, 2]
def baseStart_749853 : Nat := 118140960795 + 749853 * 2 ^ 59
def prefixEnd_749853 : Nat := 4983230072969 + 3 ^ 40 * 749853 * 2
def baseEnd_749853 : Nat := 342253341525297715901329

theorem tailTrace_749853 : CollatzResearch.WordTrace tailWord_749853 prefixEnd_749853 342253341525297715901329 := by
  unfold tailWord_749853
  simp only [CollatzResearch.WordTrace]
  refine ⟨27349385752418120541758213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18232923834945413694505475 27349385752418120541758213)
  ·
    refine ⟨5128009828578397601579665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27349385752418120541758213 5128009828578397601579665)
    ·
      refine ⟨3846007371433798201184749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5128009828578397601579665 3846007371433798201184749)
      ·
        refine ⟨1442252764287674325444281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3846007371433798201184749 1442252764287674325444281)
        ·
          refine ⟨1081689573215755744083211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1442252764287674325444281 1081689573215755744083211)
          ·
            refine ⟨1622534359823633616124817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1081689573215755744083211 1622534359823633616124817)
            ·
              refine ⟨1216900769867725212093613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1622534359823633616124817 1216900769867725212093613)
              ·
                refine ⟨456337788700396954535105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1216900769867725212093613 456337788700396954535105)
                ·
                  refine ⟨342253341525297715901329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 456337788700396954535105 342253341525297715901329)
                  ·
                    rfl

theorem cell20_749853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 2, 3, 2].length) (baseStart_749853 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_749853 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_749853 prefixEnd_749853 := by exact prefixLift 749853
  have htrace : WordTrace (prefixWord ++ tailWord_749853) baseStart_749853 baseEnd_749853 := by
    simpa [prefixWord, tailWord_749853, baseEnd_749853] using wordTrace_append hprefix tailTrace_749853
  have hstable : (prefixWord ++ tailWord_749853).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749853).length < 2 ^ (prefixWord ++ tailWord_749853).sum := by decide
  have hdescent : baseEnd_749853 < baseStart_749853 := by decide
  rcases family_descends (prefixWord ++ tailWord_749853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749857 : List Nat := [1, 2, 3, 2, 1, 1, 3, 5, 2]
def baseStart_749857 : Nat := 118140960795 + 749857 * 2 ^ 59
def prefixEnd_749857 : Nat := 4983230072969 + 3 ^ 40 * 749857 * 2
def baseEnd_749857 : Nat := 342255167234291479767979

theorem tailTrace_749857 : CollatzResearch.WordTrace tailWord_749857 prefixEnd_749857 342255167234291479767979 := by
  unfold tailWord_749857
  simp only [CollatzResearch.WordTrace]
  refine ⟨27349531644403629224903825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18233021096269086149935883 27349531644403629224903825)
  ·
    refine ⟨20512148733302721918677869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27349531644403629224903825 20512148733302721918677869)
    ·
      refine ⟨7692055774988520719504201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20512148733302721918677869 7692055774988520719504201)
      ·
        refine ⟨5769041831241390539628151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7692055774988520719504201 5769041831241390539628151)
        ·
          refine ⟨8653562746862085809442227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5769041831241390539628151 8653562746862085809442227)
          ·
            refine ⟨12980344120293128714163341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8653562746862085809442227 12980344120293128714163341)
            ·
              refine ⟨4867629045109923267811253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12980344120293128714163341 4867629045109923267811253)
              ·
                refine ⟨456340222979055306357305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4867629045109923267811253 456340222979055306357305)
                ·
                  refine ⟨342255167234291479767979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 456340222979055306357305 342255167234291479767979)
                  ·
                    rfl

theorem cell20_749857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 5, 2].length) (baseStart_749857 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_749857 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_749857 prefixEnd_749857 := by exact prefixLift 749857
  have htrace : WordTrace (prefixWord ++ tailWord_749857) baseStart_749857 baseEnd_749857 := by
    simpa [prefixWord, tailWord_749857, baseEnd_749857] using wordTrace_append hprefix tailTrace_749857
  have hstable : (prefixWord ++ tailWord_749857).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749857).length < 2 ^ (prefixWord ++ tailWord_749857).sum := by decide
  have hdescent : baseEnd_749857 < baseStart_749857 := by decide
  rcases family_descends (prefixWord ++ tailWord_749857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749863 : List Nat := [1, 1, 8, 1, 1, 2, 1, 2, 3]
def baseStart_749863 : Nat := 118140960795 + 749863 * 2 ^ 59
def prefixEnd_749863 : Nat := 4983230072969 + 3 ^ 40 * 749863 * 2
def baseEnd_749863 : Nat := 342257905797782125567955

theorem tailTrace_749863 : CollatzResearch.WordTrace tailWord_749863 prefixEnd_749863 342257905797782125567955 := by
  unfold tailWord_749863
  simp only [CollatzResearch.WordTrace]
  refine ⟨27349750482381892249622243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18233166988254594833081495 27349750482381892249622243)
  ·
    refine ⟨41024625723572838374433365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27349750482381892249622243 41024625723572838374433365)
    ·
      refine ⟨480757332698119199700391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 41024625723572838374433365 480757332698119199700391)
      ·
        refine ⟨721135999047178799550587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 480757332698119199700391 721135999047178799550587)
        ·
          refine ⟨1081703998570768199325881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 721135999047178799550587 1081703998570768199325881)
          ·
            refine ⟨811277998928076149494411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1081703998570768199325881 811277998928076149494411)
            ·
              refine ⟨1216916998392114224241617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 811277998928076149494411 1216916998392114224241617)
              ·
                refine ⟨912687748794085668181213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1216916998392114224241617 912687748794085668181213)
                ·
                  refine ⟨342257905797782125567955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 912687748794085668181213 342257905797782125567955)
                  ·
                    rfl

theorem cell20_749863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 1, 2, 3].length) (baseStart_749863 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_749863 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_749863 prefixEnd_749863 := by exact prefixLift 749863
  have htrace : WordTrace (prefixWord ++ tailWord_749863) baseStart_749863 baseEnd_749863 := by
    simpa [prefixWord, tailWord_749863, baseEnd_749863] using wordTrace_append hprefix tailTrace_749863
  have hstable : (prefixWord ++ tailWord_749863).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749863).length < 2 ^ (prefixWord ++ tailWord_749863).sum := by decide
  have hdescent : baseEnd_749863 < baseStart_749863 := by decide
  rcases family_descends (prefixWord ++ tailWord_749863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749864 : List Nat := [2, 1, 5, 1, 3, 1, 7]
def baseStart_749864 : Nat := 118140960795 + 749864 * 2 ^ 59
def prefixEnd_749864 : Nat := 4983230072969 + 3 ^ 40 * 749864 * 2
def baseEnd_749864 : Nat := 38028706913892285170513

theorem tailTrace_749864 : CollatzResearch.WordTrace tailWord_749864 prefixEnd_749864 38028706913892285170513 := by
  unfold tailWord_749864
  simp only [CollatzResearch.WordTrace]
  refine ⟨13674893477689134710204323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18233191303585512946939097 13674893477689134710204323)
  ·
    refine ⟨20512340216533702065306485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13674893477689134710204323 20512340216533702065306485)
    ·
      refine ⟨1923031895300034568622483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20512340216533702065306485 1923031895300034568622483)
      ·
        refine ⟨2884547842950051852933725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1923031895300034568622483 2884547842950051852933725)
        ·
          refine ⟨1081705441106269444850147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2884547842950051852933725 1081705441106269444850147)
          ·
            refine ⟨1622558161659404167275221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1081705441106269444850147 1622558161659404167275221)
            ·
              refine ⟨38028706913892285170513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1622558161659404167275221 38028706913892285170513)
              ·
                rfl

theorem cell20_749864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 7].length) (baseStart_749864 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_749864 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_749864 prefixEnd_749864 := by exact prefixLift 749864
  have htrace : WordTrace (prefixWord ++ tailWord_749864) baseStart_749864 baseEnd_749864 := by
    simpa [prefixWord, tailWord_749864, baseEnd_749864] using wordTrace_append hprefix tailTrace_749864
  have hstable : (prefixWord ++ tailWord_749864).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749864).length < 2 ^ (prefixWord ++ tailWord_749864).sum := by decide
  have hdescent : baseEnd_749864 < baseStart_749864 := by decide
  rcases family_descends (prefixWord ++ tailWord_749864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749871 : List Nat := [1, 1, 2, 1, 2, 1, 7, 2, 3]
def baseStart_749871 : Nat := 118140960795 + 749871 * 2 ^ 59
def prefixEnd_749871 : Nat := 4983230072969 + 3 ^ 40 * 749871 * 2
def baseEnd_749871 : Nat := 342261557215769653301255

theorem tailTrace_749871 : CollatzResearch.WordTrace tailWord_749871 prefixEnd_749871 342261557215769653301255 := by
  unfold tailWord_749871
  simp only [CollatzResearch.WordTrace]
  refine ⟨27350042266352909615913467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18233361510901939743942311 27350042266352909615913467)
  ·
    refine ⟨41025063399529364423870201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27350042266352909615913467 41025063399529364423870201)
    ·
      refine ⟨30768797549647023317902651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41025063399529364423870201 30768797549647023317902651)
      ·
        refine ⟨46153196324470534976853977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30768797549647023317902651 46153196324470534976853977)
        ·
          refine ⟨34614897243352901232640483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46153196324470534976853977 34614897243352901232640483)
          ·
            refine ⟨51922345865029351848960725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34614897243352901232640483 51922345865029351848960725)
            ·
              refine ⟨1216929981211625433960017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 51922345865029351848960725 1216929981211625433960017)
              ·
                refine ⟨912697485908719075470013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1216929981211625433960017 912697485908719075470013)
                ·
                  refine ⟨342261557215769653301255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 912697485908719075470013 342261557215769653301255)
                  ·
                    rfl

theorem cell20_749871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 7, 2, 3].length) (baseStart_749871 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_749871 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_749871 prefixEnd_749871 := by exact prefixLift 749871
  have htrace : WordTrace (prefixWord ++ tailWord_749871) baseStart_749871 baseEnd_749871 := by
    simpa [prefixWord, tailWord_749871, baseEnd_749871] using wordTrace_append hprefix tailTrace_749871
  have hstable : (prefixWord ++ tailWord_749871).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749871).length < 2 ^ (prefixWord ++ tailWord_749871).sum := by decide
  have hdescent : baseEnd_749871 < baseStart_749871 := by decide
  rcases family_descends (prefixWord ++ tailWord_749871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749899 : List Nat := [1, 1, 1, 1, 3, 1, 1, 5, 6]
def baseStart_749899 : Nat := 118140960795 + 749899 * 2 ^ 59
def prefixEnd_749899 : Nat := 4983230072969 + 3 ^ 40 * 749899 * 2
def baseEnd_749899 : Nat := 342274337178726000367807

theorem tailTrace_749899 : CollatzResearch.WordTrace tailWord_749899 prefixEnd_749899 342274337178726000367807 := by
  unfold tailWord_749899
  simp only [CollatzResearch.WordTrace]
  refine ⟨27351063510251470397932751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18234042340167646931955167 27351063510251470397932751)
  ·
    refine ⟨41026595265377205596899127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27351063510251470397932751 41026595265377205596899127)
    ·
      refine ⟨61539892898065808395348691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41026595265377205596899127 61539892898065808395348691)
      ·
        refine ⟨92309839347098712593023037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61539892898065808395348691 92309839347098712593023037)
        ·
          refine ⟨34616189755162017222383639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92309839347098712593023037 34616189755162017222383639)
          ·
            refine ⟨51924284632743025833575459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34616189755162017222383639 51924284632743025833575459)
            ·
              refine ⟨77886426949114538750363189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51924284632743025833575459 77886426949114538750363189)
              ·
                refine ⟨7301852526479488007846549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 77886426949114538750363189 7301852526479488007846549)
                ·
                  refine ⟨342274337178726000367807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7301852526479488007846549 342274337178726000367807)
                  ·
                    rfl

theorem cell20_749899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 5, 6].length) (baseStart_749899 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_749899 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_749899 prefixEnd_749899 := by exact prefixLift 749899
  have htrace : WordTrace (prefixWord ++ tailWord_749899) baseStart_749899 baseEnd_749899 := by
    simpa [prefixWord, tailWord_749899, baseEnd_749899] using wordTrace_append hprefix tailTrace_749899
  have hstable : (prefixWord ++ tailWord_749899).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749899).length < 2 ^ (prefixWord ++ tailWord_749899).sum := by decide
  have hdescent : baseEnd_749899 < baseStart_749899 := by decide
  rcases family_descends (prefixWord ++ tailWord_749899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749947 : List Nat := [1, 1, 1, 1, 1, 8, 1, 3, 3]
def baseStart_749947 : Nat := 118140960795 + 749947 * 2 ^ 59
def prefixEnd_749947 : Nat := 4983230072969 + 3 ^ 40 * 749947 * 2
def baseEnd_749947 : Nat := 342296245686651166767611

theorem tailTrace_749947 : CollatzResearch.WordTrace tailWord_749947 prefixEnd_749947 342296245686651166767611 := by
  unfold tailWord_749947
  simp only [CollatzResearch.WordTrace]
  refine ⟨27352814214077574595680095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18235209476051716397120063 27352814214077574595680095)
  ·
    refine ⟨41029221321116361893520143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27352814214077574595680095 41029221321116361893520143)
    ·
      refine ⟨61543831981674542840280215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41029221321116361893520143 61543831981674542840280215)
      ·
        refine ⟨92315747972511814260420323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61543831981674542840280215 92315747972511814260420323)
        ·
          refine ⟨138473621958767721390630485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92315747972511814260420323 138473621958767721390630485)
          ·
            refine ⟨1622737757329309235046451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 138473621958767721390630485 1622737757329309235046451)
            ·
              refine ⟨2434106635993963852569677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1622737757329309235046451 2434106635993963852569677)
              ·
                refine ⟨912789988497736444713629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2434106635993963852569677 912789988497736444713629)
                ·
                  refine ⟨342296245686651166767611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 912789988497736444713629 342296245686651166767611)
                  ·
                    rfl

theorem cell20_749947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 3, 3].length) (baseStart_749947 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_749947 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_749947 prefixEnd_749947 := by exact prefixLift 749947
  have htrace : WordTrace (prefixWord ++ tailWord_749947) baseStart_749947 baseEnd_749947 := by
    simpa [prefixWord, tailWord_749947, baseEnd_749947] using wordTrace_append hprefix tailTrace_749947
  have hstable : (prefixWord ++ tailWord_749947).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749947).length < 2 ^ (prefixWord ++ tailWord_749947).sum := by decide
  have hdescent : baseEnd_749947 < baseStart_749947 := by decide
  rcases family_descends (prefixWord ++ tailWord_749947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749961 : List Nat := [1, 2, 1, 1, 6, 1, 2, 6]
def baseStart_749961 : Nat := 118140960795 + 749961 * 2 ^ 59
def prefixEnd_749961 : Nat := 4983230072969 + 3 ^ 40 * 749961 * 2
def baseEnd_749961 : Nat := 114100878556043113433629

theorem tailTrace_749961 : CollatzResearch.WordTrace tailWord_749961 prefixEnd_749961 114100878556043113433629 := by
  unfold tailWord_749961
  simp only [CollatzResearch.WordTrace]
  refine ⟨27353324836026854986689737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18235549890684569991126491 27353324836026854986689737)
  ·
    refine ⟨20514993627020141240017303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27353324836026854986689737 20514993627020141240017303)
    ·
      refine ⟨30772490440530211860025955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20514993627020141240017303 30772490440530211860025955)
      ·
        refine ⟨46158735660795317790038933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30772490440530211860025955 46158735660795317790038933)
        ·
          refine ⟨2163690734099780521408075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 46158735660795317790038933 2163690734099780521408075)
          ·
            refine ⟨3245536101149670782112113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2163690734099780521408075 3245536101149670782112113)
            ·
              refine ⟨2434152075862253086584085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3245536101149670782112113 2434152075862253086584085)
              ·
                refine ⟨114100878556043113433629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2434152075862253086584085 114100878556043113433629)
                ·
                  rfl

theorem cell20_749961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 6].length) (baseStart_749961 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_749961 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_749961 prefixEnd_749961 := by exact prefixLift 749961
  have htrace : WordTrace (prefixWord ++ tailWord_749961) baseStart_749961 baseEnd_749961 := by
    simpa [prefixWord, tailWord_749961, baseEnd_749961] using wordTrace_append hprefix tailTrace_749961
  have hstable : (prefixWord ++ tailWord_749961).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749961).length < 2 ^ (prefixWord ++ tailWord_749961).sum := by decide
  have hdescent : baseEnd_749961 < baseStart_749961 := by decide
  rcases family_descends (prefixWord ++ tailWord_749961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749974 : List Nat := [5, 3, 1, 2, 1, 8]
def baseStart_749974 : Nat := 118140960795 + 749974 * 2 ^ 59
def prefixEnd_749974 : Nat := 4983230072969 + 3 ^ 40 * 749974 * 2
def baseEnd_749974 : Nat := 12678095156383669365463

theorem tailTrace_749974 : CollatzResearch.WordTrace tailWord_749974 prefixEnd_749974 12678095156383669365463 := by
  unfold tailWord_749974
  simp only [CollatzResearch.WordTrace]
  refine ⟨1709612436561234887932061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18235865989986505471275317 1709612436561234887932061)
  ·
    refine ⟨641104663710463082974523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1709612436561234887932061 641104663710463082974523)
    ·
      refine ⟨961656995565694624461785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 641104663710463082974523 961656995565694624461785)
      ·
        refine ⟨721242746674270968346339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 961656995565694624461785 721242746674270968346339)
        ·
          refine ⟨1081864120011406452519509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 721242746674270968346339 1081864120011406452519509)
          ·
            refine ⟨12678095156383669365463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1081864120011406452519509 12678095156383669365463)
            ·
              rfl

theorem cell20_749974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 8].length) (baseStart_749974 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_749974 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_749974 prefixEnd_749974 := by exact prefixLift 749974
  have htrace : WordTrace (prefixWord ++ tailWord_749974) baseStart_749974 baseEnd_749974 := by
    simpa [prefixWord, tailWord_749974, baseEnd_749974] using wordTrace_append hprefix tailTrace_749974
  have hstable : (prefixWord ++ tailWord_749974).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749974).length < 2 ^ (prefixWord ++ tailWord_749974).sum := by decide
  have hdescent : baseEnd_749974 < baseStart_749974 := by decide
  rcases family_descends (prefixWord ++ tailWord_749974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749988 : List Nat := [2, 3, 1, 2, 1, 1, 6, 2, 2]
def baseStart_749988 : Nat := 118140960795 + 749988 * 2 ^ 59
def prefixEnd_749988 : Nat := 4983230072969 + 3 ^ 40 * 749988 * 2
def baseEnd_749988 : Nat := 342314959203837246400777

theorem tailTrace_749988 : CollatzResearch.WordTrace tailWord_749988 prefixEnd_749988 342314959203837246400777 := by
  unfold tailWord_749988
  simp only [CollatzResearch.WordTrace]
  refine ⟨13677154803464519298961309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18236206404619359065281745 13677154803464519298961309)
  ·
    refine ⟨5128933051299194737110491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13677154803464519298961309 5128933051299194737110491)
    ·
      refine ⟨7693399576948792105665737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5128933051299194737110491 7693399576948792105665737)
      ·
        refine ⟨5770049682711594079249303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7693399576948792105665737 5770049682711594079249303)
        ·
          refine ⟨8655074524067391118873955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5770049682711594079249303 8655074524067391118873955)
          ·
            refine ⟨12982611786101086678310933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8655074524067391118873955 12982611786101086678310933)
            ·
              refine ⟨608559927473488438045825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 12982611786101086678310933 608559927473488438045825)
              ·
                refine ⟨456419945605116328534369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 608559927473488438045825 456419945605116328534369)
                ·
                  refine ⟨342314959203837246400777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 456419945605116328534369 342314959203837246400777)
                  ·
                    rfl

theorem cell20_749988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 6, 2, 2].length) (baseStart_749988 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_749988 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_749988 prefixEnd_749988 := by exact prefixLift 749988
  have htrace : WordTrace (prefixWord ++ tailWord_749988) baseStart_749988 baseEnd_749988 := by
    simpa [prefixWord, tailWord_749988, baseEnd_749988] using wordTrace_append hprefix tailTrace_749988
  have hstable : (prefixWord ++ tailWord_749988).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749988).length < 2 ^ (prefixWord ++ tailWord_749988).sum := by decide
  have hdescent : baseEnd_749988 < baseStart_749988 := by decide
  rcases family_descends (prefixWord ++ tailWord_749988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750037 : List Nat := [1, 3, 2, 3, 1, 3, 7]
def baseStart_750037 : Nat := 118140960795 + 750037 * 2 ^ 59
def prefixEnd_750037 : Nat := 4983230072969 + 3 ^ 40 * 750037 * 2
def baseEnd_750037 : Nat := 38037480459890094863027

theorem tailTrace_750037 : CollatzResearch.WordTrace tailWord_750037 prefixEnd_750037 38037480459890094863027 := by
  unfold tailWord_750037
  simp only [CollatzResearch.WordTrace]
  refine ⟨27356096783751519966456365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18237397855834346644304243 27356096783751519966456365)
  ·
    refine ⟨10258536293906819987421137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27356096783751519966456365 10258536293906819987421137)
    ·
      refine ⟨7693902220430114990565853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10258536293906819987421137 7693902220430114990565853)
      ·
        refine ⟨2885213332661293121462195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7693902220430114990565853 2885213332661293121462195)
        ·
          refine ⟨4327819998991939682193293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2885213332661293121462195 4327819998991939682193293)
          ·
            refine ⟨1622932499621977380822485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4327819998991939682193293 1622932499621977380822485)
            ·
              refine ⟨38037480459890094863027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1622932499621977380822485 38037480459890094863027)
              ·
                rfl

theorem cell20_750037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 7].length) (baseStart_750037 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_750037 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_750037 prefixEnd_750037 := by exact prefixLift 750037
  have htrace : WordTrace (prefixWord ++ tailWord_750037) baseStart_750037 baseEnd_750037 := by
    simpa [prefixWord, tailWord_750037, baseEnd_750037] using wordTrace_append hprefix tailTrace_750037
  have hstable : (prefixWord ++ tailWord_750037).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750037).length < 2 ^ (prefixWord ++ tailWord_750037).sum := by decide
  have hdescent : baseEnd_750037 < baseStart_750037 := by decide
  rcases family_descends (prefixWord ++ tailWord_750037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750047 : List Nat := [1, 1, 2, 3, 3, 2, 2, 4, 2]
def baseStart_750047 : Nat := 118140960795 + 750047 * 2 ^ 59
def prefixEnd_750047 : Nat := 4983230072969 + 3 ^ 40 * 750047 * 2
def baseEnd_750047 : Nat := 342341888411495263433869

theorem tailTrace_750047 : CollatzResearch.WordTrace tailWord_750047 prefixEnd_750047 342341888411495263433869 := by
  unfold tailWord_750047
  simp only [CollatzResearch.WordTrace]
  refine ⟨27356461513715291674320395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18237641009143527782880263 27356461513715291674320395)
  ·
    refine ⟨41034692270572937511480593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27356461513715291674320395 41034692270572937511480593)
    ·
      refine ⟨30776019202929703133610445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41034692270572937511480593 30776019202929703133610445)
      ·
        refine ⟨11541007201098638675103917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30776019202929703133610445 11541007201098638675103917)
        ·
          refine ⟨4327877700411989503163969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11541007201098638675103917 4327877700411989503163969)
          ·
            refine ⟨3245908275308992127372977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4327877700411989503163969 3245908275308992127372977)
            ·
              refine ⟨2434431206481744095529733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3245908275308992127372977 2434431206481744095529733)
              ·
                refine ⟨456455851215327017911825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2434431206481744095529733 456455851215327017911825)
                ·
                  refine ⟨342341888411495263433869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 456455851215327017911825 342341888411495263433869)
                  ·
                    rfl

theorem cell20_750047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 4, 2].length) (baseStart_750047 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_750047 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_750047 prefixEnd_750047 := by exact prefixLift 750047
  have htrace : WordTrace (prefixWord ++ tailWord_750047) baseStart_750047 baseEnd_750047 := by
    simpa [prefixWord, tailWord_750047, baseEnd_750047] using wordTrace_append hprefix tailTrace_750047
  have hstable : (prefixWord ++ tailWord_750047).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750047).length < 2 ^ (prefixWord ++ tailWord_750047).sum := by decide
  have hdescent : baseEnd_750047 < baseStart_750047 := by decide
  rcases family_descends (prefixWord ++ tailWord_750047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750085 : List Nat := [1, 3, 1, 1, 2, 2, 5, 3, 2]
def baseStart_750085 : Nat := 118140960795 + 750085 * 2 ^ 59
def prefixEnd_750085 : Nat := 4983230072969 + 3 ^ 40 * 750085 * 2
def baseEnd_750085 : Nat := 342359232646936020167047

theorem tailTrace_750085 : CollatzResearch.WordTrace tailWord_750085 prefixEnd_750085 342359232646936020167047 := by
  unfold tailWord_750085
  simp only [CollatzResearch.WordTrace]
  refine ⟨27357847487577624164203709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18238564991718416109469139 27357847487577624164203709)
  ·
    refine ⟨10259192807841609061576391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27357847487577624164203709 10259192807841609061576391)
    ·
      refine ⟨15388789211762413592364587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10259192807841609061576391 15388789211762413592364587)
      ·
        refine ⟨23083183817643620388546881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15388789211762413592364587 23083183817643620388546881)
        ·
          refine ⟨17312387863232715291410161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23083183817643620388546881 17312387863232715291410161)
          ·
            refine ⟨12984290897424536468557621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17312387863232715291410161 12984290897424536468557621)
            ·
              refine ⟨1217277271633550293927277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12984290897424536468557621 1217277271633550293927277)
              ·
                refine ⟨456478976862581360222729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1217277271633550293927277 456478976862581360222729)
                ·
                  refine ⟨342359232646936020167047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 456478976862581360222729 342359232646936020167047)
                  ·
                    rfl

theorem cell20_750085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 5, 3, 2].length) (baseStart_750085 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_750085 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_750085 prefixEnd_750085 := by exact prefixLift 750085
  have htrace : WordTrace (prefixWord ++ tailWord_750085) baseStart_750085 baseEnd_750085 := by
    simpa [prefixWord, tailWord_750085, baseEnd_750085] using wordTrace_append hprefix tailTrace_750085
  have hstable : (prefixWord ++ tailWord_750085).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750085).length < 2 ^ (prefixWord ++ tailWord_750085).sum := by decide
  have hdescent : baseEnd_750085 < baseStart_750085 := by decide
  rcases family_descends (prefixWord ++ tailWord_750085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750106 : List Nat := [3, 1, 1, 3, 1, 1, 5, 1, 4]
def baseStart_750106 : Nat := 118140960795 + 750106 * 2 ^ 59
def prefixEnd_750106 : Nat := 4983230072969 + 3 ^ 40 * 750106 * 2
def baseEnd_750106 : Nat := 342368817619153280466961

theorem tailTrace_750106 : CollatzResearch.WordTrace tailWord_750106 prefixEnd_750106 342368817619153280466961 := by
  unfold tailWord_750106
  simp only [CollatzResearch.WordTrace]
  refine ⟨6839653355125386187679543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18239075613667696500478781 6839653355125386187679543)
  ·
    refine ⟨10259480032688079281519315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6839653355125386187679543 10259480032688079281519315)
    ·
      refine ⟨15389220049032118922278973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10259480032688079281519315 15389220049032118922278973)
      ·
        refine ⟨5770957518387044595854615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15389220049032118922278973 5770957518387044595854615)
        ·
          refine ⟨8656436277580566893781923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5770957518387044595854615 8656436277580566893781923)
          ·
            refine ⟨12984654416370850340672885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8656436277580566893781923 12984654416370850340672885)
            ·
              refine ⟨1217311351534767219438083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12984654416370850340672885 1217311351534767219438083)
              ·
                refine ⟨1825967027302150829157125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1217311351534767219438083 1825967027302150829157125)
                ·
                  refine ⟨342368817619153280466961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1825967027302150829157125 342368817619153280466961)
                  ·
                    rfl

theorem cell20_750106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 5, 1, 4].length) (baseStart_750106 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_750106 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_750106 prefixEnd_750106 := by exact prefixLift 750106
  have htrace : WordTrace (prefixWord ++ tailWord_750106) baseStart_750106 baseEnd_750106 := by
    simpa [prefixWord, tailWord_750106, baseEnd_750106] using wordTrace_append hprefix tailTrace_750106
  have hstable : (prefixWord ++ tailWord_750106).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750106).length < 2 ^ (prefixWord ++ tailWord_750106).sum := by decide
  have hdescent : baseEnd_750106 < baseStart_750106 := by decide
  rcases family_descends (prefixWord ++ tailWord_750106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750112 : List Nat := [2, 1, 1, 6, 3, 1, 2, 1, 3]
def baseStart_750112 : Nat := 118140960795 + 750112 * 2 ^ 59
def prefixEnd_750112 : Nat := 4983230072969 + 3 ^ 40 * 750112 * 2
def baseEnd_750112 : Nat := 342371556182643926266937

theorem tailTrace_750112 : CollatzResearch.WordTrace tailWord_750112 prefixEnd_750112 342371556182643926266937 := by
  unfold tailWord_750112
  simp only [CollatzResearch.WordTrace]
  refine ⟨13679416129239903887718295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18239221505653205183624393 13679416129239903887718295)
  ·
    refine ⟨20519124193859855831577443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13679416129239903887718295 20519124193859855831577443)
    ·
      refine ⟨30778686290789783747366165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20519124193859855831577443 30778686290789783747366165)
      ·
        refine ⟨1442750919880771113157789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 30778686290789783747366165 1442750919880771113157789)
        ·
          refine ⟨541031594955289167434171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1442750919880771113157789 541031594955289167434171)
          ·
            refine ⟨811547392432933751151257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 541031594955289167434171 811547392432933751151257)
            ·
              refine ⟨608660544324700313363443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 811547392432933751151257 608660544324700313363443)
              ·
                refine ⟨912990816487050470045165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 608660544324700313363443 912990816487050470045165)
                ·
                  refine ⟨342371556182643926266937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 912990816487050470045165 342371556182643926266937)
                  ·
                    rfl

theorem cell20_750112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 2, 1, 3].length) (baseStart_750112 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_750112 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_750112 prefixEnd_750112 := by exact prefixLift 750112
  have htrace : WordTrace (prefixWord ++ tailWord_750112) baseStart_750112 baseEnd_750112 := by
    simpa [prefixWord, tailWord_750112, baseEnd_750112] using wordTrace_append hprefix tailTrace_750112
  have hstable : (prefixWord ++ tailWord_750112).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750112).length < 2 ^ (prefixWord ++ tailWord_750112).sum := by decide
  have hdescent : baseEnd_750112 < baseStart_750112 := by decide
  rcases family_descends (prefixWord ++ tailWord_750112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750113 : List Nat := [1, 2, 3, 2, 2, 1, 4, 5]
def baseStart_750113 : Nat := 118140960795 + 750113 * 2 ^ 59
def prefixEnd_750113 : Nat := 4983230072969 + 3 ^ 40 * 750113 * 2
def baseEnd_750113 : Nat := 114124004203297455744533

theorem tailTrace_750113 : CollatzResearch.WordTrace tailWord_750113 prefixEnd_750113 114124004203297455744533 := by
  unfold tailWord_750113
  simp only [CollatzResearch.WordTrace]
  refine ⟨27358868731476184946222993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18239245820984123297481995 27358868731476184946222993)
  ·
    refine ⟨20519151548607138709667245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27358868731476184946222993 20519151548607138709667245)
    ·
      refine ⟨7694681830727677016125217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20519151548607138709667245 7694681830727677016125217)
      ·
        refine ⟨5771011373045757762093913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7694681830727677016125217 5771011373045757762093913)
        ·
          refine ⟨4328258529784318321570435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5771011373045757762093913 4328258529784318321570435)
          ·
            refine ⟨6492387794676477482355653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4328258529784318321570435 6492387794676477482355653)
            ·
              refine ⟨1217322711501839527941685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6492387794676477482355653 1217322711501839527941685)
              ·
                refine ⟨114124004203297455744533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1217322711501839527941685 114124004203297455744533)
                ·
                  rfl

theorem cell20_750113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 4, 5].length) (baseStart_750113 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_750113 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_750113 prefixEnd_750113 := by exact prefixLift 750113
  have htrace : WordTrace (prefixWord ++ tailWord_750113) baseStart_750113 baseEnd_750113 := by
    simpa [prefixWord, tailWord_750113, baseEnd_750113] using wordTrace_append hprefix tailTrace_750113
  have hstable : (prefixWord ++ tailWord_750113).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750113).length < 2 ^ (prefixWord ++ tailWord_750113).sum := by decide
  have hdescent : baseEnd_750113 < baseStart_750113 := by decide
  rcases family_descends (prefixWord ++ tailWord_750113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750157 : List Nat := [1, 6, 1, 1, 2, 1, 4, 2, 2]
def baseStart_750157 : Nat := 118140960795 + 750157 * 2 ^ 59
def prefixEnd_750157 : Nat := 4983230072969 + 3 ^ 40 * 750157 * 2
def baseEnd_750157 : Nat := 342392095408823769766753

theorem tailTrace_750157 : CollatzResearch.WordTrace tailWord_750157 prefixEnd_750157 342392095408823769766753 := by
  unfold tailWord_750157
  simp only [CollatzResearch.WordTrace]
  refine ⟨27360473543316780460824725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18240315695544520307216483 27360473543316780460824725)
  ·
    refine ⟨1282522197342974084101159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 27360473543316780460824725 1282522197342974084101159)
    ·
      refine ⟨1923783296014461126151739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1282522197342974084101159 1923783296014461126151739)
      ·
        refine ⟨2885674944021691689227609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1923783296014461126151739 2885674944021691689227609)
        ·
          refine ⟨2164256208016268766920707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2885674944021691689227609 2164256208016268766920707)
          ·
            refine ⟨3246384312024403150381061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2164256208016268766920707 3246384312024403150381061)
            ·
              refine ⟨608697058504575590696449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3246384312024403150381061 608697058504575590696449)
              ·
                refine ⟨456522793878431693022337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 608697058504575590696449 456522793878431693022337)
                ·
                  refine ⟨342392095408823769766753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 456522793878431693022337 342392095408823769766753)
                  ·
                    rfl

theorem cell20_750157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 4, 2, 2].length) (baseStart_750157 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_750157 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_750157 prefixEnd_750157 := by exact prefixLift 750157
  have htrace : WordTrace (prefixWord ++ tailWord_750157) baseStart_750157 baseEnd_750157 := by
    simpa [prefixWord, tailWord_750157, baseEnd_750157] using wordTrace_append hprefix tailTrace_750157
  have hstable : (prefixWord ++ tailWord_750157).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750157).length < 2 ^ (prefixWord ++ tailWord_750157).sum := by decide
  have hdescent : baseEnd_750157 < baseStart_750157 := by decide
  rcases family_descends (prefixWord ++ tailWord_750157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750158 : List Nat := [4, 1, 1, 1, 1, 2, 2, 3, 5]
def baseStart_750158 : Nat := 118140960795 + 750158 * 2 ^ 59
def prefixEnd_750158 : Nat := 4983230072969 + 3 ^ 40 * 750158 * 2
def baseEnd_750158 : Nat := 342392551836072210733415

theorem tailTrace_750158 : CollatzResearch.WordTrace tailWord_750158 prefixEnd_750158 342392551836072210733415 := by
  unfold tailWord_750158
  simp only [CollatzResearch.WordTrace]
  refine ⟨3420063752039144703951391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18240340010875438421074085 3420063752039144703951391)
  ·
    refine ⟨5130095628058717055927087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3420063752039144703951391 5130095628058717055927087)
    ·
      refine ⟨7695143442088075583890631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5130095628058717055927087 7695143442088075583890631)
      ·
        refine ⟨11542715163132113375835947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7695143442088075583890631 11542715163132113375835947)
        ·
          refine ⟨17314072744698170063753921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11542715163132113375835947 17314072744698170063753921)
          ·
            refine ⟨12985554558523627547815441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17314072744698170063753921 12985554558523627547815441)
            ·
              refine ⟨9739165918892720660861581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12985554558523627547815441 9739165918892720660861581)
              ·
                refine ⟨3652187219584770247823093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9739165918892720660861581 3652187219584770247823093)
                ·
                  refine ⟨342392551836072210733415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3652187219584770247823093 342392551836072210733415)
                  ·
                    rfl

theorem cell20_750158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 3, 5].length) (baseStart_750158 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_750158 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_750158 prefixEnd_750158 := by exact prefixLift 750158
  have htrace : WordTrace (prefixWord ++ tailWord_750158) baseStart_750158 baseEnd_750158 := by
    simpa [prefixWord, tailWord_750158, baseEnd_750158] using wordTrace_append hprefix tailTrace_750158
  have hstable : (prefixWord ++ tailWord_750158).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750158).length < 2 ^ (prefixWord ++ tailWord_750158).sum := by decide
  have hdescent : baseEnd_750158 < baseStart_750158 := by decide
  rcases family_descends (prefixWord ++ tailWord_750158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750161 : List Nat := [1, 2, 2, 1, 3, 4, 1, 4, 2]
def baseStart_750161 : Nat := 118140960795 + 750161 * 2 ^ 59
def prefixEnd_750161 : Nat := 4983230072969 + 3 ^ 40 * 750161 * 2
def baseEnd_750161 : Nat := 342393921117817533633403

theorem tailTrace_750161 : CollatzResearch.WordTrace tailWord_750161 prefixEnd_750161 342393921117817533633403 := by
  unfold tailWord_750161
  simp only [CollatzResearch.WordTrace]
  refine ⟨27360619435302289143970337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18240412956868192762646891 27360619435302289143970337)
  ·
    refine ⟨20520464576476716857977753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27360619435302289143970337 20520464576476716857977753)
    ·
      refine ⟨15390348432357537643483315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20520464576476716857977753 15390348432357537643483315)
      ·
        refine ⟨23085522648536306465224973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15390348432357537643483315 23085522648536306465224973)
        ·
          refine ⟨8657070993201114924459365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23085522648536306465224973 8657070993201114924459365)
          ·
            refine ⟨1623200811225209048336131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8657070993201114924459365 1623200811225209048336131)
            ·
              refine ⟨2434801216837813572504197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1623200811225209048336131 2434801216837813572504197)
              ·
                refine ⟨456525228157090044844537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2434801216837813572504197 456525228157090044844537)
                ·
                  refine ⟨342393921117817533633403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 456525228157090044844537 342393921117817533633403)
                  ·
                    rfl

theorem cell20_750161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 4, 2].length) (baseStart_750161 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_750161 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_750161 prefixEnd_750161 := by exact prefixLift 750161
  have htrace : WordTrace (prefixWord ++ tailWord_750161) baseStart_750161 baseEnd_750161 := by
    simpa [prefixWord, tailWord_750161, baseEnd_750161] using wordTrace_append hprefix tailTrace_750161
  have hstable : (prefixWord ++ tailWord_750161).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750161).length < 2 ^ (prefixWord ++ tailWord_750161).sum := by decide
  have hdescent : baseEnd_750161 < baseStart_750161 := by decide
  rcases family_descends (prefixWord ++ tailWord_750161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750178 : List Nat := [3, 3, 2, 3, 1, 1, 1, 2, 4]
def baseStart_750178 : Nat := 118140960795 + 750178 * 2 ^ 59
def prefixEnd_750178 : Nat := 4983230072969 + 3 ^ 40 * 750178 * 2
def baseEnd_750178 : Nat := 342401680381041030066667

theorem tailTrace_750178 : CollatzResearch.WordTrace tailWord_750178 prefixEnd_750178 342401680381041030066667 := by
  unfold tailWord_750178
  simp only [CollatzResearch.WordTrace]
  refine ⟨6840309869060175261834797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18240826317493800698226125 6840309869060175261834797)
  ·
    refine ⟨2565116200897565723188049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6840309869060175261834797 2565116200897565723188049)
    ·
      refine ⟨1923837150673174292391037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2565116200897565723188049 1923837150673174292391037)
      ·
        refine ⟨721438931502440359646639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1923837150673174292391037 721438931502440359646639)
        ·
          refine ⟨1082158397253660539469959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 721438931502440359646639 1082158397253660539469959)
          ·
            refine ⟨1623237595880490809204939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1082158397253660539469959 1623237595880490809204939)
            ·
              refine ⟨2434856393820736213807409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1623237595880490809204939 2434856393820736213807409)
              ·
                refine ⟨1826142295365552160355557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2434856393820736213807409 1826142295365552160355557)
                ·
                  refine ⟨342401680381041030066667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1826142295365552160355557 342401680381041030066667)
                  ·
                    rfl

theorem cell20_750178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 2, 4].length) (baseStart_750178 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_750178 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_750178 prefixEnd_750178 := by exact prefixLift 750178
  have htrace : WordTrace (prefixWord ++ tailWord_750178) baseStart_750178 baseEnd_750178 := by
    simpa [prefixWord, tailWord_750178, baseEnd_750178] using wordTrace_append hprefix tailTrace_750178
  have hstable : (prefixWord ++ tailWord_750178).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750178).length < 2 ^ (prefixWord ++ tailWord_750178).sum := by decide
  have hdescent : baseEnd_750178 < baseStart_750178 := by decide
  rcases family_descends (prefixWord ++ tailWord_750178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750213 : List Nat := [1, 3, 1, 1, 4, 2, 3, 2, 3]
def baseStart_750213 : Nat := 118140960795 + 750213 * 2 ^ 59
def prefixEnd_750213 : Nat := 4983230072969 + 3 ^ 40 * 750213 * 2
def baseEnd_750213 : Nat := 342417655334736463899857

theorem tailTrace_750213 : CollatzResearch.WordTrace tailWord_750213 prefixEnd_750213 342417655334736463899857 := by
  unfold tailWord_750213
  simp only [CollatzResearch.WordTrace]
  refine ⟨27362516031113902024863293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18241677354075934683242195 27362516031113902024863293)
  ·
    refine ⟨10260943511667713259323735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27362516031113902024863293 10260943511667713259323735)
    ·
      refine ⟨15391415267501569888985603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10260943511667713259323735 15391415267501569888985603)
      ·
        refine ⟨23087122901252354833478405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15391415267501569888985603 23087122901252354833478405)
        ·
          refine ⟨4328835543984816531277201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23087122901252354833478405 4328835543984816531277201)
          ·
            refine ⟨3246626657988612398457901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4328835543984816531277201 3246626657988612398457901)
            ·
              refine ⟨1217484996745729649421713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3246626657988612398457901 1217484996745729649421713)
              ·
                refine ⟨913113747559297237066285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1217484996745729649421713 913113747559297237066285)
                ·
                  refine ⟨342417655334736463899857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 913113747559297237066285 342417655334736463899857)
                  ·
                    rfl

theorem cell20_750213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 3, 2, 3].length) (baseStart_750213 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_750213 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_750213 prefixEnd_750213 := by exact prefixLift 750213
  have htrace : WordTrace (prefixWord ++ tailWord_750213) baseStart_750213 baseEnd_750213 := by
    simpa [prefixWord, tailWord_750213, baseEnd_750213] using wordTrace_append hprefix tailTrace_750213
  have hstable : (prefixWord ++ tailWord_750213).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750213).length < 2 ^ (prefixWord ++ tailWord_750213).sum := by decide
  have hdescent : baseEnd_750213 < baseStart_750213 := by decide
  rcases family_descends (prefixWord ++ tailWord_750213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750250 : List Nat := [3, 1, 5, 2, 1, 2, 1, 3, 2]
def baseStart_750250 : Nat := 118140960795 + 750250 * 2 ^ 59
def prefixEnd_750250 : Nat := 4983230072969 + 3 ^ 40 * 750250 * 2
def baseEnd_750250 : Nat := 342434543142928779666373

theorem tailTrace_750250 : CollatzResearch.WordTrace tailWord_750250 prefixEnd_750250 342434543142928779666373 := by
  unfold tailWord_750250
  simp only [CollatzResearch.WordTrace]
  refine ⟨6840966382994964335990051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18242577021319904895973469 6840966382994964335990051)
  ·
    refine ⟨10261449574492446503985077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6840966382994964335990051 10261449574492446503985077)
    ·
      refine ⟨962010897608666859748601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10261449574492446503985077 962010897608666859748601)
      ·
        refine ⟨721508173206500144811451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 962010897608666859748601 721508173206500144811451)
        ·
          refine ⟨1082262259809750217217177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 721508173206500144811451 1082262259809750217217177)
          ·
            refine ⟨811696694857312662912883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1082262259809750217217177 811696694857312662912883)
            ·
              refine ⟨1217545042285968994369325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 811696694857312662912883 1217545042285968994369325)
              ·
                refine ⟨456579390857238372888497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1217545042285968994369325 456579390857238372888497)
                ·
                  refine ⟨342434543142928779666373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 456579390857238372888497 342434543142928779666373)
                  ·
                    rfl

theorem cell20_750250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 1, 3, 2].length) (baseStart_750250 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_750250 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_750250 prefixEnd_750250 := by exact prefixLift 750250
  have htrace : WordTrace (prefixWord ++ tailWord_750250) baseStart_750250 baseEnd_750250 := by
    simpa [prefixWord, tailWord_750250, baseEnd_750250] using wordTrace_append hprefix tailTrace_750250
  have hstable : (prefixWord ++ tailWord_750250).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750250).length < 2 ^ (prefixWord ++ tailWord_750250).sum := by decide
  have hdescent : baseEnd_750250 < baseStart_750250 := by decide
  rcases family_descends (prefixWord ++ tailWord_750250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750272 : List Nat := [2, 1, 1, 2, 4, 2, 2, 1, 5]
def baseStart_750272 : Nat := 118140960795 + 750272 * 2 ^ 59
def prefixEnd_750272 : Nat := 4983230072969 + 3 ^ 40 * 750272 * 2
def baseEnd_750272 : Nat := 342444584542394480932949

theorem tailTrace_750272 : CollatzResearch.WordTrace tailWord_750272 prefixEnd_750272 342444584542394480932949 := by
  unfold tailWord_750272
  simp only [CollatzResearch.WordTrace]
  refine ⟨13682333968950077550630535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18243111958600103400840713 13682333968950077550630535)
  ·
    refine ⟨20523500953425116325945803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13682333968950077550630535 20523500953425116325945803)
    ·
      refine ⟨30785251430137674488918705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20523500953425116325945803 30785251430137674488918705)
      ·
        refine ⟨23088938572603255866689029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30785251430137674488918705 23088938572603255866689029)
        ·
          refine ⟨4329175982363110475004193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23088938572603255866689029 4329175982363110475004193)
          ·
            refine ⟨3246881986772332856253145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4329175982363110475004193 3246881986772332856253145)
            ·
              refine ⟨2435161490079249642189859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3246881986772332856253145 2435161490079249642189859)
              ·
                refine ⟨3652742235118874463284789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2435161490079249642189859 3652742235118874463284789)
                ·
                  refine ⟨342444584542394480932949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3652742235118874463284789 342444584542394480932949)
                  ·
                    rfl

theorem cell20_750272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 1, 5].length) (baseStart_750272 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_750272 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_750272 prefixEnd_750272 := by exact prefixLift 750272
  have htrace : WordTrace (prefixWord ++ tailWord_750272) baseStart_750272 baseEnd_750272 := by
    simpa [prefixWord, tailWord_750272, baseEnd_750272] using wordTrace_append hprefix tailTrace_750272
  have hstable : (prefixWord ++ tailWord_750272).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750272).length < 2 ^ (prefixWord ++ tailWord_750272).sum := by decide
  have hdescent : baseEnd_750272 < baseStart_750272 := by decide
  rcases family_descends (prefixWord ++ tailWord_750272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750278 : List Nat := [6, 1, 2, 1, 2, 1, 2, 5]
def baseStart_750278 : Nat := 118140960795 + 750278 * 2 ^ 59
def prefixEnd_750278 : Nat := 4983230072969 + 3 ^ 40 * 750278 * 2
def baseEnd_750278 : Nat := 114149107701961708910975

theorem tailTrace_750278 : CollatzResearch.WordTrace tailWord_750278 prefixEnd_750278 114149107701961708910975 := by
  unfold tailWord_750278
  simp only [CollatzResearch.WordTrace]
  refine ⟨855152711746200566436859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 18243257850585612083986325 855152711746200566436859)
  ·
    refine ⟨1282729067619300849655289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 855152711746200566436859 1282729067619300849655289)
    ·
      refine ⟨962046800714475637241467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1282729067619300849655289 962046800714475637241467)
      ·
        refine ⟨1443070201071713455862201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 962046800714475637241467 1443070201071713455862201)
        ·
          refine ⟨1082302650803785091896651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1443070201071713455862201 1082302650803785091896651)
          ·
            refine ⟨1623453976205677637844977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1082302650803785091896651 1623453976205677637844977)
            ·
              refine ⟨1217590482154258228383733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1623453976205677637844977 1217590482154258228383733)
              ·
                refine ⟨114149107701961708910975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1217590482154258228383733 114149107701961708910975)
                ·
                  rfl

theorem cell20_750278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_750278 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_750278 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_750278 prefixEnd_750278 := by exact prefixLift 750278
  have htrace : WordTrace (prefixWord ++ tailWord_750278) baseStart_750278 baseEnd_750278 := by
    simpa [prefixWord, tailWord_750278, baseEnd_750278] using wordTrace_append hprefix tailTrace_750278
  have hstable : (prefixWord ++ tailWord_750278).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750278).length < 2 ^ (prefixWord ++ tailWord_750278).sum := by decide
  have hdescent : baseEnd_750278 < baseStart_750278 := by decide
  rcases family_descends (prefixWord ++ tailWord_750278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750279 : List Nat := [1, 1, 4, 1, 1, 1, 2, 5, 4]
def baseStart_750279 : Nat := 118140960795 + 750279 * 2 ^ 59
def prefixEnd_750279 : Nat := 4983230072969 + 3 ^ 40 * 750279 * 2
def baseEnd_750279 : Nat := 342447779533133567699587

theorem tailTrace_750279 : CollatzResearch.WordTrace tailWord_750279 prefixEnd_750279 342447779533133567699587 := by
  unfold tailWord_750279
  simp only [CollatzResearch.WordTrace]
  refine ⟨27364923248874795296765891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18243282165916530197843927 27364923248874795296765891)
  ·
    refine ⟨41047384873312192945148837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27364923248874795296765891 41047384873312192945148837)
    ·
      refine ⟨7696384663746036177215407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41047384873312192945148837 7696384663746036177215407)
      ·
        refine ⟨11544576995619054265823111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7696384663746036177215407 11544576995619054265823111)
        ·
          refine ⟨17316865493428581398734667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11544576995619054265823111 17316865493428581398734667)
          ·
            refine ⟨25975298240142872098102001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17316865493428581398734667 25975298240142872098102001)
            ·
              refine ⟨19481473680107154073576501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25975298240142872098102001 19481473680107154073576501)
              ·
                refine ⟨1826388157510045694397797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19481473680107154073576501 1826388157510045694397797)
                ·
                  refine ⟨342447779533133567699587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1826388157510045694397797 342447779533133567699587)
                  ·
                    rfl

theorem cell20_750279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 5, 4].length) (baseStart_750279 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_750279 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_750279 prefixEnd_750279 := by exact prefixLift 750279
  have htrace : WordTrace (prefixWord ++ tailWord_750279) baseStart_750279 baseEnd_750279 := by
    simpa [prefixWord, tailWord_750279, baseEnd_750279] using wordTrace_append hprefix tailTrace_750279
  have hstable : (prefixWord ++ tailWord_750279).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750279).length < 2 ^ (prefixWord ++ tailWord_750279).sum := by decide
  have hdescent : baseEnd_750279 < baseStart_750279 := by decide
  rcases family_descends (prefixWord ++ tailWord_750279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750285 : List Nat := [1, 6, 2, 1, 2, 1, 1, 3, 3]
def baseStart_750285 : Nat := 118140960795 + 750285 * 2 ^ 59
def prefixEnd_750285 : Nat := 4983230072969 + 3 ^ 40 * 750285 * 2
def baseEnd_750285 : Nat := 342450518096624213499563

theorem tailTrace_750285 : CollatzResearch.WordTrace tailWord_750285 prefixEnd_750285 342450518096624213499563 := by
  unfold tailWord_750285
  simp only [CollatzResearch.WordTrace]
  refine ⟨27365142086853058321484309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18243428057902038880989539 27365142086853058321484309)
  ·
    refine ⟨1282741035321237108819577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 27365142086853058321484309 1282741035321237108819577)
    ·
      refine ⟨962055776490927831614683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1282741035321237108819577 962055776490927831614683)
      ·
        refine ⟨1443083664736391747422025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 962055776490927831614683 1443083664736391747422025)
        ·
          refine ⟨1082312748552293810566519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1443083664736391747422025 1082312748552293810566519)
          ·
            refine ⟨1623469122828440715849779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1082312748552293810566519 1623469122828440715849779)
            ·
              refine ⟨2435203684242661073774669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1623469122828440715849779 2435203684242661073774669)
              ·
                refine ⟨913201381590997902665501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2435203684242661073774669 913201381590997902665501)
                ·
                  refine ⟨342450518096624213499563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 913201381590997902665501 342450518096624213499563)
                  ·
                    rfl

theorem cell20_750285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_750285 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_750285 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_750285 prefixEnd_750285 := by exact prefixLift 750285
  have htrace : WordTrace (prefixWord ++ tailWord_750285) baseStart_750285 baseEnd_750285 := by
    simpa [prefixWord, tailWord_750285, baseEnd_750285] using wordTrace_append hprefix tailTrace_750285
  have hstable : (prefixWord ++ tailWord_750285).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750285).length < 2 ^ (prefixWord ++ tailWord_750285).sum := by decide
  have hdescent : baseEnd_750285 < baseStart_750285 := by decide
  rcases family_descends (prefixWord ++ tailWord_750285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750331 : List Nat := [1, 1, 1, 1, 1, 3, 1, 2, 9]
def baseStart_750331 : Nat := 118140960795 + 750331 * 2 ^ 59
def prefixEnd_750331 : Nat := 4983230072969 + 3 ^ 40 * 750331 * 2
def baseEnd_750331 : Nat := 342471513750052497966041

theorem tailTrace_750331 : CollatzResearch.WordTrace tailWord_750331 prefixEnd_750331 342471513750052497966041 := by
  unfold tailWord_750331
  simp only [CollatzResearch.WordTrace]
  refine ⟨27366819844686408177658847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18244546563124272118439231 27366819844686408177658847)
  ·
    refine ⟨41050229767029612266488271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27366819844686408177658847 41050229767029612266488271)
    ·
      refine ⟨61575344650544418399732407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41050229767029612266488271 61575344650544418399732407)
      ·
        refine ⟨92363016975816627599598611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61575344650544418399732407 92363016975816627599598611)
        ·
          refine ⟨138544525463724941399397917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92363016975816627599598611 138544525463724941399397917)
          ·
            refine ⟨51954197048896853024774219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 138544525463724941399397917 51954197048896853024774219)
            ·
              refine ⟨77931295573345279537161329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51954197048896853024774219 77931295573345279537161329)
              ·
                refine ⟨58448471680008959652870997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77931295573345279537161329 58448471680008959652870997)
                ·
                  refine ⟨342471513750052497966041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 58448471680008959652870997 342471513750052497966041)
                  ·
                    rfl

theorem cell20_750331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 9].length) (baseStart_750331 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_750331 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_750331 prefixEnd_750331 := by exact prefixLift 750331
  have htrace : WordTrace (prefixWord ++ tailWord_750331) baseStart_750331 baseEnd_750331 := by
    simpa [prefixWord, tailWord_750331, baseEnd_750331] using wordTrace_append hprefix tailTrace_750331
  have hstable : (prefixWord ++ tailWord_750331).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750331).length < 2 ^ (prefixWord ++ tailWord_750331).sum := by decide
  have hdescent : baseEnd_750331 < baseStart_750331 := by decide
  rcases family_descends (prefixWord ++ tailWord_750331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750355 : List Nat := [1, 1, 1, 2, 1, 3, 5, 2, 4]
def baseStart_750355 : Nat := 118140960795 + 750355 * 2 ^ 59
def prefixEnd_750355 : Nat := 4983230072969 + 3 ^ 40 * 750355 * 2
def baseEnd_750355 : Nat := 342482468004015081165943

theorem tailTrace_750355 : CollatzResearch.WordTrace tailWord_750355 prefixEnd_750355 342482468004015081165943 := by
  unfold tailWord_750355
  simp only [CollatzResearch.WordTrace]
  refine ⟨27367695196599460276532519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18245130131066306851021679 27367695196599460276532519)
  ·
    refine ⟨41051542794899190414798779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27367695196599460276532519 41051542794899190414798779)
    ·
      refine ⟨61577314192348785622198169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41051542794899190414798779 61577314192348785622198169)
      ·
        refine ⟨46182985644261589216648627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61577314192348785622198169 46182985644261589216648627)
        ·
          refine ⟨69274478466392383824972941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46182985644261589216648627 69274478466392383824972941)
          ·
            refine ⟨25977929424897143934364853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69274478466392383824972941 25977929424897143934364853)
            ·
              refine ⟨2435430883584107243846705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25977929424897143934364853 2435430883584107243846705)
              ·
                refine ⟨1826573162688080432885029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2435430883584107243846705 1826573162688080432885029)
                ·
                  refine ⟨342482468004015081165943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1826573162688080432885029 342482468004015081165943)
                  ·
                    rfl

theorem cell20_750355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 2, 4].length) (baseStart_750355 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_750355 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_750355 prefixEnd_750355 := by exact prefixLift 750355
  have htrace : WordTrace (prefixWord ++ tailWord_750355) baseStart_750355 baseEnd_750355 := by
    simpa [prefixWord, tailWord_750355, baseEnd_750355] using wordTrace_append hprefix tailTrace_750355
  have hstable : (prefixWord ++ tailWord_750355).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750355).length < 2 ^ (prefixWord ++ tailWord_750355).sum := by decide
  have hdescent : baseEnd_750355 < baseStart_750355 := by decide
  rcases family_descends (prefixWord ++ tailWord_750355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750378 : List Nat := [3, 1, 4, 3, 2, 1, 1, 2, 3]
def baseStart_750378 : Nat := 118140960795 + 750378 * 2 ^ 59
def prefixEnd_750378 : Nat := 4983230072969 + 3 ^ 40 * 750378 * 2
def baseEnd_750378 : Nat := 342492965830729223399183

theorem tailTrace_750378 : CollatzResearch.WordTrace tailWord_750378 prefixEnd_750378 342492965830729223399183 := by
  unfold tailWord_750378
  simp only [CollatzResearch.WordTrace]
  refine ⟨6842133518879033801154947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18245689383677423469746525 6842133518879033801154947)
  ·
    refine ⟨10263200278318550701732421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6842133518879033801154947 10263200278318550701732421)
    ·
      refine ⟨1924350052184728256574829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10263200278318550701732421 1924350052184728256574829)
      ·
        refine ⟨721631269569273096215561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1924350052184728256574829 721631269569273096215561)
        ·
          refine ⟨541223452176954822161671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 721631269569273096215561 541223452176954822161671)
          ·
            refine ⟨811835178265432233242507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 541223452176954822161671 811835178265432233242507)
            ·
              refine ⟨1217752767398148349863761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 811835178265432233242507 1217752767398148349863761)
              ·
                refine ⟨913314575548611262397821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1217752767398148349863761 913314575548611262397821)
                ·
                  refine ⟨342492965830729223399183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 913314575548611262397821 342492965830729223399183)
                  ·
                    rfl

theorem cell20_750378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 1, 2, 3].length) (baseStart_750378 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_750378 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_750378 prefixEnd_750378 := by exact prefixLift 750378
  have htrace : WordTrace (prefixWord ++ tailWord_750378) baseStart_750378 baseEnd_750378 := by
    simpa [prefixWord, tailWord_750378, baseEnd_750378] using wordTrace_append hprefix tailTrace_750378
  have hstable : (prefixWord ++ tailWord_750378).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750378).length < 2 ^ (prefixWord ++ tailWord_750378).sum := by decide
  have hdescent : baseEnd_750378 < baseStart_750378 := by decide
  rcases family_descends (prefixWord ++ tailWord_750378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750382 : List Nat := [4, 1, 3, 2, 1, 1, 3, 2, 3]
def baseStart_750382 : Nat := 118140960795 + 750382 * 2 ^ 59
def prefixEnd_750382 : Nat := 4983230072969 + 3 ^ 40 * 750382 * 2
def baseEnd_750382 : Nat := 342494791539722987265833

theorem tailTrace_750382 : CollatzResearch.WordTrace tailWord_750382 prefixEnd_750382 342494791539722987265833 := by
  unfold tailWord_750382
  simp only [CollatzResearch.WordTrace]
  refine ⟨3421084995937705485970675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18245786645001095925176933 3421084995937705485970675)
  ·
    refine ⟨5131627493906558228956013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3421084995937705485970675 5131627493906558228956013)
    ·
      refine ⟨1924360310214959335858505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5131627493906558228956013 1924360310214959335858505)
      ·
        refine ⟨1443270232661219501893879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1924360310214959335858505 1443270232661219501893879)
        ·
          refine ⟨2164905348991829252840819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1443270232661219501893879 2164905348991829252840819)
          ·
            refine ⟨3247358023487743879261229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2164905348991829252840819 3247358023487743879261229)
            ·
              refine ⟨1217759258807903954722961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3247358023487743879261229 1217759258807903954722961)
              ·
                refine ⟨913319444105927966042221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1217759258807903954722961 913319444105927966042221)
                ·
                  refine ⟨342494791539722987265833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 913319444105927966042221 342494791539722987265833)
                  ·
                    rfl

theorem cell20_750382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 3, 2, 3].length) (baseStart_750382 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_750382 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_750382 prefixEnd_750382 := by exact prefixLift 750382
  have htrace : WordTrace (prefixWord ++ tailWord_750382) baseStart_750382 baseEnd_750382 := by
    simpa [prefixWord, tailWord_750382, baseEnd_750382] using wordTrace_append hprefix tailTrace_750382
  have hstable : (prefixWord ++ tailWord_750382).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750382).length < 2 ^ (prefixWord ++ tailWord_750382).sum := by decide
  have hdescent : baseEnd_750382 < baseStart_750382 := by decide
  rcases family_descends (prefixWord ++ tailWord_750382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750386 : List Nat := [3, 2, 1, 1, 3, 1, 3, 1, 5]
def baseStart_750386 : Nat := 118140960795 + 750386 * 2 ^ 59
def prefixEnd_750386 : Nat := 4983230072969 + 3 ^ 40 * 750386 * 2
def baseEnd_750386 : Nat := 342496617248716751132483

theorem tailTrace_750386 : CollatzResearch.WordTrace tailWord_750386 prefixEnd_750386 342496617248716751132483 := by
  unfold tailWord_750386
  simp only [CollatzResearch.WordTrace]
  refine ⟨6842206464871788142727753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18245883906324768380607341 6842206464871788142727753)
  ·
    refine ⟨5131654848653841107045815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6842206464871788142727753 5131654848653841107045815)
    ·
      refine ⟨7697482272980761660568723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5131654848653841107045815 7697482272980761660568723)
      ·
        refine ⟨11546223409471142490853085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7697482272980761660568723 11546223409471142490853085)
        ·
          refine ⟨4329833778551678434069907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11546223409471142490853085 4329833778551678434069907)
          ·
            refine ⟨6494750667827517651104861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4329833778551678434069907 6494750667827517651104861)
            ·
              refine ⟨2435531500435319119164323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6494750667827517651104861 2435531500435319119164323)
              ·
                refine ⟨3653297250652978678746485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2435531500435319119164323 3653297250652978678746485)
                ·
                  refine ⟨342496617248716751132483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3653297250652978678746485 342496617248716751132483)
                  ·
                    rfl

theorem cell20_750386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 1, 5].length) (baseStart_750386 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_750386 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_750386 prefixEnd_750386 := by exact prefixLift 750386
  have htrace : WordTrace (prefixWord ++ tailWord_750386) baseStart_750386 baseEnd_750386 := by
    simpa [prefixWord, tailWord_750386, baseEnd_750386] using wordTrace_append hprefix tailTrace_750386
  have hstable : (prefixWord ++ tailWord_750386).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750386).length < 2 ^ (prefixWord ++ tailWord_750386).sum := by decide
  have hdescent : baseEnd_750386 < baseStart_750386 := by decide
  rcases family_descends (prefixWord ++ tailWord_750386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750389 : List Nat := [1, 3, 3, 1, 3, 1, 2, 4, 2]
def baseStart_750389 : Nat := 118140960795 + 750389 * 2 ^ 59
def prefixEnd_750389 : Nat := 4983230072969 + 3 ^ 40 * 750389 * 2
def baseEnd_750389 : Nat := 342497986530462074032471

theorem tailTrace_750389 : CollatzResearch.WordTrace tailWord_750389 prefixEnd_750389 342497986530462074032471 := by
  unfold tailWord_750389
  simp only [CollatzResearch.WordTrace]
  refine ⟨27368935278476284083270221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18245956852317522722180147 27368935278476284083270221)
  ·
    refine ⟨10263350729428606531226333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27368935278476284083270221 10263350729428606531226333)
    ·
      refine ⟨3848756523535727449209875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10263350729428606531226333 3848756523535727449209875)
      ·
        refine ⟨5773134785303591173814813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3848756523535727449209875 5773134785303591173814813)
        ·
          refine ⟨2164925544488846690180555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5773134785303591173814813 2164925544488846690180555)
          ·
            refine ⟨3247388316733270035270833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2164925544488846690180555 3247388316733270035270833)
            ·
              refine ⟨2435541237549952526453125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3247388316733270035270833 2435541237549952526453125)
              ·
                refine ⟨456663982040616098709961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2435541237549952526453125 456663982040616098709961)
                ·
                  refine ⟨342497986530462074032471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 456663982040616098709961 342497986530462074032471)
                  ·
                    rfl

theorem cell20_750389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 4, 2].length) (baseStart_750389 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_750389 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_750389 prefixEnd_750389 := by exact prefixLift 750389
  have htrace : WordTrace (prefixWord ++ tailWord_750389) baseStart_750389 baseEnd_750389 := by
    simpa [prefixWord, tailWord_750389, baseEnd_750389] using wordTrace_append hprefix tailTrace_750389
  have hstable : (prefixWord ++ tailWord_750389).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750389).length < 2 ^ (prefixWord ++ tailWord_750389).sum := by decide
  have hdescent : baseEnd_750389 < baseStart_750389 := by decide
  rcases family_descends (prefixWord ++ tailWord_750389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750403 : List Nat := [1, 1, 1, 3, 1, 4, 5, 1, 3]
def baseStart_750403 : Nat := 118140960795 + 750403 * 2 ^ 59
def prefixEnd_750403 : Nat := 4983230072969 + 3 ^ 40 * 750403 * 2
def baseEnd_750403 : Nat := 342504376511940247565747

theorem tailTrace_750403 : CollatzResearch.WordTrace tailWord_750403 prefixEnd_750403 342504376511940247565747 := by
  unfold tailWord_750403
  simp only [CollatzResearch.WordTrace]
  refine ⟨27369445900425564474279863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18246297266950376316186575 27369445900425564474279863)
  ·
    refine ⟨41054168850638346711419795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27369445900425564474279863 41054168850638346711419795)
    ·
      refine ⟨61581253275957520067129693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41054168850638346711419795 61581253275957520067129693)
      ·
        refine ⟨23092969978484070025173635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61581253275957520067129693 23092969978484070025173635)
        ·
          refine ⟨34639454967726105037760453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23092969978484070025173635 34639454967726105037760453)
          ·
            refine ⟨6494897806448644694580085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34639454967726105037760453 6494897806448644694580085)
            ·
              refine ⟨608896669354560440116883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6494897806448644694580085 608896669354560440116883)
              ·
                refine ⟨913345004031840660175325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 608896669354560440116883 913345004031840660175325)
                ·
                  refine ⟨342504376511940247565747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 913345004031840660175325 342504376511940247565747)
                  ·
                    rfl

theorem cell20_750403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 5, 1, 3].length) (baseStart_750403 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_750403 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_750403 prefixEnd_750403 := by exact prefixLift 750403
  have htrace : WordTrace (prefixWord ++ tailWord_750403) baseStart_750403 baseEnd_750403 := by
    simpa [prefixWord, tailWord_750403, baseEnd_750403] using wordTrace_append hprefix tailTrace_750403
  have hstable : (prefixWord ++ tailWord_750403).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750403).length < 2 ^ (prefixWord ++ tailWord_750403).sum := by decide
  have hdescent : baseEnd_750403 < baseStart_750403 := by decide
  rcases family_descends (prefixWord ++ tailWord_750403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750417 : List Nat := [1, 2, 2, 1, 6, 1, 1, 6]
def baseStart_750417 : Nat := 118140960795 + 750417 * 2 ^ 59
def prefixEnd_750417 : Nat := 4983230072969 + 3 ^ 40 * 750417 * 2
def baseEnd_750417 : Nat := 114170255497806140366341

theorem tailTrace_750417 : CollatzResearch.WordTrace tailWord_750417 prefixEnd_750417 114170255497806140366341 := by
  unfold tailWord_750417
  simp only [CollatzResearch.WordTrace]
  refine ⟨27369956522374844865289505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18246637681583229910193003 27369956522374844865289505)
  ·
    refine ⟨20527467391781133648967129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27369956522374844865289505 20527467391781133648967129)
    ·
      refine ⟨15395600543835850236725347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20527467391781133648967129 15395600543835850236725347)
      ·
        refine ⟨23093400815753775355088021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15395600543835850236725347 23093400815753775355088021)
        ·
          refine ⟨1082503163238458219769751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 23093400815753775355088021 1082503163238458219769751)
          ·
            refine ⟨1623754744857687329654627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1082503163238458219769751 1623754744857687329654627)
            ·
              refine ⟨2435632117286530994481941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1623754744857687329654627 2435632117286530994481941)
              ·
                refine ⟨114170255497806140366341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2435632117286530994481941 114170255497806140366341)
                ·
                  rfl

theorem cell20_750417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 6].length) (baseStart_750417 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_750417 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_750417 prefixEnd_750417 := by exact prefixLift 750417
  have htrace : WordTrace (prefixWord ++ tailWord_750417) baseStart_750417 baseEnd_750417 := by
    simpa [prefixWord, tailWord_750417, baseEnd_750417] using wordTrace_append hprefix tailTrace_750417
  have hstable : (prefixWord ++ tailWord_750417).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750417).length < 2 ^ (prefixWord ++ tailWord_750417).sum := by decide
  have hdescent : baseEnd_750417 < baseStart_750417 := by decide
  rcases family_descends (prefixWord ++ tailWord_750417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750434 : List Nat := [3, 3, 2, 1, 3, 2, 6]
def baseStart_750434 : Nat := 118140960795 + 750434 * 2 ^ 59
def prefixEnd_750434 : Nat := 4983230072969 + 3 ^ 40 * 750434 * 2
def baseEnd_750434 : Nat := 38057613972960213059143

theorem tailTrace_750434 : CollatzResearch.WordTrace tailWord_750434 prefixEnd_750434 38057613972960213059143 := by
  unfold tailWord_750434
  simp only [CollatzResearch.WordTrace]
  refine ⟨6842644140828314192164589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18247051042208837845772237 6842644140828314192164589)
  ·
    refine ⟨2565991552810617822061721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6842644140828314192164589 2565991552810617822061721)
    ·
      refine ⟨1924493664607963366546291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2565991552810617822061721 1924493664607963366546291)
      ·
        refine ⟨2886740496911945049819437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1924493664607963366546291 2886740496911945049819437)
        ·
          refine ⟨1082527686341979393682289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2886740496911945049819437 1082527686341979393682289)
          ·
            refine ⟨811895764756484545261717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1082527686341979393682289 811895764756484545261717)
            ·
              refine ⟨38057613972960213059143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 811895764756484545261717 38057613972960213059143)
              ·
                rfl

theorem cell20_750434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 6].length) (baseStart_750434 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_750434 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_750434 prefixEnd_750434 := by exact prefixLift 750434
  have htrace : WordTrace (prefixWord ++ tailWord_750434) baseStart_750434 baseEnd_750434 := by
    simpa [prefixWord, tailWord_750434, baseEnd_750434] using wordTrace_append hprefix tailTrace_750434
  have hstable : (prefixWord ++ tailWord_750434).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750434).length < 2 ^ (prefixWord ++ tailWord_750434).sum := by decide
  have hdescent : baseEnd_750434 < baseStart_750434 := by decide
  rcases family_descends (prefixWord ++ tailWord_750434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750448 : List Nat := [2, 1, 1, 1, 4, 1, 2, 6, 2]
def baseStart_750448 : Nat := 118140960795 + 750448 * 2 ^ 59
def prefixEnd_750448 : Nat := 4983230072969 + 3 ^ 40 * 750448 * 2
def baseEnd_750448 : Nat := 342524915738120091065563

theorem tailTrace_750448 : CollatzResearch.WordTrace tailWord_750448 prefixEnd_750448 342524915738120091065563 := by
  unfold tailWord_750448
  simp only [CollatzResearch.WordTrace]
  refine ⟨13685543592631268579833999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18247391456841691439778665 13685543592631268579833999)
  ·
    refine ⟨20528315388946902869750999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13685543592631268579833999 20528315388946902869750999)
    ·
      refine ⟨30792473083420354304626499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20528315388946902869750999 30792473083420354304626499)
      ·
        refine ⟨46188709625130531456939749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30792473083420354304626499 46188709625130531456939749)
        ·
          refine ⟨8660383054711974648176203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46188709625130531456939749 8660383054711974648176203)
          ·
            refine ⟨12990574582067961972264305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8660383054711974648176203 12990574582067961972264305)
            ·
              refine ⟨9742930936550971479198229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12990574582067961972264305 9742930936550971479198229)
              ·
                refine ⟨456699887650826788087417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9742930936550971479198229 456699887650826788087417)
                ·
                  refine ⟨342524915738120091065563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 456699887650826788087417 342524915738120091065563)
                  ·
                    rfl

theorem cell20_750448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 6, 2].length) (baseStart_750448 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_750448 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_750448 prefixEnd_750448 := by exact prefixLift 750448
  have htrace : WordTrace (prefixWord ++ tailWord_750448) baseStart_750448 baseEnd_750448 := by
    simpa [prefixWord, tailWord_750448, baseEnd_750448] using wordTrace_append hprefix tailTrace_750448
  have hstable : (prefixWord ++ tailWord_750448).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750448).length < 2 ^ (prefixWord ++ tailWord_750448).sum := by decide
  have hdescent : baseEnd_750448 < baseStart_750448 := by decide
  rcases family_descends (prefixWord ++ tailWord_750448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750476 : List Nat := [2, 2, 1, 2, 1, 2, 4, 6]
def baseStart_750476 : Nat := 118140960795 + 750476 * 2 ^ 59
def prefixEnd_750476 : Nat := 4983230072969 + 3 ^ 40 * 750476 * 2
def baseEnd_750476 : Nat := 114179231900358812710705

theorem tailTrace_750476 : CollatzResearch.WordTrace tailWord_750476 prefixEnd_750476 114179231900358812710705 := by
  unfold tailWord_750476
  simp only [CollatzResearch.WordTrace]
  refine ⟨13686054214580548970843641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18248072286107398627791521 13686054214580548970843641)
  ·
    refine ⟨10264540660935411728132731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13686054214580548970843641 10264540660935411728132731)
    ·
      refine ⟨15396810991403117592199097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10264540660935411728132731 15396810991403117592199097)
      ·
        refine ⟨11547608243552338194149323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15396810991403117592199097 11547608243552338194149323)
        ·
          refine ⟨17321412365328507291223985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11547608243552338194149323 17321412365328507291223985)
          ·
            refine ⟨12991059273996380468417989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17321412365328507291223985 12991059273996380468417989)
            ·
              refine ⟨2435823613874321337828373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12991059273996380468417989 2435823613874321337828373)
              ·
                refine ⟨114179231900358812710705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2435823613874321337828373 114179231900358812710705)
                ·
                  rfl

theorem cell20_750476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 6].length) (baseStart_750476 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_750476 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_750476 prefixEnd_750476 := by exact prefixLift 750476
  have htrace : WordTrace (prefixWord ++ tailWord_750476) baseStart_750476 baseEnd_750476 := by
    simpa [prefixWord, tailWord_750476, baseEnd_750476] using wordTrace_append hprefix tailTrace_750476
  have hstable : (prefixWord ++ tailWord_750476).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750476).length < 2 ^ (prefixWord ++ tailWord_750476).sum := by decide
  have hdescent : baseEnd_750476 < baseStart_750476 := by decide
  rcases family_descends (prefixWord ++ tailWord_750476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750483 : List Nat := [1, 1, 1, 2, 1, 2, 1, 6, 5]
def baseStart_750483 : Nat := 118140960795 + 750483 * 2 ^ 59
def prefixEnd_750483 : Nat := 4983230072969 + 3 ^ 40 * 750483 * 2
def baseEnd_750483 : Nat := 342540890691815524898753

theorem tailTrace_750483 : CollatzResearch.WordTrace tailWord_750483 prefixEnd_750483 342540890691815524898753 := by
  unfold tailWord_750483
  simp only [CollatzResearch.WordTrace]
  refine ⟨27372363740135738137192103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18248242493423825424794735 27372363740135738137192103)
  ·
    refine ⟨41058545610203607205788155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27372363740135738137192103 41058545610203607205788155)
    ·
      refine ⟨61587818415305410808682233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41058545610203607205788155 61587818415305410808682233)
      ·
        refine ⟨46190863811479058106511675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61587818415305410808682233 46190863811479058106511675)
        ·
          refine ⟨69286295717218587159767513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46190863811479058106511675 69286295717218587159767513)
          ·
            refine ⟨51964721787913940369825635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69286295717218587159767513 51964721787913940369825635)
            ·
              refine ⟨77947082681870910554738453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51964721787913940369825635 77947082681870910554738453)
              ·
                refine ⟨3653769500712698932253365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 77947082681870910554738453 3653769500712698932253365)
                ·
                  refine ⟨342540890691815524898753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3653769500712698932253365 342540890691815524898753)
                  ·
                    rfl

theorem cell20_750483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 6, 5].length) (baseStart_750483 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_750483 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_750483 prefixEnd_750483 := by exact prefixLift 750483
  have htrace : WordTrace (prefixWord ++ tailWord_750483) baseStart_750483 baseEnd_750483 := by
    simpa [prefixWord, tailWord_750483, baseEnd_750483] using wordTrace_append hprefix tailTrace_750483
  have hstable : (prefixWord ++ tailWord_750483).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750483).length < 2 ^ (prefixWord ++ tailWord_750483).sum := by decide
  have hdescent : baseEnd_750483 < baseStart_750483 := by decide
  rcases family_descends (prefixWord ++ tailWord_750483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750552 : List Nat := [2, 1, 2, 2, 2, 4, 7]
def baseStart_750552 : Nat := 118140960795 + 750552 * 2 ^ 59
def prefixEnd_750552 : Nat := 4983230072969 + 3 ^ 40 * 750552 * 2
def baseEnd_750552 : Nat := 38063598241328661288719

theorem tailTrace_750552 : CollatzResearch.WordTrace tailWord_750552 prefixEnd_750552 38063598241328661288719 := by
  unfold tailWord_750552
  simp only [CollatzResearch.WordTrace]
  refine ⟨13687440188442881460726955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18249920251257175280969273 13687440188442881460726955)
  ·
    refine ⟨20531160282664322191090433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13687440188442881460726955 20531160282664322191090433)
    ·
      refine ⟨15398370211998241643317825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20531160282664322191090433 15398370211998241643317825)
      ·
        refine ⟨11548777658998681232488369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15398370211998241643317825 11548777658998681232488369)
        ·
          refine ⟨8661583244249010924366277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11548777658998681232488369 8661583244249010924366277)
          ·
            refine ⟨1624046858296689548318677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8661583244249010924366277 1624046858296689548318677)
            ·
              refine ⟨38063598241328661288719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1624046858296689548318677 38063598241328661288719)
              ·
                rfl

theorem cell20_750552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 7].length) (baseStart_750552 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_750552 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_750552 prefixEnd_750552 := by exact prefixLift 750552
  have htrace : WordTrace (prefixWord ++ tailWord_750552) baseStart_750552 baseEnd_750552 := by
    simpa [prefixWord, tailWord_750552, baseEnd_750552] using wordTrace_append hprefix tailTrace_750552
  have hstable : (prefixWord ++ tailWord_750552).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750552).length < 2 ^ (prefixWord ++ tailWord_750552).sum := by decide
  have hdescent : baseEnd_750552 < baseStart_750552 := by decide
  rcases family_descends (prefixWord ++ tailWord_750552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750597 : List Nat := [1, 3, 1, 1, 2, 3, 1, 1, 7]
def baseStart_750597 : Nat := 118140960795 + 750597 * 2 ^ 59
def prefixEnd_750597 : Nat := 4983230072969 + 3 ^ 40 * 750597 * 2
def baseEnd_750597 : Nat := 342592923398137795098287

theorem tailTrace_750597 : CollatzResearch.WordTrace tailWord_750597 prefixEnd_750597 342592923398137795098287 := by
  unfold tailWord_750597
  simp only [CollatzResearch.WordTrace]
  refine ⟨27376521661722735606842045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18251014441148490404561363 27376521661722735606842045)
  ·
    refine ⟨10266195623146025852565767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27376521661722735606842045 10266195623146025852565767)
    ·
      refine ⟨15399293434719038778848651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10266195623146025852565767 15399293434719038778848651)
      ·
        refine ⟨23098940152078558168272977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15399293434719038778848651 23098940152078558168272977)
        ·
          refine ⟨17324205114058918626204733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23098940152078558168272977 17324205114058918626204733)
          ·
            refine ⟨6496576917772094484826775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17324205114058918626204733 6496576917772094484826775)
            ·
              refine ⟨9744865376658141727240163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6496576917772094484826775 9744865376658141727240163)
              ·
                refine ⟨14617298064987212590860245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9744865376658141727240163 14617298064987212590860245)
                ·
                  refine ⟨342592923398137795098287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14617298064987212590860245 342592923398137795098287)
                  ·
                    rfl

theorem cell20_750597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 7].length) (baseStart_750597 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_750597 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_750597 prefixEnd_750597 := by exact prefixLift 750597
  have htrace : WordTrace (prefixWord ++ tailWord_750597) baseStart_750597 baseEnd_750597 := by
    simpa [prefixWord, tailWord_750597, baseEnd_750597] using wordTrace_append hprefix tailTrace_750597
  have hstable : (prefixWord ++ tailWord_750597).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750597).length < 2 ^ (prefixWord ++ tailWord_750597).sum := by decide
  have hdescent : baseEnd_750597 < baseStart_750597 := by decide
  rcases family_descends (prefixWord ++ tailWord_750597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750624 : List Nat := [2, 1, 1, 7, 1, 1, 2, 5]
def baseStart_750624 : Nat := 118140960795 + 750624 * 2 ^ 59
def prefixEnd_750624 : Nat := 4983230072969 + 3 ^ 40 * 750624 * 2
def baseEnd_750624 : Nat := 114201748977948567066059

theorem tailTrace_750624 : CollatzResearch.WordTrace tailWord_750624 prefixEnd_750624 114201748977948567066059 := by
  unfold tailWord_750624
  simp only [CollatzResearch.WordTrace]
  refine ⟨13688753216312459609037463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18251670955083279478716617 13688753216312459609037463)
  ·
    refine ⟨20533129824468689413556195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13688753216312459609037463 20533129824468689413556195)
    ·
      refine ⟨30799694736703034120334293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20533129824468689413556195 30799694736703034120334293)
      ·
        refine ⟨721867845391477362195335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 30799694736703034120334293 721867845391477362195335)
        ·
          refine ⟨1082801768087216043293003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 721867845391477362195335 1082801768087216043293003)
          ·
            refine ⟨1624202652130824064939505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1082801768087216043293003 1624202652130824064939505)
            ·
              refine ⟨1218151989098118048704629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1624202652130824064939505 1218151989098118048704629)
              ·
                refine ⟨114201748977948567066059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1218151989098118048704629 114201748977948567066059)
                ·
                  rfl

theorem cell20_750624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 2, 5].length) (baseStart_750624 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_750624 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_750624 prefixEnd_750624 := by exact prefixLift 750624
  have htrace : WordTrace (prefixWord ++ tailWord_750624) baseStart_750624 baseEnd_750624 := by
    simpa [prefixWord, tailWord_750624, baseEnd_750624] using wordTrace_append hprefix tailTrace_750624
  have hstable : (prefixWord ++ tailWord_750624).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750624).length < 2 ^ (prefixWord ++ tailWord_750624).sum := by decide
  have hdescent : baseEnd_750624 < baseStart_750624 := by decide
  rcases family_descends (prefixWord ++ tailWord_750624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750669 : List Nat := [1, 6, 1, 1, 1, 2, 1, 4, 3]
def baseStart_750669 : Nat := 118140960795 + 750669 * 2 ^ 59
def prefixEnd_750669 : Nat := 4983230072969 + 3 ^ 40 * 750669 * 2
def baseEnd_750669 : Nat := 342625786160025544697993

theorem tailTrace_750669 : CollatzResearch.WordTrace tailWord_750669 prefixEnd_750669 342625786160025544697993 := by
  unfold tailWord_750669
  simp only [CollatzResearch.WordTrace]
  refine ⟨27379147717461891903463061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18252765144974594602308707 27379147717461891903463061)
  ·
    refine ⟨1283397549256026182974831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 27379147717461891903463061 1283397549256026182974831)
    ·
      refine ⟨1925096323884039274462247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1283397549256026182974831 1925096323884039274462247)
      ·
        refine ⟨2887644485826058911693371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1925096323884039274462247 2887644485826058911693371)
        ·
          refine ⟨4331466728739088367540057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2887644485826058911693371 4331466728739088367540057)
          ·
            refine ⟨3248600046554316275655043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4331466728739088367540057 3248600046554316275655043)
            ·
              refine ⟨4872900069831474413482565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3248600046554316275655043 4872900069831474413482565)
              ·
                refine ⟨913668763093401452527981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4872900069831474413482565 913668763093401452527981)
                ·
                  refine ⟨342625786160025544697993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 913668763093401452527981 342625786160025544697993)
                  ·
                    rfl

theorem cell20_750669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_750669 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_750669 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_750669 prefixEnd_750669 := by exact prefixLift 750669
  have htrace : WordTrace (prefixWord ++ tailWord_750669) baseStart_750669 baseEnd_750669 := by
    simpa [prefixWord, tailWord_750669, baseEnd_750669] using wordTrace_append hprefix tailTrace_750669
  have hstable : (prefixWord ++ tailWord_750669).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750669).length < 2 ^ (prefixWord ++ tailWord_750669).sum := by decide
  have hdescent : baseEnd_750669 < baseStart_750669 := by decide
  rcases family_descends (prefixWord ++ tailWord_750669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750673 : List Nat := [1, 2, 2, 1, 3, 1, 2, 3, 5]
def baseStart_750673 : Nat := 118140960795 + 750673 * 2 ^ 59
def prefixEnd_750673 : Nat := 4983230072969 + 3 ^ 40 * 750673 * 2
def baseEnd_750673 : Nat := 342627611869019308564643

theorem tailTrace_750673 : CollatzResearch.WordTrace tailWord_750673 prefixEnd_750673 342627611869019308564643 := by
  unfold tailWord_750673
  simp only [CollatzResearch.WordTrace]
  refine ⟨27379293609447400586608673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18252862406298267057739115 27379293609447400586608673)
  ·
    refine ⟨20534470207085550439956505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27379293609447400586608673 20534470207085550439956505)
    ·
      refine ⟨15400852655314162829967379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20534470207085550439956505 15400852655314162829967379)
      ·
        refine ⟨23101278982971244244951069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15400852655314162829967379 23101278982971244244951069)
        ·
          refine ⟨8662979618614216591856651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23101278982971244244951069 8662979618614216591856651)
          ·
            refine ⟨12994469427921324887784977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8662979618614216591856651 12994469427921324887784977)
            ·
              refine ⟨9745852070940993665838733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12994469427921324887784977 9745852070940993665838733)
              ·
                refine ⟨3654694526602872624689525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9745852070940993665838733 3654694526602872624689525)
                ·
                  refine ⟨342627611869019308564643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3654694526602872624689525 342627611869019308564643)
                  ·
                    rfl

theorem cell20_750673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 3, 5].length) (baseStart_750673 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_750673 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_750673 prefixEnd_750673 := by exact prefixLift 750673
  have htrace : WordTrace (prefixWord ++ tailWord_750673) baseStart_750673 baseEnd_750673 := by
    simpa [prefixWord, tailWord_750673, baseEnd_750673] using wordTrace_append hprefix tailTrace_750673
  have hstable : (prefixWord ++ tailWord_750673).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750673).length < 2 ^ (prefixWord ++ tailWord_750673).sum := by decide
  have hdescent : baseEnd_750673 < baseStart_750673 := by decide
  rcases family_descends (prefixWord ++ tailWord_750673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750697 : List Nat := [1, 2, 1, 1, 1, 7, 1, 2, 4]
def baseStart_750697 : Nat := 118140960795 + 750697 * 2 ^ 59
def prefixEnd_750697 : Nat := 4983230072969 + 3 ^ 40 * 750697 * 2
def baseEnd_750697 : Nat := 342638566122981891764545

theorem tailTrace_750697 : CollatzResearch.WordTrace tailWord_750697 prefixEnd_750697 342638566122981891764545 := by
  unfold tailWord_750697
  simp only [CollatzResearch.WordTrace]
  refine ⟨27380168961360452685482345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18253445974240301790321563 27380168961360452685482345)
  ·
    refine ⟨20535126721020339514111759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27380168961360452685482345 20535126721020339514111759)
    ·
      refine ⟨30802690081530509271167639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20535126721020339514111759 30802690081530509271167639)
      ·
        refine ⟨46204035122295763906751459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30802690081530509271167639 46204035122295763906751459)
        ·
          refine ⟨69306052683443645860127189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46204035122295763906751459 69306052683443645860127189)
          ·
            refine ⟨1624360609768210449846731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 69306052683443645860127189 1624360609768210449846731)
            ·
              refine ⟨2436540914652315674770097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1624360609768210449846731 2436540914652315674770097)
              ·
                refine ⟨1827405685989236756077573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2436540914652315674770097 1827405685989236756077573)
                ·
                  refine ⟨342638566122981891764545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1827405685989236756077573 342638566122981891764545)
                  ·
                    rfl

theorem cell20_750697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 2, 4].length) (baseStart_750697 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_750697 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_750697 prefixEnd_750697 := by exact prefixLift 750697
  have htrace : WordTrace (prefixWord ++ tailWord_750697) baseStart_750697 baseEnd_750697 := by
    simpa [prefixWord, tailWord_750697, baseEnd_750697] using wordTrace_append hprefix tailTrace_750697
  have hstable : (prefixWord ++ tailWord_750697).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750697).length < 2 ^ (prefixWord ++ tailWord_750697).sum := by decide
  have hdescent : baseEnd_750697 < baseStart_750697 := by decide
  rcases family_descends (prefixWord ++ tailWord_750697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750711 : List Nat := [1, 1, 3, 1, 1, 4, 2, 2, 5]
def baseStart_750711 : Nat := 118140960795 + 750711 * 2 ^ 59
def prefixEnd_750711 : Nat := 4983230072969 + 3 ^ 40 * 750711 * 2
def baseEnd_750711 : Nat := 342644956104460065297821

theorem tailTrace_750711 : CollatzResearch.WordTrace tailWord_750711 prefixEnd_750711 342644956104460065297821 := by
  unfold tailWord_750711
  simp only [CollatzResearch.WordTrace]
  refine ⟨27380679583309733076491987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18253786388873155384327991 27380679583309733076491987)
  ·
    refine ⟨41071019374964599614737981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27380679583309733076491987 41071019374964599614737981)
    ·
      refine ⟨15401632265611724855526743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41071019374964599614737981 15401632265611724855526743)
      ·
        refine ⟨23102448398417587283290115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15401632265611724855526743 23102448398417587283290115)
        ·
          refine ⟨34653672597626380924935173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23102448398417587283290115 34653672597626380924935173)
          ·
            refine ⟨6497563612054946423425345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34653672597626380924935173 6497563612054946423425345)
            ·
              refine ⟨4873172709041209817569009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6497563612054946423425345 4873172709041209817569009)
              ·
                refine ⟨3654879531780907363176757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4873172709041209817569009 3654879531780907363176757)
                ·
                  refine ⟨342644956104460065297821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3654879531780907363176757 342644956104460065297821)
                  ·
                    rfl

theorem cell20_750711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 2, 5].length) (baseStart_750711 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_750711 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_750711 prefixEnd_750711 := by exact prefixLift 750711
  have htrace : WordTrace (prefixWord ++ tailWord_750711) baseStart_750711 baseEnd_750711 := by
    simpa [prefixWord, tailWord_750711, baseEnd_750711] using wordTrace_append hprefix tailTrace_750711
  have hstable : (prefixWord ++ tailWord_750711).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750711).length < 2 ^ (prefixWord ++ tailWord_750711).sum := by decide
  have hdescent : baseEnd_750711 < baseStart_750711 := by decide
  rcases family_descends (prefixWord ++ tailWord_750711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750759 : List Nat := [1, 1, 6, 2, 1, 2, 1, 6]
def baseStart_750759 : Nat := 118140960795 + 750759 * 2 ^ 59
def prefixEnd_750759 : Nat := 4983230072969 + 3 ^ 40 * 750759 * 2
def baseEnd_750759 : Nat := 114222288204128410565875

theorem tailTrace_750759 : CollatzResearch.WordTrace tailWord_750759 prefixEnd_750759 114222288204128410565875 := by
  unfold tailWord_750759
  simp only [CollatzResearch.WordTrace]
  refine ⟨27382430287135837274239331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18254953524757224849492887 27382430287135837274239331)
  ·
    refine ⟨41073645430703755911358997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27382430287135837274239331 41073645430703755911358997)
    ·
      refine ⟨1925327129564238558344953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 41073645430703755911358997 1925327129564238558344953)
      ·
        refine ⟨1443995347173178918758715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1925327129564238558344953 1443995347173178918758715)
        ·
          refine ⟨2165993020759768378138073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1443995347173178918758715 2165993020759768378138073)
          ·
            refine ⟨1624494765569826283603555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2165993020759768378138073 1624494765569826283603555)
            ·
              refine ⟨2436742148354739425405333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1624494765569826283603555 2436742148354739425405333)
              ·
                refine ⟨114222288204128410565875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2436742148354739425405333 114222288204128410565875)
                ·
                  rfl

theorem cell20_750759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 6].length) (baseStart_750759 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_750759 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_750759 prefixEnd_750759 := by exact prefixLift 750759
  have htrace : WordTrace (prefixWord ++ tailWord_750759) baseStart_750759 baseEnd_750759 := by
    simpa [prefixWord, tailWord_750759, baseEnd_750759] using wordTrace_append hprefix tailTrace_750759
  have hstable : (prefixWord ++ tailWord_750759).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750759).length < 2 ^ (prefixWord ++ tailWord_750759).sum := by decide
  have hdescent : baseEnd_750759 < baseStart_750759 := by decide
  rcases family_descends (prefixWord ++ tailWord_750759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750765 : List Nat := [1, 5, 2, 1, 4, 1, 1, 3, 2]
def baseStart_750765 : Nat := 118140960795 + 750765 * 2 ^ 59
def prefixEnd_750765 : Nat := 4983230072969 + 3 ^ 40 * 750765 * 2
def baseEnd_750765 : Nat := 342669603175875877497601

theorem tailTrace_750765 : CollatzResearch.WordTrace tailWord_750765 prefixEnd_750765 342669603175875877497601 := by
  unfold tailWord_750765
  simp only [CollatzResearch.WordTrace]
  refine ⟨27382649125114100298957749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18255099416742733532638499 27382649125114100298957749)
  ·
    refine ⟨2567123355479446903027289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27382649125114100298957749 2567123355479446903027289)
    ·
      refine ⟨1925342516609585177270467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2567123355479446903027289 1925342516609585177270467)
      ·
        refine ⟨2888013774914377765905701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1925342516609585177270467 2888013774914377765905701)
        ·
          refine ⟨541502582796445831107319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2888013774914377765905701 541502582796445831107319)
          ·
            refine ⟨812253874194668746660979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 541502582796445831107319 812253874194668746660979)
            ·
              refine ⟨1218380811292003119991469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 812253874194668746660979 1218380811292003119991469)
              ·
                refine ⟨456892804234501169996801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1218380811292003119991469 456892804234501169996801)
                ·
                  refine ⟨342669603175875877497601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 456892804234501169996801 342669603175875877497601)
                  ·
                    rfl

theorem cell20_750765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 1, 3, 2].length) (baseStart_750765 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_750765 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_750765 prefixEnd_750765 := by exact prefixLift 750765
  have htrace : WordTrace (prefixWord ++ tailWord_750765) baseStart_750765 baseEnd_750765 := by
    simpa [prefixWord, tailWord_750765, baseEnd_750765] using wordTrace_append hprefix tailTrace_750765
  have hstable : (prefixWord ++ tailWord_750765).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750765).length < 2 ^ (prefixWord ++ tailWord_750765).sum := by decide
  have hdescent : baseEnd_750765 < baseStart_750765 := by decide
  rcases family_descends (prefixWord ++ tailWord_750765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750769 : List Nat := [1, 2, 2, 5, 1, 1, 3, 3, 2]
def baseStart_750769 : Nat := 118140960795 + 750769 * 2 ^ 59
def prefixEnd_750769 : Nat := 4983230072969 + 3 ^ 40 * 750769 * 2
def baseEnd_750769 : Nat := 342671428884869641364251

theorem tailTrace_750769 : CollatzResearch.WordTrace tailWord_750769 prefixEnd_750769 342671428884869641364251 := by
  unfold tailWord_750769
  simp only [CollatzResearch.WordTrace]
  refine ⟨27382795017099608982103361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18255196678066405988068907 27382795017099608982103361)
  ·
    refine ⟨20537096262824706736577521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27382795017099608982103361 20537096262824706736577521)
    ·
      refine ⟨15402822197118530052433141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20537096262824706736577521 15402822197118530052433141)
      ·
        refine ⟨1444014580979862192415607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15402822197118530052433141 1444014580979862192415607)
        ·
          refine ⟨2166021871469793288623411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1444014580979862192415607 2166021871469793288623411)
          ·
            refine ⟨3249032807204689932935117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2166021871469793288623411 3249032807204689932935117)
            ·
              refine ⟨1218387302701758724850669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3249032807204689932935117 1218387302701758724850669)
              ·
                refine ⟨456895238513159521819001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1218387302701758724850669 456895238513159521819001)
                ·
                  refine ⟨342671428884869641364251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 456895238513159521819001 342671428884869641364251)
                  ·
                    rfl

theorem cell20_750769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 3, 3, 2].length) (baseStart_750769 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_750769 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_750769 prefixEnd_750769 := by exact prefixLift 750769
  have htrace : WordTrace (prefixWord ++ tailWord_750769) baseStart_750769 baseEnd_750769 := by
    simpa [prefixWord, tailWord_750769, baseEnd_750769] using wordTrace_append hprefix tailTrace_750769
  have hstable : (prefixWord ++ tailWord_750769).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750769).length < 2 ^ (prefixWord ++ tailWord_750769).sum := by decide
  have hdescent : baseEnd_750769 < baseStart_750769 := by decide
  rcases family_descends (prefixWord ++ tailWord_750769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750780 : List Nat := [2, 2, 2, 3, 2, 1, 8]
def baseStart_750780 : Nat := 118140960795 + 750780 * 2 ^ 59
def prefixEnd_750780 : Nat := 4983230072969 + 3 ^ 40 * 750780 * 2
def baseEnd_750780 : Nat := 38075161064955832444171

theorem tailTrace_750780 : CollatzResearch.WordTrace tailWord_750780 prefixEnd_750780 38075161064955832444171 := by
  unfold tailWord_750780
  simp only [CollatzResearch.WordTrace]
  refine ⟨13691598110029878930376897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18255464146706505240502529 13691598110029878930376897)
  ·
    refine ⟨10268698582522409197782673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13691598110029878930376897 10268698582522409197782673)
    ·
      refine ⟨7701523936891806898337005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10268698582522409197782673 7701523936891806898337005)
      ·
        refine ⟨2888071476334427586876377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7701523936891806898337005 2888071476334427586876377)
        ·
          refine ⟨2166053607250820690157283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2888071476334427586876377 2166053607250820690157283)
          ·
            refine ⟨3249080410876231035235925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2166053607250820690157283 3249080410876231035235925)
            ·
              refine ⟨38075161064955832444171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3249080410876231035235925 38075161064955832444171)
              ·
                rfl

theorem cell20_750780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 8].length) (baseStart_750780 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_750780 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_750780 prefixEnd_750780 := by exact prefixLift 750780
  have htrace : WordTrace (prefixWord ++ tailWord_750780) baseStart_750780 baseEnd_750780 := by
    simpa [prefixWord, tailWord_750780, baseEnd_750780] using wordTrace_append hprefix tailTrace_750780
  have hstable : (prefixWord ++ tailWord_750780).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750780).length < 2 ^ (prefixWord ++ tailWord_750780).sum := by decide
  have hdescent : baseEnd_750780 < baseStart_750780 := by decide
  rcases family_descends (prefixWord ++ tailWord_750780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750842 : List Nat := [3, 1, 1, 1, 1, 4, 4, 2, 3]
def baseStart_750842 : Nat := 118140960795 + 750842 * 2 ^ 59
def prefixEnd_750842 : Nat := 4983230072969 + 3 ^ 40 * 750842 * 2
def baseEnd_750842 : Nat := 342704748074005831930619

theorem tailTrace_750842 : CollatzResearch.WordTrace tailWord_750842 prefixEnd_750842 342704748074005831930619 := by
  unfold tailWord_750842
  simp only [CollatzResearch.WordTrace]
  refine ⟨6846364386458785612377695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18256971697223428299673853 6846364386458785612377695)
  ·
    refine ⟨10269546579688178418566543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6846364386458785612377695 10269546579688178418566543)
    ·
      refine ⟨15404319869532267627849815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10269546579688178418566543 15404319869532267627849815)
      ·
        refine ⟨23106479804298401441774723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15404319869532267627849815 23106479804298401441774723)
        ·
          refine ⟨34659719706447602162662085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23106479804298401441774723 34659719706447602162662085)
          ·
            refine ⟨6498697444958925405499141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34659719706447602162662085 6498697444958925405499141)
            ·
              refine ⟨1218505770929798513531089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6498697444958925405499141 1218505770929798513531089)
              ·
                refine ⟨913879328197348885148317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1218505770929798513531089 913879328197348885148317)
                ·
                  refine ⟨342704748074005831930619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 913879328197348885148317 342704748074005831930619)
                  ·
                    rfl

theorem cell20_750842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 4, 2, 3].length) (baseStart_750842 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_750842 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_750842 prefixEnd_750842 := by exact prefixLift 750842
  have htrace : WordTrace (prefixWord ++ tailWord_750842) baseStart_750842 baseEnd_750842 := by
    simpa [prefixWord, tailWord_750842, baseEnd_750842] using wordTrace_append hprefix tailTrace_750842
  have hstable : (prefixWord ++ tailWord_750842).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750842).length < 2 ^ (prefixWord ++ tailWord_750842).sum := by decide
  have hdescent : baseEnd_750842 < baseStart_750842 := by decide
  rcases family_descends (prefixWord ++ tailWord_750842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750897 : List Nat := [1, 2, 2, 3, 3, 3, 1, 2, 3]
def baseStart_750897 : Nat := 118140960795 + 750897 * 2 ^ 59
def prefixEnd_750897 : Nat := 4983230072969 + 3 ^ 40 * 750897 * 2
def baseEnd_750897 : Nat := 342729851572670085097061

theorem tailTrace_750897 : CollatzResearch.WordTrace tailWord_750897 prefixEnd_750897 342729851572670085097061 := by
  unfold tailWord_750897
  simp only [CollatzResearch.WordTrace]
  refine ⟨27387463560635886842762945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18258309040423924561841963 27387463560635886842762945)
  ·
    refine ⟨20540597670476915132072209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27387463560635886842762945 20540597670476915132072209)
    ·
      refine ⟨15405448252857686349054157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20540597670476915132072209 15405448252857686349054157)
      ·
        refine ⟨5777043094821632380895309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15405448252857686349054157 5777043094821632380895309)
        ·
          refine ⟨2166391160558112142835741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5777043094821632380895309 2166391160558112142835741)
          ·
            refine ⟨812396685209292053563403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2166391160558112142835741 812396685209292053563403)
            ·
              refine ⟨1218595027813938080345105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 812396685209292053563403 1218595027813938080345105)
              ·
                refine ⟨913946270860453560258829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1218595027813938080345105 913946270860453560258829)
                ·
                  refine ⟨342729851572670085097061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 913946270860453560258829 342729851572670085097061)
                  ·
                    rfl

theorem cell20_750897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 1, 2, 3].length) (baseStart_750897 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_750897 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_750897 prefixEnd_750897 := by exact prefixLift 750897
  have htrace : WordTrace (prefixWord ++ tailWord_750897) baseStart_750897 baseEnd_750897 := by
    simpa [prefixWord, tailWord_750897, baseEnd_750897] using wordTrace_append hprefix tailTrace_750897
  have hstable : (prefixWord ++ tailWord_750897).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750897).length < 2 ^ (prefixWord ++ tailWord_750897).sum := by decide
  have hdescent : baseEnd_750897 < baseStart_750897 := by decide
  rcases family_descends (prefixWord ++ tailWord_750897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750915 : List Nat := [1, 1, 1, 3, 1, 3, 1, 9]
def baseStart_750915 : Nat := 118140960795 + 750915 * 2 ^ 59
def prefixEnd_750915 : Nat := 4983230072969 + 3 ^ 40 * 750915 * 2
def baseEnd_750915 : Nat := 114246022421047340832329

theorem tailTrace_750915 : CollatzResearch.WordTrace tailWord_750915 prefixEnd_750915 114246022421047340832329 := by
  unfold tailWord_750915
  simp only [CollatzResearch.WordTrace]
  refine ⟨27388120074570675916918199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18258746716380450611278799 27388120074570675916918199)
  ·
    refine ⟨41082180111856013875377299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27388120074570675916918199 41082180111856013875377299)
    ·
      refine ⟨61623270167784020813065949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41082180111856013875377299 61623270167784020813065949)
      ·
        refine ⟨23108726312919007804899731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61623270167784020813065949 23108726312919007804899731)
        ·
          refine ⟨34663089469378511707349597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23108726312919007804899731 34663089469378511707349597)
          ·
            refine ⟨12998658551016941890256099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34663089469378511707349597 12998658551016941890256099)
            ·
              refine ⟨19497987826525412835384149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12998658551016941890256099 19497987826525412835384149)
              ·
                refine ⟨114246022421047340832329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19497987826525412835384149 114246022421047340832329)
                ·
                  rfl

theorem cell20_750915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 9].length) (baseStart_750915 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_750915 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_750915 prefixEnd_750915 := by exact prefixLift 750915
  have htrace : WordTrace (prefixWord ++ tailWord_750915) baseStart_750915 baseEnd_750915 := by
    simpa [prefixWord, tailWord_750915, baseEnd_750915] using wordTrace_append hprefix tailTrace_750915
  have hstable : (prefixWord ++ tailWord_750915).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750915).length < 2 ^ (prefixWord ++ tailWord_750915).sum := by decide
  have hdescent : baseEnd_750915 < baseStart_750915 := by decide
  rcases family_descends (prefixWord ++ tailWord_750915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750932 : List Nat := [2, 4, 1, 1, 2, 1, 3, 6]
def baseStart_750932 : Nat := 118140960795 + 750932 * 2 ^ 59
def prefixEnd_750932 : Nat := 4983230072969 + 3 ^ 40 * 750932 * 2
def baseEnd_750932 : Nat := 114248608842121839643417

theorem tailTrace_750932 : CollatzResearch.WordTrace tailWord_750932 prefixEnd_750932 114248608842121839643417 := by
  unfold tailWord_750932
  simp only [CollatzResearch.WordTrace]
  refine ⟨13694370057754543910143525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18259160077006058546858033 13694370057754543910143525)
  ·
    refine ⟨2567694385828976983151911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13694370057754543910143525 2567694385828976983151911)
    ·
      refine ⟨3851541578743465474727867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2567694385828976983151911 3851541578743465474727867)
      ·
        refine ⟨5777312368115198212091801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3851541578743465474727867 5777312368115198212091801)
        ·
          refine ⟨4332984276086398659068851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5777312368115198212091801 4332984276086398659068851)
          ·
            refine ⟨6499476414129597988603277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4332984276086398659068851 6499476414129597988603277)
            ·
              refine ⟨2437303655298599245726229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6499476414129597988603277 2437303655298599245726229)
              ·
                refine ⟨114248608842121839643417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2437303655298599245726229 114248608842121839643417)
                ·
                  rfl

theorem cell20_750932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 6].length) (baseStart_750932 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_750932 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_750932 prefixEnd_750932 := by exact prefixLift 750932
  have htrace : WordTrace (prefixWord ++ tailWord_750932) baseStart_750932 baseEnd_750932 := by
    simpa [prefixWord, tailWord_750932, baseEnd_750932] using wordTrace_append hprefix tailTrace_750932
  have hstable : (prefixWord ++ tailWord_750932).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750932).length < 2 ^ (prefixWord ++ tailWord_750932).sum := by decide
  have hdescent : baseEnd_750932 < baseStart_750932 := by decide
  rcases family_descends (prefixWord ++ tailWord_750932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751077 : List Nat := [1, 3, 1, 5, 1, 1, 1, 3, 4]
def baseStart_751077 : Nat := 118140960795 + 751077 * 2 ^ 59
def prefixEnd_751077 : Nat := 4983230072969 + 3 ^ 40 * 751077 * 2
def baseEnd_751077 : Nat := 342812008477389459096325

theorem tailTrace_751077 : CollatzResearch.WordTrace tailWord_751077 prefixEnd_751077 342812008477389459096325 := by
  unfold tailWord_751077
  simp only [CollatzResearch.WordTrace]
  refine ⟨27394028699983777584315485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18262685799989185056210323 27394028699983777584315485)
  ·
    refine ⟨10272760762493916594118307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27394028699983777584315485 10272760762493916594118307)
    ·
      refine ⟨15409141143740874891177461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10272760762493916594118307 15409141143740874891177461)
      ·
        refine ⟨1444606982225707021047887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15409141143740874891177461 1444606982225707021047887)
        ·
          refine ⟨2166910473338560531571831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1444606982225707021047887 2166910473338560531571831)
          ·
            refine ⟨3250365710007840797357747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2166910473338560531571831 3250365710007840797357747)
            ·
              refine ⟨4875548565011761196036621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3250365710007840797357747 4875548565011761196036621)
              ·
                refine ⟨1828330711879410448513733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4875548565011761196036621 1828330711879410448513733)
                ·
                  refine ⟨342812008477389459096325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1828330711879410448513733 342812008477389459096325)
                  ·
                    rfl

theorem cell20_751077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 3, 4].length) (baseStart_751077 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_751077 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_751077 prefixEnd_751077 := by exact prefixLift 751077
  have htrace : WordTrace (prefixWord ++ tailWord_751077) baseStart_751077 baseEnd_751077 := by
    simpa [prefixWord, tailWord_751077, baseEnd_751077] using wordTrace_append hprefix tailTrace_751077
  have hstable : (prefixWord ++ tailWord_751077).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751077).length < 2 ^ (prefixWord ++ tailWord_751077).sum := by decide
  have hdescent : baseEnd_751077 < baseStart_751077 := by decide
  rcases family_descends (prefixWord ++ tailWord_751077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751098 : List Nat := [3, 1, 1, 1, 1, 2, 3, 4, 4]
def baseStart_751098 : Nat := 118140960795 + 751098 * 2 ^ 59
def prefixEnd_751098 : Nat := 4983230072969 + 3 ^ 40 * 751098 * 2
def baseEnd_751098 : Nat := 342821593449606719396239

theorem tailTrace_751098 : CollatzResearch.WordTrace tailWord_751098 prefixEnd_751098 342821593449606719396239 := by
  unfold tailWord_751098
  simp only [CollatzResearch.WordTrace]
  refine ⟨6848698658226924542707487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18263196421938465447219965 6848698658226924542707487)
  ·
    refine ⟨10273047987340386814061231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6848698658226924542707487 10273047987340386814061231)
    ·
      refine ⟨15409571981010580221091847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10273047987340386814061231 15409571981010580221091847)
      ·
        refine ⟨23114357971515870331637771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15409571981010580221091847 23114357971515870331637771)
        ·
          refine ⟨34671536957273805497456657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23114357971515870331637771 34671536957273805497456657)
          ·
            refine ⟨26003652717955354123092493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34671536957273805497456657 26003652717955354123092493)
            ·
              refine ⟨9751369769233257796159685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26003652717955354123092493 9751369769233257796159685)
              ·
                refine ⟨1828381831731235836779941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9751369769233257796159685 1828381831731235836779941)
                ·
                  refine ⟨342821593449606719396239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1828381831731235836779941 342821593449606719396239)
                  ·
                    rfl

theorem cell20_751098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 4, 4].length) (baseStart_751098 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_751098 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_751098 prefixEnd_751098 := by exact prefixLift 751098
  have htrace : WordTrace (prefixWord ++ tailWord_751098) baseStart_751098 baseEnd_751098 := by
    simpa [prefixWord, tailWord_751098, baseEnd_751098] using wordTrace_append hprefix tailTrace_751098
  have hstable : (prefixWord ++ tailWord_751098).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751098).length < 2 ^ (prefixWord ++ tailWord_751098).sum := by decide
  have hdescent : baseEnd_751098 < baseStart_751098 := by decide
  rcases family_descends (prefixWord ++ tailWord_751098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751101 : List Nat := [1, 4, 1, 1, 1, 6, 2, 4]
def baseStart_751101 : Nat := 118140960795 + 751101 * 2 ^ 59
def prefixEnd_751101 : Nat := 4983230072969 + 3 ^ 40 * 751101 * 2
def baseEnd_751101 : Nat := 114274320910450680765409

theorem tailTrace_751101 : CollatzResearch.WordTrace tailWord_751101 prefixEnd_751101 114274320910450680765409 := by
  unfold tailWord_751101
  simp only [CollatzResearch.WordTrace]
  refine ⟨27394904051896829683189157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18263269367931219788792771 27394904051896829683189157)
  ·
    refine ⟨5136544509730655565597967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27394904051896829683189157 5136544509730655565597967)
    ·
      refine ⟨7704816764595983348396951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5136544509730655565597967 7704816764595983348396951)
      ·
        refine ⟨11557225146893975022595427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7704816764595983348396951 11557225146893975022595427)
        ·
          refine ⟨17335837720340962533893141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11557225146893975022595427 17335837720340962533893141)
          ·
            refine ⟨812617393140982618776241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 17335837720340962533893141 812617393140982618776241)
            ·
              refine ⟨609463044855736964082181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 812617393140982618776241 609463044855736964082181)
              ·
                refine ⟨114274320910450680765409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 609463044855736964082181 114274320910450680765409)
                ·
                  rfl

theorem cell20_751101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 2, 4].length) (baseStart_751101 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_751101 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_751101 prefixEnd_751101 := by exact prefixLift 751101
  have htrace : WordTrace (prefixWord ++ tailWord_751101) baseStart_751101 baseEnd_751101 := by
    simpa [prefixWord, tailWord_751101, baseEnd_751101] using wordTrace_append hprefix tailTrace_751101
  have hstable : (prefixWord ++ tailWord_751101).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751101).length < 2 ^ (prefixWord ++ tailWord_751101).sum := by decide
  have hdescent : baseEnd_751101 < baseStart_751101 := by decide
  rcases family_descends (prefixWord ++ tailWord_751101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751111 : List Nat := [1, 1, 4, 3, 2, 3, 1, 3, 2]
def baseStart_751111 : Nat := 118140960795 + 751111 * 2 ^ 59
def prefixEnd_751111 : Nat := 4983230072969 + 3 ^ 40 * 751111 * 2
def baseEnd_751111 : Nat := 342827527003836451962853

theorem tailTrace_751111 : CollatzResearch.WordTrace tailWord_751111 prefixEnd_751111 342827527003836451962853 := by
  unfold tailWord_751111
  simp only [CollatzResearch.WordTrace]
  refine ⟨27395268781860601391053187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18263512521240400927368791 27395268781860601391053187)
  ·
    refine ⟨41092903172790902086579781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27395268781860601391053187 41092903172790902086579781)
    ·
      refine ⟨7704919344898294141233709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41092903172790902086579781 7704919344898294141233709)
      ·
        refine ⟨2889344754336860302962641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7704919344898294141233709 2889344754336860302962641)
        ·
          refine ⟨2167008565752645227221981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2889344754336860302962641 2167008565752645227221981)
          ·
            refine ⟨812628212157241960208243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2167008565752645227221981 812628212157241960208243)
            ·
              refine ⟨1218942318235862940312365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 812628212157241960208243 1218942318235862940312365)
              ·
                refine ⟨457103369338448602617137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1218942318235862940312365 457103369338448602617137)
                ·
                  refine ⟨342827527003836451962853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 457103369338448602617137 342827527003836451962853)
                  ·
                    rfl

theorem cell20_751111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 1, 3, 2].length) (baseStart_751111 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_751111 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_751111 prefixEnd_751111 := by exact prefixLift 751111
  have htrace : WordTrace (prefixWord ++ tailWord_751111) baseStart_751111 baseEnd_751111 := by
    simpa [prefixWord, tailWord_751111, baseEnd_751111] using wordTrace_append hprefix tailTrace_751111
  have hstable : (prefixWord ++ tailWord_751111).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751111).length < 2 ^ (prefixWord ++ tailWord_751111).sum := by decide
  have hdescent : baseEnd_751111 < baseStart_751111 := by decide
  rcases family_descends (prefixWord ++ tailWord_751111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751146 : List Nat := [3, 1, 4, 1, 1, 1, 3, 3, 3]
def baseStart_751146 : Nat := 118140960795 + 751146 * 2 ^ 59
def prefixEnd_751146 : Nat := 4983230072969 + 3 ^ 40 * 751146 * 2
def baseEnd_751146 : Nat := 342843501957531885796043

theorem tailTrace_751146 : CollatzResearch.WordTrace tailWord_751146 prefixEnd_751146 342843501957531885796043 := by
  unfold tailWord_751146
  simp only [CollatzResearch.WordTrace]
  refine ⟨6849136334183450592144323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18264363557822534912384861 6849136334183450592144323)
  ·
    refine ⟨10273704501275175888216485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6849136334183450592144323 10273704501275175888216485)
    ·
      refine ⟨1926319593989095479040591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10273704501275175888216485 1926319593989095479040591)
      ·
        refine ⟨2889479390983643218560887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1926319593989095479040591 2889479390983643218560887)
        ·
          refine ⟨4334219086475464827841331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2889479390983643218560887 4334219086475464827841331)
          ·
            refine ⟨6501328629713197241761997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4334219086475464827841331 6501328629713197241761997)
            ·
              refine ⟨2437998236142448965660749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6501328629713197241761997 2437998236142448965660749)
              ·
                refine ⟨914249338553418362122781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2437998236142448965660749 914249338553418362122781)
                ·
                  refine ⟨342843501957531885796043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 914249338553418362122781 342843501957531885796043)
                  ·
                    rfl

theorem cell20_751146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 3, 3].length) (baseStart_751146 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_751146 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_751146 prefixEnd_751146 := by exact prefixLift 751146
  have htrace : WordTrace (prefixWord ++ tailWord_751146) baseStart_751146 baseEnd_751146 := by
    simpa [prefixWord, tailWord_751146, baseEnd_751146] using wordTrace_append hprefix tailTrace_751146
  have hstable : (prefixWord ++ tailWord_751146).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751146).length < 2 ^ (prefixWord ++ tailWord_751146).sum := by decide
  have hdescent : baseEnd_751146 < baseStart_751146 := by decide
  rcases family_descends (prefixWord ++ tailWord_751146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751190 : List Nat := [5, 2, 2, 2, 2, 1, 1, 5]
def baseStart_751190 : Nat := 118140960795 + 751190 * 2 ^ 59
def prefixEnd_751190 : Nat := 4983230072969 + 3 ^ 40 * 751190 * 2
def baseEnd_751190 : Nat := 114287861585487762776399

theorem tailTrace_751190 : CollatzResearch.WordTrace tailWord_751190 prefixEnd_751190 114287861585487762776399 := by
  unfold tailWord_751190
  simp only [CollatzResearch.WordTrace]
  refine ⟨1712384384285899867698689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18265433432382931922119349 1712384384285899867698689)
  ·
    refine ⟨1284288288214424900774017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1712384384285899867698689 1284288288214424900774017)
    ·
      refine ⟨963216216160818675580513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1284288288214424900774017 963216216160818675580513)
      ·
        refine ⟨722412162120614006685385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 963216216160818675580513 722412162120614006685385)
        ·
          refine ⟨541809121590460505014039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 722412162120614006685385 541809121590460505014039)
          ·
            refine ⟨812713682385690757521059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 541809121590460505014039 812713682385690757521059)
            ·
              refine ⟨1219070523578536136281589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 812713682385690757521059 1219070523578536136281589)
              ·
                refine ⟨114287861585487762776399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1219070523578536136281589 114287861585487762776399)
                ·
                  rfl

theorem cell20_751190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 1, 5].length) (baseStart_751190 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_751190 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_751190 prefixEnd_751190 := by exact prefixLift 751190
  have htrace : WordTrace (prefixWord ++ tailWord_751190) baseStart_751190 baseEnd_751190 := by
    simpa [prefixWord, tailWord_751190, baseEnd_751190] using wordTrace_append hprefix tailTrace_751190
  have hstable : (prefixWord ++ tailWord_751190).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751190).length < 2 ^ (prefixWord ++ tailWord_751190).sum := by decide
  have hdescent : baseEnd_751190 < baseStart_751190 := by decide
  rcases family_descends (prefixWord ++ tailWord_751190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751236 : List Nat := [2, 3, 2, 1, 4, 1, 7]
def baseStart_751236 : Nat := 118140960795 + 751236 * 2 ^ 59
def prefixEnd_751236 : Nat := 4983230072969 + 3 ^ 40 * 751236 * 2
def baseEnd_751236 : Nat := 38098286712210174755075

theorem tailTrace_751236 : CollatzResearch.WordTrace tailWord_751236 prefixEnd_751236 38098286712210174755075 := by
  unfold tailWord_751236
  simp only [CollatzResearch.WordTrace]
  refine ⟨13699913953203873869676781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18266551937605165159569041 13699913953203873869676781)
  ·
    refine ⟨5137467732451452701128793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13699913953203873869676781 5137467732451452701128793)
    ·
      refine ⟨3853100799338589525846595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5137467732451452701128793 3853100799338589525846595)
      ·
        refine ⟨5779651199007884288769893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3853100799338589525846595 5779651199007884288769893)
        ·
          refine ⟨1083684599813978304144355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5779651199007884288769893 1083684599813978304144355)
          ·
            refine ⟨1625526899720967456216533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1083684599813978304144355 1625526899720967456216533)
            ·
              refine ⟨38098286712210174755075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1625526899720967456216533 38098286712210174755075)
              ·
                rfl

theorem cell20_751236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 7].length) (baseStart_751236 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_751236 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_751236 prefixEnd_751236 := by exact prefixLift 751236
  have htrace : WordTrace (prefixWord ++ tailWord_751236) baseStart_751236 baseEnd_751236 := by
    simpa [prefixWord, tailWord_751236, baseEnd_751236] using wordTrace_append hprefix tailTrace_751236
  have hstable : (prefixWord ++ tailWord_751236).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751236).length < 2 ^ (prefixWord ++ tailWord_751236).sum := by decide
  have hdescent : baseEnd_751236 < baseStart_751236 := by decide
  rcases family_descends (prefixWord ++ tailWord_751236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751246 : List Nat := [4, 1, 1, 3, 1, 2, 2, 4, 2]
def baseStart_751246 : Nat := 118140960795 + 751246 * 2 ^ 59
def prefixEnd_751246 : Nat := 4983230072969 + 3 ^ 40 * 751246 * 2
def baseEnd_751246 : Nat := 342889144682375982462301

theorem tailTrace_751246 : CollatzResearch.WordTrace tailWord_751246 prefixEnd_751246 342889144682375982462301 := by
  unfold tailWord_751246
  simp only [CollatzResearch.WordTrace]
  refine ⟨3425024079546439930902199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18266795090914346298145061 3425024079546439930902199)
  ·
    refine ⟨5137536119319659896353299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3425024079546439930902199 5137536119319659896353299)
    ·
      refine ⟨7706304178979489844529949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5137536119319659896353299 7706304178979489844529949)
      ·
        refine ⟨2889864067117308691698731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7706304178979489844529949 2889864067117308691698731)
        ·
          refine ⟨4334796100675963037548097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2889864067117308691698731 4334796100675963037548097)
          ·
            refine ⟨3251097075506972278161073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4334796100675963037548097 3251097075506972278161073)
            ·
              refine ⟨2438322806630229208620805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3251097075506972278161073 2438322806630229208620805)
              ·
                refine ⟨457185526243167976616401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2438322806630229208620805 457185526243167976616401)
                ·
                  refine ⟨342889144682375982462301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 457185526243167976616401 342889144682375982462301)
                  ·
                    rfl

theorem cell20_751246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 4, 2].length) (baseStart_751246 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_751246 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_751246 prefixEnd_751246 := by exact prefixLift 751246
  have htrace : WordTrace (prefixWord ++ tailWord_751246) baseStart_751246 baseEnd_751246 := by
    simpa [prefixWord, tailWord_751246, baseEnd_751246] using wordTrace_append hprefix tailTrace_751246
  have hstable : (prefixWord ++ tailWord_751246).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751246).length < 2 ^ (prefixWord ++ tailWord_751246).sum := by decide
  have hdescent : baseEnd_751246 < baseStart_751246 := by decide
  rcases family_descends (prefixWord ++ tailWord_751246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751319 : List Nat := [1, 1, 3, 2, 1, 3, 3, 3, 3]
def baseStart_751319 : Nat := 118140960795 + 751319 * 2 ^ 59
def prefixEnd_751319 : Nat := 4983230072969 + 3 ^ 40 * 751319 * 2
def baseEnd_751319 : Nat := 342922463871512173028669

theorem tailTrace_751319 : CollatzResearch.WordTrace tailWord_751319 prefixEnd_751319 342922463871512173028669 := by
  unfold tailWord_751319
  simp only [CollatzResearch.WordTrace]
  refine ⟨27402855165107052914625011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18268570110071368609750007 27402855165107052914625011)
  ·
    refine ⟨41104282747660579371937517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27402855165107052914625011 41104282747660579371937517)
    ·
      refine ⟨15414106030372717264476569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41104282747660579371937517 15414106030372717264476569)
      ·
        refine ⟨11560579522779537948357427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15414106030372717264476569 11560579522779537948357427)
        ·
          refine ⟨17340869284169306922536141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11560579522779537948357427 17340869284169306922536141)
          ·
            refine ⟨6502825981563490095951053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17340869284169306922536141 6502825981563490095951053)
            ·
              refine ⟨2438559743086308785981645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6502825981563490095951053 2438559743086308785981645)
              ·
                refine ⟨914459903657365794743117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2438559743086308785981645 914459903657365794743117)
                ·
                  refine ⟨342922463871512173028669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 914459903657365794743117 342922463871512173028669)
                  ·
                    rfl

theorem cell20_751319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 3, 3].length) (baseStart_751319 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_751319 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_751319 prefixEnd_751319 := by exact prefixLift 751319
  have htrace : WordTrace (prefixWord ++ tailWord_751319) baseStart_751319 baseEnd_751319 := by
    simpa [prefixWord, tailWord_751319, baseEnd_751319] using wordTrace_append hprefix tailTrace_751319
  have hstable : (prefixWord ++ tailWord_751319).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751319).length < 2 ^ (prefixWord ++ tailWord_751319).sum := by decide
  have hdescent : baseEnd_751319 < baseStart_751319 := by decide
  rcases family_descends (prefixWord ++ tailWord_751319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751333 : List Nat := [1, 3, 1, 4, 1, 1, 1, 8]
def baseStart_751333 : Nat := 118140960795 + 751333 * 2 ^ 59
def prefixEnd_751333 : Nat := 4983230072969 + 3 ^ 40 * 751333 * 2
def baseEnd_751333 : Nat := 114309617950996782187315

theorem tailTrace_751333 : CollatzResearch.WordTrace tailWord_751333 prefixEnd_751333 114309617950996782187315 := by
  unfold tailWord_751333
  simp only [CollatzResearch.WordTrace]
  refine ⟨27403365787056333305634653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18268910524704222203756435 27403365787056333305634653)
  ·
    refine ⟨10276262170146124989612995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27403365787056333305634653 10276262170146124989612995)
    ·
      refine ⟨15414393255219187484419493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10276262170146124989612995 15414393255219187484419493)
      ·
        refine ⟨2890198735353597653328655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15414393255219187484419493 2890198735353597653328655)
        ·
          refine ⟨4335298103030396479992983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2890198735353597653328655 4335298103030396479992983)
          ·
            refine ⟨6502947154545594719989475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4335298103030396479992983 6502947154545594719989475)
            ·
              refine ⟨9754420731818392079984213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6502947154545594719989475 9754420731818392079984213)
              ·
                refine ⟨114309617950996782187315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9754420731818392079984213 114309617950996782187315)
                ·
                  rfl

theorem cell20_751333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 8].length) (baseStart_751333 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_751333 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_751333 prefixEnd_751333 := by exact prefixLift 751333
  have htrace : WordTrace (prefixWord ++ tailWord_751333) baseStart_751333 baseEnd_751333 := by
    simpa [prefixWord, tailWord_751333, baseEnd_751333] using wordTrace_append hprefix tailTrace_751333
  have hstable : (prefixWord ++ tailWord_751333).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751333).length < 2 ^ (prefixWord ++ tailWord_751333).sum := by decide
  have hdescent : baseEnd_751333 < baseStart_751333 := by decide
  rcases family_descends (prefixWord ++ tailWord_751333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751340 : List Nat := [2, 2, 1, 1, 2, 2, 2, 1, 7]
def baseStart_751340 : Nat := 118140960795 + 751340 * 2 ^ 59
def prefixEnd_751340 : Nat := 4983230072969 + 3 ^ 40 * 751340 * 2
def baseEnd_751340 : Nat := 342932048843729433328583

theorem tailTrace_751340 : CollatzResearch.WordTrace tailWord_751340 prefixEnd_751340 342932048843729433328583 := by
  unfold tailWord_751340
  simp only [CollatzResearch.WordTrace]
  refine ⟨13701810549015486750569737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18269080732020649000759649 13701810549015486750569737)
  ·
    refine ⟨10276357911761615062927303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13701810549015486750569737 10276357911761615062927303)
    ·
      refine ⟨15414536867642422594390955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10276357911761615062927303 15414536867642422594390955)
      ·
        refine ⟨23121805301463633891586433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15414536867642422594390955 23121805301463633891586433)
        ·
          refine ⟨17341353976097725418689825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23121805301463633891586433 17341353976097725418689825)
          ·
            refine ⟨13006015482073294064017369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17341353976097725418689825 13006015482073294064017369)
            ·
              refine ⟨9754511611554970548013027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13006015482073294064017369 9754511611554970548013027)
              ·
                refine ⟨14631767417332455822019541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9754511611554970548013027 14631767417332455822019541)
                ·
                  refine ⟨342932048843729433328583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14631767417332455822019541 342932048843729433328583)
                  ·
                    rfl

theorem cell20_751340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 7].length) (baseStart_751340 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_751340 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_751340 prefixEnd_751340 := by exact prefixLift 751340
  have htrace : WordTrace (prefixWord ++ tailWord_751340) baseStart_751340 baseEnd_751340 := by
    simpa [prefixWord, tailWord_751340, baseEnd_751340] using wordTrace_append hprefix tailTrace_751340
  have hstable : (prefixWord ++ tailWord_751340).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751340).length < 2 ^ (prefixWord ++ tailWord_751340).sum := by decide
  have hdescent : baseEnd_751340 < baseStart_751340 := by decide
  rcases family_descends (prefixWord ++ tailWord_751340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751343 : List Nat := [1, 1, 2, 1, 5, 1, 2, 5, 2]
def baseStart_751343 : Nat := 118140960795 + 751343 * 2 ^ 59
def prefixEnd_751343 : Nat := 4983230072969 + 3 ^ 40 * 751343 * 2
def baseEnd_751343 : Nat := 342933418125474756228571

theorem tailTrace_751343 : CollatzResearch.WordTrace tailWord_751343 prefixEnd_751343 342933418125474756228571 := by
  unfold tailWord_751343
  simp only [CollatzResearch.WordTrace]
  refine ⟨27403730517020105013498683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18269153678013403342332455 27403730517020105013498683)
  ·
    refine ⟨41105595775530157520248025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27403730517020105013498683 41105595775530157520248025)
    ·
      refine ⟨30829196831647618140186019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41105595775530157520248025 30829196831647618140186019)
      ·
        refine ⟨46243795247471427210279029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30829196831647618140186019 46243795247471427210279029)
        ·
          refine ⟨4335355804450446300963659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 46243795247471427210279029 4335355804450446300963659)
          ·
            refine ⟨6503033706675669451445489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4335355804450446300963659 6503033706675669451445489)
            ·
              refine ⟨4877275280006752088584117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6503033706675669451445489 4877275280006752088584117)
              ·
                refine ⟨457244557500633008304761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4877275280006752088584117 457244557500633008304761)
                ·
                  refine ⟨342933418125474756228571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 457244557500633008304761 342933418125474756228571)
                  ·
                    rfl

theorem cell20_751343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 5, 2].length) (baseStart_751343 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_751343 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_751343 prefixEnd_751343 := by exact prefixLift 751343
  have htrace : WordTrace (prefixWord ++ tailWord_751343) baseStart_751343 baseEnd_751343 := by
    simpa [prefixWord, tailWord_751343, baseEnd_751343] using wordTrace_append hprefix tailTrace_751343
  have hstable : (prefixWord ++ tailWord_751343).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751343).length < 2 ^ (prefixWord ++ tailWord_751343).sum := by decide
  have hdescent : baseEnd_751343 < baseStart_751343 := by decide
  rcases family_descends (prefixWord ++ tailWord_751343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751367 : List Nat := [1, 1, 4, 4, 2, 2, 1, 5]
def baseStart_751367 : Nat := 118140960795 + 751367 * 2 ^ 59
def prefixEnd_751367 : Nat := 4983230072969 + 3 ^ 40 * 751367 * 2
def baseEnd_751367 : Nat := 114314790793145779809491

theorem tailTrace_751367 : CollatzResearch.WordTrace tailWord_751367 prefixEnd_751367 114314790793145779809491 := by
  unfold tailWord_751367
  simp only [CollatzResearch.WordTrace]
  refine ⟨27404605868933157112372355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18269737245955438074914903 27404605868933157112372355)
  ·
    refine ⟨41106908803399735668558533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27404605868933157112372355 41106908803399735668558533)
    ·
      refine ⟨7707545400637450437854725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41106908803399735668558533 7707545400637450437854725)
      ·
        refine ⟨1445164762619521957097761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7707545400637450437854725 1445164762619521957097761)
        ·
          refine ⟨1083873571964641467823321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1445164762619521957097761 1083873571964641467823321)
          ·
            refine ⟨812905178973481100867491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1083873571964641467823321 812905178973481100867491)
            ·
              refine ⟨1219357768460221651301237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 812905178973481100867491 1219357768460221651301237)
              ·
                refine ⟨114314790793145779809491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1219357768460221651301237 114314790793145779809491)
                ·
                  rfl

theorem cell20_751367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 1, 5].length) (baseStart_751367 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_751367 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_751367 prefixEnd_751367 := by exact prefixLift 751367
  have htrace : WordTrace (prefixWord ++ tailWord_751367) baseStart_751367 baseEnd_751367 := by
    simpa [prefixWord, tailWord_751367, baseEnd_751367] using wordTrace_append hprefix tailTrace_751367
  have hstable : (prefixWord ++ tailWord_751367).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751367).length < 2 ^ (prefixWord ++ tailWord_751367).sum := by decide
  have hdescent : baseEnd_751367 < baseStart_751367 := by decide
  rcases family_descends (prefixWord ++ tailWord_751367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751371 : List Nat := [1, 1, 1, 1, 5, 1, 5, 5]
def baseStart_751371 : Nat := 118140960795 + 751371 * 2 ^ 59
def prefixEnd_751371 : Nat := 4983230072969 + 3 ^ 40 * 751371 * 2
def baseEnd_751371 : Nat := 114315399362810367765041

theorem tailTrace_751371 : CollatzResearch.WordTrace tailWord_751371 prefixEnd_751371 114315399362810367765041 := by
  unfold tailWord_751371
  simp only [CollatzResearch.WordTrace]
  refine ⟨27404751760918665795517967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18269834507279110530345311 27404751760918665795517967)
  ·
    refine ⟨41107127641377998693276951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27404751760918665795517967 41107127641377998693276951)
    ·
      refine ⟨61660691462066998039915427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41107127641377998693276951 61660691462066998039915427)
      ·
        refine ⟨92491037193100497059873141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61660691462066998039915427 92491037193100497059873141)
        ·
          refine ⟨8671034736853171599363107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 92491037193100497059873141 8671034736853171599363107)
          ·
            refine ⟨13006552105279757399044661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8671034736853171599363107 13006552105279757399044661)
            ·
              refine ⟨1219364259869977256160437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13006552105279757399044661 1219364259869977256160437)
              ·
                refine ⟨114315399362810367765041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1219364259869977256160437 114315399362810367765041)
                ·
                  rfl

theorem cell20_751371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 5, 5].length) (baseStart_751371 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_751371 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_751371 prefixEnd_751371 := by exact prefixLift 751371
  have htrace : WordTrace (prefixWord ++ tailWord_751371) baseStart_751371 baseEnd_751371 := by
    simpa [prefixWord, tailWord_751371, baseEnd_751371] using wordTrace_append hprefix tailTrace_751371
  have hstable : (prefixWord ++ tailWord_751371).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751371).length < 2 ^ (prefixWord ++ tailWord_751371).sum := by decide
  have hdescent : baseEnd_751371 < baseStart_751371 := by decide
  rcases family_descends (prefixWord ++ tailWord_751371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751388 : List Nat := [2, 2, 3, 1, 1, 2, 5, 4]
def baseStart_751388 : Nat := 118140960795 + 751388 * 2 ^ 59
def prefixEnd_751388 : Nat := 4983230072969 + 3 ^ 40 * 751388 * 2
def baseEnd_751388 : Nat := 114317985783884866576129

theorem tailTrace_751388 : CollatzResearch.WordTrace tailWord_751388 prefixEnd_751388 114317985783884866576129 := by
  unfold tailWord_751388
  simp only [CollatzResearch.WordTrace]
  refine ⟨13702685900928538849443409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18270247867904718465924545 13702685900928538849443409)
  ·
    refine ⟨10277014425696404137082557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13702685900928538849443409 10277014425696404137082557)
    ·
      refine ⟨3853880409636151551405959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10277014425696404137082557 3853880409636151551405959)
      ·
        refine ⟨5780820614454227327108939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3853880409636151551405959 5780820614454227327108939)
        ·
          refine ⟨8671230921681340990663409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5780820614454227327108939 8671230921681340990663409)
          ·
            refine ⟨6503423191261005742997557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8671230921681340990663409 6503423191261005742997557)
            ·
              refine ⟨609695924180719288406021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6503423191261005742997557 609695924180719288406021)
              ·
                refine ⟨114317985783884866576129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 609695924180719288406021 114317985783884866576129)
                ·
                  rfl

theorem cell20_751388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 5, 4].length) (baseStart_751388 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_751388 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_751388 prefixEnd_751388 := by exact prefixLift 751388
  have htrace : WordTrace (prefixWord ++ tailWord_751388) baseStart_751388 baseEnd_751388 := by
    simpa [prefixWord, tailWord_751388, baseEnd_751388] using wordTrace_append hprefix tailTrace_751388
  have hstable : (prefixWord ++ tailWord_751388).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751388).length < 2 ^ (prefixWord ++ tailWord_751388).sum := by decide
  have hdescent : baseEnd_751388 < baseStart_751388 := by decide
  rcases family_descends (prefixWord ++ tailWord_751388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751409 : List Nat := [1, 2, 2, 3, 2, 3, 7]
def baseStart_751409 : Nat := 118140960795 + 751409 * 2 ^ 59
def prefixEnd_751409 : Nat := 4983230072969 + 3 ^ 40 * 751409 * 2
def baseEnd_751409 : Nat := 38107060258207984447589

theorem tailTrace_751409 : CollatzResearch.WordTrace tailWord_751409 prefixEnd_751409 38107060258207984447589 := by
  unfold tailWord_751409
  simp only [CollatzResearch.WordTrace]
  refine ⟨27406137734780998285401281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18270758489853998856934187 27406137734780998285401281)
  ·
    refine ⟨20554603301085748714050961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27406137734780998285401281 20554603301085748714050961)
    ·
      refine ⟨15415952475814311535538221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20554603301085748714050961 15415952475814311535538221)
      ·
        refine ⟨5780982178430366825826833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15415952475814311535538221 5780982178430366825826833)
        ·
          refine ⟨4335736633822775119370125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5780982178430366825826833 4335736633822775119370125)
          ·
            refine ⟨1625901237683540669763797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4335736633822775119370125 1625901237683540669763797)
            ·
              refine ⟨38107060258207984447589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1625901237683540669763797 38107060258207984447589)
              ·
                rfl

theorem cell20_751409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 7].length) (baseStart_751409 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_751409 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_751409 prefixEnd_751409 := by exact prefixLift 751409
  have htrace : WordTrace (prefixWord ++ tailWord_751409) baseStart_751409 baseEnd_751409 := by
    simpa [prefixWord, tailWord_751409, baseEnd_751409] using wordTrace_append hprefix tailTrace_751409
  have hstable : (prefixWord ++ tailWord_751409).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751409).length < 2 ^ (prefixWord ++ tailWord_751409).sum := by decide
  have hdescent : baseEnd_751409 < baseStart_751409 := by decide
  rcases family_descends (prefixWord ++ tailWord_751409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751412 : List Nat := [2, 5, 1, 1, 2, 2, 1, 1, 5]
def baseStart_751412 : Nat := 118140960795 + 751412 * 2 ^ 59
def prefixEnd_751412 : Nat := 4983230072969 + 3 ^ 40 * 751412 * 2
def baseEnd_751412 : Nat := 342964911605617182928289

theorem tailTrace_751412 : CollatzResearch.WordTrace tailWord_751412 prefixEnd_751412 342964911605617182928289 := by
  unfold tailWord_751412
  simp only [CollatzResearch.WordTrace]
  refine ⟨13703123576885064898880245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18270831435846753198506993 13703123576885064898880245)
  ·
    refine ⟨1284667835332974834270023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13703123576885064898880245 1284667835332974834270023)
    ·
      refine ⟨1927001752999462251405035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1284667835332974834270023 1927001752999462251405035)
      ·
        refine ⟨2890502629499193377107553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1927001752999462251405035 2890502629499193377107553)
        ·
          refine ⟨2167876972124395032830665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2890502629499193377107553 2167876972124395032830665)
          ·
            refine ⟨1625907729093296274622999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2167876972124395032830665 1625907729093296274622999)
            ·
              refine ⟨2438861593639944411934499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1625907729093296274622999 2438861593639944411934499)
              ·
                refine ⟨3658292390459916617901749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2438861593639944411934499 3658292390459916617901749)
                ·
                  refine ⟨342964911605617182928289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3658292390459916617901749 342964911605617182928289)
                  ·
                    rfl

theorem cell20_751412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_751412 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_751412 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_751412 prefixEnd_751412 := by exact prefixLift 751412
  have htrace : WordTrace (prefixWord ++ tailWord_751412) baseStart_751412 baseEnd_751412 := by
    simpa [prefixWord, tailWord_751412, baseEnd_751412] using wordTrace_append hprefix tailTrace_751412
  have hstable : (prefixWord ++ tailWord_751412).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751412).length < 2 ^ (prefixWord ++ tailWord_751412).sum := by decide
  have hdescent : baseEnd_751412 < baseStart_751412 := by decide
  rcases family_descends (prefixWord ++ tailWord_751412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751499 : List Nat := [1, 1, 1, 1, 4, 2, 1, 3, 6]
def baseStart_751499 : Nat := 118140960795 + 751499 * 2 ^ 59
def prefixEnd_751499 : Nat := 4983230072969 + 3 ^ 40 * 751499 * 2
def baseEnd_751499 : Nat := 343004620776231547027933

theorem tailTrace_751499 : CollatzResearch.WordTrace tailWord_751499 prefixEnd_751499 343004620776231547027933 := by
  unfold tailWord_751499
  simp only [CollatzResearch.WordTrace]
  refine ⟨27409420304454943656177551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18272946869636629104118367 27409420304454943656177551)
  ·
    refine ⟨41114130456682415484266327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27409420304454943656177551 41114130456682415484266327)
    ·
      refine ⟨61671195685023623226399491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41114130456682415484266327 61671195685023623226399491)
      ·
        refine ⟨92506793527535434839599237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61671195685023623226399491 92506793527535434839599237)
        ·
          refine ⟨17345023786412894032424857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92506793527535434839599237 17345023786412894032424857)
          ·
            refine ⟨13008767839809670524318643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17345023786412894032424857 13008767839809670524318643)
            ·
              refine ⟨19513151759714505786477965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13008767839809670524318643 19513151759714505786477965)
              ·
                refine ⟨7317431909892939669929237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19513151759714505786477965 7317431909892939669929237)
                ·
                  refine ⟨343004620776231547027933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7317431909892939669929237 343004620776231547027933)
                  ·
                    rfl

theorem cell20_751499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 3, 6].length) (baseStart_751499 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_751499 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_751499 prefixEnd_751499 := by exact prefixLift 751499
  have htrace : WordTrace (prefixWord ++ tailWord_751499) baseStart_751499 baseEnd_751499 := by
    simpa [prefixWord, tailWord_751499, baseEnd_751499] using wordTrace_append hprefix tailTrace_751499
  have hstable : (prefixWord ++ tailWord_751499).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751499).length < 2 ^ (prefixWord ++ tailWord_751499).sum := by decide
  have hdescent : baseEnd_751499 < baseStart_751499 := by decide
  rcases family_descends (prefixWord ++ tailWord_751499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751575 : List Nat := [1, 1, 3, 2, 1, 1, 3, 2, 6]
def baseStart_751575 : Nat := 118140960795 + 751575 * 2 ^ 59
def prefixEnd_751575 : Nat := 4983230072969 + 3 ^ 40 * 751575 * 2
def baseEnd_751575 : Nat := 343039309247113060494289

theorem tailTrace_751575 : CollatzResearch.WordTrace tailWord_751575 prefixEnd_751575 343039309247113060494289 := by
  unfold tailWord_751575
  simp only [CollatzResearch.WordTrace]
  refine ⟨27412192252179608635944179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18274794834786405757296119 27412192252179608635944179)
  ·
    refine ⟨41118288378269412953916269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27412192252179608635944179 41118288378269412953916269)
    ·
      refine ⟨15419358141851029857718601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41118288378269412953916269 15419358141851029857718601)
      ·
        refine ⟨11564518606388272393288951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15419358141851029857718601 11564518606388272393288951)
        ·
          refine ⟨17346777909582408589933427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11564518606388272393288951 17346777909582408589933427)
          ·
            refine ⟨26020166864373612884900141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17346777909582408589933427 26020166864373612884900141)
            ·
              refine ⟨9757562574140104831837553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26020166864373612884900141 9757562574140104831837553)
              ·
                refine ⟨7318171930605078623878165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9757562574140104831837553 7318171930605078623878165)
                ·
                  refine ⟨343039309247113060494289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7318171930605078623878165 343039309247113060494289)
                  ·
                    rfl

theorem cell20_751575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 2, 6].length) (baseStart_751575 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_751575 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_751575 prefixEnd_751575 := by exact prefixLift 751575
  have htrace : WordTrace (prefixWord ++ tailWord_751575) baseStart_751575 baseEnd_751575 := by
    simpa [prefixWord, tailWord_751575, baseEnd_751575] using wordTrace_append hprefix tailTrace_751575
  have hstable : (prefixWord ++ tailWord_751575).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751575).length < 2 ^ (prefixWord ++ tailWord_751575).sum := by decide
  have hdescent : baseEnd_751575 < baseStart_751575 := by decide
  rcases family_descends (prefixWord ++ tailWord_751575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751581 : List Nat := [1, 4, 3, 1, 3, 2, 1, 2, 3]
def baseStart_751581 : Nat := 118140960795 + 751581 * 2 ^ 59
def prefixEnd_751581 : Nat := 4983230072969 + 3 ^ 40 * 751581 * 2
def baseEnd_751581 : Nat := 343042047810603706294265

theorem tailTrace_751581 : CollatzResearch.WordTrace tailWord_751581 prefixEnd_751581 343042047810603706294265 := by
  unfold tailWord_751581
  simp only [CollatzResearch.WordTrace]
  refine ⟨27412411090157871660662597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18274940726771914440441731 27412411090157871660662597)
  ·
    refine ⟨5139827079404600936374237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27412411090157871660662597 5139827079404600936374237)
    ·
      refine ⟨1927435154776725351140339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5139827079404600936374237 1927435154776725351140339)
      ·
        refine ⟨2891152732165088026710509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1927435154776725351140339 2891152732165088026710509)
        ·
          refine ⟨1084182274561908010016441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2891152732165088026710509 1084182274561908010016441)
          ·
            refine ⟨813136705921431007512331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1084182274561908010016441 813136705921431007512331)
            ·
              refine ⟨1219705058882146511268497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 813136705921431007512331 1219705058882146511268497)
              ·
                refine ⟨914778794161609883451373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1219705058882146511268497 914778794161609883451373)
                ·
                  refine ⟨343042047810603706294265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 914778794161609883451373 343042047810603706294265)
                  ·
                    rfl

theorem cell20_751581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 1, 2, 3].length) (baseStart_751581 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_751581 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_751581 prefixEnd_751581 := by exact prefixLift 751581
  have htrace : WordTrace (prefixWord ++ tailWord_751581) baseStart_751581 baseEnd_751581 := by
    simpa [prefixWord, tailWord_751581, baseEnd_751581] using wordTrace_append hprefix tailTrace_751581
  have hstable : (prefixWord ++ tailWord_751581).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751581).length < 2 ^ (prefixWord ++ tailWord_751581).sum := by decide
  have hdescent : baseEnd_751581 < baseStart_751581 := by decide
  rcases family_descends (prefixWord ++ tailWord_751581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751585 : List Nat := [1, 2, 3, 1, 2, 1, 5, 2, 3]
def baseStart_751585 : Nat := 118140960795 + 751585 * 2 ^ 59
def prefixEnd_751585 : Nat := 4983230072969 + 3 ^ 40 * 751585 * 2
def baseEnd_751585 : Nat := 343043873519597470160915

theorem tailTrace_751585 : CollatzResearch.WordTrace tailWord_751585 prefixEnd_751585 343043873519597470160915 := by
  unfold tailWord_751585
  simp only [CollatzResearch.WordTrace]
  refine ⟨27412556982143380343808209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18275037988095586895872139 27412556982143380343808209)
  ·
    refine ⟨20559417736607535257856157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27412556982143380343808209 20559417736607535257856157)
    ·
      refine ⟨7709781651227825721696059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20559417736607535257856157 7709781651227825721696059)
      ·
        refine ⟨11564672476841738582544089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7709781651227825721696059 11564672476841738582544089)
        ·
          refine ⟨8673504357631303936908067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11564672476841738582544089 8673504357631303936908067)
          ·
            refine ⟨13010256536446955905362101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8673504357631303936908067 13010256536446955905362101)
            ·
              refine ⟨1219711550291902116127697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13010256536446955905362101 1219711550291902116127697)
              ·
                refine ⟨914783662718926587095773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1219711550291902116127697 914783662718926587095773)
                ·
                  refine ⟨343043873519597470160915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 914783662718926587095773 343043873519597470160915)
                  ·
                    rfl

theorem cell20_751585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 5, 2, 3].length) (baseStart_751585 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_751585 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_751585 prefixEnd_751585 := by exact prefixLift 751585
  have htrace : WordTrace (prefixWord ++ tailWord_751585) baseStart_751585 baseEnd_751585 := by
    simpa [prefixWord, tailWord_751585, baseEnd_751585] using wordTrace_append hprefix tailTrace_751585
  have hstable : (prefixWord ++ tailWord_751585).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751585).length < 2 ^ (prefixWord ++ tailWord_751585).sum := by decide
  have hdescent : baseEnd_751585 < baseStart_751585 := by decide
  rcases family_descends (prefixWord ++ tailWord_751585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751629 : List Nat := [1, 7, 1, 2, 2, 1, 6]
def baseStart_751629 : Nat := 118140960795 + 751629 * 2 ^ 59
def prefixEnd_751629 : Nat := 4983230072969 + 3 ^ 40 * 751629 * 2
def baseEnd_751629 : Nat := 38118217368725430299341

theorem tailTrace_751629 : CollatzResearch.WordTrace tailWord_751629 prefixEnd_751629 38118217368725430299341 := by
  unfold tailWord_751629
  simp only [CollatzResearch.WordTrace]
  refine ⟨27414161793983975858409941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18276107862655983905606627 27414161793983975858409941)
  ·
    refine ⟨642519417046499434181483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 27414161793983975858409941 642519417046499434181483)
    ·
      refine ⟨963779125569749151272225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 642519417046499434181483 963779125569749151272225)
      ·
        refine ⟨722834344177311863454169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 963779125569749151272225 722834344177311863454169)
        ·
          refine ⟨542125758132983897590627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 722834344177311863454169 542125758132983897590627)
          ·
            refine ⟨813188637199475846385941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 542125758132983897590627 813188637199475846385941)
            ·
              refine ⟨38118217368725430299341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 813188637199475846385941 38118217368725430299341)
              ·
                rfl

theorem cell20_751629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 6].length) (baseStart_751629 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_751629 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_751629 prefixEnd_751629 := by exact prefixLift 751629
  have htrace : WordTrace (prefixWord ++ tailWord_751629) baseStart_751629 baseEnd_751629 := by
    simpa [prefixWord, tailWord_751629, baseEnd_751629] using wordTrace_append hprefix tailTrace_751629
  have hstable : (prefixWord ++ tailWord_751629).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751629).length < 2 ^ (prefixWord ++ tailWord_751629).sum := by decide
  have hdescent : baseEnd_751629 < baseStart_751629 := by decide
  rcases family_descends (prefixWord ++ tailWord_751629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751698 : List Nat := [3, 2, 2, 1, 5, 1, 2, 2, 2]
def baseStart_751698 : Nat := 118140960795 + 751698 * 2 ^ 59
def prefixEnd_751698 : Nat := 4983230072969 + 3 ^ 40 * 751698 * 2
def baseEnd_751698 : Nat := 343095449798671299393787

theorem tailTrace_751698 : CollatzResearch.WordTrace tailWord_751698 prefixEnd_751698 343095449798671299393787 := by
  unfold tailWord_751698
  simp only [CollatzResearch.WordTrace]
  refine ⟨6854169607683500160667937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18277785620489333761781165 6854169607683500160667937)
  ·
    refine ⟨5140627205762625120500953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6854169607683500160667937 5140627205762625120500953)
    ·
      refine ⟨3855470404321968840375715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5140627205762625120500953 3855470404321968840375715)
      ·
        refine ⟨5783205606482953260563573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3855470404321968840375715 5783205606482953260563573)
        ·
          refine ⟨542175525607776868177835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5783205606482953260563573 542175525607776868177835)
          ·
            refine ⟨813263288411665302266753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 542175525607776868177835 813263288411665302266753)
            ·
              refine ⟨609947466308748976700065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 813263288411665302266753 609947466308748976700065)
              ·
                refine ⟨457460599731561732525049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 609947466308748976700065 457460599731561732525049)
                ·
                  refine ⟨343095449798671299393787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 457460599731561732525049 343095449798671299393787)
                  ·
                    rfl

theorem cell20_751698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 2, 2, 2].length) (baseStart_751698 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_751698 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_751698 prefixEnd_751698 := by exact prefixLift 751698
  have htrace : WordTrace (prefixWord ++ tailWord_751698) baseStart_751698 baseEnd_751698 := by
    simpa [prefixWord, tailWord_751698, baseEnd_751698] using wordTrace_append hprefix tailTrace_751698
  have hstable : (prefixWord ++ tailWord_751698).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751698).length < 2 ^ (prefixWord ++ tailWord_751698).sum := by decide
  have hdescent : baseEnd_751698 < baseStart_751698 := by decide
  rcases family_descends (prefixWord ++ tailWord_751698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751709 : List Nat := [1, 4, 4, 1, 1, 3, 1, 5]
def baseStart_751709 : Nat := 118140960795 + 751709 * 2 ^ 59
def prefixEnd_751709 : Nat := 4983230072969 + 3 ^ 40 * 751709 * 2
def baseEnd_751709 : Nat := 114366823499468050009025

theorem tailTrace_751709 : CollatzResearch.WordTrace tailWord_751709 prefixEnd_751709 114366823499468050009025 := by
  unfold tailWord_751709
  simp only [CollatzResearch.WordTrace]
  refine ⟨27417079633694149521322181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18278053089129433014214787 27417079633694149521322181)
  ·
    refine ⟨5140702431317653035247909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27417079633694149521322181 5140702431317653035247909)
    ·
      refine ⟨963881705872059944108983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5140702431317653035247909 963881705872059944108983)
      ·
        refine ⟨1445822558808089916163475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 963881705872059944108983 1445822558808089916163475)
        ·
          refine ⟨2168733838212134874245213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1445822558808089916163475 2168733838212134874245213)
          ·
            refine ⟨813275189329550577841955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2168733838212134874245213 813275189329550577841955)
            ·
              refine ⟨1219912783994325866762933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 813275189329550577841955 1219912783994325866762933)
              ·
                refine ⟨114366823499468050009025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1219912783994325866762933 114366823499468050009025)
                ·
                  rfl

theorem cell20_751709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 1, 5].length) (baseStart_751709 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_751709 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_751709 prefixEnd_751709 := by exact prefixLift 751709
  have htrace : WordTrace (prefixWord ++ tailWord_751709) baseStart_751709 baseEnd_751709 := by
    simpa [prefixWord, tailWord_751709, baseEnd_751709] using wordTrace_append hprefix tailTrace_751709
  have hstable : (prefixWord ++ tailWord_751709).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751709).length < 2 ^ (prefixWord ++ tailWord_751709).sum := by decide
  have hdescent : baseEnd_751709 < baseStart_751709 := by decide
  rcases family_descends (prefixWord ++ tailWord_751709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751727 : List Nat := [1, 1, 2, 1, 3, 4, 1, 1, 6]
def baseStart_751727 : Nat := 118140960795 + 751727 * 2 ^ 59
def prefixEnd_751727 : Nat := 4983230072969 + 3 ^ 40 * 751727 * 2
def baseEnd_751727 : Nat := 343108686188876087427001

theorem tailTrace_751727 : CollatzResearch.WordTrace tailWord_751727 prefixEnd_751727 343108686188876087427001 := by
  unfold tailWord_751727
  simp only [CollatzResearch.WordTrace]
  refine ⟨27417736147628938595477435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18278490765085959063651623 27417736147628938595477435)
  ·
    refine ⟨41126604221443407893216153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27417736147628938595477435 41126604221443407893216153)
    ·
      refine ⟨30844953166082555919912115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41126604221443407893216153 30844953166082555919912115)
      ·
        refine ⟨46267429749123833879868173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30844953166082555919912115 46267429749123833879868173)
        ·
          refine ⟨17350286155921437704950565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46267429749123833879868173 17350286155921437704950565)
          ·
            refine ⟨3253178654235269569678231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17350286155921437704950565 3253178654235269569678231)
            ·
              refine ⟨4879767981352904354517347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3253178654235269569678231 4879767981352904354517347)
              ·
                refine ⟨7319651972029356531776021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4879767981352904354517347 7319651972029356531776021)
                ·
                  refine ⟨343108686188876087427001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7319651972029356531776021 343108686188876087427001)
                  ·
                    rfl

theorem cell20_751727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 1, 6].length) (baseStart_751727 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_751727 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_751727 prefixEnd_751727 := by exact prefixLift 751727
  have htrace : WordTrace (prefixWord ++ tailWord_751727) baseStart_751727 baseEnd_751727 := by
    simpa [prefixWord, tailWord_751727, baseEnd_751727] using wordTrace_append hprefix tailTrace_751727
  have hstable : (prefixWord ++ tailWord_751727).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751727).length < 2 ^ (prefixWord ++ tailWord_751727).sum := by decide
  have hdescent : baseEnd_751727 < baseStart_751727 := by decide
  rcases family_descends (prefixWord ++ tailWord_751727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751730 : List Nat := [3, 2, 1, 2, 2, 3, 3, 4]
def baseStart_751730 : Nat := 118140960795 + 751730 * 2 ^ 59
def prefixEnd_751730 : Nat := 4983230072969 + 3 ^ 40 * 751730 * 2
def baseEnd_751730 : Nat := 114370018490207136775663

theorem tailTrace_751730 : CollatzResearch.WordTrace tailWord_751730 prefixEnd_751730 114370018490207136775663 := by
  unfold tailWord_751730
  simp only [CollatzResearch.WordTrace]
  refine ⟨6854461391654517526959161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18278563711078713405224429 6854461391654517526959161)
  ·
    refine ⟨5140846043740888145219371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6854461391654517526959161 5140846043740888145219371)
    ·
      refine ⟨7711269065611332217829057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5140846043740888145219371 7711269065611332217829057)
      ·
        refine ⟨5783451799208499163371793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7711269065611332217829057 5783451799208499163371793)
        ·
          refine ⟨4337588849406374372528845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5783451799208499163371793 4337588849406374372528845)
          ·
            refine ⟨1626595818527390389698317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4337588849406374372528845 1626595818527390389698317)
            ·
              refine ⟨609973431947771396136869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1626595818527390389698317 609973431947771396136869)
              ·
                refine ⟨114370018490207136775663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 609973431947771396136869 114370018490207136775663)
                ·
                  rfl

theorem cell20_751730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 3, 4].length) (baseStart_751730 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_751730 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_751730 prefixEnd_751730 := by exact prefixLift 751730
  have htrace : WordTrace (prefixWord ++ tailWord_751730) baseStart_751730 baseEnd_751730 := by
    simpa [prefixWord, tailWord_751730, baseEnd_751730] using wordTrace_append hprefix tailTrace_751730
  have hstable : (prefixWord ++ tailWord_751730).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751730).length < 2 ^ (prefixWord ++ tailWord_751730).sum := by decide
  have hdescent : baseEnd_751730 < baseStart_751730 := by decide
  rcases family_descends (prefixWord ++ tailWord_751730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751754 : List Nat := [3, 1, 2, 3, 1, 4, 1, 2, 3]
def baseStart_751754 : Nat := 118140960795 + 751754 * 2 ^ 59
def prefixEnd_751754 : Nat := 4983230072969 + 3 ^ 40 * 751754 * 2
def baseEnd_751754 : Nat := 343121009724583993526891

theorem tailTrace_751754 : CollatzResearch.WordTrace tailWord_751754 prefixEnd_751754 343121009724583993526891 := by
  unfold tailWord_751754
  simp only [CollatzResearch.WordTrace]
  refine ⟨6854680229632780551677579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18279147279020748137806877 6854680229632780551677579)
  ·
    refine ⟨10282020344449170827516369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6854680229632780551677579 10282020344449170827516369)
    ·
      refine ⟨7711515258336878120637277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10282020344449170827516369 7711515258336878120637277)
      ·
        refine ⟨2891818221876329295238979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7711515258336878120637277 2891818221876329295238979)
        ·
          refine ⟨4337727332814493942858469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2891818221876329295238979 4337727332814493942858469)
          ·
            refine ⟨813323874902717614285963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4337727332814493942858469 813323874902717614285963)
            ·
              refine ⟨1219985812354076421428945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 813323874902717614285963 1219985812354076421428945)
              ·
                refine ⟨914989359265557316071709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1219985812354076421428945 914989359265557316071709)
                ·
                  refine ⟨343121009724583993526891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 914989359265557316071709 343121009724583993526891)
                  ·
                    rfl

theorem cell20_751754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 1, 2, 3].length) (baseStart_751754 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_751754 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_751754 prefixEnd_751754 := by exact prefixLift 751754
  have htrace : WordTrace (prefixWord ++ tailWord_751754) baseStart_751754 baseEnd_751754 := by
    simpa [prefixWord, tailWord_751754, baseEnd_751754] using wordTrace_append hprefix tailTrace_751754
  have hstable : (prefixWord ++ tailWord_751754).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751754).length < 2 ^ (prefixWord ++ tailWord_751754).sum := by decide
  have hdescent : baseEnd_751754 < baseStart_751754 := by decide
  rcases family_descends (prefixWord ++ tailWord_751754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751799 : List Nat := [1, 1, 3, 1, 4, 2, 3, 3, 2]
def baseStart_751799 : Nat := 118140960795 + 751799 * 2 ^ 59
def prefixEnd_751799 : Nat := 4983230072969 + 3 ^ 40 * 751799 * 2
def baseEnd_751799 : Nat := 343141548950763837026707

theorem tailTrace_751799 : CollatzResearch.WordTrace tailWord_751799 prefixEnd_751799 343141548950763837026707 := by
  unfold tailWord_751799
  simp only [CollatzResearch.WordTrace]
  refine ⟨27420362203368094892098451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18280241468912063261398967 27420362203368094892098451)
  ·
    refine ⟨41130543305052142338147677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27420362203368094892098451 41130543305052142338147677)
    ·
      refine ⟨15423953739394553376805379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41130543305052142338147677 15423953739394553376805379)
      ·
        refine ⟨23135930609091830065208069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15423953739394553376805379 23135930609091830065208069)
        ·
          refine ⟨4337986989204718137226513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23135930609091830065208069 4337986989204718137226513)
          ·
            refine ⟨3253490241903538602919885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4337986989204718137226513 3253490241903538602919885)
            ·
              refine ⟨1220058840713826976094957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3253490241903538602919885 1220058840713826976094957)
              ·
                refine ⟨457522065267685116035609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1220058840713826976094957 457522065267685116035609)
                ·
                  refine ⟨343141548950763837026707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 457522065267685116035609 343141548950763837026707)
                  ·
                    rfl

theorem cell20_751799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 3, 3, 2].length) (baseStart_751799 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_751799 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_751799 prefixEnd_751799 := by exact prefixLift 751799
  have htrace : WordTrace (prefixWord ++ tailWord_751799) baseStart_751799 baseEnd_751799 := by
    simpa [prefixWord, tailWord_751799, baseEnd_751799] using wordTrace_append hprefix tailTrace_751799
  have hstable : (prefixWord ++ tailWord_751799).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751799).length < 2 ^ (prefixWord ++ tailWord_751799).sum := by decide
  have hdescent : baseEnd_751799 < baseStart_751799 := by decide
  rcases family_descends (prefixWord ++ tailWord_751799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751806 : List Nat := [4, 2, 1, 1, 4, 2, 6]
def baseStart_751806 : Nat := 118140960795 + 751806 * 2 ^ 59
def prefixEnd_751806 : Nat := 4983230072969 + 3 ^ 40 * 751806 * 2
def baseEnd_751806 : Nat := 38127193771278102643705

theorem tailTrace_751806 : CollatzResearch.WordTrace tailWord_751806 prefixEnd_751806 38127193771278102643705 := by
  unfold tailWord_751806
  simp only [CollatzResearch.WordTrace]
  refine ⟨3427577189292841885950409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18280411676228490058402181 3427577189292841885950409)
  ·
    refine ⟨2570682891969631414462807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3427577189292841885950409 2570682891969631414462807)
    ·
      refine ⟨3856024337954447121694211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2570682891969631414462807 3856024337954447121694211)
      ·
        refine ⟨5784036506931670682541317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3856024337954447121694211 5784036506931670682541317)
        ·
          refine ⟨1084506845049688252976497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5784036506931670682541317 1084506845049688252976497)
          ·
            refine ⟨813380133787266189732373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1084506845049688252976497 813380133787266189732373)
            ·
              refine ⟨38127193771278102643705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 813380133787266189732373 38127193771278102643705)
              ·
                rfl

theorem cell20_751806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 6].length) (baseStart_751806 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_751806 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_751806 prefixEnd_751806 := by exact prefixLift 751806
  have htrace : WordTrace (prefixWord ++ tailWord_751806) baseStart_751806 baseEnd_751806 := by
    simpa [prefixWord, tailWord_751806, baseEnd_751806] using wordTrace_append hprefix tailTrace_751806
  have hstable : (prefixWord ++ tailWord_751806).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751806).length < 2 ^ (prefixWord ++ tailWord_751806).sum := by decide
  have hdescent : baseEnd_751806 < baseStart_751806 := by decide
  rcases family_descends (prefixWord ++ tailWord_751806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751841 : List Nat := [1, 2, 3, 1, 3, 1, 2, 1, 6]
def baseStart_751841 : Nat := 118140960795 + 751841 * 2 ^ 59
def prefixEnd_751841 : Nat := 4983230072969 + 3 ^ 40 * 751841 * 2
def baseEnd_751841 : Nat := 343160718895198357626535

theorem tailTrace_751841 : CollatzResearch.WordTrace tailWord_751841 prefixEnd_751841 343160718895198357626535 := by
  unfold tailWord_751841
  simp only [CollatzResearch.WordTrace]
  refine ⟨27421894069215936065127377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18281262712810624043418251 27421894069215936065127377)
  ·
    refine ⟨20566420551911952048845533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27421894069215936065127377 20566420551911952048845533)
    ·
      refine ⟨7712407706966982018317075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20566420551911952048845533 7712407706966982018317075)
      ·
        refine ⟨11568611560450473027475613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7712407706966982018317075 11568611560450473027475613)
        ·
          refine ⟨4338229335168927385303355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11568611560450473027475613 4338229335168927385303355)
          ·
            refine ⟨6507344002753391077955033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4338229335168927385303355 6507344002753391077955033)
            ·
              refine ⟨4880508002065043308466275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6507344002753391077955033 4880508002065043308466275)
              ·
                refine ⟨7320762003097564962699413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4880508002065043308466275 7320762003097564962699413)
                ·
                  refine ⟨343160718895198357626535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7320762003097564962699413 343160718895198357626535)
                  ·
                    rfl

theorem cell20_751841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 1, 6].length) (baseStart_751841 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_751841 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_751841 prefixEnd_751841 := by exact prefixLift 751841
  have htrace : WordTrace (prefixWord ++ tailWord_751841) baseStart_751841 baseEnd_751841 := by
    simpa [prefixWord, tailWord_751841, baseEnd_751841] using wordTrace_append hprefix tailTrace_751841
  have hstable : (prefixWord ++ tailWord_751841).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751841).length < 2 ^ (prefixWord ++ tailWord_751841).sum := by decide
  have hdescent : baseEnd_751841 < baseStart_751841 := by decide
  rcases family_descends (prefixWord ++ tailWord_751841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751872 : List Nat := [2, 1, 1, 2, 1, 1, 5, 4, 3]
def baseStart_751872 : Nat := 118140960795 + 751872 * 2 ^ 59
def prefixEnd_751872 : Nat := 4983230072969 + 3 ^ 40 * 751872 * 2
def baseEnd_751872 : Nat := 343174868139900027593075

theorem tailTrace_751872 : CollatzResearch.WordTrace tailWord_751872 prefixEnd_751872 343174868139900027593075 := by
  unfold tailWord_751872
  simp only [CollatzResearch.WordTrace]
  refine ⟨13711512366051814179752935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18282016488069085573003913 13711512366051814179752935)
  ·
    refine ⟨20567268549077721269629403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13711512366051814179752935 20567268549077721269629403)
    ·
      refine ⟨30850902823616581904444105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20567268549077721269629403 30850902823616581904444105)
      ·
        refine ⟨23138177117712436428333079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30850902823616581904444105 23138177117712436428333079)
        ·
          refine ⟨34707265676568654642499619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23138177117712436428333079 34707265676568654642499619)
          ·
            refine ⟨52060898514852981963749429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34707265676568654642499619 52060898514852981963749429)
            ·
              refine ⟨4880709235767467059101509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52060898514852981963749429 4880709235767467059101509)
              ·
                refine ⟨915132981706400073581533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4880709235767467059101509 915132981706400073581533)
                ·
                  refine ⟨343174868139900027593075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 915132981706400073581533 343174868139900027593075)
                  ·
                    rfl

theorem cell20_751872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 4, 3].length) (baseStart_751872 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_751872 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_751872 prefixEnd_751872 := by exact prefixLift 751872
  have htrace : WordTrace (prefixWord ++ tailWord_751872) baseStart_751872 baseEnd_751872 := by
    simpa [prefixWord, tailWord_751872, baseEnd_751872] using wordTrace_append hprefix tailTrace_751872
  have hstable : (prefixWord ++ tailWord_751872).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751872).length < 2 ^ (prefixWord ++ tailWord_751872).sum := by decide
  have hdescent : baseEnd_751872 < baseStart_751872 := by decide
  rcases family_descends (prefixWord ++ tailWord_751872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751934 : List Nat := [4, 2, 1, 2, 1, 2, 1, 3, 4]
def baseStart_751934 : Nat := 118140960795 + 751934 * 2 ^ 59
def prefixEnd_751934 : Nat := 4983230072969 + 3 ^ 40 * 751934 * 2
def baseEnd_751934 : Nat := 343203166629303367526155

theorem tailTrace_751934 : CollatzResearch.WordTrace tailWord_751934 prefixEnd_751934 343203166629303367526155 := by
  unfold tailWord_751934
  simp only [CollatzResearch.WordTrace]
  refine ⟨3428160757234876618532857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18283524038586008632175237 3428160757234876618532857)
  ·
    refine ⟨2571120567926157463899643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3428160757234876618532857 2571120567926157463899643)
    ·
      refine ⟨3856680851889236195849465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2571120567926157463899643 3856680851889236195849465)
      ·
        refine ⟨2892510638916927146887099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3856680851889236195849465 2892510638916927146887099)
        ·
          refine ⟨4338765958375390720330649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2892510638916927146887099 4338765958375390720330649)
          ·
            refine ⟨3254074468781543040247987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4338765958375390720330649 3254074468781543040247987)
            ·
              refine ⟨4881111703172314560371981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3254074468781543040247987 4881111703172314560371981)
              ·
                refine ⟨1830416888689617960139493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4881111703172314560371981 1830416888689617960139493)
                ·
                  refine ⟨343203166629303367526155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1830416888689617960139493 343203166629303367526155)
                  ·
                    rfl

theorem cell20_751934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_751934 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_751934 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_751934 prefixEnd_751934 := by exact prefixLift 751934
  have htrace : WordTrace (prefixWord ++ tailWord_751934) baseStart_751934 baseEnd_751934 := by
    simpa [prefixWord, tailWord_751934, baseEnd_751934] using wordTrace_append hprefix tailTrace_751934
  have hstable : (prefixWord ++ tailWord_751934).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751934).length < 2 ^ (prefixWord ++ tailWord_751934).sum := by decide
  have hdescent : baseEnd_751934 < baseStart_751934 := by decide
  rcases family_descends (prefixWord ++ tailWord_751934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751964 : List Nat := [2, 2, 4, 3, 2, 1, 1, 3, 2]
def baseStart_751964 : Nat := 118140960795 + 751964 * 2 ^ 59
def prefixEnd_751964 : Nat := 4983230072969 + 3 ^ 40 * 751964 * 2
def baseEnd_751964 : Nat := 343216859446756596526033

theorem tailTrace_751964 : CollatzResearch.WordTrace tailWord_751964 prefixEnd_751964 343216859446756596526033 := by
  unfold tailWord_751964
  simp only [CollatzResearch.WordTrace]
  refine ⟨13713190123885164035927473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18284253498513552047903297 13713190123885164035927473)
  ·
    refine ⟨10284892592913873026945605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13713190123885164035927473 10284892592913873026945605)
    ·
      refine ⟨1928417361171351192552301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10284892592913873026945605 1928417361171351192552301)
      ·
        refine ⟨723156510439256697207113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1928417361171351192552301 723156510439256697207113)
        ·
          refine ⟨542367382829442522905335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 723156510439256697207113 542367382829442522905335)
          ·
            refine ⟨813551074244163784358003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 542367382829442522905335 813551074244163784358003)
            ·
              refine ⟨1220326611366245676537005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 813551074244163784358003 1220326611366245676537005)
              ·
                refine ⟨457622479262342128701377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1220326611366245676537005 457622479262342128701377)
                ·
                  refine ⟨343216859446756596526033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 457622479262342128701377 343216859446756596526033)
                  ·
                    rfl

theorem cell20_751964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 1, 3, 2].length) (baseStart_751964 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_751964 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_751964 prefixEnd_751964 := by exact prefixLift 751964
  have htrace : WordTrace (prefixWord ++ tailWord_751964) baseStart_751964 baseEnd_751964 := by
    simpa [prefixWord, tailWord_751964, baseEnd_751964] using wordTrace_append hprefix tailTrace_751964
  have hstable : (prefixWord ++ tailWord_751964).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751964).length < 2 ^ (prefixWord ++ tailWord_751964).sum := by decide
  have hdescent : baseEnd_751964 < baseStart_751964 := by decide
  rcases family_descends (prefixWord ++ tailWord_751964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751968 : List Nat := [2, 1, 1, 3, 5, 2, 1, 3, 2]
def baseStart_751968 : Nat := 118140960795 + 751968 * 2 ^ 59
def prefixEnd_751968 : Nat := 4983230072969 + 3 ^ 40 * 751968 * 2
def baseEnd_751968 : Nat := 343218685155750360392683

theorem tailTrace_751968 : CollatzResearch.WordTrace tailWord_751968 prefixEnd_751968 343218685155750360392683 := by
  unfold tailWord_751968
  simp only [CollatzResearch.WordTrace]
  refine ⟨13713263069877918377500279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18284350759837224503333705 13713263069877918377500279)
  ·
    refine ⟨20569894604816877566250419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13713263069877918377500279 20569894604816877566250419)
    ·
      refine ⟨30854841907225316349375629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20569894604816877566250419 30854841907225316349375629)
      ·
        refine ⟨11570565715209493631015861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30854841907225316349375629 11570565715209493631015861)
        ·
          refine ⟨1084740535800890027907737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11570565715209493631015861 1084740535800890027907737)
          ·
            refine ⟨813555401850667520930803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1084740535800890027907737 813555401850667520930803)
            ·
              refine ⟨1220333102776001281396205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 813555401850667520930803 1220333102776001281396205)
              ·
                refine ⟨457624913541000480523577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1220333102776001281396205 457624913541000480523577)
                ·
                  refine ⟨343218685155750360392683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 457624913541000480523577 343218685155750360392683)
                  ·
                    rfl

theorem cell20_751968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 1, 3, 2].length) (baseStart_751968 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_751968 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_751968 prefixEnd_751968 := by exact prefixLift 751968
  have htrace : WordTrace (prefixWord ++ tailWord_751968) baseStart_751968 baseEnd_751968 := by
    simpa [prefixWord, tailWord_751968, baseEnd_751968] using wordTrace_append hprefix tailTrace_751968
  have hstable : (prefixWord ++ tailWord_751968).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751968).length < 2 ^ (prefixWord ++ tailWord_751968).sum := by decide
  have hdescent : baseEnd_751968 < baseStart_751968 := by decide
  rcases family_descends (prefixWord ++ tailWord_751968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751986 : List Nat := [3, 2, 1, 2, 1, 3, 2, 1, 5]
def baseStart_751986 : Nat := 118140960795 + 751986 * 2 ^ 59
def prefixEnd_751986 : Nat := 4983230072969 + 3 ^ 40 * 751986 * 2
def baseEnd_751986 : Nat := 343226900846222297792609

theorem tailTrace_751986 : CollatzResearch.WordTrace tailWord_751986 prefixEnd_751986 343226900846222297792609 := by
  unfold tailWord_751986
  simp only [CollatzResearch.WordTrace]
  refine ⟨6856795663422656457288953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18284788435793750552770541 6856795663422656457288953)
  ·
    refine ⟨5142596747566992342966715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6856795663422656457288953 5142596747566992342966715)
    ·
      refine ⟨7713895121350488514450073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5142596747566992342966715 7713895121350488514450073)
      ·
        refine ⟨5785421341012866385837555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7713895121350488514450073 5785421341012866385837555)
        ·
          refine ⟨8678132011519299578756333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5785421341012866385837555 8678132011519299578756333)
          ·
            refine ⟨3254299504319737342033625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8678132011519299578756333 3254299504319737342033625)
            ·
              refine ⟨2440724628239803006525219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3254299504319737342033625 2440724628239803006525219)
              ·
                refine ⟨3661086942359704509787829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2440724628239803006525219 3661086942359704509787829)
                ·
                  refine ⟨343226900846222297792609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3661086942359704509787829 343226900846222297792609)
                  ·
                    rfl

theorem cell20_751986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 1, 5].length) (baseStart_751986 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_751986 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_751986 prefixEnd_751986 := by exact prefixLift 751986
  have htrace : WordTrace (prefixWord ++ tailWord_751986) baseStart_751986 baseEnd_751986 := by
    simpa [prefixWord, tailWord_751986, baseEnd_751986] using wordTrace_append hprefix tailTrace_751986
  have hstable : (prefixWord ++ tailWord_751986).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751986).length < 2 ^ (prefixWord ++ tailWord_751986).sum := by decide
  have hdescent : baseEnd_751986 < baseStart_751986 := by decide
  rcases family_descends (prefixWord ++ tailWord_751986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751989 : List Nat := [1, 3, 4, 1, 2, 3, 1, 1, 4]
def baseStart_751989 : Nat := 118140960795 + 751989 * 2 ^ 59
def prefixEnd_751989 : Nat := 4983230072969 + 3 ^ 40 * 751989 * 2
def baseEnd_751989 : Nat := 343228270127967620692597

theorem tailTrace_751989 : CollatzResearch.WordTrace tailWord_751989 prefixEnd_751989 343228270127967620692597 := by
  unfold tailWord_751989
  simp only [CollatzResearch.WordTrace]
  refine ⟨27427292072679757341515021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18284861381786504894343347 27427292072679757341515021)
  ·
    refine ⟨10285234527254909003068133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27427292072679757341515021 10285234527254909003068133)
    ·
      refine ⟨1928481473860295438075275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10285234527254909003068133 1928481473860295438075275)
      ·
        refine ⟨2892722210790443157112913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1928481473860295438075275 2892722210790443157112913)
        ·
          refine ⟨2169541658092832367834685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2892722210790443157112913 2169541658092832367834685)
          ·
            refine ⟨813578121784812137938007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2169541658092832367834685 813578121784812137938007)
            ·
              refine ⟨1220367182677218206907011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 813578121784812137938007 1220367182677218206907011)
              ·
                refine ⟨1830550774015827310360517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1220367182677218206907011 1830550774015827310360517)
                ·
                  refine ⟨343228270127967620692597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1830550774015827310360517 343228270127967620692597)
                  ·
                    rfl

theorem cell20_751989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 1, 1, 4].length) (baseStart_751989 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_751989 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_751989 prefixEnd_751989 := by exact prefixLift 751989
  have htrace : WordTrace (prefixWord ++ tailWord_751989) baseStart_751989 baseEnd_751989 := by
    simpa [prefixWord, tailWord_751989, baseEnd_751989] using wordTrace_append hprefix tailTrace_751989
  have hstable : (prefixWord ++ tailWord_751989).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751989).length < 2 ^ (prefixWord ++ tailWord_751989).sum := by decide
  have hdescent : baseEnd_751989 < baseStart_751989 := by decide
  rcases family_descends (prefixWord ++ tailWord_751989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752003 : List Nat := [1, 1, 1, 3, 6, 1, 1, 3, 3]
def baseStart_752003 : Nat := 118140960795 + 752003 * 2 ^ 59
def prefixEnd_752003 : Nat := 4983230072969 + 3 ^ 40 * 752003 * 2
def baseEnd_752003 : Nat := 343234660109445794225873

theorem tailTrace_752003 : CollatzResearch.WordTrace tailWord_752003 prefixEnd_752003 343234660109445794225873 := by
  unfold tailWord_752003
  simp only [CollatzResearch.WordTrace]
  refine ⟨27427802694629037732524663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18285201796419358488349775 27427802694629037732524663)
  ·
    refine ⟨41141704041943556598786995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27427802694629037732524663 41141704041943556598786995)
    ·
      refine ⟨61712556062915334898180493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41141704041943556598786995 61712556062915334898180493)
      ·
        refine ⟨23142208523593250586817685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61712556062915334898180493 23142208523593250586817685)
        ·
          refine ⟨1084791024543433621257079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 23142208523593250586817685 1084791024543433621257079)
          ·
            refine ⟨1627186536815150431885619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1084791024543433621257079 1627186536815150431885619)
            ·
              refine ⟨2440779805222725647828429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1627186536815150431885619 2440779805222725647828429)
              ·
                refine ⟨915292426958522117935661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2440779805222725647828429 915292426958522117935661)
                ·
                  refine ⟨343234660109445794225873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 915292426958522117935661 343234660109445794225873)
                  ·
                    rfl

theorem cell20_752003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 3, 3].length) (baseStart_752003 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_752003 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_752003 prefixEnd_752003 := by exact prefixLift 752003
  have htrace : WordTrace (prefixWord ++ tailWord_752003) baseStart_752003 baseEnd_752003 := by
    simpa [prefixWord, tailWord_752003, baseEnd_752003] using wordTrace_append hprefix tailTrace_752003
  have hstable : (prefixWord ++ tailWord_752003).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752003).length < 2 ^ (prefixWord ++ tailWord_752003).sum := by decide
  have hdescent : baseEnd_752003 < baseStart_752003 := by decide
  rcases family_descends (prefixWord ++ tailWord_752003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752055 : List Nat := [1, 1, 3, 1, 3, 5, 1, 5]
def baseStart_752055 : Nat := 118140960795 + 752055 * 2 ^ 59
def prefixEnd_752055 : Nat := 4983230072969 + 3 ^ 40 * 752055 * 2
def baseEnd_752055 : Nat := 114419464775454908164109

theorem tailTrace_752055 : CollatzResearch.WordTrace tailWord_752055 prefixEnd_752055 114419464775454908164109 := by
  unfold tailWord_752055
  simp only [CollatzResearch.WordTrace]
  refine ⟨27429699290440650613417619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18286466193627100408945079 27429699290440650613417619)
  ·
    refine ⟨41144548935660975920126429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27429699290440650613417619 41144548935660975920126429)
    ·
      refine ⟨15429205850872865970047411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41144548935660975920126429 15429205850872865970047411)
      ·
        refine ⟨23143808776309298955071117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15429205850872865970047411 23143808776309298955071117)
        ·
          refine ⟨8678928291115987108151669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23143808776309298955071117 8678928291115987108151669)
          ·
            refine ⟨813649527292123791389219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8678928291115987108151669 813649527292123791389219)
            ·
              refine ⟨1220474290938185687083829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 813649527292123791389219 1220474290938185687083829)
              ·
                refine ⟨114419464775454908164109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1220474290938185687083829 114419464775454908164109)
                ·
                  rfl

theorem cell20_752055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 1, 5].length) (baseStart_752055 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_752055 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_752055 prefixEnd_752055 := by exact prefixLift 752055
  have htrace : WordTrace (prefixWord ++ tailWord_752055) baseStart_752055 baseEnd_752055 := by
    simpa [prefixWord, tailWord_752055, baseEnd_752055] using wordTrace_append hprefix tailTrace_752055
  have hstable : (prefixWord ++ tailWord_752055).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752055).length < 2 ^ (prefixWord ++ tailWord_752055).sum := by decide
  have hdescent : baseEnd_752055 < baseStart_752055 := by decide
  rcases family_descends (prefixWord ++ tailWord_752055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752086 : List Nat := [5, 2, 1, 1, 1, 1, 1, 2, 6]
def baseStart_752086 : Nat := 118140960795 + 752086 * 2 ^ 59
def prefixEnd_752086 : Nat := 4983230072969 + 3 ^ 40 * 752086 * 2
def baseEnd_752086 : Nat := 343272543571066394458867

theorem tailTrace_752086 : CollatzResearch.WordTrace tailWord_752086 prefixEnd_752086 343272543571066394458867 := by
  unfold tailWord_752086
  simp only [CollatzResearch.WordTrace]
  refine ⟨1714426872083021431737257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18287219968885561938530741 1714426872083021431737257)
  ·
    refine ⟨1285820154062266073802943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1714426872083021431737257 1285820154062266073802943)
    ·
      refine ⟨1928730231093399110704415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1285820154062266073802943 1928730231093399110704415)
      ·
        refine ⟨2893095346640098666056623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1928730231093399110704415 2893095346640098666056623)
        ·
          refine ⟨4339643019960147999084935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2893095346640098666056623 4339643019960147999084935)
          ·
            refine ⟨6509464529940221998627403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4339643019960147999084935 6509464529940221998627403)
            ·
              refine ⟨9764196794910332997941105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6509464529940221998627403 9764196794910332997941105)
              ·
                refine ⟨7323147596182749748455829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9764196794910332997941105 7323147596182749748455829)
                ·
                  refine ⟨343272543571066394458867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7323147596182749748455829 343272543571066394458867)
                  ·
                    rfl

theorem cell20_752086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_752086 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_752086 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_752086 prefixEnd_752086 := by exact prefixLift 752086
  have htrace : WordTrace (prefixWord ++ tailWord_752086) baseStart_752086 baseEnd_752086 := by
    simpa [prefixWord, tailWord_752086, baseEnd_752086] using wordTrace_append hprefix tailTrace_752086
  have hstable : (prefixWord ++ tailWord_752086).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752086).length < 2 ^ (prefixWord ++ tailWord_752086).sum := by decide
  have hdescent : baseEnd_752086 < baseStart_752086 := by decide
  rcases family_descends (prefixWord ++ tailWord_752086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752107 : List Nat := [1, 1, 1, 1, 2, 3, 6, 1, 4]
def baseStart_752107 : Nat := 118140960795 + 752107 * 2 ^ 59
def prefixEnd_752107 : Nat := 4983230072969 + 3 ^ 40 * 752107 * 2
def baseEnd_752107 : Nat := 343282128543283654758781

theorem tailTrace_752107 : CollatzResearch.WordTrace tailWord_752107 prefixEnd_752107 343282128543283654758781 := by
  unfold tailWord_752107
  simp only [CollatzResearch.WordTrace]
  refine ⟨27431595886252263494310575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18287730590834842329540383 27431595886252263494310575)
  ·
    refine ⟨41147393829378395241465863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27431595886252263494310575 41147393829378395241465863)
    ·
      refine ⟨61721090744067592862198795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41147393829378395241465863 61721090744067592862198795)
      ·
        refine ⟨92581636116101389293298193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61721090744067592862198795 92581636116101389293298193)
        ·
          refine ⟨69436227087076041969973645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92581636116101389293298193 69436227087076041969973645)
          ·
            refine ⟨26038585157653515738740117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69436227087076041969973645 26038585157653515738740117)
            ·
              refine ⟨1220558679265008550253443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 26038585157653515738740117 1220558679265008550253443)
              ·
                refine ⟨1830838018897512825380165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1220558679265008550253443 1830838018897512825380165)
                ·
                  refine ⟨343282128543283654758781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1830838018897512825380165 343282128543283654758781)
                  ·
                    rfl

theorem cell20_752107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 6, 1, 4].length) (baseStart_752107 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_752107 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_752107 prefixEnd_752107 := by exact prefixLift 752107
  have htrace : WordTrace (prefixWord ++ tailWord_752107) baseStart_752107 baseEnd_752107 := by
    simpa [prefixWord, tailWord_752107, baseEnd_752107] using wordTrace_append hprefix tailTrace_752107
  have hstable : (prefixWord ++ tailWord_752107).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752107).length < 2 ^ (prefixWord ++ tailWord_752107).sum := by decide
  have hdescent : baseEnd_752107 < baseStart_752107 := by decide
  rcases family_descends (prefixWord ++ tailWord_752107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752148 : List Nat := [2, 4, 3, 1, 1, 3, 6]
def baseStart_752148 : Nat := 118140960795 + 752148 * 2 ^ 59
def prefixEnd_752148 : Nat := 4983230072969 + 3 ^ 40 * 752148 * 2
def baseEnd_752148 : Nat := 38144538006718859376883

theorem tailTrace_752148 : CollatzResearch.WordTrace tailWord_752148 prefixEnd_752148 38144538006718859376883 := by
  unfold tailWord_752148
  simp only [CollatzResearch.WordTrace]
  refine ⟨13716545639551863748276549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18288727519402484997702065 13716545639551863748276549)
  ·
    refine ⟨2571852307415974452801853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13716545639551863748276549 2571852307415974452801853)
    ·
      refine ⟨964444615280990419800695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2571852307415974452801853 964444615280990419800695)
      ·
        refine ⟨1446666922921485629701043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 964444615280990419800695 1446666922921485629701043)
        ·
          refine ⟨2170000384382228444551565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1446666922921485629701043 2170000384382228444551565)
          ·
            refine ⟨813750144143335666706837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2170000384382228444551565 813750144143335666706837)
            ·
              refine ⟨38144538006718859376883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 813750144143335666706837 38144538006718859376883)
              ·
                rfl

theorem cell20_752148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 6].length) (baseStart_752148 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_752148 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_752148 prefixEnd_752148 := by exact prefixLift 752148
  have htrace : WordTrace (prefixWord ++ tailWord_752148) baseStart_752148 baseEnd_752148 := by
    simpa [prefixWord, tailWord_752148, baseEnd_752148] using wordTrace_append hprefix tailTrace_752148
  have hstable : (prefixWord ++ tailWord_752148).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752148).length < 2 ^ (prefixWord ++ tailWord_752148).sum := by decide
  have hdescent : baseEnd_752148 < baseStart_752148 := by decide
  rcases family_descends (prefixWord ++ tailWord_752148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752152 : List Nat := [2, 1, 2, 3, 3, 1, 8]
def baseStart_752152 : Nat := 118140960795 + 752152 * 2 ^ 59
def prefixEnd_752152 : Nat := 4983230072969 + 3 ^ 40 * 752152 * 2
def baseEnd_752152 : Nat := 38144740863273722028733

theorem tailTrace_752152 : CollatzResearch.WordTrace tailWord_752152 prefixEnd_752152 38144740863273722028733 := by
  unfold tailWord_752152
  simp only [CollatzResearch.WordTrace]
  refine ⟨13716618585544618089849355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18288824780726157453132473 13716618585544618089849355)
  ·
    refine ⟨20574927878316927134774033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13716618585544618089849355 20574927878316927134774033)
    ·
      refine ⟨15431195908737695351080525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20574927878316927134774033 15431195908737695351080525)
      ·
        refine ⟨5786698465776635756655197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15431195908737695351080525 5786698465776635756655197)
        ·
          refine ⟨2170011924666238408745699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5786698465776635756655197 2170011924666238408745699)
          ·
            refine ⟨3255017886999357613118549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2170011924666238408745699 3255017886999357613118549)
            ·
              refine ⟨38144740863273722028733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3255017886999357613118549 38144740863273722028733)
              ·
                rfl

theorem cell20_752152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 8].length) (baseStart_752152 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_752152 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_752152 prefixEnd_752152 := by exact prefixLift 752152
  have htrace : WordTrace (prefixWord ++ tailWord_752152) baseStart_752152 baseEnd_752152 := by
    simpa [prefixWord, tailWord_752152, baseEnd_752152] using wordTrace_append hprefix tailTrace_752152
  have hstable : (prefixWord ++ tailWord_752152).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752152).length < 2 ^ (prefixWord ++ tailWord_752152).sum := by decide
  have hdescent : baseEnd_752152 < baseStart_752152 := by decide
  rcases family_descends (prefixWord ++ tailWord_752152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752238 : List Nat := [4, 1, 2, 2, 2, 2, 1, 2, 4]
def baseStart_752238 : Nat := 118140960795 + 752238 * 2 ^ 59
def prefixEnd_752238 : Nat := 4983230072969 + 3 ^ 40 * 752238 * 2
def baseEnd_752238 : Nat := 343341920512829421391579

theorem tailTrace_752238 : CollatzResearch.WordTrace tailWord_752238 prefixEnd_752238 343341920512829421391579 := by
  unfold tailWord_752238
  simp only [CollatzResearch.WordTrace]
  refine ⟨3429546731097209108416171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18290915899185115244886245 3429546731097209108416171)
  ·
    refine ⟨5144320096645813662624257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3429546731097209108416171 5144320096645813662624257)
    ·
      refine ⟨3858240072484360246968193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5144320096645813662624257 3858240072484360246968193)
      ·
        refine ⟨2893680054363270185226145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3858240072484360246968193 2893680054363270185226145)
        ·
          refine ⟨2170260040772452638919609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2893680054363270185226145 2170260040772452638919609)
          ·
            refine ⟨1627695030579339479189707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2170260040772452638919609 1627695030579339479189707)
            ·
              refine ⟨2441542545869009218784561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1627695030579339479189707 2441542545869009218784561)
              ·
                refine ⟨1831156909401756914088421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2441542545869009218784561 1831156909401756914088421)
                ·
                  refine ⟨343341920512829421391579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1831156909401756914088421 343341920512829421391579)
                  ·
                    rfl

theorem cell20_752238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 2, 4].length) (baseStart_752238 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_752238 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_752238 prefixEnd_752238 := by exact prefixLift 752238
  have htrace : WordTrace (prefixWord ++ tailWord_752238) baseStart_752238 baseEnd_752238 := by
    simpa [prefixWord, tailWord_752238, baseEnd_752238] using wordTrace_append hprefix tailTrace_752238
  have hstable : (prefixWord ++ tailWord_752238).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752238).length < 2 ^ (prefixWord ++ tailWord_752238).sum := by decide
  have hdescent : baseEnd_752238 < baseStart_752238 := by decide
  rcases family_descends (prefixWord ++ tailWord_752238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752276 : List Nat := [2, 4, 2, 2, 1, 1, 1, 3, 4]
def baseStart_752276 : Nat := 118140960795 + 752276 * 2 ^ 59
def prefixEnd_752276 : Nat := 4983230072969 + 3 ^ 40 * 752276 * 2
def baseEnd_752276 : Nat := 343359264748270178124757

theorem tailTrace_752276 : CollatzResearch.WordTrace tailWord_752276 prefixEnd_752276 343359264748270178124757 := by
  unfold tailWord_752276
  simp only [CollatzResearch.WordTrace]
  refine ⟨13718879911320002678606341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18291839881760003571475121 13718879911320002678606341)
  ·
    refine ⟨2572289983372500502238689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13718879911320002678606341 2572289983372500502238689)
    ·
      refine ⟨1929217487529375376679017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2572289983372500502238689 1929217487529375376679017)
      ·
        refine ⟨1446913115647031532509263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1929217487529375376679017 1446913115647031532509263)
        ·
          refine ⟨2170369673470547298763895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1446913115647031532509263 2170369673470547298763895)
          ·
            refine ⟨3255554510205820948145843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2170369673470547298763895 3255554510205820948145843)
            ·
              refine ⟨4883331765308731422218765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3255554510205820948145843 4883331765308731422218765)
              ·
                refine ⟨1831249411990774283332037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4883331765308731422218765 1831249411990774283332037)
                ·
                  refine ⟨343359264748270178124757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1831249411990774283332037 343359264748270178124757)
                  ·
                    rfl

theorem cell20_752276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_752276 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_752276 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_752276 prefixEnd_752276 := by exact prefixLift 752276
  have htrace : WordTrace (prefixWord ++ tailWord_752276) baseStart_752276 baseEnd_752276 := by
    simpa [prefixWord, tailWord_752276, baseEnd_752276] using wordTrace_append hprefix tailTrace_752276
  have hstable : (prefixWord ++ tailWord_752276).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752276).length < 2 ^ (prefixWord ++ tailWord_752276).sum := by decide
  have hdescent : baseEnd_752276 < baseStart_752276 := by decide
  rcases family_descends (prefixWord ++ tailWord_752276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752286 : List Nat := [4, 3, 1, 1, 1, 1, 5, 1, 3]
def baseStart_752286 : Nat := 118140960795 + 752286 * 2 ^ 59
def prefixEnd_752286 : Nat := 4983230072969 + 3 ^ 40 * 752286 * 2
def baseEnd_752286 : Nat := 343363829020754587791383

theorem tailTrace_752286 : CollatzResearch.WordTrace tailWord_752286 prefixEnd_752286 343363829020754587791383 := by
  unfold tailWord_752286
  simp only [CollatzResearch.WordTrace]
  refine ⟨3429765569075472133134589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18292083035069184710051141 3429765569075472133134589)
  ·
    refine ⟨1286162088403302049925471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3429765569075472133134589 1286162088403302049925471)
    ·
      refine ⟨1929243132604953074888207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1286162088403302049925471 1929243132604953074888207)
      ·
        refine ⟨2893864698907429612332311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1929243132604953074888207 2893864698907429612332311)
        ·
          refine ⟨4340797048361144418498467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2893864698907429612332311 4340797048361144418498467)
          ·
            refine ⟨6511195572541716627747701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4340797048361144418498467 6511195572541716627747701)
            ·
              refine ⟨610424584925785933851347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6511195572541716627747701 610424584925785933851347)
              ·
                refine ⟨915636877388678900777021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 610424584925785933851347 915636877388678900777021)
                ·
                  refine ⟨343363829020754587791383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 915636877388678900777021 343363829020754587791383)
                  ·
                    rfl

theorem cell20_752286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_752286 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_752286 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_752286 prefixEnd_752286 := by exact prefixLift 752286
  have htrace : WordTrace (prefixWord ++ tailWord_752286) baseStart_752286 baseEnd_752286 := by
    simpa [prefixWord, tailWord_752286, baseEnd_752286] using wordTrace_append hprefix tailTrace_752286
  have hstable : (prefixWord ++ tailWord_752286).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752286).length < 2 ^ (prefixWord ++ tailWord_752286).sum := by decide
  have hdescent : baseEnd_752286 < baseStart_752286 := by decide
  rcases family_descends (prefixWord ++ tailWord_752286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752341 : List Nat := [1, 3, 2, 5, 1, 2, 2, 1, 3]
def baseStart_752341 : Nat := 118140960795 + 752341 * 2 ^ 59
def prefixEnd_752341 : Nat := 4983230072969 + 3 ^ 40 * 752341 * 2
def baseEnd_752341 : Nat := 343388932519418840957825

theorem tailTrace_752341 : CollatzResearch.WordTrace tailWord_752341 prefixEnd_752341 343388932519418840957825 := by
  unfold tailWord_752341
  simp only [CollatzResearch.WordTrace]
  refine ⟨27440130567404521458328877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18293420378269680972219251 27440130567404521458328877)
  ·
    refine ⟨10290048962776695546873329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27440130567404521458328877 10290048962776695546873329)
    ·
      refine ⟨7717536722082521660154997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10290048962776695546873329 7717536722082521660154997)
      ·
        refine ⟨723519067695236405639531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7717536722082521660154997 723519067695236405639531)
        ·
          refine ⟨1085278601542854608459297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 723519067695236405639531 1085278601542854608459297)
          ·
            refine ⟨813958951157140956344473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1085278601542854608459297 813958951157140956344473)
            ·
              refine ⟨610469213367855717258355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 813958951157140956344473 610469213367855717258355)
              ·
                refine ⟨915703820051783575887533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 610469213367855717258355 915703820051783575887533)
                ·
                  refine ⟨343388932519418840957825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 915703820051783575887533 343388932519418840957825)
                  ·
                    rfl

theorem cell20_752341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 2, 1, 3].length) (baseStart_752341 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_752341 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_752341 prefixEnd_752341 := by exact prefixLift 752341
  have htrace : WordTrace (prefixWord ++ tailWord_752341) baseStart_752341 baseEnd_752341 := by
    simpa [prefixWord, tailWord_752341, baseEnd_752341] using wordTrace_append hprefix tailTrace_752341
  have hstable : (prefixWord ++ tailWord_752341).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752341).length < 2 ^ (prefixWord ++ tailWord_752341).sum := by decide
  have hdescent : baseEnd_752341 < baseStart_752341 := by decide
  rcases family_descends (prefixWord ++ tailWord_752341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752386 : List Nat := [3, 4, 1, 1, 1, 2, 4, 2, 2]
def baseStart_752386 : Nat := 118140960795 + 752386 * 2 ^ 59
def prefixEnd_752386 : Nat := 4983230072969 + 3 ^ 40 * 752386 * 2
def baseEnd_752386 : Nat := 343409471745598684457641

theorem tailTrace_752386 : CollatzResearch.WordTrace tailWord_752386 prefixEnd_752386 343409471745598684457641 := by
  unfold tailWord_752386
  simp only [CollatzResearch.WordTrace]
  refine ⟨6860442963060373535929253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18294514568160996095811341 6860442963060373535929253)
  ·
    refine ⟨1286333055573820037986735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6860442963060373535929253 1286333055573820037986735)
    ·
      refine ⟨1929499583360730056980103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1286333055573820037986735 1929499583360730056980103)
      ·
        refine ⟨2894249375041095085470155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1929499583360730056980103 2894249375041095085470155)
        ·
          refine ⟨4341374062561642628205233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2894249375041095085470155 4341374062561642628205233)
          ·
            refine ⟨3256030546921231971153925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4341374062561642628205233 3256030546921231971153925)
            ·
              refine ⟨610505727547730994591361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3256030546921231971153925 610505727547730994591361)
              ·
                refine ⟨457879295660798245943521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 610505727547730994591361 457879295660798245943521)
                ·
                  refine ⟨343409471745598684457641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 457879295660798245943521 343409471745598684457641)
                  ·
                    rfl

theorem cell20_752386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 4, 2, 2].length) (baseStart_752386 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_752386 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_752386 prefixEnd_752386 := by exact prefixLift 752386
  have htrace : WordTrace (prefixWord ++ tailWord_752386) baseStart_752386 baseEnd_752386 := by
    simpa [prefixWord, tailWord_752386, baseEnd_752386] using wordTrace_append hprefix tailTrace_752386
  have hstable : (prefixWord ++ tailWord_752386).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752386).length < 2 ^ (prefixWord ++ tailWord_752386).sum := by decide
  have hdescent : baseEnd_752386 < baseStart_752386 := by decide
  rcases family_descends (prefixWord ++ tailWord_752386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752428 : List Nat := [2, 2, 1, 1, 1, 4, 4, 3, 2]
def baseStart_752428 : Nat := 118140960795 + 752428 * 2 ^ 59
def prefixEnd_752428 : Nat := 4983230072969 + 3 ^ 40 * 752428 * 2
def baseEnd_752428 : Nat := 343428641690033205057469

theorem tailTrace_752428 : CollatzResearch.WordTrace tailWord_752428 prefixEnd_752428 343428641690033205057469 := by
  unfold tailWord_752428
  simp only [CollatzResearch.WordTrace]
  refine ⟨13721651859044667658372969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18295535812059556877830625 13721651859044667658372969)
  ·
    refine ⟨10291238894283500743779727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13721651859044667658372969 10291238894283500743779727)
    ·
      refine ⟨15436858341425251115669591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10291238894283500743779727 15436858341425251115669591)
      ·
        refine ⟨23155287512137876673504387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15436858341425251115669591 23155287512137876673504387)
        ·
          refine ⟨34732931268206815010256581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23155287512137876673504387 34732931268206815010256581)
          ·
            refine ⟨6512424612788777814423109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34732931268206815010256581 6512424612788777814423109)
            ·
              refine ⟨1221079614897895840204333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6512424612788777814423109 1221079614897895840204333)
              ·
                refine ⟨457904855586710940076625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1221079614897895840204333 457904855586710940076625)
                ·
                  refine ⟨343428641690033205057469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 457904855586710940076625 343428641690033205057469)
                  ·
                    rfl

theorem cell20_752428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 4, 3, 2].length) (baseStart_752428 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_752428 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_752428 prefixEnd_752428 := by exact prefixLift 752428
  have htrace : WordTrace (prefixWord ++ tailWord_752428) baseStart_752428 baseEnd_752428 := by
    simpa [prefixWord, tailWord_752428, baseEnd_752428] using wordTrace_append hprefix tailTrace_752428
  have hstable : (prefixWord ++ tailWord_752428).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752428).length < 2 ^ (prefixWord ++ tailWord_752428).sum := by decide
  have hdescent : baseEnd_752428 < baseStart_752428 := by decide
  rcases family_descends (prefixWord ++ tailWord_752428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752439 : List Nat := [1, 1, 3, 1, 2, 1, 11]
def baseStart_752439 : Nat := 118140960795 + 752439 * 2 ^ 59
def prefixEnd_752439 : Nat := 4983230072969 + 3 ^ 40 * 752439 * 2
def baseEnd_752439 : Nat := 38159295821085117298973

theorem tailTrace_752439 : CollatzResearch.WordTrace tailWord_752439 prefixEnd_752439 38159295821085117298973 := by
  unfold tailWord_752439
  simp only [CollatzResearch.WordTrace]
  refine ⟨27443704921049484195396371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18295803280699656130264247 27443704921049484195396371)
  ·
    refine ⟨41165557381574226293094557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27443704921049484195396371 41165557381574226293094557)
    ·
      refine ⟨15437084018090334859910459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41165557381574226293094557 15437084018090334859910459)
      ·
        refine ⟨23155626027135502289865689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15437084018090334859910459 23155626027135502289865689)
        ·
          refine ⟨17366719520351626717399267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23155626027135502289865689 17366719520351626717399267)
          ·
            refine ⟨26050079280527440076098901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17366719520351626717399267 26050079280527440076098901)
            ·
              refine ⟨38159295821085117298973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 26050079280527440076098901 38159295821085117298973)
              ·
                rfl

theorem cell20_752439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 11].length) (baseStart_752439 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_752439 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_752439 prefixEnd_752439 := by exact prefixLift 752439
  have htrace : WordTrace (prefixWord ++ tailWord_752439) baseStart_752439 baseEnd_752439 := by
    simpa [prefixWord, tailWord_752439, baseEnd_752439] using wordTrace_append hprefix tailTrace_752439
  have hstable : (prefixWord ++ tailWord_752439).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752439).length < 2 ^ (prefixWord ++ tailWord_752439).sum := by decide
  have hdescent : baseEnd_752439 < baseStart_752439 := by decide
  rcases family_descends (prefixWord ++ tailWord_752439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752442 : List Nat := [3, 1, 1, 1, 6, 1, 1, 1, 5]
def baseStart_752442 : Nat := 118140960795 + 752442 * 2 ^ 59
def prefixEnd_752442 : Nat := 4983230072969 + 3 ^ 40 * 752442 * 2
def baseEnd_752442 : Nat := 343435031671511378590745

theorem tailTrace_752442 : CollatzResearch.WordTrace tailWord_752442 prefixEnd_752442 343435031671511378590745 := by
  unfold tailWord_752442
  simp only [CollatzResearch.WordTrace]
  refine ⟨6860953585009653926938895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18295876226692410471837053 6860953585009653926938895)
  ·
    refine ⟨10291430377514480890408343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6860953585009653926938895 10291430377514480890408343)
    ·
      refine ⟨15437145566271721335612515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10291430377514480890408343 15437145566271721335612515)
      ·
        refine ⟨23155718349407582003418773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15437145566271721335612515 23155718349407582003418773)
        ·
          refine ⟨1085424297628480406410255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 23155718349407582003418773 1085424297628480406410255)
          ·
            refine ⟨1628136446442720609615383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1085424297628480406410255 1628136446442720609615383)
            ·
              refine ⟨2442204669664080914423075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1628136446442720609615383 2442204669664080914423075)
              ·
                refine ⟨3663307004496121371634613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2442204669664080914423075 3663307004496121371634613)
                ·
                  refine ⟨343435031671511378590745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3663307004496121371634613 343435031671511378590745)
                  ·
                    rfl

theorem cell20_752442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 1, 5].length) (baseStart_752442 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_752442 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_752442 prefixEnd_752442 := by exact prefixLift 752442
  have htrace : WordTrace (prefixWord ++ tailWord_752442) baseStart_752442 baseEnd_752442 := by
    simpa [prefixWord, tailWord_752442, baseEnd_752442] using wordTrace_append hprefix tailTrace_752442
  have hstable : (prefixWord ++ tailWord_752442).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752442).length < 2 ^ (prefixWord ++ tailWord_752442).sum := by decide
  have hdescent : baseEnd_752442 < baseStart_752442 := by decide
  rcases family_descends (prefixWord ++ tailWord_752442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752473 : List Nat := [1, 2, 1, 2, 2, 6, 2, 4]
def baseStart_752473 : Nat := 118140960795 + 752473 * 2 ^ 59
def prefixEnd_752473 : Nat := 4983230072969 + 3 ^ 40 * 752473 * 2
def baseEnd_752473 : Nat := 114483060305404349519095

theorem tailTrace_752473 : CollatzResearch.WordTrace tailWord_752473 prefixEnd_752473 114483060305404349519095 := by
  unfold tailWord_752473
  simp only [CollatzResearch.WordTrace]
  refine ⟨27444945002926308002134073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18296630001950872001422715 27444945002926308002134073)
  ·
    refine ⟨20583708752194731001600555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27444945002926308002134073 20583708752194731001600555)
    ·
      refine ⟨30875563128292096502400833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20583708752194731001600555 30875563128292096502400833)
      ·
        refine ⟨23156672346219072376800625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30875563128292096502400833 23156672346219072376800625)
        ·
          refine ⟨17367504259664304282600469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23156672346219072376800625 17367504259664304282600469)
          ·
            refine ⟨814101762171764263246897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 17367504259664304282600469 814101762171764263246897)
            ·
              refine ⟨610576321628823197435173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 814101762171764263246897 610576321628823197435173)
              ·
                refine ⟨114483060305404349519095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 610576321628823197435173 114483060305404349519095)
                ·
                  rfl

theorem cell20_752473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 2, 4].length) (baseStart_752473 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_752473 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_752473 prefixEnd_752473 := by exact prefixLift 752473
  have htrace : WordTrace (prefixWord ++ tailWord_752473) baseStart_752473 baseEnd_752473 := by
    simpa [prefixWord, tailWord_752473, baseEnd_752473] using wordTrace_append hprefix tailTrace_752473
  have hstable : (prefixWord ++ tailWord_752473).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752473).length < 2 ^ (prefixWord ++ tailWord_752473).sum := by decide
  have hdescent : baseEnd_752473 < baseStart_752473 := by decide
  rcases family_descends (prefixWord ++ tailWord_752473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752483 : List Nat := [1, 1, 1, 5, 3, 3, 1, 3, 2]
def baseStart_752483 : Nat := 118140960795 + 752483 * 2 ^ 59
def prefixEnd_752483 : Nat := 4983230072969 + 3 ^ 40 * 752483 * 2
def baseEnd_752483 : Nat := 343453745188697458223911

theorem tailTrace_752483 : CollatzResearch.WordTrace tailWord_752483 prefixEnd_752483 343453745188697458223911 := by
  unfold tailWord_752483
  simp only [CollatzResearch.WordTrace]
  refine ⟨27445309732890079709998103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18296873155260053139998735 27445309732890079709998103)
  ·
    refine ⟨41167964599335119564997155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27445309732890079709998103 41167964599335119564997155)
    ·
      refine ⟨61751946899002679347495733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41167964599335119564997155 61751946899002679347495733)
      ·
        refine ⟨5789245021781501188827725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 61751946899002679347495733 5789245021781501188827725)
        ·
          refine ⟨2170966883168062945810397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5789245021781501188827725 2170966883168062945810397)
          ·
            refine ⟨814112581188023604678899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2170966883168062945810397 814112581188023604678899)
            ·
              refine ⟨1221168871782035407018349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 814112581188023604678899 1221168871782035407018349)
              ·
                refine ⟨457938326918263277631881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1221168871782035407018349 457938326918263277631881)
                ·
                  refine ⟨343453745188697458223911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 457938326918263277631881 343453745188697458223911)
                  ·
                    rfl

theorem cell20_752483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 1, 3, 2].length) (baseStart_752483 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_752483 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_752483 prefixEnd_752483 := by exact prefixLift 752483
  have htrace : WordTrace (prefixWord ++ tailWord_752483) baseStart_752483 baseEnd_752483 := by
    simpa [prefixWord, tailWord_752483, baseEnd_752483] using wordTrace_append hprefix tailTrace_752483
  have hstable : (prefixWord ++ tailWord_752483).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752483).length < 2 ^ (prefixWord ++ tailWord_752483).sum := by decide
  have hdescent : baseEnd_752483 < baseStart_752483 := by decide
  rcases family_descends (prefixWord ++ tailWord_752483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752510 : List Nat := [4, 2, 3, 1, 3, 1, 2, 1, 3]
def baseStart_752510 : Nat := 118140960795 + 752510 * 2 ^ 59
def prefixEnd_752510 : Nat := 4983230072969 + 3 ^ 40 * 752510 * 2
def baseEnd_752510 : Nat := 343466068724405364323801

theorem tailTrace_752510 : CollatzResearch.WordTrace tailWord_752510 prefixEnd_752510 343466068724405364323801 := by
  unfold tailWord_752510
  simp only [CollatzResearch.WordTrace]
  refine ⟨3430786812974032915153873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18297529669194842214153989 3430786812974032915153873)
  ·
    refine ⟨2573090109730524686365405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3430786812974032915153873 2573090109730524686365405)
    ·
      refine ⟨964908791148946757387027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2573090109730524686365405 964908791148946757387027)
      ·
        refine ⟨1447363186723420136080541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 964908791148946757387027 1447363186723420136080541)
        ·
          refine ⟨542761195021282551030203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1447363186723420136080541 542761195021282551030203)
          ·
            refine ⟨814141792531923826545305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 542761195021282551030203 814141792531923826545305)
            ·
              refine ⟨610606344398942869908979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 814141792531923826545305 610606344398942869908979)
              ·
                refine ⟨915909516598414304863469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 610606344398942869908979 915909516598414304863469)
                ·
                  refine ⟨343466068724405364323801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 915909516598414304863469 343466068724405364323801)
                  ·
                    rfl

theorem cell20_752510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 2, 1, 3].length) (baseStart_752510 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_752510 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_752510 prefixEnd_752510 := by exact prefixLift 752510
  have htrace : WordTrace (prefixWord ++ tailWord_752510) baseStart_752510 baseEnd_752510 := by
    simpa [prefixWord, tailWord_752510, baseEnd_752510] using wordTrace_append hprefix tailTrace_752510
  have hstable : (prefixWord ++ tailWord_752510).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752510).length < 2 ^ (prefixWord ++ tailWord_752510).sum := by decide
  have hdescent : baseEnd_752510 < baseStart_752510 := by decide
  rcases family_descends (prefixWord ++ tailWord_752510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752532 : List Nat := [2, 4, 2, 1, 1, 1, 1, 8]
def baseStart_752532 : Nat := 118140960795 + 752532 * 2 ^ 59
def prefixEnd_752532 : Nat := 4983230072969 + 3 ^ 40 * 752532 * 2
def baseEnd_752532 : Nat := 114492036707957021863459

theorem tailTrace_752532 : CollatzResearch.WordTrace tailWord_752532 prefixEnd_752532 114492036707957021863459 := by
  unfold tailWord_752532
  simp only [CollatzResearch.WordTrace]
  refine ⟨13723548454856280539265925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18298064606475040719021233 13723548454856280539265925)
  ·
    refine ⟨2573165335285552601112361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13723548454856280539265925 2573165335285552601112361)
    ·
      refine ⟨1929874001464164450834271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2573165335285552601112361 1929874001464164450834271)
      ·
        refine ⟨2894811002196246676251407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1929874001464164450834271 2894811002196246676251407)
        ·
          refine ⟨4342216503294370014377111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2894811002196246676251407 4342216503294370014377111)
          ·
            refine ⟨6513324754941555021565667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4342216503294370014377111 6513324754941555021565667)
            ·
              refine ⟨9769987132412332532348501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6513324754941555021565667 9769987132412332532348501)
              ·
                refine ⟨114492036707957021863459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9769987132412332532348501 114492036707957021863459)
                ·
                  rfl

theorem cell20_752532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 8].length) (baseStart_752532 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_752532 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_752532 prefixEnd_752532 := by exact prefixLift 752532
  have htrace : WordTrace (prefixWord ++ tailWord_752532) baseStart_752532 baseEnd_752532 := by
    simpa [prefixWord, tailWord_752532, baseEnd_752532] using wordTrace_append hprefix tailTrace_752532
  have hstable : (prefixWord ++ tailWord_752532).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752532).length < 2 ^ (prefixWord ++ tailWord_752532).sum := by decide
  have hdescent : baseEnd_752532 < baseStart_752532 := by decide
  rcases family_descends (prefixWord ++ tailWord_752532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752597 : List Nat := [1, 3, 2, 3, 3, 1, 2, 3, 2]
def baseStart_752597 : Nat := 118140960795 + 752597 * 2 ^ 59
def prefixEnd_752597 : Nat := 4983230072969 + 3 ^ 40 * 752597 * 2
def baseEnd_752597 : Nat := 343505777895019728423445

theorem tailTrace_752597 : CollatzResearch.WordTrace tailWord_752597 prefixEnd_752597 343505777895019728423445 := by
  unfold tailWord_752597
  simp only [CollatzResearch.WordTrace]
  refine ⟨27449467654477077179648045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18299645102984718119765363 27449467654477077179648045)
  ·
    refine ⟨10293550370428903942368017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27449467654477077179648045 10293550370428903942368017)
    ·
      refine ⟨7720162777821677956776013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10293550370428903942368017 7720162777821677956776013)
      ·
        refine ⟨2895061041683129233791005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7720162777821677956776013 2895061041683129233791005)
        ·
          refine ⟨1085647890631173462671627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2895061041683129233791005 1085647890631173462671627)
          ·
            refine ⟨1628471835946760194007441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1085647890631173462671627 1628471835946760194007441)
            ·
              refine ⟨1221353876960070145505581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1628471835946760194007441 1221353876960070145505581)
              ·
                refine ⟨458007703860026304564593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1221353876960070145505581 458007703860026304564593)
                ·
                  refine ⟨343505777895019728423445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 458007703860026304564593 343505777895019728423445)
                  ·
                    rfl

theorem cell20_752597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 2, 3, 2].length) (baseStart_752597 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_752597 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_752597 prefixEnd_752597 := by exact prefixLift 752597
  have htrace : WordTrace (prefixWord ++ tailWord_752597) baseStart_752597 baseEnd_752597 := by
    simpa [prefixWord, tailWord_752597, baseEnd_752597] using wordTrace_append hprefix tailTrace_752597
  have hstable : (prefixWord ++ tailWord_752597).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752597).length < 2 ^ (prefixWord ++ tailWord_752597).sum := by decide
  have hdescent : baseEnd_752597 < baseStart_752597 := by decide
  rcases family_descends (prefixWord ++ tailWord_752597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752618 : List Nat := [3, 1, 3, 1, 2, 2, 2, 4, 2]
def baseStart_752618 : Nat := 118140960795 + 752618 * 2 ^ 59
def prefixEnd_752618 : Nat := 4983230072969 + 3 ^ 40 * 752618 * 2
def baseEnd_752618 : Nat := 343515362867236988723359

theorem tailTrace_752618 : CollatzResearch.WordTrace tailWord_752618 prefixEnd_752618 343515362867236988723359 := by
  unfold tailWord_752618
  simp only [CollatzResearch.WordTrace]
  refine ⟨6862558396850249441540627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18300155724933998510775005 6862558396850249441540627)
  ·
    refine ⟨10293837595275374162310941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6862558396850249441540627 10293837595275374162310941)
    ·
      refine ⟨3860189098228265310866603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10293837595275374162310941 3860189098228265310866603)
      ·
        refine ⟨5790283647342397966299905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3860189098228265310866603 5790283647342397966299905)
        ·
          refine ⟨4342712735506798474724929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5790283647342397966299905 4342712735506798474724929)
          ·
            refine ⟨3257034551630098856043697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4342712735506798474724929 3257034551630098856043697)
            ·
              refine ⟨2442775913722574142032773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3257034551630098856043697 2442775913722574142032773)
              ·
                refine ⟨458020483822982651631145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2442775913722574142032773 458020483822982651631145)
                ·
                  refine ⟨343515362867236988723359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 458020483822982651631145 343515362867236988723359)
                  ·
                    rfl

theorem cell20_752618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 4, 2].length) (baseStart_752618 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_752618 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_752618 prefixEnd_752618 := by exact prefixLift 752618
  have htrace : WordTrace (prefixWord ++ tailWord_752618) baseStart_752618 baseEnd_752618 := by
    simpa [prefixWord, tailWord_752618, baseEnd_752618] using wordTrace_append hprefix tailTrace_752618
  have hstable : (prefixWord ++ tailWord_752618).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752618).length < 2 ^ (prefixWord ++ tailWord_752618).sum := by decide
  have hdescent : baseEnd_752618 < baseStart_752618 := by decide
  rcases family_descends (prefixWord ++ tailWord_752618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752642 : List Nat := [3, 4, 1, 3, 1, 1, 1, 6]
def baseStart_752642 : Nat := 118140960795 + 752642 * 2 ^ 59
def prefixEnd_752642 : Nat := 4983230072969 + 3 ^ 40 * 752642 * 2
def baseEnd_752642 : Nat := 114508772373733190641087

theorem tailTrace_752642 : CollatzResearch.WordTrace tailWord_752642 prefixEnd_752642 114508772373733190641087 := by
  unfold tailWord_752642
  simp only [CollatzResearch.WordTrace]
  refine ⟨6862777234828512466259045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18300739292876033243357453 6862777234828512466259045)
  ·
    refine ⟨1286770731530346087423571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6862777234828512466259045 1286770731530346087423571)
    ·
      refine ⟨1930156097295519131135357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1286770731530346087423571 1930156097295519131135357)
      ·
        refine ⟨723808536485819674175759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1930156097295519131135357 723808536485819674175759)
        ·
          refine ⟨1085712804728729511263639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 723808536485819674175759 1085712804728729511263639)
          ·
            refine ⟨1628569207093094266895459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1085712804728729511263639 1628569207093094266895459)
            ·
              refine ⟨2442853810639641400343189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1628569207093094266895459 2442853810639641400343189)
              ·
                refine ⟨114508772373733190641087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2442853810639641400343189 114508772373733190641087)
                ·
                  rfl

theorem cell20_752642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 6].length) (baseStart_752642 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_752642 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_752642 prefixEnd_752642 := by exact prefixLift 752642
  have htrace : WordTrace (prefixWord ++ tailWord_752642) baseStart_752642 baseEnd_752642 := by
    simpa [prefixWord, tailWord_752642, baseEnd_752642] using wordTrace_append hprefix tailTrace_752642
  have hstable : (prefixWord ++ tailWord_752642).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752642).length < 2 ^ (prefixWord ++ tailWord_752642).sum := by decide
  have hdescent : baseEnd_752642 < baseStart_752642 := by decide
  rcases family_descends (prefixWord ++ tailWord_752642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752673 : List Nat := [1, 2, 3, 2, 3, 2, 3, 2, 2]
def baseStart_752673 : Nat := 118140960795 + 752673 * 2 ^ 59
def prefixEnd_752673 : Nat := 4983230072969 + 3 ^ 40 * 752673 * 2
def baseEnd_752673 : Nat := 343540466365901241889801

theorem tailTrace_752673 : CollatzResearch.WordTrace tailWord_752673 prefixEnd_752673 343540466365901241889801 := by
  unfold tailWord_752673
  simp only [CollatzResearch.WordTrace]
  refine ⟨27452239602201742159414673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18301493068134494772943115 27452239602201742159414673)
  ·
    refine ⟨20589179701651306619561005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27452239602201742159414673 20589179701651306619561005)
    ·
      refine ⟨7720942388119239982335377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20589179701651306619561005 7720942388119239982335377)
      ·
        refine ⟨5790706791089429986751533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7720942388119239982335377 5790706791089429986751533)
        ·
          refine ⟨2171515046658536245031825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5790706791089429986751533 2171515046658536245031825)
          ·
            refine ⟨1628636284993902183773869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2171515046658536245031825 1628636284993902183773869)
            ·
              refine ⟨610738606872713318915201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1628636284993902183773869 610738606872713318915201)
              ·
                refine ⟨458053955154534989186401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 610738606872713318915201 458053955154534989186401)
                ·
                  refine ⟨343540466365901241889801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 458053955154534989186401 343540466365901241889801)
                  ·
                    rfl

theorem cell20_752673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 3, 2, 2].length) (baseStart_752673 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_752673 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_752673 prefixEnd_752673 := by exact prefixLift 752673
  have htrace : WordTrace (prefixWord ++ tailWord_752673) baseStart_752673 baseEnd_752673 := by
    simpa [prefixWord, tailWord_752673, baseEnd_752673] using wordTrace_append hprefix tailTrace_752673
  have hstable : (prefixWord ++ tailWord_752673).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752673).length < 2 ^ (prefixWord ++ tailWord_752673).sum := by decide
  have hdescent : baseEnd_752673 < baseStart_752673 := by decide
  rcases family_descends (prefixWord ++ tailWord_752673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752698 : List Nat := [3, 1, 1, 1, 3, 1, 2, 4, 4]
def baseStart_752698 : Nat := 118140960795 + 752698 * 2 ^ 59
def prefixEnd_752698 : Nat := 4983230072969 + 3 ^ 40 * 752698 * 2
def baseEnd_752698 : Nat := 343551877047112266056365

theorem tailTrace_752698 : CollatzResearch.WordTrace tailWord_752698 prefixEnd_752698 343551877047112266056365 := by
  unfold tailWord_752698
  simp only [CollatzResearch.WordTrace]
  refine ⟨6863287856777792857268687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18302100951407447619383165 6863287856777792857268687)
  ·
    refine ⟨10294931785166689285903031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6863287856777792857268687 10294931785166689285903031)
    ·
      refine ⟨15442397677750033928854547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10294931785166689285903031 15442397677750033928854547)
      ·
        refine ⟨23163596516625050893281821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15442397677750033928854547 23163596516625050893281821)
        ·
          refine ⟨8686348693734394084980683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23163596516625050893281821 8686348693734394084980683)
          ·
            refine ⟨13029523040601591127471025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8686348693734394084980683 13029523040601591127471025)
            ·
              refine ⟨9772142280451193345603269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13029523040601591127471025 9772142280451193345603269)
              ·
                refine ⟨1832276677584598752300613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9772142280451193345603269 1832276677584598752300613)
                ·
                  refine ⟨343551877047112266056365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1832276677584598752300613 343551877047112266056365)
                  ·
                    rfl

theorem cell20_752698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 4, 4].length) (baseStart_752698 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_752698 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_752698 prefixEnd_752698 := by exact prefixLift 752698
  have htrace : WordTrace (prefixWord ++ tailWord_752698) baseStart_752698 baseEnd_752698 := by
    simpa [prefixWord, tailWord_752698, baseEnd_752698] using wordTrace_append hprefix tailTrace_752698
  have hstable : (prefixWord ++ tailWord_752698).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752698).length < 2 ^ (prefixWord ++ tailWord_752698).sum := by decide
  have hdescent : baseEnd_752698 < baseStart_752698 := by decide
  rcases family_descends (prefixWord ++ tailWord_752698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752732 : List Nat := [2, 2, 4, 1, 1, 1, 3, 4, 2]
def baseStart_752732 : Nat := 118140960795 + 752732 * 2 ^ 59
def prefixEnd_752732 : Nat := 4983230072969 + 3 ^ 40 * 752732 * 2
def baseEnd_752732 : Nat := 343567395573559258922893

theorem tailTrace_752732 : CollatzResearch.WordTrace tailWord_752732 prefixEnd_752732 343567395573559258922893 := by
  unfold tailWord_752732
  simp only [CollatzResearch.WordTrace]
  refine ⟨13727195754493997617906225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18302927672658663490541633 13727195754493997617906225)
  ·
    refine ⟨10295396815870498213429669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13727195754493997617906225 10295396815870498213429669)
    ·
      refine ⟨1930386902975718415018063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10295396815870498213429669 1930386902975718415018063)
      ·
        refine ⟨2895580354463577622527095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1930386902975718415018063 2895580354463577622527095)
        ·
          refine ⟨4343370531695366433790643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2895580354463577622527095 4343370531695366433790643)
          ·
            refine ⟨6515055797543049650685965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4343370531695366433790643 6515055797543049650685965)
            ·
              refine ⟨2443145924078643619007237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6515055797543049650685965 2443145924078643619007237)
              ·
                refine ⟨458089860764745678563857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2443145924078643619007237 458089860764745678563857)
                ·
                  refine ⟨343567395573559258922893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 458089860764745678563857 343567395573559258922893)
                  ·
                    rfl

theorem cell20_752732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 4, 2].length) (baseStart_752732 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_752732 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_752732 prefixEnd_752732 := by exact prefixLift 752732
  have htrace : WordTrace (prefixWord ++ tailWord_752732) baseStart_752732 baseEnd_752732 := by
    simpa [prefixWord, tailWord_752732, baseEnd_752732] using wordTrace_append hprefix tailTrace_752732
  have hstable : (prefixWord ++ tailWord_752732).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752732).length < 2 ^ (prefixWord ++ tailWord_752732).sum := by decide
  have hdescent : baseEnd_752732 < baseStart_752732 := by decide
  rcases family_descends (prefixWord ++ tailWord_752732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752736 : List Nat := [2, 1, 1, 3, 2, 2, 2, 3, 4]
def baseStart_752736 : Nat := 118140960795 + 752736 * 2 ^ 59
def prefixEnd_752736 : Nat := 4983230072969 + 3 ^ 40 * 752736 * 2
def baseEnd_752736 : Nat := 343569221282553022789543

theorem tailTrace_752736 : CollatzResearch.WordTrace tailWord_752736 prefixEnd_752736 343569221282553022789543 := by
  unfold tailWord_752736
  simp only [CollatzResearch.WordTrace]
  refine ⟨13727268700486751959479031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18303024933982335945972041 13727268700486751959479031)
  ·
    refine ⟨20590903050730127939218547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13727268700486751959479031 20590903050730127939218547)
    ·
      refine ⟨30886354576095191908827821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20590903050730127939218547 30886354576095191908827821)
      ·
        refine ⟨11582382966035696965810433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30886354576095191908827821 11582382966035696965810433)
        ·
          refine ⟨8686787224526772724357825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11582382966035696965810433 8686787224526772724357825)
          ·
            refine ⟨6515090418395079543268369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8686787224526772724357825 6515090418395079543268369)
            ·
              refine ⟨4886317813796309657451277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6515090418395079543268369 4886317813796309657451277)
              ·
                refine ⟨1832369180173616121544229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4886317813796309657451277 1832369180173616121544229)
                ·
                  refine ⟨343569221282553022789543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1832369180173616121544229 343569221282553022789543)
                  ·
                    rfl

theorem cell20_752736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 3, 4].length) (baseStart_752736 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_752736 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_752736 prefixEnd_752736 := by exact prefixLift 752736
  have htrace : WordTrace (prefixWord ++ tailWord_752736) baseStart_752736 baseEnd_752736 := by
    simpa [prefixWord, tailWord_752736, baseEnd_752736] using wordTrace_append hprefix tailTrace_752736
  have hstable : (prefixWord ++ tailWord_752736).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752736).length < 2 ^ (prefixWord ++ tailWord_752736).sum := by decide
  have hdescent : baseEnd_752736 < baseStart_752736 := by decide
  rcases family_descends (prefixWord ++ tailWord_752736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752746 : List Nat := [3, 1, 3, 2, 2, 1, 2, 3, 3]
def baseStart_752746 : Nat := 118140960795 + 752746 * 2 ^ 59
def prefixEnd_752746 : Nat := 4983230072969 + 3 ^ 40 * 752746 * 2
def baseEnd_752746 : Nat := 343573785555037432456169

theorem tailTrace_752746 : CollatzResearch.WordTrace tailWord_752746 prefixEnd_752746 343573785555037432456169 := by
  unfold tailWord_752746
  simp only [CollatzResearch.WordTrace]
  refine ⟨6863725532734318906705523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18303268087291517084548061 6863725532734318906705523)
  ·
    refine ⟨10295588299101478360058285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6863725532734318906705523 10295588299101478360058285)
    ·
      refine ⟨3860845612163054385021857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10295588299101478360058285 3860845612163054385021857)
      ·
        refine ⟨2895634209122290788766393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3860845612163054385021857 2895634209122290788766393)
        ·
          refine ⟨2171725656841718091574795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2895634209122290788766393 2171725656841718091574795)
          ·
            refine ⟨3257588485262577137362193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2171725656841718091574795 3257588485262577137362193)
            ·
              refine ⟨2443191363946932853021645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3257588485262577137362193 2443191363946932853021645)
              ·
                refine ⟨916196761480099819883117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2443191363946932853021645 916196761480099819883117)
                ·
                  refine ⟨343573785555037432456169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 916196761480099819883117 343573785555037432456169)
                  ·
                    rfl

theorem cell20_752746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 3, 3].length) (baseStart_752746 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_752746 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_752746 prefixEnd_752746 := by exact prefixLift 752746
  have htrace : WordTrace (prefixWord ++ tailWord_752746) baseStart_752746 baseEnd_752746 := by
    simpa [prefixWord, tailWord_752746, baseEnd_752746] using wordTrace_append hprefix tailTrace_752746
  have hstable : (prefixWord ++ tailWord_752746).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752746).length < 2 ^ (prefixWord ++ tailWord_752746).sum := by decide
  have hdescent : baseEnd_752746 < baseStart_752746 := by decide
  rcases family_descends (prefixWord ++ tailWord_752746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752791 : List Nat := [1, 1, 3, 3, 3, 2, 2, 1, 4]
def baseStart_752791 : Nat := 118140960795 + 752791 * 2 ^ 59
def prefixEnd_752791 : Nat := 4983230072969 + 3 ^ 40 * 752791 * 2
def baseEnd_752791 : Nat := 343594324781217275955985

theorem tailTrace_752791 : CollatzResearch.WordTrace tailWord_752791 prefixEnd_752791 343594324781217275955985 := by
  unfold tailWord_752791
  simp only [CollatzResearch.WordTrace]
  refine ⟨27456543415774248312210227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18304362277182832208140151 27456543415774248312210227)
  ·
    refine ⟨41184815123661372468315341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27456543415774248312210227 41184815123661372468315341)
    ·
      refine ⟨15444305671373014675618253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41184815123661372468315341 15444305671373014675618253)
      ·
        refine ⟨5791614626764880503356845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15444305671373014675618253 5791614626764880503356845)
        ·
          refine ⟨2171855485036830188758817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5791614626764880503356845 2171855485036830188758817)
          ·
            refine ⟨1628891613777622641569113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2171855485036830188758817 1628891613777622641569113)
            ·
              refine ⟨1221668710333216981176835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1628891613777622641569113 1221668710333216981176835)
              ·
                refine ⟨1832503065499825471765253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1221668710333216981176835 1832503065499825471765253)
                ·
                  refine ⟨343594324781217275955985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1832503065499825471765253 343594324781217275955985)
                  ·
                    rfl

theorem cell20_752791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 2, 1, 4].length) (baseStart_752791 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_752791 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_752791 prefixEnd_752791 := by exact prefixLift 752791
  have htrace : WordTrace (prefixWord ++ tailWord_752791) baseStart_752791 baseEnd_752791 := by
    simpa [prefixWord, tailWord_752791, baseEnd_752791] using wordTrace_append hprefix tailTrace_752791
  have hstable : (prefixWord ++ tailWord_752791).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752791).length < 2 ^ (prefixWord ++ tailWord_752791).sum := by decide
  have hdescent : baseEnd_752791 < baseStart_752791 := by decide
  rcases family_descends (prefixWord ++ tailWord_752791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752838 : List Nat := [6, 1, 2, 2, 1, 1, 3, 2, 2]
def baseStart_752838 : Nat := 118140960795 + 752838 * 2 ^ 59
def prefixEnd_752838 : Nat := 4983230072969 + 3 ^ 40 * 752838 * 2
def baseEnd_752838 : Nat := 343615776861894001389127

theorem tailTrace_752838 : CollatzResearch.WordTrace tailWord_752838 prefixEnd_752838 343615776861894001389127 := by
  unfold tailWord_752838
  simp only [CollatzResearch.WordTrace]
  refine ⟨858070551456374229349099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 18305505097735983559447445 858070551456374229349099)
  ·
    refine ⟨1287105827184561344023649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 858070551456374229349099 1287105827184561344023649)
    ·
      refine ⟨965329370388421008017737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1287105827184561344023649 965329370388421008017737)
      ·
        refine ⟨723997027791315756013303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 965329370388421008017737 723997027791315756013303)
        ·
          refine ⟨1085995541686973634019955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 723997027791315756013303 1085995541686973634019955)
          ·
            refine ⟨1628993312530460451029933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1085995541686973634019955 1628993312530460451029933)
            ·
              refine ⟨610872492198922669136225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1628993312530460451029933 610872492198922669136225)
              ·
                refine ⟨458154369149192001852169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 610872492198922669136225 458154369149192001852169)
                ·
                  refine ⟨343615776861894001389127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 458154369149192001852169 343615776861894001389127)
                  ·
                    rfl

theorem cell20_752838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 3, 2, 2].length) (baseStart_752838 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_752838 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_752838 prefixEnd_752838 := by exact prefixLift 752838
  have htrace : WordTrace (prefixWord ++ tailWord_752838) baseStart_752838 baseEnd_752838 := by
    simpa [prefixWord, tailWord_752838, baseEnd_752838] using wordTrace_append hprefix tailTrace_752838
  have hstable : (prefixWord ++ tailWord_752838).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752838).length < 2 ^ (prefixWord ++ tailWord_752838).sum := by decide
  have hdescent : baseEnd_752838 < baseStart_752838 := by decide
  rcases family_descends (prefixWord ++ tailWord_752838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752846 : List Nat := [4, 1, 1, 1, 5, 2, 1, 1, 4]
def baseStart_752846 : Nat := 118140960795 + 752846 * 2 ^ 59
def prefixEnd_752846 : Nat := 4983230072969 + 3 ^ 40 * 752846 * 2
def baseEnd_752846 : Nat := 343619428279881529122427

theorem tailTrace_752846 : CollatzResearch.WordTrace tailWord_752846 prefixEnd_752846 343619428279881529122427 := by
  unfold tailWord_752846
  simp only [CollatzResearch.WordTrace]
  refine ⟨3432318678821874088182799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18305699620383328470308261 3432318678821874088182799)
  ·
    refine ⟨5148478018232811132274199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3432318678821874088182799 5148478018232811132274199)
    ·
      refine ⟨7722717027349216698411299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5148478018232811132274199 7722717027349216698411299)
      ·
        refine ⟨11584075541023825047616949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7722717027349216698411299 11584075541023825047616949)
        ·
          refine ⟨1086007081970983598214089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11584075541023825047616949 1086007081970983598214089)
          ·
            refine ⟨814505311478237698660567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1086007081970983598214089 814505311478237698660567)
            ·
              refine ⟨1221757967217356547990851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 814505311478237698660567 1221757967217356547990851)
              ·
                refine ⟨1832636950826034821986277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1221757967217356547990851 1832636950826034821986277)
                ·
                  refine ⟨343619428279881529122427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1832636950826034821986277 343619428279881529122427)
                  ·
                    rfl

theorem cell20_752846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 1, 1, 4].length) (baseStart_752846 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_752846 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_752846 prefixEnd_752846 := by exact prefixLift 752846
  have htrace : WordTrace (prefixWord ++ tailWord_752846) baseStart_752846 baseEnd_752846 := by
    simpa [prefixWord, tailWord_752846, baseEnd_752846] using wordTrace_append hprefix tailTrace_752846
  have hstable : (prefixWord ++ tailWord_752846).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752846).length < 2 ^ (prefixWord ++ tailWord_752846).sum := by decide
  have hdescent : baseEnd_752846 < baseStart_752846 := by decide
  rcases family_descends (prefixWord ++ tailWord_752846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752856 : List Nat := [2, 1, 2, 2, 6, 1, 2, 1, 3]
def baseStart_752856 : Nat := 118140960795 + 752856 * 2 ^ 59
def prefixEnd_752856 : Nat := 4983230072969 + 3 ^ 40 * 752856 * 2
def baseEnd_752856 : Nat := 343623992552365938789053

theorem tailTrace_752856 : CollatzResearch.WordTrace tailWord_752856 prefixEnd_752856 343623992552365938789053 := by
  unfold tailWord_752856
  simp only [CollatzResearch.WordTrace]
  refine ⟨13729457080269382206663211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18305942773692509608884281 13729457080269382206663211)
  ·
    refine ⟨20594185620404073309994817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13729457080269382206663211 20594185620404073309994817)
    ·
      refine ⟨15445639215303054982496113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20594185620404073309994817 15445639215303054982496113)
      ·
        refine ⟨11584229411477291236872085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15445639215303054982496113 11584229411477291236872085)
        ·
          refine ⟨543010753662998026728379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 11584229411477291236872085 543010753662998026728379)
          ·
            refine ⟨814516130494497040092569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 543010753662998026728379 814516130494497040092569)
            ·
              refine ⟨610887097870872780069427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 814516130494497040092569 610887097870872780069427)
              ·
                refine ⟨916330646806309170104141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 610887097870872780069427 916330646806309170104141)
                ·
                  refine ⟨343623992552365938789053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 916330646806309170104141 343623992552365938789053)
                  ·
                    rfl

theorem cell20_752856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 2, 1, 3].length) (baseStart_752856 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_752856 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_752856 prefixEnd_752856 := by exact prefixLift 752856
  have htrace : WordTrace (prefixWord ++ tailWord_752856) baseStart_752856 baseEnd_752856 := by
    simpa [prefixWord, tailWord_752856, baseEnd_752856] using wordTrace_append hprefix tailTrace_752856
  have hstable : (prefixWord ++ tailWord_752856).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752856).length < 2 ^ (prefixWord ++ tailWord_752856).sum := by decide
  have hdescent : baseEnd_752856 < baseStart_752856 := by decide
  rcases family_descends (prefixWord ++ tailWord_752856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752905 : List Nat := [1, 2, 1, 1, 3, 3, 3, 4, 2]
def baseStart_752905 : Nat := 118140960795 + 752905 * 2 ^ 59
def prefixEnd_752905 : Nat := 4983230072969 + 3 ^ 40 * 752905 * 2
def baseEnd_752905 : Nat := 343646357487539546155519

theorem tailTrace_752905 : CollatzResearch.WordTrace tailWord_752905 prefixEnd_752905 343646357487539546155519 := by
  unfold tailWord_752905
  simp only [CollatzResearch.WordTrace]
  refine ⟨27460701337361245781860169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18307134224907497187906779 27460701337361245781860169)
  ·
    refine ⟨20595526003020934336395127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27460701337361245781860169 20595526003020934336395127)
    ·
      refine ⟨30893289004531401504592691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20595526003020934336395127 30893289004531401504592691)
      ·
        refine ⟨46339933506797102256889037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30893289004531401504592691 46339933506797102256889037)
        ·
          refine ⟨17377475065048913346333389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46339933506797102256889037 17377475065048913346333389)
          ·
            refine ⟨6516553149393342504875021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17377475065048913346333389 6516553149393342504875021)
            ·
              refine ⟨2443707431022503439328133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6516553149393342504875021 2443707431022503439328133)
              ·
                refine ⟨458195143316719394874025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2443707431022503439328133 458195143316719394874025)
                ·
                  refine ⟨343646357487539546155519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 458195143316719394874025 343646357487539546155519)
                  ·
                    rfl

theorem cell20_752905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 4, 2].length) (baseStart_752905 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_752905 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_752905 prefixEnd_752905 := by exact prefixLift 752905
  have htrace : WordTrace (prefixWord ++ tailWord_752905) baseStart_752905 baseEnd_752905 := by
    simpa [prefixWord, tailWord_752905, baseEnd_752905] using wordTrace_append hprefix tailTrace_752905
  have hstable : (prefixWord ++ tailWord_752905).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752905).length < 2 ^ (prefixWord ++ tailWord_752905).sum := by decide
  have hdescent : baseEnd_752905 < baseStart_752905 := by decide
  rcases family_descends (prefixWord ++ tailWord_752905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752919 : List Nat := [1, 1, 3, 4, 1, 1, 1, 5, 3]
def baseStart_752919 : Nat := 118140960795 + 752919 * 2 ^ 59
def prefixEnd_752919 : Nat := 4983230072969 + 3 ^ 40 * 752919 * 2
def baseEnd_752919 : Nat := 343652747469017719688795

theorem tailTrace_752919 : CollatzResearch.WordTrace tailWord_752919 prefixEnd_752919 343652747469017719688795 := by
  unfold tailWord_752919
  simp only [CollatzResearch.WordTrace]
  refine ⟨27461211959310526172869811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18307474639540350781913207 27461211959310526172869811)
  ·
    refine ⟨41191817938965789259304717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27461211959310526172869811 41191817938965789259304717)
    ·
      refine ⟨15446931727112170972239269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41191817938965789259304717 15446931727112170972239269)
      ·
        refine ⟨2896299698833532057294863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15446931727112170972239269 2896299698833532057294863)
        ·
          refine ⟨4344449548250298085942295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2896299698833532057294863 4344449548250298085942295)
          ·
            refine ⟨6516674322375447128913443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4344449548250298085942295 6516674322375447128913443)
            ·
              refine ⟨9775011483563170693370165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6516674322375447128913443 9775011483563170693370165)
              ·
                refine ⟨916407326584047252503453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9775011483563170693370165 916407326584047252503453)
                ·
                  refine ⟨343652747469017719688795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 916407326584047252503453 343652747469017719688795)
                  ·
                    rfl

theorem cell20_752919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 5, 3].length) (baseStart_752919 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_752919 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_752919 prefixEnd_752919 := by exact prefixLift 752919
  have htrace : WordTrace (prefixWord ++ tailWord_752919) baseStart_752919 baseEnd_752919 := by
    simpa [prefixWord, tailWord_752919, baseEnd_752919] using wordTrace_append hprefix tailTrace_752919
  have hstable : (prefixWord ++ tailWord_752919).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752919).length < 2 ^ (prefixWord ++ tailWord_752919).sum := by decide
  have hdescent : baseEnd_752919 < baseStart_752919 := by decide
  rcases family_descends (prefixWord ++ tailWord_752919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752940 : List Nat := [2, 2, 1, 1, 1, 3, 1, 4, 5]
def baseStart_752940 : Nat := 118140960795 + 752940 * 2 ^ 59
def prefixEnd_752940 : Nat := 4983230072969 + 3 ^ 40 * 752940 * 2
def baseEnd_752940 : Nat := 343662332441234979988709

theorem tailTrace_752940 : CollatzResearch.WordTrace tailWord_752940 prefixEnd_752940 343662332441234979988709 := by
  unfold tailWord_752940
  simp only [CollatzResearch.WordTrace]
  refine ⟨13730988946117223379692137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18307985261489631172922849 13730988946117223379692137)
  ·
    refine ⟨10298241709587917534769103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13730988946117223379692137 10298241709587917534769103)
    ·
      refine ⟨15447362564381876302153655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10298241709587917534769103 15447362564381876302153655)
      ·
        refine ⟨23171043846572814453230483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15447362564381876302153655 23171043846572814453230483)
        ·
          refine ⟨34756565769859221679845725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23171043846572814453230483 34756565769859221679845725)
          ·
            refine ⟨13033712163697208129942147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34756565769859221679845725 13033712163697208129942147)
            ·
              refine ⟨19550568245545812194913221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13033712163697208129942147 19550568245545812194913221)
              ·
                refine ⟨3665731546039839786546229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19550568245545812194913221 3665731546039839786546229)
                ·
                  refine ⟨343662332441234979988709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3665731546039839786546229 343662332441234979988709)
                  ·
                    rfl

theorem cell20_752940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 5].length) (baseStart_752940 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_752940 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_752940 prefixEnd_752940 := by exact prefixLift 752940
  have htrace : WordTrace (prefixWord ++ tailWord_752940) baseStart_752940 baseEnd_752940 := by
    simpa [prefixWord, tailWord_752940, baseEnd_752940] using wordTrace_append hprefix tailTrace_752940
  have hstable : (prefixWord ++ tailWord_752940).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752940).length < 2 ^ (prefixWord ++ tailWord_752940).sum := by decide
  have hdescent : baseEnd_752940 < baseStart_752940 := by decide
  rcases family_descends (prefixWord ++ tailWord_752940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752953 : List Nat := [1, 2, 1, 6, 2, 2, 1, 2, 3]
def baseStart_752953 : Nat := 118140960795 + 752953 * 2 ^ 59
def prefixEnd_752953 : Nat := 4983230072969 + 3 ^ 40 * 752953 * 2
def baseEnd_752953 : Nat := 343668265995464712555323

theorem tailTrace_752953 : CollatzResearch.WordTrace tailWord_752953 prefixEnd_752953 343668265995464712555323 := by
  unfold tailWord_752953
  simp only [CollatzResearch.WordTrace]
  refine ⟨27462452041187349979607513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18308301360791566653071675 27462452041187349979607513)
  ·
    refine ⟨20596839030890512484705635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27462452041187349979607513 20596839030890512484705635)
    ·
      refine ⟨30895258546335768727058453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20596839030890512484705635 30895258546335768727058453)
      ·
        refine ⟨1448215244359489159080865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 30895258546335768727058453 1448215244359489159080865)
        ·
          refine ⟨1086161433269616869310649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1448215244359489159080865 1086161433269616869310649)
          ·
            refine ⟨814621074952212651982987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1086161433269616869310649 814621074952212651982987)
            ·
              refine ⟨1221931612428318977974481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 814621074952212651982987 1221931612428318977974481)
              ·
                refine ⟨916448709321239233480861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1221931612428318977974481 916448709321239233480861)
                ·
                  refine ⟨343668265995464712555323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 916448709321239233480861 343668265995464712555323)
                  ·
                    rfl

theorem cell20_752953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 1, 2, 3].length) (baseStart_752953 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_752953 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_752953 prefixEnd_752953 := by exact prefixLift 752953
  have htrace : WordTrace (prefixWord ++ tailWord_752953) baseStart_752953 baseEnd_752953 := by
    simpa [prefixWord, tailWord_752953, baseEnd_752953] using wordTrace_append hprefix tailTrace_752953
  have hstable : (prefixWord ++ tailWord_752953).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752953).length < 2 ^ (prefixWord ++ tailWord_752953).sum := by decide
  have hdescent : baseEnd_752953 < baseStart_752953 := by decide
  rcases family_descends (prefixWord ++ tailWord_752953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752974 : List Nat := [4, 1, 1, 1, 1, 1, 7, 1, 3]
def baseStart_752974 : Nat := 118140960795 + 752974 * 2 ^ 59
def prefixEnd_752974 : Nat := 4983230072969 + 3 ^ 40 * 752974 * 2
def baseEnd_752974 : Nat := 343677850967681972855237

theorem tailTrace_752974 : CollatzResearch.WordTrace tailWord_752974 prefixEnd_752974 343677850967681972855237 := by
  unfold tailWord_752974
  simp only [CollatzResearch.WordTrace]
  refine ⟨3432902246763908820765247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18308811982740847044081317 3432902246763908820765247)
  ·
    refine ⟨5149353370145863231147871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3432902246763908820765247 5149353370145863231147871)
    ·
      refine ⟨7724030055218794846721807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5149353370145863231147871 7724030055218794846721807)
      ·
        refine ⟨11586045082828192270082711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7724030055218794846721807 11586045082828192270082711)
        ·
          refine ⟨17379067624242288405124067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11586045082828192270082711 17379067624242288405124067)
          ·
            refine ⟨26068601436363432607686101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17379067624242288405124067 26068601436363432607686101)
            ·
              refine ⟨610982846164767951742643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 26068601436363432607686101 610982846164767951742643)
              ·
                refine ⟨916474269247151927613965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 610982846164767951742643 916474269247151927613965)
                ·
                  refine ⟨343677850967681972855237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 916474269247151927613965 343677850967681972855237)
                  ·
                    rfl

theorem cell20_752974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 7, 1, 3].length) (baseStart_752974 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_752974 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_752974 prefixEnd_752974 := by exact prefixLift 752974
  have htrace : WordTrace (prefixWord ++ tailWord_752974) baseStart_752974 baseEnd_752974 := by
    simpa [prefixWord, tailWord_752974, baseEnd_752974] using wordTrace_append hprefix tailTrace_752974
  have hstable : (prefixWord ++ tailWord_752974).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752974).length < 2 ^ (prefixWord ++ tailWord_752974).sum := by decide
  have hdescent : baseEnd_752974 < baseStart_752974 := by decide
  rcases family_descends (prefixWord ++ tailWord_752974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753022 : List Nat := [4, 2, 3, 2, 1, 1, 2, 5]
def baseStart_753022 : Nat := 118140960795 + 753022 * 2 ^ 59
def prefixEnd_753022 : Nat := 4983230072969 + 3 ^ 40 * 753022 * 2
def baseEnd_753022 : Nat := 114566586491869046418347

theorem tailTrace_753022 : CollatzResearch.WordTrace tailWord_753022 prefixEnd_753022 114566586491869046418347 := by
  unfold tailWord_753022
  simp only [CollatzResearch.WordTrace]
  refine ⟨3433121084742171845483665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18309979118624916509246213 3433121084742171845483665)
  ·
    refine ⟨2574840813556628884112749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3433121084742171845483665 2574840813556628884112749)
    ·
      refine ⟨965565305083735831542281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2574840813556628884112749 965565305083735831542281)
      ·
        refine ⟨724173978812801873656711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 965565305083735831542281 724173978812801873656711)
        ·
          refine ⟨1086260968219202810485067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 724173978812801873656711 1086260968219202810485067)
          ·
            refine ⟨1629391452328804215727601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1086260968219202810485067 1629391452328804215727601)
            ·
              refine ⟨1222043589246603161795701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1629391452328804215727601 1222043589246603161795701)
              ·
                refine ⟨114566586491869046418347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1222043589246603161795701 114566586491869046418347)
                ·
                  rfl

theorem cell20_753022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 2, 5].length) (baseStart_753022 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_753022 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_753022 prefixEnd_753022 := by exact prefixLift 753022
  have htrace : WordTrace (prefixWord ++ tailWord_753022) baseStart_753022 baseEnd_753022 := by
    simpa [prefixWord, tailWord_753022, baseEnd_753022] using wordTrace_append hprefix tailTrace_753022
  have hstable : (prefixWord ++ tailWord_753022).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753022).length < 2 ^ (prefixWord ++ tailWord_753022).sum := by decide
  have hdescent : baseEnd_753022 < baseStart_753022 := by decide
  rcases family_descends (prefixWord ++ tailWord_753022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753061 : List Nat := [1, 3, 1, 2, 1, 1, 2, 1, 8]
def baseStart_753061 : Nat := 118140960795 + 753061 * 2 ^ 59
def prefixEnd_753061 : Nat := 4983230072969 + 3 ^ 40 * 753061 * 2
def baseEnd_753061 : Nat := 343717560138296336954881

theorem tailTrace_753061 : CollatzResearch.WordTrace tailWord_753061 prefixEnd_753061 343717560138296336954881 := by
  unfold tailWord_753061
  simp only [CollatzResearch.WordTrace]
  refine ⟨27466391124796084424539037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18310927416530722949692691 27466391124796084424539037)
  ·
    refine ⟨10299896671798531659202139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27466391124796084424539037 10299896671798531659202139)
    ·
      refine ⟨15449845007697797488803209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10299896671798531659202139 15449845007697797488803209)
      ·
        refine ⟨11587383755773348116602407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15449845007697797488803209 11587383755773348116602407)
        ·
          refine ⟨17381075633660022174903611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11587383755773348116602407 17381075633660022174903611)
          ·
            refine ⟨26071613450490033262355417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17381075633660022174903611 26071613450490033262355417)
            ·
              refine ⟨19553710087867524946766563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26071613450490033262355417 19553710087867524946766563)
              ·
                refine ⟨29330565131801287420149845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19553710087867524946766563 29330565131801287420149845)
                ·
                  refine ⟨343717560138296336954881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29330565131801287420149845 343717560138296336954881)
                  ·
                    rfl

theorem cell20_753061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 8].length) (baseStart_753061 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_753061 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_753061 prefixEnd_753061 := by exact prefixLift 753061
  have htrace : WordTrace (prefixWord ++ tailWord_753061) baseStart_753061 baseEnd_753061 := by
    simpa [prefixWord, tailWord_753061, baseEnd_753061] using wordTrace_append hprefix tailTrace_753061
  have hstable : (prefixWord ++ tailWord_753061).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753061).length < 2 ^ (prefixWord ++ tailWord_753061).sum := by decide
  have hdescent : baseEnd_753061 < baseStart_753061 := by decide
  rcases family_descends (prefixWord ++ tailWord_753061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753064 : List Nat := [2, 1, 6, 1, 2, 8]
def baseStart_753064 : Nat := 118140960795 + 753064 * 2 ^ 59
def prefixEnd_753064 : Nat := 4983230072969 + 3 ^ 40 * 753064 * 2
def baseEnd_753064 : Nat := 12730330719260802216847

theorem tailTrace_753064 : CollatzResearch.WordTrace tailWord_753064 prefixEnd_753064 12730330719260802216847 := by
  unfold tailWord_753064
  simp only [CollatzResearch.WordTrace]
  refine ⟨13733250271892607968449123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18311000362523477291265497 13733250271892607968449123)
  ·
    refine ⟨20599875407838911952673685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13733250271892607968449123 20599875407838911952673685)
    ·
      refine ⟨965619159742448997781579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 20599875407838911952673685 965619159742448997781579)
      ·
        refine ⟨1448428739613673496672369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 965619159742448997781579 1448428739613673496672369)
        ·
          refine ⟨1086321554710255122504277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1448428739613673496672369 1086321554710255122504277)
          ·
            refine ⟨12730330719260802216847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1086321554710255122504277 12730330719260802216847)
            ·
              rfl

theorem cell20_753064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 8].length) (baseStart_753064 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_753064 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_753064 prefixEnd_753064 := by exact prefixLift 753064
  have htrace : WordTrace (prefixWord ++ tailWord_753064) baseStart_753064 baseEnd_753064 := by
    simpa [prefixWord, tailWord_753064, baseEnd_753064] using wordTrace_append hprefix tailTrace_753064
  have hstable : (prefixWord ++ tailWord_753064).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753064).length < 2 ^ (prefixWord ++ tailWord_753064).sum := by decide
  have hdescent : baseEnd_753064 < baseStart_753064 := by decide
  rcases family_descends (prefixWord ++ tailWord_753064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753081 : List Nat := [1, 2, 1, 4, 5, 1, 1, 5]
def baseStart_753081 : Nat := 118140960795 + 753081 * 2 ^ 59
def prefixEnd_753081 : Nat := 4983230072969 + 3 ^ 40 * 753081 * 2
def baseEnd_753081 : Nat := 114575562894421718762711

theorem tailTrace_753081 : CollatzResearch.WordTrace tailWord_753081 prefixEnd_753081 114575562894421718762711 := by
  unfold tailWord_753081
  simp only [CollatzResearch.WordTrace]
  refine ⟨27467120584723627840267097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18311413723149085226844731 27467120584723627840267097)
  ·
    refine ⟨20600340438542720880200323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27467120584723627840267097 20600340438542720880200323)
    ·
      refine ⟨30900510657814081320300485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20600340438542720880200323 30900510657814081320300485)
      ·
        refine ⟨5793845748340140247556341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30900510657814081320300485 5793845748340140247556341)
        ·
          refine ⟨543173038906888148208407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5793845748340140247556341 543173038906888148208407)
          ·
            refine ⟨814759558360332222312611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 543173038906888148208407 814759558360332222312611)
            ·
              refine ⟨1222139337540498333468917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 814759558360332222312611 1222139337540498333468917)
              ·
                refine ⟨114575562894421718762711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1222139337540498333468917 114575562894421718762711)
                ·
                  rfl

theorem cell20_753081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 1, 5].length) (baseStart_753081 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_753081 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_753081 prefixEnd_753081 := by exact prefixLift 753081
  have htrace : WordTrace (prefixWord ++ tailWord_753081) baseStart_753081 baseEnd_753081 := by
    simpa [prefixWord, tailWord_753081, baseEnd_753081] using wordTrace_append hprefix tailTrace_753081
  have hstable : (prefixWord ++ tailWord_753081).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753081).length < 2 ^ (prefixWord ++ tailWord_753081).sum := by decide
  have hdescent : baseEnd_753081 < baseStart_753081 := by decide
  rcases family_descends (prefixWord ++ tailWord_753081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753099 : List Nat := [1, 1, 1, 1, 3, 3, 3, 1, 6]
def baseStart_753099 : Nat := 118140960795 + 753099 * 2 ^ 59
def prefixEnd_753099 : Nat := 4983230072969 + 3 ^ 40 * 753099 * 2
def baseEnd_753099 : Nat := 343734904373737093688059

theorem tailTrace_753099 : CollatzResearch.WordTrace tailWord_753099 prefixEnd_753099 343734904373737093688059 := by
  unfold tailWord_753099
  simp only [CollatzResearch.WordTrace]
  refine ⟨27467777098658416914422351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18311851399105611276281567 27467777098658416914422351)
  ·
    refine ⟨41201665647987625371633527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27467777098658416914422351 41201665647987625371633527)
    ·
      refine ⟨61802498471981438057450291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41201665647987625371633527 61802498471981438057450291)
      ·
        refine ⟨92703747707972157086175437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61802498471981438057450291 92703747707972157086175437)
        ·
          refine ⟨34763905390489558907315789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92703747707972157086175437 34763905390489558907315789)
          ·
            refine ⟨13036464521433584590243421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34763905390489558907315789 13036464521433584590243421)
            ·
              refine ⟨4888674195537594221341283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13036464521433584590243421 4888674195537594221341283)
              ·
                refine ⟨7333011293306391332011925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4888674195537594221341283 7333011293306391332011925)
                ·
                  refine ⟨343734904373737093688059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7333011293306391332011925 343734904373737093688059)
                  ·
                    rfl

theorem cell20_753099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 1, 6].length) (baseStart_753099 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_753099 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_753099 prefixEnd_753099 := by exact prefixLift 753099
  have htrace : WordTrace (prefixWord ++ tailWord_753099) baseStart_753099 baseEnd_753099 := by
    simpa [prefixWord, tailWord_753099, baseEnd_753099] using wordTrace_append hprefix tailTrace_753099
  have hstable : (prefixWord ++ tailWord_753099).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753099).length < 2 ^ (prefixWord ++ tailWord_753099).sum := by decide
  have hdescent : baseEnd_753099 < baseStart_753099 := by decide
  rcases family_descends (prefixWord ++ tailWord_753099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753123 : List Nat := [1, 1, 1, 6, 2, 2, 7]
def baseStart_753123 : Nat := 118140960795 + 753123 * 2 ^ 59
def prefixEnd_753123 : Nat := 4983230072969 + 3 ^ 40 * 753123 * 2
def baseEnd_753123 : Nat := 38193984291966630765329

theorem tailTrace_753123 : CollatzResearch.WordTrace tailWord_753123 prefixEnd_753123 38193984291966630765329 := by
  unfold tailWord_753123
  simp only [CollatzResearch.WordTrace]
  refine ⟨27468652450571469013296023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18312434967047646008864015 27468652450571469013296023)
  ·
    refine ⟨41202978675857203519944035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27468652450571469013296023 41202978675857203519944035)
    ·
      refine ⟨61804468013785805279916053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41202978675857203519944035 61804468013785805279916053)
      ·
        refine ⟨2897084438146209622496065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 61804468013785805279916053 2897084438146209622496065)
        ·
          refine ⟨2172813328609657216872049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2897084438146209622496065 2172813328609657216872049)
          ·
            refine ⟨1629609996457242912654037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2172813328609657216872049 1629609996457242912654037)
            ·
              refine ⟨38193984291966630765329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1629609996457242912654037 38193984291966630765329)
              ·
                rfl

theorem cell20_753123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 7].length) (baseStart_753123 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_753123 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_753123 prefixEnd_753123 := by exact prefixLift 753123
  have htrace : WordTrace (prefixWord ++ tailWord_753123) baseStart_753123 baseEnd_753123 := by
    simpa [prefixWord, tailWord_753123, baseEnd_753123] using wordTrace_append hprefix tailTrace_753123
  have hstable : (prefixWord ++ tailWord_753123).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753123).length < 2 ^ (prefixWord ++ tailWord_753123).sum := by decide
  have hdescent : baseEnd_753123 < baseStart_753123 := by decide
  rcases family_descends (prefixWord ++ tailWord_753123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753171 : List Nat := [1, 1, 1, 2, 1, 6, 3, 3, 2]
def baseStart_753171 : Nat := 118140960795 + 753171 * 2 ^ 59
def prefixEnd_753171 : Nat := 4983230072969 + 3 ^ 40 * 753171 * 2
def baseEnd_753171 : Nat := 343767767135624843287765

theorem tailTrace_753171 : CollatzResearch.WordTrace tailWord_753171 prefixEnd_753171 343767767135624843287765 := by
  unfold tailWord_753171
  simp only [CollatzResearch.WordTrace]
  refine ⟨27470403154397573211043367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18313602102931715474028911 27470403154397573211043367)
  ·
    refine ⟨41205604731596359816565051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27470403154397573211043367 41205604731596359816565051)
    ·
      refine ⟨61808407097394539724847577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41205604731596359816565051 61808407097394539724847577)
      ·
        refine ⟨46356305323045904793635683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61808407097394539724847577 46356305323045904793635683)
        ·
          refine ⟨69534457984568857190453525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46356305323045904793635683 69534457984568857190453525)
          ·
            refine ⟨3259427718026665180802509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 69534457984568857190453525 3259427718026665180802509)
            ·
              refine ⟨1222285394259999442800941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3259427718026665180802509 1222285394259999442800941)
              ·
                refine ⟨458357022847499791050353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1222285394259999442800941 458357022847499791050353)
                ·
                  refine ⟨343767767135624843287765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 458357022847499791050353 343767767135624843287765)
                  ·
                    rfl

theorem cell20_753171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 3, 3, 2].length) (baseStart_753171 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_753171 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_753171 prefixEnd_753171 := by exact prefixLift 753171
  have htrace : WordTrace (prefixWord ++ tailWord_753171) baseStart_753171 baseEnd_753171 := by
    simpa [prefixWord, tailWord_753171, baseEnd_753171] using wordTrace_append hprefix tailTrace_753171
  have hstable : (prefixWord ++ tailWord_753171).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753171).length < 2 ^ (prefixWord ++ tailWord_753171).sum := by decide
  have hdescent : baseEnd_753171 < baseStart_753171 := by decide
  rcases family_descends (prefixWord ++ tailWord_753171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753275 : List Nat := [1, 1, 1, 1, 1, 4, 7, 4]
def baseStart_753275 : Nat := 118140960795 + 753275 * 2 ^ 59
def prefixEnd_753275 : Nat := 4983230072969 + 3 ^ 40 * 753275 * 2
def baseEnd_753275 : Nat := 114605078523154234606891

theorem tailTrace_753275 : CollatzResearch.WordTrace tailWord_753275 prefixEnd_753275 114605078523154234606891 := by
  unfold tailWord_753275
  simp only [CollatzResearch.WordTrace]
  refine ⟨27474196346020798972829279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18316130897347199315219519 27474196346020798972829279)
  ·
    refine ⟨41211294519031198459243919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27474196346020798972829279 41211294519031198459243919)
    ·
      refine ⟨61816941778546797688865879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41211294519031198459243919 61816941778546797688865879)
      ·
        refine ⟨92725412667820196533298819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61816941778546797688865879 92725412667820196533298819)
        ·
          refine ⟨139088119001730294799948229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92725412667820196533298819 139088119001730294799948229)
          ·
            refine ⟨26079022312824430274990293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 139088119001730294799948229 26079022312824430274990293)
            ·
              refine ⟨611227085456822584570085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 26079022312824430274990293 611227085456822584570085)
              ·
                refine ⟨114605078523154234606891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 611227085456822584570085 114605078523154234606891)
                ·
                  rfl

theorem cell20_753275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 7, 4].length) (baseStart_753275 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_753275 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_753275 prefixEnd_753275 := by exact prefixLift 753275
  have htrace : WordTrace (prefixWord ++ tailWord_753275) baseStart_753275 baseEnd_753275 := by
    simpa [prefixWord, tailWord_753275, baseEnd_753275] using wordTrace_append hprefix tailTrace_753275
  have hstable : (prefixWord ++ tailWord_753275).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753275).length < 2 ^ (prefixWord ++ tailWord_753275).sum := by decide
  have hdescent : baseEnd_753275 < baseStart_753275 := by decide
  rcases family_descends (prefixWord ++ tailWord_753275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753285 : List Nat := [1, 3, 1, 1, 4, 1, 4, 3, 2]
def baseStart_753285 : Nat := 118140960795 + 753285 * 2 ^ 59
def prefixEnd_753285 : Nat := 4983230072969 + 3 ^ 40 * 753285 * 2
def baseEnd_753285 : Nat := 343819799841947113487299

theorem tailTrace_753285 : CollatzResearch.WordTrace tailWord_753285 prefixEnd_753285 343819799841947113487299 := by
  unfold tailWord_753285
  simp only [CollatzResearch.WordTrace]
  refine ⟨27474561075984570680693309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18316374050656380453795539 27474561075984570680693309)
  ·
    refine ⟨10302960403494214005259991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27474561075984570680693309 10302960403494214005259991)
    ·
      refine ⟨15454440605241321007889987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10302960403494214005259991 15454440605241321007889987)
      ·
        refine ⟨23181660907861981511834981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15454440605241321007889987 23181660907861981511834981)
        ·
          refine ⟨4346561420224121533469059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23181660907861981511834981 4346561420224121533469059)
          ·
            refine ⟨6519842130336182300203589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4346561420224121533469059 6519842130336182300203589)
            ·
              refine ⟨1222470399438034181288173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6519842130336182300203589 1222470399438034181288173)
              ·
                refine ⟨458426399789262817983065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1222470399438034181288173 458426399789262817983065)
                ·
                  refine ⟨343819799841947113487299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 458426399789262817983065 343819799841947113487299)
                  ·
                    rfl

theorem cell20_753285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 4, 3, 2].length) (baseStart_753285 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_753285 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_753285 prefixEnd_753285 := by exact prefixLift 753285
  have htrace : WordTrace (prefixWord ++ tailWord_753285) baseStart_753285 baseEnd_753285 := by
    simpa [prefixWord, tailWord_753285, baseEnd_753285] using wordTrace_append hprefix tailTrace_753285
  have hstable : (prefixWord ++ tailWord_753285).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753285).length < 2 ^ (prefixWord ++ tailWord_753285).sum := by decide
  have hdescent : baseEnd_753285 < baseStart_753285 := by decide
  rcases family_descends (prefixWord ++ tailWord_753285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753316 : List Nat := [2, 3, 1, 2, 2, 3, 3, 1, 3]
def baseStart_753316 : Nat := 118140960795 + 753316 * 2 ^ 59
def prefixEnd_753316 : Nat := 4983230072969 + 3 ^ 40 * 753316 * 2
def baseEnd_753316 : Nat := 343833949086648783453839

theorem tailTrace_753316 : CollatzResearch.WordTrace tailWord_753316 prefixEnd_753316 343833949086648783453839 := by
  unfold tailWord_753316
  simp only [CollatzResearch.WordTrace]
  refine ⟨13737845869436131487535901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18317127825914841983381201 13737845869436131487535901)
  ·
    refine ⟨5151692201038549307825963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13737845869436131487535901 5151692201038549307825963)
    ·
      refine ⟨7727538301557823961738945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5151692201038549307825963 7727538301557823961738945)
      ·
        refine ⟨5795653726168367971304209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7727538301557823961738945 5795653726168367971304209)
        ·
          refine ⟨4346740294626275978478157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5795653726168367971304209 4346740294626275978478157)
          ·
            refine ⟨1630027610484853491929309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4346740294626275978478157 1630027610484853491929309)
            ·
              refine ⟨611260353931820059473491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1630027610484853491929309 611260353931820059473491)
              ·
                refine ⟨916890530897730089210237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 611260353931820059473491 916890530897730089210237)
                ·
                  refine ⟨343833949086648783453839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 916890530897730089210237 343833949086648783453839)
                  ·
                    rfl

theorem cell20_753316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 3, 1, 3].length) (baseStart_753316 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_753316 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_753316 prefixEnd_753316 := by exact prefixLift 753316
  have htrace : WordTrace (prefixWord ++ tailWord_753316) baseStart_753316 baseEnd_753316 := by
    simpa [prefixWord, tailWord_753316, baseEnd_753316] using wordTrace_append hprefix tailTrace_753316
  have hstable : (prefixWord ++ tailWord_753316).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753316).length < 2 ^ (prefixWord ++ tailWord_753316).sum := by decide
  have hdescent : baseEnd_753316 < baseStart_753316 := by decide
  rcases family_descends (prefixWord ++ tailWord_753316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753326 : List Nat := [4, 1, 4, 1, 2, 2, 2, 4]
def baseStart_753326 : Nat := 118140960795 + 753326 * 2 ^ 59
def prefixEnd_753326 : Nat := 4983230072969 + 3 ^ 40 * 753326 * 2
def baseEnd_753326 : Nat := 114612837786377731040155

theorem tailTrace_753326 : CollatzResearch.WordTrace tailWord_753326 prefixEnd_753326 114612837786377731040155 := by
  unfold tailWord_753326
  simp only [CollatzResearch.WordTrace]
  refine ⟨3434507058604504335366979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18317370979224023121957221 3434507058604504335366979)
  ·
    refine ⟨5151760587906756503050469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3434507058604504335366979 5151760587906756503050469)
    ·
      refine ⟨965955110232516844321963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5151760587906756503050469 965955110232516844321963)
      ·
        refine ⟨1448932665348775266482945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 965955110232516844321963 1448932665348775266482945)
        ·
          refine ⟨1086699499011581449862209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1448932665348775266482945 1086699499011581449862209)
          ·
            refine ⟨815024624258686087396657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1086699499011581449862209 815024624258686087396657)
            ·
              refine ⟨611268468194014565547493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 815024624258686087396657 611268468194014565547493)
              ·
                refine ⟨114612837786377731040155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 611268468194014565547493 114612837786377731040155)
                ·
                  rfl

theorem cell20_753326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 2, 4].length) (baseStart_753326 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_753326 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_753326 prefixEnd_753326 := by exact prefixLift 753326
  have htrace : WordTrace (prefixWord ++ tailWord_753326) baseStart_753326 baseEnd_753326 := by
    simpa [prefixWord, tailWord_753326, baseEnd_753326] using wordTrace_append hprefix tailTrace_753326
  have hstable : (prefixWord ++ tailWord_753326).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753326).length < 2 ^ (prefixWord ++ tailWord_753326).sum := by decide
  have hdescent : baseEnd_753326 < baseStart_753326 := by decide
  rcases family_descends (prefixWord ++ tailWord_753326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753327 : List Nat := [1, 1, 2, 1, 2, 4, 1, 4, 4]
def baseStart_753327 : Nat := 118140960795 + 753327 * 2 ^ 59
def prefixEnd_753327 : Nat := 4983230072969 + 3 ^ 40 * 753327 * 2
def baseEnd_753327 : Nat := 343838969786381634087127

theorem tailTrace_753327 : CollatzResearch.WordTrace tailWord_753327 prefixEnd_753327 343838969786381634087127 := by
  unfold tailWord_753327
  simp only [CollatzResearch.WordTrace]
  refine ⟨27476092941832411853722235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18317395294554941235814823 27476092941832411853722235)
  ·
    refine ⟨41214139412748617780583353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27476092941832411853722235 41214139412748617780583353)
    ·
      refine ⟨30910604559561463335437515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41214139412748617780583353 30910604559561463335437515)
      ·
        refine ⟨46365906839342195003156273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30910604559561463335437515 46365906839342195003156273)
        ·
          refine ⟨34774430129506646252367205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46365906839342195003156273 34774430129506646252367205)
          ·
            refine ⟨6520205649282496172318851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34774430129506646252367205 6520205649282496172318851)
            ·
              refine ⟨9780308473923744258478277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6520205649282496172318851 9780308473923744258478277)
              ·
                refine ⟨1833807838860702048464677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9780308473923744258478277 1833807838860702048464677)
                ·
                  refine ⟨343838969786381634087127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1833807838860702048464677 343838969786381634087127)
                  ·
                    rfl

theorem cell20_753327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 4, 4].length) (baseStart_753327 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_753327 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_753327 prefixEnd_753327 := by exact prefixLift 753327
  have htrace : WordTrace (prefixWord ++ tailWord_753327) baseStart_753327 baseEnd_753327 := by
    simpa [prefixWord, tailWord_753327, baseEnd_753327] using wordTrace_append hprefix tailTrace_753327
  have hstable : (prefixWord ++ tailWord_753327).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753327).length < 2 ^ (prefixWord ++ tailWord_753327).sum := by decide
  have hdescent : baseEnd_753327 < baseStart_753327 := by decide
  rcases family_descends (prefixWord ++ tailWord_753327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753340 : List Nat := [2, 2, 2, 3, 1, 4, 1, 3, 2]
def baseStart_753340 : Nat := 118140960795 + 753340 * 2 ^ 59
def prefixEnd_753340 : Nat := 4983230072969 + 3 ^ 40 * 753340 * 2
def baseEnd_753340 : Nat := 343844903340611366653741

theorem tailTrace_753340 : CollatzResearch.WordTrace tailWord_753340 prefixEnd_753340 343844903340611366653741 := by
  unfold tailWord_753340
  simp only [CollatzResearch.WordTrace]
  refine ⟨13738283545392657536972737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18317711393856876715963649 13738283545392657536972737)
  ·
    refine ⟨10303712659044493152729553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13738283545392657536972737 10303712659044493152729553)
    ·
      refine ⟨7727784494283369864547165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10303712659044493152729553 7727784494283369864547165)
      ·
        refine ⟨2897919185356263699205187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7727784494283369864547165 2897919185356263699205187)
        ·
          refine ⟨4346878778034395548807781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2897919185356263699205187 4346878778034395548807781)
          ·
            refine ⟨815039770881449165401459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4346878778034395548807781 815039770881449165401459)
            ·
              refine ⟨1222559656322173748102189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 815039770881449165401459 1222559656322173748102189)
              ·
                refine ⟨458459871120815155538321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1222559656322173748102189 458459871120815155538321)
                ·
                  refine ⟨343844903340611366653741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 458459871120815155538321 343844903340611366653741)
                  ·
                    rfl

theorem cell20_753340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 1, 3, 2].length) (baseStart_753340 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_753340 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_753340 prefixEnd_753340 := by exact prefixLift 753340
  have htrace : WordTrace (prefixWord ++ tailWord_753340) baseStart_753340 baseEnd_753340 := by
    simpa [prefixWord, tailWord_753340, baseEnd_753340] using wordTrace_append hprefix tailTrace_753340
  have hstable : (prefixWord ++ tailWord_753340).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753340).length < 2 ^ (prefixWord ++ tailWord_753340).sum := by decide
  have hdescent : baseEnd_753340 < baseStart_753340 := by decide
  rcases family_descends (prefixWord ++ tailWord_753340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753358 : List Nat := [4, 1, 1, 1, 3, 1, 1, 3, 5]
def baseStart_753358 : Nat := 118140960795 + 753358 * 2 ^ 59
def prefixEnd_753358 : Nat := 4983230072969 + 3 ^ 40 * 753358 * 2
def baseEnd_753358 : Nat := 343853119031083304053667

theorem tailTrace_753358 : CollatzResearch.WordTrace tailWord_753358 prefixEnd_753358 343853119031083304053667 := by
  unfold tailWord_753358
  simp only [CollatzResearch.WordTrace]
  refine ⟨3434652950590013018512591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18318149069813402765400485 3434652950590013018512591)
  ·
    refine ⟨5151979425885019527768887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3434652950590013018512591 5151979425885019527768887)
    ·
      refine ⟨7727969138827529291653331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5151979425885019527768887 7727969138827529291653331)
      ·
        refine ⟨11591953708241293937479997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7727969138827529291653331 11591953708241293937479997)
        ·
          refine ⟨4346982640590485226554999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11591953708241293937479997 4346982640590485226554999)
          ·
            refine ⟨6520473960885727839832499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4346982640590485226554999 6520473960885727839832499)
            ·
              refine ⟨9780710941328591759748749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6520473960885727839832499 9780710941328591759748749)
              ·
                refine ⟨3667766602998221909905781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9780710941328591759748749 3667766602998221909905781)
                ·
                  refine ⟨343853119031083304053667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3667766602998221909905781 343853119031083304053667)
                  ·
                    rfl

theorem cell20_753358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 3, 5].length) (baseStart_753358 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_753358 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_753358 prefixEnd_753358 := by exact prefixLift 753358
  have htrace : WordTrace (prefixWord ++ tailWord_753358) baseStart_753358 baseEnd_753358 := by
    simpa [prefixWord, tailWord_753358, baseEnd_753358] using wordTrace_append hprefix tailTrace_753358
  have hstable : (prefixWord ++ tailWord_753358).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753358).length < 2 ^ (prefixWord ++ tailWord_753358).sum := by decide
  have hdescent : baseEnd_753358 < baseStart_753358 := by decide
  rcases family_descends (prefixWord ++ tailWord_753358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753389 : List Nat := [1, 5, 1, 2, 1, 2, 2, 6]
def baseStart_753389 : Nat := 118140960795 + 753389 * 2 ^ 59
def prefixEnd_753389 : Nat := 4983230072969 + 3 ^ 40 * 753389 * 2
def baseEnd_753389 : Nat := 114622422758594991340069

theorem tailTrace_753389 : CollatzResearch.WordTrace tailWord_753389 prefixEnd_753389 114622422758594991340069 := by
  unfold tailWord_753389
  simp only [CollatzResearch.WordTrace]
  refine ⟨27478354267607796442479221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18318902845071864294986147 27478354267607796442479221)
  ·
    refine ⟨2576095712588230916482427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27478354267607796442479221 2576095712588230916482427)
    ·
      refine ⟨3864143568882346374723641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2576095712588230916482427 3864143568882346374723641)
      ·
        refine ⟨2898107676661759781042731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3864143568882346374723641 2898107676661759781042731)
        ·
          refine ⟨4347161514992639671564097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2898107676661759781042731 4347161514992639671564097)
          ·
            refine ⟨3260371136244479753673073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4347161514992639671564097 3260371136244479753673073)
            ·
              refine ⟨2445278352183359815254805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3260371136244479753673073 2445278352183359815254805)
              ·
                refine ⟨114622422758594991340069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2445278352183359815254805 114622422758594991340069)
                ·
                  rfl

theorem cell20_753389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 6].length) (baseStart_753389 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_753389 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_753389 prefixEnd_753389 := by exact prefixLift 753389
  have htrace : WordTrace (prefixWord ++ tailWord_753389) baseStart_753389 baseEnd_753389 := by
    simpa [prefixWord, tailWord_753389, baseEnd_753389] using wordTrace_append hprefix tailTrace_753389
  have hstable : (prefixWord ++ tailWord_753389).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753389).length < 2 ^ (prefixWord ++ tailWord_753389).sum := by decide
  have hdescent : baseEnd_753389 < baseStart_753389 := by decide
  rcases family_descends (prefixWord ++ tailWord_753389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
