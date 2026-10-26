import V185TrunkScan21Chunk055

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_678794 : List Nat := [3, 1, 2, 4, 1, 2, 1, 3, 4]
def baseStart_678794 : Nat := 118140960795 + 678794 * 2 ^ 59
def prefixEnd_678794 : Nat := 4983230072969 + 3 ^ 40 * 678794 * 2
def baseEnd_678794 : Nat := 154910038839165532912573

theorem tailTrace_678794 : CollatzResearch.WordTrace tailWord_678794 prefixEnd_678794 154910038839165532912573 := by
  unfold tailWord_678794
  simp only [CollatzResearch.WordTrace]
  refine ⟨6189412775713185407686859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16505100735235161087164957 6189412775713185407686859)
  ·
    refine ⟨9284119163569778111530289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6189412775713185407686859 9284119163569778111530289)
    ·
      refine ⟨6963089372677333583647717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9284119163569778111530289 6963089372677333583647717)
      ·
        refine ⟨1305579257377000046933947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6963089372677333583647717 1305579257377000046933947)
        ·
          refine ⟨1958368886065500070400921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1305579257377000046933947 1958368886065500070400921)
          ·
            refine ⟨1468776664549125052800691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1958368886065500070400921 1468776664549125052800691)
            ·
              refine ⟨2203164996823687579201037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1468776664549125052800691 2203164996823687579201037)
              ·
                refine ⟨826186873808882842200389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2203164996823687579201037 826186873808882842200389)
                ·
                  refine ⟨154910038839165532912573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 826186873808882842200389 154910038839165532912573)
                  ·
                    rfl

theorem cell21_678794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 3, 4].length) (baseStart_678794 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_678794 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_678794 prefixEnd_678794 := by exact prefixLift 678794
  have htrace : WordTrace (prefixWord ++ tailWord_678794) baseStart_678794 baseEnd_678794 := by
    simpa [prefixWord, tailWord_678794, baseEnd_678794] using wordTrace_append hprefix tailTrace_678794
  have hstable : (prefixWord ++ tailWord_678794).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678794).length < 2 ^ (prefixWord ++ tailWord_678794).sum := by decide
  have hdescent : baseEnd_678794 < baseStart_678794 := by decide
  rcases family_descends (prefixWord ++ tailWord_678794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678881 : List Nat := [1, 2, 3, 1, 2, 1, 1, 1, 9]
def baseStart_678881 : Nat := 118140960795 + 678881 * 2 ^ 59
def prefixEnd_678881 : Nat := 4983230072969 + 3 ^ 40 * 678881 * 2
def baseEnd_678881 : Nat := 154929893424472714962395

theorem tailTrace_678881 : CollatzResearch.WordTrace tailWord_678881 prefixEnd_678881 154929893424472714962395 := by
  unfold tailWord_678881
  simp only [CollatzResearch.WordTrace]
  refine ⟨24760824253537555489164497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16507216169025036992776331 24760824253537555489164497)
  ·
    refine ⟨18570618190153166616873373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24760824253537555489164497 18570618190153166616873373)
    ·
      refine ⟨6963981821307437481327515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18570618190153166616873373 6963981821307437481327515)
      ·
        refine ⟨10445972731961156221991273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6963981821307437481327515 10445972731961156221991273)
        ·
          refine ⟨7834479548970867166493455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10445972731961156221991273 7834479548970867166493455)
          ·
            refine ⟨11751719323456300749740183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7834479548970867166493455 11751719323456300749740183)
            ·
              refine ⟨17627578985184451124610275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11751719323456300749740183 17627578985184451124610275)
              ·
                refine ⟨26441368477776676686915413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17627578985184451124610275 26441368477776676686915413)
                ·
                  refine ⟨154929893424472714962395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 26441368477776676686915413 154929893424472714962395)
                  ·
                    rfl

theorem cell21_678881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 9].length) (baseStart_678881 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_678881 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_678881 prefixEnd_678881 := by exact prefixLift 678881
  have htrace : WordTrace (prefixWord ++ tailWord_678881) baseStart_678881 baseEnd_678881 := by
    simpa [prefixWord, tailWord_678881, baseEnd_678881] using wordTrace_append hprefix tailTrace_678881
  have hstable : (prefixWord ++ tailWord_678881).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678881).length < 2 ^ (prefixWord ++ tailWord_678881).sum := by decide
  have hdescent : baseEnd_678881 < baseStart_678881 := by decide
  rcases family_descends (prefixWord ++ tailWord_678881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678943 : List Nat := [1, 1, 2, 4, 1, 5, 7]
def baseStart_678943 : Nat := 118140960795 + 678943 * 2 ^ 59
def prefixEnd_678943 : Nat := 4983230072969 + 3 ^ 40 * 678943 * 2
def baseEnd_678943 : Nat := 17216004741019376103215

theorem tailTrace_678943 : CollatzResearch.WordTrace tailWord_678943 prefixEnd_678943 17216004741019376103215 := by
  unfold tailWord_678943
  simp only [CollatzResearch.WordTrace]
  refine ⟨24763085579312940077921483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16508723719541960051947655 24763085579312940077921483)
  ·
    refine ⟨37144628368969410116882225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24763085579312940077921483 37144628368969410116882225)
    ·
      refine ⟨27858471276727057587661669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37144628368969410116882225 27858471276727057587661669)
      ·
        refine ⟨5223463364386323297686563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27858471276727057587661669 5223463364386323297686563)
        ·
          refine ⟨7835195046579484946529845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5223463364386323297686563 7835195046579484946529845)
          ·
            refine ⟨734549535616826713737173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7835195046579484946529845 734549535616826713737173)
            ·
              refine ⟨17216004741019376103215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 734549535616826713737173 17216004741019376103215)
              ·
                rfl

theorem cell21_678943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 7].length) (baseStart_678943 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_678943 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_678943 prefixEnd_678943 := by exact prefixLift 678943
  have htrace : WordTrace (prefixWord ++ tailWord_678943) baseStart_678943 baseEnd_678943 := by
    simpa [prefixWord, tailWord_678943, baseEnd_678943] using wordTrace_append hprefix tailTrace_678943
  have hstable : (prefixWord ++ tailWord_678943).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678943).length < 2 ^ (prefixWord ++ tailWord_678943).sum := by decide
  have hdescent : baseEnd_678943 < baseStart_678943 := by decide
  rcases family_descends (prefixWord ++ tailWord_678943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679185 : List Nat := [1, 2, 2, 1, 1, 4, 2, 3, 5]
def baseStart_679185 : Nat := 118140960795 + 679185 * 2 ^ 59
def prefixEnd_679185 : Nat := 4983230072969 + 3 ^ 40 * 679185 * 2
def baseEnd_679185 : Nat := 154999270366235741895107

theorem tailTrace_679185 : CollatzResearch.WordTrace tailWord_679185 prefixEnd_679185 154999270366235741895107 := by
  unfold tailWord_679185
  simp only [CollatzResearch.WordTrace]
  refine ⟨24771912044436215408231009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16514608029624143605487339 24771912044436215408231009)
  ·
    refine ⟨18578934033327161556173257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24771912044436215408231009 18578934033327161556173257)
    ·
      refine ⟨13934200524995371167129943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18578934033327161556173257 13934200524995371167129943)
      ·
        refine ⟨20901300787493056750694915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13934200524995371167129943 20901300787493056750694915)
        ·
          refine ⟨31351951181239585126042373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20901300787493056750694915 31351951181239585126042373)
          ·
            refine ⟨5878490846482422211132945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31351951181239585126042373 5878490846482422211132945)
            ·
              refine ⟨4408868134861816658349709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5878490846482422211132945 4408868134861816658349709)
              ·
                refine ⟨1653325550573181246881141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4408868134861816658349709 1653325550573181246881141)
                ·
                  refine ⟨154999270366235741895107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1653325550573181246881141 154999270366235741895107)
                  ·
                    rfl

theorem cell21_679185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 3, 5].length) (baseStart_679185 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_679185 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_679185 prefixEnd_679185 := by exact prefixLift 679185
  have htrace : WordTrace (prefixWord ++ tailWord_679185) baseStart_679185 baseEnd_679185 := by
    simpa [prefixWord, tailWord_679185, baseEnd_679185] using wordTrace_append hprefix tailTrace_679185
  have hstable : (prefixWord ++ tailWord_679185).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679185).length < 2 ^ (prefixWord ++ tailWord_679185).sum := by decide
  have hdescent : baseEnd_679185 < baseStart_679185 := by decide
  rcases family_descends (prefixWord ++ tailWord_679185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679219 : List Nat := [1, 1, 1, 2, 5, 3, 2, 3, 3]
def baseStart_679219 : Nat := 118140960795 + 679219 * 2 ^ 59
def prefixEnd_679219 : Nat := 4983230072969 + 3 ^ 40 * 679219 * 2
def baseEnd_679219 : Nat := 155007029629459238328371

theorem tailTrace_679219 : CollatzResearch.WordTrace tailWord_679219 prefixEnd_679219 155007029629459238328371 := by
  unfold tailWord_679219
  simp only [CollatzResearch.WordTrace]
  refine ⟨24773152126313039214968711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16515434750875359476645807 24773152126313039214968711)
  ·
    refine ⟨37159728189469558822453067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24773152126313039214968711 37159728189469558822453067)
    ·
      refine ⟨55739592284204338233679601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37159728189469558822453067 55739592284204338233679601)
      ·
        refine ⟨41804694213153253675259701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55739592284204338233679601 41804694213153253675259701)
        ·
          refine ⟨3919190082483117532055597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 41804694213153253675259701 3919190082483117532055597)
          ·
            refine ⟨1469696280931169074520849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3919190082483117532055597 1469696280931169074520849)
            ·
              refine ⟨1102272210698376805890637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1469696280931169074520849 1102272210698376805890637)
              ·
                refine ⟨413352079011891302208989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1102272210698376805890637 413352079011891302208989)
                ·
                  refine ⟨155007029629459238328371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 413352079011891302208989 155007029629459238328371)
                  ·
                    rfl

theorem cell21_679219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 2, 3, 3].length) (baseStart_679219 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_679219 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_679219 prefixEnd_679219 := by exact prefixLift 679219
  have htrace : WordTrace (prefixWord ++ tailWord_679219) baseStart_679219 baseEnd_679219 := by
    simpa [prefixWord, tailWord_679219, baseEnd_679219] using wordTrace_append hprefix tailTrace_679219
  have hstable : (prefixWord ++ tailWord_679219).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679219).length < 2 ^ (prefixWord ++ tailWord_679219).sum := by decide
  have hdescent : baseEnd_679219 < baseStart_679219 := by decide
  rcases family_descends (prefixWord ++ tailWord_679219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679233 : List Nat := [1, 2, 5, 2, 1, 2, 1, 1, 6]
def baseStart_679233 : Nat := 118140960795 + 679233 * 2 ^ 59
def prefixEnd_679233 : Nat := 4983230072969 + 3 ^ 40 * 679233 * 2
def baseEnd_679233 : Nat := 155010224620198325095009

theorem tailTrace_679233 : CollatzResearch.WordTrace tailWord_679233 prefixEnd_679233 155010224620198325095009 := by
  unfold tailWord_679233
  simp only [CollatzResearch.WordTrace]
  refine ⟨24773662748262319605978353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16515775165508213070652235 24773662748262319605978353)
  ·
    refine ⟨18580247061196739704483765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24773662748262319605978353 18580247061196739704483765)
    ·
      refine ⟨1741898161987194347295353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18580247061196739704483765 1741898161987194347295353)
      ·
        refine ⟨1306423621490395760471515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1741898161987194347295353 1306423621490395760471515)
        ·
          refine ⟨1959635432235593640707273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1306423621490395760471515 1959635432235593640707273)
          ·
            refine ⟨1469726574176695230530455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1959635432235593640707273 1469726574176695230530455)
            ·
              refine ⟨2204589861265042845795683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1469726574176695230530455 2204589861265042845795683)
              ·
                refine ⟨3306884791897564268693525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2204589861265042845795683 3306884791897564268693525)
                ·
                  refine ⟨155010224620198325095009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3306884791897564268693525 155010224620198325095009)
                  ·
                    rfl

theorem cell21_679233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 1, 6].length) (baseStart_679233 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_679233 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_679233 prefixEnd_679233 := by exact prefixLift 679233
  have htrace : WordTrace (prefixWord ++ tailWord_679233) baseStart_679233 baseEnd_679233 := by
    simpa [prefixWord, tailWord_679233, baseEnd_679233] using wordTrace_append hprefix tailTrace_679233
  have hstable : (prefixWord ++ tailWord_679233).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679233).length < 2 ^ (prefixWord ++ tailWord_679233).sum := by decide
  have hdescent : baseEnd_679233 < baseStart_679233 := by decide
  rcases family_descends (prefixWord ++ tailWord_679233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679236 : List Nat := [2, 3, 4, 1, 1, 1, 2, 4, 3]
def baseStart_679236 : Nat := 118140960795 + 679236 * 2 ^ 59
def prefixEnd_679236 : Nat := 4983230072969 + 3 ^ 40 * 679236 * 2
def baseEnd_679236 : Nat := 155010909261070986545003

theorem tailTrace_679236 : CollatzResearch.WordTrace tailWord_679236 prefixEnd_679236 155010909261070986545003 := by
  unfold tailWord_679236
  simp only [CollatzResearch.WordTrace]
  refine ⟨12386886083625725559168781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16515848111500967412225041 12386886083625725559168781)
  ·
    refine ⟨4645082281359647084688293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12386886083625725559168781 4645082281359647084688293)
    ·
      refine ⟨870952927754933828379055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4645082281359647084688293 870952927754933828379055)
      ·
        refine ⟨1306429391632400742568583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 870952927754933828379055 1306429391632400742568583)
        ·
          refine ⟨1959644087448601113852875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1306429391632400742568583 1959644087448601113852875)
          ·
            refine ⟨2939466131172901670779313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1959644087448601113852875 2939466131172901670779313)
            ·
              refine ⟨2204599598379676253084485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2939466131172901670779313 2204599598379676253084485)
              ·
                refine ⟨413362424696189297453341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2204599598379676253084485 413362424696189297453341)
                ·
                  refine ⟨155010909261070986545003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 413362424696189297453341 155010909261070986545003)
                  ·
                    rfl

theorem cell21_679236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 4, 3].length) (baseStart_679236 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_679236 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_679236 prefixEnd_679236 := by exact prefixLift 679236
  have htrace : WordTrace (prefixWord ++ tailWord_679236) baseStart_679236 baseEnd_679236 := by
    simpa [prefixWord, tailWord_679236, baseEnd_679236] using wordTrace_append hprefix tailTrace_679236
  have hstable : (prefixWord ++ tailWord_679236).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679236).length < 2 ^ (prefixWord ++ tailWord_679236).sum := by decide
  have hdescent : baseEnd_679236 < baseStart_679236 := by decide
  rcases family_descends (prefixWord ++ tailWord_679236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679264 : List Nat := [2, 1, 1, 3, 4, 3, 2, 5]
def baseStart_679264 : Nat := 118140960795 + 679264 * 2 ^ 59
def prefixEnd_679264 : Nat := 4983230072969 + 3 ^ 40 * 679264 * 2
def baseEnd_679264 : Nat := 51672433080849720026093

theorem tailTrace_679264 : CollatzResearch.WordTrace tailWord_679264 prefixEnd_679264 51672433080849720026093 := by
  unfold tailWord_679264
  simp only [CollatzResearch.WordTrace]
  refine ⟨12387396705575005950178423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16516528940766674600237897 12387396705575005950178423)
  ·
    refine ⟨18581095058362508925267635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12387396705575005950178423 18581095058362508925267635)
    ·
      refine ⟨27871642587543763387901453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18581095058362508925267635 27871642587543763387901453)
      ·
        refine ⟨10451865970328911270463045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27871642587543763387901453 10451865970328911270463045)
        ·
          refine ⟨1959724869436670863211821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10451865970328911270463045 1959724869436670863211821)
          ·
            refine ⟨734896826038751573704433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1959724869436670863211821 734896826038751573704433)
            ·
              refine ⟨551172619529063680278325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 734896826038751573704433 551172619529063680278325)
              ·
                refine ⟨51672433080849720026093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 551172619529063680278325 51672433080849720026093)
                ·
                  rfl

theorem cell21_679264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 2, 5].length) (baseStart_679264 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_679264 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_679264 prefixEnd_679264 := by exact prefixLift 679264
  have htrace : WordTrace (prefixWord ++ tailWord_679264) baseStart_679264 baseEnd_679264 := by
    simpa [prefixWord, tailWord_679264, baseEnd_679264] using wordTrace_append hprefix tailTrace_679264
  have hstable : (prefixWord ++ tailWord_679264).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679264).length < 2 ^ (prefixWord ++ tailWord_679264).sum := by decide
  have hdescent : baseEnd_679264 < baseStart_679264 := by decide
  rcases family_descends (prefixWord ++ tailWord_679264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679292 : List Nat := [2, 2, 2, 1, 1, 1, 4, 4, 4]
def baseStart_679292 : Nat := 118140960795 + 679292 * 2 ^ 59
def prefixEnd_679292 : Nat := 4983230072969 + 3 ^ 40 * 679292 * 2
def baseEnd_679292 : Nat := 155023689224027333611555

theorem tailTrace_679292 : CollatzResearch.WordTrace tailWord_679292 prefixEnd_679292 155023689224027333611555 := by
  unfold tailWord_679292
  simp only [CollatzResearch.WordTrace]
  refine ⟨12387907327524286341188065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16517209770032381788250753 12387907327524286341188065)
  ·
    refine ⟨9290930495643214755891049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12387907327524286341188065 9290930495643214755891049)
    ·
      refine ⟨6968197871732411066918287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9290930495643214755891049 6968197871732411066918287)
      ·
        refine ⟨10452296807598616600377431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6968197871732411066918287 10452296807598616600377431)
        ·
          refine ⟨15678445211397924900566147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10452296807598616600377431 15678445211397924900566147)
          ·
            refine ⟨23517667817096887350849221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15678445211397924900566147 23517667817096887350849221)
            ·
              refine ⟨4409562715705666378284229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23517667817096887350849221 4409562715705666378284229)
              ·
                refine ⟨826793009194812445928293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4409562715705666378284229 826793009194812445928293)
                ·
                  refine ⟨155023689224027333611555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 826793009194812445928293 155023689224027333611555)
                  ·
                    rfl

theorem cell21_679292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 4, 4].length) (baseStart_679292 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_679292 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_679292 prefixEnd_679292 := by exact prefixLift 679292
  have htrace : WordTrace (prefixWord ++ tailWord_679292) baseStart_679292 baseEnd_679292 := by
    simpa [prefixWord, tailWord_679292, baseEnd_679292] using wordTrace_append hprefix tailTrace_679292
  have hstable : (prefixWord ++ tailWord_679292).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679292).length < 2 ^ (prefixWord ++ tailWord_679292).sum := by decide
  have hdescent : baseEnd_679292 < baseStart_679292 := by decide
  rcases family_descends (prefixWord ++ tailWord_679292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679368 : List Nat := [2, 1, 3, 1, 3, 1, 1, 5, 4]
def baseStart_679368 : Nat := 118140960795 + 679368 * 2 ^ 59
def prefixEnd_679368 : Nat := 4983230072969 + 3 ^ 40 * 679368 * 2
def baseEnd_679368 : Nat := 155041033459468090344733

theorem tailTrace_679368 : CollatzResearch.WordTrace tailWord_679368 prefixEnd_679368 155041033459468090344733 := by
  unfold tailWord_679368
  simp only [CollatzResearch.WordTrace]
  refine ⟨12389293301386618831071379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16519057735182158441428505 12389293301386618831071379)
  ·
    refine ⟨18583939952079928246607069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12389293301386618831071379 18583939952079928246607069)
    ·
      refine ⟨6968977482029973092477651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18583939952079928246607069 6968977482029973092477651)
      ·
        refine ⟨10453466223044959638716477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6968977482029973092477651 10453466223044959638716477)
        ·
          refine ⟨3920049833641859864518679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10453466223044959638716477 3920049833641859864518679)
          ·
            refine ⟨5880074750462789796778019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3920049833641859864518679 5880074750462789796778019)
            ·
              refine ⟨8820112125694184695167029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5880074750462789796778019 8820112125694184695167029)
              ·
                refine ⟨826885511783829815171909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8820112125694184695167029 826885511783829815171909)
                ·
                  refine ⟨155041033459468090344733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 826885511783829815171909 155041033459468090344733)
                  ·
                    rfl

theorem cell21_679368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 5, 4].length) (baseStart_679368 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_679368 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_679368 prefixEnd_679368 := by exact prefixLift 679368
  have htrace : WordTrace (prefixWord ++ tailWord_679368) baseStart_679368 baseEnd_679368 := by
    simpa [prefixWord, tailWord_679368, baseEnd_679368] using wordTrace_append hprefix tailTrace_679368
  have hstable : (prefixWord ++ tailWord_679368).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679368).length < 2 ^ (prefixWord ++ tailWord_679368).sum := by decide
  have hdescent : baseEnd_679368 < baseStart_679368 := by decide
  rcases family_descends (prefixWord ++ tailWord_679368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679402 : List Nat := [3, 1, 3, 1, 4, 2, 1, 2, 4]
def baseStart_679402 : Nat := 118140960795 + 679402 * 2 ^ 59
def prefixEnd_679402 : Nat := 4983230072969 + 3 ^ 40 * 679402 * 2
def baseEnd_679402 : Nat := 155048792722691586777997

theorem tailTrace_679402 : CollatzResearch.WordTrace tailWord_679402 prefixEnd_679402 155048792722691586777997 := by
  unfold tailWord_679402
  simp only [CollatzResearch.WordTrace]
  refine ⟨6194956671162515367220115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16519884456433374312586973 6194956671162515367220115)
  ·
    refine ⟨9292435006743773050830173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6194956671162515367220115 9292435006743773050830173)
    ·
      refine ⟨3484663127528914894061315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9292435006743773050830173 3484663127528914894061315)
      ·
        refine ⟨5226994691293372341091973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3484663127528914894061315 5226994691293372341091973)
        ·
          refine ⟨980061504617507313954745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5226994691293372341091973 980061504617507313954745)
          ·
            refine ⟨735046128463130485466059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 980061504617507313954745 735046128463130485466059)
            ·
              refine ⟨1102569192694695728199089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 735046128463130485466059 1102569192694695728199089)
              ·
                refine ⟨826926894521021796149317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1102569192694695728199089 826926894521021796149317)
                ·
                  refine ⟨155048792722691586777997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 826926894521021796149317 155048792722691586777997)
                  ·
                    rfl

theorem cell21_679402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 1, 2, 4].length) (baseStart_679402 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_679402 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_679402 prefixEnd_679402 := by exact prefixLift 679402
  have htrace : WordTrace (prefixWord ++ tailWord_679402) baseStart_679402 baseEnd_679402 := by
    simpa [prefixWord, tailWord_679402, baseEnd_679402] using wordTrace_append hprefix tailTrace_679402
  have hstable : (prefixWord ++ tailWord_679402).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679402).length < 2 ^ (prefixWord ++ tailWord_679402).sum := by decide
  have hdescent : baseEnd_679402 < baseStart_679402 := by decide
  rcases family_descends (prefixWord ++ tailWord_679402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679458 : List Nat := [3, 3, 1, 1, 1, 1, 11]
def baseStart_679458 : Nat := 118140960795 + 679458 * 2 ^ 59
def prefixEnd_679458 : Nat := 4983230072969 + 3 ^ 40 * 679458 * 2
def baseEnd_679458 : Nat := 17229063631738659316061

theorem tailTrace_679458 : CollatzResearch.WordTrace tailWord_679458 prefixEnd_679458 17229063631738659316061 := by
  unfold tailWord_679458
  simp only [CollatzResearch.WordTrace]
  refine ⟨6195467293111795758229757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16521246114964788688612685 6195467293111795758229757)
  ·
    refine ⟨2323300234916923409336159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6195467293111795758229757 2323300234916923409336159)
    ·
      refine ⟨3484950352375385114004239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2323300234916923409336159 3484950352375385114004239)
      ·
        refine ⟨5227425528563077671006359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3484950352375385114004239 5227425528563077671006359)
        ·
          refine ⟨7841138292844616506509539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5227425528563077671006359 7841138292844616506509539)
          ·
            refine ⟨11761707439266924759764309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7841138292844616506509539 11761707439266924759764309)
            ·
              refine ⟨17229063631738659316061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 11761707439266924759764309 17229063631738659316061)
              ·
                rfl

theorem cell21_679458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 11].length) (baseStart_679458 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_679458 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_679458 prefixEnd_679458 := by exact prefixLift 679458
  have htrace : WordTrace (prefixWord ++ tailWord_679458) baseStart_679458 baseEnd_679458 := by
    simpa [prefixWord, tailWord_679458, baseEnd_679458] using wordTrace_append hprefix tailTrace_679458
  have hstable : (prefixWord ++ tailWord_679458).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679458).length < 2 ^ (prefixWord ++ tailWord_679458).sum := by decide
  have hdescent : baseEnd_679458 < baseStart_679458 := by decide
  rcases family_descends (prefixWord ++ tailWord_679458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679464 : List Nat := [2, 1, 5, 2, 3, 1, 1, 1, 5]
def baseStart_679464 : Nat := 118140960795 + 679464 * 2 ^ 59
def prefixEnd_679464 : Nat := 4983230072969 + 3 ^ 40 * 679464 * 2
def baseEnd_679464 : Nat := 155062941967393256744537

theorem tailTrace_679464 : CollatzResearch.WordTrace tailWord_679464 prefixEnd_679464 155062941967393256744537 := by
  unfold tailWord_679464
  simp only [CollatzResearch.WordTrace]
  refine ⟨12391044005212723028818723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16521392006950297371758297 12391044005212723028818723)
  ·
    refine ⟨18586566007819084543228085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12391044005212723028818723 18586566007819084543228085)
    ·
      refine ⟨1742490563233039175927633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18586566007819084543228085 1742490563233039175927633)
      ·
        refine ⟨1306867922424779381945725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1742490563233039175927633 1306867922424779381945725)
        ·
          refine ⟨490075470909292268229647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1306867922424779381945725 490075470909292268229647)
          ·
            refine ⟨735113206363938402344471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 490075470909292268229647 735113206363938402344471)
            ·
              refine ⟨1102669809545907603516707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 735113206363938402344471 1102669809545907603516707)
              ·
                refine ⟨1654004714318861405275061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1102669809545907603516707 1654004714318861405275061)
                ·
                  refine ⟨155062941967393256744537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1654004714318861405275061 155062941967393256744537)
                  ·
                    rfl

theorem cell21_679464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 1, 1, 5].length) (baseStart_679464 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_679464 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_679464 prefixEnd_679464 := by exact prefixLift 679464
  have htrace : WordTrace (prefixWord ++ tailWord_679464) baseStart_679464 baseEnd_679464 := by
    simpa [prefixWord, tailWord_679464, baseEnd_679464] using wordTrace_append hprefix tailTrace_679464
  have hstable : (prefixWord ++ tailWord_679464).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679464).length < 2 ^ (prefixWord ++ tailWord_679464).sum := by decide
  have hdescent : baseEnd_679464 < baseStart_679464 := by decide
  rcases family_descends (prefixWord ++ tailWord_679464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679478 : List Nat := [5, 1, 2, 1, 3, 1, 1, 3, 4]
def baseStart_679478 : Nat := 118140960795 + 679478 * 2 ^ 59
def prefixEnd_679478 : Nat := 4983230072969 + 3 ^ 40 * 679478 * 2
def baseEnd_679478 : Nat := 155066136958132343511175

theorem tailTrace_679478 : CollatzResearch.WordTrace tailWord_679478 prefixEnd_679478 155066136958132343511175 := by
  unfold tailWord_679478
  simp only [CollatzResearch.WordTrace]
  refine ⟨1548912414523420403040443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16521732421583150965764725 1548912414523420403040443)
  ·
    refine ⟨2323368621785130604560665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1548912414523420403040443 2323368621785130604560665)
    ·
      refine ⟨1742526466338847953420499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2323368621785130604560665 1742526466338847953420499)
      ·
        refine ⟨2613789699508271930130749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1742526466338847953420499 2613789699508271930130749)
        ·
          refine ⟨980171137315601973799031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2613789699508271930130749 980171137315601973799031)
          ·
            refine ⟨1470256705973402960698547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 980171137315601973799031 1470256705973402960698547)
            ·
              refine ⟨2205385058960104441047821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1470256705973402960698547 2205385058960104441047821)
              ·
                refine ⟨827019397110039165392933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2205385058960104441047821 827019397110039165392933)
                ·
                  refine ⟨155066136958132343511175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 827019397110039165392933 155066136958132343511175)
                  ·
                    rfl

theorem cell21_679478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 3, 4].length) (baseStart_679478 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_679478 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_679478 prefixEnd_679478 := by exact prefixLift 679478
  have htrace : WordTrace (prefixWord ++ tailWord_679478) baseStart_679478 baseEnd_679478 := by
    simpa [prefixWord, tailWord_679478, baseEnd_679478] using wordTrace_append hprefix tailTrace_679478
  have hstable : (prefixWord ++ tailWord_679478).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679478).length < 2 ^ (prefixWord ++ tailWord_679478).sum := by decide
  have hdescent : baseEnd_679478 < baseStart_679478 := by decide
  rcases family_descends (prefixWord ++ tailWord_679478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679489 : List Nat := [1, 2, 5, 1, 1, 1, 2, 1, 7]
def baseStart_679489 : Nat := 118140960795 + 679489 * 2 ^ 59
def prefixEnd_679489 : Nat := 4983230072969 + 3 ^ 40 * 679489 * 2
def baseEnd_679489 : Nat := 155068647307998768827819

theorem tailTrace_679489 : CollatzResearch.WordTrace tailWord_679489 prefixEnd_679489 155068647307998768827819 := by
  unfold tailWord_679489
  simp only [CollatzResearch.WordTrace]
  refine ⟨24782999835334875327297521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16521999890223250218198347 24782999835334875327297521)
  ·
    refine ⟨18587249876501156495473141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24782999835334875327297521 18587249876501156495473141)
    ·
      refine ⟨1742554675921983421450607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18587249876501156495473141 1742554675921983421450607)
      ·
        refine ⟨2613832013882975132175911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1742554675921983421450607 2613832013882975132175911)
        ·
          refine ⟨3920748020824462698263867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2613832013882975132175911 3920748020824462698263867)
          ·
            refine ⟨5881122031236694047395801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3920748020824462698263867 5881122031236694047395801)
            ·
              refine ⟨4410841523427520535546851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5881122031236694047395801 4410841523427520535546851)
              ·
                refine ⟨6616262285141280803320277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4410841523427520535546851 6616262285141280803320277)
                ·
                  refine ⟨155068647307998768827819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6616262285141280803320277 155068647307998768827819)
                  ·
                    rfl

theorem cell21_679489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 1, 7].length) (baseStart_679489 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_679489 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_679489 prefixEnd_679489 := by exact prefixLift 679489
  have htrace : WordTrace (prefixWord ++ tailWord_679489) baseStart_679489 baseEnd_679489 := by
    simpa [prefixWord, tailWord_679489, baseEnd_679489] using wordTrace_append hprefix tailTrace_679489
  have hstable : (prefixWord ++ tailWord_679489).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679489).length < 2 ^ (prefixWord ++ tailWord_679489).sum := by decide
  have hdescent : baseEnd_679489 < baseStart_679489 := by decide
  rcases family_descends (prefixWord ++ tailWord_679489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679523 : List Nat := [1, 1, 1, 5, 1, 3, 4, 2, 3]
def baseStart_679523 : Nat := 118140960795 + 679523 * 2 ^ 59
def prefixEnd_679523 : Nat := 4983230072969 + 3 ^ 40 * 679523 * 2
def baseEnd_679523 : Nat := 155076406571222265261083

theorem tailTrace_679523 : CollatzResearch.WordTrace tailWord_679523 prefixEnd_679523 155076406571222265261083 := by
  unfold tailWord_679523
  simp only [CollatzResearch.WordTrace]
  refine ⟨24784239917211699134035223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16522826611474466089356815 24784239917211699134035223)
  ·
    refine ⟨37176359875817548701052835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24784239917211699134035223 37176359875817548701052835)
    ·
      refine ⟨55764539813726323051579253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37176359875817548701052835 55764539813726323051579253)
      ·
        refine ⟨5227925607536842786085555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 55764539813726323051579253 5227925607536842786085555)
        ·
          refine ⟨7841888411305264179128333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5227925607536842786085555 7841888411305264179128333)
          ·
            refine ⟨2940708154239474067173125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7841888411305264179128333 2940708154239474067173125)
            ·
              refine ⟨551382778919901387594961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2940708154239474067173125 551382778919901387594961)
              ·
                refine ⟨413537084189926040696221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 551382778919901387594961 413537084189926040696221)
                ·
                  refine ⟨155076406571222265261083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 413537084189926040696221 155076406571222265261083)
                  ·
                    rfl

theorem cell21_679523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 4, 2, 3].length) (baseStart_679523 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_679523 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_679523 prefixEnd_679523 := by exact prefixLift 679523
  have htrace : WordTrace (prefixWord ++ tailWord_679523) baseStart_679523 baseEnd_679523 := by
    simpa [prefixWord, tailWord_679523, baseEnd_679523] using wordTrace_append hprefix tailTrace_679523
  have hstable : (prefixWord ++ tailWord_679523).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679523).length < 2 ^ (prefixWord ++ tailWord_679523).sum := by decide
  have hdescent : baseEnd_679523 < baseStart_679523 := by decide
  rcases family_descends (prefixWord ++ tailWord_679523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679582 : List Nat := [4, 3, 1, 1, 1, 2, 1, 3, 5]
def baseStart_679582 : Nat := 118140960795 + 679582 * 2 ^ 59
def prefixEnd_679582 : Nat := 4983230072969 + 3 ^ 40 * 679582 * 2
def baseEnd_679582 : Nat := 155089871175051273777629

theorem tailTrace_679582 : CollatzResearch.WordTrace tailWord_679582 prefixEnd_679582 155089871175051273777629 := by
  unfold tailWord_679582
  simp only [CollatzResearch.WordTrace]
  refine ⟨3098298977999744026304125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16524261215998634806955333 3098298977999744026304125)
  ·
    refine ⟨1161862116749904009864047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3098298977999744026304125 1161862116749904009864047)
    ·
      refine ⟨1742793175124856014796071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1161862116749904009864047 1742793175124856014796071)
      ·
        refine ⟨2614189762687284022194107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1742793175124856014796071 2614189762687284022194107)
        ·
          refine ⟨3921284644030926033291161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2614189762687284022194107 3921284644030926033291161)
          ·
            refine ⟨2940963483023194524968371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3921284644030926033291161 2940963483023194524968371)
            ·
              refine ⟨4411445224534791787452557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2940963483023194524968371 4411445224534791787452557)
              ·
                refine ⟨1654291959200546920294709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4411445224534791787452557 1654291959200546920294709)
                ·
                  refine ⟨155089871175051273777629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1654291959200546920294709 155089871175051273777629)
                  ·
                    rfl

theorem cell21_679582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_679582 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_679582 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_679582 prefixEnd_679582 := by exact prefixLift 679582
  have htrace : WordTrace (prefixWord ++ tailWord_679582) baseStart_679582 baseEnd_679582 := by
    simpa [prefixWord, tailWord_679582, baseEnd_679582] using wordTrace_append hprefix tailTrace_679582
  have hstable : (prefixWord ++ tailWord_679582).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679582).length < 2 ^ (prefixWord ++ tailWord_679582).sum := by decide
  have hdescent : baseEnd_679582 < baseStart_679582 := by decide
  rcases family_descends (prefixWord ++ tailWord_679582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679610 : List Nat := [3, 1, 1, 1, 2, 5, 1, 7]
def baseStart_679610 : Nat := 118140960795 + 679610 * 2 ^ 59
def prefixEnd_679610 : Nat := 4983230072969 + 3 ^ 40 * 679610 * 2
def baseEnd_679610 : Nat := 51698753718843149103635

theorem tailTrace_679610 : CollatzResearch.WordTrace tailWord_679610 prefixEnd_679610 51698753718843149103635 := by
  unfold tailWord_679610
  simp only [CollatzResearch.WordTrace]
  refine ⟨6196853266974128248113071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16524942045264341994968189 6196853266974128248113071)
  ·
    refine ⟨9295279900461192372169607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6196853266974128248113071 9295279900461192372169607)
    ·
      refine ⟨13942919850691788558254411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9295279900461192372169607 13942919850691788558254411)
      ·
        refine ⟨20914379776037682837381617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13942919850691788558254411 20914379776037682837381617)
        ·
          refine ⟨15685784832028262128036213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20914379776037682837381617 15685784832028262128036213)
          ·
            refine ⟨1470542328002649574503395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15685784832028262128036213 1470542328002649574503395)
            ·
              refine ⟨2205813492003974361755093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1470542328002649574503395 2205813492003974361755093)
              ·
                refine ⟨51698753718843149103635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2205813492003974361755093 51698753718843149103635)
                ·
                  rfl

theorem cell21_679610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 7].length) (baseStart_679610 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_679610 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_679610 prefixEnd_679610 := by exact prefixLift 679610
  have htrace : WordTrace (prefixWord ++ tailWord_679610) baseStart_679610 baseEnd_679610 := by
    simpa [prefixWord, tailWord_679610, baseEnd_679610] using wordTrace_append hprefix tailTrace_679610
  have hstable : (prefixWord ++ tailWord_679610).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679610).length < 2 ^ (prefixWord ++ tailWord_679610).sum := by decide
  have hdescent : baseEnd_679610 < baseStart_679610 := by decide
  rcases family_descends (prefixWord ++ tailWord_679610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679641 : List Nat := [1, 2, 1, 2, 3, 3, 3, 1, 5]
def baseStart_679641 : Nat := 118140960795 + 679641 * 2 ^ 59
def prefixEnd_679641 : Nat := 4983230072969 + 3 ^ 40 * 679641 * 2
def baseEnd_679641 : Nat := 155103335778880282294175

theorem tailTrace_679641 : CollatzResearch.WordTrace tailWord_679641 prefixEnd_679641 155103335778880282294175 := by
  unfold tailWord_679641
  simp only [CollatzResearch.WordTrace]
  refine ⟨24788543730784205286830777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16525695820522803524553851 24788543730784205286830777)
  ·
    refine ⟨18591407798088153965123083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24788543730784205286830777 18591407798088153965123083)
    ·
      refine ⟨27887111697132230947684625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18591407798088153965123083 27887111697132230947684625)
      ·
        refine ⟨20915333772849173210763469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27887111697132230947684625 20915333772849173210763469)
        ·
          refine ⟨7843250164818439954036301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20915333772849173210763469 7843250164818439954036301)
          ·
            refine ⟨2941218811806914982763613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7843250164818439954036301 2941218811806914982763613)
            ·
              refine ⟨1102957054427593118536355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2941218811806914982763613 1102957054427593118536355)
              ·
                refine ⟨1654435581641389677804533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1102957054427593118536355 1654435581641389677804533)
                ·
                  refine ⟨155103335778880282294175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1654435581641389677804533 155103335778880282294175)
                  ·
                    rfl

theorem cell21_679641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 3, 1, 5].length) (baseStart_679641 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_679641 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_679641 prefixEnd_679641 := by exact prefixLift 679641
  have htrace : WordTrace (prefixWord ++ tailWord_679641) baseStart_679641 baseEnd_679641 := by
    simpa [prefixWord, tailWord_679641, baseEnd_679641] using wordTrace_append hprefix tailTrace_679641
  have hstable : (prefixWord ++ tailWord_679641).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679641).length < 2 ^ (prefixWord ++ tailWord_679641).sum := by decide
  have hdescent : baseEnd_679641 < baseStart_679641 := by decide
  rcases family_descends (prefixWord ++ tailWord_679641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679644 : List Nat := [2, 2, 5, 1, 2, 1, 2, 6]
def baseStart_679644 : Nat := 118140960795 + 679644 * 2 ^ 59
def prefixEnd_679644 : Nat := 4983230072969 + 3 ^ 40 * 679644 * 2
def baseEnd_679644 : Nat := 51701340139917647914723

theorem tailTrace_679644 : CollatzResearch.WordTrace tailWord_679644 prefixEnd_679644 51701340139917647914723 := by
  unfold tailWord_679644
  simp only [CollatzResearch.WordTrace]
  refine ⟨12394326574886668399594993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16525768766515557866126657 12394326574886668399594993)
  ·
    refine ⟨9295744931165001299696245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12394326574886668399594993 9295744931165001299696245)
    ·
      refine ⟨871476087296718871846523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9295744931165001299696245 871476087296718871846523)
      ·
        refine ⟨1307214130945078307769785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 871476087296718871846523 1307214130945078307769785)
        ·
          refine ⟨980410598208808730827339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1307214130945078307769785 980410598208808730827339)
          ·
            refine ⟨1470615897313213096241009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 980410598208808730827339 1470615897313213096241009)
            ·
              refine ⟨1102961922984909822180757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1470615897313213096241009 1102961922984909822180757)
              ·
                refine ⟨51701340139917647914723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1102961922984909822180757 51701340139917647914723)
                ·
                  rfl

theorem cell21_679644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 2, 6].length) (baseStart_679644 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_679644 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_679644 prefixEnd_679644 := by exact prefixLift 679644
  have htrace : WordTrace (prefixWord ++ tailWord_679644) baseStart_679644 baseEnd_679644 := by
    simpa [prefixWord, tailWord_679644, baseEnd_679644] using wordTrace_append hprefix tailTrace_679644
  have hstable : (prefixWord ++ tailWord_679644).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679644).length < 2 ^ (prefixWord ++ tailWord_679644).sum := by decide
  have hdescent : baseEnd_679644 < baseStart_679644 := by decide
  rcases family_descends (prefixWord ++ tailWord_679644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679703 : List Nat := [1, 1, 3, 4, 2, 3, 1, 6]
def baseStart_679703 : Nat := 118140960795 + 679703 * 2 ^ 59
def prefixEnd_679703 : Nat := 4983230072969 + 3 ^ 40 * 679703 * 2
def baseEnd_679703 : Nat := 51705828341193984086905

theorem tailTrace_679703 : CollatzResearch.WordTrace tailWord_679703 prefixEnd_679703 51705828341193984086905 := by
  unfold tailWord_679703
  simp only [CollatzResearch.WordTrace]
  refine ⟨24790805056559589875587763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16527203371039726583725175 24790805056559589875587763)
  ·
    refine ⟨37186207584839384813381645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24790805056559589875587763 37186207584839384813381645)
    ·
      refine ⟨13944827844314769305018117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37186207584839384813381645 13944827844314769305018117)
      ·
        refine ⟨2614655220809019244690897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13944827844314769305018117 2614655220809019244690897)
        ·
          refine ⟨1960991415606764433518173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2614655220809019244690897 1960991415606764433518173)
          ·
            refine ⟨735371780852536662569315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1960991415606764433518173 735371780852536662569315)
            ·
              refine ⟨1103057671278804993853973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 735371780852536662569315 1103057671278804993853973)
              ·
                refine ⟨51705828341193984086905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1103057671278804993853973 51705828341193984086905)
                ·
                  rfl

theorem cell21_679703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 1, 6].length) (baseStart_679703 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_679703 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_679703 prefixEnd_679703 := by exact prefixLift 679703
  have htrace : WordTrace (prefixWord ++ tailWord_679703) baseStart_679703 baseEnd_679703 := by
    simpa [prefixWord, tailWord_679703, baseEnd_679703] using wordTrace_append hprefix tailTrace_679703
  have hstable : (prefixWord ++ tailWord_679703).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679703).length < 2 ^ (prefixWord ++ tailWord_679703).sum := by decide
  have hdescent : baseEnd_679703 < baseStart_679703 := by decide
  rcases family_descends (prefixWord ++ tailWord_679703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679717 : List Nat := [1, 3, 1, 2, 3, 3, 1, 2, 5]
def baseStart_679717 : Nat := 118140960795 + 679717 * 2 ^ 59
def prefixEnd_679717 : Nat := 4983230072969 + 3 ^ 40 * 679717 * 2
def baseEnd_679717 : Nat := 155120680014321039027353

theorem tailTrace_679717 : CollatzResearch.WordTrace tailWord_679717 prefixEnd_679717 155120680014321039027353 := by
  unfold tailWord_679717
  simp only [CollatzResearch.WordTrace]
  refine ⟨24791315678508870266597405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16527543785672580177731603 24791315678508870266597405)
  ·
    refine ⟨9296743379440826349974027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24791315678508870266597405 9296743379440826349974027)
    ·
      refine ⟨13945115069161239524961041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9296743379440826349974027 13945115069161239524961041)
      ·
        refine ⟨10458836301870929643720781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13945115069161239524961041 10458836301870929643720781)
        ·
          refine ⟨3922063613201598616395293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10458836301870929643720781 3922063613201598616395293)
          ·
            refine ⟨1470773854950599481148235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3922063613201598616395293 1470773854950599481148235)
            ·
              refine ⟨2206160782425899221722353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1470773854950599481148235 2206160782425899221722353)
              ·
                refine ⟨1654620586819424416291765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2206160782425899221722353 1654620586819424416291765)
                ·
                  refine ⟨155120680014321039027353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1654620586819424416291765 155120680014321039027353)
                  ·
                    rfl

theorem cell21_679717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 2, 5].length) (baseStart_679717 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_679717 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_679717 prefixEnd_679717 := by exact prefixLift 679717
  have htrace : WordTrace (prefixWord ++ tailWord_679717) baseStart_679717 baseEnd_679717 := by
    simpa [prefixWord, tailWord_679717, baseEnd_679717] using wordTrace_append hprefix tailTrace_679717
  have hstable : (prefixWord ++ tailWord_679717).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679717).length < 2 ^ (prefixWord ++ tailWord_679717).sum := by decide
  have hdescent : baseEnd_679717 < baseStart_679717 := by decide
  rcases family_descends (prefixWord ++ tailWord_679717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679765 : List Nat := [1, 3, 2, 2, 2, 3, 3, 1, 4]
def baseStart_679765 : Nat := 118140960795 + 679765 * 2 ^ 59
def prefixEnd_679765 : Nat := 4983230072969 + 3 ^ 40 * 679765 * 2
def baseEnd_679765 : Nat := 155131634268283622227255

theorem tailTrace_679765 : CollatzResearch.WordTrace tailWord_679765 prefixEnd_679765 155131634268283622227255 := by
  unfold tailWord_679765
  simp only [CollatzResearch.WordTrace]
  refine ⟨24793066382334974464344749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16528710921556649642896499 24793066382334974464344749)
  ·
    refine ⟨9297399893375615424129281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24793066382334974464344749 9297399893375615424129281)
    ·
      refine ⟨6973049920031711568096961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9297399893375615424129281 6973049920031711568096961)
      ·
        refine ⟨5229787440023783676072721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6973049920031711568096961 5229787440023783676072721)
        ·
          refine ⟨3922340580017837757054541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5229787440023783676072721 3922340580017837757054541)
          ·
            refine ⟨1470877717506689158895453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3922340580017837757054541 1470877717506689158895453)
            ·
              refine ⟨551579144065008434585795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1470877717506689158895453 551579144065008434585795)
              ·
                refine ⟨827368716097512651878693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 551579144065008434585795 827368716097512651878693)
                ·
                  refine ⟨155131634268283622227255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 827368716097512651878693 155131634268283622227255)
                  ·
                    rfl

theorem cell21_679765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 3, 1, 4].length) (baseStart_679765 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_679765 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_679765 prefixEnd_679765 := by exact prefixLift 679765
  have htrace : WordTrace (prefixWord ++ tailWord_679765) baseStart_679765 baseEnd_679765 := by
    simpa [prefixWord, tailWord_679765, baseEnd_679765] using wordTrace_append hprefix tailTrace_679765
  have hstable : (prefixWord ++ tailWord_679765).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679765).length < 2 ^ (prefixWord ++ tailWord_679765).sum := by decide
  have hdescent : baseEnd_679765 < baseStart_679765 := by decide
  rcases family_descends (prefixWord ++ tailWord_679765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679807 : List Nat := [1, 1, 2, 2, 1, 1, 3, 6, 4]
def baseStart_679807 : Nat := 118140960795 + 679807 * 2 ^ 59
def prefixEnd_679807 : Nat := 4983230072969 + 3 ^ 40 * 679807 * 2
def baseEnd_679807 : Nat := 155141219240500882527169

theorem tailTrace_679807 : CollatzResearch.WordTrace tailWord_679807 prefixEnd_679807 155141219240500882527169 := by
  unfold tailWord_679807
  simp only [CollatzResearch.WordTrace]
  refine ⟨24794598248182815637373675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16529732165455210424915783 24794598248182815637373675)
  ·
    refine ⟨37191897372274223456060513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24794598248182815637373675 37191897372274223456060513)
    ·
      refine ⟨27893923029205667592045385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37191897372274223456060513 27893923029205667592045385)
      ·
        refine ⟨20920442271904250694034039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27893923029205667592045385 20920442271904250694034039)
        ·
          refine ⟨31380663407856376041051059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20920442271904250694034039 31380663407856376041051059)
          ·
            refine ⟨47070995111784564061576589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31380663407856376041051059 47070995111784564061576589)
            ·
              refine ⟨17651623166919211523091221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47070995111784564061576589 17651623166919211523091221)
              ·
                refine ⟨827419835949338040144901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 17651623166919211523091221 827419835949338040144901)
                ·
                  refine ⟨155141219240500882527169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 827419835949338040144901 155141219240500882527169)
                  ·
                    rfl

theorem cell21_679807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 6, 4].length) (baseStart_679807 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_679807 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_679807 prefixEnd_679807 := by exact prefixLift 679807
  have htrace : WordTrace (prefixWord ++ tailWord_679807) baseStart_679807 baseEnd_679807 := by
    simpa [prefixWord, tailWord_679807, baseEnd_679807] using wordTrace_append hprefix tailTrace_679807
  have hstable : (prefixWord ++ tailWord_679807).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679807).length < 2 ^ (prefixWord ++ tailWord_679807).sum := by decide
  have hdescent : baseEnd_679807 < baseStart_679807 := by decide
  rcases family_descends (prefixWord ++ tailWord_679807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679883 : List Nat := [1, 1, 1, 1, 3, 4, 1, 5, 4]
def baseStart_679883 : Nat := 118140960795 + 679883 * 2 ^ 59
def prefixEnd_679883 : Nat := 4983230072969 + 3 ^ 40 * 679883 * 2
def baseEnd_679883 : Nat := 155158563475941639260347

theorem tailTrace_679883 : CollatzResearch.WordTrace tailWord_679883 prefixEnd_679883 155158563475941639260347 := by
  unfold tailWord_679883
  simp only [CollatzResearch.WordTrace]
  refine ⟨24797370195907480617140303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16531580130604987078093535 24797370195907480617140303)
  ·
    refine ⟨37196055293861220925710455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24797370195907480617140303 37196055293861220925710455)
    ·
      refine ⟨55794082940791831388565683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37196055293861220925710455 55794082940791831388565683)
      ·
        refine ⟨83691124411187747082848525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55794082940791831388565683 83691124411187747082848525)
        ·
          refine ⟨31384171654195405156068197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83691124411187747082848525 31384171654195405156068197)
          ·
            refine ⟨5884532185161638466762787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31384171654195405156068197 5884532185161638466762787)
            ·
              refine ⟨8826798277742457700144181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5884532185161638466762787 8826798277742457700144181)
              ·
                refine ⟨827512338538355409388517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8826798277742457700144181 827512338538355409388517)
                ·
                  refine ⟨155158563475941639260347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 827512338538355409388517 155158563475941639260347)
                  ·
                    rfl

theorem cell21_679883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 5, 4].length) (baseStart_679883 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_679883 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_679883 prefixEnd_679883 := by exact prefixLift 679883
  have htrace : WordTrace (prefixWord ++ tailWord_679883) baseStart_679883 baseEnd_679883 := by
    simpa [prefixWord, tailWord_679883, baseEnd_679883] using wordTrace_append hprefix tailTrace_679883
  have hstable : (prefixWord ++ tailWord_679883).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679883).length < 2 ^ (prefixWord ++ tailWord_679883).sum := by decide
  have hdescent : baseEnd_679883 < baseStart_679883 := by decide
  rcases family_descends (prefixWord ++ tailWord_679883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679917 : List Nat := [1, 5, 1, 4, 1, 1, 1, 1, 6]
def baseStart_679917 : Nat := 118140960795 + 679917 * 2 ^ 59
def prefixEnd_679917 : Nat := 4983230072969 + 3 ^ 40 * 679917 * 2
def baseEnd_679917 : Nat := 155166322739165135693611

theorem tailTrace_679917 : CollatzResearch.WordTrace tailWord_679917 prefixEnd_679917 155166322739165135693611 := by
  unfold tailWord_679917
  simp only [CollatzResearch.WordTrace]
  refine ⟨24798610277784304423878005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16532406851856202949252003 24798610277784304423878005)
  ·
    refine ⟨2324869713542278539738563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24798610277784304423878005 2324869713542278539738563)
    ·
      refine ⟨3487304570313417809607845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2324869713542278539738563 3487304570313417809607845)
      ·
        refine ⟨653869606933765839301471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3487304570313417809607845 653869606933765839301471)
        ·
          refine ⟨980804410400648758952207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 653869606933765839301471 980804410400648758952207)
          ·
            refine ⟨1471206615600973138428311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 980804410400648758952207 1471206615600973138428311)
            ·
              refine ⟨2206809923401459707642467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1471206615600973138428311 2206809923401459707642467)
              ·
                refine ⟨3310214885102189561463701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2206809923401459707642467 3310214885102189561463701)
                ·
                  refine ⟨155166322739165135693611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3310214885102189561463701 155166322739165135693611)
                  ·
                    rfl

theorem cell21_679917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 1, 6].length) (baseStart_679917 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_679917 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_679917 prefixEnd_679917 := by exact prefixLift 679917
  have htrace : WordTrace (prefixWord ++ tailWord_679917) baseStart_679917 baseEnd_679917 := by
    simpa [prefixWord, tailWord_679917, baseEnd_679917] using wordTrace_append hprefix tailTrace_679917
  have hstable : (prefixWord ++ tailWord_679917).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679917).length < 2 ^ (prefixWord ++ tailWord_679917).sum := by decide
  have hdescent : baseEnd_679917 < baseStart_679917 := by decide
  rcases family_descends (prefixWord ++ tailWord_679917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679928 : List Nat := [2, 1, 2, 1, 1, 3, 3, 3, 5]
def baseStart_679928 : Nat := 118140960795 + 679928 * 2 ^ 59
def prefixEnd_679928 : Nat := 4983230072969 + 3 ^ 40 * 679928 * 2
def baseEnd_679928 : Nat := 155168833089031561010255

theorem tailTrace_679928 : CollatzResearch.WordTrace tailWord_679928 prefixEnd_679928 155168833089031561010255 := by
  unfold tailWord_679928
  simp only [CollatzResearch.WordTrace]
  refine ⟨12399505740372226651264219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16532674320496302201685625 12399505740372226651264219)
  ·
    refine ⟨18599258610558339976896329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12399505740372226651264219 18599258610558339976896329)
    ·
      refine ⟨13949443957918754982672247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18599258610558339976896329 13949443957918754982672247)
      ·
        refine ⟨20924165936878132474008371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13949443957918754982672247 20924165936878132474008371)
        ·
          refine ⟨31386248905317198711012557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20924165936878132474008371 31386248905317198711012557)
          ·
            refine ⟨11769843339493949516629709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31386248905317198711012557 11769843339493949516629709)
            ·
              refine ⟨4413691252310231068736141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11769843339493949516629709 4413691252310231068736141)
              ·
                refine ⟨1655134219616336650776053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4413691252310231068736141 1655134219616336650776053)
                ·
                  refine ⟨155168833089031561010255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1655134219616336650776053 155168833089031561010255)
                  ·
                    rfl

theorem cell21_679928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 3, 5].length) (baseStart_679928 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_679928 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_679928 prefixEnd_679928 := by exact prefixLift 679928
  have htrace : WordTrace (prefixWord ++ tailWord_679928) baseStart_679928 baseEnd_679928 := by
    simpa [prefixWord, tailWord_679928, baseEnd_679928] using wordTrace_append hprefix tailTrace_679928
  have hstable : (prefixWord ++ tailWord_679928).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679928).length < 2 ^ (prefixWord ++ tailWord_679928).sum := by decide
  have hdescent : baseEnd_679928 < baseStart_679928 := by decide
  rcases family_descends (prefixWord ++ tailWord_679928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679934 : List Nat := [4, 2, 2, 2, 1, 2, 3, 1, 4]
def baseStart_679934 : Nat := 118140960795 + 679934 * 2 ^ 59
def prefixEnd_679934 : Nat := 4983230072969 + 3 ^ 40 * 679934 * 2
def baseEnd_679934 : Nat := 155170202370776883910243

theorem tailTrace_679934 : CollatzResearch.WordTrace tailWord_679934 prefixEnd_679934 155170202370776883910243 := by
  unfold tailWord_679934
  simp only [CollatzResearch.WordTrace]
  refine ⟨3099903789840339540905857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16532820212481810884831237 3099903789840339540905857)
  ·
    refine ⟨2324927842380254655679393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3099903789840339540905857 2324927842380254655679393)
    ·
      refine ⟨1743695881785190991759545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2324927842380254655679393 1743695881785190991759545)
      ·
        refine ⟨1307771911338893243819659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1743695881785190991759545 1307771911338893243819659)
        ·
          refine ⟨1961657867008339865729489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1307771911338893243819659 1961657867008339865729489)
          ·
            refine ⟨1471243400256254899297117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1961657867008339865729489 1471243400256254899297117)
            ·
              refine ⟨551716275096095587236419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1471243400256254899297117 551716275096095587236419)
              ·
                refine ⟨827574412644143380854629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 551716275096095587236419 827574412644143380854629)
                ·
                  refine ⟨155170202370776883910243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 827574412644143380854629 155170202370776883910243)
                  ·
                    rfl

theorem cell21_679934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 3, 1, 4].length) (baseStart_679934 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_679934 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_679934 prefixEnd_679934 := by exact prefixLift 679934
  have htrace : WordTrace (prefixWord ++ tailWord_679934) baseStart_679934 baseEnd_679934 := by
    simpa [prefixWord, tailWord_679934, baseEnd_679934] using wordTrace_append hprefix tailTrace_679934
  have hstable : (prefixWord ++ tailWord_679934).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679934).length < 2 ^ (prefixWord ++ tailWord_679934).sum := by decide
  have hdescent : baseEnd_679934 < baseStart_679934 := by decide
  rcases family_descends (prefixWord ++ tailWord_679934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679962 : List Nat := [3, 1, 1, 3, 1, 3, 3, 3, 3]
def baseStart_679962 : Nat := 118140960795 + 679962 * 2 ^ 59
def prefixEnd_679962 : Nat := 4983230072969 + 3 ^ 40 * 679962 * 2
def baseEnd_679962 : Nat := 155176592352255057443519

theorem tailTrace_679962 : CollatzResearch.WordTrace tailWord_679962 prefixEnd_679962 155176592352255057443519 := by
  unfold tailWord_679962
  simp only [CollatzResearch.WordTrace]
  refine ⟨6200062890655319277316535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16533501041747518072844093 6200062890655319277316535)
  ·
    refine ⟨9300094335982978915974803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6200062890655319277316535 9300094335982978915974803)
    ·
      refine ⟨13950141503974468373962205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9300094335982978915974803 13950141503974468373962205)
      ·
        refine ⟨5231303063990425640235827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13950141503974468373962205 5231303063990425640235827)
        ·
          refine ⟨7846954595985638460353741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5231303063990425640235827 7846954595985638460353741)
          ·
            refine ⟨2942607973494614422632653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7846954595985638460353741 2942607973494614422632653)
            ·
              refine ⟨1103477990060480408487245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2942607973494614422632653 1103477990060480408487245)
              ·
                refine ⟨413804246272680153182717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1103477990060480408487245 413804246272680153182717)
                ·
                  refine ⟨155176592352255057443519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 413804246272680153182717 155176592352255057443519)
                  ·
                    rfl

theorem cell21_679962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 3, 3, 3].length) (baseStart_679962 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_679962 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_679962 prefixEnd_679962 := by exact prefixLift 679962
  have htrace : WordTrace (prefixWord ++ tailWord_679962) baseStart_679962 baseEnd_679962 := by
    simpa [prefixWord, tailWord_679962, baseEnd_679962] using wordTrace_append hprefix tailTrace_679962
  have hstable : (prefixWord ++ tailWord_679962).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679962).length < 2 ^ (prefixWord ++ tailWord_679962).sum := by decide
  have hdescent : baseEnd_679962 < baseStart_679962 := by decide
  rcases family_descends (prefixWord ++ tailWord_679962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679973 : List Nat := [1, 3, 1, 2, 2, 3, 9]
def baseStart_679973 : Nat := 118140960795 + 679973 * 2 ^ 59
def prefixEnd_679973 : Nat := 4983230072969 + 3 ^ 40 * 679973 * 2
def baseEnd_679973 : Nat := 17242122522457942528907

theorem tailTrace_679973 : CollatzResearch.WordTrace tailWord_679973 prefixEnd_679973 17242122522457942528907 := by
  unfold tailWord_679973
  simp only [CollatzResearch.WordTrace]
  refine ⟨24800652765581425987916573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16533768510387617325277715 24800652765581425987916573)
  ·
    refine ⟨9300244787093034745468715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24800652765581425987916573 9300244787093034745468715)
    ·
      refine ⟨13950367180639552118203073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9300244787093034745468715 13950367180639552118203073)
      ·
        refine ⟨10462775385479664088652305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13950367180639552118203073 10462775385479664088652305)
        ·
          refine ⟨7847081539109748066489229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10462775385479664088652305 7847081539109748066489229)
          ·
            refine ⟨2942655577166155524933461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7847081539109748066489229 2942655577166155524933461)
            ·
              refine ⟨17242122522457942528907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2942655577166155524933461 17242122522457942528907)
              ·
                rfl

theorem cell21_679973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 9].length) (baseStart_679973 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_679973 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_679973 prefixEnd_679973 := by exact prefixLift 679973
  have htrace : WordTrace (prefixWord ++ tailWord_679973) baseStart_679973 baseEnd_679973 := by
    simpa [prefixWord, tailWord_679973, baseEnd_679973] using wordTrace_append hprefix tailTrace_679973
  have hstable : (prefixWord ++ tailWord_679973).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679973).length < 2 ^ (prefixWord ++ tailWord_679973).sum := by decide
  have hdescent : baseEnd_679973 < baseStart_679973 := by decide
  rcases family_descends (prefixWord ++ tailWord_679973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680030 : List Nat := [4, 4, 1, 1, 2, 2, 2, 2, 3]
def baseStart_680030 : Nat := 118140960795 + 680030 * 2 ^ 59
def prefixEnd_680030 : Nat := 4983230072969 + 3 ^ 40 * 680030 * 2
def baseEnd_680030 : Nat := 155192110878702050310047

theorem tailTrace_680030 : CollatzResearch.WordTrace tailWord_680030 prefixEnd_680030 155192110878702050310047 := by
  unfold tailWord_680030
  simp only [CollatzResearch.WordTrace]
  refine ⟨3100341465796865590342693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16535154484249949815161029 3100341465796865590342693)
  ·
    refine ⟨581314024836912298189255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3100341465796865590342693 581314024836912298189255)
    ·
      refine ⟨871971037255368447283883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 581314024836912298189255 871971037255368447283883)
      ·
        refine ⟨1307956555883052670925825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 871971037255368447283883 1307956555883052670925825)
        ·
          refine ⟨980967416912289503194369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1307956555883052670925825 980967416912289503194369)
          ·
            refine ⟨735725562684217127395777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 980967416912289503194369 735725562684217127395777)
            ·
              refine ⟨551794172013162845546833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 735725562684217127395777 551794172013162845546833)
              ·
                refine ⟨413845629009872134160125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 551794172013162845546833 413845629009872134160125)
                ·
                  refine ⟨155192110878702050310047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 413845629009872134160125 155192110878702050310047)
                  ·
                    rfl

theorem cell21_680030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_680030 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_680030 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_680030 prefixEnd_680030 := by exact prefixLift 680030
  have htrace : WordTrace (prefixWord ++ tailWord_680030) baseStart_680030 baseEnd_680030 := by
    simpa [prefixWord, tailWord_680030, baseEnd_680030] using wordTrace_append hprefix tailTrace_680030
  have hstable : (prefixWord ++ tailWord_680030).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680030).length < 2 ^ (prefixWord ++ tailWord_680030).sum := by decide
  have hdescent : baseEnd_680030 < baseStart_680030 := by decide
  rcases family_descends (prefixWord ++ tailWord_680030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680035 : List Nat := [1, 1, 1, 5, 1, 1, 3, 4, 4]
def baseStart_680035 : Nat := 118140960795 + 680035 * 2 ^ 59
def prefixEnd_680035 : Nat := 4983230072969 + 3 ^ 40 * 680035 * 2
def baseEnd_680035 : Nat := 155193251946823152726703

theorem tailTrace_680035 : CollatzResearch.WordTrace tailWord_680035 prefixEnd_680035 155193251946823152726703 := by
  unfold tailWord_680035
  simp only [CollatzResearch.WordTrace]
  refine ⟨24802914091356810576673559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16535276060904540384449039 24802914091356810576673559)
  ·
    refine ⟨37204371137035215865010339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24802914091356810576673559 37204371137035215865010339)
    ·
      refine ⟨55806556705552823797515509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37204371137035215865010339 55806556705552823797515509)
      ·
        refine ⟨5231864691145577231017079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 55806556705552823797515509 5231864691145577231017079)
        ·
          refine ⟨7847797036718365846525619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5231864691145577231017079 7847797036718365846525619)
          ·
            refine ⟨11771695555077548769788429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7847797036718365846525619 11771695555077548769788429)
            ·
              refine ⟨4414385833154080788670661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11771695555077548769788429 4414385833154080788670661)
              ·
                refine ⟨827697343716390147875749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4414385833154080788670661 827697343716390147875749)
                ·
                  refine ⟨155193251946823152726703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 827697343716390147875749 155193251946823152726703)
                  ·
                    rfl

theorem cell21_680035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 4, 4].length) (baseStart_680035 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_680035 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_680035 prefixEnd_680035 := by exact prefixLift 680035
  have htrace : WordTrace (prefixWord ++ tailWord_680035) baseStart_680035 baseEnd_680035 := by
    simpa [prefixWord, tailWord_680035, baseEnd_680035] using wordTrace_append hprefix tailTrace_680035
  have hstable : (prefixWord ++ tailWord_680035).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680035).length < 2 ^ (prefixWord ++ tailWord_680035).sum := by decide
  have hdescent : baseEnd_680035 < baseStart_680035 := by decide
  rcases family_descends (prefixWord ++ tailWord_680035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680097 : List Nat := [1, 2, 3, 3, 1, 3, 2, 1, 5]
def baseStart_680097 : Nat := 118140960795 + 680097 * 2 ^ 59
def prefixEnd_680097 : Nat := 4983230072969 + 3 ^ 40 * 680097 * 2
def baseEnd_680097 : Nat := 155207401191524822693243

theorem tailTrace_680097 : CollatzResearch.WordTrace tailWord_680097 prefixEnd_680097 155207401191524822693243 := by
  unfold tailWord_680097
  simp only [CollatzResearch.WordTrace]
  refine ⟨24805175417132195165430545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16536783611421463443620363 24805175417132195165430545)
  ·
    refine ⟨18603881562849146374072909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24805175417132195165430545 18603881562849146374072909)
    ·
      refine ⟨6976455586068429890277341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18603881562849146374072909 6976455586068429890277341)
      ·
        refine ⟨2616170844775661208854003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6976455586068429890277341 2616170844775661208854003)
        ·
          refine ⟨3924256267163491813281005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2616170844775661208854003 3924256267163491813281005)
          ·
            refine ⟨1471596100186309429980377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3924256267163491813281005 1471596100186309429980377)
            ·
              refine ⟨1103697075139732072485283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1471596100186309429980377 1103697075139732072485283)
              ·
                refine ⟨1655545612709598108727925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1103697075139732072485283 1655545612709598108727925)
                ·
                  refine ⟨155207401191524822693243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1655545612709598108727925 155207401191524822693243)
                  ·
                    rfl

theorem cell21_680097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 2, 1, 5].length) (baseStart_680097 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_680097 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_680097 prefixEnd_680097 := by exact prefixLift 680097
  have htrace : WordTrace (prefixWord ++ tailWord_680097) baseStart_680097 baseEnd_680097 := by
    simpa [prefixWord, tailWord_680097, baseEnd_680097] using wordTrace_append hprefix tailTrace_680097
  have hstable : (prefixWord ++ tailWord_680097).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680097).length < 2 ^ (prefixWord ++ tailWord_680097).sum := by decide
  have hdescent : baseEnd_680097 < baseStart_680097 := by decide
  rcases family_descends (prefixWord ++ tailWord_680097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680117 : List Nat := [1, 3, 3, 4, 2, 1, 2, 5]
def baseStart_680117 : Nat := 118140960795 + 680117 * 2 ^ 59
def prefixEnd_680117 : Nat := 4983230072969 + 3 ^ 40 * 680117 * 2
def baseEnd_680117 : Nat := 51737321821336410786623

theorem tailTrace_680117 : CollatzResearch.WordTrace tailWord_680117 prefixEnd_680117 51737321821336410786623 := by
  unfold tailWord_680117
  simp only [CollatzResearch.WordTrace]
  refine ⟨24805904877059738581158605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16537269918039825720772403 24805904877059738581158605)
  ·
    refine ⟨9302214328897401967934477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24805904877059738581158605 9302214328897401967934477)
    ·
      refine ⟨3488330373336525737975429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9302214328897401967934477 3488330373336525737975429)
      ·
        refine ⟨654061945000598575870393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3488330373336525737975429 654061945000598575870393)
        ·
          refine ⟨490546458750448931902795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 654061945000598575870393 490546458750448931902795)
          ·
            refine ⟨735819688125673397854193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 490546458750448931902795 735819688125673397854193)
            ·
              refine ⟨551864766094255048390645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 735819688125673397854193 551864766094255048390645)
              ·
                refine ⟨51737321821336410786623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 551864766094255048390645 51737321821336410786623)
                ·
                  rfl

theorem cell21_680117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 2, 5].length) (baseStart_680117 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_680117 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_680117 prefixEnd_680117 := by exact prefixLift 680117
  have htrace : WordTrace (prefixWord ++ tailWord_680117) baseStart_680117 baseEnd_680117 := by
    simpa [prefixWord, tailWord_680117, baseEnd_680117] using wordTrace_append hprefix tailTrace_680117
  have hstable : (prefixWord ++ tailWord_680117).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680117).length < 2 ^ (prefixWord ++ tailWord_680117).sum := by decide
  have hdescent : baseEnd_680117 < baseStart_680117 := by decide
  rcases family_descends (prefixWord ++ tailWord_680117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680142 : List Nat := [4, 1, 1, 1, 4, 3, 7]
def baseStart_680142 : Nat := 118140960795 + 680142 * 2 ^ 59
def prefixEnd_680142 : Nat := 4983230072969 + 3 ^ 40 * 680142 * 2
def baseEnd_680142 : Nat := 17246407867179416049239

theorem tailTrace_680142 : CollatzResearch.WordTrace tailWord_680142 prefixEnd_680142 17246407867179416049239 := by
  unfold tailWord_680142
  simp only [CollatzResearch.WordTrace]
  refine ⟨3100852087746145981352335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16537877801312778567212453 3100852087746145981352335)
  ·
    refine ⟨4651278131619218972028503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3100852087746145981352335 4651278131619218972028503)
    ·
      refine ⟨6976917197428828458042755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4651278131619218972028503 6976917197428828458042755)
      ·
        refine ⟨10465375796143242687064133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6976917197428828458042755 10465375796143242687064133)
        ·
          refine ⟨1962257961776858003824525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10465375796143242687064133 1962257961776858003824525)
          ·
            refine ⟨735846735666321751434197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1962257961776858003824525 735846735666321751434197)
            ·
              refine ⟨17246407867179416049239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 735846735666321751434197 17246407867179416049239)
              ·
                rfl

theorem cell21_680142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 7].length) (baseStart_680142 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_680142 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_680142 prefixEnd_680142 := by exact prefixLift 680142
  have htrace : WordTrace (prefixWord ++ tailWord_680142) baseStart_680142 baseEnd_680142 := by
    simpa [prefixWord, tailWord_680142, baseEnd_680142] using wordTrace_append hprefix tailTrace_680142
  have hstable : (prefixWord ++ tailWord_680142).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680142).length < 2 ^ (prefixWord ++ tailWord_680142).sum := by decide
  have hdescent : baseEnd_680142 < baseStart_680142 := by decide
  rcases family_descends (prefixWord ++ tailWord_680142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680190 : List Nat := [4, 2, 2, 1, 1, 1, 2, 5, 3]
def baseStart_680190 : Nat := 118140960795 + 680190 * 2 ^ 59
def prefixEnd_680190 : Nat := 4983230072969 + 3 ^ 40 * 680190 * 2
def baseEnd_680190 : Nat := 155228625058577327643053

theorem tailTrace_680190 : CollatzResearch.WordTrace tailWord_680190 prefixEnd_680190 155228625058577327643053 := by
  unfold tailWord_680190
  simp only [CollatzResearch.WordTrace]
  refine ⟨3101070925724409006070753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16539044937196848032377349 3101070925724409006070753)
  ·
    refine ⟨2325803194293306754553065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3101070925724409006070753 2325803194293306754553065)
    ·
      refine ⟨1744352395719980065914799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2325803194293306754553065 1744352395719980065914799)
      ·
        refine ⟨2616528593579970098872199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1744352395719980065914799 2616528593579970098872199)
        ·
          refine ⟨3924792890369955148308299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2616528593579970098872199 3924792890369955148308299)
          ·
            refine ⟨5887189335554932722462449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3924792890369955148308299 5887189335554932722462449)
            ·
              refine ⟨4415392001666199541846837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5887189335554932722462449 4415392001666199541846837)
              ·
                refine ⟨413943000156206207048141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4415392001666199541846837 413943000156206207048141)
                ·
                  refine ⟨155228625058577327643053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 413943000156206207048141 155228625058577327643053)
                  ·
                    rfl

theorem cell21_680190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 5, 3].length) (baseStart_680190 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_680190 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_680190 prefixEnd_680190 := by exact prefixLift 680190
  have htrace : WordTrace (prefixWord ++ tailWord_680190) baseStart_680190 baseEnd_680190 := by
    simpa [prefixWord, tailWord_680190, baseEnd_680190] using wordTrace_append hprefix tailTrace_680190
  have hstable : (prefixWord ++ tailWord_680190).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680190).length < 2 ^ (prefixWord ++ tailWord_680190).sum := by decide
  have hdescent : baseEnd_680190 < baseStart_680190 := by decide
  rcases family_descends (prefixWord ++ tailWord_680190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680398 : List Nat := [4, 1, 1, 1, 2, 1, 1, 2, 8]
def baseStart_680398 : Nat := 118140960795 + 680398 * 2 ^ 59
def prefixEnd_680398 : Nat := 4983230072969 + 3 ^ 40 * 680398 * 2
def baseEnd_680398 : Nat := 155276093492415188175961

theorem tailTrace_680398 : CollatzResearch.WordTrace tailWord_680398 prefixEnd_680398 155276093492415188175961 := by
  unfold tailWord_680398
  simp only [CollatzResearch.WordTrace]
  refine ⟨3102019223630215446517231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16544102526027815714758565 3102019223630215446517231)
  ·
    refine ⟨4653028835445323169775847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3102019223630215446517231 4653028835445323169775847)
    ·
      refine ⟨6979543253167984754663771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4653028835445323169775847 6979543253167984754663771)
      ·
        refine ⟨10469314879751977131995657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6979543253167984754663771 10469314879751977131995657)
        ·
          refine ⟨7851986159813982848996743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10469314879751977131995657 7851986159813982848996743)
          ·
            refine ⟨11777979239720974273495115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7851986159813982848996743 11777979239720974273495115)
            ·
              refine ⟨17666968859581461410242673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11777979239720974273495115 17666968859581461410242673)
              ·
                refine ⟨13250226644686096057682005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17666968859581461410242673 13250226644686096057682005)
                ·
                  refine ⟨155276093492415188175961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13250226644686096057682005 155276093492415188175961)
                  ·
                    rfl

theorem cell21_680398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 2, 8].length) (baseStart_680398 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_680398 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_680398 prefixEnd_680398 := by exact prefixLift 680398
  have htrace : WordTrace (prefixWord ++ tailWord_680398) baseStart_680398 baseEnd_680398 := by
    simpa [prefixWord, tailWord_680398, baseEnd_680398] using wordTrace_append hprefix tailTrace_680398
  have hstable : (prefixWord ++ tailWord_680398).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680398).length < 2 ^ (prefixWord ++ tailWord_680398).sum := by decide
  have hdescent : baseEnd_680398 < baseStart_680398 := by decide
  rcases family_descends (prefixWord ++ tailWord_680398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680460 : List Nat := [2, 2, 1, 2, 4, 1, 2, 2, 5]
def baseStart_680460 : Nat := 118140960795 + 680460 * 2 ^ 59
def prefixEnd_680460 : Nat := 4983230072969 + 3 ^ 40 * 680460 * 2
def baseEnd_680460 : Nat := 155290242737116858142501

theorem tailTrace_680460 : CollatzResearch.WordTrace tailWord_680460 prefixEnd_680460 155290242737116858142501 := by
  unfold tailWord_680460
  simp only [CollatzResearch.WordTrace]
  refine ⟨12409207557408554080447417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16545610076544738773929889 12409207557408554080447417)
  ·
    refine ⟨9306905668056415560335563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12409207557408554080447417 9306905668056415560335563)
    ·
      refine ⟨13960358502084623340503345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9306905668056415560335563 13960358502084623340503345)
      ·
        refine ⟨10470268876563467505377509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13960358502084623340503345 10470268876563467505377509)
        ·
          refine ⟨1963175414355650157258283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10470268876563467505377509 1963175414355650157258283)
          ·
            refine ⟨2944763121533475235887425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1963175414355650157258283 2944763121533475235887425)
            ·
              refine ⟨2208572341150106426915569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2944763121533475235887425 2208572341150106426915569)
              ·
                refine ⟨1656429255862579820186677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2208572341150106426915569 1656429255862579820186677)
                ·
                  refine ⟨155290242737116858142501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1656429255862579820186677 155290242737116858142501)
                  ·
                    rfl

theorem cell21_680460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 2, 5].length) (baseStart_680460 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_680460 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_680460 prefixEnd_680460 := by exact prefixLift 680460
  have htrace : WordTrace (prefixWord ++ tailWord_680460) baseStart_680460 baseEnd_680460 := by
    simpa [prefixWord, tailWord_680460, baseEnd_680460] using wordTrace_append hprefix tailTrace_680460
  have hstable : (prefixWord ++ tailWord_680460).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680460).length < 2 ^ (prefixWord ++ tailWord_680460).sum := by decide
  have hdescent : baseEnd_680460 < baseStart_680460 := by decide
  rcases family_descends (prefixWord ++ tailWord_680460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680474 : List Nat := [3, 1, 1, 3, 1, 1, 3, 2, 6]
def baseStart_680474 : Nat := 118140960795 + 680474 * 2 ^ 59
def prefixEnd_680474 : Nat := 4983230072969 + 3 ^ 40 * 680474 * 2
def baseEnd_680474 : Nat := 155293437727855944909139

theorem tailTrace_680474 : CollatzResearch.WordTrace tailWord_680474 prefixEnd_680474 155293437727855944909139 := by
  unfold tailWord_680474
  simp only [CollatzResearch.WordTrace]
  refine ⟨6204731434191597137976119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16545950491177592367936317 6204731434191597137976119)
  ·
    refine ⟨9307097151287395706964179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6204731434191597137976119 9307097151287395706964179)
    ·
      refine ⟨13960645726931093560446269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9307097151287395706964179 13960645726931093560446269)
      ·
        refine ⟨5235242147599160085167351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13960645726931093560446269 5235242147599160085167351)
        ·
          refine ⟨7852863221398740127751027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5235242147599160085167351 7852863221398740127751027)
          ·
            refine ⟨11779294832098110191626541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7852863221398740127751027 11779294832098110191626541)
            ·
              refine ⟨4417235562036791321859953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11779294832098110191626541 4417235562036791321859953)
              ·
                refine ⟨3312926671527593491394965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4417235562036791321859953 3312926671527593491394965)
                ·
                  refine ⟨155293437727855944909139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3312926671527593491394965 155293437727855944909139)
                  ·
                    rfl

theorem cell21_680474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 2, 6].length) (baseStart_680474 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_680474 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_680474 prefixEnd_680474 := by exact prefixLift 680474
  have htrace : WordTrace (prefixWord ++ tailWord_680474) baseStart_680474 baseEnd_680474 := by
    simpa [prefixWord, tailWord_680474, baseEnd_680474] using wordTrace_append hprefix tailTrace_680474
  have hstable : (prefixWord ++ tailWord_680474).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680474).length < 2 ^ (prefixWord ++ tailWord_680474).sum := by decide
  have hdescent : baseEnd_680474 < baseStart_680474 := by decide
  rcases family_descends (prefixWord ++ tailWord_680474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680494 : List Nat := [4, 1, 3, 1, 3, 2, 1, 1, 5]
def baseStart_680494 : Nat := 118140960795 + 680494 * 2 ^ 59
def prefixEnd_680494 : Nat := 4983230072969 + 3 ^ 40 * 680494 * 2
def baseEnd_680494 : Nat := 155298002000340354575765

theorem tailTrace_680494 : CollatzResearch.WordTrace tailWord_680494 prefixEnd_680494 155298002000340354575765 := by
  unfold tailWord_680494
  simp only [CollatzResearch.WordTrace]
  refine ⟨3102456899586741495954067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16546436797795954645088357 3102456899586741495954067)
  ·
    refine ⟨4653685349380112243931101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3102456899586741495954067 4653685349380112243931101)
    ·
      refine ⟨1745132006017542091474163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4653685349380112243931101 1745132006017542091474163)
      ·
        refine ⟨2617698009026313137211245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1745132006017542091474163 2617698009026313137211245)
        ·
          refine ⟨981636753384867426454217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2617698009026313137211245 981636753384867426454217)
          ·
            refine ⟨736227565038650569840663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 981636753384867426454217 736227565038650569840663)
            ·
              refine ⟨1104341347557975854760995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 736227565038650569840663 1104341347557975854760995)
              ·
                refine ⟨1656512021336963782141493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1104341347557975854760995 1656512021336963782141493)
                ·
                  refine ⟨155298002000340354575765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1656512021336963782141493 155298002000340354575765)
                  ·
                    rfl

theorem cell21_680494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 1, 1, 5].length) (baseStart_680494 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_680494 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_680494 prefixEnd_680494 := by exact prefixLift 680494
  have htrace : WordTrace (prefixWord ++ tailWord_680494) baseStart_680494 baseEnd_680494 := by
    simpa [prefixWord, tailWord_680494, baseEnd_680494] using wordTrace_append hprefix tailTrace_680494
  have hstable : (prefixWord ++ tailWord_680494).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680494).length < 2 ^ (prefixWord ++ tailWord_680494).sum := by decide
  have hdescent : baseEnd_680494 < baseStart_680494 := by decide
  rcases family_descends (prefixWord ++ tailWord_680494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680505 : List Nat := [1, 2, 1, 5, 1, 1, 4, 6]
def baseStart_680505 : Nat := 118140960795 + 680505 * 2 ^ 59
def prefixEnd_680505 : Nat := 4983230072969 + 3 ^ 40 * 680505 * 2
def baseEnd_680505 : Nat := 51766837450068926630803

theorem tailTrace_680505 : CollatzResearch.WordTrace tailWord_680505 prefixEnd_680505 51766837450068926630803 := by
  unfold tailWord_680505
  simp only [CollatzResearch.WordTrace]
  refine ⟨24820056399654080846282969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16546704266436053897521979 24820056399654080846282969)
  ·
    refine ⟨18615042299740560634712227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24820056399654080846282969 18615042299740560634712227)
    ·
      refine ⟨27922563449610840952068341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18615042299740560634712227 27922563449610840952068341)
      ·
        refine ⟨2617740323401016339256407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 27922563449610840952068341 2617740323401016339256407)
        ·
          refine ⟨3926610485101524508884611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2617740323401016339256407 3926610485101524508884611)
          ·
            refine ⟨5889915727652286763326917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3926610485101524508884611 5889915727652286763326917)
            ·
              refine ⟨1104359198934803768123797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5889915727652286763326917 1104359198934803768123797)
              ·
                refine ⟨51766837450068926630803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1104359198934803768123797 51766837450068926630803)
                ·
                  rfl

theorem cell21_680505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 4, 6].length) (baseStart_680505 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_680505 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_680505 prefixEnd_680505 := by exact prefixLift 680505
  have htrace : WordTrace (prefixWord ++ tailWord_680505) baseStart_680505 baseEnd_680505 := by
    simpa [prefixWord, tailWord_680505, baseEnd_680505] using wordTrace_append hprefix tailTrace_680505
  have hstable : (prefixWord ++ tailWord_680505).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680505).length < 2 ^ (prefixWord ++ tailWord_680505).sum := by decide
  have hdescent : baseEnd_680505 < baseStart_680505 := by decide
  rcases family_descends (prefixWord ++ tailWord_680505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680508 : List Nat := [2, 2, 2, 2, 3, 1, 4, 1, 4]
def baseStart_680508 : Nat := 118140960795 + 680508 * 2 ^ 59
def prefixEnd_680508 : Nat := 4983230072969 + 3 ^ 40 * 680508 * 2
def baseEnd_680508 : Nat := 155301196991079441342403

theorem tailTrace_680508 : CollatzResearch.WordTrace tailWord_680508 prefixEnd_680508 155301196991079441342403 := by
  unfold tailWord_680508
  simp only [CollatzResearch.WordTrace]
  refine ⟨12410082909321606179321089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16546777212428808239094785 12410082909321606179321089)
  ·
    refine ⟨9307562181991204634490817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12410082909321606179321089 9307562181991204634490817)
    ·
      refine ⟨6980671636493403475868113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9307562181991204634490817 6980671636493403475868113)
      ·
        refine ⟨5235503727370052606901085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6980671636493403475868113 5235503727370052606901085)
        ·
          refine ⟨1963313897763769727587907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5235503727370052606901085 1963313897763769727587907)
          ·
            refine ⟨2944970846645654591381861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1963313897763769727587907 2944970846645654591381861)
            ·
              refine ⟨552182033746060235884099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2944970846645654591381861 552182033746060235884099)
              ·
                refine ⟨828273050619090353826149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 552182033746060235884099 828273050619090353826149)
                ·
                  refine ⟨155301196991079441342403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 828273050619090353826149 155301196991079441342403)
                  ·
                    rfl

theorem cell21_680508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 4, 1, 4].length) (baseStart_680508 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_680508 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_680508 prefixEnd_680508 := by exact prefixLift 680508
  have htrace : WordTrace (prefixWord ++ tailWord_680508) baseStart_680508 baseEnd_680508 := by
    simpa [prefixWord, tailWord_680508, baseEnd_680508] using wordTrace_append hprefix tailTrace_680508
  have hstable : (prefixWord ++ tailWord_680508).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680508).length < 2 ^ (prefixWord ++ tailWord_680508).sum := by decide
  have hdescent : baseEnd_680508 < baseStart_680508 := by decide
  rcases family_descends (prefixWord ++ tailWord_680508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680612 : List Nat := [2, 3, 1, 2, 2, 1, 4, 1, 5]
def baseStart_680612 : Nat := 118140960795 + 680612 * 2 ^ 59
def prefixEnd_680612 : Nat := 4983230072969 + 3 ^ 40 * 680612 * 2
def baseEnd_680612 : Nat := 155324931207998371608857

theorem tailTrace_680612 : CollatzResearch.WordTrace tailWord_680612 prefixEnd_680612 155324931207998371608857 := by
  unfold tailWord_680612
  simp only [CollatzResearch.WordTrace]
  refine ⟨12411979505133219060214045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16549306006844292080285393 12411979505133219060214045)
  ·
    refine ⟨4654492314424957147580267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12411979505133219060214045 4654492314424957147580267)
    ·
      refine ⟨6981738471637435721370401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4654492314424957147580267 6981738471637435721370401)
      ·
        refine ⟨5236303853728076791027801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6981738471637435721370401 5236303853728076791027801)
        ·
          refine ⟨3927227890296057593270851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5236303853728076791027801 3927227890296057593270851)
          ·
            refine ⟨5890841835444086389906277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3927227890296057593270851 5890841835444086389906277)
            ·
              refine ⟨1104532844145766198107427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5890841835444086389906277 1104532844145766198107427)
              ·
                refine ⟨1656799266218649297161141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1104532844145766198107427 1656799266218649297161141)
                ·
                  refine ⟨155324931207998371608857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1656799266218649297161141 155324931207998371608857)
                  ·
                    rfl

theorem cell21_680612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 4, 1, 5].length) (baseStart_680612 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_680612 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_680612 prefixEnd_680612 := by exact prefixLift 680612
  have htrace : WordTrace (prefixWord ++ tailWord_680612) baseStart_680612 baseEnd_680612 := by
    simpa [prefixWord, tailWord_680612, baseEnd_680612] using wordTrace_append hprefix tailTrace_680612
  have hstable : (prefixWord ++ tailWord_680612).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680612).length < 2 ^ (prefixWord ++ tailWord_680612).sum := by decide
  have hdescent : baseEnd_680612 < baseStart_680612 := by decide
  rcases family_descends (prefixWord ++ tailWord_680612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680618 : List Nat := [3, 1, 5, 2, 1, 1, 3, 1, 4]
def baseStart_680618 : Nat := 118140960795 + 680618 * 2 ^ 59
def prefixEnd_680618 : Nat := 4983230072969 + 3 ^ 40 * 680618 * 2
def baseEnd_680618 : Nat := 155326300489743694508845

theorem tailTrace_680618 : CollatzResearch.WordTrace tailWord_680618 prefixEnd_680618 155326300489743694508845 := by
  unfold tailWord_680618
  simp only [CollatzResearch.WordTrace]
  refine ⟨6206044462061175286286627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16549451898829800763431005 6206044462061175286286627)
  ·
    refine ⟨9309066693091762929429941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6206044462061175286286627 9309066693091762929429941)
    ·
      refine ⟨872725002477352774634057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9309066693091762929429941 872725002477352774634057)
      ·
        refine ⟨654543751858014580975543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 872725002477352774634057 654543751858014580975543)
        ·
          refine ⟨981815627787021871463315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 654543751858014580975543 981815627787021871463315)
          ·
            refine ⟨1472723441680532807194973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 981815627787021871463315 1472723441680532807194973)
            ·
              refine ⟨552271290630199802698115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1472723441680532807194973 552271290630199802698115)
              ·
                refine ⟨828406935945299704047173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 552271290630199802698115 828406935945299704047173)
                ·
                  refine ⟨155326300489743694508845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 828406935945299704047173 155326300489743694508845)
                  ·
                    rfl

theorem cell21_680618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 3, 1, 4].length) (baseStart_680618 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_680618 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_680618 prefixEnd_680618 := by exact prefixLift 680618
  have htrace : WordTrace (prefixWord ++ tailWord_680618) baseStart_680618 baseEnd_680618 := by
    simpa [prefixWord, tailWord_680618, baseEnd_680618] using wordTrace_append hprefix tailTrace_680618
  have hstable : (prefixWord ++ tailWord_680618).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680618).length < 2 ^ (prefixWord ++ tailWord_680618).sum := by decide
  have hdescent : baseEnd_680618 < baseStart_680618 := by decide
  rcases family_descends (prefixWord ++ tailWord_680618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680778 : List Nat := [3, 1, 2, 1, 1, 1, 2, 6, 4]
def baseStart_680778 : Nat := 118140960795 + 680778 * 2 ^ 59
def prefixEnd_680778 : Nat := 4983230072969 + 3 ^ 40 * 680778 * 2
def baseEnd_680778 : Nat := 155362814669618971841851

theorem tailTrace_680778 : CollatzResearch.WordTrace tailWord_680778 prefixEnd_680778 155362814669618971841851 := by
  unfold tailWord_680778
  simp only [CollatzResearch.WordTrace]
  refine ⟨6207503381916262117742747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16553342351776698980647325 6207503381916262117742747)
  ·
    refine ⟨9311255072874393176614121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6207503381916262117742747 9311255072874393176614121)
    ·
      refine ⟨6983441304655794882460591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9311255072874393176614121 6983441304655794882460591)
      ·
        refine ⟨10475161956983692323690887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6983441304655794882460591 10475161956983692323690887)
        ·
          refine ⟨15712742935475538485536331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10475161956983692323690887 15712742935475538485536331)
          ·
            refine ⟨23569114403213307728304497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15712742935475538485536331 23569114403213307728304497)
            ·
              refine ⟨17676835802409980796228373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23569114403213307728304497 17676835802409980796228373)
              ·
                refine ⟨828601678237967849823205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 17676835802409980796228373 828601678237967849823205)
                ·
                  refine ⟨155362814669618971841851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 828601678237967849823205 155362814669618971841851)
                  ·
                    rfl

theorem cell21_680778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 6, 4].length) (baseStart_680778 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_680778 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_680778 prefixEnd_680778 := by exact prefixLift 680778
  have htrace : WordTrace (prefixWord ++ tailWord_680778) baseStart_680778 baseEnd_680778 := by
    simpa [prefixWord, tailWord_680778, baseEnd_680778] using wordTrace_append hprefix tailTrace_680778
  have hstable : (prefixWord ++ tailWord_680778).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680778).length < 2 ^ (prefixWord ++ tailWord_680778).sum := by decide
  have hdescent : baseEnd_680778 < baseStart_680778 := by decide
  rcases family_descends (prefixWord ++ tailWord_680778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680840 : List Nat := [2, 1, 3, 3, 2, 1, 3, 1, 5]
def baseStart_680840 : Nat := 118140960795 + 680840 * 2 ^ 59
def prefixEnd_680840 : Nat := 4983230072969 + 3 ^ 40 * 680840 * 2
def baseEnd_680840 : Nat := 155376963914320641808391

theorem tailTrace_680840 : CollatzResearch.WordTrace tailWord_680840 prefixEnd_680840 155376963914320641808391 := by
  unfold tailWord_680840
  simp only [CollatzResearch.WordTrace]
  refine ⟨12416137426720216529863987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16554849902293622039818649 12416137426720216529863987)
  ·
    refine ⟨18624206140080324794795981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12416137426720216529863987 18624206140080324794795981)
    ·
      refine ⟨6984077302530121798048493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18624206140080324794795981 6984077302530121798048493)
      ·
        refine ⟨2619028988448795674268185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6984077302530121798048493 2619028988448795674268185)
        ·
          refine ⟨1964271741336596755701139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2619028988448795674268185 1964271741336596755701139)
          ·
            refine ⟨2946407612004895133551709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1964271741336596755701139 2946407612004895133551709)
            ·
              refine ⟨1104902854501835675081891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2946407612004895133551709 1104902854501835675081891)
              ·
                refine ⟨1657354281752753512622837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1104902854501835675081891 1657354281752753512622837)
                ·
                  refine ⟨155376963914320641808391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1657354281752753512622837 155376963914320641808391)
                  ·
                    rfl

theorem cell21_680840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 3, 1, 5].length) (baseStart_680840 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_680840 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_680840 prefixEnd_680840 := by exact prefixLift 680840
  have htrace : WordTrace (prefixWord ++ tailWord_680840) baseStart_680840 baseEnd_680840 := by
    simpa [prefixWord, tailWord_680840, baseEnd_680840] using wordTrace_append hprefix tailTrace_680840
  have hstable : (prefixWord ++ tailWord_680840).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680840).length < 2 ^ (prefixWord ++ tailWord_680840).sum := by decide
  have hdescent : baseEnd_680840 < baseStart_680840 := by decide
  rcases family_descends (prefixWord ++ tailWord_680840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680868 : List Nat := [2, 3, 1, 2, 1, 2, 1, 9]
def baseStart_680868 : Nat := 118140960795 + 680868 * 2 ^ 59
def prefixEnd_680868 : Nat := 4983230072969 + 3 ^ 40 * 680868 * 2
def baseEnd_680868 : Nat := 51794451298599605113889

theorem tailTrace_680868 : CollatzResearch.WordTrace tailWord_680868 prefixEnd_680868 51794451298599605113889 := by
  unfold tailWord_680868
  simp only [CollatzResearch.WordTrace]
  refine ⟨12416648048669496920873629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16555530731559329227831505 12416648048669496920873629)
  ·
    refine ⟨4656243018251061345327611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12416648048669496920873629 4656243018251061345327611)
    ·
      refine ⟨6984364527376592017991417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4656243018251061345327611 6984364527376592017991417)
      ·
        refine ⟨5238273395532444013493563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6984364527376592017991417 5238273395532444013493563)
        ·
          refine ⟨7857410093298666020240345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5238273395532444013493563 7857410093298666020240345)
          ·
            refine ⟨5893057569973999515180259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7857410093298666020240345 5893057569973999515180259)
            ·
              refine ⟨8839586354960999272770389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5893057569973999515180259 8839586354960999272770389)
              ·
                refine ⟨51794451298599605113889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8839586354960999272770389 51794451298599605113889)
                ·
                  rfl

theorem cell21_680868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 9].length) (baseStart_680868 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_680868 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_680868 prefixEnd_680868 := by exact prefixLift 680868
  have htrace : WordTrace (prefixWord ++ tailWord_680868) baseStart_680868 baseEnd_680868 := by
    simpa [prefixWord, tailWord_680868, baseEnd_680868] using wordTrace_append hprefix tailTrace_680868
  have hstable : (prefixWord ++ tailWord_680868).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680868).length < 2 ^ (prefixWord ++ tailWord_680868).sum := by decide
  have hdescent : baseEnd_680868 < baseStart_680868 := by decide
  rcases family_descends (prefixWord ++ tailWord_680868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680916 : List Nat := [2, 4, 1, 2, 1, 3, 1, 2, 5]
def baseStart_680916 : Nat := 118140960795 + 680916 * 2 ^ 59
def prefixEnd_680916 : Nat := 4983230072969 + 3 ^ 40 * 680916 * 2
def baseEnd_680916 : Nat := 155394308149761398541569

theorem tailTrace_680916 : CollatzResearch.WordTrace tailWord_680916 prefixEnd_680916 155394308149761398541569 := by
  unfold tailWord_680916
  simp only [CollatzResearch.WordTrace]
  refine ⟨12417523400582549019747301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16556697867443398692996401 12417523400582549019747301)
  ·
    refine ⟨2328285637609227941202619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12417523400582549019747301 2328285637609227941202619)
    ·
      refine ⟨3492428456413841911803929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2328285637609227941202619 3492428456413841911803929)
      ·
        refine ⟨2619321342310381433852947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3492428456413841911803929 2619321342310381433852947)
        ·
          refine ⟨3928982013465572150779421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2619321342310381433852947 3928982013465572150779421)
          ·
            refine ⟨1473368255049589556542283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3928982013465572150779421 1473368255049589556542283)
            ·
              refine ⟨2210052382574384334813425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1473368255049589556542283 2210052382574384334813425)
              ·
                refine ⟨1657539286930788251110069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2210052382574384334813425 1657539286930788251110069)
                ·
                  refine ⟨155394308149761398541569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1657539286930788251110069 155394308149761398541569)
                  ·
                    rfl

theorem cell21_680916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 2, 5].length) (baseStart_680916 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_680916 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_680916 prefixEnd_680916 := by exact prefixLift 680916
  have htrace : WordTrace (prefixWord ++ tailWord_680916) baseStart_680916 baseEnd_680916 := by
    simpa [prefixWord, tailWord_680916, baseEnd_680916] using wordTrace_append hprefix tailTrace_680916
  have hstable : (prefixWord ++ tailWord_680916).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680916).length < 2 ^ (prefixWord ++ tailWord_680916).sum := by decide
  have hdescent : baseEnd_680916 < baseStart_680916 := by decide
  rcases family_descends (prefixWord ++ tailWord_680916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681006 : List Nat := [4, 1, 3, 1, 1, 1, 1, 3, 6]
def baseStart_681006 : Nat := 118140960795 + 681006 * 2 ^ 59
def prefixEnd_681006 : Nat := 4983230072969 + 3 ^ 40 * 681006 * 2
def baseEnd_681006 : Nat := 155414847375941242041385

theorem tailTrace_681006 : CollatzResearch.WordTrace tailWord_681006 prefixEnd_681006 155414847375941242041385 := by
  unfold tailWord_681006
  simp only [CollatzResearch.WordTrace]
  refine ⟨3104791171354880426283859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16558886247226028940180581 3104791171354880426283859)
  ·
    refine ⟨4657186757032320639425789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3104791171354880426283859 4657186757032320639425789)
    ·
      refine ⟨1746445033887120239784671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4657186757032320639425789 1746445033887120239784671)
      ·
        refine ⟨2619667550830680359677007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1746445033887120239784671 2619667550830680359677007)
        ·
          refine ⟨3929501326246020539515511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2619667550830680359677007 3929501326246020539515511)
          ·
            refine ⟨5894251989369030809273267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3929501326246020539515511 5894251989369030809273267)
            ·
              refine ⟨8841377984053546213909901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5894251989369030809273267 8841377984053546213909901)
              ·
                refine ⟨3315516744020079830216213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8841377984053546213909901 3315516744020079830216213)
                ·
                  refine ⟨155414847375941242041385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3315516744020079830216213 155414847375941242041385)
                  ·
                    rfl

theorem cell21_681006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 3, 6].length) (baseStart_681006 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_681006 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_681006 prefixEnd_681006 := by exact prefixLift 681006
  have htrace : WordTrace (prefixWord ++ tailWord_681006) baseStart_681006 baseEnd_681006 := by
    simpa [prefixWord, tailWord_681006, baseEnd_681006] using wordTrace_append hprefix tailTrace_681006
  have hstable : (prefixWord ++ tailWord_681006).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681006).length < 2 ^ (prefixWord ++ tailWord_681006).sum := by decide
  have hdescent : baseEnd_681006 < baseStart_681006 := by decide
  rcases family_descends (prefixWord ++ tailWord_681006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681009 : List Nat := [1, 2, 2, 3, 1, 2, 5, 2, 3]
def baseStart_681009 : Nat := 118140960795 + 681009 * 2 ^ 59
def prefixEnd_681009 : Nat := 4983230072969 + 3 ^ 40 * 681009 * 2
def baseEnd_681009 : Nat := 155415532016813903491379

theorem tailTrace_681009 : CollatzResearch.WordTrace tailWord_681009 prefixEnd_681009 155415532016813903491379 := by
  unfold tailWord_681009
  simp only [CollatzResearch.WordTrace]
  refine ⟨24838438789828174922630081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16558959193218783281753387 24838438789828174922630081)
  ·
    refine ⟨18628829092371131191972561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24838438789828174922630081 18628829092371131191972561)
    ·
      refine ⟨13971621819278348393979421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18628829092371131191972561 13971621819278348393979421)
      ·
        refine ⟨5239358182229380647742283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13971621819278348393979421 5239358182229380647742283)
        ·
          refine ⟨7859037273344070971613425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5239358182229380647742283 7859037273344070971613425)
          ·
            refine ⟨5894277955008053228710069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7859037273344070971613425 5894277955008053228710069)
            ·
              refine ⟨552588558282004990191569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5894277955008053228710069 552588558282004990191569)
              ·
                refine ⟨414441418711503742643677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 552588558282004990191569 414441418711503742643677)
                ·
                  refine ⟨155415532016813903491379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 414441418711503742643677 155415532016813903491379)
                  ·
                    rfl

theorem cell21_681009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 5, 2, 3].length) (baseStart_681009 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_681009 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_681009 prefixEnd_681009 := by exact prefixLift 681009
  have htrace : WordTrace (prefixWord ++ tailWord_681009) baseStart_681009 baseEnd_681009 := by
    simpa [prefixWord, tailWord_681009, baseEnd_681009] using wordTrace_append hprefix tailTrace_681009
  have hstable : (prefixWord ++ tailWord_681009).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681009).length < 2 ^ (prefixWord ++ tailWord_681009).sum := by decide
  have hdescent : baseEnd_681009 < baseStart_681009 := by decide
  rcases family_descends (prefixWord ++ tailWord_681009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681020 : List Nat := [2, 2, 2, 2, 2, 2, 1, 8]
def baseStart_681020 : Nat := 118140960795 + 681020 * 2 ^ 59
def prefixEnd_681020 : Nat := 4983230072969 + 3 ^ 40 * 681020 * 2
def baseEnd_681020 : Nat := 51806014122226776269341

theorem tailTrace_681020 : CollatzResearch.WordTrace tailWord_681020 prefixEnd_681020 51806014122226776269341 := by
  unfold tailWord_681020
  simp only [CollatzResearch.WordTrace]
  refine ⟨12419419996394161900640257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16559226661858882534187009 12419419996394161900640257)
  ·
    refine ⟨9314564997295621425480193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12419419996394161900640257 9314564997295621425480193)
    ·
      refine ⟨6985923747971716069110145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9314564997295621425480193 6985923747971716069110145)
      ·
        refine ⟨5239442810978787051832609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6985923747971716069110145 5239442810978787051832609)
        ·
          refine ⟨3929582108234090288874457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5239442810978787051832609 3929582108234090288874457)
          ·
            refine ⟨2947186581175567716655843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3929582108234090288874457 2947186581175567716655843)
            ·
              refine ⟨4420779871763351574983765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2947186581175567716655843 4420779871763351574983765)
              ·
                refine ⟨51806014122226776269341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4420779871763351574983765 51806014122226776269341)
                ·
                  rfl

theorem cell21_681020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 8].length) (baseStart_681020 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_681020 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_681020 prefixEnd_681020 := by exact prefixLift 681020
  have htrace : WordTrace (prefixWord ++ tailWord_681020) baseStart_681020 baseEnd_681020 := by
    simpa [prefixWord, tailWord_681020, baseEnd_681020] using wordTrace_append hprefix tailTrace_681020
  have hstable : (prefixWord ++ tailWord_681020).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681020).length < 2 ^ (prefixWord ++ tailWord_681020).sum := by decide
  have hdescent : baseEnd_681020 < baseStart_681020 := by decide
  rcases family_descends (prefixWord ++ tailWord_681020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681037 : List Nat := [1, 6, 1, 1, 1, 2, 2, 7]
def baseStart_681037 : Nat := 118140960795 + 681037 * 2 ^ 59
def prefixEnd_681037 : Nat := 4983230072969 + 3 ^ 40 * 681037 * 2
def baseEnd_681037 : Nat := 51807307332764025674885

theorem tailTrace_681037 : CollatzResearch.WordTrace tailWord_681037 prefixEnd_681037 51807307332764025674885 := by
  unfold tailWord_681037
  simp only [CollatzResearch.WordTrace]
  refine ⟨24839460033726735704649365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16559640022484490469766243 24839460033726735704649365)
  ·
    refine ⟨1164349689080940736155439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 24839460033726735704649365 1164349689080940736155439)
    ·
      refine ⟨1746524533621411104233159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1164349689080940736155439 1746524533621411104233159)
      ·
        refine ⟨2619786800432116656349739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1746524533621411104233159 2619786800432116656349739)
        ·
          refine ⟨3929680200648174984524609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2619786800432116656349739 3929680200648174984524609)
          ·
            refine ⟨2947260150486131238393457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3929680200648174984524609 2947260150486131238393457)
            ·
              refine ⟨2210445112864598428795093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2947260150486131238393457 2210445112864598428795093)
              ·
                refine ⟨51807307332764025674885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2210445112864598428795093 51807307332764025674885)
                ·
                  rfl

theorem cell21_681037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 7].length) (baseStart_681037 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_681037 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_681037 prefixEnd_681037 := by exact prefixLift 681037
  have htrace : WordTrace (prefixWord ++ tailWord_681037) baseStart_681037 baseEnd_681037 := by
    simpa [prefixWord, tailWord_681037, baseEnd_681037] using wordTrace_append hprefix tailTrace_681037
  have hstable : (prefixWord ++ tailWord_681037).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681037).length < 2 ^ (prefixWord ++ tailWord_681037).sum := by decide
  have hdescent : baseEnd_681037 < baseStart_681037 := by decide
  rcases family_descends (prefixWord ++ tailWord_681037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681054 : List Nat := [4, 4, 1, 1, 1, 10]
def baseStart_681054 : Nat := 118140960795 + 681054 * 2 ^ 59
def prefixEnd_681054 : Nat := 4983230072969 + 3 ^ 40 * 681054 * 2
def baseEnd_681054 : Nat := 5756511171477919453381

theorem tailTrace_681054 : CollatzResearch.WordTrace tailWord_681054 prefixEnd_681054 5756511171477919453381 := by
  unfold tailWord_681054
  simp only [CollatzResearch.WordTrace]
  refine ⟨3105010009333143451002277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16560053383110098405345477 3105010009333143451002277)
  ·
    refine ⟨582189376749964397062927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3105010009333143451002277 582189376749964397062927)
    ·
      refine ⟨873284065124946595594391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 582189376749964397062927 873284065124946595594391)
      ·
        refine ⟨1309926097687419893391587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 873284065124946595594391 1309926097687419893391587)
        ·
          refine ⟨1964889146531129840087381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1309926097687419893391587 1964889146531129840087381)
          ·
            refine ⟨5756511171477919453381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1964889146531129840087381 5756511171477919453381)
            ·
              rfl

theorem cell21_681054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 10].length) (baseStart_681054 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_681054 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_681054 prefixEnd_681054 := by exact prefixLift 681054
  have htrace : WordTrace (prefixWord ++ tailWord_681054) baseStart_681054 baseEnd_681054 := by
    simpa [prefixWord, tailWord_681054, baseEnd_681054] using wordTrace_append hprefix tailTrace_681054
  have hstable : (prefixWord ++ tailWord_681054).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681054).length < 2 ^ (prefixWord ++ tailWord_681054).sum := by decide
  have hdescent : baseEnd_681054 < baseStart_681054 := by decide
  rcases family_descends (prefixWord ++ tailWord_681054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681068 : List Nat := [2, 2, 1, 1, 3, 2, 3, 4, 3]
def baseStart_681068 : Nat := 118140960795 + 681068 * 2 ^ 59
def prefixEnd_681068 : Nat := 4983230072969 + 3 ^ 40 * 681068 * 2
def baseEnd_681068 : Nat := 155428996620642912007925

theorem tailTrace_681068 : CollatzResearch.WordTrace tailWord_681068 prefixEnd_681068 155428996620642912007925 := by
  unfold tailWord_681068
  simp only [CollatzResearch.WordTrace]
  refine ⟨12420295348307213999513929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16560393797742951999351905 12420295348307213999513929)
  ·
    refine ⟨9315221511230410499635447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12420295348307213999513929 9315221511230410499635447)
    ·
      refine ⟨13972832266845615749453171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9315221511230410499635447 13972832266845615749453171)
      ·
        refine ⟨20959248400268423624179757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13972832266845615749453171 20959248400268423624179757)
        ·
          refine ⟨7859718150100658859067409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20959248400268423624179757 7859718150100658859067409)
          ·
            refine ⟨5894788612575494144300557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7859718150100658859067409 5894788612575494144300557)
            ·
              refine ⟨2210545729715810304112709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5894788612575494144300557 2210545729715810304112709)
              ·
                refine ⟨414477324321714432021133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2210545729715810304112709 414477324321714432021133)
                ·
                  refine ⟨155428996620642912007925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 414477324321714432021133 155428996620642912007925)
                  ·
                    rfl

theorem cell21_681068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 4, 3].length) (baseStart_681068 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_681068 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_681068 prefixEnd_681068 := by exact prefixLift 681068
  have htrace : WordTrace (prefixWord ++ tailWord_681068) baseStart_681068 baseEnd_681068 := by
    simpa [prefixWord, tailWord_681068, baseEnd_681068] using wordTrace_append hprefix tailTrace_681068
  have hstable : (prefixWord ++ tailWord_681068).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681068).length < 2 ^ (prefixWord ++ tailWord_681068).sum := by decide
  have hdescent : baseEnd_681068 < baseStart_681068 := by decide
  rcases family_descends (prefixWord ++ tailWord_681068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681189 : List Nat := [1, 3, 1, 4, 3, 1, 2, 6]
def baseStart_681189 : Nat := 118140960795 + 681189 * 2 ^ 59
def prefixEnd_681189 : Nat := 4983230072969 + 3 ^ 40 * 681189 * 2
def baseEnd_681189 : Nat := 51818870156391196830337

theorem tailTrace_681189 : CollatzResearch.WordTrace tailWord_681189 prefixEnd_681189 51818870156391196830337 := by
  unfold tailWord_681189
  simp only [CollatzResearch.WordTrace]
  refine ⟨24845003929176065664182621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16563335952784043776121747 24845003929176065664182621)
  ·
    refine ⟨9316876473441024624068483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24845003929176065664182621 9316876473441024624068483)
    ·
      refine ⟨13975314710161536936102725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9316876473441024624068483 13975314710161536936102725)
      ·
        refine ⟨2620371508155288175519261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13975314710161536936102725 2620371508155288175519261)
        ·
          refine ⟨982639315558233065819723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2620371508155288175519261 982639315558233065819723)
          ·
            refine ⟨1473958973337349598729585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 982639315558233065819723 1473958973337349598729585)
            ·
              refine ⟨1105469230003012199047189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1473958973337349598729585 1105469230003012199047189)
              ·
                refine ⟨51818870156391196830337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1105469230003012199047189 51818870156391196830337)
                ·
                  rfl

theorem cell21_681189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 2, 6].length) (baseStart_681189 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_681189 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_681189 prefixEnd_681189 := by exact prefixLift 681189
  have htrace : WordTrace (prefixWord ++ tailWord_681189) baseStart_681189 baseEnd_681189 := by
    simpa [prefixWord, tailWord_681189, baseEnd_681189] using wordTrace_append hprefix tailTrace_681189
  have hstable : (prefixWord ++ tailWord_681189).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681189).length < 2 ^ (prefixWord ++ tailWord_681189).sum := by decide
  have hdescent : baseEnd_681189 < baseStart_681189 := by decide
  rcases family_descends (prefixWord ++ tailWord_681189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681265 : List Nat := [1, 2, 2, 3, 3, 2, 3, 5]
def baseStart_681265 : Nat := 118140960795 + 681265 * 2 ^ 59
def prefixEnd_681265 : Nat := 4983230072969 + 3 ^ 40 * 681265 * 2
def baseEnd_681265 : Nat := 51824651568204782408063

theorem tailTrace_681265 : CollatzResearch.WordTrace tailWord_681265 prefixEnd_681265 51824651568204782408063 := by
  unfold tailWord_681265
  simp only [CollatzResearch.WordTrace]
  refine ⟨24847775876900730643949249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16565183917933820429299499 24847775876900730643949249)
  ·
    refine ⟨18635831907675547982961937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24847775876900730643949249 18635831907675547982961937)
    ·
      refine ⟨13976873930756660987221453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18635831907675547982961937 13976873930756660987221453)
      ·
        refine ⟨5241327724033747870208045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13976873930756660987221453 5241327724033747870208045)
        ·
          refine ⟨1965497896512655451328017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5241327724033747870208045 1965497896512655451328017)
          ·
            refine ⟨1474123422384491588496013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1965497896512655451328017 1474123422384491588496013)
            ·
              refine ⟨552796283394184345686005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1474123422384491588496013 552796283394184345686005)
              ·
                refine ⟨51824651568204782408063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 552796283394184345686005 51824651568204782408063)
                ·
                  rfl

theorem cell21_681265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 3, 5].length) (baseStart_681265 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_681265 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_681265 prefixEnd_681265 := by exact prefixLift 681265
  have htrace : WordTrace (prefixWord ++ tailWord_681265) baseStart_681265 baseEnd_681265 := by
    simpa [prefixWord, tailWord_681265, baseEnd_681265] using wordTrace_append hprefix tailTrace_681265
  have hstable : (prefixWord ++ tailWord_681265).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681265).length < 2 ^ (prefixWord ++ tailWord_681265).sum := by decide
  have hdescent : baseEnd_681265 < baseStart_681265 := by decide
  rcases family_descends (prefixWord ++ tailWord_681265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681324 : List Nat := [2, 2, 1, 1, 5, 2, 1, 7]
def baseStart_681324 : Nat := 118140960795 + 681324 * 2 ^ 59
def prefixEnd_681324 : Nat := 4983230072969 + 3 ^ 40 * 681324 * 2
def baseEnd_681324 : Nat := 51829139769481118580245

theorem tailTrace_681324 : CollatzResearch.WordTrace tailWord_681324 prefixEnd_681324 51829139769481118580245 := by
  unfold tailWord_681324
  simp only [CollatzResearch.WordTrace]
  refine ⟨12424963891843491860173513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16566618522457989146898017 12424963891843491860173513)
  ·
    refine ⟨9318722918882618895130135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12424963891843491860173513 9318722918882618895130135)
    ·
      refine ⟨13978084378323928342695203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9318722918882618895130135 13978084378323928342695203)
      ·
        refine ⟨20967126567485892514042805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13978084378323928342695203 20967126567485892514042805)
        ·
          refine ⟨1965668115701802423191513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20967126567485892514042805 1965668115701802423191513)
          ·
            refine ⟨1474251086776351817393635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1965668115701802423191513 1474251086776351817393635)
            ·
              refine ⟨2211376630164527726090453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1474251086776351817393635 2211376630164527726090453)
              ·
                refine ⟨51829139769481118580245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2211376630164527726090453 51829139769481118580245)
                ·
                  rfl

theorem cell21_681324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 7].length) (baseStart_681324 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_681324 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_681324 prefixEnd_681324 := by exact prefixLift 681324
  have htrace : WordTrace (prefixWord ++ tailWord_681324) baseStart_681324 baseEnd_681324 := by
    simpa [prefixWord, tailWord_681324, baseEnd_681324] using wordTrace_append hprefix tailTrace_681324
  have hstable : (prefixWord ++ tailWord_681324).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681324).length < 2 ^ (prefixWord ++ tailWord_681324).sum := by decide
  have hdescent : baseEnd_681324 < baseStart_681324 := by decide
  rcases family_descends (prefixWord ++ tailWord_681324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681448 : List Nat := [2, 1, 4, 1, 1, 2, 4, 3, 3]
def baseStart_681448 : Nat := 118140960795 + 681448 * 2 ^ 59
def prefixEnd_681448 : Nat := 4983230072969 + 3 ^ 40 * 681448 * 2
def baseEnd_681448 : Nat := 155515717797846695673815

theorem tailTrace_681448 : CollatzResearch.WordTrace tailWord_681448 prefixEnd_681448 155515717797846695673815 := by
  unfold tailWord_681448
  simp only [CollatzResearch.WordTrace]
  refine ⟨12427225217618876448930499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16569633623491835265240665 12427225217618876448930499)
  ·
    refine ⟨18640837826428314673395749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12427225217618876448930499 18640837826428314673395749)
    ·
      refine ⟨3495157092455309001261703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18640837826428314673395749 3495157092455309001261703)
      ·
        refine ⟨5242735638682963501892555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3495157092455309001261703 5242735638682963501892555)
        ·
          refine ⟨7864103458024445252838833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5242735638682963501892555 7864103458024445252838833)
          ·
            refine ⟨5898077593518333939629125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7864103458024445252838833 5898077593518333939629125)
            ·
              refine ⟨1105889548784687613680461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5898077593518333939629125 1105889548784687613680461)
              ·
                refine ⟨414708580794257855130173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1105889548784687613680461 414708580794257855130173)
                ·
                  refine ⟨155515717797846695673815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 414708580794257855130173 155515717797846695673815)
                  ·
                    rfl

theorem cell21_681448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 4, 3, 3].length) (baseStart_681448 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_681448 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_681448 prefixEnd_681448 := by exact prefixLift 681448
  have htrace : WordTrace (prefixWord ++ tailWord_681448) baseStart_681448 baseEnd_681448 := by
    simpa [prefixWord, tailWord_681448, baseEnd_681448] using wordTrace_append hprefix tailTrace_681448
  have hstable : (prefixWord ++ tailWord_681448).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681448).length < 2 ^ (prefixWord ++ tailWord_681448).sum := by decide
  have hdescent : baseEnd_681448 < baseStart_681448 := by decide
  rcases family_descends (prefixWord ++ tailWord_681448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681462 : List Nat := [5, 1, 1, 1, 2, 3, 1, 1, 6]
def baseStart_681462 : Nat := 118140960795 + 681462 * 2 ^ 59
def prefixEnd_681462 : Nat := 4983230072969 + 3 ^ 40 * 681462 * 2
def baseEnd_681462 : Nat := 155518912788585782440453

theorem tailTrace_681462 : CollatzResearch.WordTrace tailWord_681462 prefixEnd_681462 155518912788585782440453 := by
  unfold tailWord_681462
  simp only [CollatzResearch.WordTrace]
  refine ⟨1553435066074189580554415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16569974038124688859247093 1553435066074189580554415)
  ·
    refine ⟨2330152599111284370831623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1553435066074189580554415 2330152599111284370831623)
    ·
      refine ⟨3495228898666926556247435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2330152599111284370831623 3495228898666926556247435)
      ·
        refine ⟨5242843348000389834371153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3495228898666926556247435 5242843348000389834371153)
        ·
          refine ⟨3932132511000292375778365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5242843348000389834371153 3932132511000292375778365)
          ·
            refine ⟨1474549691625109640916887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3932132511000292375778365 1474549691625109640916887)
            ·
              refine ⟨2211824537437664461375331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1474549691625109640916887 2211824537437664461375331)
              ·
                refine ⟨3317736806156496692062997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2211824537437664461375331 3317736806156496692062997)
                ·
                  refine ⟨155518912788585782440453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3317736806156496692062997 155518912788585782440453)
                  ·
                    rfl

theorem cell21_681462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 1, 6].length) (baseStart_681462 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_681462 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_681462 prefixEnd_681462 := by exact prefixLift 681462
  have htrace : WordTrace (prefixWord ++ tailWord_681462) baseStart_681462 baseEnd_681462 := by
    simpa [prefixWord, tailWord_681462, baseEnd_681462] using wordTrace_append hprefix tailTrace_681462
  have hstable : (prefixWord ++ tailWord_681462).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681462).length < 2 ^ (prefixWord ++ tailWord_681462).sum := by decide
  have hdescent : baseEnd_681462 < baseStart_681462 := by decide
  rcases family_descends (prefixWord ++ tailWord_681462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681479 : List Nat := [1, 1, 4, 3, 2, 2, 3, 1, 4]
def baseStart_681479 : Nat := 118140960795 + 681479 * 2 ^ 59
def prefixEnd_681479 : Nat := 4983230072969 + 3 ^ 40 * 681479 * 2
def baseEnd_681479 : Nat := 155522792420197530657085

theorem tailTrace_681479 : CollatzResearch.WordTrace tailWord_681479 prefixEnd_681479 155522792420197530657085 := by
  unfold tailWord_681479
  simp only [CollatzResearch.WordTrace]
  refine ⟨24855581098125445192239491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16570387398750296794826327 24855581098125445192239491)
  ·
    refine ⟨37283371647188167788359237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24855581098125445192239491 37283371647188167788359237)
    ·
      refine ⟨6990632183847781460317357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37283371647188167788359237 6990632183847781460317357)
      ·
        refine ⟨2621487068942918047619009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6990632183847781460317357 2621487068942918047619009)
        ·
          refine ⟨1966115301707188535714257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2621487068942918047619009 1966115301707188535714257)
          ·
            refine ⟨1474586476280391401785693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1966115301707188535714257 1474586476280391401785693)
            ·
              refine ⟨552969928605146775669635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1474586476280391401785693 552969928605146775669635)
              ·
                refine ⟨829454892907720163504453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 552969928605146775669635 829454892907720163504453)
                ·
                  refine ⟨155522792420197530657085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 829454892907720163504453 155522792420197530657085)
                  ·
                    rfl

theorem cell21_681479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 3, 1, 4].length) (baseStart_681479 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_681479 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_681479 prefixEnd_681479 := by exact prefixLift 681479
  have htrace : WordTrace (prefixWord ++ tailWord_681479) baseStart_681479 baseEnd_681479 := by
    simpa [prefixWord, tailWord_681479, baseEnd_681479] using wordTrace_append hprefix tailTrace_681479
  have hstable : (prefixWord ++ tailWord_681479).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681479).length < 2 ^ (prefixWord ++ tailWord_681479).sum := by decide
  have hdescent : baseEnd_681479 < baseStart_681479 := by decide
  rcases family_descends (prefixWord ++ tailWord_681479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681493 : List Nat := [1, 3, 2, 1, 3, 4, 2, 5]
def baseStart_681493 : Nat := 118140960795 + 681493 * 2 ^ 59
def prefixEnd_681493 : Nat := 4983230072969 + 3 ^ 40 * 681493 * 2
def baseEnd_681493 : Nat := 51841995803645539141241

theorem tailTrace_681493 : CollatzResearch.WordTrace tailWord_681493 prefixEnd_681493 51841995803645539141241 := by
  unfold tailWord_681493
  simp only [CollatzResearch.WordTrace]
  refine ⟨24856091720074725583249133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16570727813383150388832755 24856091720074725583249133)
  ·
    refine ⟨9321034395028022093718425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24856091720074725583249133 9321034395028022093718425)
    ·
      refine ⟨6990775796271016570288819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9321034395028022093718425 6990775796271016570288819)
      ·
        refine ⟨10486163694406524855433229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6990775796271016570288819 10486163694406524855433229)
        ·
          refine ⟨3932311385402446820787461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10486163694406524855433229 3932311385402446820787461)
          ·
            refine ⟨737308384762958778897649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3932311385402446820787461 737308384762958778897649)
            ·
              refine ⟨552981288572219084173237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 737308384762958778897649 552981288572219084173237)
              ·
                refine ⟨51841995803645539141241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 552981288572219084173237 51841995803645539141241)
                ·
                  rfl

theorem cell21_681493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 2, 5].length) (baseStart_681493 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_681493 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_681493 prefixEnd_681493 := by exact prefixLift 681493
  have htrace : WordTrace (prefixWord ++ tailWord_681493) baseStart_681493 baseEnd_681493 := by
    simpa [prefixWord, tailWord_681493, baseEnd_681493] using wordTrace_append hprefix tailTrace_681493
  have hstable : (prefixWord ++ tailWord_681493).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681493).length < 2 ^ (prefixWord ++ tailWord_681493).sum := by decide
  have hdescent : baseEnd_681493 < baseStart_681493 := by decide
  rcases family_descends (prefixWord ++ tailWord_681493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681521 : List Nat := [1, 2, 2, 3, 1, 1, 1, 6, 4]
def baseStart_681521 : Nat := 118140960795 + 681521 * 2 ^ 59
def prefixEnd_681521 : Nat := 4983230072969 + 3 ^ 40 * 681521 * 2
def baseEnd_681521 : Nat := 155532377392414790956999

theorem tailTrace_681521 : CollatzResearch.WordTrace tailWord_681521 prefixEnd_681521 155532377392414790956999 := by
  unfold tailWord_681521
  simp only [CollatzResearch.WordTrace]
  refine ⟨24857112963973286365268417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16571408642648857576845611 24857112963973286365268417)
  ·
    refine ⟨18642834722979964773951313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24857112963973286365268417 18642834722979964773951313)
    ·
      refine ⟨13982126042234973580463485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18642834722979964773951313 13982126042234973580463485)
      ·
        refine ⟨5243297265838115092673807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13982126042234973580463485 5243297265838115092673807)
        ·
          refine ⟨7864945898757172639010711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5243297265838115092673807 7864945898757172639010711)
          ·
            refine ⟨11797418848135758958516067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7864945898757172639010711 11797418848135758958516067)
            ·
              refine ⟨17696128272203638437774101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11797418848135758958516067 17696128272203638437774101)
              ·
                refine ⟨829506012759545551770661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 17696128272203638437774101 829506012759545551770661)
                ·
                  refine ⟨155532377392414790956999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 829506012759545551770661 155532377392414790956999)
                  ·
                    rfl

theorem cell21_681521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 6, 4].length) (baseStart_681521 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_681521 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_681521 prefixEnd_681521 := by exact prefixLift 681521
  have htrace : WordTrace (prefixWord ++ tailWord_681521) baseStart_681521 baseEnd_681521 := by
    simpa [prefixWord, tailWord_681521, baseEnd_681521] using wordTrace_append hprefix tailTrace_681521
  have hstable : (prefixWord ++ tailWord_681521).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681521).length < 2 ^ (prefixWord ++ tailWord_681521).sum := by decide
  have hdescent : baseEnd_681521 < baseStart_681521 := by decide
  rcases family_descends (prefixWord ++ tailWord_681521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681535 : List Nat := [1, 1, 2, 2, 3, 3, 1, 8]
def baseStart_681535 : Nat := 118140960795 + 681535 * 2 ^ 59
def prefixEnd_681535 : Nat := 4983230072969 + 3 ^ 40 * 681535 * 2
def baseEnd_681535 : Nat := 51845190794384625907879

theorem tailTrace_681535 : CollatzResearch.WordTrace tailWord_681535 prefixEnd_681535 51845190794384625907879 := by
  unfold tailWord_681535
  simp only [CollatzResearch.WordTrace]
  refine ⟨24857623585922566756278059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16571749057281711170852039 24857623585922566756278059)
  ·
    refine ⟨37286435378883850134417089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24857623585922566756278059 37286435378883850134417089)
    ·
      refine ⟨27964826534162887600812817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37286435378883850134417089 27964826534162887600812817)
      ·
        refine ⟨20973619900622165700609613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27964826534162887600812817 20973619900622165700609613)
        ·
          refine ⟨7865107462733312137728605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20973619900622165700609613 7865107462733312137728605)
          ·
            refine ⟨2949415298524992051648227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7865107462733312137728605 2949415298524992051648227)
            ·
              refine ⟨4424122947787488077472341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2949415298524992051648227 4424122947787488077472341)
              ·
                refine ⟨51845190794384625907879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4424122947787488077472341 51845190794384625907879)
                ·
                  rfl

theorem cell21_681535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 8].length) (baseStart_681535 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_681535 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_681535 prefixEnd_681535 := by exact prefixLift 681535
  have htrace : WordTrace (prefixWord ++ tailWord_681535) baseStart_681535 baseEnd_681535 := by
    simpa [prefixWord, tailWord_681535, baseEnd_681535] using wordTrace_append hprefix tailTrace_681535
  have hstable : (prefixWord ++ tailWord_681535).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681535).length < 2 ^ (prefixWord ++ tailWord_681535).sum := by decide
  have hdescent : baseEnd_681535 < baseStart_681535 := by decide
  rcases family_descends (prefixWord ++ tailWord_681535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681628 : List Nat := [2, 2, 3, 2, 3, 1, 8]
def baseStart_681628 : Nat := 118140960795 + 681628 * 2 ^ 59
def prefixEnd_681628 : Nat := 4983230072969 + 3 ^ 40 * 681628 * 2
def baseEnd_681628 : Nat := 17284088472245153630383

theorem tailTrace_681628 : CollatzResearch.WordTrace tailWord_681628 prefixEnd_681628 17284088472245153630383 := by
  unfold tailWord_681628
  simp only [CollatzResearch.WordTrace]
  refine ⟨12430507787292821819706769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16574010383057095759609025 12430507787292821819706769)
  ·
    refine ⟨9322880840469616364780077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12430507787292821819706769 9322880840469616364780077)
    ·
      refine ⟨3496080315176106136792529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9322880840469616364780077 3496080315176106136792529)
      ·
        refine ⟨2622060236382079602594397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3496080315176106136792529 2622060236382079602594397)
        ·
          refine ⟨983272588643279850972899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2622060236382079602594397 983272588643279850972899)
          ·
            refine ⟨1474908882964919776459349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 983272588643279850972899 1474908882964919776459349)
            ·
              refine ⟨17284088472245153630383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1474908882964919776459349 17284088472245153630383)
              ·
                rfl

theorem cell21_681628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 8].length) (baseStart_681628 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_681628 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_681628 prefixEnd_681628 := by exact prefixLift 681628
  have htrace : WordTrace (prefixWord ++ tailWord_681628) baseStart_681628 baseEnd_681628 := by
    simpa [prefixWord, tailWord_681628, baseEnd_681628] using wordTrace_append hprefix tailTrace_681628
  have hstable : (prefixWord ++ tailWord_681628).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681628).length < 2 ^ (prefixWord ++ tailWord_681628).sum := by decide
  have hdescent : baseEnd_681628 < baseStart_681628 := by decide
  rcases family_descends (prefixWord ++ tailWord_681628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681693 : List Nat := [1, 4, 3, 3, 1, 2, 1, 1, 5]
def baseStart_681693 : Nat := 118140960795 + 681693 * 2 ^ 59
def prefixEnd_681693 : Nat := 4983230072969 + 3 ^ 40 * 681693 * 2
def baseEnd_681693 : Nat := 155571630135780714089981

theorem tailTrace_681693 : CollatzResearch.WordTrace tailWord_681693 prefixEnd_681693 155571630135780714089981 := by
  unfold tailWord_681693
  simp only [CollatzResearch.WordTrace]
  refine ⟨24863386319350159740529733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16575590879566773160353155 24863386319350159740529733)
  ·
    refine ⟨4661884934878154951349325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24863386319350159740529733 4661884934878154951349325)
    ·
      refine ⟨1748206850579308106755997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4661884934878154951349325 1748206850579308106755997)
      ·
        refine ⟨655577568967240540033499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1748206850579308106755997 655577568967240540033499)
        ·
          refine ⟨983366353450860810050249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 655577568967240540033499 983366353450860810050249)
          ·
            refine ⟨737524765088145607537687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 983366353450860810050249 737524765088145607537687)
            ·
              refine ⟨1106287147632218411306531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 737524765088145607537687 1106287147632218411306531)
              ·
                refine ⟨1659430721448327616959797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1106287147632218411306531 1659430721448327616959797)
                ·
                  refine ⟨155571630135780714089981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1659430721448327616959797 155571630135780714089981)
                  ·
                    rfl

theorem cell21_681693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 1, 1, 5].length) (baseStart_681693 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_681693 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_681693 prefixEnd_681693 := by exact prefixLift 681693
  have htrace : WordTrace (prefixWord ++ tailWord_681693) baseStart_681693 baseEnd_681693 := by
    simpa [prefixWord, tailWord_681693, baseEnd_681693] using wordTrace_append hprefix tailTrace_681693
  have hstable : (prefixWord ++ tailWord_681693).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681693).length < 2 ^ (prefixWord ++ tailWord_681693).sum := by decide
  have hdescent : baseEnd_681693 < baseStart_681693 := by decide
  rcases family_descends (prefixWord ++ tailWord_681693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681704 : List Nat := [2, 1, 4, 1, 3, 2, 2, 6]
def baseStart_681704 : Nat := 118140960795 + 681704 * 2 ^ 59
def prefixEnd_681704 : Nat := 4983230072969 + 3 ^ 40 * 681704 * 2
def baseEnd_681704 : Nat := 51858046828549046468875

theorem tailTrace_681704 : CollatzResearch.WordTrace tailWord_681704 prefixEnd_681704 51858046828549046468875 := by
  unfold tailWord_681704
  simp only [CollatzResearch.WordTrace]
  refine ⟨12431893761155154309590083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16575858348206872412786777 12431893761155154309590083)
  ·
    refine ⟨18647840641732731464385125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12431893761155154309590083 18647840641732731464385125)
    ·
      refine ⟨3496470120324887149572211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18647840641732731464385125 3496470120324887149572211)
      ·
        refine ⟨5244705180487330724358317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3496470120324887149572211 5244705180487330724358317)
        ·
          refine ⟨1966764442682749021634369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5244705180487330724358317 1966764442682749021634369)
          ·
            refine ⟨1475073332012061766225777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1966764442682749021634369 1475073332012061766225777)
            ·
              refine ⟨1106304999009046324669333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1475073332012061766225777 1106304999009046324669333)
              ·
                refine ⟨51858046828549046468875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1106304999009046324669333 51858046828549046468875)
                ·
                  rfl

theorem cell21_681704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 2, 6].length) (baseStart_681704 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_681704 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_681704 prefixEnd_681704 := by exact prefixLift 681704
  have htrace : WordTrace (prefixWord ++ tailWord_681704) baseStart_681704 baseEnd_681704 := by
    simpa [prefixWord, tailWord_681704, baseEnd_681704] using wordTrace_append hprefix tailTrace_681704
  have hstable : (prefixWord ++ tailWord_681704).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681704).length < 2 ^ (prefixWord ++ tailWord_681704).sum := by decide
  have hdescent : baseEnd_681704 < baseStart_681704 := by decide
  rcases family_descends (prefixWord ++ tailWord_681704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681749 : List Nat := [1, 3, 2, 1, 2, 3, 1, 4, 4]
def baseStart_681749 : Nat := 118140960795 + 681749 * 2 ^ 59
def prefixEnd_681749 : Nat := 4983230072969 + 3 ^ 40 * 681749 * 2
def baseEnd_681749 : Nat := 155584410098737061156533

theorem tailTrace_681749 : CollatzResearch.WordTrace tailWord_681749 prefixEnd_681749 155584410098737061156533 := by
  unfold tailWord_681749
  simp only [CollatzResearch.WordTrace]
  refine ⟨24865428807147281304568301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16576952538098187536378867 24865428807147281304568301)
  ·
    refine ⟨9324535802680230489213113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24865428807147281304568301 9324535802680230489213113)
    ·
      refine ⟨6993401852010172866909835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9324535802680230489213113 6993401852010172866909835)
      ·
        refine ⟨10490102778015259300364753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6993401852010172866909835 10490102778015259300364753)
        ·
          refine ⟨7867577083511444475273565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10490102778015259300364753 7867577083511444475273565)
          ·
            refine ⟨2950341406316791678227587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7867577083511444475273565 2950341406316791678227587)
            ·
              refine ⟨4425512109475187517341381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2950341406316791678227587 4425512109475187517341381)
              ·
                refine ⟨829783520526597659501509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4425512109475187517341381 829783520526597659501509)
                ·
                  refine ⟨155584410098737061156533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 829783520526597659501509 155584410098737061156533)
                  ·
                    rfl

theorem cell21_681749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 4, 4].length) (baseStart_681749 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_681749 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_681749 prefixEnd_681749 := by exact prefixLift 681749
  have htrace : WordTrace (prefixWord ++ tailWord_681749) baseStart_681749 baseEnd_681749 := by
    simpa [prefixWord, tailWord_681749, baseEnd_681749] using wordTrace_append hprefix tailTrace_681749
  have hstable : (prefixWord ++ tailWord_681749).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681749).length < 2 ^ (prefixWord ++ tailWord_681749).sum := by decide
  have hdescent : baseEnd_681749 < baseStart_681749 := by decide
  rcases family_descends (prefixWord ++ tailWord_681749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681752 : List Nat := [2, 1, 2, 3, 1, 1, 6, 2, 3]
def baseStart_681752 : Nat := 118140960795 + 681752 * 2 ^ 59
def prefixEnd_681752 : Nat := 4983230072969 + 3 ^ 40 * 681752 * 2
def baseEnd_681752 : Nat := 155585094739609722606527

theorem tailTrace_681752 : CollatzResearch.WordTrace tailWord_681752 prefixEnd_681752 155585094739609722606527 := by
  unfold tailWord_681752
  simp only [CollatzResearch.WordTrace]
  refine ⟨12432769113068206408463755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16577025484090941877951673 12432769113068206408463755)
  ·
    refine ⟨18649153669602309612695633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12432769113068206408463755 18649153669602309612695633)
    ·
      refine ⟨13986865252201732209521725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18649153669602309612695633 13986865252201732209521725)
      ·
        refine ⟨5245074469575649578570647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13986865252201732209521725 5245074469575649578570647)
        ·
          refine ⟨7867611704363474367855971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5245074469575649578570647 7867611704363474367855971)
          ·
            refine ⟨11801417556545211551783957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7867611704363474367855971 11801417556545211551783957)
            ·
              refine ⟨553191447963056791489873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 11801417556545211551783957 553191447963056791489873)
              ·
                refine ⟨414893585972292593617405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 553191447963056791489873 414893585972292593617405)
                ·
                  refine ⟨155585094739609722606527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 414893585972292593617405 155585094739609722606527)
                  ·
                    rfl

theorem cell21_681752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 6, 2, 3].length) (baseStart_681752 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_681752 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_681752 prefixEnd_681752 := by exact prefixLift 681752
  have htrace : WordTrace (prefixWord ++ tailWord_681752) baseStart_681752 baseEnd_681752 := by
    simpa [prefixWord, tailWord_681752, baseEnd_681752] using wordTrace_append hprefix tailTrace_681752
  have hstable : (prefixWord ++ tailWord_681752).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681752).length < 2 ^ (prefixWord ++ tailWord_681752).sum := by decide
  have hdescent : baseEnd_681752 < baseStart_681752 := by decide
  rcases family_descends (prefixWord ++ tailWord_681752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681763 : List Nat := [1, 1, 1, 4, 2, 1, 5, 6]
def baseStart_681763 : Nat := 118140960795 + 681763 * 2 ^ 59
def prefixEnd_681763 : Nat := 4983230072969 + 3 ^ 40 * 681763 * 2
def baseEnd_681763 : Nat := 51862535029825382641057

theorem tailTrace_681763 : CollatzResearch.WordTrace tailWord_681763 prefixEnd_681763 51862535029825382641057 := by
  unfold tailWord_681763
  simp only [CollatzResearch.WordTrace]
  refine ⟨24865939429096561695577943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16577292952731041130385295 24865939429096561695577943)
  ·
    refine ⟨37298909143644842543366915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24865939429096561695577943 37298909143644842543366915)
    ·
      refine ⟨55948363715467263815050373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37298909143644842543366915 55948363715467263815050373)
      ·
        refine ⟨10490318196650111965321945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55948363715467263815050373 10490318196650111965321945)
        ·
          refine ⟨7867738647487583973991459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10490318196650111965321945 7867738647487583973991459)
          ·
            refine ⟨11801607971231375960987189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7867738647487583973991459 11801607971231375960987189)
            ·
              refine ⟨1106400747302941496342549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11801607971231375960987189 1106400747302941496342549)
              ·
                refine ⟨51862535029825382641057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1106400747302941496342549 51862535029825382641057)
                ·
                  rfl

theorem cell21_681763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 5, 6].length) (baseStart_681763 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_681763 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_681763 prefixEnd_681763 := by exact prefixLift 681763
  have htrace : WordTrace (prefixWord ++ tailWord_681763) baseStart_681763 baseEnd_681763 := by
    simpa [prefixWord, tailWord_681763, baseEnd_681763] using wordTrace_append hprefix tailTrace_681763
  have hstable : (prefixWord ++ tailWord_681763).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681763).length < 2 ^ (prefixWord ++ tailWord_681763).sum := by decide
  have hdescent : baseEnd_681763 < baseStart_681763 := by decide
  rcases family_descends (prefixWord ++ tailWord_681763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681918 : List Nat := [4, 2, 1, 1, 1, 4, 2, 2, 4]
def baseStart_681918 : Nat := 118140960795 + 681918 * 2 ^ 59
def prefixEnd_681918 : Nat := 4983230072969 + 3 ^ 40 * 681918 * 2
def baseEnd_681918 : Nat := 155622978201230322839521

theorem tailTrace_681918 : CollatzResearch.WordTrace tailWord_681918 prefixEnd_681918 155622978201230322839521 := by
  unfold tailWord_681918
  simp only [CollatzResearch.WordTrace]
  refine ⟨3108949092941877895933801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16581061829023348778313605 3108949092941877895933801)
  ·
    refine ⟨2331711819706408421950351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3108949092941877895933801 2331711819706408421950351)
    ·
      refine ⟨3497567729559612632925527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2331711819706408421950351 3497567729559612632925527)
      ·
        refine ⟨5246351594339418949388291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3497567729559612632925527 5246351594339418949388291)
        ·
          refine ⟨7869527391509128424082437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5246351594339418949388291 7869527391509128424082437)
          ·
            refine ⟨1475536385907961579515457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7869527391509128424082437 1475536385907961579515457)
            ·
              refine ⟨1106652289430971184636593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1475536385907961579515457 1106652289430971184636593)
              ·
                refine ⟨829989217073228388477445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1106652289430971184636593 829989217073228388477445)
                ·
                  refine ⟨155622978201230322839521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 829989217073228388477445 155622978201230322839521)
                  ·
                    rfl

theorem cell21_681918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 2, 2, 4].length) (baseStart_681918 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_681918 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_681918 prefixEnd_681918 := by exact prefixLift 681918
  have htrace : WordTrace (prefixWord ++ tailWord_681918) baseStart_681918 baseEnd_681918 := by
    simpa [prefixWord, tailWord_681918, baseEnd_681918] using wordTrace_append hprefix tailTrace_681918
  have hstable : (prefixWord ++ tailWord_681918).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681918).length < 2 ^ (prefixWord ++ tailWord_681918).sum := by decide
  have hdescent : baseEnd_681918 < baseStart_681918 := by decide
  rcases family_descends (prefixWord ++ tailWord_681918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681932 : List Nat := [2, 2, 1, 4, 1, 4, 1, 6]
def baseStart_681932 : Nat := 118140960795 + 681932 * 2 ^ 59
def prefixEnd_681932 : Nat := 4983230072969 + 3 ^ 40 * 681932 * 2
def baseEnd_681932 : Nat := 51875391063989803202053

theorem tailTrace_681932 : CollatzResearch.WordTrace tailWord_681932 prefixEnd_681932 51875391063989803202053 := by
  unfold tailWord_681932
  simp only [CollatzResearch.WordTrace]
  refine ⟨12436051682742151779240025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16581402243656202372320033 12436051682742151779240025)
  ·
    refine ⟨9327038762056613834430019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12436051682742151779240025 9327038762056613834430019)
    ·
      refine ⟨13990558143084920751645029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9327038762056613834430019 13990558143084920751645029)
      ·
        refine ⟨2623229651828422640933443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13990558143084920751645029 2623229651828422640933443)
        ·
          refine ⟨3934844477742633961400165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2623229651828422640933443 3934844477742633961400165)
          ·
            refine ⟨737783339576743867762531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3934844477742633961400165 737783339576743867762531)
            ·
              refine ⟨1106675009365115801643797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 737783339576743867762531 1106675009365115801643797)
              ·
                refine ⟨51875391063989803202053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1106675009365115801643797 51875391063989803202053)
                ·
                  rfl

theorem cell21_681932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 1, 6].length) (baseStart_681932 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_681932 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_681932 prefixEnd_681932 := by exact prefixLift 681932
  have htrace : WordTrace (prefixWord ++ tailWord_681932) baseStart_681932 baseEnd_681932 := by
    simpa [prefixWord, tailWord_681932, baseEnd_681932] using wordTrace_append hprefix tailTrace_681932
  have hstable : (prefixWord ++ tailWord_681932).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681932).length < 2 ^ (prefixWord ++ tailWord_681932).sum := by decide
  have hdescent : baseEnd_681932 < baseStart_681932 := by decide
  rcases family_descends (prefixWord ++ tailWord_681932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681949 : List Nat := [1, 4, 3, 1, 3, 1, 3, 5]
def baseStart_681949 : Nat := 118140960795 + 681949 * 2 ^ 59
def prefixEnd_681949 : Nat := 4983230072969 + 3 ^ 40 * 681949 * 2
def baseEnd_681949 : Nat := 51876684274527052607597

theorem tailTrace_681949 : CollatzResearch.WordTrace tailWord_681949 prefixEnd_681949 51876684274527052607597 := by
  unfold tailWord_681949
  simp only [CollatzResearch.WordTrace]
  refine ⟨24872723406422715461848901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16581815604281810307899267 24872723406422715461848901)
  ·
    refine ⟨4663635638704259149096669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24872723406422715461848901 4663635638704259149096669)
    ·
      refine ⟨1748863364514097180911251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4663635638704259149096669 1748863364514097180911251)
      ·
        refine ⟨2623295046771145771366877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1748863364514097180911251 2623295046771145771366877)
        ·
          refine ⟨983735642539179664262579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2623295046771145771366877 983735642539179664262579)
          ·
            refine ⟨1475603463808769496393869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 983735642539179664262579 1475603463808769496393869)
            ·
              refine ⟨553351298928288561147701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1475603463808769496393869 553351298928288561147701)
              ·
                refine ⟨51876684274527052607597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 553351298928288561147701 51876684274527052607597)
                ·
                  rfl

theorem cell21_681949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 3, 5].length) (baseStart_681949 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_681949 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_681949 prefixEnd_681949 := by exact prefixLift 681949
  have htrace : WordTrace (prefixWord ++ tailWord_681949) baseStart_681949 baseEnd_681949 := by
    simpa [prefixWord, tailWord_681949, baseEnd_681949] using wordTrace_append hprefix tailTrace_681949
  have hstable : (prefixWord ++ tailWord_681949).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681949).length < 2 ^ (prefixWord ++ tailWord_681949).sum := by decide
  have hdescent : baseEnd_681949 < baseStart_681949 := by decide
  rcases family_descends (prefixWord ++ tailWord_681949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681960 : List Nat := [2, 1, 4, 1, 1, 1, 1, 4, 6]
def baseStart_681960 : Nat := 118140960795 + 681960 * 2 ^ 59
def prefixEnd_681960 : Nat := 4983230072969 + 3 ^ 40 * 681960 * 2
def baseEnd_681960 : Nat := 155632563173447583139435

theorem tailTrace_681960 : CollatzResearch.WordTrace tailWord_681960 prefixEnd_681960 155632563173447583139435 := by
  unfold tailWord_681960
  simp only [CollatzResearch.WordTrace]
  refine ⟨12436562304691432170249667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16582083072921909560332889 12436562304691432170249667)
  ·
    refine ⟨18654843457037148255374501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12436562304691432170249667 18654843457037148255374501)
    ·
      refine ⟨3497783148194465297882719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18654843457037148255374501 3497783148194465297882719)
      ·
        refine ⟨5246674722291697946824079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3497783148194465297882719 5246674722291697946824079)
        ·
          refine ⟨7870012083437546920236119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5246674722291697946824079 7870012083437546920236119)
          ·
            refine ⟨11805018125156320380354179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7870012083437546920236119 11805018125156320380354179)
            ·
              refine ⟨17707527187734480570531269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11805018125156320380354179 17707527187734480570531269)
              ·
                refine ⟨3320161347700215106974613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17707527187734480570531269 3320161347700215106974613)
                ·
                  refine ⟨155632563173447583139435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3320161347700215106974613 155632563173447583139435)
                  ·
                    rfl

theorem cell21_681960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 4, 6].length) (baseStart_681960 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_681960 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_681960 prefixEnd_681960 := by exact prefixLift 681960
  have htrace : WordTrace (prefixWord ++ tailWord_681960) baseStart_681960 baseEnd_681960 := by
    simpa [prefixWord, tailWord_681960, baseEnd_681960] using wordTrace_append hprefix tailTrace_681960
  have hstable : (prefixWord ++ tailWord_681960).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681960).length < 2 ^ (prefixWord ++ tailWord_681960).sum := by decide
  have hdescent : baseEnd_681960 < baseStart_681960 := by decide
  rcases family_descends (prefixWord ++ tailWord_681960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681977 : List Nat := [1, 2, 1, 3, 1, 4, 3, 2, 4]
def baseStart_681977 : Nat := 118140960795 + 681977 * 2 ^ 59
def prefixEnd_681977 : Nat := 4983230072969 + 3 ^ 40 * 681977 * 2
def baseEnd_681977 : Nat := 155636442805059331356067

theorem tailTrace_681977 : CollatzResearch.WordTrace tailWord_681977 prefixEnd_681977 155636442805059331356067 := by
  unfold tailWord_681977
  simp only [CollatzResearch.WordTrace]
  refine ⟨24873744650321276243868185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16582496433547517495912123 24873744650321276243868185)
  ·
    refine ⟨18655308487740957182901139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24873744650321276243868185 18655308487740957182901139)
    ·
      refine ⟨27982962731611435774351709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18655308487740957182901139 27982962731611435774351709)
      ·
        refine ⟨10493611024354288415381891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27982962731611435774351709 10493611024354288415381891)
        ·
          refine ⟨15740416536531432623072837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10493611024354288415381891 15740416536531432623072837)
          ·
            refine ⟨2951328100599643616826157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15740416536531432623072837 2951328100599643616826157)
            ·
              refine ⟨1106748037724866356309809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2951328100599643616826157 1106748037724866356309809)
              ·
                refine ⟨830061028293649767232357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1106748037724866356309809 830061028293649767232357)
                ·
                  refine ⟨155636442805059331356067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 830061028293649767232357 155636442805059331356067)
                  ·
                    rfl

theorem cell21_681977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 3, 2, 4].length) (baseStart_681977 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_681977 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_681977 prefixEnd_681977 := by exact prefixLift 681977
  have htrace : WordTrace (prefixWord ++ tailWord_681977) baseStart_681977 baseEnd_681977 := by
    simpa [prefixWord, tailWord_681977, baseEnd_681977] using wordTrace_append hprefix tailTrace_681977
  have hstable : (prefixWord ++ tailWord_681977).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681977).length < 2 ^ (prefixWord ++ tailWord_681977).sum := by decide
  have hdescent : baseEnd_681977 < baseStart_681977 := by decide
  rcases family_descends (prefixWord ++ tailWord_681977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682090 : List Nat := [3, 1, 3, 2, 4, 1, 2, 2, 3]
def baseStart_682090 : Nat := 118140960795 + 682090 * 2 ^ 59
def prefixEnd_682090 : Nat := 4983230072969 + 3 ^ 40 * 682090 * 2
def baseEnd_682090 : Nat := 155662230944596245972503

theorem tailTrace_682090 : CollatzResearch.WordTrace tailWord_682090 prefixEnd_682090 155662230944596245972503 := by
  unfold tailWord_682090
  simp only [CollatzResearch.WordTrace]
  refine ⟨6219466524727974135682931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16585244065941264361821149 6219466524727974135682931)
  ·
    refine ⟨9329199787091961203524397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6219466524727974135682931 9329199787091961203524397)
    ·
      refine ⟨3498449920159485451321649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9329199787091961203524397 3498449920159485451321649)
      ·
        refine ⟨2623837440119614088491237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3498449920159485451321649 2623837440119614088491237)
        ·
          refine ⟨491969520022427641592107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2623837440119614088491237 491969520022427641592107)
          ·
            refine ⟨737954280033641462388161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 491969520022427641592107 737954280033641462388161)
            ·
              refine ⟨553465710025231096791121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 737954280033641462388161 553465710025231096791121)
              ·
                refine ⟨415099282518923322593341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 553465710025231096791121 415099282518923322593341)
                ·
                  refine ⟨155662230944596245972503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 415099282518923322593341 155662230944596245972503)
                  ·
                    rfl

theorem cell21_682090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 2, 2, 3].length) (baseStart_682090 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_682090 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_682090 prefixEnd_682090 := by exact prefixLift 682090
  have htrace : WordTrace (prefixWord ++ tailWord_682090) baseStart_682090 baseEnd_682090 := by
    simpa [prefixWord, tailWord_682090, baseEnd_682090] using wordTrace_append hprefix tailTrace_682090
  have hstable : (prefixWord ++ tailWord_682090).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682090).length < 2 ^ (prefixWord ++ tailWord_682090).sum := by decide
  have hdescent : baseEnd_682090 < baseStart_682090 := by decide
  rcases family_descends (prefixWord ++ tailWord_682090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682143 : List Nat := [1, 1, 2, 6, 1, 2, 8]
def baseStart_682143 : Nat := 118140960795 + 682143 * 2 ^ 59
def prefixEnd_682143 : Nat := 4983230072969 + 3 ^ 40 * 682143 * 2
def baseEnd_682143 : Nat := 17297147362964436843229

theorem tailTrace_682143 : CollatzResearch.WordTrace tailWord_682143 prefixEnd_682143 17297147362964436843229 := by
  unfold tailWord_682143
  simp only [CollatzResearch.WordTrace]
  refine ⟨24879799167719886594411083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16586532778479924396274055 24879799167719886594411083)
  ·
    refine ⟨37319698751579829891616625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24879799167719886594411083 37319698751579829891616625)
    ·
      refine ⟨27989774063684872418712469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37319698751579829891616625 27989774063684872418712469)
      ·
        refine ⟨1312020659235228394627147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 27989774063684872418712469 1312020659235228394627147)
        ·
          refine ⟨1968030988852842591940721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1312020659235228394627147 1968030988852842591940721)
          ·
            refine ⟨1476023241639631943955541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1968030988852842591940721 1476023241639631943955541)
            ·
              refine ⟨17297147362964436843229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1476023241639631943955541 17297147362964436843229)
              ·
                rfl

theorem cell21_682143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 8].length) (baseStart_682143 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_682143 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_682143 prefixEnd_682143 := by exact prefixLift 682143
  have htrace : WordTrace (prefixWord ++ tailWord_682143) baseStart_682143 baseEnd_682143 := by
    simpa [prefixWord, tailWord_682143, baseEnd_682143] using wordTrace_append hprefix tailTrace_682143
  have hstable : (prefixWord ++ tailWord_682143).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682143).length < 2 ^ (prefixWord ++ tailWord_682143).sum := by decide
  have hdescent : baseEnd_682143 < baseStart_682143 := by decide
  rcases family_descends (prefixWord ++ tailWord_682143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682146 : List Nat := [3, 3, 1, 3, 1, 1, 3, 2, 4]
def baseStart_682146 : Nat := 118140960795 + 682146 * 2 ^ 59
def prefixEnd_682146 : Nat := 4983230072969 + 3 ^ 40 * 682146 * 2
def baseEnd_682146 : Nat := 155675010907552593039055

theorem tailTrace_682146 : CollatzResearch.WordTrace tailWord_682146 prefixEnd_682146 155675010907552593039055 := by
  unfold tailWord_682146
  simp only [CollatzResearch.WordTrace]
  refine ⟨6219977146677254526692573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16586605724472678737846861 6219977146677254526692573)
  ·
    refine ⟨2332491430003970447509715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6219977146677254526692573 2332491430003970447509715)
    ·
      refine ⟨3498737145005955671264573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2332491430003970447509715 3498737145005955671264573)
      ·
        refine ⟨1312026429377233376724215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3498737145005955671264573 1312026429377233376724215)
        ·
          refine ⟨1968039644065850065086323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1312026429377233376724215 1968039644065850065086323)
          ·
            refine ⟨2952059466098775097629485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1968039644065850065086323 2952059466098775097629485)
            ·
              refine ⟨1107022299787040661611057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2952059466098775097629485 1107022299787040661611057)
              ·
                refine ⟨830266724840280496208293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1107022299787040661611057 830266724840280496208293)
                ·
                  refine ⟨155675010907552593039055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 830266724840280496208293 155675010907552593039055)
                  ·
                    rfl

theorem cell21_682146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 3, 2, 4].length) (baseStart_682146 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_682146 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_682146 prefixEnd_682146 := by exact prefixLift 682146
  have htrace : WordTrace (prefixWord ++ tailWord_682146) baseStart_682146 baseEnd_682146 := by
    simpa [prefixWord, tailWord_682146, baseEnd_682146] using wordTrace_append hprefix tailTrace_682146
  have hstable : (prefixWord ++ tailWord_682146).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682146).length < 2 ^ (prefixWord ++ tailWord_682146).sum := by decide
  have hdescent : baseEnd_682146 < baseStart_682146 := by decide
  rcases family_descends (prefixWord ++ tailWord_682146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682202 : List Nat := [3, 1, 1, 2, 2, 1, 11]
def baseStart_682202 : Nat := 118140960795 + 682202 * 2 ^ 59
def prefixEnd_682202 : Nat := 4983230072969 + 3 ^ 40 * 682202 * 2
def baseEnd_682202 : Nat := 17298643430056548900623

theorem tailTrace_682202 : CollatzResearch.WordTrace tailWord_682202 prefixEnd_682202 17298643430056548900623 := by
  unfold tailWord_682202
  simp only [CollatzResearch.WordTrace]
  refine ⟨6220487768626534917702215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16587967383004093113872573 6220487768626534917702215)
  ·
    refine ⟨9330731652939802376553323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6220487768626534917702215 9330731652939802376553323)
    ·
      refine ⟨13996097479409703564829985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9330731652939802376553323 13996097479409703564829985)
      ·
        refine ⟨10497073109557277673622489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13996097479409703564829985 10497073109557277673622489)
        ·
          refine ⟨7872804832167958255216867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10497073109557277673622489 7872804832167958255216867)
          ·
            refine ⟨11809207248251937382825301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7872804832167958255216867 11809207248251937382825301)
            ·
              refine ⟨17298643430056548900623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 11809207248251937382825301 17298643430056548900623)
              ·
                rfl

theorem cell21_682202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 11].length) (baseStart_682202 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_682202 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_682202 prefixEnd_682202 := by exact prefixLift 682202
  have htrace : WordTrace (prefixWord ++ tailWord_682202) baseStart_682202 baseEnd_682202 := by
    simpa [prefixWord, tailWord_682202, baseEnd_682202] using wordTrace_append hprefix tailTrace_682202
  have hstable : (prefixWord ++ tailWord_682202).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682202).length < 2 ^ (prefixWord ++ tailWord_682202).sum := by decide
  have hdescent : baseEnd_682202 < baseStart_682202 := by decide
  rcases family_descends (prefixWord ++ tailWord_682202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682205 : List Nat := [1, 4, 3, 2, 1, 1, 2, 1, 6]
def baseStart_682205 : Nat := 118140960795 + 682205 * 2 ^ 59
def prefixEnd_682205 : Nat := 4983230072969 + 3 ^ 40 * 682205 * 2
def baseEnd_682205 : Nat := 155688475511381601555601

theorem tailTrace_682205 : CollatzResearch.WordTrace tailWord_682205 prefixEnd_682205 155688475511381601555601 := by
  unfold tailWord_682205
  simp only [CollatzResearch.WordTrace]
  refine ⟨24882060493495271183168069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16588040328996847455445379 24882060493495271183168069)
  ·
    refine ⟨4665386342530363346844013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24882060493495271183168069 4665386342530363346844013)
    ·
      refine ⟨1749519878448886255066505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4665386342530363346844013 1749519878448886255066505)
      ·
        refine ⟨1312139908836664691299879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1749519878448886255066505 1312139908836664691299879)
        ·
          refine ⟨1968209863254997036949819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1312139908836664691299879 1968209863254997036949819)
          ·
            refine ⟨2952314794882495555424729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1968209863254997036949819 2952314794882495555424729)
            ·
              refine ⟨2214236096161871666568547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2952314794882495555424729 2214236096161871666568547)
              ·
                refine ⟨3321354144242807499852821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2214236096161871666568547 3321354144242807499852821)
                ·
                  refine ⟨155688475511381601555601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3321354144242807499852821 155688475511381601555601)
                  ·
                    rfl

theorem cell21_682205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 1, 6].length) (baseStart_682205 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_682205 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_682205 prefixEnd_682205 := by exact prefixLift 682205
  have htrace : WordTrace (prefixWord ++ tailWord_682205) baseStart_682205 baseEnd_682205 := by
    simpa [prefixWord, tailWord_682205, baseEnd_682205] using wordTrace_append hprefix tailTrace_682205
  have hstable : (prefixWord ++ tailWord_682205).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682205).length < 2 ^ (prefixWord ++ tailWord_682205).sum := by decide
  have hdescent : baseEnd_682205 < baseStart_682205 := by decide
  rcases family_descends (prefixWord ++ tailWord_682205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682267 : List Nat := [1, 1, 1, 1, 1, 1, 10, 2, 3]
def baseStart_682267 : Nat := 118140960795 + 682267 * 2 ^ 59
def prefixEnd_682267 : Nat := 4983230072969 + 3 ^ 40 * 682267 * 2
def baseEnd_682267 : Nat := 155702624756083271522141

theorem tailTrace_682267 : CollatzResearch.WordTrace tailWord_682267 prefixEnd_682267 155702624756083271522141 := by
  unfold tailWord_682267
  simp only [CollatzResearch.WordTrace]
  refine ⟨24884321819270655771925055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16589547879513770514616703 24884321819270655771925055)
  ·
    refine ⟨37326482728905983657887583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24884321819270655771925055 37326482728905983657887583)
    ·
      refine ⟨55989724093358975486831375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37326482728905983657887583 55989724093358975486831375)
      ·
        refine ⟨83984586140038463230247063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55989724093358975486831375 83984586140038463230247063)
        ·
          refine ⟨125976879210057694845370595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83984586140038463230247063 125976879210057694845370595)
          ·
            refine ⟨188965318815086542268055893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125976879210057694845370595 188965318815086542268055893)
            ·
              refine ⟨553609332466073854300945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 188965318815086542268055893 553609332466073854300945)
              ·
                refine ⟨415206999349555390725709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 553609332466073854300945 415206999349555390725709)
                ·
                  refine ⟨155702624756083271522141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 415206999349555390725709 155702624756083271522141)
                  ·
                    rfl

theorem cell21_682267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 10, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 10, 2, 3].length) (baseStart_682267 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_682267 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_682267 prefixEnd_682267 := by exact prefixLift 682267
  have htrace : WordTrace (prefixWord ++ tailWord_682267) baseStart_682267 baseEnd_682267 := by
    simpa [prefixWord, tailWord_682267, baseEnd_682267] using wordTrace_append hprefix tailTrace_682267
  have hstable : (prefixWord ++ tailWord_682267).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682267).length < 2 ^ (prefixWord ++ tailWord_682267).sum := by decide
  have hdescent : baseEnd_682267 < baseStart_682267 := by decide
  rcases family_descends (prefixWord ++ tailWord_682267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682371 : List Nat := [1, 1, 1, 3, 6, 2, 7]
def baseStart_682371 : Nat := 118140960795 + 682371 * 2 ^ 59
def prefixEnd_682371 : Nat := 4983230072969 + 3 ^ 40 * 682371 * 2
def baseEnd_682371 : Nat := 17302928774778022420955

theorem tailTrace_682371 : CollatzResearch.WordTrace tailWord_682371 prefixEnd_682371 17302928774778022420955 := by
  unfold tailWord_682371
  simp only [CollatzResearch.WordTrace]
  refine ⟨24888115010893881533710967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16592076673929254355807311 24888115010893881533710967)
  ·
    refine ⟨37332172516340822300566451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24888115010893881533710967 37332172516340822300566451)
    ·
      refine ⟨55998258774511233450849677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37332172516340822300566451 55998258774511233450849677)
      ·
        refine ⟨20999347040441712544068629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55998258774511233450849677 20999347040441712544068629)
        ·
          refine ⟨984344392520705275503217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 20999347040441712544068629 984344392520705275503217)
          ·
            refine ⟨738258294390528956627413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 984344392520705275503217 738258294390528956627413)
            ·
              refine ⟨17302928774778022420955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 738258294390528956627413 17302928774778022420955)
              ·
                rfl

theorem cell21_682371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 7].length) (baseStart_682371 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_682371 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_682371 prefixEnd_682371 := by exact prefixLift 682371
  have htrace : WordTrace (prefixWord ++ tailWord_682371) baseStart_682371 baseEnd_682371 := by
    simpa [prefixWord, tailWord_682371, baseEnd_682371] using wordTrace_append hprefix tailTrace_682371
  have hstable : (prefixWord ++ tailWord_682371).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682371).length < 2 ^ (prefixWord ++ tailWord_682371).sum := by decide
  have hdescent : baseEnd_682371 < baseStart_682371 := by decide
  rcases family_descends (prefixWord ++ tailWord_682371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682388 : List Nat := [2, 4, 2, 1, 3, 1, 2, 6]
def baseStart_682388 : Nat := 118140960795 + 682388 * 2 ^ 59
def prefixEnd_682388 : Nat := 4983230072969 + 3 ^ 40 * 682388 * 2
def baseEnd_682388 : Nat := 51910079534871316668409

theorem tailTrace_682388 : CollatzResearch.WordTrace tailWord_682388 prefixEnd_682388 51910079534871316668409 := by
  unfold tailWord_682388
  simp only [CollatzResearch.WordTrace]
  refine ⟨12444367525916146718539909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16592490034554862291386545 12444367525916146718539909)
  ·
    refine ⟨2333318911109277509726233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12444367525916146718539909 2333318911109277509726233)
    ·
      refine ⟨1749989183331958132294675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2333318911109277509726233 1749989183331958132294675)
      ·
        refine ⟨2624983774997937198442013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1749989183331958132294675 2624983774997937198442013)
        ·
          refine ⟨984368915624226449415755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2624983774997937198442013 984368915624226449415755)
          ·
            refine ⟨1476553373436339674123633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 984368915624226449415755 1476553373436339674123633)
            ·
              refine ⟨1107415030077254755592725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1476553373436339674123633 1107415030077254755592725)
              ·
                refine ⟨51910079534871316668409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1107415030077254755592725 51910079534871316668409)
                ·
                  rfl

theorem cell21_682388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 2, 6].length) (baseStart_682388 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_682388 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_682388 prefixEnd_682388 := by exact prefixLift 682388
  have htrace : WordTrace (prefixWord ++ tailWord_682388) baseStart_682388 baseEnd_682388 := by
    simpa [prefixWord, tailWord_682388, baseEnd_682388] using wordTrace_append hprefix tailTrace_682388
  have hstable : (prefixWord ++ tailWord_682388).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682388).length < 2 ^ (prefixWord ++ tailWord_682388).sum := by decide
  have hdescent : baseEnd_682388 < baseStart_682388 := by decide
  rcases family_descends (prefixWord ++ tailWord_682388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682436 : List Nat := [2, 3, 3, 2, 2, 1, 1, 4, 3]
def baseStart_682436 : Nat := 118140960795 + 682436 * 2 ^ 59
def prefixEnd_682436 : Nat := 4983230072969 + 3 ^ 40 * 682436 * 2
def baseEnd_682436 : Nat := 155741192858576533205129

theorem tailTrace_682436 : CollatzResearch.WordTrace tailWord_682436 prefixEnd_682436 155741192858576533205129 := by
  unfold tailWord_682436
  simp only [CollatzResearch.WordTrace]
  refine ⟨12445242877829198817413581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16593657170438931756551441 12445242877829198817413581)
  ·
    refine ⟨4666966079185949556530093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12445242877829198817413581 4666966079185949556530093)
    ·
      refine ⟨1750112279694731083698785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4666966079185949556530093 1750112279694731083698785)
      ·
        refine ⟨1312584209771048312774089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1750112279694731083698785 1312584209771048312774089)
        ·
          refine ⟨984438157328286234580567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1312584209771048312774089 984438157328286234580567)
          ·
            refine ⟨1476657235992429351870851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 984438157328286234580567 1476657235992429351870851)
            ·
              refine ⟨2214985853988644027806277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1476657235992429351870851 2214985853988644027806277)
              ·
                refine ⟨415309847622870755213677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2214985853988644027806277 415309847622870755213677)
                ·
                  refine ⟨155741192858576533205129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 415309847622870755213677 155741192858576533205129)
                  ·
                    rfl

theorem cell21_682436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 4, 3].length) (baseStart_682436 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_682436 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_682436 prefixEnd_682436 := by exact prefixLift 682436
  have htrace : WordTrace (prefixWord ++ tailWord_682436) baseStart_682436 baseEnd_682436 := by
    simpa [prefixWord, tailWord_682436, baseEnd_682436] using wordTrace_append hprefix tailTrace_682436
  have hstable : (prefixWord ++ tailWord_682436).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682436).length < 2 ^ (prefixWord ++ tailWord_682436).sum := by decide
  have hdescent : baseEnd_682436 < baseStart_682436 := by decide
  rcases family_descends (prefixWord ++ tailWord_682436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682475 : List Nat := [1, 1, 1, 1, 2, 3, 4, 2, 6]
def baseStart_682475 : Nat := 118140960795 + 682475 * 2 ^ 59
def prefixEnd_682475 : Nat := 4983230072969 + 3 ^ 40 * 682475 * 2
def baseEnd_682475 : Nat := 155750093189921132055049

theorem tailTrace_682475 : CollatzResearch.WordTrace tailWord_682475 prefixEnd_682475 155750093189921132055049 := by
  unfold tailWord_682475
  simp only [CollatzResearch.WordTrace]
  refine ⟨24891908202517107295496879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16594605468344738196997919 24891908202517107295496879)
  ·
    refine ⟨37337862303775660943245319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24891908202517107295496879 37337862303775660943245319)
    ·
      refine ⟨56006793455663491414867979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37337862303775660943245319 56006793455663491414867979)
      ·
        refine ⟨84010190183495237122301969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56006793455663491414867979 84010190183495237122301969)
        ·
          refine ⟨63007642637621427841726477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84010190183495237122301969 63007642637621427841726477)
          ·
            refine ⟨23627865989108035440647429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63007642637621427841726477 23627865989108035440647429)
            ·
              refine ⟨4430224872957756645121393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23627865989108035440647429 4430224872957756645121393)
              ·
                refine ⟨3322668654718317483841045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4430224872957756645121393 3322668654718317483841045)
                ·
                  refine ⟨155750093189921132055049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3322668654718317483841045 155750093189921132055049)
                  ·
                    rfl

theorem cell21_682475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 2, 6].length) (baseStart_682475 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_682475 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_682475 prefixEnd_682475 := by exact prefixLift 682475
  have htrace : WordTrace (prefixWord ++ tailWord_682475) baseStart_682475 baseEnd_682475 := by
    simpa [prefixWord, tailWord_682475, baseEnd_682475] using wordTrace_append hprefix tailTrace_682475
  have hstable : (prefixWord ++ tailWord_682475).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682475).length < 2 ^ (prefixWord ++ tailWord_682475).sum := by decide
  have hdescent : baseEnd_682475 < baseStart_682475 := by decide
  rcases family_descends (prefixWord ++ tailWord_682475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682506 : List Nat := [3, 1, 2, 2, 2, 1, 2, 8]
def baseStart_682506 : Nat := 118140960795 + 682506 * 2 ^ 59
def prefixEnd_682506 : Nat := 4983230072969 + 3 ^ 40 * 682506 * 2
def baseEnd_682506 : Nat := 51919055937423989012773

theorem tailTrace_682506 : CollatzResearch.WordTrace tailWord_682506 prefixEnd_682506 51919055937423989012773 := by
  unfold tailWord_682506
  simp only [CollatzResearch.WordTrace]
  refine ⟨6223259716351199897468843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16595359243603199726583581 6223259716351199897468843)
  ·
    refine ⟨9334889574526799846203265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6223259716351199897468843 9334889574526799846203265)
    ·
      refine ⟨7001167180895099884652449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9334889574526799846203265 7001167180895099884652449)
      ·
        refine ⟨5250875385671324913489337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7001167180895099884652449 5250875385671324913489337)
        ·
          refine ⟨3938156539253493685117003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5250875385671324913489337 3938156539253493685117003)
          ·
            refine ⟨5907234808880240527675505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3938156539253493685117003 5907234808880240527675505)
            ·
              refine ⟨4430426106660180395756629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5907234808880240527675505 4430426106660180395756629)
              ·
                refine ⟨51919055937423989012773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4430426106660180395756629 51919055937423989012773)
                ·
                  rfl

theorem cell21_682506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 8].length) (baseStart_682506 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_682506 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_682506 prefixEnd_682506 := by exact prefixLift 682506
  have htrace : WordTrace (prefixWord ++ tailWord_682506) baseStart_682506 baseEnd_682506 := by
    simpa [prefixWord, tailWord_682506, baseEnd_682506] using wordTrace_append hprefix tailTrace_682506
  have hstable : (prefixWord ++ tailWord_682506).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682506).length < 2 ^ (prefixWord ++ tailWord_682506).sum := by decide
  have hdescent : baseEnd_682506 < baseStart_682506 := by decide
  rcases family_descends (prefixWord ++ tailWord_682506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682551 : List Nat := [1, 1, 3, 1, 2, 3, 1, 3, 6]
def baseStart_682551 : Nat := 118140960795 + 682551 * 2 ^ 59
def prefixEnd_682551 : Nat := 4983230072969 + 3 ^ 40 * 682551 * 2
def baseEnd_682551 : Nat := 155767437425361888788227

theorem tailTrace_682551 : CollatzResearch.WordTrace tailWord_682551 prefixEnd_682551 155767437425361888788227 := by
  unfold tailWord_682551
  simp only [CollatzResearch.WordTrace]
  refine ⟨24894680150241772275263507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16596453433494514850175671 24894680150241772275263507)
  ·
    refine ⟨37342020225362658412895261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24894680150241772275263507 37342020225362658412895261)
    ·
      refine ⟨14003257584510996904835723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37342020225362658412895261 14003257584510996904835723)
      ·
        refine ⟨21004886376766495357253585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14003257584510996904835723 21004886376766495357253585)
        ·
          refine ⟨15753664782574871517940189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21004886376766495357253585 15753664782574871517940189)
          ·
            refine ⟨5907624293465576819227571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15753664782574871517940189 5907624293465576819227571)
            ·
              refine ⟨8861436440198365228841357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5907624293465576819227571 8861436440198365228841357)
              ·
                refine ⟨3323038665074386960815509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8861436440198365228841357 3323038665074386960815509)
                ·
                  refine ⟨155767437425361888788227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3323038665074386960815509 155767437425361888788227)
                  ·
                    rfl

theorem cell21_682551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 3, 6].length) (baseStart_682551 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_682551 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_682551 prefixEnd_682551 := by exact prefixLift 682551
  have htrace : WordTrace (prefixWord ++ tailWord_682551) baseStart_682551 baseEnd_682551 := by
    simpa [prefixWord, tailWord_682551, baseEnd_682551] using wordTrace_append hprefix tailTrace_682551
  have hstable : (prefixWord ++ tailWord_682551).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682551).length < 2 ^ (prefixWord ++ tailWord_682551).sum := by decide
  have hdescent : baseEnd_682551 < baseStart_682551 := by decide
  rcases family_descends (prefixWord ++ tailWord_682551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682554 : List Nat := [3, 1, 1, 1, 3, 5, 1, 1, 5]
def baseStart_682554 : Nat := 118140960795 + 682554 * 2 ^ 59
def prefixEnd_682554 : Nat := 4983230072969 + 3 ^ 40 * 682554 * 2
def baseEnd_682554 : Nat := 155768122066234550238221

theorem tailTrace_682554 : CollatzResearch.WordTrace tailWord_682554 prefixEnd_682554 155768122066234550238221 := by
  unfold tailWord_682554
  simp only [CollatzResearch.WordTrace]
  refine ⟨6223697392307725946905679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16596526379487269191748477 6223697392307725946905679)
  ·
    refine ⟨9335546088461588920358519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6223697392307725946905679 9335546088461588920358519)
    ·
      refine ⟨14003319132692383380537779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9335546088461588920358519 14003319132692383380537779)
      ·
        refine ⟨21004978699038575070806669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14003319132692383380537779 21004978699038575070806669)
        ·
          refine ⟨7876867012139465651552501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21004978699038575070806669 7876867012139465651552501)
          ·
            refine ⟨738456282388074904833047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7876867012139465651552501 738456282388074904833047)
            ·
              refine ⟨1107684423582112357249571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 738456282388074904833047 1107684423582112357249571)
              ·
                refine ⟨1661526635373168535874357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1107684423582112357249571 1661526635373168535874357)
                ·
                  refine ⟨155768122066234550238221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1661526635373168535874357 155768122066234550238221)
                  ·
                    rfl

theorem cell21_682554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 1, 1, 5].length) (baseStart_682554 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_682554 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_682554 prefixEnd_682554 := by exact prefixLift 682554
  have htrace : WordTrace (prefixWord ++ tailWord_682554) baseStart_682554 baseEnd_682554 := by
    simpa [prefixWord, tailWord_682554, baseEnd_682554] using wordTrace_append hprefix tailTrace_682554
  have hstable : (prefixWord ++ tailWord_682554).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682554).length < 2 ^ (prefixWord ++ tailWord_682554).sum := by decide
  have hdescent : baseEnd_682554 < baseStart_682554 := by decide
  rcases family_descends (prefixWord ++ tailWord_682554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682692 : List Nat := [2, 3, 3, 1, 1, 4, 2, 5]
def baseStart_682692 : Nat := 118140960795 + 682692 * 2 ^ 59
def prefixEnd_682692 : Nat := 4983230072969 + 3 ^ 40 * 682692 * 2
def baseEnd_682692 : Nat := 51933205182125658979313

theorem tailTrace_682692 : CollatzResearch.WordTrace tailWord_682692 prefixEnd_682692 51933205182125658979313 := by
  unfold tailWord_682692
  simp only [CollatzResearch.WordTrace]
  refine ⟨12449911421365476678073165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16599881895153968904097553 12449911421365476678073165)
  ·
    refine ⟨4668716783012053754277437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12449911421365476678073165 4668716783012053754277437)
    ·
      refine ⟨1750768793629520157854039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4668716783012053754277437 1750768793629520157854039)
      ·
        refine ⟨2626153190444280236781059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1750768793629520157854039 2626153190444280236781059)
        ·
          refine ⟨3939229785666420355171589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2626153190444280236781059 3939229785666420355171589)
          ·
            refine ⟨738605584812453816594673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3939229785666420355171589 738605584812453816594673)
            ·
              refine ⟨553954188609340362446005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 738605584812453816594673 553954188609340362446005)
              ·
                refine ⟨51933205182125658979313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 553954188609340362446005 51933205182125658979313)
                ·
                  rfl

theorem cell21_682692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 2, 5].length) (baseStart_682692 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_682692 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_682692 prefixEnd_682692 := by exact prefixLift 682692
  have htrace : WordTrace (prefixWord ++ tailWord_682692) baseStart_682692 baseEnd_682692 := by
    simpa [prefixWord, tailWord_682692, baseEnd_682692] using wordTrace_append hprefix tailTrace_682692
  have hstable : (prefixWord ++ tailWord_682692).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682692).length < 2 ^ (prefixWord ++ tailWord_682692).sum := by decide
  have hdescent : baseEnd_682692 < baseStart_682692 := by decide
  rcases family_descends (prefixWord ++ tailWord_682692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682734 : List Nat := [4, 1, 2, 1, 1, 3, 1, 8]
def baseStart_682734 : Nat := 118140960795 + 682734 * 2 ^ 59
def prefixEnd_682734 : Nat := 4983230072969 + 3 ^ 40 * 682734 * 2
def baseEnd_682734 : Nat := 51936400172864745745951

theorem tailTrace_682734 : CollatzResearch.WordTrace tailWord_682734 prefixEnd_682734 51936400172864745745951 := by
  unfold tailWord_682734
  simp only [CollatzResearch.WordTrace]
  refine ⟨3112669338572349316146907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16600903139052529686116837 3112669338572349316146907)
  ·
    refine ⟨4669004007858523974220361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3112669338572349316146907 4669004007858523974220361)
    ·
      refine ⟨3501753005893892980665271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4669004007858523974220361 3501753005893892980665271)
      ·
        refine ⟨5252629508840839470997907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3501753005893892980665271 5252629508840839470997907)
        ·
          refine ⟨7878944263261259206496861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5252629508840839470997907 7878944263261259206496861)
          ·
            refine ⟨2954604098722972202436323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7878944263261259206496861 2954604098722972202436323)
            ·
              refine ⟨4431906148084458303654485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2954604098722972202436323 4431906148084458303654485)
              ·
                refine ⟨51936400172864745745951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4431906148084458303654485 51936400172864745745951)
                ·
                  rfl

theorem cell21_682734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 8].length) (baseStart_682734 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_682734 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_682734 prefixEnd_682734 := by exact prefixLift 682734
  have htrace : WordTrace (prefixWord ++ tailWord_682734) baseStart_682734 baseEnd_682734 := by
    simpa [prefixWord, tailWord_682734, baseEnd_682734] using wordTrace_append hprefix tailTrace_682734
  have hstable : (prefixWord ++ tailWord_682734).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682734).length < 2 ^ (prefixWord ++ tailWord_682734).sum := by decide
  have hdescent : baseEnd_682734 < baseStart_682734 := by decide
  rcases family_descends (prefixWord ++ tailWord_682734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682824 : List Nat := [2, 1, 3, 1, 1, 3, 1, 2, 7]
def baseStart_682824 : Nat := 118140960795 + 682824 * 2 ^ 59
def prefixEnd_682824 : Nat := 4983230072969 + 3 ^ 40 * 682824 * 2
def baseEnd_682824 : Nat := 155829739744774080737669

theorem tailTrace_682824 : CollatzResearch.WordTrace tailWord_682824 prefixEnd_682824 155829739744774080737669 := by
  unfold tailWord_682824
  simp only [CollatzResearch.WordTrace]
  refine ⟨12452318639126369949975763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16603091518835159933301017 12452318639126369949975763)
  ·
    refine ⟨18678477958689554924963645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12452318639126369949975763 18678477958689554924963645)
    ·
      refine ⟨7004429234508583096861367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18678477958689554924963645 7004429234508583096861367)
      ·
        refine ⟨10506643851762874645292051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7004429234508583096861367 10506643851762874645292051)
        ·
          refine ⟨15759965777644311967938077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10506643851762874645292051 15759965777644311967938077)
          ·
            refine ⟨5909987166616616987976779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15759965777644311967938077 5909987166616616987976779)
            ·
              refine ⟨8864980749924925481965169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5909987166616616987976779 8864980749924925481965169)
              ·
                refine ⟨6648735562443694111473877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8864980749924925481965169 6648735562443694111473877)
                ·
                  refine ⟨155829739744774080737669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6648735562443694111473877 155829739744774080737669)
                  ·
                    rfl

theorem cell21_682824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 2, 7].length) (baseStart_682824 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_682824 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_682824 prefixEnd_682824 := by exact prefixLift 682824
  have htrace : WordTrace (prefixWord ++ tailWord_682824) baseStart_682824 baseEnd_682824 := by
    simpa [prefixWord, tailWord_682824, baseEnd_682824] using wordTrace_append hprefix tailTrace_682824
  have hstable : (prefixWord ++ tailWord_682824).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682824).length < 2 ^ (prefixWord ++ tailWord_682824).sum := by decide
  have hdescent : baseEnd_682824 < baseStart_682824 := by decide
  rcases family_descends (prefixWord ++ tailWord_682824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682841 : List Nat := [1, 2, 1, 2, 2, 5, 2, 1, 5]
def baseStart_682841 : Nat := 118140960795 + 682841 * 2 ^ 59
def prefixEnd_682841 : Nat := 4983230072969 + 3 ^ 40 * 682841 * 2
def baseEnd_682841 : Nat := 155833619376385828954301

theorem tailTrace_682841 : CollatzResearch.WordTrace tailWord_682841 prefixEnd_682841 155833619376385828954301 := by
  unfold tailWord_682841
  simp only [CollatzResearch.WordTrace]
  refine ⟨24905257319191151803320377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16603504879460767868880251 24905257319191151803320377)
  ·
    refine ⟨18678942989393363852490283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24905257319191151803320377 18678942989393363852490283)
    ·
      refine ⟨28018414484090045778735425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18678942989393363852490283 28018414484090045778735425)
      ·
        refine ⟨21013810863067534334051569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28018414484090045778735425 21013810863067534334051569)
        ·
          refine ⟨15760358147300650750538677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21013810863067534334051569 15760358147300650750538677)
          ·
            refine ⟨1477533576309436007863001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15760358147300650750538677 1477533576309436007863001)
            ·
              refine ⟨1108150182232077005897251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1477533576309436007863001 1108150182232077005897251)
              ·
                refine ⟨1662225273348115508845877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1108150182232077005897251 1662225273348115508845877)
                ·
                  refine ⟨155833619376385828954301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1662225273348115508845877 155833619376385828954301)
                  ·
                    rfl

theorem cell21_682841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 2, 1, 5].length) (baseStart_682841 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_682841 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_682841 prefixEnd_682841 := by exact prefixLift 682841
  have htrace : WordTrace (prefixWord ++ tailWord_682841) baseStart_682841 baseEnd_682841 := by
    simpa [prefixWord, tailWord_682841, baseEnd_682841] using wordTrace_append hprefix tailTrace_682841
  have hstable : (prefixWord ++ tailWord_682841).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682841).length < 2 ^ (prefixWord ++ tailWord_682841).sum := by decide
  have hdescent : baseEnd_682841 < baseStart_682841 := by decide
  rcases family_descends (prefixWord ++ tailWord_682841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682906 : List Nat := [3, 1, 1, 4, 3, 2, 2, 1, 4]
def baseStart_682906 : Nat := 118140960795 + 682906 * 2 ^ 59
def prefixEnd_682906 : Nat := 4983230072969 + 3 ^ 40 * 682906 * 2
def baseEnd_682906 : Nat := 155848453261960160370835

theorem tailTrace_682906 : CollatzResearch.WordTrace tailWord_682906 prefixEnd_682906 155848453261960160370835 := by
  unfold tailWord_682906
  simp only [CollatzResearch.WordTrace]
  refine ⟨6226907015988916976109143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16605085375970445269624381 6226907015988916976109143)
  ·
    refine ⟨9340360523983375464163715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6226907015988916976109143 9340360523983375464163715)
    ·
      refine ⟨14010540785975063196245573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9340360523983375464163715 14010540785975063196245573)
      ·
        refine ⟨2626976397370324349296045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14010540785975063196245573 2626976397370324349296045)
        ·
          refine ⟨985116149013871630986017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2626976397370324349296045 985116149013871630986017)
          ·
            refine ⟨738837111760403723239513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 985116149013871630986017 738837111760403723239513)
            ·
              refine ⟨554127833820302792429635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 738837111760403723239513 554127833820302792429635)
              ·
                refine ⟨831191750730454188644453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 554127833820302792429635 831191750730454188644453)
                ·
                  refine ⟨155848453261960160370835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 831191750730454188644453 155848453261960160370835)
                  ·
                    rfl

theorem cell21_682906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 2, 1, 4].length) (baseStart_682906 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_682906 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_682906 prefixEnd_682906 := by exact prefixLift 682906
  have htrace : WordTrace (prefixWord ++ tailWord_682906) baseStart_682906 baseEnd_682906 := by
    simpa [prefixWord, tailWord_682906, baseEnd_682906] using wordTrace_append hprefix tailTrace_682906
  have hstable : (prefixWord ++ tailWord_682906).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682906).length < 2 ^ (prefixWord ++ tailWord_682906).sum := by decide
  have hdescent : baseEnd_682906 < baseStart_682906 := by decide
  rcases family_descends (prefixWord ++ tailWord_682906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683069 : List Nat := [1, 4, 1, 3, 1, 2, 3, 1, 5]
def baseStart_683069 : Nat := 118140960795 + 683069 * 2 ^ 59
def prefixEnd_683069 : Nat := 4983230072969 + 3 ^ 40 * 683069 * 2
def baseEnd_683069 : Nat := 155885652082708099153835

theorem tailTrace_683069 : CollatzResearch.WordTrace tailWord_683069 prefixEnd_683069 155885652082708099153835 := by
  unfold tailWord_683069
  simp only [CollatzResearch.WordTrace]
  refine ⟨24913573162365146742620261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16609048774910097828413507 24913573162365146742620261)
  ·
    refine ⟨4671294967943465014241299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24913573162365146742620261 4671294967943465014241299)
    ·
      refine ⟨7006942451915197521361949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4671294967943465014241299 7006942451915197521361949)
      ·
        refine ⟨2627603419468199070510731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7006942451915197521361949 2627603419468199070510731)
        ·
          refine ⟨3941405129202298605766097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2627603419468199070510731 3941405129202298605766097)
          ·
            refine ⟨2956053846901723954324573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3941405129202298605766097 2956053846901723954324573)
            ·
              refine ⟨1108520192588146482871715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2956053846901723954324573 1108520192588146482871715)
              ·
                refine ⟨1662780288882219724307573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1108520192588146482871715 1662780288882219724307573)
                ·
                  refine ⟨155885652082708099153835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1662780288882219724307573 155885652082708099153835)
                  ·
                    rfl

theorem cell21_683069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 3, 1, 5].length) (baseStart_683069 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_683069 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_683069 prefixEnd_683069 := by exact prefixLift 683069
  have htrace : WordTrace (prefixWord ++ tailWord_683069) baseStart_683069 baseEnd_683069 := by
    simpa [prefixWord, tailWord_683069, baseEnd_683069] using wordTrace_append hprefix tailTrace_683069
  have hstable : (prefixWord ++ tailWord_683069).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683069).length < 2 ^ (prefixWord ++ tailWord_683069).sum := by decide
  have hdescent : baseEnd_683069 < baseStart_683069 := by decide
  rcases family_descends (prefixWord ++ tailWord_683069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683162 : List Nat := [3, 1, 1, 5, 1, 1, 1, 5, 3]
def baseStart_683162 : Nat := 118140960795 + 683162 * 2 ^ 59
def prefixEnd_683162 : Nat := 4983230072969 + 3 ^ 40 * 683162 * 2
def baseEnd_683162 : Nat := 155906875949760604103645

theorem tailTrace_683162 : CollatzResearch.WordTrace tailWord_683162 prefixEnd_683162 155906875949760604103645 := by
  unfold tailWord_683162
  simp only [CollatzResearch.WordTrace]
  refine ⟨6229241287757055906438935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16611310100685482417170493 6229241287757055906438935)
  ·
    refine ⟨9343861931635583859658403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6229241287757055906438935 9343861931635583859658403)
    ·
      refine ⟨14015792897453375789487605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9343861931635583859658403 14015792897453375789487605)
      ·
        refine ⟨1313980584136253980264463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14015792897453375789487605 1313980584136253980264463)
        ·
          refine ⟨1970970876204380970396695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1313980584136253980264463 1970970876204380970396695)
          ·
            refine ⟨2956456314306571455595043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1970970876204380970396695 2956456314306571455595043)
            ·
              refine ⟨4434684471459857183392565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2956456314306571455595043 4434684471459857183392565)
              ·
                refine ⟨415751669199361610943053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4434684471459857183392565 415751669199361610943053)
                ·
                  refine ⟨155906875949760604103645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 415751669199361610943053 155906875949760604103645)
                  ·
                    rfl

theorem cell21_683162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 5, 3].length) (baseStart_683162 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_683162 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_683162 prefixEnd_683162 := by exact prefixLift 683162
  have htrace : WordTrace (prefixWord ++ tailWord_683162) baseStart_683162 baseEnd_683162 := by
    simpa [prefixWord, tailWord_683162, baseEnd_683162] using wordTrace_append hprefix tailTrace_683162
  have hstable : (prefixWord ++ tailWord_683162).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683162).length < 2 ^ (prefixWord ++ tailWord_683162).sum := by decide
  have hdescent : baseEnd_683162 < baseStart_683162 := by decide
  rcases family_descends (prefixWord ++ tailWord_683162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683173 : List Nat := [1, 3, 1, 2, 1, 5, 8]
def baseStart_683173 : Nat := 118140960795 + 683173 * 2 ^ 59
def prefixEnd_683173 : Nat := 4983230072969 + 3 ^ 40 * 683173 * 2
def baseEnd_683173 : Nat := 17323265144403003268921

theorem tailTrace_683173 : CollatzResearch.WordTrace tailWord_683173 prefixEnd_683173 17323265144403003268921 := by
  unfold tailWord_683173
  simp only [CollatzResearch.WordTrace]
  refine ⟨24917366353988372504406173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16611577569325581669604115 24917366353988372504406173)
  ·
    refine ⟨9344012382745639689152315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24917366353988372504406173 9344012382745639689152315)
    ·
      refine ⟨14016018574118459533728473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9344012382745639689152315 14016018574118459533728473)
      ·
        refine ⟨10512013930588844650296355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14016018574118459533728473 10512013930588844650296355)
        ·
          refine ⟨15768020895883266975444533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10512013930588844650296355 15768020895883266975444533)
          ·
            refine ⟨1478251958989056278947925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15768020895883266975444533 1478251958989056278947925)
            ·
              refine ⟨17323265144403003268921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1478251958989056278947925 17323265144403003268921)
              ·
                rfl

theorem cell21_683173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 8].length) (baseStart_683173 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_683173 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_683173 prefixEnd_683173 := by exact prefixLift 683173
  have htrace : WordTrace (prefixWord ++ tailWord_683173) baseStart_683173 baseEnd_683173 := by
    simpa [prefixWord, tailWord_683173, baseEnd_683173] using wordTrace_append hprefix tailTrace_683173
  have hstable : (prefixWord ++ tailWord_683173).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683173).length < 2 ^ (prefixWord ++ tailWord_683173).sum := by decide
  have hdescent : baseEnd_683173 < baseStart_683173 := by decide
  rcases family_descends (prefixWord ++ tailWord_683173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683213 : List Nat := [1, 6, 2, 2, 1, 2, 1, 3, 3]
def baseStart_683213 : Nat := 118140960795 + 683213 * 2 ^ 59
def prefixEnd_683213 : Nat := 4983230072969 + 3 ^ 40 * 683213 * 2
def baseEnd_683213 : Nat := 155918514844595848753541

theorem tailTrace_683213 : CollatzResearch.WordTrace tailWord_683213 prefixEnd_683213 155918514844595848753541 := by
  unfold tailWord_683213
  simp only [CollatzResearch.WordTrace]
  refine ⟨24918825273843459335862293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16612550182562306223908195 24918825273843459335862293)
  ·
    refine ⟨1168069934711412156368545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 24918825273843459335862293 1168069934711412156368545)
    ·
      refine ⟨876052451033559117276409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1168069934711412156368545 876052451033559117276409)
      ·
        refine ⟨657039338275169337957307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 876052451033559117276409 657039338275169337957307)
        ·
          refine ⟨985559007412754006935961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 657039338275169337957307 985559007412754006935961)
          ·
            refine ⟨739169255559565505201971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 985559007412754006935961 739169255559565505201971)
            ·
              refine ⟨1108753883339348257802957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 739169255559565505201971 1108753883339348257802957)
              ·
                refine ⟨415782706252255596676109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1108753883339348257802957 415782706252255596676109)
                ·
                  refine ⟨155918514844595848753541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 415782706252255596676109 155918514844595848753541)
                  ·
                    rfl

theorem cell21_683213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 1, 3, 3].length) (baseStart_683213 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_683213 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_683213 prefixEnd_683213 := by exact prefixLift 683213
  have htrace : WordTrace (prefixWord ++ tailWord_683213) baseStart_683213 baseEnd_683213 := by
    simpa [prefixWord, tailWord_683213, baseEnd_683213] using wordTrace_append hprefix tailTrace_683213
  have hstable : (prefixWord ++ tailWord_683213).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683213).length < 2 ^ (prefixWord ++ tailWord_683213).sum := by decide
  have hdescent : baseEnd_683213 < baseStart_683213 := by decide
  rcases family_descends (prefixWord ++ tailWord_683213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683421 : List Nat := [1, 4, 2, 1, 3, 3, 2, 1, 4]
def baseStart_683421 : Nat := 118140960795 + 683421 * 2 ^ 59
def prefixEnd_683421 : Nat := 4983230072969 + 3 ^ 40 * 683421 * 2
def baseEnd_683421 : Nat := 155965983278433709286449

theorem tailTrace_683421 : CollatzResearch.WordTrace tailWord_683421 prefixEnd_683421 155965983278433709286449 := by
  unfold tailWord_683421
  simp only [CollatzResearch.WordTrace]
  refine ⟨24926411657089910859434117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16617607771393273906289411 24926411657089910859434117)
  ·
    refine ⟨4673702185704358286143897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24926411657089910859434117 4673702185704358286143897)
    ·
      refine ⟨3505276639278268714607923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4673702185704358286143897 3505276639278268714607923)
      ·
        refine ⟨5257914958917403071911885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3505276639278268714607923 5257914958917403071911885)
        ·
          refine ⟨1971718109594026151966957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5257914958917403071911885 1971718109594026151966957)
          ·
            refine ⟨739394291097759806987609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1971718109594026151966957 739394291097759806987609)
            ·
              refine ⟨554545718323319855240707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 739394291097759806987609 554545718323319855240707)
              ·
                refine ⟨831818577484979782861061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 554545718323319855240707 831818577484979782861061)
                ·
                  refine ⟨155965983278433709286449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 831818577484979782861061 155965983278433709286449)
                  ·
                    rfl

theorem cell21_683421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 2, 1, 4].length) (baseStart_683421 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_683421 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_683421 prefixEnd_683421 := by exact prefixLift 683421
  have htrace : WordTrace (prefixWord ++ tailWord_683421) baseStart_683421 baseEnd_683421 := by
    simpa [prefixWord, tailWord_683421, baseEnd_683421] using wordTrace_append hprefix tailTrace_683421
  have hstable : (prefixWord ++ tailWord_683421).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683421).length < 2 ^ (prefixWord ++ tailWord_683421).sum := by decide
  have hdescent : baseEnd_683421 < baseStart_683421 := by decide
  rcases family_descends (prefixWord ++ tailWord_683421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683463 : List Nat := [1, 1, 4, 1, 1, 3, 4, 2, 4]
def baseStart_683463 : Nat := 118140960795 + 683463 * 2 ^ 59
def prefixEnd_683463 : Nat := 4983230072969 + 3 ^ 40 * 683463 * 2
def baseEnd_683463 : Nat := 155975568250650969586363

theorem tailTrace_683463 : CollatzResearch.WordTrace tailWord_683463 prefixEnd_683463 155975568250650969586363 := by
  unfold tailWord_683463
  simp only [CollatzResearch.WordTrace]
  refine ⟨24927943522937752032463043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16618629015291834688308695 24927943522937752032463043)
  ·
    refine ⟨37391915284406628048694565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24927943522937752032463043 37391915284406628048694565)
    ·
      refine ⟨7010984115826242759130231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37391915284406628048694565 7010984115826242759130231)
      ·
        refine ⟨10516476173739364138695347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7010984115826242759130231 10516476173739364138695347)
        ·
          refine ⟨15774714260609046208043021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10516476173739364138695347 15774714260609046208043021)
          ·
            refine ⟨5915517847728392328016133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15774714260609046208043021 5915517847728392328016133)
            ·
              refine ⟨1109159596449073561503025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5915517847728392328016133 1109159596449073561503025)
              ·
                refine ⟨831869697336805171127269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1109159596449073561503025 831869697336805171127269)
                ·
                  refine ⟨155975568250650969586363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 831869697336805171127269 155975568250650969586363)
                  ·
                    rfl

theorem cell21_683463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 4, 2, 4].length) (baseStart_683463 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_683463 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_683463 prefixEnd_683463 := by exact prefixLift 683463
  have htrace : WordTrace (prefixWord ++ tailWord_683463) baseStart_683463 baseEnd_683463 := by
    simpa [prefixWord, tailWord_683463, baseEnd_683463] using wordTrace_append hprefix tailTrace_683463
  have hstable : (prefixWord ++ tailWord_683463).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683463).length < 2 ^ (prefixWord ++ tailWord_683463).sum := by decide
  have hdescent : baseEnd_683463 < baseStart_683463 := by decide
  rcases family_descends (prefixWord ++ tailWord_683463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683466 : List Nat := [3, 1, 2, 1, 2, 3, 4, 2, 3]
def baseStart_683466 : Nat := 118140960795 + 683466 * 2 ^ 59
def prefixEnd_683466 : Nat := 4983230072969 + 3 ^ 40 * 683466 * 2
def baseEnd_683466 : Nat := 155976252891523631036357

theorem tailTrace_683466 : CollatzResearch.WordTrace tailWord_683466 prefixEnd_683466 155976252891523631036357 := by
  unfold tailWord_683466
  simp only [CollatzResearch.WordTrace]
  refine ⟨6232013235481720886205563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16618701961284589029881501 6232013235481720886205563)
  ·
    refine ⟨9348019853222581329308345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6232013235481720886205563 9348019853222581329308345)
    ·
      refine ⟨7011014889916935996981259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9348019853222581329308345 7011014889916935996981259)
      ·
        refine ⟨10516522334875403995471889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7011014889916935996981259 10516522334875403995471889)
        ·
          refine ⟨7887391751156552996603917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10516522334875403995471889 7887391751156552996603917)
          ·
            refine ⟨2957771906683707373726469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7887391751156552996603917 2957771906683707373726469)
            ·
              refine ⟨554582232503195132573713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2957771906683707373726469 554582232503195132573713)
              ·
                refine ⟨415936674377396349430285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 554582232503195132573713 415936674377396349430285)
                ·
                  refine ⟨155976252891523631036357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 415936674377396349430285 155976252891523631036357)
                  ·
                    rfl

theorem cell21_683466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 4, 2, 3].length) (baseStart_683466 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_683466 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_683466 prefixEnd_683466 := by exact prefixLift 683466
  have htrace : WordTrace (prefixWord ++ tailWord_683466) baseStart_683466 baseEnd_683466 := by
    simpa [prefixWord, tailWord_683466, baseEnd_683466] using wordTrace_append hprefix tailTrace_683466
  have hstable : (prefixWord ++ tailWord_683466).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683466).length < 2 ^ (prefixWord ++ tailWord_683466).sum := by decide
  have hdescent : baseEnd_683466 < baseStart_683466 := by decide
  rcases family_descends (prefixWord ++ tailWord_683466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683553 : List Nat := [1, 2, 3, 2, 2, 3, 1, 7]
def baseStart_683553 : Nat := 118140960795 + 683553 * 2 ^ 59
def prefixEnd_683553 : Nat := 4983230072969 + 3 ^ 40 * 683553 * 2
def baseEnd_683553 : Nat := 51998702492276937695393

theorem tailTrace_683553 : CollatzResearch.WordTrace tailWord_683553 prefixEnd_683553 51998702492276937695393 := by
  unfold tailWord_683553
  simp only [CollatzResearch.WordTrace]
  refine ⟨24931226092611697403239313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16620817395074464935492875 24931226092611697403239313)
  ·
    refine ⟨18698419569458773052429485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24931226092611697403239313 18698419569458773052429485)
    ·
      refine ⟨7011907338547039894661057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18698419569458773052429485 7011907338547039894661057)
      ·
        refine ⟨5258930503910279920995793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7011907338547039894661057 5258930503910279920995793)
        ·
          refine ⟨3944197877932709940746845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5258930503910279920995793 3944197877932709940746845)
          ·
            refine ⟨1479074204224766227780067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3944197877932709940746845 1479074204224766227780067)
            ·
              refine ⟨2218611306337149341670101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1479074204224766227780067 2218611306337149341670101)
              ·
                refine ⟨51998702492276937695393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2218611306337149341670101 51998702492276937695393)
                ·
                  rfl

theorem cell21_683553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 7].length) (baseStart_683553 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_683553 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_683553 prefixEnd_683553 := by exact prefixLift 683553
  have htrace : WordTrace (prefixWord ++ tailWord_683553) baseStart_683553 baseEnd_683553 := by
    simpa [prefixWord, tailWord_683553, baseEnd_683553] using wordTrace_append hprefix tailTrace_683553
  have hstable : (prefixWord ++ tailWord_683553).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683553).length < 2 ^ (prefixWord ++ tailWord_683553).sum := by decide
  have hdescent : baseEnd_683553 < baseStart_683553 := by decide
  rcases family_descends (prefixWord ++ tailWord_683553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683629 : List Nat := [1, 5, 1, 1, 4, 9]
def baseStart_683629 : Nat := 118140960795 + 683629 * 2 ^ 59
def prefixEnd_683629 : Nat := 4983230072969 + 3 ^ 40 * 683629 * 2
def baseEnd_683629 : Nat := 5778275989343391474791

theorem tailTrace_683629 : CollatzResearch.WordTrace tailWord_683629 prefixEnd_683629 5778275989343391474791 := by
  unfold tailWord_683629
  simp only [CollatzResearch.WordTrace]
  refine ⟨24933998040336362383005941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16622665360224241588670627 24933998040336362383005941)
  ·
    refine ⟨2337562316281533973406807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24933998040336362383005941 2337562316281533973406807)
    ·
      refine ⟨3506343474422300960110211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2337562316281533973406807 3506343474422300960110211)
      ·
        refine ⟨5259515211633451440165317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3506343474422300960110211 5259515211633451440165317)
        ·
          refine ⟨986159102181272145030997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5259515211633451440165317 986159102181272145030997)
          ·
            refine ⟨5778275989343391474791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 986159102181272145030997 5778275989343391474791)
            ·
              rfl

theorem cell21_683629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 9].length) (baseStart_683629 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_683629 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_683629 prefixEnd_683629 := by exact prefixLift 683629
  have htrace : WordTrace (prefixWord ++ tailWord_683629) baseStart_683629 baseEnd_683629 := by
    simpa [prefixWord, tailWord_683629, baseEnd_683629] using wordTrace_append hprefix tailTrace_683629
  have hstable : (prefixWord ++ tailWord_683629).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683629).length < 2 ^ (prefixWord ++ tailWord_683629).sum := by decide
  have hdescent : baseEnd_683629 < baseStart_683629 := by decide
  rcases family_descends (prefixWord ++ tailWord_683629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683643 : List Nat := [1, 1, 1, 1, 1, 4, 4, 3, 5]
def baseStart_683643 : Nat := 118140960795 + 683643 * 2 ^ 59
def prefixEnd_683643 : Nat := 4983230072969 + 3 ^ 40 * 683643 * 2
def baseEnd_683643 : Nat := 156016646703010656585995

theorem tailTrace_683643 : CollatzResearch.WordTrace tailWord_683643 prefixEnd_683643 156016646703010656585995 := by
  unfold tailWord_683643
  simp only [CollatzResearch.WordTrace]
  refine ⟨24934508662285642774015583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16623005774857095182677055 24934508662285642774015583)
  ·
    refine ⟨37401762993428464161023375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24934508662285642774015583 37401762993428464161023375)
    ·
      refine ⟨56102644490142696241535063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37401762993428464161023375 56102644490142696241535063)
      ·
        refine ⟨84153966735214044362302595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56102644490142696241535063 84153966735214044362302595)
        ·
          refine ⟨126230950102821066543453893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84153966735214044362302595 126230950102821066543453893)
          ·
            refine ⟨23668303144278949976897605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 126230950102821066543453893 23668303144278949976897605)
            ·
              refine ⟨4437806839552303120668301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23668303144278949976897605 4437806839552303120668301)
              ·
                refine ⟨1664177564832113670250613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4437806839552303120668301 1664177564832113670250613)
                ·
                  refine ⟨156016646703010656585995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1664177564832113670250613 156016646703010656585995)
                  ·
                    rfl

theorem cell21_683643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 3, 5].length) (baseStart_683643 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_683643 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_683643 prefixEnd_683643 := by exact prefixLift 683643
  have htrace : WordTrace (prefixWord ++ tailWord_683643) baseStart_683643 baseEnd_683643 := by
    simpa [prefixWord, tailWord_683643, baseEnd_683643] using wordTrace_append hprefix tailTrace_683643
  have hstable : (prefixWord ++ tailWord_683643).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683643).length < 2 ^ (prefixWord ++ tailWord_683643).sum := by decide
  have hdescent : baseEnd_683643 < baseStart_683643 := by decide
  rcases family_descends (prefixWord ++ tailWord_683643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683694 : List Nat := [4, 1, 4, 1, 2, 1, 2, 1, 5]
def baseStart_683694 : Nat := 118140960795 + 683694 * 2 ^ 59
def prefixEnd_683694 : Nat := 4983230072969 + 3 ^ 40 * 683694 * 2
def baseEnd_683694 : Nat := 156028285597845901235891

theorem tailTrace_683694 : CollatzResearch.WordTrace tailWord_683694 prefixEnd_683694 156028285597845901235891 := by
  unfold tailWord_683694
  simp only [CollatzResearch.WordTrace]
  refine ⟨3117046098137609810515267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16624245856733918989414757 3117046098137609810515267)
  ·
    refine ⟨4675569147206414715772901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3117046098137609810515267 4675569147206414715772901)
    ·
      refine ⟨876669215101202759207419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4675569147206414715772901 876669215101202759207419)
      ·
        refine ⟨1315003822651804138811129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 876669215101202759207419 1315003822651804138811129)
        ·
          refine ⟨986252866988853104108347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1315003822651804138811129 986252866988853104108347)
          ·
            refine ⟨1479379300483279656162521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 986252866988853104108347 1479379300483279656162521)
            ·
              refine ⟨1109534475362459742121891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1479379300483279656162521 1109534475362459742121891)
              ·
                refine ⟨1664301713043689613182837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1109534475362459742121891 1664301713043689613182837)
                ·
                  refine ⟨156028285597845901235891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1664301713043689613182837 156028285597845901235891)
                  ·
                    rfl

theorem cell21_683694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 2, 1, 5].length) (baseStart_683694 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_683694 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_683694 prefixEnd_683694 := by exact prefixLift 683694
  have htrace : WordTrace (prefixWord ++ tailWord_683694) baseStart_683694 baseEnd_683694 := by
    simpa [prefixWord, tailWord_683694, baseEnd_683694] using wordTrace_append hprefix tailTrace_683694
  have hstable : (prefixWord ++ tailWord_683694).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683694).length < 2 ^ (prefixWord ++ tailWord_683694).sum := by decide
  have hdescent : baseEnd_683694 < baseStart_683694 := by decide
  rcases family_descends (prefixWord ++ tailWord_683694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683708 : List Nat := [2, 2, 2, 3, 1, 3, 3, 1, 4]
def baseStart_683708 : Nat := 118140960795 + 683708 * 2 ^ 59
def prefixEnd_683708 : Nat := 4983230072969 + 3 ^ 40 * 683708 * 2
def baseEnd_683708 : Nat := 156031480588584988002529

theorem tailTrace_683708 : CollatzResearch.WordTrace tailWord_683708 prefixEnd_683708 156031480588584988002529 := by
  unfold tailWord_683708
  simp only [CollatzResearch.WordTrace]
  refine ⟨12468439703525079437565889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16624586271366772583421185 12468439703525079437565889)
  ·
    refine ⟨9351329777643809578174417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12468439703525079437565889 9351329777643809578174417)
    ·
      refine ⟨7013497333232857183630813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9351329777643809578174417 7013497333232857183630813)
      ·
        refine ⟨2630061499962321443861555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7013497333232857183630813 2630061499962321443861555)
        ·
          refine ⟨3945092249943482165792333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2630061499962321443861555 3945092249943482165792333)
          ·
            refine ⟨1479409593728805812172125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3945092249943482165792333 1479409593728805812172125)
            ·
              refine ⟨554778597648302179564547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1479409593728805812172125 554778597648302179564547)
              ·
                refine ⟨832167896472453269346821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 554778597648302179564547 832167896472453269346821)
                ·
                  refine ⟨156031480588584988002529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 832167896472453269346821 156031480588584988002529)
                  ·
                    rfl

theorem cell21_683708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 3, 1, 4].length) (baseStart_683708 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_683708 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_683708 prefixEnd_683708 := by exact prefixLift 683708
  have htrace : WordTrace (prefixWord ++ tailWord_683708) baseStart_683708 baseEnd_683708 := by
    simpa [prefixWord, tailWord_683708, baseEnd_683708] using wordTrace_append hprefix tailTrace_683708
  have hstable : (prefixWord ++ tailWord_683708).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683708).length < 2 ^ (prefixWord ++ tailWord_683708).sum := by decide
  have hdescent : baseEnd_683708 < baseStart_683708 := by decide
  rcases family_descends (prefixWord ++ tailWord_683708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683714 : List Nat := [3, 5, 1, 2, 2, 1, 2, 5]
def baseStart_683714 : Nat := 118140960795 + 683714 * 2 ^ 59
def prefixEnd_683714 : Nat := 4983230072969 + 3 ^ 40 * 683714 * 2
def baseEnd_683714 : Nat := 52010949956776770300839

theorem tailTrace_683714 : CollatzResearch.WordTrace tailWord_683714 prefixEnd_683714 52010949956776770300839 := by
  unfold tailWord_683714
  simp only [CollatzResearch.WordTrace]
  refine ⟨6234274561257105474962549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16624732163352281266566797 6234274561257105474962549)
  ·
    refine ⟨584463240117853638277739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6234274561257105474962549 584463240117853638277739)
    ·
      refine ⟨876694860176780457416609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 584463240117853638277739 876694860176780457416609)
      ·
        refine ⟨657521145132585343062457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 876694860176780457416609 657521145132585343062457)
        ·
          refine ⟨493140858849439007296843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 657521145132585343062457 493140858849439007296843)
          ·
            refine ⟨739711288274158510945265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 493140858849439007296843 739711288274158510945265)
            ·
              refine ⟨554783466205618883208949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 739711288274158510945265 554783466205618883208949)
              ·
                refine ⟨52010949956776770300839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 554783466205618883208949 52010949956776770300839)
                ·
                  rfl

theorem cell21_683714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 2, 5].length) (baseStart_683714 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_683714 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_683714 prefixEnd_683714 := by exact prefixLift 683714
  have htrace : WordTrace (prefixWord ++ tailWord_683714) baseStart_683714 baseEnd_683714 := by
    simpa [prefixWord, tailWord_683714, baseEnd_683714] using wordTrace_append hprefix tailTrace_683714
  have hstable : (prefixWord ++ tailWord_683714).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683714).length < 2 ^ (prefixWord ++ tailWord_683714).sum := by decide
  have hdescent : baseEnd_683714 < baseStart_683714 := by decide
  rcases family_descends (prefixWord ++ tailWord_683714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683719 : List Nat := [1, 1, 4, 1, 1, 1, 3, 4, 5]
def baseStart_683719 : Nat := 118140960795 + 683719 * 2 ^ 59
def prefixEnd_683719 : Nat := 4983230072969 + 3 ^ 40 * 683719 * 2
def baseEnd_683719 : Nat := 156033990938451413319173

theorem tailTrace_683719 : CollatzResearch.WordTrace tailWord_683719 prefixEnd_683719 156033990938451413319173 := by
  unfold tailWord_683719
  simp only [CollatzResearch.WordTrace]
  refine ⟨24937280610010307753782211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16624853740006871835854807 24937280610010307753782211)
  ·
    refine ⟨37405920915015461630673317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24937280610010307753782211 37405920915015461630673317)
    ·
      refine ⟨7013610171565399055751247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37405920915015461630673317 7013610171565399055751247)
      ·
        refine ⟨10520415257348098583626871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7013610171565399055751247 10520415257348098583626871)
        ·
          refine ⟨15780622886022147875440307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10520415257348098583626871 15780622886022147875440307)
          ·
            refine ⟨23670934329033221813160461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15780622886022147875440307 23670934329033221813160461)
            ·
              refine ⟨8876600373387458179935173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23670934329033221813160461 8876600373387458179935173)
              ·
                refine ⟨1664362570010148408737845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8876600373387458179935173 1664362570010148408737845)
                ·
                  refine ⟨156033990938451413319173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1664362570010148408737845 156033990938451413319173)
                  ·
                    rfl

theorem cell21_683719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 4, 5].length) (baseStart_683719 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_683719 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_683719 prefixEnd_683719 := by exact prefixLift 683719
  have htrace : WordTrace (prefixWord ++ tailWord_683719) baseStart_683719 baseEnd_683719 := by
    simpa [prefixWord, tailWord_683719, baseEnd_683719] using wordTrace_append hprefix tailTrace_683719
  have hstable : (prefixWord ++ tailWord_683719).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683719).length < 2 ^ (prefixWord ++ tailWord_683719).sum := by decide
  have hdescent : baseEnd_683719 < baseStart_683719 := by decide
  rcases family_descends (prefixWord ++ tailWord_683719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683767 : List Nat := [1, 1, 3, 1, 1, 1, 8, 1, 4]
def baseStart_683767 : Nat := 118140960795 + 683767 * 2 ^ 59
def prefixEnd_683767 : Nat := 4983230072969 + 3 ^ 40 * 683767 * 2
def baseEnd_683767 : Nat := 156044945192413996519075

theorem tailTrace_683767 : CollatzResearch.WordTrace tailWord_683767 prefixEnd_683767 156044945192413996519075 := by
  unfold tailWord_683767
  simp only [CollatzResearch.WordTrace]
  refine ⟨24939031313836411951529555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16626020875890941301019703 24939031313836411951529555)
  ·
    refine ⟨37408546970754617927294333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24939031313836411951529555 37408546970754617927294333)
    ·
      refine ⟨14028205114032981722735375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37408546970754617927294333 14028205114032981722735375)
      ·
        refine ⟨21042307671049472584103063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14028205114032981722735375 21042307671049472584103063)
        ·
          refine ⟨31563461506574208876154595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21042307671049472584103063 31563461506574208876154595)
          ·
            refine ⟨47345192259861313314231893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31563461506574208876154595 47345192259861313314231893)
            ·
              refine ⟨554826471795249765401155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 47345192259861313314231893 554826471795249765401155)
              ·
                refine ⟨832239707692874648101733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 554826471795249765401155 832239707692874648101733)
                ·
                  refine ⟨156044945192413996519075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 832239707692874648101733 156044945192413996519075)
                  ·
                    rfl

theorem cell21_683767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 8, 1, 4].length) (baseStart_683767 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_683767 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_683767 prefixEnd_683767 := by exact prefixLift 683767
  have htrace : WordTrace (prefixWord ++ tailWord_683767) baseStart_683767 baseEnd_683767 := by
    simpa [prefixWord, tailWord_683767, baseEnd_683767] using wordTrace_append hprefix tailTrace_683767
  have hstable : (prefixWord ++ tailWord_683767).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683767).length < 2 ^ (prefixWord ++ tailWord_683767).sum := by decide
  have hdescent : baseEnd_683767 < baseStart_683767 := by decide
  rcases family_descends (prefixWord ++ tailWord_683767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683860 : List Nat := [2, 4, 1, 1, 3, 3, 1, 2, 4]
def baseStart_683860 : Nat := 118140960795 + 683860 * 2 ^ 59
def prefixEnd_683860 : Nat := 4983230072969 + 3 ^ 40 * 683860 * 2
def baseEnd_683860 : Nat := 156066169059466501468885

theorem tailTrace_683860 : CollatzResearch.WordTrace tailWord_683860 prefixEnd_683860 156066169059466501468885 := by
  unfold tailWord_683860
  simp only [CollatzResearch.WordTrace]
  refine ⟨12471211651249744417332517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16628282201666325889776689 12471211651249744417332517)
  ·
    refine ⟨2338352184609327078249847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12471211651249744417332517 2338352184609327078249847)
    ·
      refine ⟨3507528276913990617374771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2338352184609327078249847 3507528276913990617374771)
      ·
        refine ⟨5261292415370985926062157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3507528276913990617374771 5261292415370985926062157)
        ·
          refine ⟨1972984655764119722273309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5261292415370985926062157 1972984655764119722273309)
          ·
            refine ⟨739869245911544895852491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1972984655764119722273309 739869245911544895852491)
            ·
              refine ⟨1109803868867317343778737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 739869245911544895852491 1109803868867317343778737)
              ·
                refine ⟨832352901650488007834053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1109803868867317343778737 832352901650488007834053)
                ·
                  refine ⟨156066169059466501468885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 832352901650488007834053 156066169059466501468885)
                  ·
                    rfl

theorem cell21_683860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 1, 2, 4].length) (baseStart_683860 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_683860 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_683860 prefixEnd_683860 := by exact prefixLift 683860
  have htrace : WordTrace (prefixWord ++ tailWord_683860) baseStart_683860 baseEnd_683860 := by
    simpa [prefixWord, tailWord_683860, baseEnd_683860] using wordTrace_append hprefix tailTrace_683860
  have hstable : (prefixWord ++ tailWord_683860).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683860).length < 2 ^ (prefixWord ++ tailWord_683860).sum := by decide
  have hdescent : baseEnd_683860 < baseStart_683860 := by decide
  rcases family_descends (prefixWord ++ tailWord_683860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683871 : List Nat := [1, 1, 2, 3, 1, 4, 1, 3, 5]
def baseStart_683871 : Nat := 118140960795 + 683871 * 2 ^ 59
def prefixEnd_683871 : Nat := 4983230072969 + 3 ^ 40 * 683871 * 2
def baseEnd_683871 : Nat := 156068679409332926785529

theorem tailTrace_683871 : CollatzResearch.WordTrace tailWord_683871 prefixEnd_683871 156068679409332926785529 := by
  unfold tailWord_683871
  simp only [CollatzResearch.WordTrace]
  refine ⟨24942824505459637713315467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16628549670306425142210311 24942824505459637713315467)
  ·
    refine ⟨37414236758189456569973201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24942824505459637713315467 37414236758189456569973201)
    ·
      refine ⟨28060677568642092427479901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37414236758189456569973201 28060677568642092427479901)
      ·
        refine ⟨10522754088240784660304963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28060677568642092427479901 10522754088240784660304963)
        ·
          refine ⟨15784131132361176990457445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10522754088240784660304963 15784131132361176990457445)
          ·
            refine ⟨2959524587317720685710771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15784131132361176990457445 2959524587317720685710771)
            ·
              refine ⟨4439286880976581028566157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2959524587317720685710771 4439286880976581028566157)
              ·
                refine ⟨1664732580366217885712309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4439286880976581028566157 1664732580366217885712309)
                ·
                  refine ⟨156068679409332926785529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1664732580366217885712309 156068679409332926785529)
                  ·
                    rfl

theorem cell21_683871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 3, 5].length) (baseStart_683871 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_683871 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_683871 prefixEnd_683871 := by exact prefixLift 683871
  have htrace : WordTrace (prefixWord ++ tailWord_683871) baseStart_683871 baseEnd_683871 := by
    simpa [prefixWord, tailWord_683871, baseEnd_683871] using wordTrace_append hprefix tailTrace_683871
  have hstable : (prefixWord ++ tailWord_683871).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683871).length < 2 ^ (prefixWord ++ tailWord_683871).sum := by decide
  have hdescent : baseEnd_683871 < baseStart_683871 := by decide
  rcases family_descends (prefixWord ++ tailWord_683871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683933 : List Nat := [1, 4, 2, 1, 2, 3, 2, 6]
def baseStart_683933 : Nat := 118140960795 + 683933 * 2 ^ 59
def prefixEnd_683933 : Nat := 4983230072969 + 3 ^ 40 * 683933 * 2
def baseEnd_683933 : Nat := 52027609551344865584023

theorem tailTrace_683933 : CollatzResearch.WordTrace tailWord_683933 prefixEnd_683933 52027609551344865584023 := by
  unfold tailWord_683933
  simp only [CollatzResearch.WordTrace]
  refine ⟨24945085831235022302072453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16630057220823348201381635 24945085831235022302072453)
  ·
    refine ⟨4677203593356566681638585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24945085831235022302072453 4677203593356566681638585)
    ·
      refine ⟨3507902695017425011228939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4677203593356566681638585 3507902695017425011228939)
      ·
        refine ⟨5261854042526137516843409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3507902695017425011228939 5261854042526137516843409)
        ·
          refine ⟨3946390531894603137632557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5261854042526137516843409 3946390531894603137632557)
          ·
            refine ⟨1479896449460476176612209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3946390531894603137632557 1479896449460476176612209)
            ·
              refine ⟨1109922337095357132459157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1479896449460476176612209 1109922337095357132459157)
              ·
                refine ⟨52027609551344865584023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1109922337095357132459157 52027609551344865584023)
                ·
                  rfl

theorem cell21_683933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 2, 6].length) (baseStart_683933 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_683933 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_683933 prefixEnd_683933 := by exact prefixLift 683933
  have htrace : WordTrace (prefixWord ++ tailWord_683933) baseStart_683933 baseEnd_683933 := by
    simpa [prefixWord, tailWord_683933, baseEnd_683933] using wordTrace_append hprefix tailTrace_683933
  have hstable : (prefixWord ++ tailWord_683933).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683933).length < 2 ^ (prefixWord ++ tailWord_683933).sum := by decide
  have hdescent : baseEnd_683933 < baseStart_683933 := by decide
  rcases family_descends (prefixWord ++ tailWord_683933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683978 : List Nat := [3, 1, 2, 1, 2, 1, 3, 4, 4]
def baseStart_683978 : Nat := 118140960795 + 683978 * 2 ^ 59
def prefixEnd_683978 : Nat := 4983230072969 + 3 ^ 40 * 683978 * 2
def baseEnd_683978 : Nat := 156093098267124518501977

theorem tailTrace_683978 : CollatzResearch.WordTrace tailWord_683978 prefixEnd_683978 156093098267124518501977 := by
  unfold tailWord_683978
  simp only [CollatzResearch.WordTrace]
  refine ⟨6236681779017998746865147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16631151410714663324973725 6236681779017998746865147)
  ·
    refine ⟨9355022668526998120297721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6236681779017998746865147 9355022668526998120297721)
    ·
      refine ⟨7016267001395248590223291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9355022668526998120297721 7016267001395248590223291)
      ·
        refine ⟨10524400502092872885334937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7016267001395248590223291 10524400502092872885334937)
        ·
          refine ⟨7893300376569654664001203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10524400502092872885334937 7893300376569654664001203)
          ·
            refine ⟨11839950564854481996001805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7893300376569654664001203 11839950564854481996001805)
            ·
              refine ⟨4439981461820430748500677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11839950564854481996001805 4439981461820430748500677)
              ·
                refine ⟨832496524091330765343877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4439981461820430748500677 832496524091330765343877)
                ·
                  refine ⟨156093098267124518501977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 832496524091330765343877 156093098267124518501977)
                  ·
                    rfl

theorem cell21_683978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 4, 4].length) (baseStart_683978 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_683978 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_683978 prefixEnd_683978 := by exact prefixLift 683978
  have htrace : WordTrace (prefixWord ++ tailWord_683978) baseStart_683978 baseEnd_683978 := by
    simpa [prefixWord, tailWord_683978, baseEnd_683978] using wordTrace_append hprefix tailTrace_683978
  have hstable : (prefixWord ++ tailWord_683978).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683978).length < 2 ^ (prefixWord ++ tailWord_683978).sum := by decide
  have hdescent : baseEnd_683978 < baseStart_683978 := by decide
  rcases family_descends (prefixWord ++ tailWord_683978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684040 : List Nat := [2, 1, 3, 2, 1, 2, 1, 6, 3]
def baseStart_684040 : Nat := 118140960795 + 684040 * 2 ^ 59
def prefixEnd_684040 : Nat := 4983230072969 + 3 ^ 40 * 684040 * 2
def baseEnd_684040 : Nat := 156107247511826188468517

theorem tailTrace_684040 : CollatzResearch.WordTrace tailWord_684040 prefixEnd_684040 156107247511826188468517 := by
  unfold tailWord_684040
  simp only [CollatzResearch.WordTrace]
  refine ⟨12474494220923689788108787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16632658961231586384145049 12474494220923689788108787)
  ·
    refine ⟨18711741331385534682163181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12474494220923689788108787 18711741331385534682163181)
    ·
      refine ⟨7016902999269575505811193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18711741331385534682163181 7016902999269575505811193)
      ·
        refine ⟨5262677249452181629358395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7016902999269575505811193 5262677249452181629358395)
        ·
          refine ⟨7894015874178272444037593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5262677249452181629358395 7894015874178272444037593)
          ·
            refine ⟨5920511905633704333028195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7894015874178272444037593 5920511905633704333028195)
            ·
              refine ⟨8880767858450556499542293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5920511905633704333028195 8880767858450556499542293)
              ·
                refine ⟨416285993364869835916045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 8880767858450556499542293 416285993364869835916045)
                ·
                  refine ⟨156107247511826188468517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 416285993364869835916045 156107247511826188468517)
                  ·
                    rfl

theorem cell21_684040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 6, 3].length) (baseStart_684040 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_684040 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_684040 prefixEnd_684040 := by exact prefixLift 684040
  have htrace : WordTrace (prefixWord ++ tailWord_684040) baseStart_684040 baseEnd_684040 := by
    simpa [prefixWord, tailWord_684040, baseEnd_684040] using wordTrace_append hprefix tailTrace_684040
  have hstable : (prefixWord ++ tailWord_684040).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684040).length < 2 ^ (prefixWord ++ tailWord_684040).sum := by decide
  have hdescent : baseEnd_684040 < baseStart_684040 := by decide
  rcases family_descends (prefixWord ++ tailWord_684040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684074 : List Nat := [3, 1, 4, 1, 2, 3, 1, 3, 3]
def baseStart_684074 : Nat := 118140960795 + 684074 * 2 ^ 59
def prefixEnd_684074 : Nat := 4983230072969 + 3 ^ 40 * 684074 * 2
def baseEnd_684074 : Nat := 156115006775049684901781

theorem tailTrace_684074 : CollatzResearch.WordTrace tailWord_684074 prefixEnd_684074 156115006775049684901781 := by
  unfold tailWord_684074
  simp only [CollatzResearch.WordTrace]
  refine ⟨6237557130931050845738819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16633485682482802255303517 6237557130931050845738819)
  ·
    refine ⟨9356335696396576268608229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6237557130931050845738819 9356335696396576268608229)
    ·
      refine ⟨1754312943074358050364043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9356335696396576268608229 1754312943074358050364043)
      ·
        refine ⟨2631469414611537075546065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1754312943074358050364043 2631469414611537075546065)
        ·
          refine ⟨1973602060958652806659549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2631469414611537075546065 1973602060958652806659549)
          ·
            refine ⟨740100772859494802497331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1973602060958652806659549 740100772859494802497331)
            ·
              refine ⟨1110151159289242203745997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 740100772859494802497331 1110151159289242203745997)
              ·
                refine ⟨416306684733465826404749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1110151159289242203745997 416306684733465826404749)
                ·
                  refine ⟨156115006775049684901781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 416306684733465826404749 156115006775049684901781)
                  ·
                    rfl

theorem cell21_684074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 1, 3, 3].length) (baseStart_684074 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_684074 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_684074 prefixEnd_684074 := by exact prefixLift 684074
  have htrace : WordTrace (prefixWord ++ tailWord_684074) baseStart_684074 baseEnd_684074 := by
    simpa [prefixWord, tailWord_684074, baseEnd_684074] using wordTrace_append hprefix tailTrace_684074
  have hstable : (prefixWord ++ tailWord_684074).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684074).length < 2 ^ (prefixWord ++ tailWord_684074).sum := by decide
  have hdescent : baseEnd_684074 < baseStart_684074 := by decide
  rcases family_descends (prefixWord ++ tailWord_684074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684102 : List Nat := [6, 1, 1, 1, 1, 1, 4, 6]
def baseStart_684102 : Nat := 118140960795 + 684102 * 2 ^ 59
def prefixEnd_684102 : Nat := 4983230072969 + 3 ^ 40 * 684102 * 2
def baseEnd_684102 : Nat := 52040465585509286145019

theorem tailTrace_684102 : CollatzResearch.WordTrace tailWord_684102 prefixEnd_684102 52040465585509286145019 := by
  unfold tailWord_684102
  simp only [CollatzResearch.WordTrace]
  refine ⟨779726555238211380155455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 16634166511748509443316373 779726555238211380155455)
  ·
    refine ⟨1169589832857317070233183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 779726555238211380155455 1169589832857317070233183)
    ·
      refine ⟨1754384749285975605349775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1169589832857317070233183 1754384749285975605349775)
      ·
        refine ⟨2631577123928963408024663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1754384749285975605349775 2631577123928963408024663)
        ·
          refine ⟨3947365685893445112036995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2631577123928963408024663 3947365685893445112036995)
          ·
            refine ⟨5921048528840167668055493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3947365685893445112036995 5921048528840167668055493)
            ·
              refine ⟨1110196599157531437760405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5921048528840167668055493 1110196599157531437760405)
              ·
                refine ⟨52040465585509286145019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1110196599157531437760405 52040465585509286145019)
                ·
                  rfl

theorem cell21_684102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 4, 6].length) (baseStart_684102 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_684102 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_684102 prefixEnd_684102 := by exact prefixLift 684102
  have htrace : WordTrace (prefixWord ++ tailWord_684102) baseStart_684102 baseEnd_684102 := by
    simpa [prefixWord, tailWord_684102, baseEnd_684102] using wordTrace_append hprefix tailTrace_684102
  have hstable : (prefixWord ++ tailWord_684102).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684102).length < 2 ^ (prefixWord ++ tailWord_684102).sum := by decide
  have hdescent : baseEnd_684102 < baseStart_684102 := by decide
  rcases family_descends (prefixWord ++ tailWord_684102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684150 : List Nat := [5, 1, 1, 2, 1, 2, 4, 2, 3]
def baseStart_684150 : Nat := 118140960795 + 684150 * 2 ^ 59
def prefixEnd_684150 : Nat := 4983230072969 + 3 ^ 40 * 684150 * 2
def baseEnd_684150 : Nat := 156132351010490441634959

theorem tailTrace_684150 : CollatzResearch.WordTrace tailWord_684150 prefixEnd_684150 156132351010490441634959 := by
  unfold tailWord_684150
  simp only [CollatzResearch.WordTrace]
  refine ⟨1559562529465554272670119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16635333647632578908481269 1559562529465554272670119)
  ·
    refine ⟨2339343794198331409005179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1559562529465554272670119 2339343794198331409005179)
    ·
      refine ⟨3509015691297497113507769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2339343794198331409005179 3509015691297497113507769)
      ·
        refine ⟨2631761768473122835130827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3509015691297497113507769 2631761768473122835130827)
        ·
          refine ⟨3947642652709684252696241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2631761768473122835130827 3947642652709684252696241)
          ·
            refine ⟨2960731989532263189522181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3947642652709684252696241 2960731989532263189522181)
            ·
              refine ⟨555137248037299348035409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2960731989532263189522181 555137248037299348035409)
              ·
                refine ⟨416352936027974511026557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 555137248037299348035409 416352936027974511026557)
                ·
                  refine ⟨156132351010490441634959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 416352936027974511026557 156132351010490441634959)
                  ·
                    rfl

theorem cell21_684150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 4, 2, 3].length) (baseStart_684150 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_684150 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_684150 prefixEnd_684150 := by exact prefixLift 684150
  have htrace : WordTrace (prefixWord ++ tailWord_684150) baseStart_684150 baseEnd_684150 := by
    simpa [prefixWord, tailWord_684150, baseEnd_684150] using wordTrace_append hprefix tailTrace_684150
  have hstable : (prefixWord ++ tailWord_684150).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684150).length < 2 ^ (prefixWord ++ tailWord_684150).sum := by decide
  have hdescent : baseEnd_684150 < baseStart_684150 := by decide
  rcases family_descends (prefixWord ++ tailWord_684150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684192 : List Nat := [2, 1, 1, 4, 2, 2, 1, 5, 3]
def baseStart_684192 : Nat := 118140960795 + 684192 * 2 ^ 59
def prefixEnd_684192 : Nat := 4983230072969 + 3 ^ 40 * 684192 * 2
def baseEnd_684192 : Nat := 156141935982707701934873

theorem tailTrace_684192 : CollatzResearch.WordTrace tailWord_684192 prefixEnd_684192 156141935982707701934873 := by
  unfold tailWord_684192
  simp only [CollatzResearch.WordTrace]
  refine ⟨12477266168648354767875415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16636354891531139690500553 12477266168648354767875415)
  ·
    refine ⟨18715899252972532151813123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12477266168648354767875415 18715899252972532151813123)
    ·
      refine ⟨28073848879458798227719685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18715899252972532151813123 28073848879458798227719685)
      ·
        refine ⟨5263846664898524667697441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28073848879458798227719685 5263846664898524667697441)
        ·
          refine ⟨3947884998673893500773081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5263846664898524667697441 3947884998673893500773081)
          ·
            refine ⟨2960913749005420125579811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3947884998673893500773081 2960913749005420125579811)
            ·
              refine ⟨4441370623508130188369717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2960913749005420125579811 4441370623508130188369717)
              ·
                refine ⟨416378495953887205159661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4441370623508130188369717 416378495953887205159661)
                ·
                  refine ⟨156141935982707701934873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 416378495953887205159661 156141935982707701934873)
                  ·
                    rfl

theorem cell21_684192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 5, 3].length) (baseStart_684192 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_684192 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_684192 prefixEnd_684192 := by exact prefixLift 684192
  have htrace : WordTrace (prefixWord ++ tailWord_684192) baseStart_684192 baseEnd_684192 := by
    simpa [prefixWord, tailWord_684192, baseEnd_684192] using wordTrace_append hprefix tailTrace_684192
  have hstable : (prefixWord ++ tailWord_684192).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684192).length < 2 ^ (prefixWord ++ tailWord_684192).sum := by decide
  have hdescent : baseEnd_684192 < baseStart_684192 := by decide
  rcases family_descends (prefixWord ++ tailWord_684192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684282 : List Nat := [3, 1, 1, 1, 1, 6, 1, 3, 4]
def baseStart_684282 : Nat := 118140960795 + 684282 * 2 ^ 59
def prefixEnd_684282 : Nat := 4983230072969 + 3 ^ 40 * 684282 * 2
def baseEnd_684282 : Nat := 156162475208887545434689

theorem tailTrace_684282 : CollatzResearch.WordTrace tailWord_684282 prefixEnd_684282 156162475208887545434689 := by
  unfold tailWord_684282
  simp only [CollatzResearch.WordTrace]
  refine ⟨6239453726742663726631775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16638543271313769937684733 6239453726742663726631775)
  ·
    refine ⟨9359180590113995589947663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6239453726742663726631775 9359180590113995589947663)
    ·
      refine ⟨14038770885170993384921495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9359180590113995589947663 14038770885170993384921495)
      ·
        refine ⟨21058156327756490077382243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14038770885170993384921495 21058156327756490077382243)
        ·
          refine ⟨31587234491634735116073365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21058156327756490077382243 31587234491634735116073365)
          ·
            refine ⟨1480651616795378208565939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 31587234491634735116073365 1480651616795378208565939)
            ·
              refine ⟨2220977425193067312848909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1480651616795378208565939 2220977425193067312848909)
              ·
                refine ⟨832866534447400242318341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2220977425193067312848909 832866534447400242318341)
                ·
                  refine ⟨156162475208887545434689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 832866534447400242318341 156162475208887545434689)
                  ·
                    rfl

theorem cell21_684282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 3, 4].length) (baseStart_684282 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_684282 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_684282 prefixEnd_684282 := by exact prefixLift 684282
  have htrace : WordTrace (prefixWord ++ tailWord_684282) baseStart_684282 baseEnd_684282 := by
    simpa [prefixWord, tailWord_684282, baseEnd_684282] using wordTrace_append hprefix tailTrace_684282
  have hstable : (prefixWord ++ tailWord_684282).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684282).length < 2 ^ (prefixWord ++ tailWord_684282).sum := by decide
  have hdescent : baseEnd_684282 < baseStart_684282 := by decide
  rcases family_descends (prefixWord ++ tailWord_684282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684296 : List Nat := [2, 1, 3, 2, 3, 1, 2, 7]
def baseStart_684296 : Nat := 118140960795 + 684296 * 2 ^ 59
def prefixEnd_684296 : Nat := 4983230072969 + 3 ^ 40 * 684296 * 2
def baseEnd_684296 : Nat := 52055223399875544067109

theorem tailTrace_684296 : CollatzResearch.WordTrace tailWord_684296 prefixEnd_684296 52055223399875544067109 := by
  unfold tailWord_684296
  simp only [CollatzResearch.WordTrace]
  refine ⟨12479162764459967648768371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16638883685946623531691161 12479162764459967648768371)
  ·
    refine ⟨18718744146689951473152557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12479162764459967648768371 18718744146689951473152557)
    ·
      refine ⟨7019529055008731802432209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18718744146689951473152557 7019529055008731802432209)
      ·
        refine ⟨5264646791256548851824157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7019529055008731802432209 5264646791256548851824157)
        ·
          refine ⟨1974242546721205819434059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5264646791256548851824157 1974242546721205819434059)
          ·
            refine ⟨2961363820081808729151089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1974242546721205819434059 2961363820081808729151089)
            ·
              refine ⟨2221022865061356546863317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2961363820081808729151089 2221022865061356546863317)
              ·
                refine ⟨52055223399875544067109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2221022865061356546863317 52055223399875544067109)
                ·
                  rfl

theorem cell21_684296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 7].length) (baseStart_684296 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_684296 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_684296 prefixEnd_684296 := by exact prefixLift 684296
  have htrace : WordTrace (prefixWord ++ tailWord_684296) baseStart_684296 baseEnd_684296 := by
    simpa [prefixWord, tailWord_684296, baseEnd_684296] using wordTrace_append hprefix tailTrace_684296
  have hstable : (prefixWord ++ tailWord_684296).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684296).length < 2 ^ (prefixWord ++ tailWord_684296).sum := by decide
  have hdescent : baseEnd_684296 < baseStart_684296 := by decide
  rcases family_descends (prefixWord ++ tailWord_684296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684330 : List Nat := [3, 1, 4, 2, 2, 2, 1, 6]
def baseStart_684330 : Nat := 118140960795 + 684330 * 2 ^ 59
def prefixEnd_684330 : Nat := 4983230072969 + 3 ^ 40 * 684330 * 2
def baseEnd_684330 : Nat := 52057809820950042878197

theorem tailTrace_684330 : CollatzResearch.WordTrace tailWord_684330 prefixEnd_684330 52057809820950042878197 := by
  unfold tailWord_684330
  simp only [CollatzResearch.WordTrace]
  refine ⟨6239891402699189776068611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16639710407197839402849629 6239891402699189776068611)
  ·
    refine ⟨9359837104048784664102917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6239891402699189776068611 9359837104048784664102917)
    ·
      refine ⟨1754969457009147124519297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9359837104048784664102917 1754969457009147124519297)
      ·
        refine ⟨1316227092756860343389473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1754969457009147124519297 1316227092756860343389473)
        ·
          refine ⟨987170319567645257542105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1316227092756860343389473 987170319567645257542105)
          ·
            refine ⟨740377739675733943156579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 987170319567645257542105 740377739675733943156579)
            ·
              refine ⟨1110566609513600914734869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 740377739675733943156579 1110566609513600914734869)
              ·
                refine ⟨52057809820950042878197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1110566609513600914734869 52057809820950042878197)
                ·
                  rfl

theorem cell21_684330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 1, 6].length) (baseStart_684330 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_684330 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_684330 prefixEnd_684330 := by exact prefixLift 684330
  have htrace : WordTrace (prefixWord ++ tailWord_684330) baseStart_684330 baseEnd_684330 := by
    simpa [prefixWord, tailWord_684330, baseEnd_684330] using wordTrace_append hprefix tailTrace_684330
  have hstable : (prefixWord ++ tailWord_684330).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684330).length < 2 ^ (prefixWord ++ tailWord_684330).sum := by decide
  have hdescent : baseEnd_684330 < baseStart_684330 := by decide
  rcases family_descends (prefixWord ++ tailWord_684330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684355 : List Nat := [1, 1, 1, 3, 1, 3, 2, 9]
def baseStart_684355 : Nat := 118140960795 + 684355 * 2 ^ 59
def prefixEnd_684355 : Nat := 4983230072969 + 3 ^ 40 * 684355 * 2
def baseEnd_684355 : Nat := 52059711601151880239291

theorem tailTrace_684355 : CollatzResearch.WordTrace tailWord_684355 prefixEnd_684355 52059711601151880239291 := by
  unfold tailWord_684355
  simp only [CollatzResearch.WordTrace]
  refine ⟨24960477435706188373934519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16640318290470792249289679 24960477435706188373934519)
  ·
    refine ⟨37440716153559282560901779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24960477435706188373934519 37440716153559282560901779)
    ·
      refine ⟨56161074230338923841352669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37440716153559282560901779 56161074230338923841352669)
      ·
        refine ⟨21060402836377096440507251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56161074230338923841352669 21060402836377096440507251)
        ·
          refine ⟨31590604254565644660760877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21060402836377096440507251 31590604254565644660760877)
          ·
            refine ⟨11846476595462116747785329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31590604254565644660760877 11846476595462116747785329)
            ·
              refine ⟨8884857446596587560838997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11846476595462116747785329 8884857446596587560838997)
              ·
                refine ⟨52059711601151880239291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8884857446596587560838997 52059711601151880239291)
                ·
                  rfl

theorem cell21_684355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 9].length) (baseStart_684355 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_684355 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_684355 prefixEnd_684355 := by exact prefixLift 684355
  have htrace : WordTrace (prefixWord ++ tailWord_684355) baseStart_684355 baseEnd_684355 := by
    simpa [prefixWord, tailWord_684355, baseEnd_684355] using wordTrace_append hprefix tailTrace_684355
  have hstable : (prefixWord ++ tailWord_684355).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684355).length < 2 ^ (prefixWord ++ tailWord_684355).sum := by decide
  have hdescent : baseEnd_684355 < baseStart_684355 := by decide
  rcases family_descends (prefixWord ++ tailWord_684355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684372 : List Nat := [2, 4, 1, 1, 2, 3, 8]
def baseStart_684372 : Nat := 118140960795 + 684372 * 2 ^ 59
def prefixEnd_684372 : Nat := 4983230072969 + 3 ^ 40 * 684372 * 2
def baseEnd_684372 : Nat := 17353668270563043214945

theorem tailTrace_684372 : CollatzResearch.WordTrace tailWord_684372 prefixEnd_684372 17353668270563043214945 := by
  unfold tailWord_684372
  simp only [CollatzResearch.WordTrace]
  refine ⟨12480548738322300138651685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16640731651096400184868913 12480548738322300138651685)
  ·
    refine ⟨2340102888435431275997191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12480548738322300138651685 2340102888435431275997191)
    ·
      refine ⟨3510154332653146913995787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2340102888435431275997191 3510154332653146913995787)
      ·
        refine ⟨5265231498979720370993681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3510154332653146913995787 5265231498979720370993681)
        ·
          refine ⟨3948923624234790278245261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5265231498979720370993681 3948923624234790278245261)
          ·
            refine ⟨1480846359088046354341973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3948923624234790278245261 1480846359088046354341973)
            ·
              refine ⟨17353668270563043214945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1480846359088046354341973 17353668270563043214945)
              ·
                rfl

theorem cell21_684372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 8].length) (baseStart_684372 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_684372 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_684372 prefixEnd_684372 := by exact prefixLift 684372
  have htrace : WordTrace (prefixWord ++ tailWord_684372) baseStart_684372 baseEnd_684372 := by
    simpa [prefixWord, tailWord_684372, baseEnd_684372] using wordTrace_append hprefix tailTrace_684372
  have hstable : (prefixWord ++ tailWord_684372).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684372).length < 2 ^ (prefixWord ++ tailWord_684372).sum := by decide
  have hdescent : baseEnd_684372 < baseStart_684372 := by decide
  rcases family_descends (prefixWord ++ tailWord_684372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684406 : List Nat := [5, 1, 1, 4, 1, 1, 1, 7]
def baseStart_684406 : Nat := 118140960795 + 684406 * 2 ^ 59
def prefixEnd_684406 : Nat := 4983230072969 + 3 ^ 40 * 684406 * 2
def baseEnd_684406 : Nat := 52063591232763628455923

theorem tailTrace_684406 : CollatzResearch.WordTrace tailWord_684406 prefixEnd_684406 52063591232763628455923 := by
  unfold tailWord_684406
  simp only [CollatzResearch.WordTrace]
  refine ⟨1560146097407589005252567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16641558372347616056027381 1560146097407589005252567)
  ·
    refine ⟨2340219146111383507878851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1560146097407589005252567 2340219146111383507878851)
    ·
      refine ⟨3510328719167075261818277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2340219146111383507878851 3510328719167075261818277)
      ·
        refine ⟨658186634843826611590927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3510328719167075261818277 658186634843826611590927)
        ·
          refine ⟨987279952265739917386391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 658186634843826611590927 987279952265739917386391)
          ·
            refine ⟨1480919928398609876079587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 987279952265739917386391 1480919928398609876079587)
            ·
              refine ⟨2221379892597914814119381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1480919928398609876079587 2221379892597914814119381)
              ·
                refine ⟨52063591232763628455923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2221379892597914814119381 52063591232763628455923)
                ·
                  rfl

theorem cell21_684406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 7].length) (baseStart_684406 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_684406 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_684406 prefixEnd_684406 := by exact prefixLift 684406
  have htrace : WordTrace (prefixWord ++ tailWord_684406) baseStart_684406 baseEnd_684406 := by
    simpa [prefixWord, tailWord_684406, baseEnd_684406] using wordTrace_append hprefix tailTrace_684406
  have hstable : (prefixWord ++ tailWord_684406).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684406).length < 2 ^ (prefixWord ++ tailWord_684406).sum := by decide
  have hdescent : baseEnd_684406 < baseStart_684406 := by decide
  rcases family_descends (prefixWord ++ tailWord_684406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684448 : List Nat := [2, 1, 1, 4, 1, 4, 2, 6]
def baseStart_684448 : Nat := 118140960795 + 684448 * 2 ^ 59
def prefixEnd_684448 : Nat := 4983230072969 + 3 ^ 40 * 684448 * 2
def baseEnd_684448 : Nat := 52066786223502715222561

theorem tailTrace_684448 : CollatzResearch.WordTrace tailWord_684448 prefixEnd_684448 52066786223502715222561 := by
  unfold tailWord_684448
  simp only [CollatzResearch.WordTrace]
  refine ⟨12481934712184632628534999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16642579616246176838046665 12481934712184632628534999)
  ·
    refine ⟨18722902068276948942802499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12481934712184632628534999 18722902068276948942802499)
    ·
      refine ⟨28084353102415423414203749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18722902068276948942802499 28084353102415423414203749)
      ·
        refine ⟨5265816206702891890163203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28084353102415423414203749 5265816206702891890163203)
        ·
          refine ⟨7898724310054337835244805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5265816206702891890163203 7898724310054337835244805)
          ·
            refine ⟨1481010808135188344108401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7898724310054337835244805 1481010808135188344108401)
            ·
              refine ⟨1110758106101391258081301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1481010808135188344108401 1110758106101391258081301)
              ·
                refine ⟨52066786223502715222561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1110758106101391258081301 52066786223502715222561)
                ·
                  rfl

theorem cell21_684448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 2, 6].length) (baseStart_684448 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_684448 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_684448 prefixEnd_684448 := by exact prefixLift 684448
  have htrace : WordTrace (prefixWord ++ tailWord_684448) baseStart_684448 baseEnd_684448 := by
    simpa [prefixWord, tailWord_684448, baseEnd_684448] using wordTrace_append hprefix tailTrace_684448
  have hstable : (prefixWord ++ tailWord_684448).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684448).length < 2 ^ (prefixWord ++ tailWord_684448).sum := by decide
  have hdescent : baseEnd_684448 < baseStart_684448 := by decide
  rcases family_descends (prefixWord ++ tailWord_684448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684451 : List Nat := [1, 1, 1, 4, 1, 6, 2, 1, 4]
def baseStart_684451 : Nat := 118140960795 + 684451 * 2 ^ 59
def prefixEnd_684451 : Nat := 4983230072969 + 3 ^ 40 * 684451 * 2
def baseEnd_684451 : Nat := 156201043311380807117677

theorem tailTrace_684451 : CollatzResearch.WordTrace tailWord_684451 prefixEnd_684451 156201043311380807117677 := by
  unfold tailWord_684451
  simp only [CollatzResearch.WordTrace]
  refine ⟨24963978843358396769429207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16642652562238931179619471 24963978843358396769429207)
  ·
    refine ⟨37445968265037595154143811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24963978843358396769429207 37445968265037595154143811)
    ·
      refine ⟨56168952397556392731215717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37445968265037595154143811 56168952397556392731215717)
      ·
        refine ⟨10531678574541823637102947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56168952397556392731215717 10531678574541823637102947)
        ·
          refine ⟨15797517861812735455654421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10531678574541823637102947 15797517861812735455654421)
          ·
            refine ⟨740508649772471974483801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 15797517861812735455654421 740508649772471974483801)
            ·
              refine ⟨555381487329353980862851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 740508649772471974483801 555381487329353980862851)
              ·
                refine ⟨833072230994030971294277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 555381487329353980862851 833072230994030971294277)
                ·
                  refine ⟨156201043311380807117677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 833072230994030971294277 156201043311380807117677)
                  ·
                    rfl

theorem cell21_684451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 2, 1, 4].length) (baseStart_684451 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_684451 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_684451 prefixEnd_684451 := by exact prefixLift 684451
  have htrace : WordTrace (prefixWord ++ tailWord_684451) baseStart_684451 baseEnd_684451 := by
    simpa [prefixWord, tailWord_684451, baseEnd_684451] using wordTrace_append hprefix tailTrace_684451
  have hstable : (prefixWord ++ tailWord_684451).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684451).length < 2 ^ (prefixWord ++ tailWord_684451).sum := by decide
  have hdescent : baseEnd_684451 < baseStart_684451 := by decide
  rcases family_descends (prefixWord ++ tailWord_684451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684524 : List Nat := [2, 2, 1, 1, 2, 1, 7, 5]
def baseStart_684524 : Nat := 118140960795 + 684524 * 2 ^ 59
def prefixEnd_684524 : Nat := 4983230072969 + 3 ^ 40 * 684524 * 2
def baseEnd_684524 : Nat := 52072567635316300800287

theorem tailTrace_684524 : CollatzResearch.WordTrace tailWord_684524 prefixEnd_684524 52072567635316300800287 := by
  unfold tailWord_684524
  simp only [CollatzResearch.WordTrace]
  refine ⟨12483320686046965118418313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16644427581395953491224417 12483320686046965118418313)
  ·
    refine ⟨9362490514535223838813735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12483320686046965118418313 9362490514535223838813735)
    ·
      refine ⟨14043735771802835758220603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9362490514535223838813735 14043735771802835758220603)
      ·
        refine ⟨21065603657704253637330905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14043735771802835758220603 21065603657704253637330905)
        ·
          refine ⟨15799202743278190227998179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21065603657704253637330905 15799202743278190227998179)
          ·
            refine ⟨23698804114917285341997269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15799202743278190227998179 23698804114917285341997269)
            ·
              refine ⟨555440721443373875203061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 23698804114917285341997269 555440721443373875203061)
              ·
                refine ⟨52072567635316300800287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 555440721443373875203061 52072567635316300800287)
                ·
                  rfl

theorem cell21_684524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 7, 5].length) (baseStart_684524 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_684524 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_684524 prefixEnd_684524 := by exact prefixLift 684524
  have htrace : WordTrace (prefixWord ++ tailWord_684524) baseStart_684524 baseEnd_684524 := by
    simpa [prefixWord, tailWord_684524, baseEnd_684524] using wordTrace_append hprefix tailTrace_684524
  have hstable : (prefixWord ++ tailWord_684524).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684524).length < 2 ^ (prefixWord ++ tailWord_684524).sum := by decide
  have hdescent : baseEnd_684524 < baseStart_684524 := by decide
  rcases family_descends (prefixWord ++ tailWord_684524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684555 : List Nat := [1, 1, 1, 1, 7, 2, 2, 1, 5]
def baseStart_684555 : Nat := 118140960795 + 684555 * 2 ^ 59
def prefixEnd_684555 : Nat := 4983230072969 + 3 ^ 40 * 684555 * 2
def baseEnd_684555 : Nat := 156224777528299737384131

theorem tailTrace_684555 : CollatzResearch.WordTrace tailWord_684555 prefixEnd_684555 156224777528299737384131 := by
  unfold tailWord_684555
  simp only [CollatzResearch.WordTrace]
  refine ⟨24967772034981622531215119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16645181356654415020810079 24967772034981622531215119)
  ·
    refine ⟨37451658052472433796822679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24967772034981622531215119 37451658052472433796822679)
    ·
      refine ⟨56177487078708650695234019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37451658052472433796822679 56177487078708650695234019)
      ·
        refine ⟨84266230618062976042851029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56177487078708650695234019 84266230618062976042851029)
        ·
          refine ⟨1974989780110851001004321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 84266230618062976042851029 1974989780110851001004321)
          ·
            refine ⟨1481242335083138250753241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1974989780110851001004321 1481242335083138250753241)
            ·
              refine ⟨1110931751312353688064931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1481242335083138250753241 1110931751312353688064931)
              ·
                refine ⟨1666397626968530532097397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1110931751312353688064931 1666397626968530532097397)
                ·
                  refine ⟨156224777528299737384131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1666397626968530532097397 156224777528299737384131)
                  ·
                    rfl

theorem cell21_684555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 2, 1, 5].length) (baseStart_684555 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_684555 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_684555 prefixEnd_684555 := by exact prefixLift 684555
  have htrace : WordTrace (prefixWord ++ tailWord_684555) baseStart_684555 baseEnd_684555 := by
    simpa [prefixWord, tailWord_684555, baseEnd_684555] using wordTrace_append hprefix tailTrace_684555
  have hstable : (prefixWord ++ tailWord_684555).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684555).length < 2 ^ (prefixWord ++ tailWord_684555).sum := by decide
  have hdescent : baseEnd_684555 < baseStart_684555 := by decide
  rcases family_descends (prefixWord ++ tailWord_684555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684606 : List Nat := [4, 2, 1, 4, 2, 1, 1, 1, 5]
def baseStart_684606 : Nat := 118140960795 + 684606 * 2 ^ 59
def prefixEnd_684606 : Nat := 4983230072969 + 3 ^ 40 * 684606 * 2
def baseEnd_684606 : Nat := 156236416423134982034027

theorem tailTrace_684606 : CollatzResearch.WordTrace tailWord_684606 prefixEnd_684606 156236416423134982034027 := by
  unfold tailWord_684606
  simp only [CollatzResearch.WordTrace]
  refine ⟨3121204019724607280165209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16646421438531238827547781 3121204019724607280165209)
  ·
    refine ⟨2340903014793455460123907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3121204019724607280165209 2340903014793455460123907)
    ·
      refine ⟨3511354522190183190185861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2340903014793455460123907 3511354522190183190185861)
      ·
        refine ⟨658378972910659348159849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3511354522190183190185861 658378972910659348159849)
        ·
          refine ⟨493784229682994511119887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 658378972910659348159849 493784229682994511119887)
          ·
            refine ⟨740676344524491766679831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 493784229682994511119887 740676344524491766679831)
            ·
              refine ⟨1111014516786737650019747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 740676344524491766679831 1111014516786737650019747)
              ·
                refine ⟨1666521775180106475029621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1111014516786737650019747 1666521775180106475029621)
                ·
                  refine ⟨156236416423134982034027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1666521775180106475029621 156236416423134982034027)
                  ·
                    rfl

theorem cell21_684606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 1, 1, 5].length) (baseStart_684606 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_684606 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_684606 prefixEnd_684606 := by exact prefixLift 684606
  have htrace : WordTrace (prefixWord ++ tailWord_684606) baseStart_684606 baseEnd_684606 := by
    simpa [prefixWord, tailWord_684606, baseEnd_684606] using wordTrace_append hprefix tailTrace_684606
  have hstable : (prefixWord ++ tailWord_684606).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684606).length < 2 ^ (prefixWord ++ tailWord_684606).sum := by decide
  have hdescent : baseEnd_684606 < baseStart_684606 := by decide
  rcases family_descends (prefixWord ++ tailWord_684606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684665 : List Nat := [1, 2, 1, 3, 3, 4, 2, 2, 3]
def baseStart_684665 : Nat := 118140960795 + 684665 * 2 ^ 59
def prefixEnd_684665 : Nat := 4983230072969 + 3 ^ 40 * 684665 * 2
def baseEnd_684665 : Nat := 156249881026963990550573

theorem tailTrace_684665 : CollatzResearch.WordTrace tailWord_684665 prefixEnd_684665 156249881026963990550573 := by
  unfold tailWord_684665
  simp only [CollatzResearch.WordTrace]
  refine ⟨24971784064583111317719449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16647856043055407545146299 24971784064583111317719449)
  ·
    refine ⟨18728838048437333488289587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24971784064583111317719449 18728838048437333488289587)
    ·
      refine ⟨28093257072656000232434381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18728838048437333488289587 28093257072656000232434381)
      ·
        refine ⟨10534971402246000087162893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28093257072656000232434381 10534971402246000087162893)
        ·
          refine ⟨3950614275842250032686085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10534971402246000087162893 3950614275842250032686085)
          ·
            refine ⟨740740176720421881128641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3950614275842250032686085 740740176720421881128641)
            ·
              refine ⟨555555132540316410846481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 740740176720421881128641 555555132540316410846481)
              ·
                refine ⟨416666349405237308134861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 555555132540316410846481 416666349405237308134861)
                ·
                  refine ⟨156249881026963990550573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 416666349405237308134861 156249881026963990550573)
                  ·
                    rfl

theorem cell21_684665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 2, 2, 3].length) (baseStart_684665 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_684665 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_684665 prefixEnd_684665 := by exact prefixLift 684665
  have htrace : WordTrace (prefixWord ++ tailWord_684665) baseStart_684665 baseEnd_684665 := by
    simpa [prefixWord, tailWord_684665, baseEnd_684665] using wordTrace_append hprefix tailTrace_684665
  have hstable : (prefixWord ++ tailWord_684665).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684665).length < 2 ^ (prefixWord ++ tailWord_684665).sum := by decide
  have hdescent : baseEnd_684665 < baseStart_684665 := by decide
  rcases family_descends (prefixWord ++ tailWord_684665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684676 : List Nat := [2, 3, 2, 1, 3, 1, 3, 6]
def baseStart_684676 : Nat := 118140960795 + 684676 * 2 ^ 59
def prefixEnd_684676 : Nat := 4983230072969 + 3 ^ 40 * 684676 * 2
def baseEnd_684676 : Nat := 52084130458943471955739

theorem tailTrace_684676 : CollatzResearch.WordTrace tailWord_684676 prefixEnd_684676 52084130458943471955739 := by
  unfold tailWord_684676
  simp only [CollatzResearch.WordTrace]
  refine ⟨12486092633771630098184941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16648123511695506797579921 12486092633771630098184941)
  ·
    refine ⟨4682284737664361286819353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12486092633771630098184941 4682284737664361286819353)
    ·
      refine ⟨3511713553248270965114515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4682284737664361286819353 3511713553248270965114515)
      ·
        refine ⟨5267570329872406447671773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3511713553248270965114515 5267570329872406447671773)
        ·
          refine ⟨1975338873702152417876915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5267570329872406447671773 1975338873702152417876915)
          ·
            refine ⟨2963008310553228626815373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1975338873702152417876915 2963008310553228626815373)
            ·
              refine ⟨1111128116457460735055765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2963008310553228626815373 1111128116457460735055765)
              ·
                refine ⟨52084130458943471955739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1111128116457460735055765 52084130458943471955739)
                ·
                  rfl

theorem cell21_684676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 3, 6].length) (baseStart_684676 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_684676 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_684676 prefixEnd_684676 := by exact prefixLift 684676
  have htrace : WordTrace (prefixWord ++ tailWord_684676) baseStart_684676 baseEnd_684676 := by
    simpa [prefixWord, tailWord_684676, baseEnd_684676] using wordTrace_append hprefix tailTrace_684676
  have hstable : (prefixWord ++ tailWord_684676).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684676).length < 2 ^ (prefixWord ++ tailWord_684676).sum := by decide
  have hdescent : baseEnd_684676 < baseStart_684676 := by decide
  rcases family_descends (prefixWord ++ tailWord_684676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684783 : List Nat := [1, 1, 2, 1, 5, 4, 1, 1, 5]
def baseStart_684783 : Nat := 118140960795 + 684783 * 2 ^ 59
def prefixEnd_684783 : Nat := 4983230072969 + 3 ^ 40 * 684783 * 2
def baseEnd_684783 : Nat := 156276810234622007583665

theorem tailTrace_684783 : CollatzResearch.WordTrace tailWord_684783 prefixEnd_684783 156276810234622007583665 := by
  unfold tailWord_684783
  simp only [CollatzResearch.WordTrace]
  refine ⟨24976087878155617470515003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16650725252103744980343335 24976087878155617470515003)
  ·
    refine ⟨37464131817233426205772505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24976087878155617470515003 37464131817233426205772505)
    ·
      refine ⟨28098098862925069654329379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37464131817233426205772505 28098098862925069654329379)
      ·
        refine ⟨42147148294387604481494069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28098098862925069654329379 42147148294387604481494069)
        ·
          refine ⟨3951295152598837920140069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42147148294387604481494069 3951295152598837920140069)
          ·
            refine ⟨740867841112282110026263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3951295152598837920140069 740867841112282110026263)
            ·
              refine ⟨1111301761668423165039395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 740867841112282110026263 1111301761668423165039395)
              ·
                refine ⟨1666952642502634747559093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1111301761668423165039395 1666952642502634747559093)
                ·
                  refine ⟨156276810234622007583665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1666952642502634747559093 156276810234622007583665)
                  ·
                    rfl

theorem cell21_684783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 1, 1, 5].length) (baseStart_684783 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_684783 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_684783 prefixEnd_684783 := by exact prefixLift 684783
  have htrace : WordTrace (prefixWord ++ tailWord_684783) baseStart_684783 baseEnd_684783 := by
    simpa [prefixWord, tailWord_684783, baseEnd_684783] using wordTrace_append hprefix tailTrace_684783
  have hstable : (prefixWord ++ tailWord_684783).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684783).length < 2 ^ (prefixWord ++ tailWord_684783).sum := by decide
  have hdescent : baseEnd_684783 < baseStart_684783 := by decide
  rcases family_descends (prefixWord ++ tailWord_684783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684797 : List Nat := [1, 4, 1, 1, 1, 1, 5, 3, 4]
def baseStart_684797 : Nat := 118140960795 + 684797 * 2 ^ 59
def prefixEnd_684797 : Nat := 4983230072969 + 3 ^ 40 * 684797 * 2
def baseEnd_684797 : Nat := 156280005225361094350303

theorem tailTrace_684797 : CollatzResearch.WordTrace tailWord_684797 prefixEnd_684797 156280005225361094350303 := by
  unfold tailWord_684797
  simp only [CollatzResearch.WordTrace]
  refine ⟨24976598500104897861524645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16651065666736598574349763 24976598500104897861524645)
  ·
    refine ⟨4683112218769668349035871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24976598500104897861524645 4683112218769668349035871)
    ·
      refine ⟨7024668328154502523553807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4683112218769668349035871 7024668328154502523553807)
      ·
        refine ⟨10537002492231753785330711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7024668328154502523553807 10537002492231753785330711)
        ·
          refine ⟨15805503738347630677996067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10537002492231753785330711 15805503738347630677996067)
          ·
            refine ⟨23708255607521446016994101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15805503738347630677996067 23708255607521446016994101)
            ·
              refine ⟨2222648963205135564093197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23708255607521446016994101 2222648963205135564093197)
              ·
                refine ⟨833493361201925836534949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2222648963205135564093197 833493361201925836534949)
                ·
                  refine ⟨156280005225361094350303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 833493361201925836534949 156280005225361094350303)
                  ·
                    rfl

theorem cell21_684797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 3, 4].length) (baseStart_684797 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_684797 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_684797 prefixEnd_684797 := by exact prefixLift 684797
  have htrace : WordTrace (prefixWord ++ tailWord_684797) baseStart_684797 baseEnd_684797 := by
    simpa [prefixWord, tailWord_684797, baseEnd_684797] using wordTrace_append hprefix tailTrace_684797
  have hstable : (prefixWord ++ tailWord_684797).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684797).length < 2 ^ (prefixWord ++ tailWord_684797).sum := by decide
  have hdescent : baseEnd_684797 < baseStart_684797 := by decide
  rcases family_descends (prefixWord ++ tailWord_684797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684825 : List Nat := [1, 2, 1, 2, 1, 1, 1, 3, 9]
def baseStart_684825 : Nat := 118140960795 + 684825 * 2 ^ 59
def prefixEnd_684825 : Nat := 4983230072969 + 3 ^ 40 * 684825 * 2
def baseEnd_684825 : Nat := 156286395206839267883579

theorem tailTrace_684825 : CollatzResearch.WordTrace tailWord_684825 prefixEnd_684825 156286395206839267883579 := by
  unfold tailWord_684825
  simp only [CollatzResearch.WordTrace]
  refine ⟨24977619744003458643543929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16651746496002305762362619 24977619744003458643543929)
  ·
    refine ⟨18733214808002593982657947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24977619744003458643543929 18733214808002593982657947)
    ·
      refine ⟨28099822212003890973986921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18733214808002593982657947 28099822212003890973986921)
      ·
        refine ⟨21074866659002918230490191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28099822212003890973986921 21074866659002918230490191)
        ·
          refine ⟨31612299988504377345735287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21074866659002918230490191 31612299988504377345735287)
          ·
            refine ⟨47418449982756566018602931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31612299988504377345735287 47418449982756566018602931)
            ·
              refine ⟨71127674974134849027904397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47418449982756566018602931 71127674974134849027904397)
              ·
                refine ⟨26672878115300568385464149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71127674974134849027904397 26672878115300568385464149)
                ·
                  refine ⟨156286395206839267883579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 26672878115300568385464149 156286395206839267883579)
                  ·
                    rfl

theorem cell21_684825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 9].length) (baseStart_684825 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_684825 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_684825 prefixEnd_684825 := by exact prefixLift 684825
  have htrace : WordTrace (prefixWord ++ tailWord_684825) baseStart_684825 baseEnd_684825 := by
    simpa [prefixWord, tailWord_684825, baseEnd_684825] using wordTrace_append hprefix tailTrace_684825
  have hstable : (prefixWord ++ tailWord_684825).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684825).length < 2 ^ (prefixWord ++ tailWord_684825).sum := by decide
  have hdescent : baseEnd_684825 < baseStart_684825 := by decide
  rcases family_descends (prefixWord ++ tailWord_684825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684876 : List Nat := [2, 2, 1, 3, 3, 2, 2, 3, 3]
def baseStart_684876 : Nat := 118140960795 + 684876 * 2 ^ 59
def prefixEnd_684876 : Nat := 4983230072969 + 3 ^ 40 * 684876 * 2
def baseEnd_684876 : Nat := 156298034101674512533475

theorem tailTrace_684876 : CollatzResearch.WordTrace tailWord_684876 prefixEnd_684876 156298034101674512533475 := by
  unfold tailWord_684876
  simp only [CollatzResearch.WordTrace]
  refine ⟨12489739933409347176825241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16652986577879129569100321 12489739933409347176825241)
  ·
    refine ⟨9367304950057010382618931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12489739933409347176825241 9367304950057010382618931)
    ·
      refine ⟨14050957425085515573928397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9367304950057010382618931 14050957425085515573928397)
      ·
        refine ⟨5269109034407068340223149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14050957425085515573928397 5269109034407068340223149)
        ·
          refine ⟨1975915887902650627583681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5269109034407068340223149 1975915887902650627583681)
          ·
            refine ⟨1481936915926987970687761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1975915887902650627583681 1481936915926987970687761)
            ·
              refine ⟨1111452686945240978015821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1481936915926987970687761 1111452686945240978015821)
              ·
                refine ⟨416794757604465366755933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1111452686945240978015821 416794757604465366755933)
                ·
                  refine ⟨156298034101674512533475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 416794757604465366755933 156298034101674512533475)
                  ·
                    rfl

theorem cell21_684876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 2, 3, 3].length) (baseStart_684876 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_684876 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_684876 prefixEnd_684876 := by exact prefixLift 684876
  have htrace : WordTrace (prefixWord ++ tailWord_684876) baseStart_684876 baseEnd_684876 := by
    simpa [prefixWord, tailWord_684876, baseEnd_684876] using wordTrace_append hprefix tailTrace_684876
  have hstable : (prefixWord ++ tailWord_684876).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684876).length < 2 ^ (prefixWord ++ tailWord_684876).sum := by decide
  have hdescent : baseEnd_684876 < baseStart_684876 := by decide
  rcases family_descends (prefixWord ++ tailWord_684876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684887 : List Nat := [1, 1, 3, 2, 4, 2, 8]
def baseStart_684887 : Nat := 118140960795 + 684887 * 2 ^ 59
def prefixEnd_684887 : Nat := 4983230072969 + 3 ^ 40 * 684887 * 2
def baseEnd_684887 : Nat := 17366727161282326427791

theorem tailTrace_684887 : CollatzResearch.WordTrace tailWord_684887 prefixEnd_684887 17366727161282326427791 := by
  unfold tailWord_684887
  simp only [CollatzResearch.WordTrace]
  refine ⟨24979881069778843232300915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16653254046519228821533943 24979881069778843232300915)
  ·
    refine ⟨37469821604668264848451373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24979881069778843232300915 37469821604668264848451373)
    ·
      refine ⟨14051183101750599318169265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37469821604668264848451373 14051183101750599318169265)
      ·
        refine ⟨10538387326312949488626949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14051183101750599318169265 10538387326312949488626949)
        ·
          refine ⟨1975947623683678029117553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10538387326312949488626949 1975947623683678029117553)
          ·
            refine ⟨1481960717762758521838165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1975947623683678029117553 1481960717762758521838165)
            ·
              refine ⟨17366727161282326427791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1481960717762758521838165 17366727161282326427791)
              ·
                rfl

theorem cell21_684887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 8].length) (baseStart_684887 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_684887 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_684887 prefixEnd_684887 := by exact prefixLift 684887
  have htrace : WordTrace (prefixWord ++ tailWord_684887) baseStart_684887 baseEnd_684887 := by
    simpa [prefixWord, tailWord_684887, baseEnd_684887] using wordTrace_append hprefix tailTrace_684887
  have hstable : (prefixWord ++ tailWord_684887).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684887).length < 2 ^ (prefixWord ++ tailWord_684887).sum := by decide
  have hdescent : baseEnd_684887 < baseStart_684887 := by decide
  rcases family_descends (prefixWord ++ tailWord_684887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684890 : List Nat := [3, 1, 1, 2, 1, 6, 1, 2, 4]
def baseStart_684890 : Nat := 118140960795 + 684890 * 2 ^ 59
def prefixEnd_684890 : Nat := 4983230072969 + 3 ^ 40 * 684890 * 2
def baseEnd_684890 : Nat := 156301229092413599300113

theorem tailTrace_684890 : CollatzResearch.WordTrace tailWord_684890 prefixEnd_684890 156301229092413599300113 := by
  unfold tailWord_684890
  simp only [CollatzResearch.WordTrace]
  refine ⟨6244997622191993686165031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16653326992511983163106749 6244997622191993686165031)
  ·
    refine ⟨9367496433287990529247547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6244997622191993686165031 9367496433287990529247547)
    ·
      refine ⟨14051244649931985793871321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9367496433287990529247547 14051244649931985793871321)
      ·
        refine ⟨10538433487448989345403491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14051244649931985793871321 10538433487448989345403491)
        ·
          refine ⟨15807650231173484018105237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10538433487448989345403491 15807650231173484018105237)
          ·
            refine ⟨740983604586257063348683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 15807650231173484018105237 740983604586257063348683)
            ·
              refine ⟨1111475406879385595023025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 740983604586257063348683 1111475406879385595023025)
              ·
                refine ⟨833606555159539196267269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1111475406879385595023025 833606555159539196267269)
                ·
                  refine ⟨156301229092413599300113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 833606555159539196267269 156301229092413599300113)
                  ·
                    rfl

theorem cell21_684890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 1, 2, 4].length) (baseStart_684890 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_684890 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_684890 prefixEnd_684890 := by exact prefixLift 684890
  have htrace : WordTrace (prefixWord ++ tailWord_684890) baseStart_684890 baseEnd_684890 := by
    simpa [prefixWord, tailWord_684890, baseEnd_684890] using wordTrace_append hprefix tailTrace_684890
  have hstable : (prefixWord ++ tailWord_684890).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684890).length < 2 ^ (prefixWord ++ tailWord_684890).sum := by decide
  have hdescent : baseEnd_684890 < baseStart_684890 := by decide
  rcases family_descends (prefixWord ++ tailWord_684890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685053 : List Nat := [1, 4, 1, 1, 1, 2, 1, 1, 9]
def baseStart_685053 : Nat := 118140960795 + 685053 * 2 ^ 59
def prefixEnd_685053 : Nat := 4983230072969 + 3 ^ 40 * 685053 * 2
def baseEnd_685053 : Nat := 156338427913161538083113

theorem tailTrace_685053 : CollatzResearch.WordTrace tailWord_685053 prefixEnd_685053 156338427913161538083113 := by
  unfold tailWord_685053
  simp only [CollatzResearch.WordTrace]
  refine ⟨24985935587177453582843813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16657290391451635721895875 24985935587177453582843813)
  ·
    refine ⟨4684862922595772546783215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24985935587177453582843813 4684862922595772546783215)
    ·
      refine ⟨7027294383893658820174823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4684862922595772546783215 7027294383893658820174823)
      ·
        refine ⟨10540941575840488230262235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7027294383893658820174823 10540941575840488230262235)
        ·
          refine ⟨15811412363760732345393353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10540941575840488230262235 15811412363760732345393353)
          ·
            refine ⟨11858559272820549259045015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15811412363760732345393353 11858559272820549259045015)
            ·
              refine ⟨17787838909230823888567523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11858559272820549259045015 17787838909230823888567523)
              ·
                refine ⟨26681758363846235832851285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17787838909230823888567523 26681758363846235832851285)
                ·
                  refine ⟨156338427913161538083113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 26681758363846235832851285 156338427913161538083113)
                  ·
                    rfl

theorem cell21_685053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 9].length) (baseStart_685053 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_685053 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_685053 prefixEnd_685053 := by exact prefixLift 685053
  have htrace : WordTrace (prefixWord ++ tailWord_685053) baseStart_685053 baseEnd_685053 := by
    simpa [prefixWord, tailWord_685053, baseEnd_685053] using wordTrace_append hprefix tailTrace_685053
  have hstable : (prefixWord ++ tailWord_685053).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685053).length < 2 ^ (prefixWord ++ tailWord_685053).sum := by decide
  have hdescent : baseEnd_685053 < baseStart_685053 := by decide
  rcases family_descends (prefixWord ++ tailWord_685053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685070 : List Nat := [4, 1, 1, 2, 2, 2, 1, 3, 5]
def baseStart_685070 : Nat := 118140960795 + 685070 * 2 ^ 59
def prefixEnd_685070 : Nat := 4983230072969 + 3 ^ 40 * 685070 * 2
def baseEnd_685070 : Nat := 156342307544773286299745

theorem tailTrace_685070 : CollatzResearch.WordTrace tailWord_685070 prefixEnd_685070 156342307544773286299745 := by
  unfold tailWord_685070
  simp only [CollatzResearch.WordTrace]
  refine ⟨3123319453514483185776583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16657703752077243657475109 3123319453514483185776583)
  ·
    refine ⟨4684979180271724778664875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3123319453514483185776583 4684979180271724778664875)
    ·
      refine ⟨7027468770407587167997313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4684979180271724778664875 7027468770407587167997313)
      ·
        refine ⟨5270601577805690375997985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7027468770407587167997313 5270601577805690375997985)
        ·
          refine ⟨3952951183354267781998489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5270601577805690375997985 3952951183354267781998489)
          ·
            refine ⟨2964713387515700836498867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3952951183354267781998489 2964713387515700836498867)
            ·
              refine ⟨4447070081273551254748301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2964713387515700836498867 4447070081273551254748301)
              ·
                refine ⟨1667651280477581720530613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4447070081273551254748301 1667651280477581720530613)
                ·
                  refine ⟨156342307544773286299745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1667651280477581720530613 156342307544773286299745)
                  ·
                    rfl

theorem cell21_685070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 3, 5].length) (baseStart_685070 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_685070 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_685070 prefixEnd_685070 := by exact prefixLift 685070
  have htrace : WordTrace (prefixWord ++ tailWord_685070) baseStart_685070 baseEnd_685070 := by
    simpa [prefixWord, tailWord_685070, baseEnd_685070] using wordTrace_append hprefix tailTrace_685070
  have hstable : (prefixWord ++ tailWord_685070).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685070).length < 2 ^ (prefixWord ++ tailWord_685070).sum := by decide
  have hdescent : baseEnd_685070 < baseStart_685070 := by decide
  rcases family_descends (prefixWord ++ tailWord_685070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685121 : List Nat := [1, 2, 5, 1, 3, 1, 3, 2, 3]
def baseStart_685121 : Nat := 118140960795 + 685121 * 2 ^ 59
def prefixEnd_685121 : Nat := 4983230072969 + 3 ^ 40 * 685121 * 2
def baseEnd_685121 : Nat := 156353946439608530949641

theorem tailTrace_685121 : CollatzResearch.WordTrace tailWord_685121 prefixEnd_685121 156353946439608530949641 := by
  unfold tailWord_685121
  simp only [CollatzResearch.WordTrace]
  refine ⟨24988415750931101196319217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16658943833954067464212811 24988415750931101196319217)
  ·
    refine ⟨18741311813198325897239413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24988415750931101196319217 18741311813198325897239413)
    ·
      refine ⟨1756997982487343052866195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18741311813198325897239413 1756997982487343052866195)
      ·
        refine ⟨2635496973731014579299293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1756997982487343052866195 2635496973731014579299293)
        ·
          refine ⟨988311365149130467237235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2635496973731014579299293 988311365149130467237235)
          ·
            refine ⟨1482467047723695700855853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 988311365149130467237235 1482467047723695700855853)
            ·
              refine ⟨555925142896385887820945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1482467047723695700855853 555925142896385887820945)
              ·
                refine ⟨416943857172289415865709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 555925142896385887820945 416943857172289415865709)
                ·
                  refine ⟨156353946439608530949641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 416943857172289415865709 156353946439608530949641)
                  ·
                    rfl

theorem cell21_685121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 3, 2, 3].length) (baseStart_685121 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_685121 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_685121 prefixEnd_685121 := by exact prefixLift 685121
  have htrace : WordTrace (prefixWord ++ tailWord_685121) baseStart_685121 baseEnd_685121 := by
    simpa [prefixWord, tailWord_685121, baseEnd_685121] using wordTrace_append hprefix tailTrace_685121
  have hstable : (prefixWord ++ tailWord_685121).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685121).length < 2 ^ (prefixWord ++ tailWord_685121).sum := by decide
  have hdescent : baseEnd_685121 < baseStart_685121 := by decide
  rcases family_descends (prefixWord ++ tailWord_685121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685129 : List Nat := [1, 2, 1, 1, 2, 2, 2, 5, 5]
def baseStart_685129 : Nat := 118140960795 + 685129 * 2 ^ 59
def prefixEnd_685129 : Nat := 4983230072969 + 3 ^ 40 * 685129 * 2
def baseEnd_685129 : Nat := 156355772148602294816291

theorem tailTrace_685129 : CollatzResearch.WordTrace tailWord_685129 prefixEnd_685129 156355772148602294816291 := by
  unfold tailWord_685129
  simp only [CollatzResearch.WordTrace]
  refine ⟨24988707534902118562610441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16659138356601412375073627 24988707534902118562610441)
  ·
    refine ⟨18741530651176588921957831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24988707534902118562610441 18741530651176588921957831)
    ·
      refine ⟨28112295976764883382936747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18741530651176588921957831 28112295976764883382936747)
      ·
        refine ⟨42168443965147325074405121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28112295976764883382936747 42168443965147325074405121)
        ·
          refine ⟨31626332973860493805803841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42168443965147325074405121 31626332973860493805803841)
          ·
            refine ⟨23719749730395370354352881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31626332973860493805803841 23719749730395370354352881)
            ·
              refine ⟨17789812297796527765764661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23719749730395370354352881 17789812297796527765764661)
              ·
                refine ⟨1667794902918424478040437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17789812297796527765764661 1667794902918424478040437)
                ·
                  refine ⟨156355772148602294816291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1667794902918424478040437 156355772148602294816291)
                  ·
                    rfl

theorem cell21_685129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 5, 5].length) (baseStart_685129 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_685129 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_685129 prefixEnd_685129 := by exact prefixLift 685129
  have htrace : WordTrace (prefixWord ++ tailWord_685129) baseStart_685129 baseEnd_685129 := by
    simpa [prefixWord, tailWord_685129, baseEnd_685129] using wordTrace_append hprefix tailTrace_685129
  have hstable : (prefixWord ++ tailWord_685129).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685129).length < 2 ^ (prefixWord ++ tailWord_685129).sum := by decide
  have hdescent : baseEnd_685129 < baseStart_685129 := by decide
  rcases family_descends (prefixWord ++ tailWord_685129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685208 : List Nat := [2, 1, 2, 4, 2, 2, 3, 5]
def baseStart_685208 : Nat := 118140960795 + 685208 * 2 ^ 59
def prefixEnd_685208 : Nat := 4983230072969 + 3 ^ 40 * 685208 * 2
def baseEnd_685208 : Nat := 52124600341638570999821

theorem tailTrace_685208 : CollatzResearch.WordTrace tailWord_685208 prefixEnd_685208 52124600341638570999821 := by
  unfold tailWord_685208
  simp only [CollatzResearch.WordTrace]
  refine ⟨12495794450807957527368139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16661059267743943369824185 12495794450807957527368139)
  ·
    refine ⟨18743691676211936291052209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12495794450807957527368139 18743691676211936291052209)
    ·
      refine ⟨14057768757158952218289157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18743691676211936291052209 14057768757158952218289157)
      ·
        refine ⟨2635831641967303540929217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14057768757158952218289157 2635831641967303540929217)
        ·
          refine ⟨1976873731475477655696913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2635831641967303540929217 1976873731475477655696913)
          ·
            refine ⟨1482655298606608241772685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1976873731475477655696913 1482655298606608241772685)
            ·
              refine ⟨555995736977478090664757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1482655298606608241772685 555995736977478090664757)
              ·
                refine ⟨52124600341638570999821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 555995736977478090664757 52124600341638570999821)
                ·
                  rfl

theorem cell21_685208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 3, 5].length) (baseStart_685208 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_685208 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_685208 prefixEnd_685208 := by exact prefixLift 685208
  have htrace : WordTrace (prefixWord ++ tailWord_685208) baseStart_685208 baseEnd_685208 := by
    simpa [prefixWord, tailWord_685208, baseEnd_685208] using wordTrace_append hprefix tailTrace_685208
  have hstable : (prefixWord ++ tailWord_685208).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685208).length < 2 ^ (prefixWord ++ tailWord_685208).sum := by decide
  have hdescent : baseEnd_685208 < baseStart_685208 := by decide
  rcases family_descends (prefixWord ++ tailWord_685208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685343 : List Nat := [1, 1, 2, 4, 5, 8]
def baseStart_685343 : Nat := 118140960795 + 685343 * 2 ^ 59
def prefixEnd_685343 : Nat := 4983230072969 + 3 ^ 40 * 685343 * 2
def baseEnd_685343 : Nat := 5792763328303165861081

theorem tailTrace_685343 : CollatzResearch.WordTrace tailWord_685343 prefixEnd_685343 5792763328303165861081 := by
  unfold tailWord_685343
  simp only [CollatzResearch.WordTrace]
  refine ⟨24996512756126833110900683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16664341837417888740600455 24996512756126833110900683)
  ·
    refine ⟨37494769134190249666351025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24996512756126833110900683 37494769134190249666351025)
    ·
      refine ⟨28121076850642687249763269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37494769134190249666351025 28121076850642687249763269)
      ·
        refine ⟨5272701909495503859330613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28121076850642687249763269 5272701909495503859330613)
        ·
          refine ⟨494315804015203486812245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5272701909495503859330613 494315804015203486812245)
          ·
            refine ⟨5792763328303165861081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 494315804015203486812245 5792763328303165861081)
            ·
              rfl

theorem cell21_685343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 8].length) (baseStart_685343 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_685343 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_685343 prefixEnd_685343 := by exact prefixLift 685343
  have htrace : WordTrace (prefixWord ++ tailWord_685343) baseStart_685343 baseEnd_685343 := by
    simpa [prefixWord, tailWord_685343, baseEnd_685343] using wordTrace_append hprefix tailTrace_685343
  have hstable : (prefixWord ++ tailWord_685343).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685343).length < 2 ^ (prefixWord ++ tailWord_685343).sum := by decide
  have hdescent : baseEnd_685343 < baseStart_685343 := by decide
  rcases family_descends (prefixWord ++ tailWord_685343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685346 : List Nat := [3, 3, 1, 1, 4, 1, 2, 2, 4]
def baseStart_685346 : Nat := 118140960795 + 685346 * 2 ^ 59
def prefixEnd_685346 : Nat := 4983230072969 + 3 ^ 40 * 685346 * 2
def baseEnd_685346 : Nat := 156405294505058139699181

theorem tailTrace_685346 : CollatzResearch.WordTrace tailWord_685346 prefixEnd_685346 156405294505058139699181 := by
  unfold tailWord_685346
  simp only [CollatzResearch.WordTrace]
  refine ⟨6249155543778991155814973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16664414783410643082173261 6249155543778991155814973)
  ·
    refine ⟨2343433328917121683430615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6249155543778991155814973 2343433328917121683430615)
    ·
      refine ⟨3515149993375682525145923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2343433328917121683430615 3515149993375682525145923)
      ·
        refine ⟨5272724990063523787718885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3515149993375682525145923 5272724990063523787718885)
        ·
          refine ⟨988635935636910710197291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5272724990063523787718885 988635935636910710197291)
          ·
            refine ⟨1482953903455366065295937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 988635935636910710197291 1482953903455366065295937)
            ·
              refine ⟨1112215427591524548971953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1482953903455366065295937 1112215427591524548971953)
              ·
                refine ⟨834161570693643411728965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1112215427591524548971953 834161570693643411728965)
                ·
                  refine ⟨156405294505058139699181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 834161570693643411728965 156405294505058139699181)
                  ·
                    rfl

theorem cell21_685346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 2, 2, 4].length) (baseStart_685346 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_685346 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_685346 prefixEnd_685346 := by exact prefixLift 685346
  have htrace : WordTrace (prefixWord ++ tailWord_685346) baseStart_685346 baseEnd_685346 := by
    simpa [prefixWord, tailWord_685346, baseEnd_685346] using wordTrace_append hprefix tailTrace_685346
  have hstable : (prefixWord ++ tailWord_685346).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685346).length < 2 ^ (prefixWord ++ tailWord_685346).sum := by decide
  have hdescent : baseEnd_685346 < baseStart_685346 := by decide
  rcases family_descends (prefixWord ++ tailWord_685346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685374 : List Nat := [4, 2, 1, 2, 1, 1, 3, 2, 5]
def baseStart_685374 : Nat := 118140960795 + 685374 * 2 ^ 59
def prefixEnd_685374 : Nat := 4983230072969 + 3 ^ 40 * 685374 * 2
def baseEnd_685374 : Nat := 156411684486536313232457

theorem tailTrace_685374 : CollatzResearch.WordTrace tailWord_685374 prefixEnd_685374 156411684486536313232457 := by
  unfold tailWord_685374
  simp only [CollatzResearch.WordTrace]
  refine ⟨3124705427376815675659897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16665095612676350270186117 3124705427376815675659897)
  ·
    refine ⟨2343529070532611756744923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3124705427376815675659897 2343529070532611756744923)
    ·
      refine ⟨3515293605798917635117385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2343529070532611756744923 3515293605798917635117385)
      ·
        refine ⟨2636470204349188226338039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3515293605798917635117385 2636470204349188226338039)
        ·
          refine ⟨3954705306523782339507059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2636470204349188226338039 3954705306523782339507059)
          ·
            refine ⟨5932057959785673509260589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3954705306523782339507059 5932057959785673509260589)
            ·
              refine ⟨2224521734919627565972721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5932057959785673509260589 2224521734919627565972721)
              ·
                refine ⟨1668391301189720674479541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2224521734919627565972721 1668391301189720674479541)
                ·
                  refine ⟨156411684486536313232457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1668391301189720674479541 156411684486536313232457)
                  ·
                    rfl

theorem cell21_685374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 2, 5].length) (baseStart_685374 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_685374 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_685374 prefixEnd_685374 := by exact prefixLift 685374
  have htrace : WordTrace (prefixWord ++ tailWord_685374) baseStart_685374 baseEnd_685374 := by
    simpa [prefixWord, tailWord_685374, baseEnd_685374] using wordTrace_append hprefix tailTrace_685374
  have hstable : (prefixWord ++ tailWord_685374).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685374).length < 2 ^ (prefixWord ++ tailWord_685374).sum := by decide
  have hdescent : baseEnd_685374 < baseStart_685374 := by decide
  rcases family_descends (prefixWord ++ tailWord_685374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685433 : List Nat := [1, 2, 1, 3, 2, 1, 4, 2, 5]
def baseStart_685433 : Nat := 118140960795 + 685433 * 2 ^ 59
def prefixEnd_685433 : Nat := 4983230072969 + 3 ^ 40 * 685433 * 2
def baseEnd_685433 : Nat := 156425149090365321749003

theorem tailTrace_685433 : CollatzResearch.WordTrace tailWord_685433 prefixEnd_685433 156425149090365321749003 := by
  unfold tailWord_685433
  simp only [CollatzResearch.WordTrace]
  refine ⟨24999795325800778481676953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16666530217200518987784635 24999795325800778481676953)
  ·
    refine ⟨18749846494350583861257715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24999795325800778481676953 18749846494350583861257715)
    ·
      refine ⟨28124769741525875791886573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18749846494350583861257715 28124769741525875791886573)
      ·
        refine ⟨10546788653072203421957465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28124769741525875791886573 10546788653072203421957465)
        ·
          refine ⟨7910091489804152566468099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10546788653072203421957465 7910091489804152566468099)
          ·
            refine ⟨11865137234706228849702149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7910091489804152566468099 11865137234706228849702149)
            ·
              refine ⟨2224713231507417909319153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11865137234706228849702149 2224713231507417909319153)
              ·
                refine ⟨1668534923630563431989365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2224713231507417909319153 1668534923630563431989365)
                ·
                  refine ⟨156425149090365321749003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1668534923630563431989365 156425149090365321749003)
                  ·
                    rfl

theorem cell21_685433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 2, 5].length) (baseStart_685433 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_685433 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_685433 prefixEnd_685433 := by exact prefixLift 685433
  have htrace : WordTrace (prefixWord ++ tailWord_685433) baseStart_685433 baseEnd_685433 := by
    simpa [prefixWord, tailWord_685433, baseEnd_685433] using wordTrace_append hprefix tailTrace_685433
  have hstable : (prefixWord ++ tailWord_685433).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685433).length < 2 ^ (prefixWord ++ tailWord_685433).sum := by decide
  have hdescent : baseEnd_685433 < baseStart_685433 := by decide
  rcases family_descends (prefixWord ++ tailWord_685433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685585 : List Nat := [1, 2, 2, 1, 1, 2, 6, 1, 5]
def baseStart_685585 : Nat := 118140960795 + 685585 * 2 ^ 59
def prefixEnd_685585 : Nat := 4983230072969 + 3 ^ 40 * 685585 * 2
def baseEnd_685585 : Nat := 156459837561246835215359

theorem tailTrace_685585 : CollatzResearch.WordTrace tailWord_685585 prefixEnd_685585 156459837561246835215359 := by
  unfold tailWord_685585
  simp only [CollatzResearch.WordTrace]
  refine ⟨25005339221250108441210209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16670226147500072294140139 25005339221250108441210209)
  ·
    refine ⟨18754004415937581330907657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25005339221250108441210209 18754004415937581330907657)
    ·
      refine ⟨14065503311953185998180743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18754004415937581330907657 14065503311953185998180743)
      ·
        refine ⟨21098254967929778997271115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14065503311953185998180743 21098254967929778997271115)
        ·
          refine ⟨31647382451894668495906673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21098254967929778997271115 31647382451894668495906673)
          ·
            refine ⟨23735536838921001371930005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31647382451894668495906673 23735536838921001371930005)
            ·
              refine ⟨1112603289324421939309219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 23735536838921001371930005 1112603289324421939309219)
              ·
                refine ⟨1668904933986632908963829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1112603289324421939309219 1668904933986632908963829)
                ·
                  refine ⟨156459837561246835215359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1668904933986632908963829 156459837561246835215359)
                  ·
                    rfl

theorem cell21_685585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 6, 1, 5].length) (baseStart_685585 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_685585 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_685585 prefixEnd_685585 := by exact prefixLift 685585
  have htrace : WordTrace (prefixWord ++ tailWord_685585) baseStart_685585 baseEnd_685585 := by
    simpa [prefixWord, tailWord_685585, baseEnd_685585] using wordTrace_append hprefix tailTrace_685585
  have hstable : (prefixWord ++ tailWord_685585).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685585).length < 2 ^ (prefixWord ++ tailWord_685585).sum := by decide
  have hdescent : baseEnd_685585 < baseStart_685585 := by decide
  rcases family_descends (prefixWord ++ tailWord_685585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685619 : List Nat := [1, 1, 1, 2, 4, 5, 1, 3, 3]
def baseStart_685619 : Nat := 118140960795 + 685619 * 2 ^ 59
def prefixEnd_685619 : Nat := 4983230072969 + 3 ^ 40 * 685619 * 2
def baseEnd_685619 : Nat := 156467596824470331648623

theorem tailTrace_685619 : CollatzResearch.WordTrace tailWord_685619 prefixEnd_685619 156467596824470331648623 := by
  unfold tailWord_685619
  simp only [CollatzResearch.WordTrace]
  refine ⟨25006579303126932247947911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16671052868751288165298607 25006579303126932247947911)
  ·
    refine ⟨37509868954690398371921867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25006579303126932247947911 37509868954690398371921867)
    ·
      refine ⟨56264803432035597557882801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37509868954690398371921867 56264803432035597557882801)
      ·
        refine ⟨42198602574026698168412101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56264803432035597557882801 42198602574026698168412101)
        ·
          refine ⟨7912237982630005906577269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42198602574026698168412101 7912237982630005906577269)
          ·
            refine ⟨741772310871563053741619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7912237982630005906577269 741772310871563053741619)
            ·
              refine ⟨1112658466307344580612429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 741772310871563053741619 1112658466307344580612429)
              ·
                refine ⟨417246924865254217729661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1112658466307344580612429 417246924865254217729661)
                ·
                  refine ⟨156467596824470331648623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 417246924865254217729661 156467596824470331648623)
                  ·
                    rfl

theorem cell21_685619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 1, 3, 3].length) (baseStart_685619 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_685619 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_685619 prefixEnd_685619 := by exact prefixLift 685619
  have htrace : WordTrace (prefixWord ++ tailWord_685619) baseStart_685619 baseEnd_685619 := by
    simpa [prefixWord, tailWord_685619, baseEnd_685619] using wordTrace_append hprefix tailTrace_685619
  have hstable : (prefixWord ++ tailWord_685619).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685619).length < 2 ^ (prefixWord ++ tailWord_685619).sum := by decide
  have hdescent : baseEnd_685619 < baseStart_685619 := by decide
  rcases family_descends (prefixWord ++ tailWord_685619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685650 : List Nat := [3, 2, 2, 1, 2, 4, 2, 1, 4]
def baseStart_685650 : Nat := 118140960795 + 685650 * 2 ^ 59
def prefixEnd_685650 : Nat := 4983230072969 + 3 ^ 40 * 685650 * 2
def baseEnd_685650 : Nat := 156474671446821166631893

theorem tailTrace_685650 : CollatzResearch.WordTrace tailWord_685650 prefixEnd_685650 156474671446821166631893 := by
  unfold tailWord_685650
  simp only [CollatzResearch.WordTrace]
  refine ⟨6251927491503656135581601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16671806644009749694884269 6251927491503656135581601)
  ·
    refine ⟨4688945618627742101686201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6251927491503656135581601 4688945618627742101686201)
    ·
      refine ⟨3516709213970806576264651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4688945618627742101686201 3516709213970806576264651)
      ·
        refine ⟨5275063820956209864396977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3516709213970806576264651 5275063820956209864396977)
        ·
          refine ⟨3956297865717157398297733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5275063820956209864396977 3956297865717157398297733)
          ·
            refine ⟨741805849821967012180825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3956297865717157398297733 741805849821967012180825)
            ·
              refine ⟨556354387366475259135619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 741805849821967012180825 556354387366475259135619)
              ·
                refine ⟨834531581049712888703429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 556354387366475259135619 834531581049712888703429)
                ·
                  refine ⟨156474671446821166631893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 834531581049712888703429 156474671446821166631893)
                  ·
                    rfl

theorem cell21_685650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 2, 1, 4].length) (baseStart_685650 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_685650 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_685650 prefixEnd_685650 := by exact prefixLift 685650
  have htrace : WordTrace (prefixWord ++ tailWord_685650) baseStart_685650 baseEnd_685650 := by
    simpa [prefixWord, tailWord_685650, baseEnd_685650] using wordTrace_append hprefix tailTrace_685650
  have hstable : (prefixWord ++ tailWord_685650).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685650).length < 2 ^ (prefixWord ++ tailWord_685650).sum := by decide
  have hdescent : baseEnd_685650 < baseStart_685650 := by decide
  rcases family_descends (prefixWord ++ tailWord_685650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685754 : List Nat := [3, 1, 1, 1, 2, 4, 2, 4, 3]
def baseStart_685754 : Nat := 118140960795 + 685754 * 2 ^ 59
def prefixEnd_685754 : Nat := 4983230072969 + 3 ^ 40 * 685754 * 2
def baseEnd_685754 : Nat := 156498405663740096898347

theorem tailTrace_685754 : CollatzResearch.WordTrace tailWord_685754 prefixEnd_685754 156498405663740096898347 := by
  unfold tailWord_685754
  simp only [CollatzResearch.WordTrace]
  refine ⟨6252875789409462576028079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16674335438425233536074877 6252875789409462576028079)
  ·
    refine ⟨9379313684114193864042119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6252875789409462576028079 9379313684114193864042119)
    ·
      refine ⟨14068970526171290796063179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9379313684114193864042119 14068970526171290796063179)
      ·
        refine ⟨21103455789256936194094769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14068970526171290796063179 21103455789256936194094769)
        ·
          refine ⟨15827591841942702145571077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21103455789256936194094769 15827591841942702145571077)
          ·
            refine ⟨2967673470364256652294577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15827591841942702145571077 2967673470364256652294577)
            ·
              refine ⟨2225755102773192489220933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2967673470364256652294577 2225755102773192489220933)
              ·
                refine ⟨417329081769973591728925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2225755102773192489220933 417329081769973591728925)
                ·
                  refine ⟨156498405663740096898347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 417329081769973591728925 156498405663740096898347)
                  ·
                    rfl

theorem cell21_685754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 4, 3].length) (baseStart_685754 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_685754 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_685754 prefixEnd_685754 := by exact prefixLift 685754
  have htrace : WordTrace (prefixWord ++ tailWord_685754) baseStart_685754 baseEnd_685754 := by
    simpa [prefixWord, tailWord_685754, baseEnd_685754] using wordTrace_append hprefix tailTrace_685754
  have hstable : (prefixWord ++ tailWord_685754).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685754).length < 2 ^ (prefixWord ++ tailWord_685754).sum := by decide
  have hdescent : baseEnd_685754 < baseStart_685754 := by decide
  rcases family_descends (prefixWord ++ tailWord_685754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685864 : List Nat := [2, 1, 5, 1, 1, 4, 2, 2, 3]
def baseStart_685864 : Nat := 118140960795 + 685864 * 2 ^ 59
def prefixEnd_685864 : Nat := 4983230072969 + 3 ^ 40 * 685864 * 2
def baseEnd_685864 : Nat := 156523509162404350064789

theorem tailTrace_685864 : CollatzResearch.WordTrace tailWord_685864 prefixEnd_685864 156523509162404350064789 := by
  unfold tailWord_685864
  simp only [CollatzResearch.WordTrace]
  refine ⟨12507757593619669545308323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16677010124826226060411097 12507757593619669545308323)
  ·
    refine ⟨18761636390429504317962485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12507757593619669545308323 18761636390429504317962485)
    ·
      refine ⟨1758903411602766029808983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18761636390429504317962485 1758903411602766029808983)
      ·
        refine ⟨2638355117404149044713475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1758903411602766029808983 2638355117404149044713475)
        ·
          refine ⟨3957532676106223567070213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2638355117404149044713475 3957532676106223567070213)
          ·
            refine ⟨742037376769916918825665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3957532676106223567070213 742037376769916918825665)
            ·
              refine ⟨556528032577437689119249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 742037376769916918825665 556528032577437689119249)
              ·
                refine ⟨417396024433078266839437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 556528032577437689119249 417396024433078266839437)
                ·
                  refine ⟨156523509162404350064789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 417396024433078266839437 156523509162404350064789)
                  ·
                    rfl

theorem cell21_685864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 2, 2, 3].length) (baseStart_685864 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_685864 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_685864 prefixEnd_685864 := by exact prefixLift 685864
  have htrace : WordTrace (prefixWord ++ tailWord_685864) baseStart_685864 baseEnd_685864 := by
    simpa [prefixWord, tailWord_685864, baseEnd_685864] using wordTrace_append hprefix tailTrace_685864
  have hstable : (prefixWord ++ tailWord_685864).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685864).length < 2 ^ (prefixWord ++ tailWord_685864).sum := by decide
  have hdescent : baseEnd_685864 < baseStart_685864 := by decide
  rcases family_descends (prefixWord ++ tailWord_685864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685875 : List Nat := [1, 1, 1, 2, 7, 2, 1, 6]
def baseStart_685875 : Nat := 118140960795 + 685875 * 2 ^ 59
def prefixEnd_685875 : Nat := 4983230072969 + 3 ^ 40 * 685875 * 2
def baseEnd_685875 : Nat := 52175339837423591793811

theorem tailTrace_685875 : CollatzResearch.WordTrace tailWord_685875 prefixEnd_685875 52175339837423591793811 := by
  unfold tailWord_685875
  simp only [CollatzResearch.WordTrace]
  refine ⟨25015916390199487969267079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16677277593466325312844719 25015916390199487969267079)
  ·
    refine ⟨37523874585299231953900619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25015916390199487969267079 37523874585299231953900619)
    ·
      refine ⟨56285811877948847930850929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37523874585299231953900619 56285811877948847930850929)
      ·
        refine ⟨42214358908461635948138197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56285811877948847930850929 42214358908461635948138197)
        ·
          refine ⟨989399036917069592534489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 42214358908461635948138197 989399036917069592534489)
          ·
            refine ⟨742049277687802194400867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 989399036917069592534489 742049277687802194400867)
            ·
              refine ⟨1113073916531703291601301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 742049277687802194400867 1113073916531703291601301)
              ·
                refine ⟨52175339837423591793811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1113073916531703291601301 52175339837423591793811)
                ·
                  rfl

theorem cell21_685875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 1, 6].length) (baseStart_685875 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_685875 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_685875 prefixEnd_685875 := by exact prefixLift 685875
  have htrace : WordTrace (prefixWord ++ tailWord_685875) baseStart_685875 baseEnd_685875 := by
    simpa [prefixWord, tailWord_685875, baseEnd_685875] using wordTrace_append hprefix tailTrace_685875
  have hstable : (prefixWord ++ tailWord_685875).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685875).length < 2 ^ (prefixWord ++ tailWord_685875).sum := by decide
  have hdescent : baseEnd_685875 < baseStart_685875 := by decide
  rcases family_descends (prefixWord ++ tailWord_685875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685906 : List Nat := [3, 2, 2, 1, 1, 3, 1, 5, 3]
def baseStart_685906 : Nat := 118140960795 + 685906 * 2 ^ 59
def prefixEnd_685906 : Nat := 4983230072969 + 3 ^ 40 * 685906 * 2
def baseEnd_685906 : Nat := 156533094134621610364703

theorem tailTrace_685906 : CollatzResearch.WordTrace tailWord_685906 prefixEnd_685906 156533094134621610364703 := by
  unfold tailWord_685906
  simp only [CollatzResearch.WordTrace]
  refine ⟨6254261763271795065911393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16678031368724786842430381 6254261763271795065911393)
  ·
    refine ⟨4690696322453846299433545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6254261763271795065911393 4690696322453846299433545)
    ·
      refine ⟨3518022241840384724575159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4690696322453846299433545 3518022241840384724575159)
      ·
        refine ⟨5277033362760577086862739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3518022241840384724575159 5277033362760577086862739)
        ·
          refine ⟨7915550044140865630294109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5277033362760577086862739 7915550044140865630294109)
          ·
            refine ⟨2968331266552824611360291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7915550044140865630294109 2968331266552824611360291)
            ·
              refine ⟨4452496899829236917040437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2968331266552824611360291 4452496899829236917040437)
              ·
                refine ⟨417421584358990960972541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4452496899829236917040437 417421584358990960972541)
                ·
                  refine ⟨156533094134621610364703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 417421584358990960972541 156533094134621610364703)
                  ·
                    rfl

theorem cell21_685906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 5, 3].length) (baseStart_685906 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_685906 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_685906 prefixEnd_685906 := by exact prefixLift 685906
  have htrace : WordTrace (prefixWord ++ tailWord_685906) baseStart_685906 baseEnd_685906 := by
    simpa [prefixWord, tailWord_685906, baseEnd_685906] using wordTrace_append hprefix tailTrace_685906
  have hstable : (prefixWord ++ tailWord_685906).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685906).length < 2 ^ (prefixWord ++ tailWord_685906).sum := by decide
  have hdescent : baseEnd_685906 < baseStart_685906 := by decide
  rcases family_descends (prefixWord ++ tailWord_685906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685920 : List Nat := [2, 1, 1, 3, 3, 2, 3, 2, 4]
def baseStart_685920 : Nat := 118140960795 + 685920 * 2 ^ 59
def prefixEnd_685920 : Nat := 4983230072969 + 3 ^ 40 * 685920 * 2
def baseEnd_685920 : Nat := 156536289125360697131341

theorem tailTrace_685920 : CollatzResearch.WordTrace tailWord_685920 prefixEnd_685920 156536289125360697131341 := by
  unfold tailWord_685920
  simp only [CollatzResearch.WordTrace]
  refine ⟨12508778837518230327327607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16678371783357640436436809 12508778837518230327327607)
  ·
    refine ⟨18763168256277345490991411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12508778837518230327327607 18763168256277345490991411)
    ·
      refine ⟨28144752384416018236487117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18763168256277345490991411 28144752384416018236487117)
      ·
        refine ⟨10554282144156006838682669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28144752384416018236487117 10554282144156006838682669)
        ·
          refine ⟨3957855804058502564506001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10554282144156006838682669 3957855804058502564506001)
          ·
            refine ⟨2968391853043876923379501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3957855804058502564506001 2968391853043876923379501)
            ·
              refine ⟨1113146944891453846267313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2968391853043876923379501 1113146944891453846267313)
              ·
                refine ⟨834860208668590384700485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1113146944891453846267313 834860208668590384700485)
                ·
                  refine ⟨156536289125360697131341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 834860208668590384700485 156536289125360697131341)
                  ·
                    rfl

theorem cell21_685920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 3, 2, 4].length) (baseStart_685920 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_685920 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_685920 prefixEnd_685920 := by exact prefixLift 685920
  have htrace : WordTrace (prefixWord ++ tailWord_685920) baseStart_685920 baseEnd_685920 := by
    simpa [prefixWord, tailWord_685920, baseEnd_685920] using wordTrace_append hprefix tailTrace_685920
  have hstable : (prefixWord ++ tailWord_685920).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685920).length < 2 ^ (prefixWord ++ tailWord_685920).sum := by decide
  have hdescent : baseEnd_685920 < baseStart_685920 := by decide
  rcases family_descends (prefixWord ++ tailWord_685920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685974 : List Nat := [5, 3, 1, 1, 2, 1, 3, 2, 3]
def baseStart_685974 : Nat := 118140960795 + 685974 * 2 ^ 59
def prefixEnd_685974 : Nat := 4983230072969 + 3 ^ 40 * 685974 * 2
def baseEnd_685974 : Nat := 156548612661068603231231

theorem tailTrace_685974 : CollatzResearch.WordTrace tailWord_685974 prefixEnd_685974 156548612661068603231231 := by
  unfold tailWord_685974
  simp only [CollatzResearch.WordTrace]
  refine ⟨1563720451052551742320061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16679684811227218584747317 1563720451052551742320061)
  ·
    refine ⟨586395169144706903370023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1563720451052551742320061 586395169144706903370023)
    ·
      refine ⟨879592753717060355055035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 586395169144706903370023 879592753717060355055035)
      ·
        refine ⟨1319389130575590532582553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 879592753717060355055035 1319389130575590532582553)
        ·
          refine ⟨989541847931692899436915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1319389130575590532582553 989541847931692899436915)
          ·
            refine ⟨1484312771897539349155373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 989541847931692899436915 1484312771897539349155373)
            ·
              refine ⟨556617289461577255933265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1484312771897539349155373 556617289461577255933265)
              ·
                refine ⟨417462967096182941949949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 556617289461577255933265 417462967096182941949949)
                ·
                  refine ⟨156548612661068603231231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 417462967096182941949949 156548612661068603231231)
                  ·
                    rfl

theorem cell21_685974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_685974 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_685974 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_685974 prefixEnd_685974 := by exact prefixLift 685974
  have htrace : WordTrace (prefixWord ++ tailWord_685974) baseStart_685974 baseEnd_685974 := by
    simpa [prefixWord, tailWord_685974, baseEnd_685974] using wordTrace_append hprefix tailTrace_685974
  have hstable : (prefixWord ++ tailWord_685974).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685974).length < 2 ^ (prefixWord ++ tailWord_685974).sum := by decide
  have hdescent : baseEnd_685974 < baseStart_685974 := by decide
  rcases family_descends (prefixWord ++ tailWord_685974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686165 : List Nat := [1, 3, 2, 2, 1, 5, 2, 1, 4]
def baseStart_686165 : Nat := 118140960795 + 686165 * 2 ^ 59
def prefixEnd_686165 : Nat := 4983230072969 + 3 ^ 40 * 686165 * 2
def baseEnd_686165 : Nat := 156592201463294715547507

theorem tailTrace_686165 : CollatzResearch.WordTrace tailWord_686165 prefixEnd_686165 156592201463294715547507 := by
  unfold tailWord_686165
  simp only [CollatzResearch.WordTrace]
  refine ⟨25026493559148867497323949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16684329039432578331549299 25026493559148867497323949)
  ·
    refine ⟨9384935084680825311496481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25026493559148867497323949 9384935084680825311496481)
    ·
      refine ⟨7038701313510618983622361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9384935084680825311496481 7038701313510618983622361)
      ·
        refine ⟨5279025985132964237716771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7038701313510618983622361 5279025985132964237716771)
        ·
          refine ⟨7918538977699446356575157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5279025985132964237716771 7918538977699446356575157)
          ·
            refine ⟨742363029159323095928921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7918538977699446356575157 742363029159323095928921)
            ·
              refine ⟨556772271869492321946691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 742363029159323095928921 556772271869492321946691)
              ·
                refine ⟨835158407804238482920037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 556772271869492321946691 835158407804238482920037)
                ·
                  refine ⟨156592201463294715547507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 835158407804238482920037 156592201463294715547507)
                  ·
                    rfl

theorem cell21_686165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 2, 1, 4].length) (baseStart_686165 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_686165 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_686165 prefixEnd_686165 := by exact prefixLift 686165
  have htrace : WordTrace (prefixWord ++ tailWord_686165) baseStart_686165 baseEnd_686165 := by
    simpa [prefixWord, tailWord_686165, baseEnd_686165] using wordTrace_append hprefix tailTrace_686165
  have hstable : (prefixWord ++ tailWord_686165).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686165).length < 2 ^ (prefixWord ++ tailWord_686165).sum := by decide
  have hdescent : baseEnd_686165 < baseStart_686165 := by decide
  rcases family_descends (prefixWord ++ tailWord_686165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686193 : List Nat := [1, 2, 2, 2, 1, 1, 4, 5, 3]
def baseStart_686193 : Nat := 118140960795 + 686193 * 2 ^ 59
def prefixEnd_686193 : Nat := 4983230072969 + 3 ^ 40 * 686193 * 2
def baseEnd_686193 : Nat := 156598591444772889080783

theorem tailTrace_686193 : CollatzResearch.WordTrace tailWord_686193 prefixEnd_686193 156598591444772889080783 := by
  unfold tailWord_686193
  simp only [CollatzResearch.WordTrace]
  refine ⟨25027514803047428279343233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16685009868698285519562155 25027514803047428279343233)
  ·
    refine ⟨18770636102285571209507425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25027514803047428279343233 18770636102285571209507425)
    ·
      refine ⟨14077977076714178407130569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18770636102285571209507425 14077977076714178407130569)
      ·
        refine ⟨10558482807535633805347927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14077977076714178407130569 10558482807535633805347927)
        ·
          refine ⟨15837724211303450708021891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10558482807535633805347927 15837724211303450708021891)
          ·
            refine ⟨23756586316955176062032837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15837724211303450708021891 23756586316955176062032837)
            ·
              refine ⟨4454359934429095511631157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23756586316955176062032837 4454359934429095511631157)
              ·
                refine ⟨417596243852727704215421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4454359934429095511631157 417596243852727704215421)
                ·
                  refine ⟨156598591444772889080783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 417596243852727704215421 156598591444772889080783)
                  ·
                    rfl

theorem cell21_686193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 5, 3].length) (baseStart_686193 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_686193 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_686193 prefixEnd_686193 := by exact prefixLift 686193
  have htrace : WordTrace (prefixWord ++ tailWord_686193) baseStart_686193 baseEnd_686193 := by
    simpa [prefixWord, tailWord_686193, baseEnd_686193] using wordTrace_append hprefix tailTrace_686193
  have hstable : (prefixWord ++ tailWord_686193).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686193).length < 2 ^ (prefixWord ++ tailWord_686193).sum := by decide
  have hdescent : baseEnd_686193 < baseStart_686193 := by decide
  rcases family_descends (prefixWord ++ tailWord_686193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686373 : List Nat := [1, 3, 1, 2, 5, 9]
def baseStart_686373 : Nat := 118140960795 + 686373 * 2 ^ 59
def prefixEnd_686373 : Nat := 4983230072969 + 3 ^ 40 * 686373 * 2
def baseEnd_686373 : Nat := 5801469255449354669645

theorem tailTrace_686373 : CollatzResearch.WordTrace tailWord_686373 prefixEnd_686373 5801469255449354669645 := by
  unfold tailWord_686373
  simp only [CollatzResearch.WordTrace]
  refine ⟨25034079942395319020895773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16689386628263546013930515 25034079942395319020895773)
  ·
    refine ⟨9387779978398244632835915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25034079942395319020895773 9387779978398244632835915)
    ·
      refine ⟨14081669967597366949253873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9387779978398244632835915 14081669967597366949253873)
      ·
        refine ⟨10561252475698025211940405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14081669967597366949253873 10561252475698025211940405)
        ·
          refine ⟨990117419596689863619413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10561252475698025211940405 990117419596689863619413)
          ·
            refine ⟨5801469255449354669645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 990117419596689863619413 5801469255449354669645)
            ·
              rfl

theorem cell21_686373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 9].length) (baseStart_686373 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_686373 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_686373 prefixEnd_686373 := by exact prefixLift 686373
  have htrace : WordTrace (prefixWord ++ tailWord_686373) baseStart_686373 baseEnd_686373 := by
    simpa [prefixWord, tailWord_686373, baseEnd_686373] using wordTrace_append hprefix tailTrace_686373
  have hstable : (prefixWord ++ tailWord_686373).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686373).length < 2 ^ (prefixWord ++ tailWord_686373).sum := by decide
  have hdescent : baseEnd_686373 < baseStart_686373 := by decide
  rcases family_descends (prefixWord ++ tailWord_686373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686525 : List Nat := [1, 4, 1, 2, 2, 2, 2, 7]
def baseStart_686525 : Nat := 118140960795 + 686525 * 2 ^ 59
def prefixEnd_686525 : Nat := 4983230072969 + 3 ^ 40 * 686525 * 2
def baseEnd_686525 : Nat := 52224786122671363182257

theorem tailTrace_686525 : CollatzResearch.WordTrace tailWord_686525 prefixEnd_686525 52224786122671363182257 := by
  unfold tailWord_686525
  simp only [CollatzResearch.WordTrace]
  refine ⟨25039623837844648980429029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16693082558563099320286019 25039623837844648980429029)
  ·
    refine ⟨4694929469595871683830443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25039623837844648980429029 4694929469595871683830443)
    ·
      refine ⟨7042394204393807525745665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4694929469595871683830443 7042394204393807525745665)
      ·
        refine ⟨5281795653295355644309249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7042394204393807525745665 5281795653295355644309249)
        ·
          refine ⟨3961346739971516733231937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5281795653295355644309249 3961346739971516733231937)
          ·
            refine ⟨2971010054978637549923953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3961346739971516733231937 2971010054978637549923953)
            ·
              refine ⟨2228257541233978162442965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2971010054978637549923953 2228257541233978162442965)
              ·
                refine ⟨52224786122671363182257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2228257541233978162442965 52224786122671363182257)
                ·
                  rfl

theorem cell21_686525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 7].length) (baseStart_686525 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_686525 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_686525 prefixEnd_686525 := by exact prefixLift 686525
  have htrace : WordTrace (prefixWord ++ tailWord_686525) baseStart_686525 baseEnd_686525 := by
    simpa [prefixWord, tailWord_686525, baseEnd_686525] using wordTrace_append hprefix tailTrace_686525
  have hstable : (prefixWord ++ tailWord_686525).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686525).length < 2 ^ (prefixWord ++ tailWord_686525).sum := by decide
  have hdescent : baseEnd_686525 < baseStart_686525 := by decide
  rcases family_descends (prefixWord ++ tailWord_686525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686573 : List Nat := [1, 5, 1, 3, 1, 2, 1, 2, 5]
def baseStart_686573 : Nat := 118140960795 + 686573 * 2 ^ 59
def prefixEnd_686573 : Nat := 4983230072969 + 3 ^ 40 * 686573 * 2
def baseEnd_686573 : Nat := 156685312621976672746673

theorem tailTrace_686573 : CollatzResearch.WordTrace tailWord_686573 prefixEnd_686573 156685312621976672746673 := by
  unfold tailWord_686573
  simp only [CollatzResearch.WordTrace]
  refine ⟨25041374541670753178176373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16694249694447168785450915 25041374541670753178176373)
  ·
    refine ⟨2347628863281633110454035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25041374541670753178176373 2347628863281633110454035)
    ·
      refine ⟨3521443294922449665681053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2347628863281633110454035 3521443294922449665681053)
      ·
        refine ⟨1320541235595918624630395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3521443294922449665681053 1320541235595918624630395)
        ·
          refine ⟨1980811853393877936945593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1320541235595918624630395 1980811853393877936945593)
          ·
            refine ⟨1485608890045408452709195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1980811853393877936945593 1485608890045408452709195)
            ·
              refine ⟨2228413335068112679063793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1485608890045408452709195 2228413335068112679063793)
              ·
                refine ⟨1671310001301084509297845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2228413335068112679063793 1671310001301084509297845)
                ·
                  refine ⟨156685312621976672746673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1671310001301084509297845 156685312621976672746673)
                  ·
                    rfl

theorem cell21_686573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 2, 5].length) (baseStart_686573 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_686573 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_686573 prefixEnd_686573 := by exact prefixLift 686573
  have htrace : WordTrace (prefixWord ++ tailWord_686573) baseStart_686573 baseEnd_686573 := by
    simpa [prefixWord, tailWord_686573, baseEnd_686573] using wordTrace_append hprefix tailTrace_686573
  have hstable : (prefixWord ++ tailWord_686573).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686573).length < 2 ^ (prefixWord ++ tailWord_686573).sum := by decide
  have hdescent : baseEnd_686573 < baseStart_686573 := by decide
  rcases family_descends (prefixWord ++ tailWord_686573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686604 : List Nat := [2, 2, 1, 2, 4, 3, 1, 2, 4]
def baseStart_686604 : Nat := 118140960795 + 686604 * 2 ^ 59
def prefixEnd_686604 : Nat := 4983230072969 + 3 ^ 40 * 686604 * 2
def baseEnd_686604 : Nat := 156692387244327507729943

theorem tailTrace_686604 : CollatzResearch.WordTrace tailWord_686604 prefixEnd_686604 156692387244327507729943 := by
  unfold tailWord_686604
  simp only [CollatzResearch.WordTrace]
  refine ⟨12521252602279222736277433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16695003469705630315036577 12521252602279222736277433)
  ·
    refine ⟨9390939451709417052208075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12521252602279222736277433 9390939451709417052208075)
    ·
      refine ⟨14086409177564125578312113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9390939451709417052208075 14086409177564125578312113)
      ·
        refine ⟨10564806883173094183734085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14086409177564125578312113 10564806883173094183734085)
        ·
          refine ⟨1980901290594955159450141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10564806883173094183734085 1980901290594955159450141)
          ·
            refine ⟨742837983973108184793803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1980901290594955159450141 742837983973108184793803)
            ·
              refine ⟨1114256975959662277190705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 742837983973108184793803 1114256975959662277190705)
              ·
                refine ⟨835692731969746707893029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1114256975959662277190705 835692731969746707893029)
                ·
                  refine ⟨156692387244327507729943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 835692731969746707893029 156692387244327507729943)
                  ·
                    rfl

theorem cell21_686604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 1, 2, 4].length) (baseStart_686604 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_686604 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_686604 prefixEnd_686604 := by exact prefixLift 686604
  have htrace : WordTrace (prefixWord ++ tailWord_686604) baseStart_686604 baseEnd_686604 := by
    simpa [prefixWord, tailWord_686604, baseEnd_686604] using wordTrace_append hprefix tailTrace_686604
  have hstable : (prefixWord ++ tailWord_686604).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686604).length < 2 ^ (prefixWord ++ tailWord_686604).sum := by decide
  have hdescent : baseEnd_686604 < baseStart_686604 := by decide
  rcases family_descends (prefixWord ++ tailWord_686604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686666 : List Nat := [3, 1, 2, 1, 1, 5, 3, 2, 3]
def baseStart_686666 : Nat := 118140960795 + 686666 * 2 ^ 59
def prefixEnd_686666 : Nat := 4983230072969 + 3 ^ 40 * 686666 * 2
def baseEnd_686666 : Nat := 156706536489029177696483

theorem tailTrace_686666 : CollatzResearch.WordTrace tailWord_686666 prefixEnd_686666 156706536489029177696483 := by
  unfold tailWord_686666
  simp only [CollatzResearch.WordTrace]
  refine ⟨6261191632583457515327963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16696511020222553374207901 6261191632583457515327963)
  ·
    refine ⟨9391787448875186272991945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6261191632583457515327963 9391787448875186272991945)
    ·
      refine ⟨7043840586656389704743959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9391787448875186272991945 7043840586656389704743959)
      ·
        refine ⟨10565760879984584557115939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7043840586656389704743959 10565760879984584557115939)
        ·
          refine ⟨15848641319976876835673909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10565760879984584557115939 15848641319976876835673909)
          ·
            refine ⟨1485810123747832203344429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15848641319976876835673909 1485810123747832203344429)
            ·
              refine ⟨557178796405437076254161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1485810123747832203344429 557178796405437076254161)
              ·
                refine ⟨417884097304077807190621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 557178796405437076254161 417884097304077807190621)
                ·
                  refine ⟨156706536489029177696483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 417884097304077807190621 156706536489029177696483)
                  ·
                    rfl

theorem cell21_686666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 3, 2, 3].length) (baseStart_686666 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_686666 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_686666 prefixEnd_686666 := by exact prefixLift 686666
  have htrace : WordTrace (prefixWord ++ tailWord_686666) baseStart_686666 baseEnd_686666 := by
    simpa [prefixWord, tailWord_686666, baseEnd_686666] using wordTrace_append hprefix tailTrace_686666
  have hstable : (prefixWord ++ tailWord_686666).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686666).length < 2 ^ (prefixWord ++ tailWord_686666).sum := by decide
  have hdescent : baseEnd_686666 < baseStart_686666 := by decide
  rcases family_descends (prefixWord ++ tailWord_686666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686691 : List Nat := [1, 1, 1, 5, 1, 2, 2, 1, 7]
def baseStart_686691 : Nat := 118140960795 + 686691 * 2 ^ 59
def prefixEnd_686691 : Nat := 4983230072969 + 3 ^ 40 * 686691 * 2
def baseEnd_686691 : Nat := 156712241829634689779765

theorem tailTrace_686691 : CollatzResearch.WordTrace tailWord_686691 prefixEnd_686691 156712241829634689779765 := by
  unfold tailWord_686691
  simp only [CollatzResearch.WordTrace]
  refine ⟨25045678355243259330971927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16697118903495506220647951 25045678355243259330971927)
  ·
    refine ⟨37568517532864888996457891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25045678355243259330971927 37568517532864888996457891)
    ·
      refine ⟨56352776299297333494686837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37568517532864888996457891 56352776299297333494686837)
      ·
        refine ⟨5283072778059125015126891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 56352776299297333494686837 5283072778059125015126891)
        ·
          refine ⟨7924609167088687522690337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5283072778059125015126891 7924609167088687522690337)
          ·
            refine ⟨5943456875316515642017753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7924609167088687522690337 5943456875316515642017753)
            ·
              refine ⟨4457592656487386731513315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5943456875316515642017753 4457592656487386731513315)
              ·
                refine ⟨6686388984731080097269973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4457592656487386731513315 6686388984731080097269973)
                ·
                  refine ⟨156712241829634689779765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6686388984731080097269973 156712241829634689779765)
                  ·
                    rfl

theorem cell21_686691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 1, 7].length) (baseStart_686691 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_686691 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_686691 prefixEnd_686691 := by exact prefixLift 686691
  have htrace : WordTrace (prefixWord ++ tailWord_686691) baseStart_686691 baseEnd_686691 := by
    simpa [prefixWord, tailWord_686691, baseEnd_686691] using wordTrace_append hprefix tailTrace_686691
  have hstable : (prefixWord ++ tailWord_686691).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686691).length < 2 ^ (prefixWord ++ tailWord_686691).sum := by decide
  have hdescent : baseEnd_686691 < baseStart_686691 := by decide
  rcases family_descends (prefixWord ++ tailWord_686691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686725 : List Nat := [1, 3, 1, 1, 4, 3, 1, 4, 3]
def baseStart_686725 : Nat := 118140960795 + 686725 * 2 ^ 59
def prefixEnd_686725 : Nat := 4983230072969 + 3 ^ 40 * 686725 * 2
def baseEnd_686725 : Nat := 156720001092858186213029

theorem tailTrace_686725 : CollatzResearch.WordTrace tailWord_686725 prefixEnd_686725 156720001092858186213029 := by
  unfold tailWord_686725
  simp only [CollatzResearch.WordTrace]
  refine ⟨25046918437120083137709629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16697945624746722091806419 25046918437120083137709629)
  ·
    refine ⟨9392594413920031176641111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25046918437120083137709629 9392594413920031176641111)
    ·
      refine ⟨14088891620880046764961667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9392594413920031176641111 14088891620880046764961667)
      ·
        refine ⟨21133337431320070147442501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14088891620880046764961667 21133337431320070147442501)
        ·
          refine ⟨3962500768372513152645469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21133337431320070147442501 3962500768372513152645469)
          ·
            refine ⟨1485937788139692432242051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3962500768372513152645469 1485937788139692432242051)
            ·
              refine ⟨2228906682209538648363077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1485937788139692432242051 2228906682209538648363077)
              ·
                refine ⟨417920002914288496568077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2228906682209538648363077 417920002914288496568077)
                ·
                  refine ⟨156720001092858186213029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 417920002914288496568077 156720001092858186213029)
                  ·
                    rfl

theorem cell21_686725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 4, 3].length) (baseStart_686725 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_686725 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_686725 prefixEnd_686725 := by exact prefixLift 686725
  have htrace : WordTrace (prefixWord ++ tailWord_686725) baseStart_686725 baseEnd_686725 := by
    simpa [prefixWord, tailWord_686725, baseEnd_686725] using wordTrace_append hprefix tailTrace_686725
  have hstable : (prefixWord ++ tailWord_686725).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686725).length < 2 ^ (prefixWord ++ tailWord_686725).sum := by decide
  have hdescent : baseEnd_686725 < baseStart_686725 := by decide
  rcases family_descends (prefixWord ++ tailWord_686725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686759 : List Nat := [1, 1, 6, 3, 1, 1, 2, 3, 3]
def baseStart_686759 : Nat := 118140960795 + 686759 * 2 ^ 59
def prefixEnd_686759 : Nat := 4983230072969 + 3 ^ 40 * 686759 * 2
def baseEnd_686759 : Nat := 156727760356081682646293

theorem tailTrace_686759 : CollatzResearch.WordTrace tailWord_686759 prefixEnd_686759 156727760356081682646293 := by
  unfold tailWord_686759
  simp only [CollatzResearch.WordTrace]
  refine ⟨25048158518996906944447331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16698772345997937962964887 25048158518996906944447331)
  ·
    refine ⟨37572237778495360416670997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25048158518996906944447331 37572237778495360416670997)
    ·
      refine ⟨1761198645866970019531453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 37572237778495360416670997 1761198645866970019531453)
      ·
        refine ⟨660449492200113757324295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1761198645866970019531453 660449492200113757324295)
        ·
          refine ⟨990674238300170635986443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 660449492200113757324295 990674238300170635986443)
          ·
            refine ⟨1486011357450255953979665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 990674238300170635986443 1486011357450255953979665)
            ·
              refine ⟨1114508518087691965484749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1486011357450255953979665 1114508518087691965484749)
              ·
                refine ⟨417940694282884487056781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1114508518087691965484749 417940694282884487056781)
                ·
                  refine ⟨156727760356081682646293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 417940694282884487056781 156727760356081682646293)
                  ·
                    rfl

theorem cell21_686759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 2, 3, 3].length) (baseStart_686759 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_686759 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_686759 prefixEnd_686759 := by exact prefixLift 686759
  have htrace : WordTrace (prefixWord ++ tailWord_686759) baseStart_686759 baseEnd_686759 := by
    simpa [prefixWord, tailWord_686759, baseEnd_686759] using wordTrace_append hprefix tailTrace_686759
  have hstable : (prefixWord ++ tailWord_686759).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686759).length < 2 ^ (prefixWord ++ tailWord_686759).sum := by decide
  have hdescent : baseEnd_686759 < baseStart_686759 := by decide
  rcases family_descends (prefixWord ++ tailWord_686759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686784 : List Nat := [2, 1, 1, 2, 4, 3, 2, 1, 5]
def baseStart_686784 : Nat := 118140960795 + 686784 * 2 ^ 59
def prefixEnd_686784 : Nat := 4983230072969 + 3 ^ 40 * 686784 * 2
def baseEnd_686784 : Nat := 156733465696687194729575

theorem tailTrace_686784 : CollatzResearch.WordTrace tailWord_686784 prefixEnd_686784 156733465696687194729575 := by
  unfold tailWord_686784
  simp only [CollatzResearch.WordTrace]
  refine ⟨12524535171953168107053703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16699380229270890809404937 12524535171953168107053703)
  ·
    refine ⟨18786802757929752160580555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12524535171953168107053703 18786802757929752160580555)
    ·
      refine ⟨28180204136894628240870833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18786802757929752160580555 28180204136894628240870833)
      ·
        refine ⟨21135153102670971180653125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28180204136894628240870833 21135153102670971180653125)
        ·
          refine ⟨3962841206750807096372461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21135153102670971180653125 3962841206750807096372461)
          ·
            refine ⟨1486065452531552661139673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3962841206750807096372461 1486065452531552661139673)
            ·
              refine ⟨1114549089398664495854755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1486065452531552661139673 1114549089398664495854755)
              ·
                refine ⟨1671823634097996743782133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1114549089398664495854755 1671823634097996743782133)
                ·
                  refine ⟨156733465696687194729575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1671823634097996743782133 156733465696687194729575)
                  ·
                    rfl

theorem cell21_686784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 2, 1, 5].length) (baseStart_686784 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_686784 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_686784 prefixEnd_686784 := by exact prefixLift 686784
  have htrace : WordTrace (prefixWord ++ tailWord_686784) baseStart_686784 baseEnd_686784 := by
    simpa [prefixWord, tailWord_686784, baseEnd_686784] using wordTrace_append hprefix tailTrace_686784
  have hstable : (prefixWord ++ tailWord_686784).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686784).length < 2 ^ (prefixWord ++ tailWord_686784).sum := by decide
  have hdescent : baseEnd_686784 < baseStart_686784 := by decide
  rcases family_descends (prefixWord ++ tailWord_686784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686804 : List Nat := [2, 4, 1, 3, 3, 1, 2, 5]
def baseStart_686804 : Nat := 118140960795 + 686804 * 2 ^ 59
def prefixEnd_686804 : Nat := 4983230072969 + 3 ^ 40 * 686804 * 2
def baseEnd_686804 : Nat := 52246009989723868132067

theorem tailTrace_686804 : CollatzResearch.WordTrace tailWord_686804 prefixEnd_686804 52246009989723868132067 := by
  unfold tailWord_686804
  simp only [CollatzResearch.WordTrace]
  refine ⟨12524899901916939814917733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16699866535889253086556977 12524899901916939814917733)
  ·
    refine ⟨2348418731609426215297075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12524899901916939814917733 2348418731609426215297075)
    ·
      refine ⟨3522628097414139322945613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2348418731609426215297075 3522628097414139322945613)
      ·
        refine ⟨1320985536530302246104605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3522628097414139322945613 1320985536530302246104605)
        ·
          refine ⟨495369576198863342289227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1320985536530302246104605 495369576198863342289227)
          ·
            refine ⟨743054364298295013433841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 495369576198863342289227 743054364298295013433841)
            ·
              refine ⟨557290773223721260075381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 743054364298295013433841 557290773223721260075381)
              ·
                refine ⟨52246009989723868132067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 557290773223721260075381 52246009989723868132067)
                ·
                  rfl

theorem cell21_686804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 2, 5].length) (baseStart_686804 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_686804 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_686804 prefixEnd_686804 := by exact prefixLift 686804
  have htrace : WordTrace (prefixWord ++ tailWord_686804) baseStart_686804 baseEnd_686804 := by
    simpa [prefixWord, tailWord_686804, baseEnd_686804] using wordTrace_append hprefix tailTrace_686804
  have hstable : (prefixWord ++ tailWord_686804).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686804).length < 2 ^ (prefixWord ++ tailWord_686804).sum := by decide
  have hdescent : baseEnd_686804 < baseStart_686804 := by decide
  rcases family_descends (prefixWord ++ tailWord_686804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686846 : List Nat := [4, 2, 2, 1, 2, 2, 2, 6]
def baseStart_686846 : Nat := 118140960795 + 686846 * 2 ^ 59
def prefixEnd_686846 : Nat := 4983230072969 + 3 ^ 40 * 686846 * 2
def baseEnd_686846 : Nat := 52249204980462954898705

theorem tailTrace_686846 : CollatzResearch.WordTrace tailWord_686846 prefixEnd_686846 52249204980462954898705 := by
  unfold tailWord_686846
  simp only [CollatzResearch.WordTrace]
  refine ⟨3131416458710215100358049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16700887779787813868576261 3131416458710215100358049)
  ·
    refine ⟨2348562344032661325268537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3131416458710215100358049 2348562344032661325268537)
    ·
      refine ⟨1761421758024495993951403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2348562344032661325268537 1761421758024495993951403)
      ·
        refine ⟨2642132637036743990927105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1761421758024495993951403 2642132637036743990927105)
        ·
          refine ⟨1981599477777557993195329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2642132637036743990927105 1981599477777557993195329)
          ·
            refine ⟨1486199608333168494896497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1981599477777557993195329 1486199608333168494896497)
            ·
              refine ⟨1114649706249876371172373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1486199608333168494896497 1114649706249876371172373)
              ·
                refine ⟨52249204980462954898705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1114649706249876371172373 52249204980462954898705)
                ·
                  rfl

theorem cell21_686846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 2, 6].length) (baseStart_686846 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_686846 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_686846 prefixEnd_686846 := by exact prefixLift 686846
  have htrace : WordTrace (prefixWord ++ tailWord_686846) baseStart_686846 baseEnd_686846 := by
    simpa [prefixWord, tailWord_686846, baseEnd_686846] using wordTrace_append hprefix tailTrace_686846
  have hstable : (prefixWord ++ tailWord_686846).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686846).length < 2 ^ (prefixWord ++ tailWord_686846).sum := by decide
  have hdescent : baseEnd_686846 < baseStart_686846 := by decide
  rcases family_descends (prefixWord ++ tailWord_686846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686894 : List Nat := [4, 1, 3, 2, 1, 2, 1, 4, 3]
def baseStart_686894 : Nat := 118140960795 + 686894 * 2 ^ 59
def prefixEnd_686894 : Nat := 4983230072969 + 3 ^ 40 * 686894 * 2
def baseEnd_686894 : Nat := 156758569195351447896017

theorem tailTrace_686894 : CollatzResearch.WordTrace tailWord_686894 prefixEnd_686894 156758569195351447896017 := by
  unfold tailWord_686894
  simp only [CollatzResearch.WordTrace]
  refine ⟨3131635296688478125076467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16702054915671883333741157 3131635296688478125076467)
  ·
    refine ⟨4697452945032717187614701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3131635296688478125076467 4697452945032717187614701)
    ·
      refine ⟨1761544854387268945355513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4697452945032717187614701 1761544854387268945355513)
      ·
        refine ⟨1321158640790451709016635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1761544854387268945355513 1321158640790451709016635)
        ·
          refine ⟨1981737961185677563524953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1321158640790451709016635 1981737961185677563524953)
          ·
            refine ⟨1486303470889258172643715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1981737961185677563524953 1486303470889258172643715)
            ·
              refine ⟨2229455206333887258965573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1486303470889258172643715 2229455206333887258965573)
              ·
                refine ⟨418022851187603861056045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2229455206333887258965573 418022851187603861056045)
                ·
                  refine ⟨156758569195351447896017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 418022851187603861056045 156758569195351447896017)
                  ·
                    rfl

theorem cell21_686894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 4, 3].length) (baseStart_686894 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_686894 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_686894 prefixEnd_686894 := by exact prefixLift 686894
  have htrace : WordTrace (prefixWord ++ tailWord_686894) baseStart_686894 baseEnd_686894 := by
    simpa [prefixWord, tailWord_686894, baseEnd_686894] using wordTrace_append hprefix tailTrace_686894
  have hstable : (prefixWord ++ tailWord_686894).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686894).length < 2 ^ (prefixWord ++ tailWord_686894).sum := by decide
  have hdescent : baseEnd_686894 < baseStart_686894 := by decide
  rcases family_descends (prefixWord ++ tailWord_686894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686981 : List Nat := [1, 3, 1, 1, 3, 3, 4, 5]
def baseStart_686981 : Nat := 118140960795 + 686981 * 2 ^ 59
def prefixEnd_686981 : Nat := 4983230072969 + 3 ^ 40 * 686981 * 2
def baseEnd_686981 : Nat := 52259474593552876648613

theorem tailTrace_686981 : CollatzResearch.WordTrace tailWord_686981 prefixEnd_686981 52259474593552876648613 := by
  unfold tailWord_686981
  simp only [CollatzResearch.WordTrace]
  refine ⟨25056255524192638859028797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16704170349461759239352531 25056255524192638859028797)
  ·
    refine ⟨9396095821572239572135799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25056255524192638859028797 9396095821572239572135799)
    ·
      refine ⟨14094143732358359358203699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9396095821572239572135799 14094143732358359358203699)
      ·
        refine ⟨21141215598537539037305549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14094143732358359358203699 21141215598537539037305549)
        ·
          refine ⟨7927955849451577138989581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21141215598537539037305549 7927955849451577138989581)
          ·
            refine ⟨2972983443544341427121093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7927955849451577138989581 2972983443544341427121093)
            ·
              refine ⟨557434395664564017585205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2972983443544341427121093 557434395664564017585205)
              ·
                refine ⟨52259474593552876648613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 557434395664564017585205 52259474593552876648613)
                ·
                  rfl

theorem cell21_686981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 4, 5].length) (baseStart_686981 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_686981 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_686981 prefixEnd_686981 := by exact prefixLift 686981
  have htrace : WordTrace (prefixWord ++ tailWord_686981) baseStart_686981 baseEnd_686981 := by
    simpa [prefixWord, tailWord_686981, baseEnd_686981] using wordTrace_append hprefix tailTrace_686981
  have hstable : (prefixWord ++ tailWord_686981).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686981).length < 2 ^ (prefixWord ++ tailWord_686981).sum := by decide
  have hdescent : baseEnd_686981 < baseStart_686981 := by decide
  rcases family_descends (prefixWord ++ tailWord_686981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687040 : List Nat := [2, 1, 1, 2, 3, 3, 2, 7]
def baseStart_687040 : Nat := 118140960795 + 687040 * 2 ^ 59
def prefixEnd_687040 : Nat := 4983230072969 + 3 ^ 40 * 687040 * 2
def baseEnd_687040 : Nat := 52263962794829212820795

theorem tailTrace_687040 : CollatzResearch.WordTrace tailWord_687040 prefixEnd_687040 52263962794829212820795 := by
  unfold tailWord_687040
  simp only [CollatzResearch.WordTrace]
  refine ⟨12529203715489445967713287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16705604953985927956951049 12529203715489445967713287)
  ·
    refine ⟨18793805573234168951569931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12529203715489445967713287 18793805573234168951569931)
    ·
      refine ⟨28190708359851253427354897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18793805573234168951569931 28190708359851253427354897)
      ·
        refine ⟨21143031269888440070516173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28190708359851253427354897 21143031269888440070516173)
        ·
          refine ⟨7928636726208165026443565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21143031269888440070516173 7928636726208165026443565)
          ·
            refine ⟨2973238772328061884916337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7928636726208165026443565 2973238772328061884916337)
            ·
              refine ⟨2229929079246046413687253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2973238772328061884916337 2229929079246046413687253)
              ·
                refine ⟨52263962794829212820795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2229929079246046413687253 52263962794829212820795)
                ·
                  rfl

theorem cell21_687040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 7].length) (baseStart_687040 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_687040 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_687040 prefixEnd_687040 := by exact prefixLift 687040
  have htrace : WordTrace (prefixWord ++ tailWord_687040) baseStart_687040 baseEnd_687040 := by
    simpa [prefixWord, tailWord_687040, baseEnd_687040] using wordTrace_append hprefix tailTrace_687040
  have hstable : (prefixWord ++ tailWord_687040).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687040).length < 2 ^ (prefixWord ++ tailWord_687040).sum := by decide
  have hdescent : baseEnd_687040 < baseStart_687040 := by decide
  rcases family_descends (prefixWord ++ tailWord_687040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687074 : List Nat := [3, 3, 3, 1, 1, 1, 3, 6]
def baseStart_687074 : Nat := 118140960795 + 687074 * 2 ^ 59
def prefixEnd_687074 : Nat := 4983230072969 + 3 ^ 40 * 687074 * 2
def baseEnd_687074 : Nat := 52266549215903711631883

theorem tailTrace_687074 : CollatzResearch.WordTrace tailWord_687074 prefixEnd_687074 52266549215903711631883 := by
  unfold tailWord_687074
  simp only [CollatzResearch.WordTrace]
  refine ⟨6264911878213928935541069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16706431675237143828109517 6264911878213928935541069)
  ·
    refine ⟨2349341954330223350827901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6264911878213928935541069 2349341954330223350827901)
    ·
      refine ⟨881003232873833756560463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2349341954330223350827901 881003232873833756560463)
      ·
        refine ⟨1321504849310750634840695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 881003232873833756560463 1321504849310750634840695)
        ·
          refine ⟨1982257273966125952261043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1321504849310750634840695 1982257273966125952261043)
          ·
            refine ⟨2973385910949188928391565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1982257273966125952261043 2973385910949188928391565)
            ·
              refine ⟨1115019716605945848146837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2973385910949188928391565 1115019716605945848146837)
              ·
                refine ⟨52266549215903711631883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1115019716605945848146837 52266549215903711631883)
                ·
                  rfl

theorem cell21_687074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 3, 6].length) (baseStart_687074 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_687074 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_687074 prefixEnd_687074 := by exact prefixLift 687074
  have htrace : WordTrace (prefixWord ++ tailWord_687074) baseStart_687074 baseEnd_687074 := by
    simpa [prefixWord, tailWord_687074, baseEnd_687074] using wordTrace_append hprefix tailTrace_687074
  have hstable : (prefixWord ++ tailWord_687074).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687074).length < 2 ^ (prefixWord ++ tailWord_687074).sum := by decide
  have hdescent : baseEnd_687074 < baseStart_687074 := by decide
  rcases family_descends (prefixWord ++ tailWord_687074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687105 : List Nat := [1, 2, 4, 1, 2, 3, 2, 3, 3]
def baseStart_687105 : Nat := 118140960795 + 687105 * 2 ^ 59
def prefixEnd_687105 : Nat := 4983230072969 + 3 ^ 40 * 687105 * 2
def baseEnd_687105 : Nat := 156806722270061969878919

theorem tailTrace_687105 : CollatzResearch.WordTrace tailWord_687105 prefixEnd_687105 156806722270061969878919 := by
  unfold tailWord_687105
  simp only [CollatzResearch.WordTrace]
  refine ⟨25060778175743408036542769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16707185450495605357695179 25060778175743408036542769)
  ·
    refine ⟨18795583631807556027407077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25060778175743408036542769 18795583631807556027407077)
    ·
      refine ⟨3524171930963916755138827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18795583631807556027407077 3524171930963916755138827)
      ·
        refine ⟨5286257896445875132708241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3524171930963916755138827 5286257896445875132708241)
        ·
          refine ⟨3964693422334406349531181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5286257896445875132708241 3964693422334406349531181)
          ·
            refine ⟨1486760033375402381074193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3964693422334406349531181 1486760033375402381074193)
            ·
              refine ⟨1115070025031551785805645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1486760033375402381074193 1115070025031551785805645)
              ·
                refine ⟨418151259386831919677117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1115070025031551785805645 418151259386831919677117)
                ·
                  refine ⟨156806722270061969878919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 418151259386831919677117 156806722270061969878919)
                  ·
                    rfl

theorem cell21_687105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 2, 3, 3].length) (baseStart_687105 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_687105 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_687105 prefixEnd_687105 := by exact prefixLift 687105
  have htrace : WordTrace (prefixWord ++ tailWord_687105) baseStart_687105 baseEnd_687105 := by
    simpa [prefixWord, tailWord_687105, baseEnd_687105] using wordTrace_append hprefix tailTrace_687105
  have hstable : (prefixWord ++ tailWord_687105).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687105).length < 2 ^ (prefixWord ++ tailWord_687105).sum := by decide
  have hdescent : baseEnd_687105 < baseStart_687105 := by decide
  rcases family_descends (prefixWord ++ tailWord_687105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687116 : List Nat := [2, 2, 1, 2, 3, 3, 8]
def baseStart_687116 : Nat := 118140960795 + 687116 * 2 ^ 59
def prefixEnd_687116 : Nat := 4983230072969 + 3 ^ 40 * 687116 * 2
def baseEnd_687116 : Nat := 17423248068880932799507

theorem tailTrace_687116 : CollatzResearch.WordTrace tailWord_687116 prefixEnd_687116 17423248068880932799507 := by
  unfold tailWord_687116
  simp only [CollatzResearch.WordTrace]
  refine ⟨12530589689351778457596601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16707452919135704610128801 12530589689351778457596601)
  ·
    refine ⟨9397942267013833843197451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12530589689351778457596601 9397942267013833843197451)
    ·
      refine ⟨14096913400520750764796177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9397942267013833843197451 14096913400520750764796177)
      ·
        refine ⟨10572685050390563073597133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14096913400520750764796177 10572685050390563073597133)
        ·
          refine ⟨3964756893896461152598925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10572685050390563073597133 3964756893896461152598925)
          ·
            refine ⟨1486783835211172932224597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3964756893896461152598925 1486783835211172932224597)
            ·
              refine ⟨17423248068880932799507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1486783835211172932224597 17423248068880932799507)
              ·
                rfl

theorem cell21_687116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 8].length) (baseStart_687116 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_687116 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_687116 prefixEnd_687116 := by exact prefixLift 687116
  have htrace : WordTrace (prefixWord ++ tailWord_687116) baseStart_687116 baseEnd_687116 := by
    simpa [prefixWord, tailWord_687116, baseEnd_687116] using wordTrace_append hprefix tailTrace_687116
  have hstable : (prefixWord ++ tailWord_687116).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687116).length < 2 ^ (prefixWord ++ tailWord_687116).sum := by decide
  have hdescent : baseEnd_687116 < baseStart_687116 := by decide
  rcases family_descends (prefixWord ++ tailWord_687116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687181 : List Nat := [1, 6, 1, 1, 1, 4, 1, 1, 5]
def baseStart_687181 : Nat := 118140960795 + 687181 * 2 ^ 59
def prefixEnd_687181 : Nat := 4983230072969 + 3 ^ 40 * 687181 * 2
def baseEnd_687181 : Nat := 156824066505502726612097

theorem tailTrace_687181 : CollatzResearch.WordTrace tailWord_687181 prefixEnd_687181 156824066505502726612097 := by
  unfold tailWord_687181
  simp only [CollatzResearch.WordTrace]
  refine ⟨25063550123468073016309397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16709033415645382010872931 25063550123468073016309397)
  ·
    refine ⟨1174853912037565922639503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 25063550123468073016309397 1174853912037565922639503)
    ·
      refine ⟨1762280868056348883959255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1174853912037565922639503 1762280868056348883959255)
      ·
        refine ⟨2643421302084523325938883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1762280868056348883959255 2643421302084523325938883)
        ·
          refine ⟨3965131953126784988908325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2643421302084523325938883 3965131953126784988908325)
          ·
            refine ⟨743462241211272185420311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3965131953126784988908325 743462241211272185420311)
            ·
              refine ⟨1115193361816908278130467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 743462241211272185420311 1115193361816908278130467)
              ·
                refine ⟨1672790042725362417195701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1115193361816908278130467 1672790042725362417195701)
                ·
                  refine ⟨156824066505502726612097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1672790042725362417195701 156824066505502726612097)
                  ·
                    rfl

theorem cell21_687181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_687181 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_687181 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_687181 prefixEnd_687181 := by exact prefixLift 687181
  have htrace : WordTrace (prefixWord ++ tailWord_687181) baseStart_687181 baseEnd_687181 := by
    simpa [prefixWord, tailWord_687181, baseEnd_687181] using wordTrace_append hprefix tailTrace_687181
  have hstable : (prefixWord ++ tailWord_687181).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687181).length < 2 ^ (prefixWord ++ tailWord_687181).sum := by decide
  have hdescent : baseEnd_687181 < baseStart_687181 := by decide
  rcases family_descends (prefixWord ++ tailWord_687181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687192 : List Nat := [2, 1, 2, 2, 1, 3, 4, 6]
def baseStart_687192 : Nat := 118140960795 + 687192 * 2 ^ 59
def prefixEnd_687192 : Nat := 4983230072969 + 3 ^ 40 * 687192 * 2
def baseEnd_687192 : Nat := 52275525618456383976247

theorem tailTrace_687192 : CollatzResearch.WordTrace tailWord_687192 prefixEnd_687192 52275525618456383976247 := by
  unfold tailWord_687192
  simp only [CollatzResearch.WordTrace]
  refine ⟨12531975663214110947479915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16709300884285481263306553 12531975663214110947479915)
  ·
    refine ⟨18797963494821166421219873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12531975663214110947479915 18797963494821166421219873)
    ·
      refine ⟨14098472621115874815914905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18797963494821166421219873 14098472621115874815914905)
      ·
        refine ⟨10573854465836906111936179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14098472621115874815914905 10573854465836906111936179)
        ·
          refine ⟨15860781698755359167904269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10573854465836906111936179 15860781698755359167904269)
          ·
            refine ⟨5947793137033259687964101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15860781698755359167904269 5947793137033259687964101)
            ·
              refine ⟨1115211213193736191493269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5947793137033259687964101 1115211213193736191493269)
              ·
                refine ⟨52275525618456383976247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1115211213193736191493269 52275525618456383976247)
                ·
                  rfl

theorem cell21_687192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 4, 6].length) (baseStart_687192 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_687192 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_687192 prefixEnd_687192 := by exact prefixLift 687192
  have htrace : WordTrace (prefixWord ++ tailWord_687192) baseStart_687192 baseEnd_687192 := by
    simpa [prefixWord, tailWord_687192, baseEnd_687192] using wordTrace_append hprefix tailTrace_687192
  have hstable : (prefixWord ++ tailWord_687192).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687192).length < 2 ^ (prefixWord ++ tailWord_687192).sum := by decide
  have hdescent : baseEnd_687192 < baseStart_687192 := by decide
  rcases family_descends (prefixWord ++ tailWord_687192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687274 : List Nat := [3, 1, 5, 1, 1, 2, 2, 3, 3]
def baseStart_687274 : Nat := 118140960795 + 687274 * 2 ^ 59
def prefixEnd_687274 : Nat := 4983230072969 + 3 ^ 40 * 687274 * 2
def baseEnd_687274 : Nat := 156845290372555231561907

theorem tailTrace_687274 : CollatzResearch.WordTrace tailWord_687274 prefixEnd_687274 156845290372555231561907 := by
  unfold tailWord_687274
  simp only [CollatzResearch.WordTrace]
  refine ⟨6266735528032787474861219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16711294741420766599629917 6266735528032787474861219)
  ·
    refine ⟨9400103292049181212291829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6266735528032787474861219 9400103292049181212291829)
    ·
      refine ⟨881259683629610738652359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9400103292049181212291829 881259683629610738652359)
      ·
        refine ⟨1321889525444416107978539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 881259683629610738652359 1321889525444416107978539)
        ·
          refine ⟨1982834288166624161967809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1321889525444416107978539 1982834288166624161967809)
          ·
            refine ⟨1487125716124968121475857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1982834288166624161967809 1487125716124968121475857)
            ·
              refine ⟨1115344287093726091106893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1487125716124968121475857 1115344287093726091106893)
              ·
                refine ⟨418254107660147284165085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1115344287093726091106893 418254107660147284165085)
                ·
                  refine ⟨156845290372555231561907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 418254107660147284165085 156845290372555231561907)
                  ·
                    rfl

theorem cell21_687274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 2, 3, 3].length) (baseStart_687274 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_687274 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_687274 prefixEnd_687274 := by exact prefixLift 687274
  have htrace : WordTrace (prefixWord ++ tailWord_687274) baseStart_687274 baseEnd_687274 := by
    simpa [prefixWord, tailWord_687274, baseEnd_687274] using wordTrace_append hprefix tailTrace_687274
  have hstable : (prefixWord ++ tailWord_687274).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687274).length < 2 ^ (prefixWord ++ tailWord_687274).sum := by decide
  have hdescent : baseEnd_687274 < baseStart_687274 := by decide
  rcases family_descends (prefixWord ++ tailWord_687274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687364 : List Nat := [2, 3, 2, 2, 2, 3, 2, 1, 4]
def baseStart_687364 : Nat := 118140960795 + 687364 * 2 ^ 59
def prefixEnd_687364 : Nat := 4983230072969 + 3 ^ 40 * 687364 * 2
def baseEnd_687364 : Nat := 156865829598735075061723

theorem tailTrace_687364 : CollatzResearch.WordTrace tailWord_687364 prefixEnd_687364 156865829598735075061723 := by
  unfold tailWord_687364
  simp only [CollatzResearch.WordTrace]
  refine ⟨12535112340902547635110573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16713483121203396846814097 12535112340902547635110573)
  ·
    refine ⟨4700667127838455363166465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12535112340902547635110573 4700667127838455363166465)
    ·
      refine ⟨3525500345878841522374849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4700667127838455363166465 3525500345878841522374849)
      ·
        refine ⟨2644125259409131141781137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3525500345878841522374849 2644125259409131141781137)
        ·
          refine ⟨1983093944556848356335853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2644125259409131141781137 1983093944556848356335853)
          ·
            refine ⟨743660229208818133625945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1983093944556848356335853 743660229208818133625945)
            ·
              refine ⟨557745171906613600219459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 743660229208818133625945 557745171906613600219459)
              ·
                refine ⟨836617757859920400329189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 557745171906613600219459 836617757859920400329189)
                ·
                  refine ⟨156865829598735075061723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 836617757859920400329189 156865829598735075061723)
                  ·
                    rfl

theorem cell21_687364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 2, 1, 4].length) (baseStart_687364 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_687364 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_687364 prefixEnd_687364 := by exact prefixLift 687364
  have htrace : WordTrace (prefixWord ++ tailWord_687364) baseStart_687364 baseEnd_687364 := by
    simpa [prefixWord, tailWord_687364, baseEnd_687364] using wordTrace_append hprefix tailTrace_687364
  have hstable : (prefixWord ++ tailWord_687364).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687364).length < 2 ^ (prefixWord ++ tailWord_687364).sum := by decide
  have hdescent : baseEnd_687364 < baseStart_687364 := by decide
  rcases family_descends (prefixWord ++ tailWord_687364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687409 : List Nat := [1, 2, 2, 3, 3, 1, 4, 2, 3]
def baseStart_687409 : Nat := 118140960795 + 687409 * 2 ^ 59
def prefixEnd_687409 : Nat := 4983230072969 + 3 ^ 40 * 687409 * 2
def baseEnd_687409 : Nat := 156876099211824996811631

theorem tailTrace_687409 : CollatzResearch.WordTrace tailWord_687409 prefixEnd_687409 156876099211824996811631 := by
  unfold tailWord_687409
  simp only [CollatzResearch.WordTrace]
  refine ⟨25071865966642067955609281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16714577311094711970406187 25071865966642067955609281)
  ·
    refine ⟨18803899474981550966706961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25071865966642067955609281 18803899474981550966706961)
    ·
      refine ⟨14102924606236163225030221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18803899474981550966706961 14102924606236163225030221)
      ·
        refine ⟨5288596727338561209386333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14102924606236163225030221 5288596727338561209386333)
        ·
          refine ⟨1983223772751960453519875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5288596727338561209386333 1983223772751960453519875)
          ·
            refine ⟨2974835659127940680279813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1983223772751960453519875 2974835659127940680279813)
            ·
              refine ⟨557781686086488877552465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2974835659127940680279813 557781686086488877552465)
              ·
                refine ⟨418336264564866658164349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 557781686086488877552465 418336264564866658164349)
                ·
                  refine ⟨156876099211824996811631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 418336264564866658164349 156876099211824996811631)
                  ·
                    rfl

theorem cell21_687409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 4, 2, 3].length) (baseStart_687409 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_687409 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_687409 prefixEnd_687409 := by exact prefixLift 687409
  have htrace : WordTrace (prefixWord ++ tailWord_687409) baseStart_687409 baseEnd_687409 := by
    simpa [prefixWord, tailWord_687409, baseEnd_687409] using wordTrace_append hprefix tailTrace_687409
  have hstable : (prefixWord ++ tailWord_687409).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687409).length < 2 ^ (prefixWord ++ tailWord_687409).sum := by decide
  have hdescent : baseEnd_687409 < baseStart_687409 := by decide
  rcases family_descends (prefixWord ++ tailWord_687409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687420 : List Nat := [2, 2, 2, 2, 1, 3, 3, 6]
def baseStart_687420 : Nat := 118140960795 + 687420 * 2 ^ 59
def prefixEnd_687420 : Nat := 4983230072969 + 3 ^ 40 * 687420 * 2
def baseEnd_687420 : Nat := 52292869853897140709425

theorem tailTrace_687420 : CollatzResearch.WordTrace tailWord_687420 prefixEnd_687420 52292869853897140709425 := by
  unfold tailWord_687420
  simp only [CollatzResearch.WordTrace]
  refine ⟨12536133584801108417129857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16714844779734811222839809 12536133584801108417129857)
  ·
    refine ⟨9402100188600831312847393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12536133584801108417129857 9402100188600831312847393)
    ·
      refine ⟨7051575141450623484635545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9402100188600831312847393 7051575141450623484635545)
      ·
        refine ⟨5288681356087967613476659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7051575141450623484635545 5288681356087967613476659)
        ·
          refine ⟨7933022034131951420214989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5288681356087967613476659 7933022034131951420214989)
          ·
            refine ⟨2974883262799481782580621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7933022034131951420214989 2974883262799481782580621)
            ·
              refine ⟨1115581223549805668467733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2974883262799481782580621 1115581223549805668467733)
              ·
                refine ⟨52292869853897140709425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1115581223549805668467733 52292869853897140709425)
                ·
                  rfl

theorem cell21_687420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 3, 6].length) (baseStart_687420 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_687420 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_687420 prefixEnd_687420 := by exact prefixLift 687420
  have htrace : WordTrace (prefixWord ++ tailWord_687420) baseStart_687420 baseEnd_687420 := by
    simpa [prefixWord, tailWord_687420, baseEnd_687420] using wordTrace_append hprefix tailTrace_687420
  have hstable : (prefixWord ++ tailWord_687420).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687420).length < 2 ^ (prefixWord ++ tailWord_687420).sum := by decide
  have hdescent : baseEnd_687420 < baseStart_687420 := by decide
  rcases family_descends (prefixWord ++ tailWord_687420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687465 : List Nat := [1, 2, 1, 1, 1, 3, 2, 6, 4]
def baseStart_687465 : Nat := 118140960795 + 687465 * 2 ^ 59
def prefixEnd_687465 : Nat := 4983230072969 + 3 ^ 40 * 687465 * 2
def baseEnd_687465 : Nat := 156888879174781343878183

theorem tailTrace_687465 : CollatzResearch.WordTrace tailWord_687465 prefixEnd_687465 156888879174781343878183 := by
  unfold tailWord_687465
  simp only [CollatzResearch.WordTrace]
  refine ⟨25073908454439189519647849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16715938969626126346431899 25073908454439189519647849)
  ·
    refine ⟨18805431340829392139735887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25073908454439189519647849 18805431340829392139735887)
    ·
      refine ⟨28208147011244088209603831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18805431340829392139735887 28208147011244088209603831)
      ·
        refine ⟨42312220516866132314405747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28208147011244088209603831 42312220516866132314405747)
        ·
          refine ⟨63468330775299198471608621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42312220516866132314405747 63468330775299198471608621)
          ·
            refine ⟨23800624040737199426853233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63468330775299198471608621 23800624040737199426853233)
            ·
              refine ⟨17850468030552899570139925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23800624040737199426853233 17850468030552899570139925)
              ·
                refine ⟨836740688932167167350309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 17850468030552899570139925 836740688932167167350309)
                ·
                  refine ⟨156888879174781343878183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 836740688932167167350309 156888879174781343878183)
                  ·
                    rfl

theorem cell21_687465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 6, 4].length) (baseStart_687465 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_687465 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_687465 prefixEnd_687465 := by exact prefixLift 687465
  have htrace : WordTrace (prefixWord ++ tailWord_687465) baseStart_687465 baseEnd_687465 := by
    simpa [prefixWord, tailWord_687465, baseEnd_687465] using wordTrace_append hprefix tailTrace_687465
  have hstable : (prefixWord ++ tailWord_687465).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687465).length < 2 ^ (prefixWord ++ tailWord_687465).sum := by decide
  have hdescent : baseEnd_687465 < baseStart_687465 := by decide
  rcases family_descends (prefixWord ++ tailWord_687465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687468 : List Nat := [2, 2, 1, 1, 5, 1, 2, 4, 3]
def baseStart_687468 : Nat := 118140960795 + 687468 * 2 ^ 59
def prefixEnd_687468 : Nat := 4983230072969 + 3 ^ 40 * 687468 * 2
def baseEnd_687468 : Nat := 156889563815654005328177

theorem tailTrace_687468 : CollatzResearch.WordTrace tailWord_687468 prefixEnd_687468 156889563815654005328177 := by
  unfold tailWord_687468
  simp only [CollatzResearch.WordTrace]
  refine ⟨12537008936714160516003529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16716011915618880688004705 12537008936714160516003529)
  ·
    refine ⟨9402756702535620387002647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12537008936714160516003529 9402756702535620387002647)
    ·
      refine ⟨14104135053803430580503971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9402756702535620387002647 14104135053803430580503971)
      ·
        refine ⟨21156202580705145870755957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14104135053803430580503971 21156202580705145870755957)
        ·
          refine ⟨1983393991941107425383371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21156202580705145870755957 1983393991941107425383371)
          ·
            refine ⟨2975090987911661138075057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1983393991941107425383371 2975090987911661138075057)
            ·
              refine ⟨2231318240933745853556293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2975090987911661138075057 2231318240933745853556293)
              ·
                refine ⟨418372170175077347541805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2231318240933745853556293 418372170175077347541805)
                ·
                  refine ⟨156889563815654005328177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 418372170175077347541805 156889563815654005328177)
                  ·
                    rfl

theorem cell21_687468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 4, 3].length) (baseStart_687468 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_687468 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_687468 prefixEnd_687468 := by exact prefixLift 687468
  have htrace : WordTrace (prefixWord ++ tailWord_687468) baseStart_687468 baseEnd_687468 := by
    simpa [prefixWord, tailWord_687468, baseEnd_687468] using wordTrace_append hprefix tailTrace_687468
  have hstable : (prefixWord ++ tailWord_687468).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687468).length < 2 ^ (prefixWord ++ tailWord_687468).sum := by decide
  have hdescent : baseEnd_687468 < baseStart_687468 := by decide
  rcases family_descends (prefixWord ++ tailWord_687468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687479 : List Nat := [1, 1, 3, 1, 1, 2, 4, 8]
def baseStart_687479 : Nat := 118140960795 + 687479 * 2 ^ 59
def prefixEnd_687479 : Nat := 4983230072969 + 3 ^ 40 * 687479 * 2
def baseEnd_687479 : Nat := 52297358055173476881607

theorem tailTrace_687479 : CollatzResearch.WordTrace tailWord_687479 prefixEnd_687479 52297358055173476881607 := by
  unfold tailWord_687479
  simp only [CollatzResearch.WordTrace]
  refine ⟨25074419076388469910657491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16716279384258979940438327 25074419076388469910657491)
  ·
    refine ⟨37611628614582704865986237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25074419076388469910657491 37611628614582704865986237)
    ·
      refine ⟨14104360730468514324744839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37611628614582704865986237 14104360730468514324744839)
      ·
        refine ⟨21156541095702771487117259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14104360730468514324744839 21156541095702771487117259)
        ·
          refine ⟨31734811643554157230675889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21156541095702771487117259 31734811643554157230675889)
          ·
            refine ⟨23801108732665617923006917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31734811643554157230675889 23801108732665617923006917)
            ·
              refine ⟨4462707887374803360563797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23801108732665617923006917 4462707887374803360563797)
              ·
                refine ⟨52297358055173476881607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4462707887374803360563797 52297358055173476881607)
                ·
                  rfl

theorem cell21_687479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 8].length) (baseStart_687479 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_687479 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_687479 prefixEnd_687479 := by exact prefixLift 687479
  have htrace : WordTrace (prefixWord ++ tailWord_687479) baseStart_687479 baseEnd_687479 := by
    simpa [prefixWord, tailWord_687479, baseEnd_687479] using wordTrace_append hprefix tailTrace_687479
  have hstable : (prefixWord ++ tailWord_687479).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687479).length < 2 ^ (prefixWord ++ tailWord_687479).sum := by decide
  have hdescent : baseEnd_687479 < baseStart_687479 := by decide
  rcases family_descends (prefixWord ++ tailWord_687479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687496 : List Nat := [2, 1, 3, 3, 1, 3, 1, 7]
def baseStart_687496 : Nat := 118140960795 + 687496 * 2 ^ 59
def prefixEnd_687496 : Nat := 4983230072969 + 3 ^ 40 * 687496 * 2
def baseEnd_687496 : Nat := 52298651265710726287151

theorem tailTrace_687496 : CollatzResearch.WordTrace tailWord_687496 prefixEnd_687496 52298651265710726287151 := by
  unfold tailWord_687496
  simp only [CollatzResearch.WordTrace]
  refine ⟨12537519558663440907013171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16716692744884587876017561 12537519558663440907013171)
  ·
    refine ⟨18806279337995161360519757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12537519558663440907013171 18806279337995161360519757)
    ·
      refine ⟨7052354751748185510194909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18806279337995161360519757 7052354751748185510194909)
      ·
        refine ⟨2644633031905569566323091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7052354751748185510194909 2644633031905569566323091)
        ·
          refine ⟨3966949547858354349484637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2644633031905569566323091 3966949547858354349484637)
          ·
            refine ⟨1487606080446882881056739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3966949547858354349484637 1487606080446882881056739)
            ·
              refine ⟨2231409120670324321585109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1487606080446882881056739 2231409120670324321585109)
              ·
                refine ⟨52298651265710726287151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2231409120670324321585109 52298651265710726287151)
                ·
                  rfl

theorem cell21_687496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 7].length) (baseStart_687496 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_687496 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_687496 prefixEnd_687496 := by exact prefixLift 687496
  have htrace : WordTrace (prefixWord ++ tailWord_687496) baseStart_687496 baseEnd_687496 := by
    simpa [prefixWord, tailWord_687496, baseEnd_687496] using wordTrace_append hprefix tailTrace_687496
  have hstable : (prefixWord ++ tailWord_687496).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687496).length < 2 ^ (prefixWord ++ tailWord_687496).sum := by decide
  have hdescent : baseEnd_687496 < baseStart_687496 := by decide
  rcases family_descends (prefixWord ++ tailWord_687496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687502 : List Nat := [4, 1, 1, 4, 2, 2, 1, 3, 3]
def baseStart_687502 : Nat := 118140960795 + 687502 * 2 ^ 59
def prefixEnd_687502 : Nat := 4983230072969 + 3 ^ 40 * 687502 * 2
def baseEnd_687502 : Nat := 156897323078877501761441

theorem tailTrace_687502 : CollatzResearch.WordTrace tailWord_687502 prefixEnd_687502 156897323078877501761441 := by
  unfold tailWord_687502
  simp only [CollatzResearch.WordTrace]
  refine ⟨3134407244413143104843095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16716838636870096559163173 3134407244413143104843095)
  ·
    refine ⟨4701610866619714657264643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3134407244413143104843095 4701610866619714657264643)
    ·
      refine ⟨7052416299929571985896965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4701610866619714657264643 7052416299929571985896965)
      ·
        refine ⟨1322328056236794747355681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7052416299929571985896965 1322328056236794747355681)
        ·
          refine ⟨991746042177596060516761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1322328056236794747355681 991746042177596060516761)
          ·
            refine ⟨743809531633197045387571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 991746042177596060516761 743809531633197045387571)
            ·
              refine ⟨1115714297449795568081357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 743809531633197045387571 1115714297449795568081357)
              ·
                refine ⟨418392861543673338030509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1115714297449795568081357 418392861543673338030509)
                ·
                  refine ⟨156897323078877501761441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 418392861543673338030509 156897323078877501761441)
                  ·
                    rfl

theorem cell21_687502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 1, 3, 3].length) (baseStart_687502 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_687502 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_687502 prefixEnd_687502 := by exact prefixLift 687502
  have htrace : WordTrace (prefixWord ++ tailWord_687502) baseStart_687502 baseEnd_687502 := by
    simpa [prefixWord, tailWord_687502, baseEnd_687502] using wordTrace_append hprefix tailTrace_687502
  have hstable : (prefixWord ++ tailWord_687502).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687502).length < 2 ^ (prefixWord ++ tailWord_687502).sum := by decide
  have hdescent : baseEnd_687502 < baseStart_687502 := by decide
  rcases family_descends (prefixWord ++ tailWord_687502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687555 : List Nat := [1, 1, 1, 3, 1, 1, 6, 7]
def baseStart_687555 : Nat := 118140960795 + 687555 * 2 ^ 59
def prefixEnd_687555 : Nat := 4983230072969 + 3 ^ 40 * 687555 * 2
def baseEnd_687555 : Nat := 52303139466987062459333

theorem tailTrace_687555 : CollatzResearch.WordTrace tailWord_687555 prefixEnd_687555 52303139466987062459333 := by
  unfold tailWord_687555
  simp only [CollatzResearch.WordTrace]
  refine ⟨25077191024113134890424119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16718127349408756593616079 25077191024113134890424119)
  ·
    refine ⟨37615786536169702335636179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25077191024113134890424119 37615786536169702335636179)
    ·
      refine ⟨56423679804254553503454269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37615786536169702335636179 56423679804254553503454269)
      ·
        refine ⟨21158879926595457563795351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56423679804254553503454269 21158879926595457563795351)
        ·
          refine ⟨31738319889893186345693027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21158879926595457563795351 31738319889893186345693027)
          ·
            refine ⟨47607479834839779518539541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31738319889893186345693027 47607479834839779518539541)
            ·
              refine ⟨2231600617258114664931541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 47607479834839779518539541 2231600617258114664931541)
              ·
                refine ⟨52303139466987062459333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2231600617258114664931541 52303139466987062459333)
                ·
                  rfl

theorem cell21_687555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 7].length) (baseStart_687555 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_687555 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_687555 prefixEnd_687555 := by exact prefixLift 687555
  have htrace : WordTrace (prefixWord ++ tailWord_687555) baseStart_687555 baseEnd_687555 := by
    simpa [prefixWord, tailWord_687555, baseEnd_687555] using wordTrace_append hprefix tailTrace_687555
  have hstable : (prefixWord ++ tailWord_687555).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687555).length < 2 ^ (prefixWord ++ tailWord_687555).sum := by decide
  have hdescent : baseEnd_687555 < baseStart_687555 := by decide
  rcases family_descends (prefixWord ++ tailWord_687555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687572 : List Nat := [2, 4, 1, 2, 3, 9]
def baseStart_687572 : Nat := 118140960795 + 687572 * 2 ^ 59
def prefixEnd_687572 : Nat := 4983230072969 + 3 ^ 40 * 687572 * 2
def baseEnd_687572 : Nat := 5811603630836034651653

theorem tailTrace_687572 : CollatzResearch.WordTrace tailWord_687572 prefixEnd_687572 5811603630836034651653 := by
  unfold tailWord_687572
  simp only [CollatzResearch.WordTrace]
  refine ⟨12538905532525773396896485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16718540710034364529195313 12538905532525773396896485)
  ·
    refine ⟨2351044787348582511918091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12538905532525773396896485 2351044787348582511918091)
    ·
      refine ⟨3526567181022873767877137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2351044787348582511918091 3526567181022873767877137)
      ·
        refine ⟨2644925385767155325907853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3526567181022873767877137 2644925385767155325907853)
        ·
          refine ⟨991847019662683247215445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2644925385767155325907853 991847019662683247215445)
          ·
            refine ⟨5811603630836034651653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 991847019662683247215445 5811603630836034651653)
            ·
              rfl

theorem cell21_687572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 9].length) (baseStart_687572 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_687572 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_687572 prefixEnd_687572 := by exact prefixLift 687572
  have htrace : WordTrace (prefixWord ++ tailWord_687572) baseStart_687572 baseEnd_687572 := by
    simpa [prefixWord, tailWord_687572, baseEnd_687572] using wordTrace_append hprefix tailTrace_687572
  have hstable : (prefixWord ++ tailWord_687572).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687572).length < 2 ^ (prefixWord ++ tailWord_687572).sum := by decide
  have hdescent : baseEnd_687572 < baseStart_687572 := by decide
  rcases family_descends (prefixWord ++ tailWord_687572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687589 : List Nat := [1, 3, 1, 5, 1, 3, 1, 6]
def baseStart_687589 : Nat := 118140960795 + 687589 * 2 ^ 59
def prefixEnd_687589 : Nat := 4983230072969 + 3 ^ 40 * 687589 * 2
def baseEnd_687589 : Nat := 52305725888061561270421

theorem tailTrace_687589 : CollatzResearch.WordTrace tailWord_687589 prefixEnd_687589 52305725888061561270421 := by
  unfold tailWord_687589
  simp only [CollatzResearch.WordTrace]
  refine ⟨25078431105989958697161821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16718954070659972464774547 25078431105989958697161821)
  ·
    refine ⟨9404411664746234511435683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25078431105989958697161821 9404411664746234511435683)
    ·
      refine ⟨14106617497119351767153525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9404411664746234511435683 14106617497119351767153525)
      ·
        refine ⟨1322495390354939228170643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14106617497119351767153525 1322495390354939228170643)
        ·
          refine ⟨1983743085532408842255965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1322495390354939228170643 1983743085532408842255965)
          ·
            refine ⟨743903657074653315845987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1983743085532408842255965 743903657074653315845987)
            ·
              refine ⟨1115855485611979973768981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 743903657074653315845987 1115855485611979973768981)
              ·
                refine ⟨52305725888061561270421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1115855485611979973768981 52305725888061561270421)
                ·
                  rfl

theorem cell21_687589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 1, 6].length) (baseStart_687589 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_687589 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_687589 prefixEnd_687589 := by exact prefixLift 687589
  have htrace : WordTrace (prefixWord ++ tailWord_687589) baseStart_687589 baseEnd_687589 := by
    simpa [prefixWord, tailWord_687589, baseEnd_687589] using wordTrace_append hprefix tailTrace_687589
  have hstable : (prefixWord ++ tailWord_687589).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687589).length < 2 ^ (prefixWord ++ tailWord_687589).sum := by decide
  have hdescent : baseEnd_687589 < baseStart_687589 := by decide
  rcases family_descends (prefixWord ++ tailWord_687589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687651 : List Nat := [1, 1, 1, 4, 5, 1, 3, 1, 4]
def baseStart_687651 : Nat := 118140960795 + 687651 * 2 ^ 59
def prefixEnd_687651 : Nat := 4983230072969 + 3 ^ 40 * 687651 * 2
def baseEnd_687651 : Nat := 156931326908886353777803

theorem tailTrace_687651 : CollatzResearch.WordTrace tailWord_687651 prefixEnd_687651 156931326908886353777803 := by
  unfold tailWord_687651
  simp only [CollatzResearch.WordTrace]
  refine ⟨25080692431765343285918807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16720461621176895523945871 25080692431765343285918807)
  ·
    refine ⟨37621038647648014928878211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25080692431765343285918807 37621038647648014928878211)
    ·
      refine ⟨56431557971472022393317317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37621038647648014928878211 56431557971472022393317317)
      ·
        refine ⟨10580917119651004198746997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56431557971472022393317317 10580917119651004198746997)
        ·
          refine ⟨991960979967281643632531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10580917119651004198746997 991960979967281643632531)
          ·
            refine ⟨1487941469950922465448797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 991960979967281643632531 1487941469950922465448797)
            ·
              refine ⟨557978051231595924543299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1487941469950922465448797 557978051231595924543299)
              ·
                refine ⟨836967076847393886814949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 557978051231595924543299 836967076847393886814949)
                ·
                  refine ⟨156931326908886353777803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 836967076847393886814949 156931326908886353777803)
                  ·
                    rfl

theorem cell21_687651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 3, 1, 4].length) (baseStart_687651 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_687651 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_687651 prefixEnd_687651 := by exact prefixLift 687651
  have htrace : WordTrace (prefixWord ++ tailWord_687651) baseStart_687651 baseEnd_687651 := by
    simpa [prefixWord, tailWord_687651, baseEnd_687651] using wordTrace_append hprefix tailTrace_687651
  have hstable : (prefixWord ++ tailWord_687651).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687651).length < 2 ^ (prefixWord ++ tailWord_687651).sum := by decide
  have hdescent : baseEnd_687651 < baseStart_687651 := by decide
  rcases family_descends (prefixWord ++ tailWord_687651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687696 : List Nat := [2, 1, 1, 1, 1, 3, 7, 2, 3]
def baseStart_687696 : Nat := 118140960795 + 687696 * 2 ^ 59
def prefixEnd_687696 : Nat := 4983230072969 + 3 ^ 40 * 687696 * 2
def baseEnd_687696 : Nat := 156941596521976275527711

theorem tailTrace_687696 : CollatzResearch.WordTrace tailWord_687696 prefixEnd_687696 156941596521976275527711 := by
  unfold tailWord_687696
  simp only [CollatzResearch.WordTrace]
  refine ⟨12541166858301157985653471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16721555811068210647537961 12541166858301157985653471)
  ·
    refine ⟨18811750287451736978480207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12541166858301157985653471 18811750287451736978480207)
    ·
      refine ⟨28217625431177605467720311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18811750287451736978480207 28217625431177605467720311)
      ·
        refine ⟨42326438146766408201580467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28217625431177605467720311 42326438146766408201580467)
        ·
          refine ⟨63489657220149612302370701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42326438146766408201580467 63489657220149612302370701)
          ·
            refine ⟨23808621457556104613389013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63489657220149612302370701 23808621457556104613389013)
            ·
              refine ⟨558014565411471201876305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 23808621457556104613389013 558014565411471201876305)
              ·
                refine ⟨418510924058603401407229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 558014565411471201876305 418510924058603401407229)
                ·
                  refine ⟨156941596521976275527711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 418510924058603401407229 156941596521976275527711)
                  ·
                    rfl

theorem cell21_687696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 7, 2, 3].length) (baseStart_687696 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_687696 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_687696 prefixEnd_687696 := by exact prefixLift 687696
  have htrace : WordTrace (prefixWord ++ tailWord_687696) baseStart_687696 baseEnd_687696 := by
    simpa [prefixWord, tailWord_687696, baseEnd_687696] using wordTrace_append hprefix tailTrace_687696
  have hstable : (prefixWord ++ tailWord_687696).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687696).length < 2 ^ (prefixWord ++ tailWord_687696).sum := by decide
  have hdescent : baseEnd_687696 < baseStart_687696 := by decide
  rcases family_descends (prefixWord ++ tailWord_687696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687702 : List Nat := [5, 2, 2, 2, 1, 2, 2, 1, 4]
def baseStart_687702 : Nat := 118140960795 + 687702 * 2 ^ 59
def prefixEnd_687702 : Nat := 4983230072969 + 3 ^ 40 * 687702 * 2
def baseEnd_687702 : Nat := 156942965803721598427699

theorem tailTrace_687702 : CollatzResearch.WordTrace tailWord_687702 prefixEnd_687702 156942965803721598427699 := by
  unfold tailWord_687702
  simp only [CollatzResearch.WordTrace]
  refine ⟨1567659534661286187251585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16721701703053719330683573 1567659534661286187251585)
  ·
    refine ⟨1175744650995964640438689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1567659534661286187251585 1175744650995964640438689)
    ·
      refine ⟨881808488246973480329017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1175744650995964640438689 881808488246973480329017)
      ·
        refine ⟨661356366185230110246763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 881808488246973480329017 661356366185230110246763)
        ·
          refine ⟨992034549277845165370145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 661356366185230110246763 992034549277845165370145)
          ·
            refine ⟨744025911958383874027609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 992034549277845165370145 744025911958383874027609)
            ·
              refine ⟨558019433968787905520707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 744025911958383874027609 558019433968787905520707)
              ·
                refine ⟨837029150953181858281061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 558019433968787905520707 837029150953181858281061)
                ·
                  refine ⟨156942965803721598427699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 837029150953181858281061 156942965803721598427699)
                  ·
                    rfl

theorem cell21_687702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_687702 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_687702 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_687702 prefixEnd_687702 := by exact prefixLift 687702
  have htrace : WordTrace (prefixWord ++ tailWord_687702) baseStart_687702 baseEnd_687702 := by
    simpa [prefixWord, tailWord_687702, baseEnd_687702] using wordTrace_append hprefix tailTrace_687702
  have hstable : (prefixWord ++ tailWord_687702).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687702).length < 2 ^ (prefixWord ++ tailWord_687702).sum := by decide
  have hdescent : baseEnd_687702 < baseStart_687702 := by decide
  rcases family_descends (prefixWord ++ tailWord_687702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687755 : List Nat := [1, 1, 1, 1, 4, 1, 5, 4, 3]
def baseStart_687755 : Nat := 118140960795 + 687755 * 2 ^ 59
def prefixEnd_687755 : Nat := 4983230072969 + 3 ^ 40 * 687755 * 2
def baseEnd_687755 : Nat := 156955061125805284044257

theorem tailTrace_687755 : CollatzResearch.WordTrace tailWord_687755 prefixEnd_687755 156955061125805284044257 := by
  unfold tailWord_687755
  simp only [CollatzResearch.WordTrace]
  refine ⟨25084485623388569047704719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16722990415592379365136479 25084485623388569047704719)
  ·
    refine ⟨37626728435082853571557079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25084485623388569047704719 37626728435082853571557079)
    ·
      refine ⟨56440092652624280357335619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37626728435082853571557079 56440092652624280357335619)
      ·
        refine ⟨84660138978936420536003429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56440092652624280357335619 84660138978936420536003429)
        ·
          refine ⟨15873776058550578850500643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 84660138978936420536003429 15873776058550578850500643)
          ·
            refine ⟨23810664087825868275750965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15873776058550578850500643 23810664087825868275750965)
            ·
              refine ⟨2232249758233675150851653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23810664087825868275750965 2232249758233675150851653)
              ·
                refine ⟨418546829668814090784685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2232249758233675150851653 418546829668814090784685)
                ·
                  refine ⟨156955061125805284044257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 418546829668814090784685 156955061125805284044257)
                  ·
                    rfl

theorem cell21_687755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 4, 3].length) (baseStart_687755 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_687755 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_687755 prefixEnd_687755 := by exact prefixLift 687755
  have htrace : WordTrace (prefixWord ++ tailWord_687755) baseStart_687755 baseEnd_687755 := by
    simpa [prefixWord, tailWord_687755, baseEnd_687755] using wordTrace_append hprefix tailTrace_687755
  have hstable : (prefixWord ++ tailWord_687755).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687755).length < 2 ^ (prefixWord ++ tailWord_687755).sum := by decide
  have hdescent : baseEnd_687755 < baseStart_687755 := by decide
  rcases family_descends (prefixWord ++ tailWord_687755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687848 : List Nat := [2, 1, 4, 1, 3, 1, 3, 3, 3]
def baseStart_687848 : Nat := 118140960795 + 687848 * 2 ^ 59
def prefixEnd_687848 : Nat := 4983230072969 + 3 ^ 40 * 687848 * 2
def baseEnd_687848 : Nat := 156976284992857788994067

theorem tailTrace_687848 : CollatzResearch.WordTrace tailWord_687848 prefixEnd_687848 156976284992857788994067 := by
  unfold tailWord_687848
  simp only [CollatzResearch.WordTrace]
  refine ⟨12543938806025822965420099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16725251741367763953893465 12543938806025822965420099)
  ·
    refine ⟨18815908209038734448130149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12543938806025822965420099 18815908209038734448130149)
    ·
      refine ⟨3527982789194762709024403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18815908209038734448130149 3527982789194762709024403)
      ·
        refine ⟨5291974183792144063536605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3527982789194762709024403 5291974183792144063536605)
        ·
          refine ⟨1984490318922054023826227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5291974183792144063536605 1984490318922054023826227)
          ·
            refine ⟨2976735478383081035739341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1984490318922054023826227 2976735478383081035739341)
            ·
              refine ⟨1116275804393655388402253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2976735478383081035739341 1116275804393655388402253)
              ·
                refine ⟨418603426647620770650845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1116275804393655388402253 418603426647620770650845)
                ·
                  refine ⟨156976284992857788994067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 418603426647620770650845 156976284992857788994067)
                  ·
                    rfl

theorem cell21_687848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 3, 3, 3].length) (baseStart_687848 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_687848 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_687848 prefixEnd_687848 := by exact prefixLift 687848
  have htrace : WordTrace (prefixWord ++ tailWord_687848) baseStart_687848 baseEnd_687848 := by
    simpa [prefixWord, tailWord_687848, baseEnd_687848] using wordTrace_append hprefix tailTrace_687848
  have hstable : (prefixWord ++ tailWord_687848).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687848).length < 2 ^ (prefixWord ++ tailWord_687848).sum := by decide
  have hdescent : baseEnd_687848 < baseStart_687848 := by decide
  rcases family_descends (prefixWord ++ tailWord_687848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687876 : List Nat := [2, 3, 2, 2, 1, 3, 2, 6]
def baseStart_687876 : Nat := 118140960795 + 687876 * 2 ^ 59
def prefixEnd_687876 : Nat := 4983230072969 + 3 ^ 40 * 687876 * 2
def baseEnd_687876 : Nat := 52327558324778654175781

theorem tailTrace_687876 : CollatzResearch.WordTrace tailWord_687876 prefixEnd_687876 52327558324778654175781 := by
  unfold tailWord_687876
  simp only [CollatzResearch.WordTrace]
  refine ⟨12544449427975103356429741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16725932570633471141906321 12544449427975103356429741)
  ·
    refine ⟨4704168535490663758661153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12544449427975103356429741 4704168535490663758661153)
    ·
      refine ⟨3528126401617997818995865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4704168535490663758661153 3528126401617997818995865)
      ·
        refine ⟨2646094801213498364246899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3528126401617997818995865 2646094801213498364246899)
        ·
          refine ⟨3969142201820247546370349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2646094801213498364246899 3969142201820247546370349)
          ·
            refine ⟨1488428325682592829888881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3969142201820247546370349 1488428325682592829888881)
            ·
              refine ⟨1116321244261944622416661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1488428325682592829888881 1116321244261944622416661)
              ·
                refine ⟨52327558324778654175781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1116321244261944622416661 52327558324778654175781)
                ·
                  rfl

theorem cell21_687876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 2, 6].length) (baseStart_687876 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_687876 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_687876 prefixEnd_687876 := by exact prefixLift 687876
  have htrace : WordTrace (prefixWord ++ tailWord_687876) baseStart_687876 baseEnd_687876 := by
    simpa [prefixWord, tailWord_687876, baseEnd_687876] using wordTrace_append hprefix tailTrace_687876
  have hstable : (prefixWord ++ tailWord_687876).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687876).length < 2 ^ (prefixWord ++ tailWord_687876).sum := by decide
  have hdescent : baseEnd_687876 < baseStart_687876 := by decide
  rcases family_descends (prefixWord ++ tailWord_687876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687921 : List Nat := [1, 2, 2, 3, 2, 2, 1, 4, 4]
def baseStart_687921 : Nat := 118140960795 + 687921 * 2 ^ 59
def prefixEnd_687921 : Nat := 4983230072969 + 3 ^ 40 * 687921 * 2
def baseEnd_687921 : Nat := 156992944587425884277251

theorem tailTrace_687921 : CollatzResearch.WordTrace tailWord_687921 prefixEnd_687921 156992944587425884277251 := by
  unfold tailWord_687921
  simp only [CollatzResearch.WordTrace]
  refine ⟨25090540140787179398247617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16727026760524786265498411 25090540140787179398247617)
  ·
    refine ⟨18817905105590384548685713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25090540140787179398247617 18817905105590384548685713)
    ·
      refine ⟨14113428829192788411514285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18817905105590384548685713 14113428829192788411514285)
      ·
        refine ⟨5292535810947295654317857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14113428829192788411514285 5292535810947295654317857)
        ·
          refine ⟨3969401858210471740738393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5292535810947295654317857 3969401858210471740738393)
          ·
            refine ⟨2977051393657853805553795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3969401858210471740738393 2977051393657853805553795)
            ·
              refine ⟨4465577090486780708330693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2977051393657853805553795 4465577090486780708330693)
              ·
                refine ⟨837295704466271382812005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4465577090486780708330693 837295704466271382812005)
                ·
                  refine ⟨156992944587425884277251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 837295704466271382812005 156992944587425884277251)
                  ·
                    rfl

theorem cell21_687921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 4, 4].length) (baseStart_687921 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_687921 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_687921 prefixEnd_687921 := by exact prefixLift 687921
  have htrace : WordTrace (prefixWord ++ tailWord_687921) baseStart_687921 baseEnd_687921 := by
    simpa [prefixWord, tailWord_687921, baseEnd_687921] using wordTrace_append hprefix tailTrace_687921
  have hstable : (prefixWord ++ tailWord_687921).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687921).length < 2 ^ (prefixWord ++ tailWord_687921).sum := by decide
  have hdescent : baseEnd_687921 < baseStart_687921 := by decide
  rcases family_descends (prefixWord ++ tailWord_687921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688025 : List Nat := [1, 2, 1, 2, 1, 3, 2, 2, 7]
def baseStart_688025 : Nat := 118140960795 + 688025 * 2 ^ 59
def prefixEnd_688025 : Nat := 4983230072969 + 3 ^ 40 * 688025 * 2
def baseEnd_688025 : Nat := 157016678804344814543705

theorem tailTrace_688025 : CollatzResearch.WordTrace tailWord_688025 prefixEnd_688025 157016678804344814543705 := by
  unfold tailWord_688025
  simp only [CollatzResearch.WordTrace]
  refine ⟨25094333332410405160033529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16729555554940270106689019 25094333332410405160033529)
  ·
    refine ⟨18820749999307803870025147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25094333332410405160033529 18820749999307803870025147)
    ·
      refine ⟨28231124998961705805037721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18820749999307803870025147 28231124998961705805037721)
      ·
        refine ⟨21173343749221279353778291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28231124998961705805037721 21173343749221279353778291)
        ·
          refine ⟨31760015623831919030667437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21173343749221279353778291 31760015623831919030667437)
          ·
            refine ⟨11910005858936969636500289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31760015623831919030667437 11910005858936969636500289)
            ·
              refine ⟨8932504394202727227375217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11910005858936969636500289 8932504394202727227375217)
              ·
                refine ⟨6699378295652045420531413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8932504394202727227375217 6699378295652045420531413)
                ·
                  refine ⟨157016678804344814543705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6699378295652045420531413 157016678804344814543705)
                  ·
                    rfl

theorem cell21_688025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 2, 7].length) (baseStart_688025 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_688025 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_688025 prefixEnd_688025 := by exact prefixLift 688025
  have htrace : WordTrace (prefixWord ++ tailWord_688025) baseStart_688025 baseEnd_688025 := by
    simpa [prefixWord, tailWord_688025, baseEnd_688025] using wordTrace_append hprefix tailTrace_688025
  have hstable : (prefixWord ++ tailWord_688025).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688025).length < 2 ^ (prefixWord ++ tailWord_688025).sum := by decide
  have hdescent : baseEnd_688025 < baseStart_688025 := by decide
  rcases family_descends (prefixWord ++ tailWord_688025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688028 : List Nat := [2, 2, 3, 3, 1, 3, 7]
def baseStart_688028 : Nat := 118140960795 + 688028 * 2 ^ 59
def prefixEnd_688028 : Nat := 4983230072969 + 3 ^ 40 * 688028 * 2
def baseEnd_688028 : Nat := 17446373716135275110411

theorem tailTrace_688028 : CollatzResearch.WordTrace tailWord_688028 prefixEnd_688028 17446373716135275110411 := by
  unfold tailWord_688028
  simp only [CollatzResearch.WordTrace]
  refine ⟨12547221375699768336196369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16729628500933024448261825 12547221375699768336196369)
  ·
    refine ⟨9410416031774826252147277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12547221375699768336196369 9410416031774826252147277)
    ·
      refine ⟨3528906011915559844555229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9410416031774826252147277 3528906011915559844555229)
      ·
        refine ⟨1323339754468334941708211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3528906011915559844555229 1323339754468334941708211)
        ·
          refine ⟨1985009631702502412562317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1323339754468334941708211 1985009631702502412562317)
          ·
            refine ⟨744378611888438404710869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1985009631702502412562317 744378611888438404710869)
            ·
              refine ⟨17446373716135275110411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 744378611888438404710869 17446373716135275110411)
              ·
                rfl

theorem cell21_688028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 7].length) (baseStart_688028 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_688028 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_688028 prefixEnd_688028 := by exact prefixLift 688028
  have htrace : WordTrace (prefixWord ++ tailWord_688028) baseStart_688028 baseEnd_688028 := by
    simpa [prefixWord, tailWord_688028, baseEnd_688028] using wordTrace_append hprefix tailTrace_688028
  have hstable : (prefixWord ++ tailWord_688028).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688028).length < 2 ^ (prefixWord ++ tailWord_688028).sum := by decide
  have hdescent : baseEnd_688028 < baseStart_688028 := by decide
  rcases family_descends (prefixWord ++ tailWord_688028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688090 : List Nat := [3, 1, 1, 2, 5, 1, 2, 2, 4]
def baseStart_688090 : Nat := 118140960795 + 688090 * 2 ^ 59
def prefixEnd_688090 : Nat := 4983230072969 + 3 ^ 40 * 688090 * 2
def baseEnd_688090 : Nat := 157031512689919145960239

theorem tailTrace_688090 : CollatzResearch.WordTrace tailWord_688090 prefixEnd_688090 157031512689919145960239 := by
  unfold tailWord_688090
  simp only [CollatzResearch.WordTrace]
  refine ⟨6274176019293730315287431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16731136051449947507433149 6274176019293730315287431)
  ·
    refine ⟨9411264028940595472931147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6274176019293730315287431 9411264028940595472931147)
    ·
      refine ⟨14116896043410893209396721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9411264028940595472931147 14116896043410893209396721)
      ·
        refine ⟨10587672032558169907047541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14116896043410893209396721 10587672032558169907047541)
        ·
          refine ⟨992594253052328428785707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10587672032558169907047541 992594253052328428785707)
          ·
            refine ⟨1488891379578492643178561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 992594253052328428785707 1488891379578492643178561)
            ·
              refine ⟨1116668534683869482383921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1488891379578492643178561 1116668534683869482383921)
              ·
                refine ⟨837501401012902111787941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1116668534683869482383921 837501401012902111787941)
                ·
                  refine ⟨157031512689919145960239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 837501401012902111787941 157031512689919145960239)
                  ·
                    rfl

theorem cell21_688090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 2, 2, 4].length) (baseStart_688090 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_688090 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_688090 prefixEnd_688090 := by exact prefixLift 688090
  have htrace : WordTrace (prefixWord ++ tailWord_688090) baseStart_688090 baseEnd_688090 := by
    simpa [prefixWord, tailWord_688090, baseEnd_688090] using wordTrace_append hprefix tailTrace_688090
  have hstable : (prefixWord ++ tailWord_688090).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688090).length < 2 ^ (prefixWord ++ tailWord_688090).sum := by decide
  have hdescent : baseEnd_688090 < baseStart_688090 := by decide
  rcases family_descends (prefixWord ++ tailWord_688090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688135 : List Nat := [1, 1, 4, 3, 1, 2, 1, 5, 3]
def baseStart_688135 : Nat := 118140960795 + 688135 * 2 ^ 59
def prefixEnd_688135 : Nat := 4983230072969 + 3 ^ 40 * 688135 * 2
def baseEnd_688135 : Nat := 157041782303009067710147

theorem tailTrace_688135 : CollatzResearch.WordTrace tailWord_688135 prefixEnd_688135 157041782303009067710147 := by
  unfold tailWord_688135
  simp only [CollatzResearch.WordTrace]
  refine ⟨25098345362011893946537859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16732230241341262631025239 25098345362011893946537859)
  ·
    refine ⟨37647518043017840919806789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25098345362011893946537859 37647518043017840919806789)
    ·
      refine ⟨7058909633065845172463773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37647518043017840919806789 7058909633065845172463773)
      ·
        refine ⟨2647091112399691939673915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7058909633065845172463773 2647091112399691939673915)
        ·
          refine ⟨3970636668599537909510873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2647091112399691939673915 3970636668599537909510873)
          ·
            refine ⟨2977977501449653432133155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3970636668599537909510873 2977977501449653432133155)
            ·
              refine ⟨4466966252174480148199733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2977977501449653432133155 4466966252174480148199733)
              ·
                refine ⟨418778086141357513893725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4466966252174480148199733 418778086141357513893725)
                ·
                  refine ⟨157041782303009067710147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 418778086141357513893725 157041782303009067710147)
                  ·
                    rfl

theorem cell21_688135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 5, 3].length) (baseStart_688135 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_688135 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_688135 prefixEnd_688135 := by exact prefixLift 688135
  have htrace : WordTrace (prefixWord ++ tailWord_688135) baseStart_688135 baseEnd_688135 := by
    simpa [prefixWord, tailWord_688135, baseEnd_688135] using wordTrace_append hprefix tailTrace_688135
  have hstable : (prefixWord ++ tailWord_688135).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688135).length < 2 ^ (prefixWord ++ tailWord_688135).sum := by decide
  have hdescent : baseEnd_688135 < baseStart_688135 := by decide
  rcases family_descends (prefixWord ++ tailWord_688135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688141 : List Nat := [1, 7, 1, 2, 1, 2, 1, 2, 4]
def baseStart_688141 : Nat := 118140960795 + 688141 * 2 ^ 59
def prefixEnd_688141 : Nat := 4983230072969 + 3 ^ 40 * 688141 * 2
def baseEnd_688141 : Nat := 157043151584754390610135

theorem tailTrace_688141 : CollatzResearch.WordTrace tailWord_688141 prefixEnd_688141 157043151584754390610135 := by
  unfold tailWord_688141
  simp only [CollatzResearch.WordTrace]
  refine ⟨25098564199990156971256277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16732376133326771314170851 25098564199990156971256277)
  ·
    refine ⟨588247598437269304013819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 25098564199990156971256277 588247598437269304013819)
    ·
      refine ⟨882371397655903956020729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 588247598437269304013819 882371397655903956020729)
      ·
        refine ⟨661778548241927967015547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 882371397655903956020729 661778548241927967015547)
        ·
          refine ⟨992667822362891950523321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 661778548241927967015547 992667822362891950523321)
          ·
            refine ⟨744500866772168962892491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 992667822362891950523321 744500866772168962892491)
            ·
              refine ⟨1116751300158253444338737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 744500866772168962892491 1116751300158253444338737)
              ·
                refine ⟨837563475118690083254053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1116751300158253444338737 837563475118690083254053)
                ·
                  refine ⟨157043151584754390610135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 837563475118690083254053 157043151584754390610135)
                  ·
                    rfl

theorem cell21_688141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_688141 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_688141 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_688141 prefixEnd_688141 := by exact prefixLift 688141
  have htrace : WordTrace (prefixWord ++ tailWord_688141) baseStart_688141 baseEnd_688141 := by
    simpa [prefixWord, tailWord_688141, baseEnd_688141] using wordTrace_append hprefix tailTrace_688141
  have hstable : (prefixWord ++ tailWord_688141).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688141).length < 2 ^ (prefixWord ++ tailWord_688141).sum := by decide
  have hdescent : baseEnd_688141 < baseStart_688141 := by decide
  rcases family_descends (prefixWord ++ tailWord_688141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688149 : List Nat := [1, 3, 2, 1, 5, 1, 1, 1, 6]
def baseStart_688149 : Nat := 118140960795 + 688149 * 2 ^ 59
def prefixEnd_688149 : Nat := 4983230072969 + 3 ^ 40 * 688149 * 2
def baseEnd_688149 : Nat := 157044977293748154476785

theorem tailTrace_688149 : CollatzResearch.WordTrace tailWord_688149 prefixEnd_688149 157044977293748154476785 := by
  unfold tailWord_688149
  simp only [CollatzResearch.WordTrace]
  refine ⟨25098855983961174337547501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16732570655974116225031667 25098855983961174337547501)
  ·
    refine ⟨9412070993985440376580313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25098855983961174337547501 9412070993985440376580313)
    ·
      refine ⟨7059053245489080282435235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9412070993985440376580313 7059053245489080282435235)
      ·
        refine ⟨10588579868233620423652853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7059053245489080282435235 10588579868233620423652853)
        ·
          refine ⟨992679362646901914717455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10588579868233620423652853 992679362646901914717455)
          ·
            refine ⟨1489019043970352872076183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 992679362646901914717455 1489019043970352872076183)
            ·
              refine ⟨2233528565955529308114275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1489019043970352872076183 2233528565955529308114275)
              ·
                refine ⟨3350292848933293962171413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2233528565955529308114275 3350292848933293962171413)
                ·
                  refine ⟨157044977293748154476785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3350292848933293962171413 157044977293748154476785)
                  ·
                    rfl

theorem cell21_688149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 1, 6].length) (baseStart_688149 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_688149 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_688149 prefixEnd_688149 := by exact prefixLift 688149
  have htrace : WordTrace (prefixWord ++ tailWord_688149) baseStart_688149 baseEnd_688149 := by
    simpa [prefixWord, tailWord_688149, baseEnd_688149] using wordTrace_append hprefix tailTrace_688149
  have hstable : (prefixWord ++ tailWord_688149).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688149).length < 2 ^ (prefixWord ++ tailWord_688149).sum := by decide
  have hdescent : baseEnd_688149 < baseStart_688149 := by decide
  rcases family_descends (prefixWord ++ tailWord_688149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688349 : List Nat := [1, 4, 3, 2, 1, 3, 2, 5]
def baseStart_688349 : Nat := 118140960795 + 688349 * 2 ^ 59
def prefixEnd_688349 : Nat := 4983230072969 + 3 ^ 40 * 688349 * 2
def baseEnd_688349 : Nat := 52363540006197417047681

theorem tailTrace_688349 : CollatzResearch.WordTrace tailWord_688349 prefixEnd_688349 52363540006197417047681 := by
  unfold tailWord_688349
  simp only [CollatzResearch.WordTrace]
  refine ⟨25106150583236608494828101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16737433722157738996552067 25106150583236608494828101)
  ·
    refine ⟨4707403234356864092780269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25106150583236608494828101 4707403234356864092780269)
    ·
      refine ⟨1765276212883824034792601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4707403234356864092780269 1765276212883824034792601)
      ·
        refine ⟨1323957159662868026094451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1765276212883824034792601 1323957159662868026094451)
        ·
          refine ⟨1985935739494302039141677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1323957159662868026094451 1985935739494302039141677)
          ·
            refine ⟨744725902310363264678129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1985935739494302039141677 744725902310363264678129)
            ·
              refine ⟨558544426732772448508597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 744725902310363264678129 558544426732772448508597)
              ·
                refine ⟨52363540006197417047681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 558544426732772448508597 52363540006197417047681)
                ·
                  rfl

theorem cell21_688349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 2, 5].length) (baseStart_688349 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_688349 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_688349 prefixEnd_688349 := by exact prefixLift 688349
  have htrace : WordTrace (prefixWord ++ tailWord_688349) baseStart_688349 baseEnd_688349 := by
    simpa [prefixWord, tailWord_688349, baseEnd_688349] using wordTrace_append hprefix tailTrace_688349
  have hstable : (prefixWord ++ tailWord_688349).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688349).length < 2 ^ (prefixWord ++ tailWord_688349).sum := by decide
  have hdescent : baseEnd_688349 < baseStart_688349 := by decide
  rcases family_descends (prefixWord ++ tailWord_688349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688360 : List Nat := [2, 1, 4, 1, 2, 2, 1, 2, 6]
def baseStart_688360 : Nat := 118140960795 + 688360 * 2 ^ 59
def prefixEnd_688360 : Nat := 4983230072969 + 3 ^ 40 * 688360 * 2
def baseEnd_688360 : Nat := 157093130368458676459687

theorem tailTrace_688360 : CollatzResearch.WordTrace tailWord_688360 prefixEnd_688360 157093130368458676459687 := by
  unfold tailWord_688360
  simp only [CollatzResearch.WordTrace]
  refine ⟨12553275893098378686739267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16737701190797838248985689 12553275893098378686739267)
  ·
    refine ⟨18829913839647568030108901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12553275893098378686739267 18829913839647568030108901)
    ·
      refine ⟨3530608844933919005645419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18829913839647568030108901 3530608844933919005645419)
      ·
        refine ⟨5295913267400878508468129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3530608844933919005645419 5295913267400878508468129)
        ·
          refine ⟨3971934950550658881351097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5295913267400878508468129 3971934950550658881351097)
          ·
            refine ⟨2978951212912994161013323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3971934950550658881351097 2978951212912994161013323)
            ·
              refine ⟨4468426819369491241519985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2978951212912994161013323 4468426819369491241519985)
              ·
                refine ⟨3351320114527118431139989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4468426819369491241519985 3351320114527118431139989)
                ·
                  refine ⟨157093130368458676459687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3351320114527118431139989 157093130368458676459687)
                  ·
                    rfl

theorem cell21_688360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 2, 6].length) (baseStart_688360 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_688360 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_688360 prefixEnd_688360 := by exact prefixLift 688360
  have htrace : WordTrace (prefixWord ++ tailWord_688360) baseStart_688360 baseEnd_688360 := by
    simpa [prefixWord, tailWord_688360, baseEnd_688360] using wordTrace_append hprefix tailTrace_688360
  have hstable : (prefixWord ++ tailWord_688360).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688360).length < 2 ^ (prefixWord ++ tailWord_688360).sum := by decide
  have hdescent : baseEnd_688360 < baseStart_688360 := by decide
  rcases family_descends (prefixWord ++ tailWord_688360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688380 : List Nat := [2, 2, 2, 1, 4, 2, 3, 2, 3]
def baseStart_688380 : Nat := 118140960795 + 688380 * 2 ^ 59
def prefixEnd_688380 : Nat := 4983230072969 + 3 ^ 40 * 688380 * 2
def baseEnd_688380 : Nat := 157097694640943086126313

theorem tailTrace_688380 : CollatzResearch.WordTrace tailWord_688380 prefixEnd_688380 157097694640943086126313 := by
  unfold tailWord_688380
  simp only [CollatzResearch.WordTrace]
  refine ⟨12553640623062150394603297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16738187497416200526137729 12553640623062150394603297)
  ·
    refine ⟨9415230467296612795952473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12553640623062150394603297 9415230467296612795952473)
    ·
      refine ⟨7061422850472459596964355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9415230467296612795952473 7061422850472459596964355)
      ·
        refine ⟨10592134275708689395446533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7061422850472459596964355 10592134275708689395446533)
        ·
          refine ⟨1986025176695379261646225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10592134275708689395446533 1986025176695379261646225)
          ·
            refine ⟨1489518882521534446234669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1986025176695379261646225 1489518882521534446234669)
            ·
              refine ⟨558569580945575417338001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1489518882521534446234669 558569580945575417338001)
              ·
                refine ⟨418927185709181563003501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 558569580945575417338001 418927185709181563003501)
                ·
                  refine ⟨157097694640943086126313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 418927185709181563003501 157097694640943086126313)
                  ·
                    rfl

theorem cell21_688380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 3, 2, 3].length) (baseStart_688380 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_688380 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_688380 prefixEnd_688380 := by exact prefixLift 688380
  have htrace : WordTrace (prefixWord ++ tailWord_688380) baseStart_688380 baseEnd_688380 := by
    simpa [prefixWord, tailWord_688380, baseEnd_688380] using wordTrace_append hprefix tailTrace_688380
  have hstable : (prefixWord ++ tailWord_688380).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688380).length < 2 ^ (prefixWord ++ tailWord_688380).sum := by decide
  have hdescent : baseEnd_688380 < baseStart_688380 := by decide
  rcases family_descends (prefixWord ++ tailWord_688380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688405 : List Nat := [1, 3, 2, 1, 2, 1, 2, 4, 5]
def baseStart_688405 : Nat := 118140960795 + 688405 * 2 ^ 59
def prefixEnd_688405 : Nat := 4983230072969 + 3 ^ 40 * 688405 * 2
def baseEnd_688405 : Nat := 157103399981548598209595

theorem tailTrace_688405 : CollatzResearch.WordTrace tailWord_688405 prefixEnd_688405 157103399981548598209595 := by
  unfold tailWord_688405
  simp only [CollatzResearch.WordTrace]
  refine ⟨25108193071033730058866669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16738795380689153372577779 25108193071033730058866669)
  ·
    refine ⟨9415572401637648772075001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25108193071033730058866669 9415572401637648772075001)
    ·
      refine ⟨7061679301228236579056251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9415572401637648772075001 7061679301228236579056251)
      ·
        refine ⟨10592518951842354868584377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7061679301228236579056251 10592518951842354868584377)
        ·
          refine ⟨7944389213881766151438283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10592518951842354868584377 7944389213881766151438283)
          ·
            refine ⟨11916583820822649227157425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7944389213881766151438283 11916583820822649227157425)
            ·
              refine ⟨8937437865616986920368069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11916583820822649227157425 8937437865616986920368069)
              ·
                refine ⟨1675769599803185047569013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8937437865616986920368069 1675769599803185047569013)
                ·
                  refine ⟨157103399981548598209595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1675769599803185047569013 157103399981548598209595)
                  ·
                    rfl

theorem cell21_688405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 4, 5].length) (baseStart_688405 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_688405 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_688405 prefixEnd_688405 := by exact prefixLift 688405
  have htrace : WordTrace (prefixWord ++ tailWord_688405) baseStart_688405 baseEnd_688405 := by
    simpa [prefixWord, tailWord_688405, baseEnd_688405] using wordTrace_append hprefix tailTrace_688405
  have hstable : (prefixWord ++ tailWord_688405).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688405).length < 2 ^ (prefixWord ++ tailWord_688405).sum := by decide
  have hdescent : baseEnd_688405 < baseStart_688405 := by decide
  rcases family_descends (prefixWord ++ tailWord_688405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688498 : List Nat := [3, 2, 1, 2, 1, 4, 2, 1, 5]
def baseStart_688498 : Nat := 118140960795 + 688498 * 2 ^ 59
def prefixEnd_688498 : Nat := 4983230072969 + 3 ^ 40 * 688498 * 2
def baseEnd_688498 : Nat := 157124623848601103159405

theorem tailTrace_688498 : CollatzResearch.WordTrace tailWord_688498 prefixEnd_688498 157124623848601103159405 := by
  unfold tailWord_688498
  simp only [CollatzResearch.WordTrace]
  refine ⟨6277896264924201735500537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16741056706464537961334765 6277896264924201735500537)
  ·
    refine ⟨4708422198693151301625403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6277896264924201735500537 4708422198693151301625403)
    ·
      refine ⟨7062633298039726952438105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4708422198693151301625403 7062633298039726952438105)
      ·
        refine ⟨5296974973529795214328579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7062633298039726952438105 5296974973529795214328579)
        ·
          refine ⟨7945462460294692821492869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5296974973529795214328579 7945462460294692821492869)
          ·
            refine ⟨1489774211305254904029913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7945462460294692821492869 1489774211305254904029913)
            ·
              refine ⟨1117330658478941178022435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1489774211305254904029913 1117330658478941178022435)
              ·
                refine ⟨1675995987718411767033653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1117330658478941178022435 1675995987718411767033653)
                ·
                  refine ⟨157124623848601103159405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1675995987718411767033653 157124623848601103159405)
                  ·
                    rfl

theorem cell21_688498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 2, 1, 5].length) (baseStart_688498 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_688498 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_688498 prefixEnd_688498 := by exact prefixLift 688498
  have htrace : WordTrace (prefixWord ++ tailWord_688498) baseStart_688498 baseEnd_688498 := by
    simpa [prefixWord, tailWord_688498, baseEnd_688498] using wordTrace_append hprefix tailTrace_688498
  have hstable : (prefixWord ++ tailWord_688498).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688498).length < 2 ^ (prefixWord ++ tailWord_688498).sum := by decide
  have hdescent : baseEnd_688498 < baseStart_688498 := by decide
  rcases family_descends (prefixWord ++ tailWord_688498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688605 : List Nat := [1, 4, 3, 1, 1, 1, 4, 2, 4]
def baseStart_688605 : Nat := 118140960795 + 688605 * 2 ^ 59
def prefixEnd_688605 : Nat := 4983230072969 + 3 ^ 40 * 688605 * 2
def baseEnd_688605 : Nat := 157149042706392694875853

theorem tailTrace_688605 : CollatzResearch.WordTrace tailWord_688605 prefixEnd_688605 157149042706392694875853 := by
  unfold tailWord_688605
  simp only [CollatzResearch.WordTrace]
  refine ⟨25115487670309164216147269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16743658446872776144098179 25115487670309164216147269)
  ·
    refine ⟨4709153938182968290527613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25115487670309164216147269 4709153938182968290527613)
    ·
      refine ⟨1765932726818613108947855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4709153938182968290527613 1765932726818613108947855)
      ·
        refine ⟨2648899090227919663421783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1765932726818613108947855 2648899090227919663421783)
        ·
          refine ⟨3973348635341879495132675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2648899090227919663421783 3973348635341879495132675)
          ·
            refine ⟨5960022953012819242699013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3973348635341879495132675 5960022953012819242699013)
            ·
              refine ⟨1117504303689903608006065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5960022953012819242699013 1117504303689903608006065)
              ·
                refine ⟨838128227767427706004549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1117504303689903608006065 838128227767427706004549)
                ·
                  refine ⟨157149042706392694875853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 838128227767427706004549 157149042706392694875853)
                  ·
                    rfl

theorem cell21_688605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 4, 2, 4].length) (baseStart_688605 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_688605 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_688605 prefixEnd_688605 := by exact prefixLift 688605
  have htrace : WordTrace (prefixWord ++ tailWord_688605) baseStart_688605 baseEnd_688605 := by
    simpa [prefixWord, tailWord_688605, baseEnd_688605] using wordTrace_append hprefix tailTrace_688605
  have hstable : (prefixWord ++ tailWord_688605).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688605).length < 2 ^ (prefixWord ++ tailWord_688605).sum := by decide
  have hdescent : baseEnd_688605 < baseStart_688605 := by decide
  rcases family_descends (prefixWord ++ tailWord_688605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688664 : List Nat := [2, 1, 2, 3, 3, 2, 1, 1, 6]
def baseStart_688664 : Nat := 118140960795 + 688664 * 2 ^ 59
def prefixEnd_688664 : Nat := 4983230072969 + 3 ^ 40 * 688664 * 2
def baseEnd_688664 : Nat := 157162507310221703392399

theorem tailTrace_688664 : CollatzResearch.WordTrace tailWord_688664 prefixEnd_688664 157162507310221703392399 := by
  unfold tailWord_688664
  simp only [CollatzResearch.WordTrace]
  refine ⟨12558819788547708646272523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16745093051396944861696697 12558819788547708646272523)
  ·
    refine ⟨18838229682821562969408785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12558819788547708646272523 18838229682821562969408785)
    ·
      refine ⟨14128672262116172227056589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18838229682821562969408785 14128672262116172227056589)
      ·
        refine ⟨5298252098293564585146221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14128672262116172227056589 5298252098293564585146221)
        ·
          refine ⟨1986844536860086719429833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5298252098293564585146221 1986844536860086719429833)
          ·
            refine ⟨1490133402645065039572375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1986844536860086719429833 1490133402645065039572375)
            ·
              refine ⟨2235200103967597559358563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1490133402645065039572375 2235200103967597559358563)
              ·
                refine ⟨3352800155951396339037845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2235200103967597559358563 3352800155951396339037845)
                ·
                  refine ⟨157162507310221703392399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3352800155951396339037845 157162507310221703392399)
                  ·
                    rfl

theorem cell21_688664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 1, 6].length) (baseStart_688664 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_688664 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_688664 prefixEnd_688664 := by exact prefixLift 688664
  have htrace : WordTrace (prefixWord ++ tailWord_688664) baseStart_688664 baseEnd_688664 := by
    simpa [prefixWord, tailWord_688664, baseEnd_688664] using wordTrace_append hprefix tailTrace_688664
  have hstable : (prefixWord ++ tailWord_688664).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688664).length < 2 ^ (prefixWord ++ tailWord_688664).sum := by decide
  have hdescent : baseEnd_688664 < baseStart_688664 := by decide
  rcases family_descends (prefixWord ++ tailWord_688664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688740 : List Nat := [2, 3, 1, 1, 2, 2, 3, 3, 4]
def baseStart_688740 : Nat := 118140960795 + 688740 * 2 ^ 59
def prefixEnd_688740 : Nat := 4983230072969 + 3 ^ 40 * 688740 * 2
def baseEnd_688740 : Nat := 157179851545662460125577

theorem tailTrace_688740 : CollatzResearch.WordTrace tailWord_688740 prefixEnd_688740 157179851545662460125577 := by
  unfold tailWord_688740
  simp only [CollatzResearch.WordTrace]
  refine ⟨12560205762410041136155837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16746941016546721514874449 12560205762410041136155837)
  ·
    refine ⟨4710077160903765426058439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12560205762410041136155837 4710077160903765426058439)
    ·
      refine ⟨7065115741355648139087659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4710077160903765426058439 7065115741355648139087659)
      ·
        refine ⟨10597673612033472208631489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7065115741355648139087659 10597673612033472208631489)
        ·
          refine ⟨7948255209025104156473617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10597673612033472208631489 7948255209025104156473617)
          ·
            refine ⟨5961191406768828117355213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7948255209025104156473617 5961191406768828117355213)
            ·
              refine ⟨2235446777538310544008205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5961191406768828117355213 2235446777538310544008205)
              ·
                refine ⟨838292541576866454003077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2235446777538310544008205 838292541576866454003077)
                ·
                  refine ⟨157179851545662460125577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 838292541576866454003077 157179851545662460125577)
                  ·
                    rfl

theorem cell21_688740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 3, 4].length) (baseStart_688740 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_688740 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_688740 prefixEnd_688740 := by exact prefixLift 688740
  have htrace : WordTrace (prefixWord ++ tailWord_688740) baseStart_688740 baseEnd_688740 := by
    simpa [prefixWord, tailWord_688740, baseEnd_688740] using wordTrace_append hprefix tailTrace_688740
  have hstable : (prefixWord ++ tailWord_688740).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688740).length < 2 ^ (prefixWord ++ tailWord_688740).sum := by decide
  have hdescent : baseEnd_688740 < baseStart_688740 := by decide
  rcases family_descends (prefixWord ++ tailWord_688740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688788 : List Nat := [2, 4, 2, 2, 1, 3, 1, 6]
def baseStart_688788 : Nat := 118140960795 + 688788 * 2 ^ 59
def prefixEnd_688788 : Nat := 4983230072969 + 3 ^ 40 * 688788 * 2
def baseEnd_688788 : Nat := 52396935266541681108493

theorem tailTrace_688788 : CollatzResearch.WordTrace tailWord_688788 prefixEnd_688788 52396935266541681108493 := by
  unfold tailWord_688788
  simp only [CollatzResearch.WordTrace]
  refine ⟨12561081114323093235029509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16748108152430790980039345 12561081114323093235029509)
  ·
    refine ⟨2355202708935579981568033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12561081114323093235029509 2355202708935579981568033)
    ·
      refine ⟨1766402031701684986176025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2355202708935579981568033 1766402031701684986176025)
      ·
        refine ⟨1324801523776263739632019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1766402031701684986176025 1324801523776263739632019)
        ·
          refine ⟨1987202285664395609448029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1324801523776263739632019 1987202285664395609448029)
          ·
            refine ⟨745200857124148353543011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1987202285664395609448029 745200857124148353543011)
            ·
              refine ⟨1117801285686222530314517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 745200857124148353543011 1117801285686222530314517)
              ·
                refine ⟨52396935266541681108493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1117801285686222530314517 52396935266541681108493)
                ·
                  rfl

theorem cell21_688788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 1, 6].length) (baseStart_688788 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_688788 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_688788 prefixEnd_688788 := by exact prefixLift 688788
  have htrace : WordTrace (prefixWord ++ tailWord_688788) baseStart_688788 baseEnd_688788 := by
    simpa [prefixWord, tailWord_688788, baseEnd_688788] using wordTrace_append hprefix tailTrace_688788
  have hstable : (prefixWord ++ tailWord_688788).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688788).length < 2 ^ (prefixWord ++ tailWord_688788).sum := by decide
  have hdescent : baseEnd_688788 < baseStart_688788 := by decide
  rcases family_descends (prefixWord ++ tailWord_688788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688830 : List Nat := [4, 2, 1, 1, 2, 1, 10]
def baseStart_688830 : Nat := 118140960795 + 688830 * 2 ^ 59
def prefixEnd_688830 : Nat := 4983230072969 + 3 ^ 40 * 688830 * 2
def baseEnd_688830 : Nat := 17466710085760255958377

theorem tailTrace_688830 : CollatzResearch.WordTrace tailWord_688830 prefixEnd_688830 17466710085760255958377 := by
  unfold tailWord_688830
  simp only [CollatzResearch.WordTrace]
  refine ⟨3140461761811753455385993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16749129396329351762058629 3140461761811753455385993)
  ·
    refine ⟨2355346321358815091539495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3140461761811753455385993 2355346321358815091539495)
    ·
      refine ⟨3533019482038222637309243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2355346321358815091539495 3533019482038222637309243)
      ·
        refine ⟨5299529223057333955963865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3533019482038222637309243 5299529223057333955963865)
        ·
          refine ⟨3974646917293000466972899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5299529223057333955963865 3974646917293000466972899)
          ·
            refine ⟨5961970375939500700459349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3974646917293000466972899 5961970375939500700459349)
            ·
              refine ⟨17466710085760255958377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 5961970375939500700459349 17466710085760255958377)
              ·
                rfl

theorem cell21_688830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 10].length) (baseStart_688830 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_688830 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_688830 prefixEnd_688830 := by exact prefixLift 688830
  have htrace : WordTrace (prefixWord ++ tailWord_688830) baseStart_688830 baseEnd_688830 := by
    simpa [prefixWord, tailWord_688830, baseEnd_688830] using wordTrace_append hprefix tailTrace_688830
  have hstable : (prefixWord ++ tailWord_688830).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688830).length < 2 ^ (prefixWord ++ tailWord_688830).sum := by decide
  have hdescent : baseEnd_688830 < baseStart_688830 := by decide
  rcases family_descends (prefixWord ++ tailWord_688830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688850 : List Nat := [3, 2, 2, 2, 3, 1, 3, 1, 4]
def baseStart_688850 : Nat := 118140960795 + 688850 * 2 ^ 59
def prefixEnd_688850 : Nat := 4983230072969 + 3 ^ 40 * 688850 * 2
def baseEnd_688850 : Nat := 157204955044326713292019

theorem tailTrace_688850 : CollatzResearch.WordTrace tailWord_688850 prefixEnd_688850 157204955044326713292019 := by
  unfold tailWord_688850
  simp only [CollatzResearch.WordTrace]
  refine ⟨6281105888605392764704001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16749615702947714039210669 6281105888605392764704001)
  ·
    refine ⟨4710829416454044573528001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6281105888605392764704001 4710829416454044573528001)
    ·
      refine ⟨3533122062340533430146001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4710829416454044573528001 3533122062340533430146001)
      ·
        refine ⟨2649841546755400072609501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3533122062340533430146001 2649841546755400072609501)
        ·
          refine ⟨993690580033275027228563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2649841546755400072609501 993690580033275027228563)
          ·
            refine ⟨1490535870049912540842845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 993690580033275027228563 1490535870049912540842845)
            ·
              refine ⟨558950951268717202816067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1490535870049912540842845 558950951268717202816067)
              ·
                refine ⟨838426426903075804224101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 558950951268717202816067 838426426903075804224101)
                ·
                  refine ⟨157204955044326713292019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 838426426903075804224101 157204955044326713292019)
                  ·
                    rfl

theorem cell21_688850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 3, 1, 4].length) (baseStart_688850 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_688850 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_688850 prefixEnd_688850 := by exact prefixLift 688850
  have htrace : WordTrace (prefixWord ++ tailWord_688850) baseStart_688850 baseEnd_688850 := by
    simpa [prefixWord, tailWord_688850, baseEnd_688850] using wordTrace_append hprefix tailTrace_688850
  have hstable : (prefixWord ++ tailWord_688850).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688850).length < 2 ^ (prefixWord ++ tailWord_688850).sum := by decide
  have hdescent : baseEnd_688850 < baseStart_688850 := by decide
  rcases family_descends (prefixWord ++ tailWord_688850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688906 : List Nat := [3, 1, 2, 2, 1, 2, 4, 6]
def baseStart_688906 : Nat := 118140960795 + 688906 * 2 ^ 59
def prefixEnd_688906 : Nat := 4983230072969 + 3 ^ 40 * 688906 * 2
def baseEnd_688906 : Nat := 52405911669094353452857

theorem tailTrace_688906 : CollatzResearch.WordTrace tailWord_688906 prefixEnd_688906 52405911669094353452857 := by
  unfold tailWord_688906
  simp only [CollatzResearch.WordTrace]
  refine ⟨6281616510554673155713643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16750977361479128415236381 6281616510554673155713643)
  ·
    refine ⟨9422424765832009733570465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6281616510554673155713643 9422424765832009733570465)
    ·
      refine ⟨7066818574374007300177849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9422424765832009733570465 7066818574374007300177849)
      ·
        refine ⟨5300113930780505475133387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7066818574374007300177849 5300113930780505475133387)
        ·
          refine ⟨7950170896170758212700081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5300113930780505475133387 7950170896170758212700081)
          ·
            refine ⟨5962628172128068659525061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7950170896170758212700081 5962628172128068659525061)
            ·
              refine ⟨1117992782274012873660949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5962628172128068659525061 1117992782274012873660949)
              ·
                refine ⟨52405911669094353452857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1117992782274012873660949 52405911669094353452857)
                ·
                  rfl

theorem cell21_688906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 4, 6].length) (baseStart_688906 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_688906 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_688906 prefixEnd_688906 := by exact prefixLift 688906
  have htrace : WordTrace (prefixWord ++ tailWord_688906) baseStart_688906 baseEnd_688906 := by
    simpa [prefixWord, tailWord_688906, baseEnd_688906] using wordTrace_append hprefix tailTrace_688906
  have hstable : (prefixWord ++ tailWord_688906).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688906).length < 2 ^ (prefixWord ++ tailWord_688906).sum := by decide
  have hdescent : baseEnd_688906 < baseStart_688906 := by decide
  rcases family_descends (prefixWord ++ tailWord_688906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688920 : List Nat := [2, 1, 2, 3, 1, 1, 1, 3, 7]
def baseStart_688920 : Nat := 118140960795 + 688920 * 2 ^ 59
def prefixEnd_688920 : Nat := 4983230072969 + 3 ^ 40 * 688920 * 2
def baseEnd_688920 : Nat := 157220929998022147125209

theorem tailTrace_688920 : CollatzResearch.WordTrace tailWord_688920 prefixEnd_688920 157220929998022147125209 := by
  unfold tailWord_688920
  simp only [CollatzResearch.WordTrace]
  refine ⟨12563488332083986506932107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16751317776111982009242809 12563488332083986506932107)
  ·
    refine ⟨18845232498125979760398161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12563488332083986506932107 18845232498125979760398161)
    ·
      refine ⟨14133924373594484820298621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18845232498125979760398161 14133924373594484820298621)
      ·
        refine ⟨5300221640097931807611983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14133924373594484820298621 5300221640097931807611983)
        ·
          refine ⟨7950332460146897711417975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5300221640097931807611983 7950332460146897711417975)
          ·
            refine ⟨11925498690220346567126963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7950332460146897711417975 11925498690220346567126963)
            ·
              refine ⟨17888248035330519850690445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11925498690220346567126963 17888248035330519850690445)
              ·
                refine ⟨6708093013248944944008917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17888248035330519850690445 6708093013248944944008917)
                ·
                  refine ⟨157220929998022147125209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6708093013248944944008917 157220929998022147125209)
                  ·
                    rfl

theorem cell21_688920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 3, 7].length) (baseStart_688920 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_688920 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_688920 prefixEnd_688920 := by exact prefixLift 688920
  have htrace : WordTrace (prefixWord ++ tailWord_688920) baseStart_688920 baseEnd_688920 := by
    simpa [prefixWord, tailWord_688920, baseEnd_688920] using wordTrace_append hprefix tailTrace_688920
  have hstable : (prefixWord ++ tailWord_688920).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688920).length < 2 ^ (prefixWord ++ tailWord_688920).sum := by decide
  have hdescent : baseEnd_688920 < baseStart_688920 := by decide
  rcases family_descends (prefixWord ++ tailWord_688920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688965 : List Nat := [1, 3, 1, 1, 1, 2, 2, 10]
def baseStart_688965 : Nat := 118140960795 + 688965 * 2 ^ 59
def prefixEnd_688965 : Nat := 4983230072969 + 3 ^ 40 * 688965 * 2
def baseEnd_688965 : Nat := 52410399870370689625039

theorem tailTrace_688965 : CollatzResearch.WordTrace tailWord_688965 prefixEnd_688965 52410399870370689625039 := by
  unfold tailWord_688965
  simp only [CollatzResearch.WordTrace]
  refine ⟨25128617949004945699252349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16752411966003297132834899 25128617949004945699252349)
  ·
    refine ⟨9423231730876854637219631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25128617949004945699252349 9423231730876854637219631)
    ·
      refine ⟨14134847596315281955829447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9423231730876854637219631 14134847596315281955829447)
      ·
        refine ⟨21202271394472922933744171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14134847596315281955829447 21202271394472922933744171)
        ·
          refine ⟨31803407091709384400616257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21202271394472922933744171 31803407091709384400616257)
          ·
            refine ⟨23852555318782038300462193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31803407091709384400616257 23852555318782038300462193)
            ·
              refine ⟨17889416489086528725346645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23852555318782038300462193 17889416489086528725346645)
              ·
                refine ⟨52410399870370689625039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 17889416489086528725346645 52410399870370689625039)
                ·
                  rfl

theorem cell21_688965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 10].length) (baseStart_688965 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_688965 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_688965 prefixEnd_688965 := by exact prefixLift 688965
  have htrace : WordTrace (prefixWord ++ tailWord_688965) baseStart_688965 baseEnd_688965 := by
    simpa [prefixWord, tailWord_688965, baseEnd_688965] using wordTrace_append hprefix tailTrace_688965
  have hstable : (prefixWord ++ tailWord_688965).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688965).length < 2 ^ (prefixWord ++ tailWord_688965).sum := by decide
  have hdescent : baseEnd_688965 < baseStart_688965 := by decide
  rcases family_descends (prefixWord ++ tailWord_688965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689013 : List Nat := [1, 3, 4, 1, 1, 2, 1, 3, 5]
def baseStart_689013 : Nat := 118140960795 + 689013 * 2 ^ 59
def prefixEnd_689013 : Nat := 4983230072969 + 3 ^ 40 * 689013 * 2
def baseEnd_689013 : Nat := 157242153865074652075019

theorem tailTrace_689013 : CollatzResearch.WordTrace tailWord_689013 prefixEnd_689013 157242153865074652075019 := by
  unfold tailWord_689013
  simp only [CollatzResearch.WordTrace]
  refine ⟨25130368652831049896999693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16753579101887366597999795 25130368652831049896999693)
  ·
    refine ⟨9423888244811643711374885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25130368652831049896999693 9423888244811643711374885)
    ·
      refine ⟨1766979045902183195882791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9423888244811643711374885 1766979045902183195882791)
      ·
        refine ⟨2650468568853274793824187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1766979045902183195882791 2650468568853274793824187)
        ·
          refine ⟨3975702853279912190736281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2650468568853274793824187 3975702853279912190736281)
          ·
            refine ⟨2981777139959934143052211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3975702853279912190736281 2981777139959934143052211)
            ·
              refine ⟨4472665709939901214578317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2981777139959934143052211 4472665709939901214578317)
              ·
                refine ⟨1677249641227462955466869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4472665709939901214578317 1677249641227462955466869)
                ·
                  refine ⟨157242153865074652075019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1677249641227462955466869 157242153865074652075019)
                  ·
                    rfl

theorem cell21_689013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 3, 5].length) (baseStart_689013 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_689013 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_689013 prefixEnd_689013 := by exact prefixLift 689013
  have htrace : WordTrace (prefixWord ++ tailWord_689013) baseStart_689013 baseEnd_689013 := by
    simpa [prefixWord, tailWord_689013, baseEnd_689013] using wordTrace_append hprefix tailTrace_689013
  have hstable : (prefixWord ++ tailWord_689013).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689013).length < 2 ^ (prefixWord ++ tailWord_689013).sum := by decide
  have hdescent : baseEnd_689013 < baseStart_689013 := by decide
  rcases family_descends (prefixWord ++ tailWord_689013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689058 : List Nat := [3, 3, 1, 2, 2, 1, 9]
def baseStart_689058 : Nat := 118140960795 + 689058 * 2 ^ 59
def prefixEnd_689058 : Nat := 4983230072969 + 3 ^ 40 * 689058 * 2
def baseEnd_689058 : Nat := 17472491497573841536103

theorem tailTrace_689058 : CollatzResearch.WordTrace tailWord_689058 prefixEnd_689058 17472491497573841536103 := by
  unfold tailWord_689058
  simp only [CollatzResearch.WordTrace]
  refine ⟨6283002484417005645596957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16754673291778681721591885 6283002484417005645596957)
  ·
    refine ⟨2356125931656377117098859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6283002484417005645596957 2356125931656377117098859)
    ·
      refine ⟨3534188897484565675648289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2356125931656377117098859 3534188897484565675648289)
      ·
        refine ⟨2650641673113424256736217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3534188897484565675648289 2650641673113424256736217)
        ·
          refine ⟨1987981254835068192552163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2650641673113424256736217 1987981254835068192552163)
          ·
            refine ⟨2981971882252602288828245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1987981254835068192552163 2981971882252602288828245)
            ·
              refine ⟨17472491497573841536103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2981971882252602288828245 17472491497573841536103)
              ·
                rfl

theorem cell21_689058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 9].length) (baseStart_689058 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_689058 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_689058 prefixEnd_689058 := by exact prefixLift 689058
  have htrace : WordTrace (prefixWord ++ tailWord_689058) baseStart_689058 baseEnd_689058 := by
    simpa [prefixWord, tailWord_689058, baseEnd_689058] using wordTrace_append hprefix tailTrace_689058
  have hstable : (prefixWord ++ tailWord_689058).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689058).length < 2 ^ (prefixWord ++ tailWord_689058).sum := by decide
  have hdescent : baseEnd_689058 < baseStart_689058 := by decide
  rcases family_descends (prefixWord ++ tailWord_689058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689148 : List Nat := [2, 2, 2, 1, 2, 3, 1, 1, 7]
def baseStart_689148 : Nat := 118140960795 + 689148 * 2 ^ 59
def prefixEnd_689148 : Nat := 4983230072969 + 3 ^ 40 * 689148 * 2
def baseEnd_689148 : Nat := 157272962704344417324743

theorem tailTrace_689148 : CollatzResearch.WordTrace tailWord_689148 prefixEnd_689148 157272962704344417324743 := by
  unfold tailWord_689148
  simp only [CollatzResearch.WordTrace]
  refine ⟨12567646253670983976582049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16756861671561311968776065 12567646253670983976582049)
  ·
    refine ⟨9425734690253237982436537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12567646253670983976582049 9425734690253237982436537)
    ·
      refine ⟨7069301017689928486827403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9425734690253237982436537 7069301017689928486827403)
      ·
        refine ⟨10603951526534892730241105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7069301017689928486827403 10603951526534892730241105)
        ·
          refine ⟨7952963644901169547680829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10603951526534892730241105 7952963644901169547680829)
          ·
            refine ⟨2982361366837938580380311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7952963644901169547680829 2982361366837938580380311)
            ·
              refine ⟨4473542050256907870570467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2982361366837938580380311 4473542050256907870570467)
              ·
                refine ⟨6710313075385361805855701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4473542050256907870570467 6710313075385361805855701)
                ·
                  refine ⟨157272962704344417324743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6710313075385361805855701 157272962704344417324743)
                  ·
                    rfl

theorem cell21_689148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 1, 7].length) (baseStart_689148 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_689148 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_689148 prefixEnd_689148 := by exact prefixLift 689148
  have htrace : WordTrace (prefixWord ++ tailWord_689148) baseStart_689148 baseEnd_689148 := by
    simpa [prefixWord, tailWord_689148, baseEnd_689148] using wordTrace_append hprefix tailTrace_689148
  have hstable : (prefixWord ++ tailWord_689148).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689148).length < 2 ^ (prefixWord ++ tailWord_689148).sum := by decide
  have hdescent : baseEnd_689148 < baseStart_689148 := by decide
  rcases family_descends (prefixWord ++ tailWord_689148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689196 : List Nat := [2, 2, 1, 1, 1, 2, 7, 1, 4]
def baseStart_689196 : Nat := 118140960795 + 689196 * 2 ^ 59
def prefixEnd_689196 : Nat := 4983230072969 + 3 ^ 40 * 689196 * 2
def baseEnd_689196 : Nat := 157283916958307000524645

theorem tailTrace_689196 : CollatzResearch.WordTrace tailWord_689196 prefixEnd_689196 157283916958307000524645 := by
  unfold tailWord_689196
  simp only [CollatzResearch.WordTrace]
  refine ⟨12568521605584036075455721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16758028807445381433940961 12568521605584036075455721)
  ·
    refine ⟨9426391204188027056591791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12568521605584036075455721 9426391204188027056591791)
    ·
      refine ⟨14139586806282040584887687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9426391204188027056591791 14139586806282040584887687)
      ·
        refine ⟨21209380209423060877331531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14139586806282040584887687 21209380209423060877331531)
        ·
          refine ⟨31814070314134591315997297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21209380209423060877331531 31814070314134591315997297)
          ·
            refine ⟨23860552735600943486997973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31814070314134591315997297 23860552735600943486997973)
            ·
              refine ⟨559231704740647112976515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 23860552735600943486997973 559231704740647112976515)
              ·
                refine ⟨838847557110970669464773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 559231704740647112976515 838847557110970669464773)
                ·
                  refine ⟨157283916958307000524645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 838847557110970669464773 157283916958307000524645)
                  ·
                    rfl

theorem cell21_689196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 4].length) (baseStart_689196 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_689196 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_689196 prefixEnd_689196 := by exact prefixLift 689196
  have htrace : WordTrace (prefixWord ++ tailWord_689196) baseStart_689196 baseEnd_689196 := by
    simpa [prefixWord, tailWord_689196, baseEnd_689196] using wordTrace_append hprefix tailTrace_689196
  have hstable : (prefixWord ++ tailWord_689196).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689196).length < 2 ^ (prefixWord ++ tailWord_689196).sum := by decide
  have hdescent : baseEnd_689196 < baseStart_689196 := by decide
  rcases family_descends (prefixWord ++ tailWord_689196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689210 : List Nat := [3, 1, 1, 1, 3, 1, 6, 5]
def baseStart_689210 : Nat := 118140960795 + 689210 * 2 ^ 59
def prefixEnd_689210 : Nat := 4983230072969 + 3 ^ 40 * 689210 * 2
def baseEnd_689210 : Nat := 52429037316348695763761

theorem tailTrace_689210 : CollatzResearch.WordTrace tailWord_689210 prefixEnd_689210 52429037316348695763761 := by
  unfold tailWord_689210
  simp only [CollatzResearch.WordTrace]
  refine ⟨6284388458279338135480271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16758369222078235027947389 6284388458279338135480271)
  ·
    refine ⟨9426582687419007203220407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6284388458279338135480271 9426582687419007203220407)
    ·
      refine ⟨14139874031128510804830611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9426582687419007203220407 14139874031128510804830611)
      ·
        refine ⟨21209811046692766207245917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14139874031128510804830611 21209811046692766207245917)
        ·
          refine ⟨7953679142509787327717219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21209811046692766207245917 7953679142509787327717219)
          ·
            refine ⟨11930518713764680991575829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7953679142509787327717219 11930518713764680991575829)
            ·
              refine ⟨559243064707719421480117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 11930518713764680991575829 559243064707719421480117)
              ·
                refine ⟨52429037316348695763761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 559243064707719421480117 52429037316348695763761)
                ·
                  rfl

theorem cell21_689210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 6, 5].length) (baseStart_689210 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_689210 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_689210 prefixEnd_689210 := by exact prefixLift 689210
  have htrace : WordTrace (prefixWord ++ tailWord_689210) baseStart_689210 baseEnd_689210 := by
    simpa [prefixWord, tailWord_689210, baseEnd_689210] using wordTrace_append hprefix tailTrace_689210
  have hstable : (prefixWord ++ tailWord_689210).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689210).length < 2 ^ (prefixWord ++ tailWord_689210).sum := by decide
  have hdescent : baseEnd_689210 < baseStart_689210 := by decide
  rcases family_descends (prefixWord ++ tailWord_689210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689348 : List Nat := [2, 3, 3, 1, 3, 1, 1, 1, 6]
def baseStart_689348 : Nat := 118140960795 + 689348 * 2 ^ 59
def prefixEnd_689348 : Nat := 4983230072969 + 3 ^ 40 * 689348 * 2
def baseEnd_689348 : Nat := 157318605429188513991001

theorem tailTrace_689348 : CollatzResearch.WordTrace tailWord_689348 prefixEnd_689348 157318605429188513991001 := by
  unfold tailWord_689348
  simp only [CollatzResearch.WordTrace]
  refine ⟨12571293553308701055222349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16761724737744934740296465 12571293553308701055222349)
  ·
    refine ⟨4714235082490762895708381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12571293553308701055222349 4714235082490762895708381)
    ·
      refine ⟨1767838155934036085890643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4714235082490762895708381 1767838155934036085890643)
      ·
        refine ⟨2651757233901054128835965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1767838155934036085890643 2651757233901054128835965)
        ·
          refine ⟨994408962712895298313487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2651757233901054128835965 994408962712895298313487)
          ·
            refine ⟨1491613444069342947470231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 994408962712895298313487 1491613444069342947470231)
            ·
              refine ⟨2237420166104014421205347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1491613444069342947470231 2237420166104014421205347)
              ·
                refine ⟨3356130249156021631808021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2237420166104014421205347 3356130249156021631808021)
                ·
                  refine ⟨157318605429188513991001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3356130249156021631808021 157318605429188513991001)
                  ·
                    rfl

theorem cell21_689348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 1, 6].length) (baseStart_689348 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_689348 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_689348 prefixEnd_689348 := by exact prefixLift 689348
  have htrace : WordTrace (prefixWord ++ tailWord_689348) baseStart_689348 baseEnd_689348 := by
    simpa [prefixWord, tailWord_689348, baseEnd_689348] using wordTrace_append hprefix tailTrace_689348
  have hstable : (prefixWord ++ tailWord_689348).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689348).length < 2 ^ (prefixWord ++ tailWord_689348).sum := by decide
  have hdescent : baseEnd_689348 < baseStart_689348 := by decide
  rcases family_descends (prefixWord ++ tailWord_689348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689365 : List Nat := [1, 3, 2, 4, 1, 2, 3, 1, 4]
def baseStart_689365 : Nat := 118140960795 + 689365 * 2 ^ 59
def prefixEnd_689365 : Nat := 4983230072969 + 3 ^ 40 * 689365 * 2
def baseEnd_689365 : Nat := 157322485060800262207633

theorem tailTrace_689365 : CollatzResearch.WordTrace tailWord_689365 prefixEnd_689365 157322485060800262207633 := by
  unfold tailWord_689365
  simp only [CollatzResearch.WordTrace]
  refine ⟨25143207147555814013813549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16762138098370542675875699 25143207147555814013813549)
  ·
    refine ⟨9428702680333430255180081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25143207147555814013813549 9428702680333430255180081)
    ·
      refine ⟨7071527010250072691385061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9428702680333430255180081 7071527010250072691385061)
      ·
        refine ⟨1325911314421888629634699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7071527010250072691385061 1325911314421888629634699)
        ·
          refine ⟨1988866971632832944452049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1325911314421888629634699 1988866971632832944452049)
          ·
            refine ⟨1491650228724624708339037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1988866971632832944452049 1491650228724624708339037)
            ·
              refine ⟨559368835771734265627139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1491650228724624708339037 559368835771734265627139)
              ·
                refine ⟨839053253657601398440709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 559368835771734265627139 839053253657601398440709)
                ·
                  refine ⟨157322485060800262207633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 839053253657601398440709 157322485060800262207633)
                  ·
                    rfl

theorem cell21_689365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 3, 1, 4].length) (baseStart_689365 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_689365 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_689365 prefixEnd_689365 := by exact prefixLift 689365
  have htrace : WordTrace (prefixWord ++ tailWord_689365) baseStart_689365 baseEnd_689365 := by
    simpa [prefixWord, tailWord_689365, baseEnd_689365] using wordTrace_append hprefix tailTrace_689365
  have hstable : (prefixWord ++ tailWord_689365).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689365).length < 2 ^ (prefixWord ++ tailWord_689365).sum := by decide
  have hdescent : baseEnd_689365 < baseStart_689365 := by decide
  rcases family_descends (prefixWord ++ tailWord_689365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689376 : List Nat := [2, 1, 1, 3, 1, 4, 2, 2, 5]
def baseStart_689376 : Nat := 118140960795 + 689376 * 2 ^ 59
def prefixEnd_689376 : Nat := 4983230072969 + 3 ^ 40 * 689376 * 2
def baseEnd_689376 : Nat := 157324995410666687524277

theorem tailTrace_689376 : CollatzResearch.WordTrace tailWord_689376 prefixEnd_689376 157324995410666687524277 := by
  unfold tailWord_689376
  simp only [CollatzResearch.WordTrace]
  refine ⟨12571804175257981446231991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16762405567010641928309321 12571804175257981446231991)
  ·
    refine ⟨18857706262886972169347987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12571804175257981446231991 18857706262886972169347987)
    ·
      refine ⟨28286559394330458254021981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18857706262886972169347987 28286559394330458254021981)
      ·
        refine ⟨10607459772873921845258243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28286559394330458254021981 10607459772873921845258243)
        ·
          refine ⟨15911189659310882767887365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10607459772873921845258243 15911189659310882767887365)
          ·
            refine ⟨2983348061120790518978881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15911189659310882767887365 2983348061120790518978881)
            ·
              refine ⟨2237511045840592889234161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2983348061120790518978881 2237511045840592889234161)
              ·
                refine ⟨1678133284380444666925621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2237511045840592889234161 1678133284380444666925621)
                ·
                  refine ⟨157324995410666687524277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1678133284380444666925621 157324995410666687524277)
                  ·
                    rfl

theorem cell21_689376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 2, 5].length) (baseStart_689376 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_689376 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_689376 prefixEnd_689376 := by exact prefixLift 689376
  have htrace : WordTrace (prefixWord ++ tailWord_689376) baseStart_689376 baseEnd_689376 := by
    simpa [prefixWord, tailWord_689376, baseEnd_689376] using wordTrace_append hprefix tailTrace_689376
  have hstable : (prefixWord ++ tailWord_689376).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689376).length < 2 ^ (prefixWord ++ tailWord_689376).sum := by decide
  have hdescent : baseEnd_689376 < baseStart_689376 := by decide
  rcases family_descends (prefixWord ++ tailWord_689376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689435 : List Nat := [1, 1, 1, 1, 1, 1, 5, 3, 7]
def baseStart_689435 : Nat := 118140960795 + 689435 * 2 ^ 59
def prefixEnd_689435 : Nat := 4983230072969 + 3 ^ 40 * 689435 * 2
def baseEnd_689435 : Nat := 157338460014495696040823

theorem tailTrace_689435 : CollatzResearch.WordTrace tailWord_689435 prefixEnd_689435 157338460014495696040823 := by
  unfold tailWord_689435
  simp only [CollatzResearch.WordTrace]
  refine ⟨25145760257302215968861759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16763840171534810645907839 25145760257302215968861759)
  ·
    refine ⟨37718640385953323953292639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25145760257302215968861759 37718640385953323953292639)
    ·
      refine ⟨56577960578929985929938959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37718640385953323953292639 56577960578929985929938959)
      ·
        refine ⟨84866940868394978894908439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56577960578929985929938959 84866940868394978894908439)
        ·
          refine ⟨127300411302592468342362659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84866940868394978894908439 127300411302592468342362659)
          ·
            refine ⟨190950616953888702513543989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127300411302592468342362659 190950616953888702513543989)
            ·
              refine ⟨17901620339427065860644749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 190950616953888702513543989 17901620339427065860644749)
              ·
                refine ⟨6713107627285149697741781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17901620339427065860644749 6713107627285149697741781)
                ·
                  refine ⟨157338460014495696040823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6713107627285149697741781 157338460014495696040823)
                  ·
                    rfl

theorem cell21_689435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 3, 7].length) (baseStart_689435 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_689435 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_689435 prefixEnd_689435 := by exact prefixLift 689435
  have htrace : WordTrace (prefixWord ++ tailWord_689435) baseStart_689435 baseEnd_689435 := by
    simpa [prefixWord, tailWord_689435, baseEnd_689435] using wordTrace_append hprefix tailTrace_689435
  have hstable : (prefixWord ++ tailWord_689435).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689435).length < 2 ^ (prefixWord ++ tailWord_689435).sum := by decide
  have hdescent : baseEnd_689435 < baseStart_689435 := by decide
  rcases family_descends (prefixWord ++ tailWord_689435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689514 : List Nat := [3, 1, 3, 3, 2, 1, 8]
def baseStart_689514 : Nat := 118140960795 + 689514 * 2 ^ 59
def prefixEnd_689514 : Nat := 4983230072969 + 3 ^ 40 * 689514 * 2
def baseEnd_689514 : Nat := 17484054321201012691555

theorem tailTrace_689514 : CollatzResearch.WordTrace tailWord_689514 prefixEnd_689514 17484054321201012691555 := by
  unfold tailWord_689514
  simp only [CollatzResearch.WordTrace]
  refine ⟨6287160406004003115246899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16765761082677341640658397 6287160406004003115246899)
  ·
    refine ⟨9430740609006004672870349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6287160406004003115246899 9430740609006004672870349)
    ·
      refine ⟨3536527728377251752326381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9430740609006004672870349 3536527728377251752326381)
      ·
        refine ⟨1326197898141469407122393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3536527728377251752326381 1326197898141469407122393)
        ·
          refine ⟨994648423606102055341795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1326197898141469407122393 994648423606102055341795)
          ·
            refine ⟨1491972635409153083012693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 994648423606102055341795 1491972635409153083012693)
            ·
              refine ⟨17484054321201012691555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1491972635409153083012693 17484054321201012691555)
              ·
                rfl

theorem cell21_689514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 8].length) (baseStart_689514 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_689514 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_689514 prefixEnd_689514 := by exact prefixLift 689514
  have htrace : WordTrace (prefixWord ++ tailWord_689514) baseStart_689514 baseEnd_689514 := by
    simpa [prefixWord, tailWord_689514, baseEnd_689514] using wordTrace_append hprefix tailTrace_689514
  have hstable : (prefixWord ++ tailWord_689514).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689514).length < 2 ^ (prefixWord ++ tailWord_689514).sum := by decide
  have hdescent : baseEnd_689514 < baseStart_689514 := by decide
  rcases family_descends (prefixWord ++ tailWord_689514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689593 : List Nat := [1, 2, 1, 4, 4, 2, 2, 1, 4]
def baseStart_689593 : Nat := 118140960795 + 689593 * 2 ^ 59
def prefixEnd_689593 : Nat := 4983230072969 + 3 ^ 40 * 689593 * 2
def baseEnd_689593 : Nat := 157374517767122532407167

theorem tailTrace_689593 : CollatzResearch.WordTrace tailWord_689593 prefixEnd_689593 157374517767122532407167 := by
  unfold tailWord_689593
  simp only [CollatzResearch.WordTrace]
  refine ⟨25151522990729808953113433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16767681993819872635408955 25151522990729808953113433)
  ·
    refine ⟨18863642243047356714835075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25151522990729808953113433 18863642243047356714835075)
    ·
      refine ⟨28295463364571035072252613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18863642243047356714835075 28295463364571035072252613)
      ·
        refine ⟨5305399380857069076047365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28295463364571035072252613 5305399380857069076047365)
        ·
          refine ⟨994762383910700451758881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5305399380857069076047365 994762383910700451758881)
          ·
            refine ⟨746071787933025338819161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 994762383910700451758881 746071787933025338819161)
            ·
              refine ⟨559553840949769004114371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 746071787933025338819161 559553840949769004114371)
              ·
                refine ⟨839330761424653506171557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 559553840949769004114371 839330761424653506171557)
                ·
                  refine ⟨157374517767122532407167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 839330761424653506171557 157374517767122532407167)
                  ·
                    rfl

theorem cell21_689593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 2, 1, 4].length) (baseStart_689593 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_689593 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_689593 prefixEnd_689593 := by exact prefixLift 689593
  have htrace : WordTrace (prefixWord ++ tailWord_689593) baseStart_689593 baseEnd_689593 := by
    simpa [prefixWord, tailWord_689593, baseEnd_689593] using wordTrace_append hprefix tailTrace_689593
  have hstable : (prefixWord ++ tailWord_689593).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689593).length < 2 ^ (prefixWord ++ tailWord_689593).sum := by decide
  have hdescent : baseEnd_689593 < baseStart_689593 := by decide
  rcases family_descends (prefixWord ++ tailWord_689593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689621 : List Nat := [1, 3, 2, 3, 1, 1, 2, 5, 3]
def baseStart_689621 : Nat := 118140960795 + 689621 * 2 ^ 59
def prefixEnd_689621 : Nat := 4983230072969 + 3 ^ 40 * 689621 * 2
def baseEnd_689621 : Nat := 157380907748600705940443

theorem tailTrace_689621 : CollatzResearch.WordTrace tailWord_689621 prefixEnd_689621 157380907748600705940443 := by
  unfold tailWord_689621
  simp only [CollatzResearch.WordTrace]
  refine ⟨25152544234628369735132717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16768362823085579823421811 25152544234628369735132717)
  ·
    refine ⟨9432204087985638650674769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25152544234628369735132717 9432204087985638650674769)
    ·
      refine ⟨7074153065989228988006077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9432204087985638650674769 7074153065989228988006077)
      ·
        refine ⟨2652807399745960870502279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7074153065989228988006077 2652807399745960870502279)
        ·
          refine ⟨3979211099618941305753419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2652807399745960870502279 3979211099618941305753419)
          ·
            refine ⟨5968816649428411958630129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3979211099618941305753419 5968816649428411958630129)
            ·
              refine ⟨4476612487071308968972597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5968816649428411958630129 4476612487071308968972597)
              ·
                refine ⟨419682420662935215841181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4476612487071308968972597 419682420662935215841181)
                ·
                  refine ⟨157380907748600705940443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 419682420662935215841181 157380907748600705940443)
                  ·
                    rfl

theorem cell21_689621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 5, 3].length) (baseStart_689621 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_689621 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_689621 prefixEnd_689621 := by exact prefixLift 689621
  have htrace : WordTrace (prefixWord ++ tailWord_689621) baseStart_689621 baseEnd_689621 := by
    simpa [prefixWord, tailWord_689621, baseEnd_689621] using wordTrace_append hprefix tailTrace_689621
  have hstable : (prefixWord ++ tailWord_689621).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689621).length < 2 ^ (prefixWord ++ tailWord_689621).sum := by decide
  have hdescent : baseEnd_689621 < baseStart_689621 := by decide
  rcases family_descends (prefixWord ++ tailWord_689621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689635 : List Nat := [1, 1, 1, 6, 2, 1, 1, 4, 4]
def baseStart_689635 : Nat := 118140960795 + 689635 * 2 ^ 59
def prefixEnd_689635 : Nat := 4983230072969 + 3 ^ 40 * 689635 * 2
def baseEnd_689635 : Nat := 157384102739339792707081

theorem tailTrace_689635 : CollatzResearch.WordTrace tailWord_689635 prefixEnd_689635 157384102739339792707081 := by
  unfold tailWord_689635
  simp only [CollatzResearch.WordTrace]
  refine ⟨25153054856577650126142359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16768703237718433417428239 25153054856577650126142359)
  ·
    refine ⟨37729582284866475189213539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25153054856577650126142359 37729582284866475189213539)
    ·
      refine ⟨56594373427299712783820309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37729582284866475189213539 56594373427299712783820309)
      ·
        refine ⟨2652861254404674036741577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 56594373427299712783820309 2652861254404674036741577)
        ·
          refine ⟨1989645940803505527556183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2652861254404674036741577 1989645940803505527556183)
          ·
            refine ⟨2984468911205258291334275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1989645940803505527556183 2984468911205258291334275)
            ·
              refine ⟨4476703366807887437001413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2984468911205258291334275 4476703366807887437001413)
              ·
                refine ⟨839381881276478894437765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4476703366807887437001413 839381881276478894437765)
                ·
                  refine ⟨157384102739339792707081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 839381881276478894437765 157384102739339792707081)
                  ·
                    rfl

theorem cell21_689635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 4, 4].length) (baseStart_689635 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_689635 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_689635 prefixEnd_689635 := by exact prefixLift 689635
  have htrace : WordTrace (prefixWord ++ tailWord_689635) baseStart_689635 baseEnd_689635 := by
    simpa [prefixWord, tailWord_689635, baseEnd_689635] using wordTrace_append hprefix tailTrace_689635
  have hstable : (prefixWord ++ tailWord_689635).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689635).length < 2 ^ (prefixWord ++ tailWord_689635).sum := by decide
  have hdescent : baseEnd_689635 < baseStart_689635 := by decide
  rcases family_descends (prefixWord ++ tailWord_689635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689649 : List Nat := [1, 2, 2, 2, 3, 2, 3, 6]
def baseStart_689649 : Nat := 118140960795 + 689649 * 2 ^ 59
def prefixEnd_689649 : Nat := 4983230072969 + 3 ^ 40 * 689649 * 2
def baseEnd_689649 : Nat := 52462432576692959824573

theorem tailTrace_689649 : CollatzResearch.WordTrace tailWord_689649 prefixEnd_689649 52462432576692959824573 := by
  unfold tailWord_689649
  simp only [CollatzResearch.WordTrace]
  refine ⟨25153565478526930517152001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16769043652351287011434667 25153565478526930517152001)
  ·
    refine ⟨18865174108895197887864001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25153565478526930517152001 18865174108895197887864001)
    ·
      refine ⟨14148880581671398415898001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18865174108895197887864001 14148880581671398415898001)
      ·
        refine ⟨10611660436253548811923501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14148880581671398415898001 10611660436253548811923501)
        ·
          refine ⟨3979372663595080804471313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10611660436253548811923501 3979372663595080804471313)
          ·
            refine ⟨2984529497696310603353485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3979372663595080804471313 2984529497696310603353485)
            ·
              refine ⟨1119198561636116476257557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2984529497696310603353485 1119198561636116476257557)
              ·
                refine ⟨52462432576692959824573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1119198561636116476257557 52462432576692959824573)
                ·
                  rfl

theorem cell21_689649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 3, 6].length) (baseStart_689649 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_689649 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_689649 prefixEnd_689649 := by exact prefixLift 689649
  have htrace : WordTrace (prefixWord ++ tailWord_689649) baseStart_689649 baseEnd_689649 := by
    simpa [prefixWord, tailWord_689649, baseEnd_689649] using wordTrace_append hprefix tailTrace_689649
  have hstable : (prefixWord ++ tailWord_689649).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689649).length < 2 ^ (prefixWord ++ tailWord_689649).sum := by decide
  have hdescent : baseEnd_689649 < baseStart_689649 := by decide
  rcases family_descends (prefixWord ++ tailWord_689649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689697 : List Nat := [1, 2, 3, 2, 2, 2, 2, 4, 3]
def baseStart_689697 : Nat := 118140960795 + 689697 * 2 ^ 59
def prefixEnd_689697 : Nat := 4983230072969 + 3 ^ 40 * 689697 * 2
def baseEnd_689697 : Nat := 157398251984041462673621

theorem tailTrace_689697 : CollatzResearch.WordTrace tailWord_689697 prefixEnd_689697 157398251984041462673621 := by
  unfold tailWord_689697
  simp only [CollatzResearch.WordTrace]
  refine ⟨25155316182353034714899345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16770210788235356476599563 25155316182353034714899345)
  ·
    refine ⟨18866487136764776036174509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25155316182353034714899345 18866487136764776036174509)
    ·
      refine ⟨7074932676286791013565441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18866487136764776036174509 7074932676286791013565441)
      ·
        refine ⟨5306199507215093260174081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7074932676286791013565441 5306199507215093260174081)
        ·
          refine ⟨3979649630411319945130561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5306199507215093260174081 3979649630411319945130561)
          ·
            refine ⟨2984737222808489958847921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3979649630411319945130561 2984737222808489958847921)
            ·
              refine ⟨2238552917106367469135941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2984737222808489958847921 2238552917106367469135941)
              ·
                refine ⟨419728671957443900462989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2238552917106367469135941 419728671957443900462989)
                ·
                  refine ⟨157398251984041462673621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 419728671957443900462989 157398251984041462673621)
                  ·
                    rfl

theorem cell21_689697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 4, 3].length) (baseStart_689697 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_689697 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_689697 prefixEnd_689697 := by exact prefixLift 689697
  have htrace : WordTrace (prefixWord ++ tailWord_689697) baseStart_689697 baseEnd_689697 := by
    simpa [prefixWord, tailWord_689697, baseEnd_689697] using wordTrace_append hprefix tailTrace_689697
  have hstable : (prefixWord ++ tailWord_689697).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689697).length < 2 ^ (prefixWord ++ tailWord_689697).sum := by decide
  have hdescent : baseEnd_689697 < baseStart_689697 := by decide
  rcases family_descends (prefixWord ++ tailWord_689697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690018 : List Nat := [3, 3, 2, 1, 2, 2, 2, 3, 3]
def baseStart_690018 : Nat := 118140960795 + 690018 * 2 ^ 59
def prefixEnd_690018 : Nat := 4983230072969 + 3 ^ 40 * 690018 * 2
def baseEnd_690018 : Nat := 157471508557416237822965

theorem tailTrace_690018 : CollatzResearch.WordTrace tailWord_690018 prefixEnd_690018 157471508557416237822965 := by
  unfold tailWord_690018
  simp only [CollatzResearch.WordTrace]
  refine ⟨6291756003547526634333677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16778016009460071024889805 6291756003547526634333677)
  ·
    refine ⟨2359408501330322487875129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6291756003547526634333677 2359408501330322487875129)
    ·
      refine ⟨1769556375997741865906347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2359408501330322487875129 1769556375997741865906347)
      ·
        refine ⟨2654334563996612798859521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1769556375997741865906347 2654334563996612798859521)
        ·
          refine ⟨1990750922997459599144641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2654334563996612798859521 1990750922997459599144641)
          ·
            refine ⟨1493063192248094699358481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1990750922997459599144641 1493063192248094699358481)
            ·
              refine ⟨1119797394186071024518861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1493063192248094699358481 1119797394186071024518861)
              ·
                refine ⟨419924022819776634194573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1119797394186071024518861 419924022819776634194573)
                ·
                  refine ⟨157471508557416237822965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 419924022819776634194573 157471508557416237822965)
                  ·
                    rfl

theorem cell21_690018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 2, 3, 3].length) (baseStart_690018 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_690018 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_690018 prefixEnd_690018 := by exact prefixLift 690018
  have htrace : WordTrace (prefixWord ++ tailWord_690018) baseStart_690018 baseEnd_690018 := by
    simpa [prefixWord, tailWord_690018, baseEnd_690018] using wordTrace_append hprefix tailTrace_690018
  have hstable : (prefixWord ++ tailWord_690018).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690018).length < 2 ^ (prefixWord ++ tailWord_690018).sum := by decide
  have hdescent : baseEnd_690018 < baseStart_690018 := by decide
  rcases family_descends (prefixWord ++ tailWord_690018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690049 : List Nat := [1, 2, 4, 4, 1, 1, 3, 1, 4]
def baseStart_690049 : Nat := 118140960795 + 690049 * 2 ^ 59
def prefixEnd_690049 : Nat := 4983230072969 + 3 ^ 40 * 690049 * 2
def baseEnd_690049 : Nat := 157478583179767072806235

theorem tailTrace_690049 : CollatzResearch.WordTrace tailWord_690049 prefixEnd_690049 157478583179767072806235 := by
  unfold tailWord_690049
  simp only [CollatzResearch.WordTrace]
  refine ⟨25168154677077798831713201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16778769784718532554475467 25168154677077798831713201)
  ·
    refine ⟨18876116007808349123784901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25168154677077798831713201 18876116007808349123784901)
    ·
      refine ⟨3539271751464065460709669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18876116007808349123784901 3539271751464065460709669)
      ·
        refine ⟨663613453399512273883063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3539271751464065460709669 663613453399512273883063)
        ·
          refine ⟨995420180099268410824595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 663613453399512273883063 995420180099268410824595)
          ·
            refine ⟨1493130270148902616236893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 995420180099268410824595 1493130270148902616236893)
            ·
              refine ⟨559923851305838481088835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1493130270148902616236893 559923851305838481088835)
              ·
                refine ⟨839885776958757721633253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 559923851305838481088835 839885776958757721633253)
                ·
                  refine ⟨157478583179767072806235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 839885776958757721633253 157478583179767072806235)
                  ·
                    rfl

theorem cell21_690049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 3, 1, 4].length) (baseStart_690049 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_690049 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_690049 prefixEnd_690049 := by exact prefixLift 690049
  have htrace : WordTrace (prefixWord ++ tailWord_690049) baseStart_690049 baseEnd_690049 := by
    simpa [prefixWord, tailWord_690049, baseEnd_690049] using wordTrace_append hprefix tailTrace_690049
  have hstable : (prefixWord ++ tailWord_690049).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690049).length < 2 ^ (prefixWord ++ tailWord_690049).sum := by decide
  have hdescent : baseEnd_690049 < baseStart_690049 := by decide
  rcases family_descends (prefixWord ++ tailWord_690049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690074 : List Nat := [3, 1, 1, 4, 2, 1, 1, 2, 6]
def baseStart_690074 : Nat := 118140960795 + 690074 * 2 ^ 59
def prefixEnd_690074 : Nat := 4983230072969 + 3 ^ 40 * 690074 * 2
def baseEnd_690074 : Nat := 157484288520372584889517

theorem tailTrace_690074 : CollatzResearch.WordTrace tailWord_690074 prefixEnd_690074 157484288520372584889517 := by
  unfold tailWord_690074
  simp only [CollatzResearch.WordTrace]
  refine ⟨6292266625496807025343319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16779377667991485400915517 6292266625496807025343319)
  ·
    refine ⟨9438399938245210538014979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6292266625496807025343319 9438399938245210538014979)
    ·
      refine ⟨14157599907367815807022469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9438399938245210538014979 14157599907367815807022469)
      ·
        refine ⟨2654549982631465463816713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14157599907367815807022469 2654549982631465463816713)
        ·
          refine ⟨1990912486973599097862535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2654549982631465463816713 1990912486973599097862535)
          ·
            refine ⟨2986368730460398646793803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1990912486973599097862535 2986368730460398646793803)
            ·
              refine ⟨4479553095690597970190705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2986368730460398646793803 4479553095690597970190705)
              ·
                refine ⟨3359664821767948477643029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4479553095690597970190705 3359664821767948477643029)
                ·
                  refine ⟨157484288520372584889517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3359664821767948477643029 157484288520372584889517)
                  ·
                    rfl

theorem cell21_690074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 2, 6].length) (baseStart_690074 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_690074 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_690074 prefixEnd_690074 := by exact prefixLift 690074
  have htrace : WordTrace (prefixWord ++ tailWord_690074) baseStart_690074 baseEnd_690074 := by
    simpa [prefixWord, tailWord_690074, baseEnd_690074] using wordTrace_append hprefix tailTrace_690074
  have hstable : (prefixWord ++ tailWord_690074).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690074).length < 2 ^ (prefixWord ++ tailWord_690074).sum := by decide
  have hdescent : baseEnd_690074 < baseStart_690074 := by decide
  rcases family_descends (prefixWord ++ tailWord_690074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690077 : List Nat := [1, 4, 2, 1, 2, 2, 3, 3, 3]
def baseStart_690077 : Nat := 118140960795 + 690077 * 2 ^ 59
def prefixEnd_690077 : Nat := 4983230072969 + 3 ^ 40 * 690077 * 2
def baseEnd_690077 : Nat := 157484973161245246339511

theorem tailTrace_690077 : CollatzResearch.WordTrace tailWord_690077 prefixEnd_690077 157484973161245246339511 := by
  unfold tailWord_690077
  simp only [CollatzResearch.WordTrace]
  refine ⟨25169175920976359613732485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16779450613984239742488323 25169175920976359613732485)
  ·
    refine ⟨4719220485183067427574841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25169175920976359613732485 4719220485183067427574841)
    ·
      refine ⟨3539415363887300570681131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4719220485183067427574841 3539415363887300570681131)
      ·
        refine ⟨5309123045830950856021697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3539415363887300570681131 5309123045830950856021697)
        ·
          refine ⟨3981842284373213142016273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5309123045830950856021697 3981842284373213142016273)
          ·
            refine ⟨2986381713279909856512205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3981842284373213142016273 2986381713279909856512205)
            ·
              refine ⟨1119893142479966196192077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2986381713279909856512205 1119893142479966196192077)
              ·
                refine ⟨419959928429987323572029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1119893142479966196192077 419959928429987323572029)
                ·
                  refine ⟨157484973161245246339511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 419959928429987323572029 157484973161245246339511)
                  ·
                    rfl

theorem cell21_690077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 3, 3, 3].length) (baseStart_690077 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_690077 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_690077 prefixEnd_690077 := by exact prefixLift 690077
  have htrace : WordTrace (prefixWord ++ tailWord_690077) baseStart_690077 baseEnd_690077 := by
    simpa [prefixWord, tailWord_690077, baseEnd_690077] using wordTrace_append hprefix tailTrace_690077
  have hstable : (prefixWord ++ tailWord_690077).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690077).length < 2 ^ (prefixWord ++ tailWord_690077).sum := by decide
  have hdescent : baseEnd_690077 < baseStart_690077 := by decide
  rcases family_descends (prefixWord ++ tailWord_690077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690108 : List Nat := [2, 2, 2, 5, 1, 1, 1, 3, 4]
def baseStart_690108 : Nat := 118140960795 + 690108 * 2 ^ 59
def prefixEnd_690108 : Nat := 4983230072969 + 3 ^ 40 * 690108 * 2
def baseEnd_690108 : Nat := 157492047783596081322781

theorem tailTrace_690108 : CollatzResearch.WordTrace tailWord_690108 prefixEnd_690108 157492047783596081322781 := by
  unfold tailWord_690108
  simp only [CollatzResearch.WordTrace]
  refine ⟨12585153291932025954055489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16780204389242701272073985 12585153291932025954055489)
  ·
    refine ⟨9438864968949019465541617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12585153291932025954055489 9438864968949019465541617)
    ·
      refine ⟨7079148726711764599156213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9438864968949019465541617 7079148726711764599156213)
      ·
        refine ⟨663670193129227931170895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7079148726711764599156213 663670193129227931170895)
        ·
          refine ⟨995505289693841896756343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 663670193129227931170895 995505289693841896756343)
          ·
            refine ⟨1493257934540762845134515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 995505289693841896756343 1493257934540762845134515)
            ·
              refine ⟨2239886901811144267701773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1493257934540762845134515 2239886901811144267701773)
              ·
                refine ⟨839957588179179100388165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2239886901811144267701773 839957588179179100388165)
                ·
                  refine ⟨157492047783596081322781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 839957588179179100388165 157492047783596081322781)
                  ·
                    rfl

theorem cell21_690108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 3, 4].length) (baseStart_690108 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_690108 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_690108 prefixEnd_690108 := by exact prefixLift 690108
  have htrace : WordTrace (prefixWord ++ tailWord_690108) baseStart_690108 baseEnd_690108 := by
    simpa [prefixWord, tailWord_690108, baseEnd_690108] using wordTrace_append hprefix tailTrace_690108
  have hstable : (prefixWord ++ tailWord_690108).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690108).length < 2 ^ (prefixWord ++ tailWord_690108).sum := by decide
  have hdescent : baseEnd_690108 < baseStart_690108 := by decide
  rcases family_descends (prefixWord ++ tailWord_690108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690136 : List Nat := [2, 1, 2, 2, 2, 2, 2, 5, 3]
def baseStart_690136 : Nat := 118140960795 + 690136 * 2 ^ 59
def prefixEnd_690136 : Nat := 4983230072969 + 3 ^ 40 * 690136 * 2
def baseEnd_690136 : Nat := 157498437765074254856057

theorem tailTrace_690136 : CollatzResearch.WordTrace tailWord_690136 prefixEnd_690136 157498437765074254856057 := by
  unfold tailWord_690136
  simp only [CollatzResearch.WordTrace]
  refine ⟨12585663913881306345065131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16780885218508408460086841 12585663913881306345065131)
  ·
    refine ⟨18878495870821959517597697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12585663913881306345065131 18878495870821959517597697)
    ·
      refine ⟨14158871903116469638198273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18878495870821959517597697 14158871903116469638198273)
      ·
        refine ⟨10619153927337352228648705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14158871903116469638198273 10619153927337352228648705)
        ·
          refine ⟨7964365445503014171486529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10619153927337352228648705 7964365445503014171486529)
          ·
            refine ⟨5973274084127260628614897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7964365445503014171486529 5973274084127260628614897)
            ·
              refine ⟨4479955563095445471461173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5973274084127260628614897 4479955563095445471461173)
              ·
                refine ⟨419995834040198012949485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4479955563095445471461173 419995834040198012949485)
                ·
                  refine ⟨157498437765074254856057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 419995834040198012949485 157498437765074254856057)
                  ·
                    rfl

theorem cell21_690136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 5, 3].length) (baseStart_690136 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_690136 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_690136 prefixEnd_690136 := by exact prefixLift 690136
  have htrace : WordTrace (prefixWord ++ tailWord_690136) baseStart_690136 baseEnd_690136 := by
    simpa [prefixWord, tailWord_690136, baseEnd_690136] using wordTrace_append hprefix tailTrace_690136
  have hstable : (prefixWord ++ tailWord_690136).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690136).length < 2 ^ (prefixWord ++ tailWord_690136).sum := by decide
  have hdescent : baseEnd_690136 < baseStart_690136 := by decide
  rcases family_descends (prefixWord ++ tailWord_690136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690181 : List Nat := [1, 3, 1, 1, 2, 5, 3, 5]
def baseStart_690181 : Nat := 118140960795 + 690181 * 2 ^ 59
def prefixEnd_690181 : Nat := 4983230072969 + 3 ^ 40 * 690181 * 2
def baseEnd_690181 : Nat := 52502902459388058868655

theorem tailTrace_690181 : CollatzResearch.WordTrace tailWord_690181 prefixEnd_690181 52502902459388058868655 := by
  unfold tailWord_690181
  simp only [CollatzResearch.WordTrace]
  refine ⟨25172969112599585375518397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16781979408399723583678931 25172969112599585375518397)
  ·
    refine ⟨9439863417224844515819399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25172969112599585375518397 9439863417224844515819399)
    ·
      refine ⟨14159795125837266773729099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9439863417224844515819399 14159795125837266773729099)
      ·
        refine ⟨21239692688755900160593649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14159795125837266773729099 21239692688755900160593649)
        ·
          refine ⟨15929769516566925120445237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21239692688755900160593649 15929769516566925120445237)
          ·
            refine ⟨1493415892178149230041741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15929769516566925120445237 1493415892178149230041741)
            ·
              refine ⟨560030959566805961265653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1493415892178149230041741 560030959566805961265653)
              ·
                refine ⟨52502902459388058868655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 560030959566805961265653 52502902459388058868655)
                ·
                  rfl

theorem cell21_690181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 3, 5].length) (baseStart_690181 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_690181 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_690181 prefixEnd_690181 := by exact prefixLift 690181
  have htrace : WordTrace (prefixWord ++ tailWord_690181) baseStart_690181 baseEnd_690181 := by
    simpa [prefixWord, tailWord_690181, baseEnd_690181] using wordTrace_append hprefix tailTrace_690181
  have hstable : (prefixWord ++ tailWord_690181).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690181).length < 2 ^ (prefixWord ++ tailWord_690181).sum := by decide
  have hdescent : baseEnd_690181 < baseStart_690181 := by decide
  rcases family_descends (prefixWord ++ tailWord_690181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690240 : List Nat := [2, 1, 1, 2, 2, 5, 1, 7]
def baseStart_690240 : Nat := 118140960795 + 690240 * 2 ^ 59
def prefixEnd_690240 : Nat := 4983230072969 + 3 ^ 40 * 690240 * 2
def baseEnd_690240 : Nat := 52507390660664395040837

theorem tailTrace_690240 : CollatzResearch.WordTrace tailWord_690240 prefixEnd_690240 52507390660664395040837 := by
  unfold tailWord_690240
  simp only [CollatzResearch.WordTrace]
  refine ⟨12587560509692919225958087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16783414012923892301277449 12587560509692919225958087)
  ·
    refine ⟨18881340764539378838937131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12587560509692919225958087 18881340764539378838937131)
    ·
      refine ⟨28322011146809068258405697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18881340764539378838937131 28322011146809068258405697)
      ·
        refine ⟨21241508360106801193804273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28322011146809068258405697 21241508360106801193804273)
        ·
          refine ⟨15931131270080100895353205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21241508360106801193804273 15931131270080100895353205)
          ·
            refine ⟨1493543556570009458939363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15931131270080100895353205 1493543556570009458939363)
            ·
              refine ⟨2240315334855014188409045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1493543556570009458939363 2240315334855014188409045)
              ·
                refine ⟨52507390660664395040837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2240315334855014188409045 52507390660664395040837)
                ·
                  rfl

theorem cell21_690240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 7].length) (baseStart_690240 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_690240 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_690240 prefixEnd_690240 := by exact prefixLift 690240
  have htrace : WordTrace (prefixWord ++ tailWord_690240) baseStart_690240 baseEnd_690240 := by
    simpa [prefixWord, tailWord_690240, baseEnd_690240] using wordTrace_append hprefix tailTrace_690240
  have hstable : (prefixWord ++ tailWord_690240).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690240).length < 2 ^ (prefixWord ++ tailWord_690240).sum := by decide
  have hdescent : baseEnd_690240 < baseStart_690240 := by decide
  rcases family_descends (prefixWord ++ tailWord_690240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690274 : List Nat := [3, 3, 2, 2, 2, 1, 2, 6]
def baseStart_690274 : Nat := 118140960795 + 690274 * 2 ^ 59
def prefixEnd_690274 : Nat := 4983230072969 + 3 ^ 40 * 690274 * 2
def baseEnd_690274 : Nat := 52509977081738893851925

theorem tailTrace_690274 : CollatzResearch.WordTrace tailWord_690274 prefixEnd_690274 52509977081738893851925 := by
  unfold tailWord_690274
  simp only [CollatzResearch.WordTrace]
  refine ⟨6294090275315665564663469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16784240734175108172435917 6294090275315665564663469)
  ·
    refine ⟨2360283853243374586748801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6294090275315665564663469 2360283853243374586748801)
    ·
      refine ⟨1770212889932530940061601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2360283853243374586748801 1770212889932530940061601)
      ·
        refine ⟨1327659667449398205046201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1770212889932530940061601 1327659667449398205046201)
        ·
          refine ⟨995744750587048653784651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1327659667449398205046201 995744750587048653784651)
          ·
            refine ⟨1493617125880572980676977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 995744750587048653784651 1493617125880572980676977)
            ·
              refine ⟨1120212844410429735507733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1493617125880572980676977 1120212844410429735507733)
              ·
                refine ⟨52509977081738893851925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1120212844410429735507733 52509977081738893851925)
                ·
                  rfl

theorem cell21_690274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 2, 6].length) (baseStart_690274 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_690274 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_690274 prefixEnd_690274 := by exact prefixLift 690274
  have htrace : WordTrace (prefixWord ++ tailWord_690274) baseStart_690274 baseEnd_690274 := by
    simpa [prefixWord, tailWord_690274, baseEnd_690274] using wordTrace_append hprefix tailTrace_690274
  have hstable : (prefixWord ++ tailWord_690274).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690274).length < 2 ^ (prefixWord ++ tailWord_690274).sum := by decide
  have hdescent : baseEnd_690274 < baseStart_690274 := by decide
  rcases family_descends (prefixWord ++ tailWord_690274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690333 : List Nat := [1, 4, 2, 1, 1, 5, 1, 6]
def baseStart_690333 : Nat := 118140960795 + 690333 * 2 ^ 59
def prefixEnd_690333 : Nat := 4983230072969 + 3 ^ 40 * 690333 * 2
def baseEnd_690333 : Nat := 52514465283015230024107

theorem tailTrace_690333 : CollatzResearch.WordTrace tailWord_690333 prefixEnd_690333 52514465283015230024107 := by
  unfold tailWord_690333
  simp only [CollatzResearch.WordTrace]
  refine ⟨25178513008048915335051653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16785675338699276890034435 25178513008048915335051653)
  ·
    refine ⟨4720971189009171625322185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25178513008048915335051653 4720971189009171625322185)
    ·
      refine ⟨3540728391756878718991639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4720971189009171625322185 3540728391756878718991639)
      ·
        refine ⟨5311092587635318078487459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3540728391756878718991639 5311092587635318078487459)
        ·
          refine ⟨7966638881452977117731189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5311092587635318078487459 7966638881452977117731189)
          ·
            refine ⟨746872395136216604787299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7966638881452977117731189 746872395136216604787299)
            ·
              refine ⟨1120308592704324907180949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 746872395136216604787299 1120308592704324907180949)
              ·
                refine ⟨52514465283015230024107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1120308592704324907180949 52514465283015230024107)
                ·
                  rfl

theorem cell21_690333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 1, 6].length) (baseStart_690333 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_690333 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_690333 prefixEnd_690333 := by exact prefixLift 690333
  have htrace : WordTrace (prefixWord ++ tailWord_690333) baseStart_690333 baseEnd_690333 := by
    simpa [prefixWord, tailWord_690333, baseEnd_690333] using wordTrace_append hprefix tailTrace_690333
  have hstable : (prefixWord ++ tailWord_690333).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690333).length < 2 ^ (prefixWord ++ tailWord_690333).sum := by decide
  have hdescent : baseEnd_690333 < baseStart_690333 := by decide
  rcases family_descends (prefixWord ++ tailWord_690333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690356 : List Nat := [2, 5, 3, 1, 1, 1, 2, 3, 3]
def baseStart_690356 : Nat := 118140960795 + 690356 * 2 ^ 59
def prefixEnd_690356 : Nat := 4983230072969 + 3 ^ 40 * 690356 * 2
def baseEnd_690356 : Nat := 157548644762402761188941

theorem tailTrace_690356 : CollatzResearch.WordTrace tailWord_690356 prefixEnd_690356 157548644762402761188941 := by
  unfold tailWord_690356
  simp only [CollatzResearch.WordTrace]
  refine ⟨12589675943482795131569461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16786234591310393508759281 12589675943482795131569461)
  ·
    refine ⟨1180282119701512043584637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12589675943482795131569461 1180282119701512043584637)
    ·
      refine ⟨442605794888067016344239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1180282119701512043584637 442605794888067016344239)
      ·
        refine ⟨663908692332100524516359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 442605794888067016344239 663908692332100524516359)
        ·
          refine ⟨995863038498150786774539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 663908692332100524516359 995863038498150786774539)
          ·
            refine ⟨1493794557747226180161809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 995863038498150786774539 1493794557747226180161809)
            ·
              refine ⟨1120345918310419635121357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1493794557747226180161809 1120345918310419635121357)
              ·
                refine ⟨420129719366407363170509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1120345918310419635121357 420129719366407363170509)
                ·
                  refine ⟨157548644762402761188941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 420129719366407363170509 157548644762402761188941)
                  ·
                    rfl

theorem cell21_690356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 2, 3, 3].length) (baseStart_690356 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_690356 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_690356 prefixEnd_690356 := by exact prefixLift 690356
  have htrace : WordTrace (prefixWord ++ tailWord_690356) baseStart_690356 baseEnd_690356 := by
    simpa [prefixWord, tailWord_690356, baseEnd_690356] using wordTrace_append hprefix tailTrace_690356
  have hstable : (prefixWord ++ tailWord_690356).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690356).length < 2 ^ (prefixWord ++ tailWord_690356).sum := by decide
  have hdescent : baseEnd_690356 < baseStart_690356 := by decide
  rcases family_descends (prefixWord ++ tailWord_690356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690361 : List Nat := [1, 2, 1, 4, 1, 2, 2, 2, 6]
def baseStart_690361 : Nat := 118140960795 + 690361 * 2 ^ 59
def prefixEnd_690361 : Nat := 4983230072969 + 3 ^ 40 * 690361 * 2
def baseEnd_690361 : Nat := 157549785830523863605597

theorem tailTrace_690361 : CollatzResearch.WordTrace tailWord_690361 prefixEnd_690361 157549785830523863605597 := by
  unfold tailWord_690361
  simp only [CollatzResearch.WordTrace]
  refine ⟨25179534251947476117070937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16786356167964984078047291 25179534251947476117070937)
  ·
    refine ⟨18884650688960607087803203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25179534251947476117070937 18884650688960607087803203)
    ·
      refine ⟨28326976033440910631704805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18884650688960607087803203 28326976033440910631704805)
      ·
        refine ⟨5311308006270170743444651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28326976033440910631704805 5311308006270170743444651)
        ·
          refine ⟨7966962009405256115166977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5311308006270170743444651 7966962009405256115166977)
          ·
            refine ⟨5975221507053942086375233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7966962009405256115166977 5975221507053942086375233)
            ·
              refine ⟨4481416130290456564781425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5975221507053942086375233 4481416130290456564781425)
              ·
                refine ⟨3361062097717842423586069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4481416130290456564781425 3361062097717842423586069)
                ·
                  refine ⟨157549785830523863605597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3361062097717842423586069 157549785830523863605597)
                  ·
                    rfl

theorem cell21_690361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 2, 6].length) (baseStart_690361 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_690361 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_690361 prefixEnd_690361 := by exact prefixLift 690361
  have htrace : WordTrace (prefixWord ++ tailWord_690361) baseStart_690361 baseEnd_690361 := by
    simpa [prefixWord, tailWord_690361, baseEnd_690361] using wordTrace_append hprefix tailTrace_690361
  have hstable : (prefixWord ++ tailWord_690361).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690361).length < 2 ^ (prefixWord ++ tailWord_690361).sum := by decide
  have hdescent : baseEnd_690361 < baseStart_690361 := by decide
  rcases family_descends (prefixWord ++ tailWord_690361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690440 : List Nat := [2, 1, 3, 2, 3, 3, 1, 1, 5]
def baseStart_690440 : Nat := 118140960795 + 690440 * 2 ^ 59
def prefixEnd_690440 : Nat := 4983230072969 + 3 ^ 40 * 690440 * 2
def baseEnd_690440 : Nat := 157567814706837281788769

theorem tailTrace_690440 : CollatzResearch.WordTrace tailWord_690440 prefixEnd_690440 157567814706837281788769 := by
  unfold tailWord_690440
  simp only [CollatzResearch.WordTrace]
  refine ⟨12591207809330636304598387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16788277079107515072797849 12591207809330636304598387)
  ·
    refine ⟨18886811713995954456897581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12591207809330636304598387 18886811713995954456897581)
    ·
      refine ⟨7082554392748482921336593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18886811713995954456897581 7082554392748482921336593)
      ·
        refine ⟨5311915794561362191002445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7082554392748482921336593 5311915794561362191002445)
        ·
          refine ⟨1991968422960510821625917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5311915794561362191002445 1991968422960510821625917)
          ·
            refine ⟨746988158610191558109719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1991968422960510821625917 746988158610191558109719)
            ·
              refine ⟨1120482237915287337164579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 746988158610191558109719 1120482237915287337164579)
              ·
                refine ⟨1680723356872931005746869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1120482237915287337164579 1680723356872931005746869)
                ·
                  refine ⟨157567814706837281788769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1680723356872931005746869 157567814706837281788769)
                  ·
                    rfl

theorem cell21_690440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 1, 1, 5].length) (baseStart_690440 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_690440 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_690440 prefixEnd_690440 := by exact prefixLift 690440
  have htrace : WordTrace (prefixWord ++ tailWord_690440) baseStart_690440 baseEnd_690440 := by
    simpa [prefixWord, tailWord_690440, baseEnd_690440] using wordTrace_append hprefix tailTrace_690440
  have hstable : (prefixWord ++ tailWord_690440).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690440).length < 2 ^ (prefixWord ++ tailWord_690440).sum := by decide
  have hdescent : baseEnd_690440 < baseStart_690440 := by decide
  rcases family_descends (prefixWord ++ tailWord_690440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690468 : List Nat := [2, 3, 1, 3, 1, 2, 2, 7]
def baseStart_690468 : Nat := 118140960795 + 690468 * 2 ^ 59
def prefixEnd_690468 : Nat := 4983230072969 + 3 ^ 40 * 690468 * 2
def baseEnd_690468 : Nat := 52524734896105151774015

theorem tailTrace_690468 : CollatzResearch.WordTrace tailWord_690468 prefixEnd_690468 52524734896105151774015 := by
  unfold tailWord_690468
  simp only [CollatzResearch.WordTrace]
  refine ⟨12591718431279916695608029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16788957908373222260810705 12591718431279916695608029)
  ·
    refine ⟨4721894411729968760853011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12591718431279916695608029 4721894411729968760853011)
    ·
      refine ⟨7082841617594953141279517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4721894411729968760853011 7082841617594953141279517)
      ·
        refine ⟨2656065606598107427979819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7082841617594953141279517 2656065606598107427979819)
        ·
          refine ⟨3984098409897161141969729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2656065606598107427979819 3984098409897161141969729)
          ·
            refine ⟨2988073807422870856477297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3984098409897161141969729 2988073807422870856477297)
            ·
              refine ⟨2241055355567153142357973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2988073807422870856477297 2241055355567153142357973)
              ·
                refine ⟨52524734896105151774015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2241055355567153142357973 52524734896105151774015)
                ·
                  rfl

theorem cell21_690468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 7].length) (baseStart_690468 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_690468 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_690468 prefixEnd_690468 := by exact prefixLift 690468
  have htrace : WordTrace (prefixWord ++ tailWord_690468) baseStart_690468 baseEnd_690468 := by
    simpa [prefixWord, tailWord_690468, baseEnd_690468] using wordTrace_append hprefix tailTrace_690468
  have hstable : (prefixWord ++ tailWord_690468).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690468).length < 2 ^ (prefixWord ++ tailWord_690468).sum := by decide
  have hdescent : baseEnd_690468 < baseStart_690468 := by decide
  rcases family_descends (prefixWord ++ tailWord_690468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690527 : List Nat := [1, 1, 2, 3, 1, 2, 2, 9]
def baseStart_690527 : Nat := 118140960795 + 690527 * 2 ^ 59
def prefixEnd_690527 : Nat := 4983230072969 + 3 ^ 40 * 690527 * 2
def baseEnd_690527 : Nat := 52529223097381487946197

theorem tailTrace_690527 : CollatzResearch.WordTrace tailWord_690527 prefixEnd_690527 52529223097381487946197 := by
  unfold tailWord_690527
  simp only [CollatzResearch.WordTrace]
  refine ⟨25185588769346086467613835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16790392512897390978409223 25185588769346086467613835)
  ·
    refine ⟨37778383154019129701420753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25185588769346086467613835 37778383154019129701420753)
    ·
      refine ⟨28333787365514347276065565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37778383154019129701420753 28333787365514347276065565)
      ·
        refine ⟨10625170262067880228524587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28333787365514347276065565 10625170262067880228524587)
        ·
          refine ⟨15937755393101820342786881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10625170262067880228524587 15937755393101820342786881)
          ·
            refine ⟨11953316544826365257090161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15937755393101820342786881 11953316544826365257090161)
            ·
              refine ⟨8964987408619773942817621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11953316544826365257090161 8964987408619773942817621)
              ·
                refine ⟨52529223097381487946197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8964987408619773942817621 52529223097381487946197)
                ·
                  rfl

theorem cell21_690527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 9].length) (baseStart_690527 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_690527 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_690527 prefixEnd_690527 := by exact prefixLift 690527
  have htrace : WordTrace (prefixWord ++ tailWord_690527) baseStart_690527 baseEnd_690527 := by
    simpa [prefixWord, tailWord_690527, baseEnd_690527] using wordTrace_append hprefix tailTrace_690527
  have hstable : (prefixWord ++ tailWord_690527).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690527).length < 2 ^ (prefixWord ++ tailWord_690527).sum := by decide
  have hdescent : baseEnd_690527 < baseStart_690527 := by decide
  rcases family_descends (prefixWord ++ tailWord_690527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690592 : List Nat := [2, 1, 1, 4, 1, 3, 3, 3, 3]
def baseStart_690592 : Nat := 118140960795 + 690592 * 2 ^ 59
def prefixEnd_690592 : Nat := 4983230072969 + 3 ^ 40 * 690592 * 2
def baseEnd_690592 : Nat := 157602503177718795255125

theorem tailTrace_690592 : CollatzResearch.WordTrace tailWord_690592 prefixEnd_690592 157602503177718795255125 := by
  unfold tailWord_690592
  simp only [CollatzResearch.WordTrace]
  refine ⟨12593979757055301284365015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16791973009407068379153353 12593979757055301284365015)
  ·
    refine ⟨18890969635582951926547523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12593979757055301284365015 18890969635582951926547523)
    ·
      refine ⟨28336454453374427889821285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18890969635582951926547523 28336454453374427889821285)
      ·
        refine ⟨5313085210007705229341491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28336454453374427889821285 5313085210007705229341491)
        ·
          refine ⟨7969627815011557844012237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5313085210007705229341491 7969627815011557844012237)
          ·
            refine ⟨2988610430629334191504589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7969627815011557844012237 2988610430629334191504589)
            ·
              refine ⟨1120728911486000321814221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2988610430629334191504589 1120728911486000321814221)
              ·
                refine ⟨420273341807250120680333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1120728911486000321814221 420273341807250120680333)
                ·
                  refine ⟨157602503177718795255125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 420273341807250120680333 157602503177718795255125)
                  ·
                    rfl

theorem cell21_690592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 3, 3, 3].length) (baseStart_690592 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_690592 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_690592 prefixEnd_690592 := by exact prefixLift 690592
  have htrace : WordTrace (prefixWord ++ tailWord_690592) baseStart_690592 baseEnd_690592 := by
    simpa [prefixWord, tailWord_690592, baseEnd_690592] using wordTrace_append hprefix tailTrace_690592
  have hstable : (prefixWord ++ tailWord_690592).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690592).length < 2 ^ (prefixWord ++ tailWord_690592).sum := by decide
  have hdescent : baseEnd_690592 < baseStart_690592 := by decide
  rcases family_descends (prefixWord ++ tailWord_690592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690609 : List Nat := [1, 2, 2, 4, 1, 3, 3, 2, 3]
def baseStart_690609 : Nat := 118140960795 + 690609 * 2 ^ 59
def prefixEnd_690609 : Nat := 4983230072969 + 3 ^ 40 * 690609 * 2
def baseEnd_690609 : Nat := 157606382809330543471757

theorem tailTrace_690609 : CollatzResearch.WordTrace tailWord_690609 prefixEnd_690609 157606382809330543471757 := by
  unfold tailWord_690609
  simp only [CollatzResearch.WordTrace]
  refine ⟨25188579555049014472098881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16792386370032676314732587 25188579555049014472098881)
  ·
    refine ⟨18891434666286760854074161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25188579555049014472098881 18891434666286760854074161)
    ·
      refine ⟨14168575999715070640555621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18891434666286760854074161 14168575999715070640555621)
      ·
        refine ⟨2656607999946575745104179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14168575999715070640555621 2656607999946575745104179)
        ·
          refine ⟨3984911999919863617656269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2656607999946575745104179 3984911999919863617656269)
          ·
            refine ⟨1494341999969948856621101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3984911999919863617656269 1494341999969948856621101)
            ·
              refine ⟨560378249988730821232913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1494341999969948856621101 560378249988730821232913)
              ·
                refine ⟨420283687491548115924685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 560378249988730821232913 420283687491548115924685)
                ·
                  refine ⟨157606382809330543471757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 420283687491548115924685 157606382809330543471757)
                  ·
                    rfl

theorem cell21_690609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 3, 2, 3].length) (baseStart_690609 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_690609 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_690609 prefixEnd_690609 := by exact prefixLift 690609
  have htrace : WordTrace (prefixWord ++ tailWord_690609) baseStart_690609 baseEnd_690609 := by
    simpa [prefixWord, tailWord_690609, baseEnd_690609] using wordTrace_append hprefix tailTrace_690609
  have hstable : (prefixWord ++ tailWord_690609).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690609).length < 2 ^ (prefixWord ++ tailWord_690609).sum := by decide
  have hdescent : baseEnd_690609 < baseStart_690609 := by decide
  rcases family_descends (prefixWord ++ tailWord_690609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690620 : List Nat := [2, 2, 2, 4, 1, 1, 1, 8]
def baseStart_690620 : Nat := 118140960795 + 690620 * 2 ^ 59
def prefixEnd_690620 : Nat := 4983230072969 + 3 ^ 40 * 690620 * 2
def baseEnd_690620 : Nat := 52536297719732322929467

theorem tailTrace_690620 : CollatzResearch.WordTrace tailWord_690620 prefixEnd_690620 52536297719732322929467 := by
  unfold tailWord_690620
  simp only [CollatzResearch.WordTrace]
  refine ⟨12594490379004581675374657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16792653838672775567166209 12594490379004581675374657)
  ·
    refine ⟨9445867784253436256530993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12594490379004581675374657 9445867784253436256530993)
    ·
      refine ⟨7084400838190077192398245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9445867784253436256530993 7084400838190077192398245)
      ·
        refine ⟨1328325157160639473574671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7084400838190077192398245 1328325157160639473574671)
        ·
          refine ⟨1992487735740959210362007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1328325157160639473574671 1992487735740959210362007)
          ·
            refine ⟨2988731603611438815543011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1992487735740959210362007 2988731603611438815543011)
            ·
              refine ⟨4483097405417158223314517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2988731603611438815543011 4483097405417158223314517)
              ·
                refine ⟨52536297719732322929467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4483097405417158223314517 52536297719732322929467)
                ·
                  rfl

theorem cell21_690620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 8].length) (baseStart_690620 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_690620 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_690620 prefixEnd_690620 := by exact prefixLift 690620
  have htrace : WordTrace (prefixWord ++ tailWord_690620) baseStart_690620 baseEnd_690620 := by
    simpa [prefixWord, tailWord_690620, baseEnd_690620] using wordTrace_append hprefix tailTrace_690620
  have hstable : (prefixWord ++ tailWord_690620).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690620).length < 2 ^ (prefixWord ++ tailWord_690620).sum := by decide
  have hdescent : baseEnd_690620 < baseStart_690620 := by decide
  rcases family_descends (prefixWord ++ tailWord_690620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690634 : List Nat := [3, 1, 2, 1, 2, 2, 2, 1, 7]
def baseStart_690634 : Nat := 118140960795 + 690634 * 2 ^ 59
def prefixEnd_690634 : Nat := 4983230072969 + 3 ^ 40 * 690634 * 2
def baseEnd_690634 : Nat := 157612088149936055555039

theorem tailTrace_690634 : CollatzResearch.WordTrace tailWord_690634 prefixEnd_690634 157612088149936055555039 := by
  unfold tailWord_690634
  simp only [CollatzResearch.WordTrace]
  refine ⟨6297372844989610935439739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16792994253305629161172637 6297372844989610935439739)
  ·
    refine ⟨9446059267484416403159609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6297372844989610935439739 9446059267484416403159609)
    ·
      refine ⟨7084544450613312302369707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9446059267484416403159609 7084544450613312302369707)
      ·
        refine ⟨10626816675919968453554561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7084544450613312302369707 10626816675919968453554561)
        ·
          refine ⟨7970112506939976340165921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10626816675919968453554561 7970112506939976340165921)
          ·
            refine ⟨5977584380204982255124441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7970112506939976340165921 5977584380204982255124441)
            ·
              refine ⟨4483188285153736691343331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5977584380204982255124441 4483188285153736691343331)
              ·
                refine ⟨6724782427730605037014997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4483188285153736691343331 6724782427730605037014997)
                ·
                  refine ⟨157612088149936055555039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6724782427730605037014997 157612088149936055555039)
                  ·
                    rfl

theorem cell21_690634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 1, 7].length) (baseStart_690634 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_690634 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_690634 prefixEnd_690634 := by exact prefixLift 690634
  have htrace : WordTrace (prefixWord ++ tailWord_690634) baseStart_690634 baseEnd_690634 := by
    simpa [prefixWord, tailWord_690634, baseEnd_690634] using wordTrace_append hprefix tailTrace_690634
  have hstable : (prefixWord ++ tailWord_690634).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690634).length < 2 ^ (prefixWord ++ tailWord_690634).sum := by decide
  have hdescent : baseEnd_690634 < baseStart_690634 := by decide
  rcases family_descends (prefixWord ++ tailWord_690634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690772 : List Nat := [2, 4, 1, 1, 1, 5, 7]
def baseStart_690772 : Nat := 118140960795 + 690772 * 2 ^ 59
def prefixEnd_690772 : Nat := 4983230072969 + 3 ^ 40 * 690772 * 2
def baseEnd_690772 : Nat := 17515953514453164694973

theorem tailTrace_690772 : CollatzResearch.WordTrace tailWord_690772 prefixEnd_690772 17515953514453164694973 := by
  unfold tailWord_690772
  simp only [CollatzResearch.WordTrace]
  refine ⟨12597262326729246655141285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16796349768972328873521713 12597262326729246655141285)
  ·
    refine ⟨2361986686261733747838991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12597262326729246655141285 2361986686261733747838991)
    ·
      refine ⟨3542980029392600621758487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2361986686261733747838991 3542980029392600621758487)
      ·
        refine ⟨5314470044088900932637731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3542980029392600621758487 5314470044088900932637731)
        ·
          refine ⟨7971705066133351398956597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5314470044088900932637731 7971705066133351398956597)
          ·
            refine ⟨747347349950001693652181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7971705066133351398956597 747347349950001693652181)
            ·
              refine ⟨17515953514453164694973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 747347349950001693652181 17515953514453164694973)
              ·
                rfl

theorem cell21_690772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 7].length) (baseStart_690772 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_690772 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_690772 prefixEnd_690772 := by exact prefixLift 690772
  have htrace : WordTrace (prefixWord ++ tailWord_690772) baseStart_690772 baseEnd_690772 := by
    simpa [prefixWord, tailWord_690772, baseEnd_690772] using wordTrace_append hprefix tailTrace_690772
  have hstable : (prefixWord ++ tailWord_690772).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690772).length < 2 ^ (prefixWord ++ tailWord_690772).sum := by decide
  have hdescent : baseEnd_690772 < baseStart_690772 := by decide
  rcases family_descends (prefixWord ++ tailWord_690772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690792 : List Nat := [2, 1, 4, 3, 2, 2, 2, 1, 4]
def baseStart_690792 : Nat := 118140960795 + 690792 * 2 ^ 59
def prefixEnd_690792 : Nat := 4983230072969 + 3 ^ 40 * 690792 * 2
def baseEnd_690792 : Nat := 157648145902562891921383

theorem tailTrace_690792 : CollatzResearch.WordTrace tailWord_690792 prefixEnd_690792 157648145902562891921383 := by
  unfold tailWord_690792
  simp only [CollatzResearch.WordTrace]
  refine ⟨12597627056693018363005315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16796836075590691150673753 12597627056693018363005315)
  ·
    refine ⟨18896440585039527544507973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12597627056693018363005315 18896440585039527544507973)
    ·
      refine ⟨3543082609694911414595245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18896440585039527544507973 3543082609694911414595245)
      ·
        refine ⟨1328655978635591780473217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3543082609694911414595245 1328655978635591780473217)
        ·
          refine ⟨996491983976693835354913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1328655978635591780473217 996491983976693835354913)
          ·
            refine ⟨747368987982520376516185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 996491983976693835354913 747368987982520376516185)
            ·
              refine ⟨560526740986890282387139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 747368987982520376516185 560526740986890282387139)
              ·
                refine ⟨840790111480335423580709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 560526740986890282387139 840790111480335423580709)
                ·
                  refine ⟨157648145902562891921383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 840790111480335423580709 157648145902562891921383)
                  ·
                    rfl

theorem cell21_690792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 2, 1, 4].length) (baseStart_690792 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_690792 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_690792 prefixEnd_690792 := by exact prefixLift 690792
  have htrace : WordTrace (prefixWord ++ tailWord_690792) baseStart_690792 baseEnd_690792 := by
    simpa [prefixWord, tailWord_690792, baseEnd_690792] using wordTrace_append hprefix tailTrace_690792
  have hstable : (prefixWord ++ tailWord_690792).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690792).length < 2 ^ (prefixWord ++ tailWord_690792).sum := by decide
  have hdescent : baseEnd_690792 < baseStart_690792 := by decide
  rcases family_descends (prefixWord ++ tailWord_690792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690834 : List Nat := [3, 2, 3, 1, 2, 1, 1, 4, 4]
def baseStart_690834 : Nat := 118140960795 + 690834 * 2 ^ 59
def prefixEnd_690834 : Nat := 4983230072969 + 3 ^ 40 * 690834 * 2
def baseEnd_690834 : Nat := 157657730874780152221297

theorem tailTrace_690834 : CollatzResearch.WordTrace tailWord_690834 prefixEnd_690834 157657730874780152221297 := by
  unfold tailWord_690834
  simp only [CollatzResearch.WordTrace]
  refine ⟨6299196494808469474759889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16797857319489251932693037 6299196494808469474759889)
  ·
    refine ⟨4724397371106352106069917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6299196494808469474759889 4724397371106352106069917)
    ·
      refine ⟨1771649014164882039776219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4724397371106352106069917 1771649014164882039776219)
      ·
        refine ⟨2657473521247323059664329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1771649014164882039776219 2657473521247323059664329)
        ·
          refine ⟨1993105140935492294748247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2657473521247323059664329 1993105140935492294748247)
          ·
            refine ⟨2989657711403238442122371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1993105140935492294748247 2989657711403238442122371)
            ·
              refine ⟨4484486567104857663183557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2989657711403238442122371 4484486567104857663183557)
              ·
                refine ⟨840841231332160811846917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4484486567104857663183557 840841231332160811846917)
                ·
                  refine ⟨157657730874780152221297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 840841231332160811846917 157657730874780152221297)
                  ·
                    rfl

theorem cell21_690834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 4, 4].length) (baseStart_690834 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_690834 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_690834 prefixEnd_690834 := by exact prefixLift 690834
  have htrace : WordTrace (prefixWord ++ tailWord_690834) baseStart_690834 baseEnd_690834 := by
    simpa [prefixWord, tailWord_690834, baseEnd_690834] using wordTrace_append hprefix tailTrace_690834
  have hstable : (prefixWord ++ tailWord_690834).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690834).length < 2 ^ (prefixWord ++ tailWord_690834).sum := by decide
  have hdescent : baseEnd_690834 < baseStart_690834 := by decide
  rcases family_descends (prefixWord ++ tailWord_690834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690879 : List Nat := [1, 1, 2, 2, 2, 4, 1, 5, 3]
def baseStart_690879 : Nat := 118140960795 + 690879 * 2 ^ 59
def prefixEnd_690879 : Nat := 4983230072969 + 3 ^ 40 * 690879 * 2
def baseEnd_690879 : Nat := 157668000487870073971205

theorem tailTrace_690879 : CollatzResearch.WordTrace tailWord_690879 prefixEnd_690879 157668000487870073971205 := by
  unfold tailWord_690879
  simp only [CollatzResearch.WordTrace]
  refine ⟨25198427264070850584427691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16798951509380567056285127 25198427264070850584427691)
  ·
    refine ⟨37797640896106275876641537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25198427264070850584427691 37797640896106275876641537)
    ·
      refine ⟨28348230672079706907481153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37797640896106275876641537 28348230672079706907481153)
      ·
        refine ⟨21261173004059780180610865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28348230672079706907481153 21261173004059780180610865)
        ·
          refine ⟨15945879753044835135458149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21261173004059780180610865 15945879753044835135458149)
          ·
            refine ⟨2989852453695906587898403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15945879753044835135458149 2989852453695906587898403)
            ·
              refine ⟨4484778680543859881847605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2989852453695906587898403 4484778680543859881847605)
              ·
                refine ⟨420448001300986863923213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4484778680543859881847605 420448001300986863923213)
                ·
                  refine ⟨157668000487870073971205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 420448001300986863923213 157668000487870073971205)
                  ·
                    rfl

theorem cell21_690879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 5, 3].length) (baseStart_690879 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_690879 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_690879 prefixEnd_690879 := by exact prefixLift 690879
  have htrace : WordTrace (prefixWord ++ tailWord_690879) baseStart_690879 baseEnd_690879 := by
    simpa [prefixWord, tailWord_690879, baseEnd_690879] using wordTrace_append hprefix tailTrace_690879
  have hstable : (prefixWord ++ tailWord_690879).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690879).length < 2 ^ (prefixWord ++ tailWord_690879).sum := by decide
  have hdescent : baseEnd_690879 < baseStart_690879 := by decide
  rcases family_descends (prefixWord ++ tailWord_690879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691006 : List Nat := [4, 2, 1, 2, 3, 2, 2, 2, 3]
def baseStart_691006 : Nat := 118140960795 + 691006 * 2 ^ 59
def prefixEnd_691006 : Nat := 4983230072969 + 3 ^ 40 * 691006 * 2
def baseEnd_691006 : Nat := 157696983618146075354279

theorem tailTrace_691006 : CollatzResearch.WordTrace tailWord_691006 prefixEnd_691006 157696983618146075354279 := by
  unfold tailWord_691006
  simp only [CollatzResearch.WordTrace]
  refine ⟨3150382416826343909287609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16802039556407167516200581 3150382416826343909287609)
  ·
    refine ⟨2362786812619757931965707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3150382416826343909287609 2362786812619757931965707)
    ·
      refine ⟨3544180218929636897948561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2362786812619757931965707 3544180218929636897948561)
      ·
        refine ⟨2658135164197227673461421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3544180218929636897948561 2658135164197227673461421)
        ·
          refine ⟨996800686573960377548033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2658135164197227673461421 996800686573960377548033)
          ·
            refine ⟨747600514930470283161025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 996800686573960377548033 747600514930470283161025)
            ·
              refine ⟨560700386197852712370769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 747600514930470283161025 560700386197852712370769)
              ·
                refine ⟨420525289648389534278077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 560700386197852712370769 420525289648389534278077)
                ·
                  refine ⟨157696983618146075354279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 420525289648389534278077 157696983618146075354279)
                  ·
                    rfl

theorem cell21_691006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 2, 2, 3].length) (baseStart_691006 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_691006 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_691006 prefixEnd_691006 := by exact prefixLift 691006
  have htrace : WordTrace (prefixWord ++ tailWord_691006) baseStart_691006 baseEnd_691006 := by
    simpa [prefixWord, tailWord_691006, baseEnd_691006] using wordTrace_append hprefix tailTrace_691006
  have hstable : (prefixWord ++ tailWord_691006).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691006).length < 2 ^ (prefixWord ++ tailWord_691006).sum := by decide
  have hdescent : baseEnd_691006 < baseStart_691006 := by decide
  rcases family_descends (prefixWord ++ tailWord_691006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691048 : List Nat := [2, 1, 4, 2, 1, 3, 2, 3, 3]
def baseStart_691048 : Nat := 118140960795 + 691048 * 2 ^ 59
def prefixEnd_691048 : Nat := 4983230072969 + 3 ^ 40 * 691048 * 2
def baseEnd_691048 : Nat := 157706568590363335654193

theorem tailTrace_691048 : CollatzResearch.WordTrace tailWord_691048 prefixEnd_691048 157706568590363335654193 := by
  unfold tailWord_691048
  simp only [CollatzResearch.WordTrace]
  refine ⟨12602295600229296223664899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16803060800305728298219865 12602295600229296223664899)
  ·
    refine ⟨18903443400343944335497349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12602295600229296223664899 18903443400343944335497349)
    ·
      refine ⟨3544395637564489562905753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18903443400343944335497349 3544395637564489562905753)
      ·
        refine ⟨2658296728173367172179315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3544395637564489562905753 2658296728173367172179315)
        ·
          refine ⟨3987445092260050758268973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2658296728173367172179315 3987445092260050758268973)
          ·
            refine ⟨1495291909597519034350865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3987445092260050758268973 1495291909597519034350865)
            ·
              refine ⟨1121468932198139275763149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1495291909597519034350865 1121468932198139275763149)
              ·
                refine ⟨420550849574302228411181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1121468932198139275763149 420550849574302228411181)
                ·
                  refine ⟨157706568590363335654193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 420550849574302228411181 157706568590363335654193)
                  ·
                    rfl

theorem cell21_691048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 2, 3, 3].length) (baseStart_691048 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_691048 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_691048 prefixEnd_691048 := by exact prefixLift 691048
  have htrace : WordTrace (prefixWord ++ tailWord_691048) baseStart_691048 baseEnd_691048 := by
    simpa [prefixWord, tailWord_691048, baseEnd_691048] using wordTrace_append hprefix tailTrace_691048
  have hstable : (prefixWord ++ tailWord_691048).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691048).length < 2 ^ (prefixWord ++ tailWord_691048).sum := by decide
  have hdescent : baseEnd_691048 < baseStart_691048 := by decide
  rcases family_descends (prefixWord ++ tailWord_691048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691062 : List Nat := [5, 1, 1, 3, 1, 2, 1, 1, 6]
def baseStart_691062 : Nat := 118140960795 + 691062 * 2 ^ 59
def prefixEnd_691062 : Nat := 4983230072969 + 3 ^ 40 * 691062 * 2
def baseEnd_691062 : Nat := 157709763581102422420831

theorem tailTrace_691062 : CollatzResearch.WordTrace tailWord_691062 prefixEnd_691062 157709763581102422420831 := by
  unfold tailWord_691062
  simp only [CollatzResearch.WordTrace]
  refine ⟨1575318863900492052396215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16803401214938581892226293 1575318863900492052396215)
  ·
    refine ⟨2362978295850738078594323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1575318863900492052396215 2362978295850738078594323)
    ·
      refine ⟨3544467443776107117891485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2362978295850738078594323 3544467443776107117891485)
      ·
        refine ⟨1329175291416040169209307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3544467443776107117891485 1329175291416040169209307)
        ·
          refine ⟨1993762937124060253813961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1329175291416040169209307 1993762937124060253813961)
          ·
            refine ⟨1495322202843045190360471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1993762937124060253813961 1495322202843045190360471)
            ·
              refine ⟨2242983304264567785540707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1495322202843045190360471 2242983304264567785540707)
              ·
                refine ⟨3364474956396851678311061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2242983304264567785540707 3364474956396851678311061)
                ·
                  refine ⟨157709763581102422420831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3364474956396851678311061 157709763581102422420831)
                  ·
                    rfl

theorem cell21_691062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 1, 6].length) (baseStart_691062 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_691062 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_691062 prefixEnd_691062 := by exact prefixLift 691062
  have htrace : WordTrace (prefixWord ++ tailWord_691062) baseStart_691062 baseEnd_691062 := by
    simpa [prefixWord, tailWord_691062, baseEnd_691062] using wordTrace_append hprefix tailTrace_691062
  have hstable : (prefixWord ++ tailWord_691062).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691062).length < 2 ^ (prefixWord ++ tailWord_691062).sum := by decide
  have hdescent : baseEnd_691062 < baseStart_691062 := by decide
  rcases family_descends (prefixWord ++ tailWord_691062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691104 : List Nat := [2, 1, 1, 4, 1, 1, 3, 2, 6]
def baseStart_691104 : Nat := 118140960795 + 691104 * 2 ^ 59
def prefixEnd_691104 : Nat := 4983230072969 + 3 ^ 40 * 691104 * 2
def baseEnd_691104 : Nat := 157719348553319682720745

theorem tailTrace_691104 : CollatzResearch.WordTrace tailWord_691104 prefixEnd_691104 157719348553319682720745 := by
  unfold tailWord_691104
  simp only [CollatzResearch.WordTrace]
  refine ⟨12603316844127857005684183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16804422458837142674245577 12603316844127857005684183)
  ·
    refine ⟨18904975266191785508526275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12603316844127857005684183 18904975266191785508526275)
    ·
      refine ⟨28357462899287678262789413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18904975266191785508526275 28357462899287678262789413)
      ·
        refine ⟨5317024293616439674273015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28357462899287678262789413 5317024293616439674273015)
        ·
          refine ⟨7975536440424659511409523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5317024293616439674273015 7975536440424659511409523)
          ·
            refine ⟨11963304660636989267114285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7975536440424659511409523 11963304660636989267114285)
            ·
              refine ⟨4486239247738870975167857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11963304660636989267114285 4486239247738870975167857)
              ·
                refine ⟨3364679435804153231375893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4486239247738870975167857 3364679435804153231375893)
                ·
                  refine ⟨157719348553319682720745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3364679435804153231375893 157719348553319682720745)
                  ·
                    rfl

theorem cell21_691104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 2, 6].length) (baseStart_691104 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_691104 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_691104 prefixEnd_691104 := by exact prefixLift 691104
  have htrace : WordTrace (prefixWord ++ tailWord_691104) baseStart_691104 baseEnd_691104 := by
    simpa [prefixWord, tailWord_691104, baseEnd_691104] using wordTrace_append hprefix tailTrace_691104
  have hstable : (prefixWord ++ tailWord_691104).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691104).length < 2 ^ (prefixWord ++ tailWord_691104).sum := by decide
  have hdescent : baseEnd_691104 < baseStart_691104 := by decide
  rcases family_descends (prefixWord ++ tailWord_691104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691107 : List Nat := [1, 1, 1, 4, 1, 2, 5, 3, 3]
def baseStart_691107 : Nat := 118140960795 + 691107 * 2 ^ 59
def prefixEnd_691107 : Nat := 4983230072969 + 3 ^ 40 * 691107 * 2
def baseEnd_691107 : Nat := 157720033194192344170739

theorem tailTrace_691107 : CollatzResearch.WordTrace tailWord_691107 prefixEnd_691107 157720033194192344170739 := by
  unfold tailWord_691107
  simp only [CollatzResearch.WordTrace]
  refine ⟨25206743107244845523727575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16804495404829897015818383 25206743107244845523727575)
  ·
    refine ⟨37810114660867268285591363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25206743107244845523727575 37810114660867268285591363)
    ·
      refine ⟨56715171991300902428387045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37810114660867268285591363 56715171991300902428387045)
      ·
        refine ⟨10634094748368919205322571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56715171991300902428387045 10634094748368919205322571)
        ·
          refine ⟨15951142122553378807983857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10634094748368919205322571 15951142122553378807983857)
          ·
            refine ⟨11963356591915034105987893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15951142122553378807983857 11963356591915034105987893)
            ·
              refine ⟨1121564680492034447436365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11963356591915034105987893 1121564680492034447436365)
              ·
                refine ⟨420586755184512917788637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1121564680492034447436365 420586755184512917788637)
                ·
                  refine ⟨157720033194192344170739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 420586755184512917788637 157720033194192344170739)
                  ·
                    rfl

theorem cell21_691107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 5, 3, 3].length) (baseStart_691107 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_691107 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_691107 prefixEnd_691107 := by exact prefixLift 691107
  have htrace : WordTrace (prefixWord ++ tailWord_691107) baseStart_691107 baseEnd_691107 := by
    simpa [prefixWord, tailWord_691107, baseEnd_691107] using wordTrace_append hprefix tailTrace_691107
  have hstable : (prefixWord ++ tailWord_691107).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691107).length < 2 ^ (prefixWord ++ tailWord_691107).sum := by decide
  have hdescent : baseEnd_691107 < baseStart_691107 := by decide
  rcases family_descends (prefixWord ++ tailWord_691107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
