import V185TrunkScan22Chunk460

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_4107850 : List Nat := [3, 1, 2, 1, 1, 3, 2, 1, 4, 4]
def baseStart_4107850 : Nat := 118140960795 + 4107850 * 2 ^ 59
def prefixEnd_4107850 : Nat := 4983230072969 + 3 ^ 40 * 4107850 * 2
def baseEnd_4107850 : Nat := 1406201004381238834455565

theorem tailTrace_4107850 : CollatzResearch.WordTrace tailWord_4107850 prefixEnd_4107850 1406201004381238834455565 := by
  unfold tailWord_4107850
  simp only [CollatzResearch.WordTrace]
  refine ⟨37456399541992122442668251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99883732111978993180448669 37456399541992122442668251)
  ·
    refine ⟨56184599312988183664002377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37456399541992122442668251 56184599312988183664002377)
    ·
      refine ⟨42138449484741137748001783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56184599312988183664002377 42138449484741137748001783)
      ·
        refine ⟨63207674227111706622002675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42138449484741137748001783 63207674227111706622002675)
        ·
          refine ⟨94811511340667559933004013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63207674227111706622002675 94811511340667559933004013)
          ·
            refine ⟨35554316752750334974876505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94811511340667559933004013 35554316752750334974876505)
            ·
              refine ⟨26665737564562751231157379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35554316752750334974876505 26665737564562751231157379)
              ·
                refine ⟨39998606346844126846736069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26665737564562751231157379 39998606346844126846736069)
                ·
                  refine ⟨7499738690033273783763013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39998606346844126846736069 7499738690033273783763013)
                  ·
                    refine ⟨1406201004381238834455565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7499738690033273783763013 1406201004381238834455565)
                    ·
                      rfl

theorem cell22_4107850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 1, 4, 4].length) (baseStart_4107850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4107850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4107850 prefixEnd_4107850 := by exact prefixLift 4107850
  have htrace : WordTrace (prefixWord ++ tailWord_4107850) baseStart_4107850 baseEnd_4107850 := by
    simpa [prefixWord, tailWord_4107850, baseEnd_4107850] using wordTrace_append hprefix tailTrace_4107850
  have hstable : (prefixWord ++ tailWord_4107850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4107850).length < 2 ^ (prefixWord ++ tailWord_4107850).sum := by decide
  have hdescent : baseEnd_4107850 < baseStart_4107850 := by decide
  rcases family_descends (prefixWord ++ tailWord_4107850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4107852 : List Nat := [2, 2, 1, 3, 1, 4, 1, 1, 4, 3]
def baseStart_4107852 : Nat := 118140960795 + 4107852 * 2 ^ 59
def prefixEnd_4107852 : Nat := 4983230072969 + 3 ^ 40 * 4107852 * 2
def baseEnd_4107852 : Nat := 1406201689022111495905559

theorem tailTrace_4107852 : CollatzResearch.WordTrace tailWord_4107852 prefixEnd_4107852 1406201689022111495905559 := by
  unfold tailWord_4107852
  simp only [CollatzResearch.WordTrace]
  refine ⟨74912835556980622056122905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99883780742640829408163873 74912835556980622056122905)
  ·
    refine ⟨56184626667735466542092179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74912835556980622056122905 56184626667735466542092179)
    ·
      refine ⟨84276940001603199813138269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56184626667735466542092179 84276940001603199813138269)
      ·
        refine ⟨31603852500601199929926851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84276940001603199813138269 31603852500601199929926851)
        ·
          refine ⟨47405778750901799894890277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31603852500601199929926851 47405778750901799894890277)
          ·
            refine ⟨8888583515794087480291927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47405778750901799894890277 8888583515794087480291927)
            ·
              refine ⟨13332875273691131220437891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8888583515794087480291927 13332875273691131220437891)
              ·
                refine ⟨19999312910536696830656837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13332875273691131220437891 19999312910536696830656837)
                ·
                  refine ⟨3749871170725630655748157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19999312910536696830656837 3749871170725630655748157)
                  ·
                    refine ⟨1406201689022111495905559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3749871170725630655748157 1406201689022111495905559)
                    ·
                      rfl

theorem cell22_4107852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 1, 4, 3].length) (baseStart_4107852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4107852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4107852 prefixEnd_4107852 := by exact prefixLift 4107852
  have htrace : WordTrace (prefixWord ++ tailWord_4107852) baseStart_4107852 baseEnd_4107852 := by
    simpa [prefixWord, tailWord_4107852, baseEnd_4107852] using wordTrace_append hprefix tailTrace_4107852
  have hstable : (prefixWord ++ tailWord_4107852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4107852).length < 2 ^ (prefixWord ++ tailWord_4107852).sum := by decide
  have hdescent : baseEnd_4107852 < baseStart_4107852 := by decide
  rcases family_descends (prefixWord ++ tailWord_4107852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4107882 : List Nat := [3, 1, 3, 2, 1, 2, 4, 6]
def baseStart_4107882 : Nat := 118140960795 + 4107882 * 2 ^ 59
def prefixEnd_4107882 : Nat := 4983230072969 + 3 ^ 40 * 4107882 * 2
def baseEnd_4107882 : Nat := 156245773181689046406163

theorem tailTrace_4107882 : CollatzResearch.WordTrace tailWord_4107882 prefixEnd_4107882 156245773181689046406163 := by
  unfold tailWord_4107882
  simp only [CollatzResearch.WordTrace]
  refine ⟨37456691325963139808959475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99884510202568372823891933 37456691325963139808959475)
  ·
    refine ⟨56185036988944709713439213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37456691325963139808959475 56185036988944709713439213)
    ·
      refine ⟨21069388870854266142539705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56185036988944709713439213 21069388870854266142539705)
      ·
        refine ⟨15802041653140699606904779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21069388870854266142539705 15802041653140699606904779)
        ·
          refine ⟨23703062479711049410357169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15802041653140699606904779 23703062479711049410357169)
          ·
            refine ⟨17777296859783287057767877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23703062479711049410357169 17777296859783287057767877)
            ·
              refine ⟨3333243161209366323331477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17777296859783287057767877 3333243161209366323331477)
              ·
                refine ⟨156245773181689046406163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3333243161209366323331477 156245773181689046406163)
                ·
                  rfl

theorem cell22_4107882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 4, 6].length) (baseStart_4107882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4107882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4107882 prefixEnd_4107882 := by exact prefixLift 4107882
  have htrace : WordTrace (prefixWord ++ tailWord_4107882) baseStart_4107882 baseEnd_4107882 := by
    simpa [prefixWord, tailWord_4107882, baseEnd_4107882] using wordTrace_append hprefix tailTrace_4107882
  have hstable : (prefixWord ++ tailWord_4107882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4107882).length < 2 ^ (prefixWord ++ tailWord_4107882).sum := by decide
  have hdescent : baseEnd_4107882 < baseStart_4107882 := by decide
  rcases family_descends (prefixWord ++ tailWord_4107882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4107914 : List Nat := [3, 1, 2, 3, 2, 1, 3, 1, 3, 3]
def baseStart_4107914 : Nat := 118140960795 + 4107914 * 2 ^ 59
def prefixEnd_4107914 : Nat := 4983230072969 + 3 ^ 40 * 4107914 * 2
def baseEnd_4107914 : Nat := 1406222912889164000855369

theorem tailTrace_4107914 : CollatzResearch.WordTrace tailWord_4107914 prefixEnd_4107914 1406222912889164000855369 := by
  unfold tailWord_4107914
  simp only [CollatzResearch.WordTrace]
  refine ⟨37456983109934157175250699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99885288293157752467335197 37456983109934157175250699)
  ·
    refine ⟨56185474664901235762876049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37456983109934157175250699 56185474664901235762876049)
    ·
      refine ⟨42139105998675926822157037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56185474664901235762876049 42139105998675926822157037)
      ·
        refine ⟨15802164749503472558308889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42139105998675926822157037 15802164749503472558308889)
        ·
          refine ⟨11851623562127604418731667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15802164749503472558308889 11851623562127604418731667)
          ·
            refine ⟨17777435343191406628097501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11851623562127604418731667 17777435343191406628097501)
            ·
              refine ⟨6666538253696777485536563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17777435343191406628097501 6666538253696777485536563)
              ·
                refine ⟨9999807380545166228304845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6666538253696777485536563 9999807380545166228304845)
                ·
                  refine ⟨3749927767704437335614317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9999807380545166228304845 3749927767704437335614317)
                  ·
                    refine ⟨1406222912889164000855369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3749927767704437335614317 1406222912889164000855369)
                    ·
                      rfl

theorem cell22_4107914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 3, 1, 3, 3].length) (baseStart_4107914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4107914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4107914 prefixEnd_4107914 := by exact prefixLift 4107914
  have htrace : WordTrace (prefixWord ++ tailWord_4107914) baseStart_4107914 baseEnd_4107914 := by
    simpa [prefixWord, tailWord_4107914, baseEnd_4107914] using wordTrace_append hprefix tailTrace_4107914
  have hstable : (prefixWord ++ tailWord_4107914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4107914).length < 2 ^ (prefixWord ++ tailWord_4107914).sum := by decide
  have hdescent : baseEnd_4107914 < baseStart_4107914 := by decide
  rcases family_descends (prefixWord ++ tailWord_4107914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4107925 : List Nat := [1, 3, 2, 1, 1, 1, 1, 5, 2, 5]
def baseStart_4107925 : Nat := 118140960795 + 4107925 * 2 ^ 59
def prefixEnd_4107925 : Nat := 4983230072969 + 3 ^ 40 * 4107925 * 2
def baseEnd_4107925 : Nat := 1406226678413963638830335

theorem tailTrace_4107925 : CollatzResearch.WordTrace tailWord_4107925 prefixEnd_4107925 1406226678413963638830335 := by
  unfold tailWord_4107925
  simp only [CollatzResearch.WordTrace]
  refine ⟨149828333642696777579653229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99885555761797851719768819 149828333642696777579653229)
  ·
    refine ⟨56185625116011291592369961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149828333642696777579653229 56185625116011291592369961)
    ·
      refine ⟨42139218837008468694277471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56185625116011291592369961 42139218837008468694277471)
      ·
        refine ⟨63208828255512703041416207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42139218837008468694277471 63208828255512703041416207)
        ·
          refine ⟨94813242383269054562124311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63208828255512703041416207 94813242383269054562124311)
          ·
            refine ⟨142219863574903581843186467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94813242383269054562124311 142219863574903581843186467)
            ·
              refine ⟨213329795362355372764779701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142219863574903581843186467 213329795362355372764779701)
              ·
                refine ⟨19999668315220816196698097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 213329795362355372764779701 19999668315220816196698097)
                ·
                  refine ⟨14999751236415612147523573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19999668315220816196698097 14999751236415612147523573)
                  ·
                    refine ⟨1406226678413963638830335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14999751236415612147523573 1406226678413963638830335)
                    ·
                      rfl

theorem cell22_4107925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 5, 2, 5].length) (baseStart_4107925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4107925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4107925 prefixEnd_4107925 := by exact prefixLift 4107925
  have htrace : WordTrace (prefixWord ++ tailWord_4107925) baseStart_4107925 baseEnd_4107925 := by
    simpa [prefixWord, tailWord_4107925, baseEnd_4107925] using wordTrace_append hprefix tailTrace_4107925
  have hstable : (prefixWord ++ tailWord_4107925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4107925).length < 2 ^ (prefixWord ++ tailWord_4107925).sum := by decide
  have hdescent : baseEnd_4107925 < baseStart_4107925 := by decide
  rcases family_descends (prefixWord ++ tailWord_4107925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4107927 : List Nat := [1, 1, 3, 3, 2, 3, 1, 3, 5]
def baseStart_4107927 : Nat := 118140960795 + 4107927 * 2 ^ 59
def prefixEnd_4107927 : Nat := 4983230072969 + 3 ^ 40 * 4107927 * 2
def baseEnd_4107927 : Nat := 468742454351612100093443

theorem tailTrace_4107927 : CollatzResearch.WordTrace tailWord_4107927 prefixEnd_4107927 468742454351612100093443 := by
  unfold tailWord_4107927
  simp only [CollatzResearch.WordTrace]
  refine ⟨149828406588689531921226035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99885604392459687947484023 149828406588689531921226035)
  ·
    refine ⟨224742609883034297881839053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149828406588689531921226035 224742609883034297881839053)
    ·
      refine ⟨84278478706137861705689645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224742609883034297881839053 84278478706137861705689645)
      ·
        refine ⟨31604429514801698139633617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84278478706137861705689645 31604429514801698139633617)
        ·
          refine ⟨23703322136101273604725213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31604429514801698139633617 23703322136101273604725213)
          ·
            refine ⟨8888745801037977601771955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23703322136101273604725213 8888745801037977601771955)
            ·
              refine ⟨13333118701556966402657933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8888745801037977601771955 13333118701556966402657933)
              ·
                refine ⟨4999919513083862400996725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13333118701556966402657933 4999919513083862400996725)
                ·
                  refine ⟨468742454351612100093443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4999919513083862400996725 468742454351612100093443)
                  ·
                    rfl

theorem cell22_4107927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 3, 5].length) (baseStart_4107927 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4107927 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4107927 prefixEnd_4107927 := by exact prefixLift 4107927
  have htrace : WordTrace (prefixWord ++ tailWord_4107927) baseStart_4107927 baseEnd_4107927 := by
    simpa [prefixWord, tailWord_4107927, baseEnd_4107927] using wordTrace_append hprefix tailTrace_4107927
  have hstable : (prefixWord ++ tailWord_4107927).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4107927).length < 2 ^ (prefixWord ++ tailWord_4107927).sum := by decide
  have hdescent : baseEnd_4107927 < baseStart_4107927 := by decide
  rcases family_descends (prefixWord ++ tailWord_4107927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4107972 : List Nat := [2, 3, 3, 1, 1, 1, 2, 3, 6]
def baseStart_4107972 : Nat := 118140960795 + 4107972 * 2 ^ 59
def prefixEnd_4107972 : Nat := 4983230072969 + 3 ^ 40 * 4107972 * 2
def baseEnd_4107972 : Nat := 468747589158157060968397

theorem tailTrace_4107972 : CollatzResearch.WordTrace tailWord_4107972 prefixEnd_4107972 468747589158157060968397 := by
  unfold tailWord_4107972
  simp only [CollatzResearch.WordTrace]
  refine ⟨74915023936763252303307085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99886698582351003071076113 74915023936763252303307085)
  ·
    refine ⟨28093133976286219613740157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74915023936763252303307085 28093133976286219613740157)
    ·
      refine ⟨10534925241107332355152559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28093133976286219613740157 10534925241107332355152559)
      ·
        refine ⟨15802387861660998532728839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10534925241107332355152559 15802387861660998532728839)
        ·
          refine ⟨23703581792491497799093259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15802387861660998532728839 23703581792491497799093259)
          ·
            refine ⟨35555372688737246698639889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23703581792491497799093259 35555372688737246698639889)
            ·
              refine ⟨26666529516552935023979917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35555372688737246698639889 26666529516552935023979917)
              ·
                refine ⟨9999948568707350633992469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26666529516552935023979917 9999948568707350633992469)
                ·
                  refine ⟨468747589158157060968397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9999948568707350633992469 468747589158157060968397)
                  ·
                    rfl

theorem cell22_4107972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 3, 6].length) (baseStart_4107972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4107972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4107972 prefixEnd_4107972 := by exact prefixLift 4107972
  have htrace : WordTrace (prefixWord ++ tailWord_4107972) baseStart_4107972 baseEnd_4107972 := by
    simpa [prefixWord, tailWord_4107972, baseEnd_4107972] using wordTrace_append hprefix tailTrace_4107972
  have hstable : (prefixWord ++ tailWord_4107972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4107972).length < 2 ^ (prefixWord ++ tailWord_4107972).sum := by decide
  have hdescent : baseEnd_4107972 < baseStart_4107972 := by decide
  rcases family_descends (prefixWord ++ tailWord_4107972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4108000 : List Nat := [2, 1, 1, 3, 1, 2, 2, 10]
def baseStart_4108000 : Nat := 118140960795 + 4108000 * 2 ^ 59
def prefixEnd_4108000 : Nat := 4983230072969 + 3 ^ 40 * 4108000 * 2
def baseEnd_4108000 : Nat := 156250261382965382578345

theorem tailTrace_4108000 : CollatzResearch.WordTrace tailWord_4108000 prefixEnd_4108000 156250261382965382578345 := by
  unfold tailWord_4108000
  simp only [CollatzResearch.WordTrace]
  refine ⟨74915534558712532694316727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99887379411616710259088969 74915534558712532694316727)
  ·
    refine ⟨112373301838068799041475091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74915534558712532694316727 112373301838068799041475091)
    ·
      refine ⟨168559952757103198562212637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112373301838068799041475091 168559952757103198562212637)
      ·
        refine ⟨63209982283913699460829739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168559952757103198562212637 63209982283913699460829739)
        ·
          refine ⟨94814973425870549191244609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63209982283913699460829739 94814973425870549191244609)
          ·
            refine ⟨71111230069402911893433457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94814973425870549191244609 71111230069402911893433457)
            ·
              refine ⟨53333422552052183920075093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71111230069402911893433457 53333422552052183920075093)
              ·
                refine ⟨156250261382965382578345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 53333422552052183920075093 156250261382965382578345)
                ·
                  rfl

theorem cell22_4108000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 10].length) (baseStart_4108000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4108000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4108000 prefixEnd_4108000 := by exact prefixLift 4108000
  have htrace : WordTrace (prefixWord ++ tailWord_4108000) baseStart_4108000 baseEnd_4108000 := by
    simpa [prefixWord, tailWord_4108000, baseEnd_4108000] using wordTrace_append hprefix tailTrace_4108000
  have hstable : (prefixWord ++ tailWord_4108000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4108000).length < 2 ^ (prefixWord ++ tailWord_4108000).sum := by decide
  have hdescent : baseEnd_4108000 < baseStart_4108000 := by decide
  rcases family_descends (prefixWord ++ tailWord_4108000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4108032 : List Nat := [2, 1, 1, 2, 1, 1, 2, 2, 7, 3]
def baseStart_4108032 : Nat := 118140960795 + 4108032 * 2 ^ 59
def prefixEnd_4108032 : Nat := 4983230072969 + 3 ^ 40 * 4108032 * 2
def baseEnd_4108032 : Nat := 1406263306700651026405007

theorem tailTrace_4108032 : CollatzResearch.WordTrace tailWord_4108032 prefixEnd_4108032 1406263306700651026405007 := by
  unfold tailWord_4108032
  simp only [CollatzResearch.WordTrace]
  refine ⟨74916118126654567426899175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99888157502206089902532233 74916118126654567426899175)
  ·
    refine ⟨112374177189981851140348763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74916118126654567426899175 112374177189981851140348763)
    ·
      refine ⟨168561265784972776710523145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112374177189981851140348763 168561265784972776710523145)
      ·
        refine ⟨126420949338729582532892359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168561265784972776710523145 126420949338729582532892359)
        ·
          refine ⟨189631424008094373799338539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126420949338729582532892359 189631424008094373799338539)
          ·
            refine ⟨284447136012141560699007809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189631424008094373799338539 284447136012141560699007809)
            ·
              refine ⟨213335352009106170524255857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 284447136012141560699007809 213335352009106170524255857)
              ·
                refine ⟨160001514006829627893191893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 213335352009106170524255857 160001514006829627893191893)
                ·
                  refine ⟨3750035484535069403746685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 160001514006829627893191893 3750035484535069403746685)
                  ·
                    refine ⟨1406263306700651026405007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3750035484535069403746685 1406263306700651026405007)
                    ·
                      rfl

theorem cell22_4108032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 7, 3].length) (baseStart_4108032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4108032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4108032 prefixEnd_4108032 := by exact prefixLift 4108032
  have htrace : WordTrace (prefixWord ++ tailWord_4108032) baseStart_4108032 baseEnd_4108032 := by
    simpa [prefixWord, tailWord_4108032, baseEnd_4108032] using wordTrace_append hprefix tailTrace_4108032
  have hstable : (prefixWord ++ tailWord_4108032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4108032).length < 2 ^ (prefixWord ++ tailWord_4108032).sum := by decide
  have hdescent : baseEnd_4108032 < baseStart_4108032 := by decide
  rcases family_descends (prefixWord ++ tailWord_4108032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4108083 : List Nat := [1, 1, 1, 2, 8, 1, 1, 1, 3, 3]
def baseStart_4108083 : Nat := 118140960795 + 4108083 * 2 ^ 59
def prefixEnd_4108083 : Nat := 4983230072969 + 3 ^ 40 * 4108083 * 2
def baseEnd_4108083 : Nat := 1406280765042903893379851

theorem tailTrace_4108083 : CollatzResearch.WordTrace tailWord_4108083 prefixEnd_4108083 1406280765042903893379851 := by
  unfold tailWord_4108083
  simp only [CollatzResearch.WordTrace]
  refine ⟨149834096376124370563904903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99889397584082913709269935 149834096376124370563904903)
  ·
    refine ⟨224751144564186555845857355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149834096376124370563904903 224751144564186555845857355)
    ·
      refine ⟨337126716846279833768786033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224751144564186555845857355 337126716846279833768786033)
      ·
        refine ⟨252845037634709875326589525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 337126716846279833768786033 252845037634709875326589525)
        ·
          refine ⟨2963027784781756351483471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 252845037634709875326589525 2963027784781756351483471)
          ·
            refine ⟨4444541677172634527225207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2963027784781756351483471 4444541677172634527225207)
            ·
              refine ⟨6666812515758951790837811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4444541677172634527225207 6666812515758951790837811)
              ·
                refine ⟨10000218773638427686256717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6666812515758951790837811 10000218773638427686256717)
                ·
                  refine ⟨3750082040114410382346269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10000218773638427686256717 3750082040114410382346269)
                  ·
                    refine ⟨1406280765042903893379851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3750082040114410382346269 1406280765042903893379851)
                    ·
                      rfl

theorem cell22_4108083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 1, 1, 3, 3].length) (baseStart_4108083 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4108083 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4108083 prefixEnd_4108083 := by exact prefixLift 4108083
  have htrace : WordTrace (prefixWord ++ tailWord_4108083) baseStart_4108083 baseEnd_4108083 := by
    simpa [prefixWord, tailWord_4108083, baseEnd_4108083] using wordTrace_append hprefix tailTrace_4108083
  have hstable : (prefixWord ++ tailWord_4108083).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4108083).length < 2 ^ (prefixWord ++ tailWord_4108083).sum := by decide
  have hdescent : baseEnd_4108083 < baseStart_4108083 := by decide
  rcases family_descends (prefixWord ++ tailWord_4108083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4108169 : List Nat := [1, 2, 1, 1, 5, 1, 5, 6]
def baseStart_4108169 : Nat := 118140960795 + 4108169 * 2 ^ 59
def prefixEnd_4108169 : Nat := 4983230072969 + 3 ^ 40 * 4108169 * 2
def baseEnd_4108169 : Nat := 156256689400047592858843

theorem tailTrace_4108169 : CollatzResearch.WordTrace tailWord_4108169 prefixEnd_4108169 156256689400047592858843 := by
  unfold tailWord_4108169
  simp only [CollatzResearch.WordTrace]
  refine ⟨149837233053812807251535561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99891488702541871501023707 149837233053812807251535561)
  ·
    refine ⟨112377924790359605438651671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149837233053812807251535561 112377924790359605438651671)
    ·
      refine ⟨168566887185539408157977507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112377924790359605438651671 168566887185539408157977507)
      ·
        refine ⟨252850330778309112236966261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168566887185539408157977507 252850330778309112236966261)
        ·
          refine ⟨23704718510466479272215587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 252850330778309112236966261 23704718510466479272215587)
          ·
            refine ⟨35557077765699718908323381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23704718510466479272215587 35557077765699718908323381)
            ·
              refine ⟨3333476040534348647655317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35557077765699718908323381 3333476040534348647655317)
              ·
                refine ⟨156256689400047592858843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3333476040534348647655317 156256689400047592858843)
                ·
                  rfl

theorem cell22_4108169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 5, 6].length) (baseStart_4108169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4108169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4108169 prefixEnd_4108169 := by exact prefixLift 4108169
  have htrace : WordTrace (prefixWord ++ tailWord_4108169) baseStart_4108169 baseEnd_4108169 := by
    simpa [prefixWord, tailWord_4108169, baseEnd_4108169] using wordTrace_append hprefix tailTrace_4108169
  have hstable : (prefixWord ++ tailWord_4108169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4108169).length < 2 ^ (prefixWord ++ tailWord_4108169).sum := by decide
  have hdescent : baseEnd_4108169 < baseStart_4108169 := by decide
  rcases family_descends (prefixWord ++ tailWord_4108169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4108190 : List Nat := [4, 3, 1, 3, 1, 1, 1, 1, 4, 3]
def baseStart_4108190 : Nat := 118140960795 + 4108190 * 2 ^ 59
def prefixEnd_4108190 : Nat := 4983230072969 + 3 ^ 40 * 4108190 * 2
def baseEnd_4108190 : Nat := 1406317393329591280954523

theorem tailTrace_4108190 : CollatzResearch.WordTrace tailWord_4108190 prefixEnd_4108190 1406317393329591280954523 := by
  unfold tailWord_4108190
  simp only [CollatzResearch.WordTrace]
  refine ⟨18729749873342090979756253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99891999324491151892033349 18729749873342090979756253)
  ·
    refine ⟨7023656202503284117408595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18729749873342090979756253 7023656202503284117408595)
    ·
      refine ⟨10535484303754926176112893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7023656202503284117408595 10535484303754926176112893)
      ·
        refine ⟨3950806613908097316042335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10535484303754926176112893 3950806613908097316042335)
        ·
          refine ⟨5926209920862145974063503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3950806613908097316042335 5926209920862145974063503)
          ·
            refine ⟨8889314881293218961095255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5926209920862145974063503 8889314881293218961095255)
            ·
              refine ⟨13333972321939828441642883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8889314881293218961095255 13333972321939828441642883)
              ·
                refine ⟨20000958482909742662464325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13333972321939828441642883 20000958482909742662464325)
                ·
                  refine ⟨3750179715545576749212061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20000958482909742662464325 3750179715545576749212061)
                  ·
                    refine ⟨1406317393329591280954523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3750179715545576749212061 1406317393329591280954523)
                    ·
                      rfl

theorem cell22_4108190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 1, 4, 3].length) (baseStart_4108190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4108190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4108190 prefixEnd_4108190 := by exact prefixLift 4108190
  have htrace : WordTrace (prefixWord ++ tailWord_4108190) baseStart_4108190 baseEnd_4108190 := by
    simpa [prefixWord, tailWord_4108190, baseEnd_4108190] using wordTrace_append hprefix tailTrace_4108190
  have hstable : (prefixWord ++ tailWord_4108190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4108190).length < 2 ^ (prefixWord ++ tailWord_4108190).sum := by decide
  have hdescent : baseEnd_4108190 < baseStart_4108190 := by decide
  rcases family_descends (prefixWord ++ tailWord_4108190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4108220 : List Nat := [2, 2, 2, 5, 2, 1, 2, 6]
def baseStart_4108220 : Nat := 118140960795 + 4108220 * 2 ^ 59
def prefixEnd_4108220 : Nat := 4983230072969 + 3 ^ 40 * 4108220 * 2
def baseEnd_4108220 : Nat := 156258629215853466967159

theorem tailTrace_4108220 : CollatzResearch.WordTrace tailWord_4108220 prefixEnd_4108220 156258629215853466967159 := by
  unfold tailWord_4108220
  simp only [CollatzResearch.WordTrace]
  refine ⟨74919546588314021480821057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99892728784418695307761409 74919546588314021480821057)
  ·
    refine ⟨56189659941235516110615793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74919546588314021480821057 56189659941235516110615793)
    ·
      refine ⟨42142244955926637082961845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56189659941235516110615793 42142244955926637082961845)
      ·
        refine ⟨3950835464618122226527673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 42142244955926637082961845 3950835464618122226527673)
        ·
          refine ⟨2963126598463591669895755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3950835464618122226527673 2963126598463591669895755)
          ·
            refine ⟨4444689897695387504843633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2963126598463591669895755 4444689897695387504843633)
            ·
              refine ⟨3333517423271540628632725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4444689897695387504843633 3333517423271540628632725)
              ·
                refine ⟨156258629215853466967159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3333517423271540628632725 156258629215853466967159)
                ·
                  rfl

theorem cell22_4108220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 2, 6].length) (baseStart_4108220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4108220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4108220 prefixEnd_4108220 := by exact prefixLift 4108220
  have htrace : WordTrace (prefixWord ++ tailWord_4108220) baseStart_4108220 baseEnd_4108220 := by
    simpa [prefixWord, tailWord_4108220, baseEnd_4108220] using wordTrace_append hprefix tailTrace_4108220
  have hstable : (prefixWord ++ tailWord_4108220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4108220).length < 2 ^ (prefixWord ++ tailWord_4108220).sum := by decide
  have hdescent : baseEnd_4108220 < baseStart_4108220 := by decide
  rcases family_descends (prefixWord ++ tailWord_4108220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4108278 : List Nat := [5, 1, 1, 1, 4, 1, 1, 1, 3, 4]
def baseStart_4108278 : Nat := 118140960795 + 4108278 * 2 ^ 59
def prefixEnd_4108278 : Nat := 4983230072969 + 3 ^ 40 * 4108278 * 2
def baseEnd_4108278 : Nat := 1406347517527988384754253

theorem tailTrace_4108278 : CollatzResearch.WordTrace tailWord_4108278 prefixEnd_4108278 1406347517527988384754253 := by
  unfold tailWord_4108278
  simp only [CollatzResearch.WordTrace]
  refine ⟨9365075538151119929203343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 99894139073611945911502325 9365075538151119929203343)
  ·
    refine ⟨14047613307226679893805015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9365075538151119929203343 14047613307226679893805015)
    ·
      refine ⟨21071419960840019840707523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14047613307226679893805015 21071419960840019840707523)
      ·
        refine ⟨31607129941260029761061285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21071419960840019840707523 31607129941260029761061285)
        ·
          refine ⟨5926336863986255580198991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31607129941260029761061285 5926336863986255580198991)
          ·
            refine ⟨8889505295979383370298487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5926336863986255580198991 8889505295979383370298487)
            ·
              refine ⟨13334257943969075055447731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8889505295979383370298487 13334257943969075055447731)
              ·
                refine ⟨20001386915953612583171597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13334257943969075055447731 20001386915953612583171597)
                ·
                  refine ⟨7500520093482604718689349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20001386915953612583171597 7500520093482604718689349)
                  ·
                    refine ⟨1406347517527988384754253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7500520093482604718689349 1406347517527988384754253)
                    ·
                      rfl

theorem cell22_4108278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 1, 3, 4].length) (baseStart_4108278 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4108278 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4108278 prefixEnd_4108278 := by exact prefixLift 4108278
  have htrace : WordTrace (prefixWord ++ tailWord_4108278) baseStart_4108278 baseEnd_4108278 := by
    simpa [prefixWord, tailWord_4108278, baseEnd_4108278] using wordTrace_append hprefix tailTrace_4108278
  have hstable : (prefixWord ++ tailWord_4108278).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4108278).length < 2 ^ (prefixWord ++ tailWord_4108278).sum := by decide
  have hdescent : baseEnd_4108278 < baseStart_4108278 := by decide
  rcases family_descends (prefixWord ++ tailWord_4108278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4108336 : List Nat := [2, 1, 1, 1, 2, 5, 1, 1, 5, 3]
def baseStart_4108336 : Nat := 118140960795 + 4108336 * 2 ^ 59
def prefixEnd_4108336 : Nat := 4983230072969 + 3 ^ 40 * 4108336 * 2
def baseEnd_4108336 : Nat := 1406367372113295566804075

theorem tailTrace_4108336 : CollatzResearch.WordTrace tailWord_4108336 prefixEnd_4108336 1406367372113295566804075 := by
  unfold tailWord_4108336
  simp only [CollatzResearch.WordTrace]
  refine ⟨74921662022103897386432431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99895549362805196515243241 74921662022103897386432431)
  ·
    refine ⟨112382493033155846079648647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74921662022103897386432431 112382493033155846079648647)
    ·
      refine ⟨168573739549733769119472971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112382493033155846079648647 168573739549733769119472971)
      ·
        refine ⟨252860609324600653679209457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168573739549733769119472971 252860609324600653679209457)
        ·
          refine ⟨189645456993450490259407093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252860609324600653679209457 189645456993450490259407093)
          ·
            refine ⟨17779261593135983461819415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 189645456993450490259407093 17779261593135983461819415)
            ·
              refine ⟨26668892389703975192729123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17779261593135983461819415 26668892389703975192729123)
              ·
                refine ⟨40003338584555962789093685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26668892389703975192729123 40003338584555962789093685)
                ·
                  refine ⟨3750312992302121511477533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40003338584555962789093685 3750312992302121511477533)
                  ·
                    refine ⟨1406367372113295566804075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3750312992302121511477533 1406367372113295566804075)
                    ·
                      rfl

theorem cell22_4108336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 1, 5, 3].length) (baseStart_4108336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4108336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4108336 prefixEnd_4108336 := by exact prefixLift 4108336
  have htrace : WordTrace (prefixWord ++ tailWord_4108336) baseStart_4108336 baseEnd_4108336 := by
    simpa [prefixWord, tailWord_4108336, baseEnd_4108336] using wordTrace_append hprefix tailTrace_4108336
  have hstable : (prefixWord ++ tailWord_4108336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4108336).length < 2 ^ (prefixWord ++ tailWord_4108336).sum := by decide
  have hdescent : baseEnd_4108336 < baseStart_4108336 := by decide
  rcases family_descends (prefixWord ++ tailWord_4108336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4108366 : List Nat := [4, 1, 1, 1, 1, 5, 1, 1, 7]
def baseStart_4108366 : Nat := 118140960795 + 4108366 * 2 ^ 59
def prefixEnd_4108366 : Nat := 4983230072969 + 3 ^ 40 * 4108366 * 2
def baseEnd_4108366 : Nat := 468792547242128496184661

theorem tailTrace_4108366 : CollatzResearch.WordTrace tailWord_4108366 prefixEnd_4108366 468792547242128496184661 := by
  unfold tailWord_4108366
  simp only [CollatzResearch.WordTrace]
  refine ⟨18730552279262388737057119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99896278822732739930971301 18730552279262388737057119)
  ·
    refine ⟨28095828418893583105585679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18730552279262388737057119 28095828418893583105585679)
    ·
      refine ⟨42143742628340374658378519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28095828418893583105585679 42143742628340374658378519)
      ·
        refine ⟨63215613942510561987567779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42143742628340374658378519 63215613942510561987567779)
        ·
          refine ⟨94823420913765842981351669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63215613942510561987567779 94823420913765842981351669)
          ·
            refine ⟨8889695710665547779501719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 94823420913765842981351669 8889695710665547779501719)
            ·
              refine ⟨13334543565998321669252579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8889695710665547779501719 13334543565998321669252579)
              ·
                refine ⟨20001815348997482503878869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13334543565998321669252579 20001815348997482503878869)
                ·
                  refine ⟨468792547242128496184661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20001815348997482503878869 468792547242128496184661)
                  ·
                    rfl

theorem cell22_4108366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 1, 7].length) (baseStart_4108366 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4108366 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4108366 prefixEnd_4108366 := by exact prefixLift 4108366
  have htrace : WordTrace (prefixWord ++ tailWord_4108366) baseStart_4108366 baseEnd_4108366 := by
    simpa [prefixWord, tailWord_4108366, baseEnd_4108366] using wordTrace_append hprefix tailTrace_4108366
  have hstable : (prefixWord ++ tailWord_4108366).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4108366).length < 2 ^ (prefixWord ++ tailWord_4108366).sum := by decide
  have hdescent : baseEnd_4108366 < baseStart_4108366 := by decide
  rcases family_descends (prefixWord ++ tailWord_4108366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4108370 : List Nat := [3, 2, 2, 1, 4, 1, 2, 1, 3, 3]
def baseStart_4108370 : Nat := 118140960795 + 4108370 * 2 ^ 59
def prefixEnd_4108370 : Nat := 4983230072969 + 3 ^ 40 * 4108370 * 2
def baseEnd_4108370 : Nat := 1406379011008130811453971

theorem tailTrace_4108370 : CollatzResearch.WordTrace tailWord_4108370 prefixEnd_4108370 1406379011008130811453971 := by
  unfold tailWord_4108370
  simp only [CollatzResearch.WordTrace]
  refine ⟨37461141031521154644900641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99896376084056412386401709 37461141031521154644900641)
  ·
    refine ⟨28095855773640865983675481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37461141031521154644900641 28095855773640865983675481)
    ·
      refine ⟨21071891830230649487756611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28095855773640865983675481 21071891830230649487756611)
      ·
        refine ⟨31607837745345974231634917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21071891830230649487756611 31607837745345974231634917)
        ·
          refine ⟨5926469577252370168431547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31607837745345974231634917 5926469577252370168431547)
          ·
            refine ⟨8889704365878555252647321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5926469577252370168431547 8889704365878555252647321)
            ·
              refine ⟨6667278274408916439485491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8889704365878555252647321 6667278274408916439485491)
              ·
                refine ⟨10000917411613374659228237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6667278274408916439485491 10000917411613374659228237)
                ·
                  refine ⟨3750344029355015497210589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10000917411613374659228237 3750344029355015497210589)
                  ·
                    refine ⟨1406379011008130811453971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3750344029355015497210589 1406379011008130811453971)
                    ·
                      rfl

theorem cell22_4108370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 2, 1, 3, 3].length) (baseStart_4108370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4108370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4108370 prefixEnd_4108370 := by exact prefixLift 4108370
  have htrace : WordTrace (prefixWord ++ tailWord_4108370) baseStart_4108370 baseEnd_4108370 := by
    simpa [prefixWord, tailWord_4108370, baseEnd_4108370] using wordTrace_append hprefix tailTrace_4108370
  have hstable : (prefixWord ++ tailWord_4108370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4108370).length < 2 ^ (prefixWord ++ tailWord_4108370).sum := by decide
  have hdescent : baseEnd_4108370 < baseStart_4108370 := by decide
  rcases family_descends (prefixWord ++ tailWord_4108370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4108413 : List Nat := [1, 4, 1, 1, 3, 2, 2, 3, 1, 4]
def baseStart_4108413 : Nat := 118140960795 + 4108413 * 2 ^ 59
def prefixEnd_4108413 : Nat := 4983230072969 + 3 ^ 40 * 4108413 * 2
def baseEnd_4108413 : Nat := 1406393730786893032628839

theorem tailTrace_4108413 : CollatzResearch.WordTrace tailWord_4108413 prefixEnd_4108413 1406393730786893032628839 := by
  unfold tailWord_4108413
  simp only [CollatzResearch.WordTrace]
  refine ⟨149846132464928836923417893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99897421643285891282278595 149846132464928836923417893)
  ·
    refine ⟨28096149837174156923140855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149846132464928836923417893 28096149837174156923140855)
    ·
      refine ⟨42144224755761235384711283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28096149837174156923140855 42144224755761235384711283)
      ·
        refine ⟨63216337133641853077066925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42144224755761235384711283 63216337133641853077066925)
        ·
          refine ⟨23706126425115694903900097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63216337133641853077066925 23706126425115694903900097)
          ·
            refine ⟨17779594818836771177925073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23706126425115694903900097 17779594818836771177925073)
            ·
              refine ⟨13334696114127578383443805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17779594818836771177925073 13334696114127578383443805)
              ·
                refine ⟨5000511042797841893791427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13334696114127578383443805 5000511042797841893791427)
                ·
                  refine ⟨7500766564196762840687141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5000511042797841893791427 7500766564196762840687141)
                  ·
                    refine ⟨1406393730786893032628839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7500766564196762840687141 1406393730786893032628839)
                    ·
                      rfl

theorem cell22_4108413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 3, 1, 4].length) (baseStart_4108413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4108413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4108413 prefixEnd_4108413 := by exact prefixLift 4108413
  have htrace : WordTrace (prefixWord ++ tailWord_4108413) baseStart_4108413 baseEnd_4108413 := by
    simpa [prefixWord, tailWord_4108413, baseEnd_4108413] using wordTrace_append hprefix tailTrace_4108413
  have hstable : (prefixWord ++ tailWord_4108413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4108413).length < 2 ^ (prefixWord ++ tailWord_4108413).sum := by decide
  have hdescent : baseEnd_4108413 < baseStart_4108413 := by decide
  rcases family_descends (prefixWord ++ tailWord_4108413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4108488 : List Nat := [2, 1, 3, 1, 2, 1, 1, 5, 3, 3]
def baseStart_4108488 : Nat := 118140960795 + 4108488 * 2 ^ 59
def prefixEnd_4108488 : Nat := 4983230072969 + 3 ^ 40 * 4108488 * 2
def baseEnd_4108488 : Nat := 1406419404819617837003609

theorem tailTrace_4108488 : CollatzResearch.WordTrace tailWord_4108488 prefixEnd_4108488 1406419404819617837003609 := by
  unfold tailWord_4108488
  simp only [CollatzResearch.WordTrace]
  refine ⟨74924433969828562366199059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99899245293104749821598745 74924433969828562366199059)
  ·
    refine ⟨112386650954742843549298589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74924433969828562366199059 112386650954742843549298589)
    ·
      refine ⟨42144994108028566330986971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112386650954742843549298589 42144994108028566330986971)
      ·
        refine ⟨63217491162042849496480457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42144994108028566330986971 63217491162042849496480457)
        ·
          refine ⟨47413118371532137122360343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63217491162042849496480457 47413118371532137122360343)
          ·
            refine ⟨71119677557298205683540515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47413118371532137122360343 71119677557298205683540515)
            ·
              refine ⟨106679516335947308525310773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71119677557298205683540515 106679516335947308525310773)
              ·
                refine ⟨10001204656495060174247885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 106679516335947308525310773 10001204656495060174247885)
                ·
                  refine ⟨3750451746185647565342957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10001204656495060174247885 3750451746185647565342957)
                  ·
                    refine ⟨1406419404819617837003609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3750451746185647565342957 1406419404819617837003609)
                    ·
                      rfl

theorem cell22_4108488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 5, 3, 3].length) (baseStart_4108488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4108488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4108488 prefixEnd_4108488 := by exact prefixLift 4108488
  have htrace : WordTrace (prefixWord ++ tailWord_4108488) baseStart_4108488 baseEnd_4108488 := by
    simpa [prefixWord, tailWord_4108488, baseEnd_4108488] using wordTrace_append hprefix tailTrace_4108488
  have hstable : (prefixWord ++ tailWord_4108488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4108488).length < 2 ^ (prefixWord ++ tailWord_4108488).sum := by decide
  have hdescent : baseEnd_4108488 < baseStart_4108488 := by decide
  rcases family_descends (prefixWord ++ tailWord_4108488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4108516 : List Nat := [2, 3, 1, 1, 1, 2, 1, 1, 3, 7]
def baseStart_4108516 : Nat := 118140960795 + 4108516 * 2 ^ 59
def prefixEnd_4108516 : Nat := 4983230072969 + 3 ^ 40 * 4108516 * 2
def baseEnd_4108516 : Nat := 1406428989791835097303523

theorem tailTrace_4108516 : CollatzResearch.WordTrace tailWord_4108516 prefixEnd_4108516 1406428989791835097303523 := by
  unfold tailWord_4108516
  simp only [CollatzResearch.WordTrace]
  refine ⟨74924944591777842757208701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99899926122370457009611601 74924944591777842757208701)
  ·
    refine ⟨28096854221916691033953263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74924944591777842757208701 28096854221916691033953263)
    ·
      refine ⟨42145281332875036550929895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28096854221916691033953263 42145281332875036550929895)
      ·
        refine ⟨63217921999312554826394843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42145281332875036550929895 63217921999312554826394843)
        ·
          refine ⟨94826882998968832239592265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63217921999312554826394843 94826882998968832239592265)
          ·
            refine ⟨71120162249226624179694199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94826882998968832239592265 71120162249226624179694199)
            ·
              refine ⟨106680243373839936269541299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71120162249226624179694199 106680243373839936269541299)
              ·
                refine ⟨160020365060759904404311949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106680243373839936269541299 160020365060759904404311949)
                ·
                  refine ⟨60007636897784964151616981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 160020365060759904404311949 60007636897784964151616981)
                  ·
                    refine ⟨1406428989791835097303523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60007636897784964151616981 1406428989791835097303523)
                    ·
                      rfl

theorem cell22_4108516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 3, 7].length) (baseStart_4108516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4108516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4108516 prefixEnd_4108516 := by exact prefixLift 4108516
  have htrace : WordTrace (prefixWord ++ tailWord_4108516) baseStart_4108516 baseEnd_4108516 := by
    simpa [prefixWord, tailWord_4108516, baseEnd_4108516] using wordTrace_append hprefix tailTrace_4108516
  have hstable : (prefixWord ++ tailWord_4108516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4108516).length < 2 ^ (prefixWord ++ tailWord_4108516).sum := by decide
  have hdescent : baseEnd_4108516 < baseStart_4108516 := by decide
  rcases family_descends (prefixWord ++ tailWord_4108516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4108522 : List Nat := [3, 1, 3, 1, 1, 2, 4, 3, 1, 3]
def baseStart_4108522 : Nat := 118140960795 + 4108522 * 2 ^ 59
def prefixEnd_4108522 : Nat := 4983230072969 + 3 ^ 40 * 4108522 * 2
def baseEnd_4108522 : Nat := 1406431043714453081653505

theorem tailTrace_4108522 : CollatzResearch.WordTrace tailWord_4108522 prefixEnd_4108522 1406431043714453081653505 := by
  unfold tailWord_4108522
  simp only [CollatzResearch.WordTrace]
  refine ⟨37462527005383487134783955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99900072014355965692757213 37462527005383487134783955)
  ·
    refine ⟨56193790508075230702175933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37462527005383487134783955 56193790508075230702175933)
    ·
      refine ⟨21072671440528211513315975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56193790508075230702175933 21072671440528211513315975)
      ·
        refine ⟨31609007160792317269973963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21072671440528211513315975 31609007160792317269973963)
        ·
          refine ⟨47413510741188475904960945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31609007160792317269973963 47413510741188475904960945)
          ·
            refine ⟨35560133055891356928720709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47413510741188475904960945 35560133055891356928720709)
            ·
              refine ⟨6667524947979629424135133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35560133055891356928720709 6667524947979629424135133)
              ·
                refine ⟨2500321855492361034050675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6667524947979629424135133 2500321855492361034050675)
                ·
                  refine ⟨3750482783238541551076013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2500321855492361034050675 3750482783238541551076013)
                  ·
                    refine ⟨1406431043714453081653505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3750482783238541551076013 1406431043714453081653505)
                    ·
                      rfl

theorem cell22_4108522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 4, 3, 1, 3].length) (baseStart_4108522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4108522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4108522 prefixEnd_4108522 := by exact prefixLift 4108522
  have htrace : WordTrace (prefixWord ++ tailWord_4108522) baseStart_4108522 baseEnd_4108522 := by
    simpa [prefixWord, tailWord_4108522, baseEnd_4108522] using wordTrace_append hprefix tailTrace_4108522
  have hstable : (prefixWord ++ tailWord_4108522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4108522).length < 2 ^ (prefixWord ++ tailWord_4108522).sum := by decide
  have hdescent : baseEnd_4108522 < baseStart_4108522 := by decide
  rcases family_descends (prefixWord ++ tailWord_4108522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4108591 : List Nat := [1, 1, 2, 1, 2, 1, 14]
def baseStart_4108591 : Nat := 118140960795 + 4108591 * 2 ^ 59
def prefixEnd_4108591 : Nat := 4983230072969 + 3 ^ 40 * 4108591 * 2
def baseEnd_4108591 : Nat := 52090913474983700062159

theorem tailTrace_4108591 : CollatzResearch.WordTrace tailWord_4108591 prefixEnd_4108591 52090913474983700062159 := by
  unfold tailWord_4108591
  simp only [CollatzResearch.WordTrace]
  refine ⟨149852624658283973323397627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99901749772189315548931751 149852624658283973323397627)
  ·
    refine ⟨224778936987425959985096441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149852624658283973323397627 224778936987425959985096441)
    ·
      refine ⟨168584202740569469988822331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224778936987425959985096441 168584202740569469988822331)
      ·
        refine ⟨252876304110854204983233497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168584202740569469988822331 252876304110854204983233497)
        ·
          refine ⟨189657228083140653737425123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252876304110854204983233497 189657228083140653737425123)
          ·
            refine ⟨284485842124710980606137685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189657228083140653737425123 284485842124710980606137685)
            ·
              refine ⟨52090913474983700062159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 14 284485842124710980606137685 52090913474983700062159)
              ·
                rfl

theorem cell22_4108591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 14].length) (baseStart_4108591 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4108591 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4108591 prefixEnd_4108591 := by exact prefixLift 4108591
  have htrace : WordTrace (prefixWord ++ tailWord_4108591) baseStart_4108591 baseEnd_4108591 := by
    simpa [prefixWord, tailWord_4108591, baseEnd_4108591] using wordTrace_append hprefix tailTrace_4108591
  have hstable : (prefixWord ++ tailWord_4108591).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4108591).length < 2 ^ (prefixWord ++ tailWord_4108591).sum := by decide
  have hdescent : baseEnd_4108591 < baseStart_4108591 := by decide
  rcases family_descends (prefixWord ++ tailWord_4108591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4108595 : List Nat := [1, 1, 1, 2, 5, 1, 2, 4, 2, 3]
def baseStart_4108595 : Nat := 118140960795 + 4108595 * 2 ^ 59
def prefixEnd_4108595 : Nat := 4983230072969 + 3 ^ 40 * 4108595 * 2
def baseEnd_4108595 : Nat := 1406456033106305224578281

theorem tailTrace_4108595 : CollatzResearch.WordTrace tailWord_4108595 prefixEnd_4108595 1406456033106305224578281 := by
  unfold tailWord_4108595
  simp only [CollatzResearch.WordTrace]
  refine ⟨149852770550269482006543239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99901847033512988004362159 149852770550269482006543239)
  ·
    refine ⟨224779155825404223009814859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149852770550269482006543239 224779155825404223009814859)
    ·
      refine ⟨337168733738106334514722289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224779155825404223009814859 337168733738106334514722289)
      ·
        refine ⟨252876550303579750886041717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 337168733738106334514722289 252876550303579750886041717)
        ·
          refine ⟨23707176590960601645566411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 252876550303579750886041717 23707176590960601645566411)
          ·
            refine ⟨35560764886440902468349617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23707176590960601645566411 35560764886440902468349617)
            ·
              refine ⟨26670573664830676851262213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35560764886440902468349617 26670573664830676851262213)
              ·
                refine ⟨5000732562155751909611665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26670573664830676851262213 5000732562155751909611665)
                ·
                  refine ⟨3750549421616813932208749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5000732562155751909611665 3750549421616813932208749)
                  ·
                    refine ⟨1406456033106305224578281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3750549421616813932208749 1406456033106305224578281)
                    ·
                      rfl

theorem cell22_4108595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 4, 2, 3].length) (baseStart_4108595 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4108595 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4108595 prefixEnd_4108595 := by exact prefixLift 4108595
  have htrace : WordTrace (prefixWord ++ tailWord_4108595) baseStart_4108595 baseEnd_4108595 := by
    simpa [prefixWord, tailWord_4108595, baseEnd_4108595] using wordTrace_append hprefix tailTrace_4108595
  have hstable : (prefixWord ++ tailWord_4108595).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4108595).length < 2 ^ (prefixWord ++ tailWord_4108595).sum := by decide
  have hdescent : baseEnd_4108595 < baseStart_4108595 := by decide
  rcases family_descends (prefixWord ++ tailWord_4108595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4108597 : List Nat := [1, 3, 3, 1, 2, 1, 5, 2, 4]
def baseStart_4108597 : Nat := 118140960795 + 4108597 * 2 ^ 59
def prefixEnd_4108597 : Nat := 4983230072969 + 3 ^ 40 * 4108597 * 2
def baseEnd_4108597 : Nat := 468818905915725962009425

theorem tailTrace_4108597 : CollatzResearch.WordTrace tailWord_4108597 prefixEnd_4108597 468818905915725962009425 := by
  unfold tailWord_4108597
  simp only [CollatzResearch.WordTrace]
  refine ⟨149852843496262236348116045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99901895664174824232077363 149852843496262236348116045)
  ·
    refine ⟨56194816311098338630543517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149852843496262236348116045 56194816311098338630543517)
    ·
      refine ⟨21073056116661876986453819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56194816311098338630543517 21073056116661876986453819)
      ·
        refine ⟨31609584174992815479680729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21073056116661876986453819 31609584174992815479680729)
        ·
          refine ⟨23707188131244611609760547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31609584174992815479680729 23707188131244611609760547)
          ·
            refine ⟨35560782196866917414640821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23707188131244611609760547 35560782196866917414640821)
            ·
              refine ⟨3333823330956273507622577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35560782196866917414640821 3333823330956273507622577)
              ·
                refine ⟨2500367498217205130716933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3333823330956273507622577 2500367498217205130716933)
                ·
                  refine ⟨468818905915725962009425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2500367498217205130716933 468818905915725962009425)
                  ·
                    rfl

theorem cell22_4108597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 5, 2, 4].length) (baseStart_4108597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4108597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4108597 prefixEnd_4108597 := by exact prefixLift 4108597
  have htrace : WordTrace (prefixWord ++ tailWord_4108597) baseStart_4108597 baseEnd_4108597 := by
    simpa [prefixWord, tailWord_4108597, baseEnd_4108597] using wordTrace_append hprefix tailTrace_4108597
  have hstable : (prefixWord ++ tailWord_4108597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4108597).length < 2 ^ (prefixWord ++ tailWord_4108597).sum := by decide
  have hdescent : baseEnd_4108597 < baseStart_4108597 := by decide
  rcases family_descends (prefixWord ++ tailWord_4108597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4108702 : List Nat := [4, 3, 1, 2, 1, 1, 1, 2, 2, 5]
def baseStart_4108702 : Nat := 118140960795 + 4108702 * 2 ^ 59
def prefixEnd_4108702 : Nat := 4983230072969 + 3 ^ 40 * 4108702 * 2
def baseEnd_4108702 : Nat := 1406492661392992612152953

theorem tailTrace_4108702 : CollatzResearch.WordTrace tailWord_4108702 prefixEnd_4108702 1406492661392992612152953 := by
  unfold tailWord_4108702
  simp only [CollatzResearch.WordTrace]
  refine ⟨18732084145110229910086045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99904448773921226187125573 18732084145110229910086045)
  ·
    refine ⟨7024531554416336216282267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18732084145110229910086045 7024531554416336216282267)
    ·
      refine ⟨10536797331624504324423401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7024531554416336216282267 10536797331624504324423401)
      ·
        refine ⟨7902597998718378243317551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10536797331624504324423401 7902597998718378243317551)
        ·
          refine ⟨11853896998077567364976327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7902597998718378243317551 11853896998077567364976327)
          ·
            refine ⟨17780845497116351047464491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11853896998077567364976327 17780845497116351047464491)
            ·
              refine ⟨26671268245674526571196737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17780845497116351047464491 26671268245674526571196737)
              ·
                refine ⟨20003451184255894928397553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26671268245674526571196737 20003451184255894928397553)
                ·
                  refine ⟨15002588388191921196298165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20003451184255894928397553 15002588388191921196298165)
                  ·
                    refine ⟨1406492661392992612152953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15002588388191921196298165 1406492661392992612152953)
                    ·
                      rfl

theorem cell22_4108702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_4108702 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4108702 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4108702 prefixEnd_4108702 := by exact prefixLift 4108702
  have htrace : WordTrace (prefixWord ++ tailWord_4108702) baseStart_4108702 baseEnd_4108702 := by
    simpa [prefixWord, tailWord_4108702, baseEnd_4108702] using wordTrace_append hprefix tailTrace_4108702
  have hstable : (prefixWord ++ tailWord_4108702).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4108702).length < 2 ^ (prefixWord ++ tailWord_4108702).sum := by decide
  have hdescent : baseEnd_4108702 < baseStart_4108702 := by decide
  rcases family_descends (prefixWord ++ tailWord_4108702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4108713 : List Nat := [1, 2, 1, 1, 1, 1, 3, 4, 3, 5]
def baseStart_4108713 : Nat := 118140960795 + 4108713 * 2 ^ 59
def prefixEnd_4108713 : Nat := 4983230072969 + 3 ^ 40 * 4108713 * 2
def baseEnd_4108713 : Nat := 1406496426917792250127919

theorem tailTrace_4108713 : CollatzResearch.WordTrace tailWord_4108713 prefixEnd_4108713 1406496426917792250127919 := by
  unfold tailWord_4108713
  simp only [CollatzResearch.WordTrace]
  refine ⟨149857074363841988159338793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99904716242561325439559195 149857074363841988159338793)
  ·
    refine ⟨112392805772881491119504095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149857074363841988159338793 112392805772881491119504095)
    ·
      refine ⟨168589208659322236679256143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112392805772881491119504095 168589208659322236679256143)
      ·
        refine ⟨252883812988983355018884215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168589208659322236679256143 252883812988983355018884215)
        ·
          refine ⟨379325719483475032528326323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252883812988983355018884215 379325719483475032528326323)
          ·
            refine ⟨568988579225212548792489485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 379325719483475032528326323 568988579225212548792489485)
            ·
              refine ⟨213370717209454705797183557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 568988579225212548792489485 213370717209454705797183557)
              ·
                refine ⟨40007009476772757336971917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 213370717209454705797183557 40007009476772757336971917)
                ·
                  refine ⟨15002628553789784001364469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40007009476772757336971917 15002628553789784001364469)
                  ·
                    refine ⟨1406496426917792250127919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15002628553789784001364469 1406496426917792250127919)
                    ·
                      rfl

theorem cell22_4108713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 4, 3, 5].length) (baseStart_4108713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4108713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4108713 prefixEnd_4108713 := by exact prefixLift 4108713
  have htrace : WordTrace (prefixWord ++ tailWord_4108713) baseStart_4108713 baseEnd_4108713 := by
    simpa [prefixWord, tailWord_4108713, baseEnd_4108713] using wordTrace_append hprefix tailTrace_4108713
  have hstable : (prefixWord ++ tailWord_4108713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4108713).length < 2 ^ (prefixWord ++ tailWord_4108713).sum := by decide
  have hdescent : baseEnd_4108713 < baseStart_4108713 := by decide
  rcases family_descends (prefixWord ++ tailWord_4108713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4108781 : List Nat := [1, 5, 1, 3, 1, 1, 4, 1, 2, 3]
def baseStart_4108781 : Nat := 118140960795 + 4108781 * 2 ^ 59
def prefixEnd_4108781 : Nat := 4983230072969 + 3 ^ 40 * 4108781 * 2
def baseEnd_4108781 : Nat := 1406519704707462739427711

theorem tailTrace_4108781 : CollatzResearch.WordTrace tailWord_4108781 prefixEnd_4108781 1406519704707462739427711 := by
  unfold tailWord_4108781
  simp only [CollatzResearch.WordTrace]
  refine ⟨149859554527595635772814197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99906369685063757181876131 149859554527595635772814197)
  ·
    refine ⟨14049333236962090853701331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 149859554527595635772814197 14049333236962090853701331)
    ·
      refine ⟨21073999855443136280551997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14049333236962090853701331 21073999855443136280551997)
      ·
        refine ⟨7902749945791176105206999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21073999855443136280551997 7902749945791176105206999)
        ·
          refine ⟨11854124918686764157810499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7902749945791176105206999 11854124918686764157810499)
          ·
            refine ⟨17781187378030146236715749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11854124918686764157810499 17781187378030146236715749)
            ·
              refine ⟨3333972633380652419384203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17781187378030146236715749 3333972633380652419384203)
              ·
                refine ⟨5000958950070978629076305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3333972633380652419384203 5000958950070978629076305)
                ·
                  refine ⟨3750719212553233971807229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5000958950070978629076305 3750719212553233971807229)
                  ·
                    refine ⟨1406519704707462739427711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3750719212553233971807229 1406519704707462739427711)
                    ·
                      rfl

theorem cell22_4108781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 4, 1, 2, 3].length) (baseStart_4108781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4108781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4108781 prefixEnd_4108781 := by exact prefixLift 4108781
  have htrace : WordTrace (prefixWord ++ tailWord_4108781) baseStart_4108781 baseEnd_4108781 := by
    simpa [prefixWord, tailWord_4108781, baseEnd_4108781] using wordTrace_append hprefix tailTrace_4108781
  have hstable : (prefixWord ++ tailWord_4108781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4108781).length < 2 ^ (prefixWord ++ tailWord_4108781).sum := by decide
  have hdescent : baseEnd_4108781 < baseStart_4108781 := by decide
  rcases family_descends (prefixWord ++ tailWord_4108781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4108826 : List Nat := [3, 1, 1, 3, 1, 1, 6, 2, 1, 3]
def baseStart_4108826 : Nat := 118140960795 + 4108826 * 2 ^ 59
def prefixEnd_4108826 : Nat := 4983230072969 + 3 ^ 40 * 4108826 * 2
def baseEnd_4108826 : Nat := 1406535109127097622052573

theorem tailTrace_4108826 : CollatzResearch.WordTrace tailWord_4108826 prefixEnd_4108826 1406535109127097622052573 := by
  unfold tailWord_4108826
  simp only [CollatzResearch.WordTrace]
  refine ⟨37465298953108152114550583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99907463874955072305468221 37465298953108152114550583)
  ·
    refine ⟨56197948429662228171825875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37465298953108152114550583 56197948429662228171825875)
    ·
      refine ⟨84296922644493342257738813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56197948429662228171825875 84296922644493342257738813)
      ·
        refine ⟨31611345991685003346652055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84296922644493342257738813 31611345991685003346652055)
        ·
          refine ⟨47417018987527505019978083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31611345991685003346652055 47417018987527505019978083)
          ·
            refine ⟨71125528481291257529967125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47417018987527505019978083 71125528481291257529967125)
            ·
              refine ⟨3334009147560527696717209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 71125528481291257529967125 3334009147560527696717209)
              ·
                refine ⟨2500506860670395772537907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3334009147560527696717209 2500506860670395772537907)
                ·
                  refine ⟨3750760291005593658806861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2500506860670395772537907 3750760291005593658806861)
                  ·
                    refine ⟨1406535109127097622052573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3750760291005593658806861 1406535109127097622052573)
                    ·
                      rfl

theorem cell22_4108826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 6, 2, 1, 3].length) (baseStart_4108826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4108826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4108826 prefixEnd_4108826 := by exact prefixLift 4108826
  have htrace : WordTrace (prefixWord ++ tailWord_4108826) baseStart_4108826 baseEnd_4108826 := by
    simpa [prefixWord, tailWord_4108826, baseEnd_4108826] using wordTrace_append hprefix tailTrace_4108826
  have hstable : (prefixWord ++ tailWord_4108826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4108826).length < 2 ^ (prefixWord ++ tailWord_4108826).sum := by decide
  have hdescent : baseEnd_4108826 < baseStart_4108826 := by decide
  rcases family_descends (prefixWord ++ tailWord_4108826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4108850 : List Nat := [3, 2, 1, 1, 2, 1, 3, 1, 8]
def baseStart_4108850 : Nat := 118140960795 + 4108850 * 2 ^ 59
def prefixEnd_4108850 : Nat := 4983230072969 + 3 ^ 40 * 4108850 * 2
def baseEnd_4108850 : Nat := 468847774939189853150833

theorem tailTrace_4108850 : CollatzResearch.WordTrace tailWord_4108850 prefixEnd_4108850 468847774939189853150833 := by
  unfold tailWord_4108850
  simp only [CollatzResearch.WordTrace]
  refine ⟨37465517791086415139269001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99908047442897107038050669 37465517791086415139269001)
  ·
    refine ⟨28099138343314811354451751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37465517791086415139269001 28099138343314811354451751)
    ·
      refine ⟨42148707514972217031677627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28099138343314811354451751 42148707514972217031677627)
      ·
        refine ⟨63223061272458325547516441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42148707514972217031677627 63223061272458325547516441)
        ·
          refine ⟨47417295954343744160637331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63223061272458325547516441 47417295954343744160637331)
          ·
            refine ⟨71125943931515616240955997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47417295954343744160637331 71125943931515616240955997)
            ·
              refine ⟨26672228974318356090358499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71125943931515616240955997 26672228974318356090358499)
              ·
                refine ⟨40008343461477534135537749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26672228974318356090358499 40008343461477534135537749)
                ·
                  refine ⟨468847774939189853150833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40008343461477534135537749 468847774939189853150833)
                  ·
                    rfl

theorem cell22_4108850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 1, 8].length) (baseStart_4108850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4108850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4108850 prefixEnd_4108850 := by exact prefixLift 4108850
  have htrace : WordTrace (prefixWord ++ tailWord_4108850) baseStart_4108850 baseEnd_4108850 := by
    simpa [prefixWord, tailWord_4108850, baseEnd_4108850] using wordTrace_append hprefix tailTrace_4108850
  have hstable : (prefixWord ++ tailWord_4108850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4108850).length < 2 ^ (prefixWord ++ tailWord_4108850).sum := by decide
  have hdescent : baseEnd_4108850 < baseStart_4108850 := by decide
  rcases family_descends (prefixWord ++ tailWord_4108850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4108869 : List Nat := [1, 3, 1, 1, 1, 5, 4, 1, 1, 4]
def baseStart_4108869 : Nat := 118140960795 + 4108869 * 2 ^ 59
def prefixEnd_4108869 : Nat := 4983230072969 + 3 ^ 40 * 4108869 * 2
def baseEnd_4108869 : Nat := 1406549828905859843227441

theorem tailTrace_4108869 : CollatzResearch.WordTrace tailWord_4108869 prefixEnd_4108869 1406549828905859843227441 := by
  unfold tailWord_4108869
  simp only [CollatzResearch.WordTrace]
  refine ⟨149862764151276826802017661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99908509434184551201345107 149862764151276826802017661)
  ·
    refine ⟨56198536556728810050756623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149862764151276826802017661 56198536556728810050756623)
    ·
      refine ⟨84297804835093215076134935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56198536556728810050756623 84297804835093215076134935)
      ·
        refine ⟨126446707252639822614202403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84297804835093215076134935 126446707252639822614202403)
        ·
          refine ⟨189670060878959733921303605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126446707252639822614202403 189670060878959733921303605)
          ·
            refine ⟨17781568207402475055122213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 189670060878959733921303605 17781568207402475055122213)
            ·
              refine ⟨3334044038887964072835415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17781568207402475055122213 3334044038887964072835415)
              ·
                refine ⟨5001066058331946109253123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3334044038887964072835415 5001066058331946109253123)
                ·
                  refine ⟨7501599087497919163879685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5001066058331946109253123 7501599087497919163879685)
                  ·
                    refine ⟨1406549828905859843227441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7501599087497919163879685 1406549828905859843227441)
                    ·
                      rfl

theorem cell22_4108869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 4, 1, 1, 4].length) (baseStart_4108869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4108869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4108869 prefixEnd_4108869 := by exact prefixLift 4108869
  have htrace : WordTrace (prefixWord ++ tailWord_4108869) baseStart_4108869 baseEnd_4108869 := by
    simpa [prefixWord, tailWord_4108869, baseEnd_4108869] using wordTrace_append hprefix tailTrace_4108869
  have hstable : (prefixWord ++ tailWord_4108869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4108869).length < 2 ^ (prefixWord ++ tailWord_4108869).sum := by decide
  have hdescent : baseEnd_4108869 < baseStart_4108869 := by decide
  rcases family_descends (prefixWord ++ tailWord_4108869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4108884 : List Nat := [2, 4, 1, 1, 1, 3, 2, 4, 4]
def baseStart_4108884 : Nat := 118140960795 + 4108884 * 2 ^ 59
def prefixEnd_4108884 : Nat := 4983230072969 + 3 ^ 40 * 4108884 * 2
def baseEnd_4108884 : Nat := 468851654570801601367465

theorem tailTrace_4108884 : CollatzResearch.WordTrace tailWord_4108884 prefixEnd_4108884 468851654570801601367465 := by
  unfold tailWord_4108884
  simp only [CollatzResearch.WordTrace]
  refine ⟨74931655623111242181906853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99908874164148322909209137 74931655623111242181906853)
  ·
    refine ⟨14049685429333357909107535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74931655623111242181906853 14049685429333357909107535)
    ·
      refine ⟨21074528144000036863661303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14049685429333357909107535 21074528144000036863661303)
      ·
        refine ⟨31611792216000055295491955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21074528144000036863661303 31611792216000055295491955)
        ·
          refine ⟨47417688324000082943237933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31611792216000055295491955 47417688324000082943237933)
          ·
            refine ⟨17781633121500031103714225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47417688324000082943237933 17781633121500031103714225)
            ·
              refine ⟨13336224841125023327785669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17781633121500031103714225 13336224841125023327785669)
              ·
                refine ⟨2500542157710941873959813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13336224841125023327785669 2500542157710941873959813)
                ·
                  refine ⟨468851654570801601367465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2500542157710941873959813 468851654570801601367465)
                  ·
                    rfl

theorem cell22_4108884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 4, 4].length) (baseStart_4108884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4108884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4108884 prefixEnd_4108884 := by exact prefixLift 4108884
  have htrace : WordTrace (prefixWord ++ tailWord_4108884) baseStart_4108884 baseEnd_4108884 := by
    simpa [prefixWord, tailWord_4108884, baseEnd_4108884] using wordTrace_append hprefix tailTrace_4108884
  have hstable : (prefixWord ++ tailWord_4108884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4108884).length < 2 ^ (prefixWord ++ tailWord_4108884).sum := by decide
  have hdescent : baseEnd_4108884 < baseStart_4108884 := by decide
  rcases family_descends (prefixWord ++ tailWord_4108884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4108912 : List Nat := [2, 1, 1, 1, 7, 1, 1, 8]
def baseStart_4108912 : Nat := 118140960795 + 4108912 * 2 ^ 59
def prefixEnd_4108912 : Nat := 4983230072969 + 3 ^ 40 * 4108912 * 2
def baseEnd_4108912 : Nat := 156284949853846896044701

theorem tailTrace_4108912 : CollatzResearch.WordTrace tailWord_4108912 prefixEnd_4108912 156284949853846896044701 := by
  unfold tailWord_4108912
  simp only [CollatzResearch.WordTrace]
  refine ⟨74932166245060522572916495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99909554993414030097221993 74932166245060522572916495)
  ·
    refine ⟨112398249367590783859374743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74932166245060522572916495 112398249367590783859374743)
    ·
      refine ⟨168597374051386175789062115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112398249367590783859374743 168597374051386175789062115)
      ·
        refine ⟨252896061077079263683593173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168597374051386175789062115 252896061077079263683593173)
        ·
          refine ⟨5927251431494045242584215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 252896061077079263683593173 5927251431494045242584215)
          ·
            refine ⟨8890877147241067863876323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5927251431494045242584215 8890877147241067863876323)
            ·
              refine ⟨13336315720861601795814485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8890877147241067863876323 13336315720861601795814485)
              ·
                refine ⟨156284949853846896044701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13336315720861601795814485 156284949853846896044701)
                ·
                  rfl

theorem cell22_4108912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 8].length) (baseStart_4108912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4108912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4108912 prefixEnd_4108912 := by exact prefixLift 4108912
  have htrace : WordTrace (prefixWord ++ tailWord_4108912) baseStart_4108912 baseEnd_4108912 := by
    simpa [prefixWord, tailWord_4108912, baseEnd_4108912] using wordTrace_append hprefix tailTrace_4108912
  have hstable : (prefixWord ++ tailWord_4108912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4108912).length < 2 ^ (prefixWord ++ tailWord_4108912).sum := by decide
  have hdescent : baseEnd_4108912 < baseStart_4108912 := by decide
  rcases family_descends (prefixWord ++ tailWord_4108912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4108918 : List Nat := [5, 1, 1, 2, 3, 2, 1, 3, 4]
def baseStart_4108918 : Nat := 118140960795 + 4108918 * 2 ^ 59
def prefixEnd_4108918 : Nat := 4983230072969 + 3 ^ 40 * 4108918 * 2
def baseEnd_4108918 : Nat := 468855534202413349584097

theorem tailTrace_4108918 : CollatzResearch.WordTrace tailWord_4108918 prefixEnd_4108918 468855534202413349584097 := by
  unfold tailWord_4108918
  simp only [CollatzResearch.WordTrace]
  refine ⟨9366534458006206760659463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 99909700885399538780367605 9366534458006206760659463)
  ·
    refine ⟨14049801687009310140989195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9366534458006206760659463 14049801687009310140989195)
    ·
      refine ⟨21074702530513965211483793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14049801687009310140989195 21074702530513965211483793)
      ·
        refine ⟨15806026897885473908612845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21074702530513965211483793 15806026897885473908612845)
        ·
          refine ⟨5927260086707052715729817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15806026897885473908612845 5927260086707052715729817)
          ·
            refine ⟨4445445065030289536797363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5927260086707052715729817 4445445065030289536797363)
            ·
              refine ⟨6668167597545434305196045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4445445065030289536797363 6668167597545434305196045)
              ·
                refine ⟨2500562849079537864448517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6668167597545434305196045 2500562849079537864448517)
                ·
                  refine ⟨468855534202413349584097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2500562849079537864448517 468855534202413349584097)
                  ·
                    rfl

theorem cell22_4108918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 1, 3, 4].length) (baseStart_4108918 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4108918 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4108918 prefixEnd_4108918 := by exact prefixLift 4108918
  have htrace : WordTrace (prefixWord ++ tailWord_4108918) baseStart_4108918 baseEnd_4108918 := by
    simpa [prefixWord, tailWord_4108918, baseEnd_4108918] using wordTrace_append hprefix tailTrace_4108918
  have hstable : (prefixWord ++ tailWord_4108918).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4108918).length < 2 ^ (prefixWord ++ tailWord_4108918).sum := by decide
  have hdescent : baseEnd_4108918 < baseStart_4108918 := by decide
  rcases family_descends (prefixWord ++ tailWord_4108918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4108942 : List Nat := [4, 1, 1, 3, 1, 1, 2, 1, 2, 6]
def baseStart_4108942 : Nat := 118140960795 + 4108942 * 2 ^ 59
def prefixEnd_4108942 : Nat := 4983230072969 + 3 ^ 40 * 4108942 * 2
def baseEnd_4108942 : Nat := 1406574818297711986152217

theorem tailTrace_4108942 : CollatzResearch.WordTrace tailWord_4108942 prefixEnd_4108942 1406574818297711986152217 := by
  unfold tailWord_4108942
  simp only [CollatzResearch.WordTrace]
  refine ⟨18733178335001545033678135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99910284453341573512950053 18733178335001545033678135)
  ·
    refine ⟨28099767502502317550517203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18733178335001545033678135 28099767502502317550517203)
    ·
      refine ⟨42149651253753476325775805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28099767502502317550517203 42149651253753476325775805)
      ·
        refine ⟨15806119220157553622165927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42149651253753476325775805 15806119220157553622165927)
        ·
          refine ⟨23709178830236330433248891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15806119220157553622165927 23709178830236330433248891)
          ·
            refine ⟨35563768245354495649873337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23709178830236330433248891 35563768245354495649873337)
            ·
              refine ⟨26672826184015871737405003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35563768245354495649873337 26672826184015871737405003)
              ·
                refine ⟨40009239276023807606107505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26672826184015871737405003 40009239276023807606107505)
                ·
                  refine ⟨30006929457017855704580629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40009239276023807606107505 30006929457017855704580629)
                  ·
                    refine ⟨1406574818297711986152217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30006929457017855704580629 1406574818297711986152217)
                    ·
                      rfl

theorem cell22_4108942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 1, 2, 6].length) (baseStart_4108942 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4108942 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4108942 prefixEnd_4108942 := by exact prefixLift 4108942
  have htrace : WordTrace (prefixWord ++ tailWord_4108942) baseStart_4108942 baseEnd_4108942 := by
    simpa [prefixWord, tailWord_4108942, baseEnd_4108942] using wordTrace_append hprefix tailTrace_4108942
  have hstable : (prefixWord ++ tailWord_4108942).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4108942).length < 2 ^ (prefixWord ++ tailWord_4108942).sum := by decide
  have hdescent : baseEnd_4108942 < baseStart_4108942 := by decide
  rcases family_descends (prefixWord ++ tailWord_4108942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4108955 : List Nat := [1, 1, 1, 1, 1, 1, 2, 2, 5, 7]
def baseStart_4108955 : Nat := 118140960795 + 4108955 * 2 ^ 59
def prefixEnd_4108955 : Nat := 4983230072969 + 3 ^ 40 * 4108955 * 2
def baseEnd_4108955 : Nat := 1406579268463384285577177

theorem tailTrace_4108955 : CollatzResearch.WordTrace tailWord_4108955 prefixEnd_4108955 1406579268463384285577177 := by
  unfold tailWord_4108955
  simp only [CollatzResearch.WordTrace]
  refine ⟨149865900828965263489648319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99910600552643508993098879 149865900828965263489648319)
  ·
    refine ⟨224798851243447895234472479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149865900828965263489648319 224798851243447895234472479)
    ·
      refine ⟨337198276865171842851708719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224798851243447895234472479 337198276865171842851708719)
      ·
        refine ⟨505797415297757764277563079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337198276865171842851708719 505797415297757764277563079)
        ·
          refine ⟨758696122946636646416344619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 505797415297757764277563079 758696122946636646416344619)
          ·
            refine ⟨1138044184419954969624516929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 758696122946636646416344619 1138044184419954969624516929)
            ·
              refine ⟨853533138314966227218387697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1138044184419954969624516929 853533138314966227218387697)
              ·
                refine ⟨640149853736224670413790773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 853533138314966227218387697 640149853736224670413790773)
                ·
                  refine ⟨60014048787771062851292885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 640149853736224670413790773 60014048787771062851292885)
                  ·
                    refine ⟨1406579268463384285577177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60014048787771062851292885 1406579268463384285577177)
                    ·
                      rfl

theorem cell22_4108955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5, 7].length) (baseStart_4108955 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4108955 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4108955 prefixEnd_4108955 := by exact prefixLift 4108955
  have htrace : WordTrace (prefixWord ++ tailWord_4108955) baseStart_4108955 baseEnd_4108955 := by
    simpa [prefixWord, tailWord_4108955, baseEnd_4108955] using wordTrace_append hprefix tailTrace_4108955
  have hstable : (prefixWord ++ tailWord_4108955).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4108955).length < 2 ^ (prefixWord ++ tailWord_4108955).sum := by decide
  have hdescent : baseEnd_4108955 < baseStart_4108955 := by decide
  rcases family_descends (prefixWord ++ tailWord_4108955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4109004 : List Nat := [2, 2, 1, 5, 1, 1, 1, 2, 3, 4]
def baseStart_4109004 : Nat := 118140960795 + 4109004 * 2 ^ 59
def prefixEnd_4109004 : Nat := 4983230072969 + 3 ^ 40 * 4109004 * 2
def baseEnd_4109004 : Nat := 1406596042164764491102027

theorem tailTrace_4109004 : CollatzResearch.WordTrace tailWord_4109004 prefixEnd_4109004 1406596042164764491102027 := by
  unfold tailWord_4109004
  simp only [CollatzResearch.WordTrace]
  refine ⟨74933844002893872429091033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99911792003858496572121377 74933844002893872429091033)
  ·
    refine ⟨56200383002170404321818275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74933844002893872429091033 56200383002170404321818275)
    ·
      refine ⟨84300574503255606482727413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56200383002170404321818275 84300574503255606482727413)
      ·
        refine ⟨7903178859680213107755695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 84300574503255606482727413 7903178859680213107755695)
        ·
          refine ⟨11854768289520319661633543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7903178859680213107755695 11854768289520319661633543)
          ·
            refine ⟨17782152434280479492450315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11854768289520319661633543 17782152434280479492450315)
            ·
              refine ⟨26673228651420719238675473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17782152434280479492450315 26673228651420719238675473)
              ·
                refine ⟨20004921488565539429006605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26673228651420719238675473 20004921488565539429006605)
                ·
                  refine ⟨7501845558212077285877477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20004921488565539429006605 7501845558212077285877477)
                  ·
                    refine ⟨1406596042164764491102027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7501845558212077285877477 1406596042164764491102027)
                    ·
                      rfl

theorem cell22_4109004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 2, 3, 4].length) (baseStart_4109004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4109004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4109004 prefixEnd_4109004 := by exact prefixLift 4109004
  have htrace : WordTrace (prefixWord ++ tailWord_4109004) baseStart_4109004 baseEnd_4109004 := by
    simpa [prefixWord, tailWord_4109004, baseEnd_4109004] using wordTrace_append hprefix tailTrace_4109004
  have hstable : (prefixWord ++ tailWord_4109004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4109004).length < 2 ^ (prefixWord ++ tailWord_4109004).sum := by decide
  have hdescent : baseEnd_4109004 < baseStart_4109004 := by decide
  rcases family_descends (prefixWord ++ tailWord_4109004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4109034 : List Nat := [3, 1, 3, 1, 1, 1, 1, 4, 4, 3]
def baseStart_4109034 : Nat := 118140960795 + 4109034 * 2 ^ 59
def prefixEnd_4109034 : Nat := 4983230072969 + 3 ^ 40 * 4109034 * 2
def baseEnd_4109034 : Nat := 1406606311777854412851935

theorem tailTrace_4109034 : CollatzResearch.WordTrace tailWord_4109034 prefixEnd_4109034 1406606311777854412851935 := by
  unfold tailWord_4109034
  simp only [CollatzResearch.WordTrace]
  refine ⟨37467195548919764995443539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99912521463786039987849437 37467195548919764995443539)
  ·
    refine ⟨56200793323379647493165309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37467195548919764995443539 56200793323379647493165309)
    ·
      refine ⟨21075297496267367809936991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56200793323379647493165309 21075297496267367809936991)
      ·
        refine ⟨31612946244401051714905487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21075297496267367809936991 31612946244401051714905487)
        ·
          refine ⟨47419419366601577572358231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31612946244401051714905487 47419419366601577572358231)
          ·
            refine ⟨71129129049902366358537347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47419419366601577572358231 71129129049902366358537347)
            ·
              refine ⟨106693693574853549537806021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71129129049902366358537347 106693693574853549537806021)
              ·
                refine ⟨20005067545285040538338629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106693693574853549537806021 20005067545285040538338629)
                ·
                  refine ⟨3750950164740945100938493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20005067545285040538338629 3750950164740945100938493)
                  ·
                    refine ⟨1406606311777854412851935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3750950164740945100938493 1406606311777854412851935)
                    ·
                      rfl

theorem cell22_4109034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 4, 4, 3].length) (baseStart_4109034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4109034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4109034 prefixEnd_4109034 := by exact prefixLift 4109034
  have htrace : WordTrace (prefixWord ++ tailWord_4109034) baseStart_4109034 baseEnd_4109034 := by
    simpa [prefixWord, tailWord_4109034, baseEnd_4109034] using wordTrace_append hprefix tailTrace_4109034
  have hstable : (prefixWord ++ tailWord_4109034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4109034).length < 2 ^ (prefixWord ++ tailWord_4109034).sum := by decide
  have hdescent : baseEnd_4109034 < baseStart_4109034 := by decide
  rcases family_descends (prefixWord ++ tailWord_4109034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4109038 : List Nat := [4, 1, 2, 1, 1, 5, 2, 1, 1, 4]
def baseStart_4109038 : Nat := 118140960795 + 4109038 * 2 ^ 59
def prefixEnd_4109038 : Nat := 4983230072969 + 3 ^ 40 * 4109038 * 2
def baseEnd_4109038 : Nat := 1406607681059599735751923

theorem tailTrace_4109038 : CollatzResearch.WordTrace tailWord_4109038 prefixEnd_4109038 1406607681059599735751923 := by
  unfold tailWord_4109038
  simp only [CollatzResearch.WordTrace]
  refine ⟨18733616010958071083114971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99912618725109712443279845 18733616010958071083114971)
  ·
    refine ⟨28100424016437106624672457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18733616010958071083114971 28100424016437106624672457)
    ·
      refine ⟨21075318012327829968504343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28100424016437106624672457 21075318012327829968504343)
      ·
        refine ⟨31612977018491744952756515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21075318012327829968504343 31612977018491744952756515)
        ·
          refine ⟨47419465527737617429134773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31612977018491744952756515 47419465527737617429134773)
          ·
            refine ⟨4445574893225401633981385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47419465527737617429134773 4445574893225401633981385)
            ·
              refine ⟨3334181169919051225486039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4445574893225401633981385 3334181169919051225486039)
              ·
                refine ⟨5001271754878576838229059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3334181169919051225486039 5001271754878576838229059)
                ·
                  refine ⟨7501907632317865257343589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5001271754878576838229059 7501907632317865257343589)
                  ·
                    refine ⟨1406607681059599735751923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7501907632317865257343589 1406607681059599735751923)
                    ·
                      rfl

theorem cell22_4109038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 2, 1, 1, 4].length) (baseStart_4109038 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4109038 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4109038 prefixEnd_4109038 := by exact prefixLift 4109038
  have htrace : WordTrace (prefixWord ++ tailWord_4109038) baseStart_4109038 baseEnd_4109038 := by
    simpa [prefixWord, tailWord_4109038, baseEnd_4109038] using wordTrace_append hprefix tailTrace_4109038
  have hstable : (prefixWord ++ tailWord_4109038).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4109038).length < 2 ^ (prefixWord ++ tailWord_4109038).sum := by decide
  have hdescent : baseEnd_4109038 < baseStart_4109038 := by decide
  rcases family_descends (prefixWord ++ tailWord_4109038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4109098 : List Nat := [3, 1, 4, 3, 2, 1, 8]
def baseStart_4109098 : Nat := 118140960795 + 4109098 * 2 ^ 59
def prefixEnd_4109098 : Nat := 4983230072969 + 3 ^ 40 * 4109098 * 2
def baseEnd_4109098 : Nat := 52097341492065910342657

theorem tailTrace_4109098 : CollatzResearch.WordTrace tailWord_4109098 prefixEnd_4109098 52097341492065910342657 := by
  unfold tailWord_4109098
  simp only [CollatzResearch.WordTrace]
  refine ⟨37467779116861799728025987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99914077644964799274735965 37467779116861799728025987)
  ·
    refine ⟨56201668675292699592038981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37467779116861799728025987 56201668675292699592038981)
    ·
      refine ⟨10537812876617381173507309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56201668675292699592038981 10537812876617381173507309)
      ·
        refine ⟨3951679828731517940065241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10537812876617381173507309 3951679828731517940065241)
        ·
          refine ⟨2963759871548638455048931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3951679828731517940065241 2963759871548638455048931)
          ·
            refine ⟨4445639807322957682573397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2963759871548638455048931 4445639807322957682573397)
            ·
              refine ⟨52097341492065910342657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4445639807322957682573397 52097341492065910342657)
              ·
                rfl

theorem cell22_4109098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 8].length) (baseStart_4109098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4109098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4109098 prefixEnd_4109098 := by exact prefixLift 4109098
  have htrace : WordTrace (prefixWord ++ tailWord_4109098) baseStart_4109098 baseEnd_4109098 := by
    simpa [prefixWord, tailWord_4109098, baseEnd_4109098] using wordTrace_append hprefix tailTrace_4109098
  have hstable : (prefixWord ++ tailWord_4109098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4109098).length < 2 ^ (prefixWord ++ tailWord_4109098).sum := by decide
  have hdescent : baseEnd_4109098 < baseStart_4109098 := by decide
  rcases family_descends (prefixWord ++ tailWord_4109098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4109109 : List Nat := [1, 3, 3, 1, 3, 1, 2, 1, 7]
def baseStart_4109109 : Nat := 118140960795 + 4109109 * 2 ^ 59
def prefixEnd_4109109 : Nat := 4983230072969 + 3 ^ 40 * 4109109 * 2
def baseEnd_4109109 : Nat := 468877328603526405742235

theorem tailTrace_4109109 : CollatzResearch.WordTrace tailWord_4109109 prefixEnd_4109109 468877328603526405742235 := by
  unfold tailWord_4109109
  simp only [CollatzResearch.WordTrace]
  refine ⟨149871517670407347790754381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99914345113604898527169587 149871517670407347790754381)
  ·
    refine ⟨56201819126402755421532893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149871517670407347790754381 56201819126402755421532893)
    ·
      refine ⟨21075682172401033283074835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56201819126402755421532893 21075682172401033283074835)
      ·
        refine ⟨31613523258601549924612253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21075682172401033283074835 31613523258601549924612253)
        ·
          refine ⟨11855071221975581221729595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31613523258601549924612253 11855071221975581221729595)
          ·
            refine ⟨17782606832963371832594393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11855071221975581221729595 17782606832963371832594393)
            ·
              refine ⟨13336955124722528874445795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17782606832963371832594393 13336955124722528874445795)
              ·
                refine ⟨20005432687083793311668693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13336955124722528874445795 20005432687083793311668693)
                ·
                  refine ⟨468877328603526405742235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20005432687083793311668693 468877328603526405742235)
                  ·
                    rfl

theorem cell22_4109109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 1, 7].length) (baseStart_4109109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4109109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4109109 prefixEnd_4109109 := by exact prefixLift 4109109
  have htrace : WordTrace (prefixWord ++ tailWord_4109109) baseStart_4109109 baseEnd_4109109 := by
    simpa [prefixWord, tailWord_4109109, baseEnd_4109109] using wordTrace_append hprefix tailTrace_4109109
  have hstable : (prefixWord ++ tailWord_4109109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4109109).length < 2 ^ (prefixWord ++ tailWord_4109109).sum := by decide
  have hdescent : baseEnd_4109109 < baseStart_4109109 := by decide
  rcases family_descends (prefixWord ++ tailWord_4109109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4109282 : List Nat := [3, 3, 3, 1, 1, 3, 1, 1, 3, 3]
def baseStart_4109282 : Nat := 118140960795 + 4109282 * 2 ^ 59
def prefixEnd_4109282 : Nat := 4983230072969 + 3 ^ 40 * 4109282 * 2
def baseEnd_4109282 : Nat := 1406691207246064432651175

theorem tailTrace_4109282 : CollatzResearch.WordTrace tailWord_4109282 prefixEnd_4109282 1406691207246064432651175 := by
  unfold tailWord_4109282
  simp only [CollatzResearch.WordTrace]
  refine ⟨37469456874695149584200525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99918551665853732224534733 37469456874695149584200525)
  ·
    refine ⟨14051046328010681094075197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37469456874695149584200525 14051046328010681094075197)
    ·
      refine ⟨5269142373004005410278199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14051046328010681094075197 5269142373004005410278199)
      ·
        refine ⟨7903713559506008115417299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5269142373004005410278199 7903713559506008115417299)
        ·
          refine ⟨11855570339259012173125949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7903713559506008115417299 11855570339259012173125949)
          ·
            refine ⟨4445838877222129564922231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11855570339259012173125949 4445838877222129564922231)
            ·
              refine ⟨6668758315833194347383347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4445838877222129564922231 6668758315833194347383347)
              ·
                refine ⟨10003137473749791521075021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6668758315833194347383347 10003137473749791521075021)
                ·
                  refine ⟨3751176552656171820403133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10003137473749791521075021 3751176552656171820403133)
                  ·
                    refine ⟨1406691207246064432651175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3751176552656171820403133 1406691207246064432651175)
                    ·
                      rfl

theorem cell22_4109282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_4109282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4109282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4109282 prefixEnd_4109282 := by exact prefixLift 4109282
  have htrace : WordTrace (prefixWord ++ tailWord_4109282) baseStart_4109282 baseEnd_4109282 := by
    simpa [prefixWord, tailWord_4109282, baseEnd_4109282] using wordTrace_append hprefix tailTrace_4109282
  have hstable : (prefixWord ++ tailWord_4109282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4109282).length < 2 ^ (prefixWord ++ tailWord_4109282).sum := by decide
  have hdescent : baseEnd_4109282 < baseStart_4109282 := by decide
  rcases family_descends (prefixWord ++ tailWord_4109282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4109308 : List Nat := [2, 2, 2, 1, 2, 3, 3, 2, 1, 4]
def baseStart_4109308 : Nat := 118140960795 + 4109308 * 2 ^ 59
def prefixEnd_4109308 : Nat := 4983230072969 + 3 ^ 40 * 4109308 * 2
def baseEnd_4109308 : Nat := 1406700107577409031501095

theorem tailTrace_4109308 : CollatzResearch.WordTrace tailWord_4109308 prefixEnd_4109308 1406700107577409031501095 := by
  unfold tailWord_4109308
  simp only [CollatzResearch.WordTrace]
  refine ⟨74939387898343202388624289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99919183864457603184832385 74939387898343202388624289)
  ·
    refine ⟨56204540923757401791468217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74939387898343202388624289 56204540923757401791468217)
    ·
      refine ⟨42153405692818051343601163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56204540923757401791468217 42153405692818051343601163)
      ·
        refine ⟨63230108539227077015401745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42153405692818051343601163 63230108539227077015401745)
        ·
          refine ⟨47422581404420307761551309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63230108539227077015401745 47422581404420307761551309)
          ·
            refine ⟨17783468026657615410581741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47422581404420307761551309 17783468026657615410581741)
            ·
              refine ⟨6668800509996605778968153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17783468026657615410581741 6668800509996605778968153)
              ·
                refine ⟨5001600382497454334226115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6668800509996605778968153 5001600382497454334226115)
                ·
                  refine ⟨7502400573746181501339173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5001600382497454334226115 7502400573746181501339173)
                  ·
                    refine ⟨1406700107577409031501095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7502400573746181501339173 1406700107577409031501095)
                    ·
                      rfl

theorem cell22_4109308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 3, 2, 1, 4].length) (baseStart_4109308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4109308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4109308 prefixEnd_4109308 := by exact prefixLift 4109308
  have htrace : WordTrace (prefixWord ++ tailWord_4109308) baseStart_4109308 baseEnd_4109308 := by
    simpa [prefixWord, tailWord_4109308, baseEnd_4109308] using wordTrace_append hprefix tailTrace_4109308
  have hstable : (prefixWord ++ tailWord_4109308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4109308).length < 2 ^ (prefixWord ++ tailWord_4109308).sum := by decide
  have hdescent : baseEnd_4109308 < baseStart_4109308 := by decide
  rcases family_descends (prefixWord ++ tailWord_4109308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4109321 : List Nat := [1, 2, 1, 1, 3, 1, 1, 3, 6, 3]
def baseStart_4109321 : Nat := 118140960795 + 4109321 * 2 ^ 59
def prefixEnd_4109321 : Nat := 4983230072969 + 3 ^ 40 * 4109321 * 2
def baseEnd_4109321 : Nat := 1406704557743081330926055

theorem tailTrace_4109321 : CollatzResearch.WordTrace tailWord_4109321 prefixEnd_4109321 1406704557743081330926055 := by
  unfold tailWord_4109321
  simp only [CollatzResearch.WordTrace]
  refine ⟨149879249945639307997471817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99919499963759538664981211 149879249945639307997471817)
  ·
    refine ⟨112409437459229480998103863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149879249945639307997471817 112409437459229480998103863)
    ·
      refine ⟨168614156188844221497155795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112409437459229480998103863 168614156188844221497155795)
      ·
        refine ⟨252921234283266332245733693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168614156188844221497155795 252921234283266332245733693)
        ·
          refine ⟨94845462856224874592150135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 252921234283266332245733693 94845462856224874592150135)
          ·
            refine ⟨142268194284337311888225203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94845462856224874592150135 142268194284337311888225203)
            ·
              refine ⟨213402291426505967832337805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142268194284337311888225203 213402291426505967832337805)
              ·
                refine ⟨80025859284939737937126677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 213402291426505967832337805 80025859284939737937126677)
                ·
                  refine ⟨3751212153981550215802813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 80025859284939737937126677 3751212153981550215802813)
                  ·
                    refine ⟨1406704557743081330926055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3751212153981550215802813 1406704557743081330926055)
                    ·
                      rfl

theorem cell22_4109321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 3, 6, 3].length) (baseStart_4109321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4109321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4109321 prefixEnd_4109321 := by exact prefixLift 4109321
  have htrace : WordTrace (prefixWord ++ tailWord_4109321) baseStart_4109321 baseEnd_4109321 := by
    simpa [prefixWord, tailWord_4109321, baseEnd_4109321] using wordTrace_append hprefix tailTrace_4109321
  have hstable : (prefixWord ++ tailWord_4109321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4109321).length < 2 ^ (prefixWord ++ tailWord_4109321).sum := by decide
  have hdescent : baseEnd_4109321 < baseStart_4109321 := by decide
  rcases family_descends (prefixWord ++ tailWord_4109321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4109340 : List Nat := [2, 2, 3, 1, 4, 1, 1, 4, 4]
def baseStart_4109340 : Nat := 118140960795 + 4109340 * 2 ^ 59
def prefixEnd_4109340 : Nat := 4983230072969 + 3 ^ 40 * 4109340 * 2
def baseEnd_4109340 : Nat := 468903687277123871566999

theorem tailTrace_4109340 : CollatzResearch.WordTrace tailWord_4109340 prefixEnd_4109340 468903687277123871566999 := by
  unfold tailWord_4109340
  simp only [CollatzResearch.WordTrace]
  refine ⟨74939971466285237121206737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99919961955046982828275649 74939971466285237121206737)
  ·
    refine ⟨56204978599713927840905053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74939971466285237121206737 56204978599713927840905053)
    ·
      refine ⟨21076866974892722940339395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56204978599713927840905053 21076866974892722940339395)
      ·
        refine ⟨31615300462339084410509093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21076866974892722940339395 31615300462339084410509093)
        ·
          refine ⟨5927868836688578326970455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31615300462339084410509093 5927868836688578326970455)
          ·
            refine ⟨8891803255032867490455683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5927868836688578326970455 8891803255032867490455683)
            ·
              refine ⟨13337704882549301235683525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8891803255032867490455683 13337704882549301235683525)
              ·
                refine ⟨2500819665477993981690661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13337704882549301235683525 2500819665477993981690661)
                ·
                  refine ⟨468903687277123871566999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2500819665477993981690661 468903687277123871566999)
                  ·
                    rfl

theorem cell22_4109340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 4, 4].length) (baseStart_4109340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4109340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4109340 prefixEnd_4109340 := by exact prefixLift 4109340
  have htrace : WordTrace (prefixWord ++ tailWord_4109340) baseStart_4109340 baseEnd_4109340 := by
    simpa [prefixWord, tailWord_4109340, baseEnd_4109340] using wordTrace_append hprefix tailTrace_4109340
  have hstable : (prefixWord ++ tailWord_4109340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4109340).length < 2 ^ (prefixWord ++ tailWord_4109340).sum := by decide
  have hdescent : baseEnd_4109340 < baseStart_4109340 := by decide
  rcases family_descends (prefixWord ++ tailWord_4109340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4109368 : List Nat := [2, 1, 2, 1, 5, 2, 3, 6]
def baseStart_4109368 : Nat := 118140960795 + 4109368 * 2 ^ 59
def prefixEnd_4109368 : Nat := 4983230072969 + 3 ^ 40 * 4109368 * 2
def baseEnd_4109368 : Nat := 156302294089287652777879

theorem tailTrace_4109368 : CollatzResearch.WordTrace tailWord_4109368 prefixEnd_4109368 156302294089287652777879 := by
  unfold tailWord_4109368
  simp only [CollatzResearch.WordTrace]
  refine ⟨74940482088234517512216379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99920642784312690016288505 74940482088234517512216379)
  ·
    refine ⟨112410723132351776268324569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74940482088234517512216379 112410723132351776268324569)
    ·
      refine ⟨84308042349263832201243427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112410723132351776268324569 84308042349263832201243427)
      ·
        refine ⟨126462063523895748301865141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84308042349263832201243427 126462063523895748301865141)
        ·
          refine ⟨11855818455365226403299857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 126462063523895748301865141 11855818455365226403299857)
          ·
            refine ⟨8891863841523919802474893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11855818455365226403299857 8891863841523919802474893)
            ·
              refine ⟨3334448940571469925928085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8891863841523919802474893 3334448940571469925928085)
              ·
                refine ⟨156302294089287652777879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3334448940571469925928085 156302294089287652777879)
                ·
                  rfl

theorem cell22_4109368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 3, 6].length) (baseStart_4109368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4109368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4109368 prefixEnd_4109368 := by exact prefixLift 4109368
  have htrace : WordTrace (prefixWord ++ tailWord_4109368) baseStart_4109368 baseEnd_4109368 := by
    simpa [prefixWord, tailWord_4109368, baseEnd_4109368] using wordTrace_append hprefix tailTrace_4109368
  have hstable : (prefixWord ++ tailWord_4109368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4109368).length < 2 ^ (prefixWord ++ tailWord_4109368).sum := by decide
  have hdescent : baseEnd_4109368 < baseStart_4109368 := by decide
  rcases family_descends (prefixWord ++ tailWord_4109368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4109400 : List Nat := [2, 1, 2, 2, 1, 3, 1, 6, 1, 3]
def baseStart_4109400 : Nat := 118140960795 + 4109400 * 2 ^ 59
def prefixEnd_4109400 : Nat := 4983230072969 + 3 ^ 40 * 4109400 * 2
def baseEnd_4109400 : Nat := 1406731601057551458200813

theorem tailTrace_4109400 : CollatzResearch.WordTrace tailWord_4109400 prefixEnd_4109400 1406731601057551458200813 := by
  unfold tailWord_4109400
  simp only [CollatzResearch.WordTrace]
  refine ⟨74941065656176552244798827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99921420874902069659731769 74941065656176552244798827)
  ·
    refine ⟨112411598484264828367198241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74941065656176552244798827 112411598484264828367198241)
    ·
      refine ⟨84308698863198621275398681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112411598484264828367198241 84308698863198621275398681)
      ·
        refine ⟨63231524147398965956549011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84308698863198621275398681 63231524147398965956549011)
        ·
          refine ⟨94847286221098448934823517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63231524147398965956549011 94847286221098448934823517)
          ·
            refine ⟨35567732332911918350558819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94847286221098448934823517 35567732332911918350558819)
            ·
              refine ⟨53351598499367877525838229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35567732332911918350558819 53351598499367877525838229)
              ·
                refine ⟨2500856179657869259023667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 53351598499367877525838229 2500856179657869259023667)
                ·
                  refine ⟨3751284269486803888535501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2500856179657869259023667 3751284269486803888535501)
                  ·
                    refine ⟨1406731601057551458200813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3751284269486803888535501 1406731601057551458200813)
                    ·
                      rfl

theorem cell22_4109400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 6, 1, 3].length) (baseStart_4109400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4109400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4109400 prefixEnd_4109400 := by exact prefixLift 4109400
  have htrace : WordTrace (prefixWord ++ tailWord_4109400) baseStart_4109400 baseEnd_4109400 := by
    simpa [prefixWord, tailWord_4109400, baseEnd_4109400] using wordTrace_append hprefix tailTrace_4109400
  have hstable : (prefixWord ++ tailWord_4109400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4109400).length < 2 ^ (prefixWord ++ tailWord_4109400).sum := by decide
  have hdescent : baseEnd_4109400 < baseStart_4109400 := by decide
  rcases family_descends (prefixWord ++ tailWord_4109400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4109406 : List Nat := [4, 4, 1, 1, 1, 2, 3, 1, 2, 3]
def baseStart_4109406 : Nat := 118140960795 + 4109406 * 2 ^ 59
def prefixEnd_4109406 : Nat := 4983230072969 + 3 ^ 40 * 4109406 * 2
def baseEnd_4109406 : Nat := 1406733654980169442550795

theorem tailTrace_4109406 : CollatzResearch.WordTrace tailWord_4109406 prefixEnd_4109406 1406733654980169442550795 := by
  unfold tailWord_4109406
  simp only [CollatzResearch.WordTrace]
  refine ⟨18735293768791420939289509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99921566766887578342877381 18735293768791420939289509)
  ·
    refine ⟨3512867581648391426116783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18735293768791420939289509 3512867581648391426116783)
    ·
      refine ⟨5269301372472587139175175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3512867581648391426116783 5269301372472587139175175)
      ·
        refine ⟨7903952058708880708762763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5269301372472587139175175 7903952058708880708762763)
        ·
          refine ⟨11855928088063321063144145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7903952058708880708762763 11855928088063321063144145)
          ·
            refine ⟨8891946066047490797358109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11855928088063321063144145 8891946066047490797358109)
            ·
              refine ⟨3334479774767809049009291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8891946066047490797358109 3334479774767809049009291)
              ·
                refine ⟨5001719662151713573513937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3334479774767809049009291 5001719662151713573513937)
                ·
                  refine ⟨3751289746613785180135453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5001719662151713573513937 3751289746613785180135453)
                  ·
                    refine ⟨1406733654980169442550795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3751289746613785180135453 1406733654980169442550795)
                    ·
                      rfl

theorem cell22_4109406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_4109406 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4109406 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4109406 prefixEnd_4109406 := by exact prefixLift 4109406
  have htrace : WordTrace (prefixWord ++ tailWord_4109406) baseStart_4109406 baseEnd_4109406 := by
    simpa [prefixWord, tailWord_4109406, baseEnd_4109406] using wordTrace_append hprefix tailTrace_4109406
  have hstable : (prefixWord ++ tailWord_4109406).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4109406).length < 2 ^ (prefixWord ++ tailWord_4109406).sum := by decide
  have hdescent : baseEnd_4109406 < baseStart_4109406 := by decide
  rcases family_descends (prefixWord ++ tailWord_4109406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4109443 : List Nat := [1, 1, 1, 3, 3, 2, 1, 5, 1, 4]
def baseStart_4109443 : Nat := 118140960795 + 4109443 * 2 ^ 59
def prefixEnd_4109443 : Nat := 4983230072969 + 3 ^ 40 * 4109443 * 2
def baseEnd_4109443 : Nat := 1406746320836313679375681

theorem tailTrace_4109443 : CollatzResearch.WordTrace tailWord_4109443 prefixEnd_4109443 1406746320836313679375681 := by
  unfold tailWord_4109443
  simp only [CollatzResearch.WordTrace]
  refine ⟨149883699651197322833412983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99922466434131548555608655 149883699651197322833412983)
  ·
    refine ⟨224825549476795984250119475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149883699651197322833412983 224825549476795984250119475)
    ·
      refine ⟨337238324215193976375179213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224825549476795984250119475 337238324215193976375179213)
      ·
        refine ⟨126464371580697741140692205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 337238324215193976375179213 126464371580697741140692205)
        ·
          refine ⟨47424139342761652927759577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126464371580697741140692205 47424139342761652927759577)
          ·
            refine ⟨35568104507071239695819683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47424139342761652927759577 35568104507071239695819683)
            ·
              refine ⟨53352156760606859543729525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35568104507071239695819683 53352156760606859543729525)
              ·
                refine ⟨5001764696306893082224643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53352156760606859543729525 5001764696306893082224643)
                ·
                  refine ⟨7502647044460339623336965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5001764696306893082224643 7502647044460339623336965)
                  ·
                    refine ⟨1406746320836313679375681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7502647044460339623336965 1406746320836313679375681)
                    ·
                      rfl

theorem cell22_4109443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 5, 1, 4].length) (baseStart_4109443 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4109443 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4109443 prefixEnd_4109443 := by exact prefixLift 4109443
  have htrace : WordTrace (prefixWord ++ tailWord_4109443) baseStart_4109443 baseEnd_4109443 := by
    simpa [prefixWord, tailWord_4109443, baseEnd_4109443] using wordTrace_append hprefix tailTrace_4109443
  have hstable : (prefixWord ++ tailWord_4109443).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4109443).length < 2 ^ (prefixWord ++ tailWord_4109443).sum := by decide
  have hdescent : baseEnd_4109443 < baseStart_4109443 := by decide
  rcases family_descends (prefixWord ++ tailWord_4109443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4109456 : List Nat := [2, 1, 1, 1, 1, 1, 4, 1, 5, 5]
def baseStart_4109456 : Nat := 118140960795 + 4109456 * 2 ^ 59
def prefixEnd_4109456 : Nat := 4983230072969 + 3 ^ 40 * 4109456 * 2
def baseEnd_4109456 : Nat := 1406750771001985978800641

theorem tailTrace_4109456 : CollatzResearch.WordTrace tailWord_4109456 prefixEnd_4109456 1406750771001985978800641 := by
  unfold tailWord_4109456
  simp only [CollatzResearch.WordTrace]
  refine ⟨74942086900075113026818111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99922782533433484035757481 74942086900075113026818111)
  ·
    refine ⟨112413130350112669540227167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74942086900075113026818111 112413130350112669540227167)
    ·
      refine ⟨168619695525169004310340751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112413130350112669540227167 168619695525169004310340751)
      ·
        refine ⟨252929543287753506465511127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168619695525169004310340751 252929543287753506465511127)
        ·
          refine ⟨379394314931630259698266691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252929543287753506465511127 379394314931630259698266691)
          ·
            refine ⟨569091472397445389547400037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 379394314931630259698266691 569091472397445389547400037)
            ·
              refine ⟨106704651074521010540137507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 569091472397445389547400037 106704651074521010540137507)
              ·
                refine ⟨160056976611781515810206261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106704651074521010540137507 160056976611781515810206261)
                ·
                  refine ⟨15005341557354517107206837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 160056976611781515810206261 15005341557354517107206837)
                  ·
                    refine ⟨1406750771001985978800641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15005341557354517107206837 1406750771001985978800641)
                    ·
                      rfl

theorem cell22_4109456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 5, 5].length) (baseStart_4109456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4109456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4109456 prefixEnd_4109456 := by exact prefixLift 4109456
  have htrace : WordTrace (prefixWord ++ tailWord_4109456) baseStart_4109456 baseEnd_4109456 := by
    simpa [prefixWord, tailWord_4109456, baseEnd_4109456] using wordTrace_append hprefix tailTrace_4109456
  have hstable : (prefixWord ++ tailWord_4109456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4109456).length < 2 ^ (prefixWord ++ tailWord_4109456).sum := by decide
  have hdescent : baseEnd_4109456 < baseStart_4109456 := by decide
  rcases family_descends (prefixWord ++ tailWord_4109456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4109473 : List Nat := [1, 2, 3, 3, 1, 1, 2, 3, 1, 5]
def baseStart_4109473 : Nat := 118140960795 + 4109473 * 2 ^ 59
def prefixEnd_4109473 : Nat := 4983230072969 + 3 ^ 40 * 4109473 * 2
def baseEnd_4109473 : Nat := 1406756590449403601125589

theorem tailTrace_4109473 : CollatzResearch.WordTrace tailWord_4109473 prefixEnd_4109473 1406756590449403601125589 := by
  unfold tailWord_4109473
  simp only [CollatzResearch.WordTrace]
  refine ⟨149884793841088637957005073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99923195894059091971336715 149884793841088637957005073)
  ·
    refine ⟨112413595380816478467753805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149884793841088637957005073 112413595380816478467753805)
    ·
      refine ⟨42155098267806179425407677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112413595380816478467753805 42155098267806179425407677)
      ·
        refine ⟨15808161850427317284527879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42155098267806179425407677 15808161850427317284527879)
        ·
          refine ⟨23712242775640975926791819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15808161850427317284527879 23712242775640975926791819)
          ·
            refine ⟨35568364163461463890187729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23712242775640975926791819 35568364163461463890187729)
            ·
              refine ⟨26676273122596097917640797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35568364163461463890187729 26676273122596097917640797)
              ·
                refine ⟨10003602420973536719115299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26676273122596097917640797 10003602420973536719115299)
                ·
                  refine ⟨15005403631460305078672949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10003602420973536719115299 15005403631460305078672949)
                  ·
                    refine ⟨1406756590449403601125589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15005403631460305078672949 1406756590449403601125589)
                    ·
                      rfl

theorem cell22_4109473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 3, 1, 5].length) (baseStart_4109473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4109473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4109473 prefixEnd_4109473 := by exact prefixLift 4109473
  have htrace : WordTrace (prefixWord ++ tailWord_4109473) baseStart_4109473 baseEnd_4109473 := by
    simpa [prefixWord, tailWord_4109473, baseEnd_4109473] using wordTrace_append hprefix tailTrace_4109473
  have hstable : (prefixWord ++ tailWord_4109473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4109473).length < 2 ^ (prefixWord ++ tailWord_4109473).sum := by decide
  have hdescent : baseEnd_4109473 < baseStart_4109473 := by decide
  rcases family_descends (prefixWord ++ tailWord_4109473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4109582 : List Nat := [4, 1, 1, 2, 1, 4, 3, 1, 5]
def baseStart_4109582 : Nat := 118140960795 + 4109582 * 2 ^ 59
def prefixEnd_4109582 : Nat := 4983230072969 + 3 ^ 40 * 4109582 * 2
def baseEnd_4109582 : Nat := 468931301125654550050085

theorem tailTrace_4109582 : CollatzResearch.WordTrace tailWord_4109582 prefixEnd_4109582 468931301125654550050085 := by
  unfold tailWord_4109582
  simp only [CollatzResearch.WordTrace]
  refine ⟨18736096174711718696590375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99925846265129166381815333 18736096174711718696590375)
  ·
    refine ⟨28104144262067578044885563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18736096174711718696590375 28104144262067578044885563)
    ·
      refine ⟨42156216393101367067328345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28104144262067578044885563 42156216393101367067328345)
      ·
        refine ⟨31617162294826025300496259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42156216393101367067328345 31617162294826025300496259)
        ·
          refine ⟨47425743442239037950744389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31617162294826025300496259 47425743442239037950744389)
          ·
            refine ⟨8892326895419819615764573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47425743442239037950744389 8892326895419819615764573)
            ·
              refine ⟨3334622585782432355911715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8892326895419819615764573 3334622585782432355911715)
              ·
                refine ⟨5001933878673648533867573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3334622585782432355911715 5001933878673648533867573)
                ·
                  refine ⟨468931301125654550050085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5001933878673648533867573 468931301125654550050085)
                  ·
                    rfl

theorem cell22_4109582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 3, 1, 5].length) (baseStart_4109582 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4109582 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4109582 prefixEnd_4109582 := by exact prefixLift 4109582
  have htrace : WordTrace (prefixWord ++ tailWord_4109582) baseStart_4109582 baseEnd_4109582 := by
    simpa [prefixWord, tailWord_4109582, baseEnd_4109582] using wordTrace_append hprefix tailTrace_4109582
  have hstable : (prefixWord ++ tailWord_4109582).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4109582).length < 2 ^ (prefixWord ++ tailWord_4109582).sum := by decide
  have hdescent : baseEnd_4109582 < baseStart_4109582 := by decide
  rcases family_descends (prefixWord ++ tailWord_4109582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4109678 : List Nat := [4, 1, 2, 4, 1, 2, 2, 2, 4]
def baseStart_4109678 : Nat := 118140960795 + 4109678 * 2 ^ 59
def prefixEnd_4109678 : Nat := 4983230072969 + 3 ^ 40 * 4109678 * 2
def baseEnd_4109678 : Nat := 468942255379617133249987

theorem tailTrace_4109678 : CollatzResearch.WordTrace tailWord_4109678 prefixEnd_4109678 468942255379617133249987 := by
  unfold tailWord_4109678
  simp only [CollatzResearch.WordTrace]
  refine ⟨18736533850668244746027211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99928180536897305312145125 18736533850668244746027211)
  ·
    refine ⟨28104800776002367119040817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18736533850668244746027211 28104800776002367119040817)
    ·
      refine ⟨21078600582001775339280613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28104800776002367119040817 21078600582001775339280613)
      ·
        refine ⟨3952237609125332876115115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21078600582001775339280613 3952237609125332876115115)
        ·
          refine ⟨5928356413687999314172673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3952237609125332876115115 5928356413687999314172673)
          ·
            refine ⟨4446267310265999485629505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5928356413687999314172673 4446267310265999485629505)
            ·
              refine ⟨3334700482699499614222129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4446267310265999485629505 3334700482699499614222129)
              ·
                refine ⟨2501025362024624710666597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3334700482699499614222129 2501025362024624710666597)
                ·
                  refine ⟨468942255379617133249987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2501025362024624710666597 468942255379617133249987)
                  ·
                    rfl

theorem cell22_4109678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 2, 2, 4].length) (baseStart_4109678 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4109678 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4109678 prefixEnd_4109678 := by exact prefixLift 4109678
  have htrace : WordTrace (prefixWord ++ tailWord_4109678) baseStart_4109678 baseEnd_4109678 := by
    simpa [prefixWord, tailWord_4109678, baseEnd_4109678] using wordTrace_append hprefix tailTrace_4109678
  have hstable : (prefixWord ++ tailWord_4109678).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4109678).length < 2 ^ (prefixWord ++ tailWord_4109678).sum := by decide
  have hdescent : baseEnd_4109678 < baseStart_4109678 := by decide
  rcases family_descends (prefixWord ++ tailWord_4109678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4109764 : List Nat := [2, 3, 3, 2, 1, 1, 1, 4, 1, 4]
def baseStart_4109764 : Nat := 118140960795 + 4109764 * 2 ^ 59
def prefixEnd_4109764 : Nat := 4983230072969 + 3 ^ 40 * 4109764 * 2
def baseEnd_4109764 : Nat := 1406856205696375842099697

theorem tailTrace_4109764 : CollatzResearch.WordTrace tailWord_4109764 prefixEnd_4109764 1406856205696375842099697 := by
  unfold tailWord_4109764
  simp only [CollatzResearch.WordTrace]
  refine ⟨74947703741517197327924173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99930271655356263103898897 74947703741517197327924173)
  ·
    refine ⟨28105388903068948997971565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74947703741517197327924173 28105388903068948997971565)
    ·
      refine ⟨10539520838650855874239337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28105388903068948997971565 10539520838650855874239337)
      ·
        refine ⟨7904640628988141905679503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10539520838650855874239337 7904640628988141905679503)
        ·
          refine ⟨11856960943482212858519255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7904640628988141905679503 11856960943482212858519255)
          ·
            refine ⟨17785441415223319287778883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11856960943482212858519255 17785441415223319287778883)
            ·
              refine ⟨26678162122834978931668325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17785441415223319287778883 26678162122834978931668325)
              ·
                refine ⟨5002155398031558549687811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26678162122834978931668325 5002155398031558549687811)
                ·
                  refine ⟨7503233097047337824531717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5002155398031558549687811 7503233097047337824531717)
                  ·
                    refine ⟨1406856205696375842099697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7503233097047337824531717 1406856205696375842099697)
                    ·
                      rfl

theorem cell22_4109764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_4109764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4109764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4109764 prefixEnd_4109764 := by exact prefixLift 4109764
  have htrace : WordTrace (prefixWord ++ tailWord_4109764) baseStart_4109764 baseEnd_4109764 := by
    simpa [prefixWord, tailWord_4109764, baseEnd_4109764] using wordTrace_append hprefix tailTrace_4109764
  have hstable : (prefixWord ++ tailWord_4109764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4109764).length < 2 ^ (prefixWord ++ tailWord_4109764).sum := by decide
  have hdescent : baseEnd_4109764 < baseStart_4109764 := by decide
  rcases family_descends (prefixWord ++ tailWord_4109764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4109775 : List Nat := [1, 1, 2, 1, 1, 4, 4, 1, 1, 6]
def baseStart_4109775 : Nat := 118140960795 + 4109775 * 2 ^ 59
def prefixEnd_4109775 : Nat := 4983230072969 + 3 ^ 40 * 4109775 * 2
def baseEnd_4109775 : Nat := 1406859971221175480074663

theorem tailTrace_4109775 : CollatzResearch.WordTrace tailWord_4109775 prefixEnd_4109775 1406859971221175480074663 := by
  unfold tailWord_4109775
  simp only [CollatzResearch.WordTrace]
  refine ⟨149895808685994543534498779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99930539123996362356332519 149895808685994543534498779)
  ·
    refine ⟨224843713028991815301748169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149895808685994543534498779 224843713028991815301748169)
    ·
      refine ⟨168632784771743861476311127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224843713028991815301748169 168632784771743861476311127)
      ·
        refine ⟨252949177157615792214466691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168632784771743861476311127 252949177157615792214466691)
        ·
          refine ⟨379423765736423688321700037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252949177157615792214466691 379423765736423688321700037)
          ·
            refine ⟨71141956075579441560318757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 379423765736423688321700037 71141956075579441560318757)
            ·
              refine ⟨13339116764171145292559767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71141956075579441560318757 13339116764171145292559767)
              ·
                refine ⟨20008675146256717938839651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13339116764171145292559767 20008675146256717938839651)
                ·
                  refine ⟨30013012719385076908259477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20008675146256717938839651 30013012719385076908259477)
                  ·
                    refine ⟨1406859971221175480074663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30013012719385076908259477 1406859971221175480074663)
                    ·
                      rfl

theorem cell22_4109775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 1, 1, 6].length) (baseStart_4109775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4109775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4109775 prefixEnd_4109775 := by exact prefixLift 4109775
  have htrace : WordTrace (prefixWord ++ tailWord_4109775) baseStart_4109775 baseEnd_4109775 := by
    simpa [prefixWord, tailWord_4109775, baseEnd_4109775] using wordTrace_append hprefix tailTrace_4109775
  have hstable : (prefixWord ++ tailWord_4109775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4109775).length < 2 ^ (prefixWord ++ tailWord_4109775).sum := by decide
  have hdescent : baseEnd_4109775 < baseStart_4109775 := by decide
  rcases family_descends (prefixWord ++ tailWord_4109775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4109826 : List Nat := [3, 4, 1, 2, 1, 2, 2, 1, 2, 4]
def baseStart_4109826 : Nat := 118140960795 + 4109826 * 2 ^ 59
def prefixEnd_4109826 : Nat := 4983230072969 + 3 ^ 40 * 4109826 * 2
def baseEnd_4109826 : Nat := 1406877429563428347049507

theorem tailTrace_4109826 : CollatzResearch.WordTrace tailWord_4109826 prefixEnd_4109826 1406877429563428347049507 := by
  unfold tailWord_4109826
  simp only [CollatzResearch.WordTrace]
  refine ⟨37474417202202444811151333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99931779205873186163070221 37474417202202444811151333)
  ·
    refine ⟨7026453225412958402090875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37474417202202444811151333 7026453225412958402090875)
    ·
      refine ⟨10539679838119437603136313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7026453225412958402090875 10539679838119437603136313)
      ·
        refine ⟨7904759878589578202352235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10539679838119437603136313 7904759878589578202352235)
        ·
          refine ⟨11857139817884367303528353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7904759878589578202352235 11857139817884367303528353)
          ·
            refine ⟨8892854863413275477646265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11857139817884367303528353 8892854863413275477646265)
            ·
              refine ⟨6669641147559956608234699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8892854863413275477646265 6669641147559956608234699)
              ·
                refine ⟨10004461721339934912352049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6669641147559956608234699 10004461721339934912352049)
                ·
                  refine ⟨7503346291004951184264037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10004461721339934912352049 7503346291004951184264037)
                  ·
                    refine ⟨1406877429563428347049507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7503346291004951184264037 1406877429563428347049507)
                    ·
                      rfl

theorem cell22_4109826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_4109826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4109826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4109826 prefixEnd_4109826 := by exact prefixLift 4109826
  have htrace : WordTrace (prefixWord ++ tailWord_4109826) baseStart_4109826 baseEnd_4109826 := by
    simpa [prefixWord, tailWord_4109826, baseEnd_4109826] using wordTrace_append hprefix tailTrace_4109826
  have hstable : (prefixWord ++ tailWord_4109826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4109826).length < 2 ^ (prefixWord ++ tailWord_4109826).sum := by decide
  have hdescent : baseEnd_4109826 < baseStart_4109826 := by decide
  rcases family_descends (prefixWord ++ tailWord_4109826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4109882 : List Nat := [3, 1, 1, 1, 3, 2, 1, 3, 3, 4]
def baseStart_4109882 : Nat := 118140960795 + 4109882 * 2 ^ 59
def prefixEnd_4109882 : Nat := 4983230072969 + 3 ^ 40 * 4109882 * 2
def baseEnd_4109882 : Nat := 1406896599507862867649335

theorem tailTrace_4109882 : CollatzResearch.WordTrace tailWord_4109882 prefixEnd_4109882 1406896599507862867649335 := by
  unfold tailWord_4109882
  simp only [CollatzResearch.WordTrace]
  refine ⟨37474927824151725202160975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99933140864404600539095933 37474927824151725202160975)
  ·
    refine ⟨56212391736227587803241463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37474927824151725202160975 56212391736227587803241463)
    ·
      refine ⟨84318587604341381704862195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56212391736227587803241463 84318587604341381704862195)
      ·
        refine ⟨126477881406512072557293293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84318587604341381704862195 126477881406512072557293293)
        ·
          refine ⟨47429205527442027208984985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126477881406512072557293293 47429205527442027208984985)
          ·
            refine ⟨35571904145581520406738739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47429205527442027208984985 35571904145581520406738739)
            ·
              refine ⟨53357856218372280610108109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35571904145581520406738739 53357856218372280610108109)
              ·
                refine ⟨20009196081889605228790541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53357856218372280610108109 20009196081889605228790541)
                ·
                  refine ⟨7503448530708601960796453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20009196081889605228790541 7503448530708601960796453)
                  ·
                    refine ⟨1406896599507862867649335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7503448530708601960796453 1406896599507862867649335)
                    ·
                      rfl

theorem cell22_4109882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 3, 3, 4].length) (baseStart_4109882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4109882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4109882 prefixEnd_4109882 := by exact prefixLift 4109882
  have htrace : WordTrace (prefixWord ++ tailWord_4109882) baseStart_4109882 baseEnd_4109882 := by
    simpa [prefixWord, tailWord_4109882, baseEnd_4109882] using wordTrace_append hprefix tailTrace_4109882
  have hstable : (prefixWord ++ tailWord_4109882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4109882).length < 2 ^ (prefixWord ++ tailWord_4109882).sum := by decide
  have hdescent : baseEnd_4109882 < baseStart_4109882 := by decide
  rcases family_descends (prefixWord ++ tailWord_4109882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4109927 : List Nat := [1, 1, 5, 1, 1, 1, 3, 2, 1, 6]
def baseStart_4109927 : Nat := 118140960795 + 4109927 * 2 ^ 59
def prefixEnd_4109927 : Nat := 4983230072969 + 3 ^ 40 * 4109927 * 2
def baseEnd_4109927 : Nat := 1406912003927497750274197

theorem tailTrace_4109927 : CollatzResearch.WordTrace tailWord_4109927 prefixEnd_4109927 1406912003927497750274197 := by
  unfold tailWord_4109927
  simp only [CollatzResearch.WordTrace]
  refine ⟨149901352581443873494032035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99934235054295915662688023 149901352581443873494032035)
  ·
    refine ⟨224852028872165810241048053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149901352581443873494032035 224852028872165810241048053)
    ·
      refine ⟨21079877706765544710098255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 224852028872165810241048053 21079877706765544710098255)
      ·
        refine ⟨31619816560148317065147383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21079877706765544710098255 31619816560148317065147383)
        ·
          refine ⟨47429724840222475597721075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31619816560148317065147383 47429724840222475597721075)
          ·
            refine ⟨71144587260333713396581613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47429724840222475597721075 71144587260333713396581613)
            ·
              refine ⟨26679220222625142523718105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71144587260333713396581613 26679220222625142523718105)
              ·
                refine ⟨20009415166968856892788579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26679220222625142523718105 20009415166968856892788579)
                ·
                  refine ⟨30014122750453285339182869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20009415166968856892788579 30014122750453285339182869)
                  ·
                    refine ⟨1406912003927497750274197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30014122750453285339182869 1406912003927497750274197)
                    ·
                      rfl

theorem cell22_4109927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 2, 1, 6].length) (baseStart_4109927 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4109927 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4109927 prefixEnd_4109927 := by exact prefixLift 4109927
  have htrace : WordTrace (prefixWord ++ tailWord_4109927) baseStart_4109927 baseEnd_4109927 := by
    simpa [prefixWord, tailWord_4109927, baseEnd_4109927] using wordTrace_append hprefix tailTrace_4109927
  have hstable : (prefixWord ++ tailWord_4109927).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4109927).length < 2 ^ (prefixWord ++ tailWord_4109927).sum := by decide
  have hdescent : baseEnd_4109927 < baseStart_4109927 := by decide
  rcases family_descends (prefixWord ++ tailWord_4109927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4109929 : List Nat := [1, 2, 1, 1, 1, 4, 2, 5, 2, 3]
def baseStart_4109929 : Nat := 118140960795 + 4109929 * 2 ^ 59
def prefixEnd_4109929 : Nat := 4983230072969 + 3 ^ 40 * 4109929 * 2
def baseEnd_4109929 : Nat := 1406912688568370411724191

theorem tailTrace_4109929 : CollatzResearch.WordTrace tailWord_4109929 prefixEnd_4109929 1406912688568370411724191 := by
  unfold tailWord_4109929
  simp only [CollatzResearch.WordTrace]
  refine ⟨149901425527436627835604841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99934283684957751890403227 149901425527436627835604841)
  ·
    refine ⟨112426069145577470876703631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149901425527436627835604841 112426069145577470876703631)
    ·
      refine ⟨168639103718366206315055447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112426069145577470876703631 168639103718366206315055447)
      ·
        refine ⟨252958655577549309472583171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168639103718366206315055447 252958655577549309472583171)
        ·
          refine ⟨379437983366323964208874757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252958655577549309472583171 379437983366323964208874757)
          ·
            refine ⟨71144621881185743289164017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 379437983366323964208874757 71144621881185743289164017)
            ·
              refine ⟨53358466410889307466873013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71144621881185743289164017 53358466410889307466873013)
              ·
                refine ⟨5002356226020872575019345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53358466410889307466873013 5002356226020872575019345)
                ·
                  refine ⟨3751767169515654431264509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5002356226020872575019345 3751767169515654431264509)
                  ·
                    refine ⟨1406912688568370411724191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3751767169515654431264509 1406912688568370411724191)
                    ·
                      rfl

theorem cell22_4109929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 5, 2, 3].length) (baseStart_4109929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4109929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4109929 prefixEnd_4109929 := by exact prefixLift 4109929
  have htrace : WordTrace (prefixWord ++ tailWord_4109929) baseStart_4109929 baseEnd_4109929 := by
    simpa [prefixWord, tailWord_4109929, baseEnd_4109929] using wordTrace_append hprefix tailTrace_4109929
  have hstable : (prefixWord ++ tailWord_4109929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4109929).length < 2 ^ (prefixWord ++ tailWord_4109929).sum := by decide
  have hdescent : baseEnd_4109929 < baseStart_4109929 := by decide
  rcases family_descends (prefixWord ++ tailWord_4109929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4109980 : List Nat := [2, 2, 3, 2, 3, 2, 2, 1, 2, 3]
def baseStart_4109980 : Nat := 118140960795 + 4109980 * 2 ^ 59
def prefixEnd_4109980 : Nat := 4983230072969 + 3 ^ 40 * 4109980 * 2
def baseEnd_4109980 : Nat := 1406930146910623278699035

theorem tailTrace_4109980 : CollatzResearch.WordTrace tailWord_4109980 prefixEnd_4109980 1406930146910623278699035 := by
  unfold tailWord_4109980
  simp only [CollatzResearch.WordTrace]
  refine ⟨74951642825125931772855697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99935523766834575697140929 74951642825125931772855697)
  ·
    refine ⟨56213732118844448829641773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74951642825125931772855697 56213732118844448829641773)
    ·
      refine ⟨21080149544566668311115665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56213732118844448829641773 21080149544566668311115665)
      ·
        refine ⟨15810112158425001233336749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21080149544566668311115665 15810112158425001233336749)
        ·
          refine ⟨5928792059409375462501281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15810112158425001233336749 5928792059409375462501281)
          ·
            refine ⟨4446594044557031596875961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5928792059409375462501281 4446594044557031596875961)
            ·
              refine ⟨3334945533417773697656971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4446594044557031596875961 3334945533417773697656971)
              ·
                refine ⟨5002418300126660546485457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3334945533417773697656971 5002418300126660546485457)
                ·
                  refine ⟨3751813725094995409864093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5002418300126660546485457 3751813725094995409864093)
                  ·
                    refine ⟨1406930146910623278699035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3751813725094995409864093 1406930146910623278699035)
                    ·
                      rfl

theorem cell22_4109980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 2, 1, 2, 3].length) (baseStart_4109980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4109980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4109980 prefixEnd_4109980 := by exact prefixLift 4109980
  have htrace : WordTrace (prefixWord ++ tailWord_4109980) baseStart_4109980 baseEnd_4109980 := by
    simpa [prefixWord, tailWord_4109980, baseEnd_4109980] using wordTrace_append hprefix tailTrace_4109980
  have hstable : (prefixWord ++ tailWord_4109980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4109980).length < 2 ^ (prefixWord ++ tailWord_4109980).sum := by decide
  have hdescent : baseEnd_4109980 < baseStart_4109980 := by decide
  rcases family_descends (prefixWord ++ tailWord_4109980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4110036 : List Nat := [2, 4, 1, 3, 1, 2, 1, 1, 2, 5]
def baseStart_4110036 : Nat := 118140960795 + 4110036 * 2 ^ 59
def prefixEnd_4110036 : Nat := 4983230072969 + 3 ^ 40 * 4110036 * 2
def baseEnd_4110036 : Nat := 1406949316855057799298863

theorem tailTrace_4110036 : CollatzResearch.WordTrace tailWord_4110036 prefixEnd_4110036 1406949316855057799298863 := by
  unfold tailWord_4110036
  simp only [CollatzResearch.WordTrace]
  refine ⟨74952664069024492554874981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99936885425365990073166641 74952664069024492554874981)
  ·
    refine ⟨14053624512942092354039059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74952664069024492554874981 14053624512942092354039059)
    ·
      refine ⟨21080436769413138531058589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14053624512942092354039059 21080436769413138531058589)
      ·
        refine ⟨7905163788529926949146971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21080436769413138531058589 7905163788529926949146971)
        ·
          refine ⟨11857745682794890423720457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7905163788529926949146971 11857745682794890423720457)
          ·
            refine ⟨8893309262096167817790343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11857745682794890423720457 8893309262096167817790343)
            ·
              refine ⟨13339963893144251726685515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8893309262096167817790343 13339963893144251726685515)
              ·
                refine ⟨20009945839716377590028273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13339963893144251726685515 20009945839716377590028273)
                ·
                  refine ⟨15007459379787283192521205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20009945839716377590028273 15007459379787283192521205)
                  ·
                    refine ⟨1406949316855057799298863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15007459379787283192521205 1406949316855057799298863)
                    ·
                      rfl

theorem cell22_4110036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 1, 2, 5].length) (baseStart_4110036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4110036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4110036 prefixEnd_4110036 := by exact prefixLift 4110036
  have htrace : WordTrace (prefixWord ++ tailWord_4110036) baseStart_4110036 baseEnd_4110036 := by
    simpa [prefixWord, tailWord_4110036, baseEnd_4110036] using wordTrace_append hprefix tailTrace_4110036
  have hstable : (prefixWord ++ tailWord_4110036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4110036).length < 2 ^ (prefixWord ++ tailWord_4110036).sum := by decide
  have hdescent : baseEnd_4110036 < baseStart_4110036 := by decide
  rcases family_descends (prefixWord ++ tailWord_4110036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4110079 : List Nat := [1, 1, 2, 2, 1, 3, 2, 4, 2, 4]
def baseStart_4110079 : Nat := 118140960795 + 4110079 * 2 ^ 59
def prefixEnd_4110079 : Nat := 4983230072969 + 3 ^ 40 * 4110079 * 2
def baseEnd_4110079 : Nat := 1406964036633820020473731

theorem tailTrace_4110079 : CollatzResearch.WordTrace tailWord_4110079 prefixEnd_4110079 1406964036633820020473731 := by
  unfold tailWord_4110079
  simp only [CollatzResearch.WordTrace]
  refine ⟨149906896476893203453565291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99937930984595468969043527 149906896476893203453565291)
  ·
    refine ⟨224860344715339805180347937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149906896476893203453565291 224860344715339805180347937)
    ·
      refine ⟨168645258536504853885260953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224860344715339805180347937 168645258536504853885260953)
      ·
        refine ⟨126483943902378640413945715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168645258536504853885260953 126483943902378640413945715)
        ·
          refine ⟨189725915853567960620918573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126483943902378640413945715 189725915853567960620918573)
          ·
            refine ⟨71147218445087985232844465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 189725915853567960620918573 71147218445087985232844465)
            ·
              refine ⟨53360413833815988924633349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71147218445087985232844465 53360413833815988924633349)
              ·
                refine ⟨10005077593840497923368753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53360413833815988924633349 10005077593840497923368753)
                ·
                  refine ⟨7503808195380373442526565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10005077593840497923368753 7503808195380373442526565)
                  ·
                    refine ⟨1406964036633820020473731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7503808195380373442526565 1406964036633820020473731)
                    ·
                      rfl

theorem cell22_4110079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 4, 2, 4].length) (baseStart_4110079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4110079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4110079 prefixEnd_4110079 := by exact prefixLift 4110079
  have htrace : WordTrace (prefixWord ++ tailWord_4110079) baseStart_4110079 baseEnd_4110079 := by
    simpa [prefixWord, tailWord_4110079, baseEnd_4110079] using wordTrace_append hprefix tailTrace_4110079
  have hstable : (prefixWord ++ tailWord_4110079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4110079).length < 2 ^ (prefixWord ++ tailWord_4110079).sum := by decide
  have hdescent : baseEnd_4110079 < baseStart_4110079 := by decide
  rcases family_descends (prefixWord ++ tailWord_4110079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4110098 : List Nat := [3, 2, 4, 1, 1, 1, 3, 1, 1, 5]
def baseStart_4110098 : Nat := 118140960795 + 4110098 * 2 ^ 59
def prefixEnd_4110098 : Nat := 4983230072969 + 3 ^ 40 * 4110098 * 2
def baseEnd_4110098 : Nat := 1406970540722110304248673

theorem tailTrace_4110098 : CollatzResearch.WordTrace tailWord_4110098 prefixEnd_4110098 1406970540722110304248673 := by
  unfold tailWord_4110098
  simp only [CollatzResearch.WordTrace]
  refine ⟨37476897365956092424626737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99938392975882913132337965 37476897365956092424626737)
  ·
    refine ⟨28107673024467069318470053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37476897365956092424626737 28107673024467069318470053)
    ·
      refine ⟨5270188692087575497213135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28107673024467069318470053 5270188692087575497213135)
      ·
        refine ⟨7905283038131363245819703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5270188692087575497213135 7905283038131363245819703)
        ·
          refine ⟨11857924557197044868729555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7905283038131363245819703 11857924557197044868729555)
          ·
            refine ⟨17786886835795567303094333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11857924557197044868729555 17786886835795567303094333)
            ·
              refine ⟨6670082563423337738660375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17786886835795567303094333 6670082563423337738660375)
              ·
                refine ⟨10005123845135006607990563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6670082563423337738660375 10005123845135006607990563)
                ·
                  refine ⟨15007685767702509911985845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10005123845135006607990563 15007685767702509911985845)
                  ·
                    refine ⟨1406970540722110304248673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15007685767702509911985845 1406970540722110304248673)
                    ·
                      rfl

theorem cell22_4110098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_4110098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4110098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4110098 prefixEnd_4110098 := by exact prefixLift 4110098
  have htrace : WordTrace (prefixWord ++ tailWord_4110098) baseStart_4110098 baseEnd_4110098 := by
    simpa [prefixWord, tailWord_4110098, baseEnd_4110098] using wordTrace_append hprefix tailTrace_4110098
  have hstable : (prefixWord ++ tailWord_4110098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4110098).length < 2 ^ (prefixWord ++ tailWord_4110098).sum := by decide
  have hdescent : baseEnd_4110098 < baseStart_4110098 := by decide
  rcases family_descends (prefixWord ++ tailWord_4110098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4110154 : List Nat := [3, 1, 2, 1, 1, 1, 4, 1, 1, 7]
def baseStart_4110154 : Nat := 118140960795 + 4110154 * 2 ^ 59
def prefixEnd_4110154 : Nat := 4983230072969 + 3 ^ 40 * 4110154 * 2
def baseEnd_4110154 : Nat := 1406989710666544824848501

theorem tailTrace_4110154 : CollatzResearch.WordTrace tailWord_4110154 prefixEnd_4110154 1406989710666544824848501 := by
  unfold tailWord_4110154
  simp only [CollatzResearch.WordTrace]
  refine ⟨37477407987905372815636379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99939754634414327508363677 37477407987905372815636379)
  ·
    refine ⟨56216111981858059223454569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37477407987905372815636379 56216111981858059223454569)
    ·
      refine ⟨42162083986393544417590927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56216111981858059223454569 42162083986393544417590927)
      ·
        refine ⟨63243125979590316626386391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42162083986393544417590927 63243125979590316626386391)
        ·
          refine ⟨94864688969385474939579587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63243125979590316626386391 94864688969385474939579587)
          ·
            refine ⟨142297033454078212409369381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94864688969385474939579587 142297033454078212409369381)
            ·
              refine ⟨26680693772639664826756759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 142297033454078212409369381 26680693772639664826756759)
              ·
                refine ⟨40021040658959497240135139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26680693772639664826756759 40021040658959497240135139)
                ·
                  refine ⟨60031560988439245860202709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40021040658959497240135139 60031560988439245860202709)
                  ·
                    refine ⟨1406989710666544824848501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60031560988439245860202709 1406989710666544824848501)
                    ·
                      rfl

theorem cell22_4110154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 1, 1, 7].length) (baseStart_4110154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4110154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4110154 prefixEnd_4110154 := by exact prefixLift 4110154
  have htrace : WordTrace (prefixWord ++ tailWord_4110154) baseStart_4110154 baseEnd_4110154 := by
    simpa [prefixWord, tailWord_4110154, baseEnd_4110154] using wordTrace_append hprefix tailTrace_4110154
  have hstable : (prefixWord ++ tailWord_4110154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4110154).length < 2 ^ (prefixWord ++ tailWord_4110154).sum := by decide
  have hdescent : baseEnd_4110154 < baseStart_4110154 := by decide
  rcases family_descends (prefixWord ++ tailWord_4110154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4110218 : List Nat := [3, 1, 2, 4, 2, 1, 1, 2, 6]
def baseStart_4110218 : Nat := 118140960795 + 4110218 * 2 ^ 59
def prefixEnd_4110218 : Nat := 4983230072969 + 3 ^ 40 * 4110218 * 2
def baseEnd_4110218 : Nat := 469003873058156663749435

theorem tailTrace_4110218 : CollatzResearch.WordTrace tailWord_4110218 prefixEnd_4110218 469003873058156663749435 := by
  unfold tailWord_4110218
  simp only [CollatzResearch.WordTrace]
  refine ⟨37477991555847407548218827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99941310815593086795250205 37477991555847407548218827)
  ·
    refine ⟨56216987333771111322328241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37477991555847407548218827 56216987333771111322328241)
    ·
      refine ⟨42162740500328333491746181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56216987333771111322328241 42162740500328333491746181)
      ·
        refine ⟨7905513843811562529702409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42162740500328333491746181 7905513843811562529702409)
        ·
          refine ⟨5929135382858671897276807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7905513843811562529702409 5929135382858671897276807)
          ·
            refine ⟨8893703074288007845915211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5929135382858671897276807 8893703074288007845915211)
            ·
              refine ⟨13340554611432011768872817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8893703074288007845915211 13340554611432011768872817)
              ·
                refine ⟨10005415958574008826654613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13340554611432011768872817 10005415958574008826654613)
                ·
                  refine ⟨469003873058156663749435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10005415958574008826654613 469003873058156663749435)
                  ·
                    rfl

theorem cell22_4110218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 2, 6].length) (baseStart_4110218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4110218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4110218 prefixEnd_4110218 := by exact prefixLift 4110218
  have htrace : WordTrace (prefixWord ++ tailWord_4110218) baseStart_4110218 baseEnd_4110218 := by
    simpa [prefixWord, tailWord_4110218, baseEnd_4110218] using wordTrace_append hprefix tailTrace_4110218
  have hstable : (prefixWord ++ tailWord_4110218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4110218).length < 2 ^ (prefixWord ++ tailWord_4110218).sum := by decide
  have hdescent : baseEnd_4110218 < baseStart_4110218 := by decide
  rcases family_descends (prefixWord ++ tailWord_4110218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4110231 : List Nat := [1, 1, 3, 3, 1, 4, 1, 1, 1, 6]
def baseStart_4110231 : Nat := 118140960795 + 4110231 * 2 ^ 59
def prefixEnd_4110231 : Nat := 4983230072969 + 3 ^ 40 * 4110231 * 2
def baseEnd_4110231 : Nat := 1407016069340142290673265

theorem tailTrace_4110231 : CollatzResearch.WordTrace tailWord_4110231 prefixEnd_4110231 1407016069340142290673265 := by
  unfold tailWord_4110231
  simp only [CollatzResearch.WordTrace]
  refine ⟨149912440372342533413098547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99941626914895022275399031 149912440372342533413098547)
  ·
    refine ⟨224868660558513800119647821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149912440372342533413098547 224868660558513800119647821)
    ·
      refine ⟨84325747709442675044867933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224868660558513800119647821 84325747709442675044867933)
      ·
        refine ⟨31622155391041003141825475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84325747709442675044867933 31622155391041003141825475)
        ·
          refine ⟨47433233086561504712738213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31622155391041003141825475 47433233086561504712738213)
          ·
            refine ⟨8893731203730282133638415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47433233086561504712738213 8893731203730282133638415)
            ·
              refine ⟨13340596805595423200457623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8893731203730282133638415 13340596805595423200457623)
              ·
                refine ⟨20010895208393134800686435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13340596805595423200457623 20010895208393134800686435)
                ·
                  refine ⟨30016342812589702201029653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20010895208393134800686435 30016342812589702201029653)
                  ·
                    refine ⟨1407016069340142290673265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30016342812589702201029653 1407016069340142290673265)
                    ·
                      rfl

theorem cell22_4110231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 1, 1, 6].length) (baseStart_4110231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4110231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4110231 prefixEnd_4110231 := by exact prefixLift 4110231
  have htrace : WordTrace (prefixWord ++ tailWord_4110231) baseStart_4110231 baseEnd_4110231 := by
    simpa [prefixWord, tailWord_4110231, baseEnd_4110231] using wordTrace_append hprefix tailTrace_4110231
  have hstable : (prefixWord ++ tailWord_4110231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4110231).length < 2 ^ (prefixWord ++ tailWord_4110231).sum := by decide
  have hdescent : baseEnd_4110231 < baseStart_4110231 := by decide
  rcases family_descends (prefixWord ++ tailWord_4110231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4110370 : List Nat := [3, 3, 1, 1, 1, 2, 3, 4, 4]
def baseStart_4110370 : Nat := 118140960795 + 4110370 * 2 ^ 59
def prefixEnd_4110370 : Nat := 4983230072969 + 3 ^ 40 * 4110370 * 2
def baseEnd_4110370 : Nat := 469021217293597420482613

theorem tailTrace_4110370 : CollatzResearch.WordTrace tailWord_4110370 prefixEnd_4110370 469021217293597420482613 := by
  unfold tailWord_4110370
  simp only [CollatzResearch.WordTrace]
  refine ⟨37479377529709740038102141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99945006745892640101605709 37479377529709740038102141)
  ·
    refine ⟨14054766573641152514288303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37479377529709740038102141 14054766573641152514288303)
    ·
      refine ⟨21082149860461728771432455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14054766573641152514288303 21082149860461728771432455)
      ·
        refine ⟨31623224790692593157148683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21082149860461728771432455 31623224790692593157148683)
        ·
          refine ⟨47434837186038889735723025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31623224790692593157148683 47434837186038889735723025)
          ·
            refine ⟨35576127889529167301792269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47434837186038889735723025 35576127889529167301792269)
            ·
              refine ⟨13341047958573437738172101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35576127889529167301792269 13341047958573437738172101)
              ·
                refine ⟨2501446492232519575907269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13341047958573437738172101 2501446492232519575907269)
                ·
                  refine ⟨469021217293597420482613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2501446492232519575907269 469021217293597420482613)
                  ·
                    rfl

theorem cell22_4110370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 4, 4].length) (baseStart_4110370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4110370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4110370 prefixEnd_4110370 := by exact prefixLift 4110370
  have htrace : WordTrace (prefixWord ++ tailWord_4110370) baseStart_4110370 baseEnd_4110370 := by
    simpa [prefixWord, tailWord_4110370, baseEnd_4110370] using wordTrace_append hprefix tailTrace_4110370
  have hstable : (prefixWord ++ tailWord_4110370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4110370).length < 2 ^ (prefixWord ++ tailWord_4110370).sum := by decide
  have hdescent : baseEnd_4110370 < baseStart_4110370 := by decide
  rcases family_descends (prefixWord ++ tailWord_4110370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4110385 : List Nat := [1, 2, 2, 3, 1, 3, 2, 3, 2, 3]
def baseStart_4110385 : Nat := 118140960795 + 4110385 * 2 ^ 59
def prefixEnd_4110385 : Nat := 4983230072969 + 3 ^ 40 * 4110385 * 2
def baseEnd_4110385 : Nat := 1407068786687337222322793

theorem tailTrace_4110385 : CollatzResearch.WordTrace tailWord_4110385 prefixEnd_4110385 1407068786687337222322793 := by
  unfold tailWord_4110385
  simp only [CollatzResearch.WordTrace]
  refine ⟨149918057213784617714204609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99945371475856411809469739 149918057213784617714204609)
  ·
    refine ⟨112438542910338463285653457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149918057213784617714204609 112438542910338463285653457)
    ·
      refine ⟨84328907182753847464240093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112438542910338463285653457 84328907182753847464240093)
      ·
        refine ⟨31623340193532692799090035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84328907182753847464240093 31623340193532692799090035)
        ·
          refine ⟨47435010290299039198635053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31623340193532692799090035 47435010290299039198635053)
          ·
            refine ⟨17788128858862139699488145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47435010290299039198635053 17788128858862139699488145)
            ·
              refine ⟨13341096644146604774616109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17788128858862139699488145 13341096644146604774616109)
              ·
                refine ⟨5002911241554976790481041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13341096644146604774616109 5002911241554976790481041)
                ·
                  refine ⟨3752183431166232592860781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5002911241554976790481041 3752183431166232592860781)
                  ·
                    refine ⟨1407068786687337222322793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3752183431166232592860781 1407068786687337222322793)
                    ·
                      rfl

theorem cell22_4110385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 3, 2, 3].length) (baseStart_4110385 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4110385 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4110385 prefixEnd_4110385 := by exact prefixLift 4110385
  have htrace : WordTrace (prefixWord ++ tailWord_4110385) baseStart_4110385 baseEnd_4110385 := by
    simpa [prefixWord, tailWord_4110385, baseEnd_4110385] using wordTrace_append hprefix tailTrace_4110385
  have hstable : (prefixWord ++ tailWord_4110385).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4110385).length < 2 ^ (prefixWord ++ tailWord_4110385).sum := by decide
  have hdescent : baseEnd_4110385 < baseStart_4110385 := by decide
  rcases family_descends (prefixWord ++ tailWord_4110385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4110400 : List Nat := [2, 1, 1, 2, 2, 6, 1, 1, 2, 4]
def baseStart_4110400 : Nat := 118140960795 + 4110400 * 2 ^ 59
def prefixEnd_4110400 : Nat := 4983230072969 + 3 ^ 40 * 4110400 * 2
def baseEnd_4110400 : Nat := 1407073921493882183197747

theorem tailTrace_4110400 : CollatzResearch.WordTrace tailWord_4110400 prefixEnd_4110400 1407073921493882183197747 := by
  unfold tailWord_4110400
  simp only [CollatzResearch.WordTrace]
  refine ⟨74959302154365137638000327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99945736205820183517333769 74959302154365137638000327)
  ·
    refine ⟨112438953231547706457000491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74959302154365137638000327 112438953231547706457000491)
    ·
      refine ⟨168658429847321559685500737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112438953231547706457000491 168658429847321559685500737)
      ·
        refine ⟨126493822385491169764125553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168658429847321559685500737 126493822385491169764125553)
        ·
          refine ⟨94870366789118377323094165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126493822385491169764125553 94870366789118377323094165)
          ·
            refine ⟨4447048443239923937020039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 94870366789118377323094165 4447048443239923937020039)
            ·
              refine ⟨6670572664859885905530059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4447048443239923937020039 6670572664859885905530059)
              ·
                refine ⟨10005858997289828858295089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6670572664859885905530059 10005858997289828858295089)
                ·
                  refine ⟨7504394247967371643721317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10005858997289828858295089 7504394247967371643721317)
                  ·
                    refine ⟨1407073921493882183197747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7504394247967371643721317 1407073921493882183197747)
                    ·
                      rfl

theorem cell22_4110400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 1, 1, 2, 4].length) (baseStart_4110400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4110400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4110400 prefixEnd_4110400 := by exact prefixLift 4110400
  have htrace : WordTrace (prefixWord ++ tailWord_4110400) baseStart_4110400 baseEnd_4110400 := by
    simpa [prefixWord, tailWord_4110400, baseEnd_4110400] using wordTrace_append hprefix tailTrace_4110400
  have hstable : (prefixWord ++ tailWord_4110400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4110400).length < 2 ^ (prefixWord ++ tailWord_4110400).sum := by decide
  have hdescent : baseEnd_4110400 < baseStart_4110400 := by decide
  rcases family_descends (prefixWord ++ tailWord_4110400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4110411 : List Nat := [1, 1, 1, 1, 3, 1, 2, 2, 4, 6]
def baseStart_4110411 : Nat := 118140960795 + 4110411 * 2 ^ 59
def prefixEnd_4110411 : Nat := 4983230072969 + 3 ^ 40 * 4110411 * 2
def baseEnd_4110411 : Nat := 1407077687018681821172713

theorem tailTrace_4110411 : CollatzResearch.WordTrace tailWord_4110411 prefixEnd_4110411 1407077687018681821172713 := by
  unfold tailWord_4110411
  simp only [CollatzResearch.WordTrace]
  refine ⟨149919005511690424154651087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99946003674460282769767391 149919005511690424154651087)
  ·
    refine ⟨224878508267535636231976631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149919005511690424154651087 224878508267535636231976631)
    ·
      refine ⟨337317762401303454347964947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224878508267535636231976631 337317762401303454347964947)
      ·
        refine ⟨505976643601955181521947421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337317762401303454347964947 505976643601955181521947421)
        ·
          refine ⟨189741241350733193070730283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 505976643601955181521947421 189741241350733193070730283)
          ·
            refine ⟨284611862026099789606095425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189741241350733193070730283 284611862026099789606095425)
            ·
              refine ⟨213458896519574842204571569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 284611862026099789606095425 213458896519574842204571569)
              ·
                refine ⟨160094172389681131653428677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 213458896519574842204571569 160094172389681131653428677)
                ·
                  refine ⟨30017657323065212185017877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 160094172389681131653428677 30017657323065212185017877)
                  ·
                    refine ⟨1407077687018681821172713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30017657323065212185017877 1407077687018681821172713)
                    ·
                      rfl

theorem cell22_4110411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 4, 6].length) (baseStart_4110411 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4110411 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4110411 prefixEnd_4110411 := by exact prefixLift 4110411
  have htrace : WordTrace (prefixWord ++ tailWord_4110411) baseStart_4110411 baseEnd_4110411 := by
    simpa [prefixWord, tailWord_4110411, baseEnd_4110411] using wordTrace_append hprefix tailTrace_4110411
  have hstable : (prefixWord ++ tailWord_4110411).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4110411).length < 2 ^ (prefixWord ++ tailWord_4110411).sum := by decide
  have hdescent : baseEnd_4110411 < baseStart_4110411 := by decide
  rcases family_descends (prefixWord ++ tailWord_4110411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4110524 : List Nat := [2, 2, 2, 3, 3, 1, 3, 1, 1, 4]
def baseStart_4110524 : Nat := 118140960795 + 4110524 * 2 ^ 59
def prefixEnd_4110524 : Nat := 4983230072969 + 3 ^ 40 * 4110524 * 2
def baseEnd_4110524 : Nat := 1407116369227987193097367

theorem tailTrace_4110524 : CollatzResearch.WordTrace tailWord_4110524 prefixEnd_4110524 1407116369227987193097367 := by
  unfold tailWord_4110524
  simp only [CollatzResearch.WordTrace]
  refine ⟨74961563480140522226757313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99948751306854029635676417 74961563480140522226757313)
  ·
    refine ⟨56221172610105391670067985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74961563480140522226757313 56221172610105391670067985)
    ·
      refine ⟨42165879457579043752550989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56221172610105391670067985 42165879457579043752550989)
      ·
        refine ⟨15812204796592141407206621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42165879457579043752550989 15812204796592141407206621)
        ·
          refine ⟨5929576798722053027702483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15812204796592141407206621 5929576798722053027702483)
          ·
            refine ⟨8894365198083079541553725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5929576798722053027702483 8894365198083079541553725)
            ·
              refine ⟨3335386949281154828082647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8894365198083079541553725 3335386949281154828082647)
              ·
                refine ⟨5003080423921732242123971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3335386949281154828082647 5003080423921732242123971)
                ·
                  refine ⟨7504620635882598363185957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5003080423921732242123971 7504620635882598363185957)
                  ·
                    refine ⟨1407116369227987193097367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7504620635882598363185957 1407116369227987193097367)
                    ·
                      rfl

theorem cell22_4110524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 3, 1, 1, 4].length) (baseStart_4110524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4110524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4110524 prefixEnd_4110524 := by exact prefixLift 4110524
  have htrace : WordTrace (prefixWord ++ tailWord_4110524) baseStart_4110524 baseEnd_4110524 := by
    simpa [prefixWord, tailWord_4110524, baseEnd_4110524] using wordTrace_append hprefix tailTrace_4110524
  have hstable : (prefixWord ++ tailWord_4110524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4110524).length < 2 ^ (prefixWord ++ tailWord_4110524).sum := by decide
  have hdescent : baseEnd_4110524 < baseStart_4110524 := by decide
  rcases family_descends (prefixWord ++ tailWord_4110524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4110567 : List Nat := [1, 1, 5, 3, 1, 2, 3, 6]
def baseStart_4110567 : Nat := 118140960795 + 4110567 * 2 ^ 59
def prefixEnd_4110567 : Nat := 4983230072969 + 3 ^ 40 * 4110567 * 2
def baseEnd_4110567 : Nat := 156347898778527712696915

theorem tailTrace_4110567 : CollatzResearch.WordTrace tailWord_4110567 prefixEnd_4110567 156347898778527712696915 := by
  unfold tailWord_4110567
  simp only [CollatzResearch.WordTrace]
  refine ⟨149924695299125262797329955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99949796866083508531553303 149924695299125262797329955)
  ·
    refine ⟨224887042948687894195994933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149924695299125262797329955 224887042948687894195994933)
    ·
      refine ⟨21083160276439490080874525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 224887042948687894195994933 21083160276439490080874525)
      ·
        refine ⟨7906185103664808780327947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21083160276439490080874525 7906185103664808780327947)
        ·
          refine ⟨11859277655497213170491921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7906185103664808780327947 11859277655497213170491921)
          ·
            refine ⟨8894458241622909877868941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11859277655497213170491921 8894458241622909877868941)
            ·
              refine ⟨3335421840608591204200853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8894458241622909877868941 3335421840608591204200853)
              ·
                refine ⟨156347898778527712696915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3335421840608591204200853 156347898778527712696915)
                ·
                  rfl

theorem cell22_4110567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 3, 6].length) (baseStart_4110567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4110567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4110567 prefixEnd_4110567 := by exact prefixLift 4110567
  have htrace : WordTrace (prefixWord ++ tailWord_4110567) baseStart_4110567 baseEnd_4110567 := by
    simpa [prefixWord, tailWord_4110567, baseEnd_4110567] using wordTrace_append hprefix tailTrace_4110567
  have hstable : (prefixWord ++ tailWord_4110567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4110567).length < 2 ^ (prefixWord ++ tailWord_4110567).sum := by decide
  have hdescent : baseEnd_4110567 < baseStart_4110567 := by decide
  rcases family_descends (prefixWord ++ tailWord_4110567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4110625 : List Nat := [1, 2, 3, 2, 1, 1, 2, 3, 3, 4]
def baseStart_4110625 : Nat := 118140960795 + 4110625 * 2 ^ 59
def prefixEnd_4110625 : Nat := 4983230072969 + 3 ^ 40 * 4110625 * 2
def baseEnd_4110625 : Nat := 1407150943592056596322057

theorem tailTrace_4110625 : CollatzResearch.WordTrace tailWord_4110625 prefixEnd_4110625 1407150943592056596322057 := by
  unfold tailWord_4110625
  simp only [CollatzResearch.WordTrace]
  refine ⟨149926810732915138702941329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99951207155276759135294219 149926810732915138702941329)
  ·
    refine ⟨112445108049686354027205997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149926810732915138702941329 112445108049686354027205997)
    ·
      refine ⟨42166915518632382760202249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112445108049686354027205997 42166915518632382760202249)
      ·
        refine ⟨31625186638974287070151687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42166915518632382760202249 31625186638974287070151687)
        ·
          refine ⟨47437779958461430605227531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31625186638974287070151687 47437779958461430605227531)
          ·
            refine ⟨71156669937692145907841297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47437779958461430605227531 71156669937692145907841297)
            ·
              refine ⟨53367502453269109430880973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71156669937692145907841297 53367502453269109430880973)
              ·
                refine ⟨20012813419975916036580365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53367502453269109430880973 20012813419975916036580365)
                ·
                  refine ⟨7504805032490968513717637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20012813419975916036580365 7504805032490968513717637)
                  ·
                    refine ⟨1407150943592056596322057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7504805032490968513717637 1407150943592056596322057)
                    ·
                      rfl

theorem cell22_4110625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 3, 3, 4].length) (baseStart_4110625 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4110625 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4110625 prefixEnd_4110625 := by exact prefixLift 4110625
  have htrace : WordTrace (prefixWord ++ tailWord_4110625) baseStart_4110625 baseEnd_4110625 := by
    simpa [prefixWord, tailWord_4110625, baseEnd_4110625] using wordTrace_append hprefix tailTrace_4110625
  have hstable : (prefixWord ++ tailWord_4110625).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4110625).length < 2 ^ (prefixWord ++ tailWord_4110625).sum := by decide
  have hdescent : baseEnd_4110625 < baseStart_4110625 := by decide
  rcases family_descends (prefixWord ++ tailWord_4110625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4110670 : List Nat := [4, 1, 1, 1, 1, 1, 2, 4, 1, 6]
def baseStart_4110670 : Nat := 118140960795 + 4110670 * 2 ^ 59
def prefixEnd_4110670 : Nat := 4983230072969 + 3 ^ 40 * 4110670 * 2
def baseEnd_4110670 : Nat := 1407166348011691478946919

theorem tailTrace_4110670 : CollatzResearch.WordTrace tailWord_4110670 prefixEnd_4110670 1407166348011691478946919 := by
  unfold tailWord_4110670
  simp only [CollatzResearch.WordTrace]
  refine ⟨18741056502219013923541183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99952301345168074258886309 18741056502219013923541183)
  ·
    refine ⟨28111584753328520885311775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18741056502219013923541183 28111584753328520885311775)
    ·
      refine ⟨42167377129992781327967663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28111584753328520885311775 42167377129992781327967663)
      ·
        refine ⟨63251065694989171991951495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42167377129992781327967663 63251065694989171991951495)
        ·
          refine ⟨94876598542483757987927243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63251065694989171991951495 94876598542483757987927243)
          ·
            refine ⟨142314897813725636981890865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94876598542483757987927243 142314897813725636981890865)
            ·
              refine ⟨106736173360294227736418149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142314897813725636981890865 106736173360294227736418149)
              ·
                refine ⟨20013032505055167700578403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106736173360294227736418149 20013032505055167700578403)
                ·
                  refine ⟨30019548757582751550867605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20013032505055167700578403 30019548757582751550867605)
                  ·
                    refine ⟨1407166348011691478946919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30019548757582751550867605 1407166348011691478946919)
                    ·
                      rfl

theorem cell22_4110670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 4, 1, 6].length) (baseStart_4110670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4110670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4110670 prefixEnd_4110670 := by exact prefixLift 4110670
  have htrace : WordTrace (prefixWord ++ tailWord_4110670) baseStart_4110670 baseEnd_4110670 := by
    simpa [prefixWord, tailWord_4110670, baseEnd_4110670] using wordTrace_append hprefix tailTrace_4110670
  have hstable : (prefixWord ++ tailWord_4110670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4110670).length < 2 ^ (prefixWord ++ tailWord_4110670).sum := by decide
  have hdescent : baseEnd_4110670 < baseStart_4110670 := by decide
  rcases family_descends (prefixWord ++ tailWord_4110670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4110715 : List Nat := [1, 1, 1, 1, 1, 7, 1, 1, 2, 6]
def baseStart_4110715 : Nat := 118140960795 + 4110715 * 2 ^ 59
def prefixEnd_4110715 : Nat := 4983230072969 + 3 ^ 40 * 4110715 * 2
def baseEnd_4110715 : Nat := 1407181752431326361571781

theorem tailTrace_4110715 : CollatzResearch.WordTrace tailWord_4110715 prefixEnd_4110715 1407181752431326361571781 := by
  unfold tailWord_4110715
  simp only [CollatzResearch.WordTrace]
  refine ⟨149930093302589084073717599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99953395535059389382478399 149930093302589084073717599)
  ·
    refine ⟨224895139953883626110576399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149930093302589084073717599 224895139953883626110576399)
    ·
      refine ⟨337342709930825439165864599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224895139953883626110576399 337342709930825439165864599)
      ·
        refine ⟨506014064896238158748796899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337342709930825439165864599 506014064896238158748796899)
        ·
          refine ⟨759021097344357238123195349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 506014064896238158748796899 759021097344357238123195349)
          ·
            refine ⟨17789556969008372768512391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 759021097344357238123195349 17789556969008372768512391)
            ·
              refine ⟨26684335453512559152768587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17789556969008372768512391 26684335453512559152768587)
              ·
                refine ⟨40026503180268838729152881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26684335453512559152768587 40026503180268838729152881)
                ·
                  refine ⟨30019877385201629046864661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40026503180268838729152881 30019877385201629046864661)
                  ·
                    refine ⟨1407181752431326361571781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30019877385201629046864661 1407181752431326361571781)
                    ·
                      rfl

theorem cell22_4110715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 1, 2, 6].length) (baseStart_4110715 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4110715 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4110715 prefixEnd_4110715 := by exact prefixLift 4110715
  have htrace : WordTrace (prefixWord ++ tailWord_4110715) baseStart_4110715 baseEnd_4110715 := by
    simpa [prefixWord, tailWord_4110715, baseEnd_4110715] using wordTrace_append hprefix tailTrace_4110715
  have hstable : (prefixWord ++ tailWord_4110715).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4110715).length < 2 ^ (prefixWord ++ tailWord_4110715).sum := by decide
  have hdescent : baseEnd_4110715 < baseStart_4110715 := by decide
  rcases family_descends (prefixWord ++ tailWord_4110715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4110734 : List Nat := [4, 1, 1, 4, 1, 1, 1, 1, 5, 3]
def baseStart_4110734 : Nat := 118140960795 + 4110734 * 2 ^ 59
def prefixEnd_4110734 : Nat := 4983230072969 + 3 ^ 40 * 4110734 * 2
def baseEnd_4110734 : Nat := 1407188256519616645346723

theorem tailTrace_4110734 : CollatzResearch.WordTrace tailWord_4110734 prefixEnd_4110734 1407188256519616645346723 := by
  unfold tailWord_4110734
  simp only [CollatzResearch.WordTrace]
  refine ⟨18741348286190031289832407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99953857526346833545772837 18741348286190031289832407)
  ·
    refine ⟨28112022429285046934748611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18741348286190031289832407 28112022429285046934748611)
    ·
      refine ⟨42168033643927570402122917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28112022429285046934748611 42168033643927570402122917)
      ·
        refine ⟨7906506308236419450398047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42168033643927570402122917 7906506308236419450398047)
        ·
          refine ⟨11859759462354629175597071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7906506308236419450398047 11859759462354629175597071)
          ·
            refine ⟨17789639193531943763395607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11859759462354629175597071 17789639193531943763395607)
            ·
              refine ⟨26684458790297915645093411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17789639193531943763395607 26684458790297915645093411)
              ·
                refine ⟨40026688185446873467640117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26684458790297915645093411 40026688185446873467640117)
                ·
                  refine ⟨3752502017385644387591261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40026688185446873467640117 3752502017385644387591261)
                  ·
                    refine ⟨1407188256519616645346723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3752502017385644387591261 1407188256519616645346723)
                    ·
                      rfl

theorem cell22_4110734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 1, 5, 3].length) (baseStart_4110734 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4110734 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4110734 prefixEnd_4110734 := by exact prefixLift 4110734
  have htrace : WordTrace (prefixWord ++ tailWord_4110734) baseStart_4110734 baseEnd_4110734 := by
    simpa [prefixWord, tailWord_4110734, baseEnd_4110734] using wordTrace_append hprefix tailTrace_4110734
  have hstable : (prefixWord ++ tailWord_4110734).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4110734).length < 2 ^ (prefixWord ++ tailWord_4110734).sum := by decide
  have hdescent : baseEnd_4110734 < baseStart_4110734 := by decide
  rcases family_descends (prefixWord ++ tailWord_4110734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4110745 : List Nat := [1, 2, 1, 2, 1, 4, 1, 2, 1, 7]
def baseStart_4110745 : Nat := 118140960795 + 4110745 * 2 ^ 59
def prefixEnd_4110745 : Nat := 4983230072969 + 3 ^ 40 * 4110745 * 2
def baseEnd_4110745 : Nat := 1407192022044416283321689

theorem tailTrace_4110745 : CollatzResearch.WordTrace tailWord_4110745 prefixEnd_4110745 1407192022044416283321689 := by
  unfold tailWord_4110745
  simp only [CollatzResearch.WordTrace]
  refine ⟨149931187492480399197309689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99954124994986932798206459 149931187492480399197309689)
  ·
    refine ⟨112448390619360299397982267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149931187492480399197309689 112448390619360299397982267)
    ·
      refine ⟨168672585929040449096973401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112448390619360299397982267 168672585929040449096973401)
      ·
        refine ⟨126504439446780336822730051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168672585929040449096973401 126504439446780336822730051)
        ·
          refine ⟨189756659170170505234095077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126504439446780336822730051 189756659170170505234095077)
          ·
            refine ⟨35579373594406969731392827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 189756659170170505234095077 35579373594406969731392827)
            ·
              refine ⟨53369060391610454597089241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35579373594406969731392827 53369060391610454597089241)
              ·
                refine ⟨40026795293707840947816931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53369060391610454597089241 40026795293707840947816931)
                ·
                  refine ⟨60040192940561761421725397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40026795293707840947816931 60040192940561761421725397)
                  ·
                    refine ⟨1407192022044416283321689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60040192940561761421725397 1407192022044416283321689)
                    ·
                      rfl

theorem cell22_4110745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 2, 1, 7].length) (baseStart_4110745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4110745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4110745 prefixEnd_4110745 := by exact prefixLift 4110745
  have htrace : WordTrace (prefixWord ++ tailWord_4110745) baseStart_4110745 baseEnd_4110745 := by
    simpa [prefixWord, tailWord_4110745, baseEnd_4110745] using wordTrace_append hprefix tailTrace_4110745
  have hstable : (prefixWord ++ tailWord_4110745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4110745).length < 2 ^ (prefixWord ++ tailWord_4110745).sum := by decide
  have hdescent : baseEnd_4110745 < baseStart_4110745 := by decide
  rcases family_descends (prefixWord ++ tailWord_4110745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4110751 : List Nat := [1, 1, 2, 5, 1, 1, 4, 3, 1, 3]
def baseStart_4110751 : Nat := 118140960795 + 4110751 * 2 ^ 59
def prefixEnd_4110751 : Nat := 4983230072969 + 3 ^ 40 * 4110751 * 2
def baseEnd_4110751 : Nat := 1407194075967034267671671

theorem tailTrace_4110751 : CollatzResearch.WordTrace tailWord_4110751 prefixEnd_4110751 1407194075967034267671671 := by
  unfold tailWord_4110751
  simp only [CollatzResearch.WordTrace]
  refine ⟨149931406330458662222028107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99954270886972441481352071 149931406330458662222028107)
  ·
    refine ⟨224897109495687993333042161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149931406330458662222028107 224897109495687993333042161)
    ·
      refine ⟨168672832121765994999781621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224897109495687993333042161 168672832121765994999781621)
      ·
        refine ⟨15813078011415562031229527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 168672832121765994999781621 15813078011415562031229527)
        ·
          refine ⟨23719617017123343046844291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15813078011415562031229527 23719617017123343046844291)
          ·
            refine ⟨35579425525685014570266437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23719617017123343046844291 35579425525685014570266437)
            ·
              refine ⟨6671142286065940231924957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35579425525685014570266437 6671142286065940231924957)
              ·
                refine ⟨2501678357274727586971859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6671142286065940231924957 2501678357274727586971859)
                ·
                  refine ⟨3752517535912091380457789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2501678357274727586971859 3752517535912091380457789)
                  ·
                    refine ⟨1407194075967034267671671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3752517535912091380457789 1407194075967034267671671)
                    ·
                      rfl

theorem cell22_4110751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 4, 3, 1, 3].length) (baseStart_4110751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4110751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4110751 prefixEnd_4110751 := by exact prefixLift 4110751
  have htrace : WordTrace (prefixWord ++ tailWord_4110751) baseStart_4110751 baseEnd_4110751 := by
    simpa [prefixWord, tailWord_4110751, baseEnd_4110751] using wordTrace_append hprefix tailTrace_4110751
  have hstable : (prefixWord ++ tailWord_4110751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4110751).length < 2 ^ (prefixWord ++ tailWord_4110751).sum := by decide
  have hdescent : baseEnd_4110751 < baseStart_4110751 := by decide
  rcases family_descends (prefixWord ++ tailWord_4110751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4110792 : List Nat := [2, 1, 3, 1, 3, 2, 2, 2, 6]
def baseStart_4110792 : Nat := 118140960795 + 4110792 * 2 ^ 59
def prefixEnd_4110792 : Nat := 4983230072969 + 3 ^ 40 * 4110792 * 2
def baseEnd_4110792 : Nat := 469069370368307942465515

theorem tailTrace_4110792 : CollatzResearch.WordTrace tailWord_4110792 prefixEnd_4110792 469069370368307942465515 := by
  unfold tailWord_4110792
  simp only [CollatzResearch.WordTrace]
  refine ⟨74966450861655063112135315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99955267815540084149513753 74966450861655063112135315)
  ·
    refine ⟨112449676292482594668202973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74966450861655063112135315 112449676292482594668202973)
    ·
      refine ⟨42168628609680973000576115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112449676292482594668202973 42168628609680973000576115)
      ·
        refine ⟨63252942914521459500864173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42168628609680973000576115 63252942914521459500864173)
        ·
          refine ⟨23719853592945547312824065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63252942914521459500864173 23719853592945547312824065)
          ·
            refine ⟨17789890194709160484618049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23719853592945547312824065 17789890194709160484618049)
            ·
              refine ⟨13342417646031870363463537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17789890194709160484618049 13342417646031870363463537)
              ·
                refine ⟨10006813234523902772597653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13342417646031870363463537 10006813234523902772597653)
                ·
                  refine ⟨469069370368307942465515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10006813234523902772597653 469069370368307942465515)
                  ·
                    rfl

theorem cell22_4110792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 2, 6].length) (baseStart_4110792 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4110792 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4110792 prefixEnd_4110792 := by exact prefixLift 4110792
  have htrace : WordTrace (prefixWord ++ tailWord_4110792) baseStart_4110792 baseEnd_4110792 := by
    simpa [prefixWord, tailWord_4110792, baseEnd_4110792] using wordTrace_append hprefix tailTrace_4110792
  have hstable : (prefixWord ++ tailWord_4110792).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4110792).length < 2 ^ (prefixWord ++ tailWord_4110792).sum := by decide
  have hdescent : baseEnd_4110792 < baseStart_4110792 := by decide
  rcases family_descends (prefixWord ++ tailWord_4110792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4110794 : List Nat := [3, 1, 2, 1, 2, 2, 4, 2, 1, 4]
def baseStart_4110794 : Nat := 118140960795 + 4110794 * 2 ^ 59
def prefixEnd_4110794 : Nat := 4983230072969 + 3 ^ 40 * 4110794 * 2
def baseEnd_4110794 : Nat := 1407208795745796488846539

theorem tailTrace_4110794 : CollatzResearch.WordTrace tailWord_4110794 prefixEnd_4110794 1407208795745796488846539 := by
  unfold tailWord_4110794
  simp only [CollatzResearch.WordTrace]
  refine ⟨37483243667325720141460859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99955316446201920377228957 37483243667325720141460859)
  ·
    refine ⟨56224865500988580212191289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37483243667325720141460859 56224865500988580212191289)
    ·
      refine ⟨42168649125741435159143467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56224865500988580212191289 42168649125741435159143467)
      ·
        refine ⟨63252973688612152738715201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42168649125741435159143467 63252973688612152738715201)
        ·
          refine ⟨47439730266459114554036401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63252973688612152738715201 47439730266459114554036401)
          ·
            refine ⟨35579797699844335915527301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47439730266459114554036401 35579797699844335915527301)
            ·
              refine ⟨6671212068720812984161369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35579797699844335915527301 6671212068720812984161369)
              ·
                refine ⟨5003409051540609738121027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6671212068720812984161369 5003409051540609738121027)
                ·
                  refine ⟨7505113577310914607181541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5003409051540609738121027 7505113577310914607181541)
                  ·
                    refine ⟨1407208795745796488846539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7505113577310914607181541 1407208795745796488846539)
                    ·
                      rfl

theorem cell22_4110794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 4, 2, 1, 4].length) (baseStart_4110794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4110794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4110794 prefixEnd_4110794 := by exact prefixLift 4110794
  have htrace : WordTrace (prefixWord ++ tailWord_4110794) baseStart_4110794 baseEnd_4110794 := by
    simpa [prefixWord, tailWord_4110794, baseEnd_4110794] using wordTrace_append hprefix tailTrace_4110794
  have hstable : (prefixWord ++ tailWord_4110794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4110794).length < 2 ^ (prefixWord ++ tailWord_4110794).sum := by decide
  have hdescent : baseEnd_4110794 < baseStart_4110794 := by decide
  rcases family_descends (prefixWord ++ tailWord_4110794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4110802 : List Nat := [3, 2, 2, 4, 2, 1, 1, 3, 1, 3]
def baseStart_4110802 : Nat := 118140960795 + 4110802 * 2 ^ 59
def prefixEnd_4110802 : Nat := 4983230072969 + 3 ^ 40 * 4110802 * 2
def baseEnd_4110802 : Nat := 1407211534309287134646515

theorem tailTrace_4110802 : CollatzResearch.WordTrace tailWord_4110802 prefixEnd_4110802 1407211534309287134646515 := by
  unfold tailWord_4110802
  simp only [CollatzResearch.WordTrace]
  refine ⟨37483316613318474483033665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99955510968849265288089773 37483316613318474483033665)
  ·
    refine ⟨28112487459988855862275249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37483316613318474483033665 28112487459988855862275249)
    ·
      refine ⟨21084365594991641896706437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28112487459988855862275249 21084365594991641896706437)
      ·
        refine ⟨3953318549060932855632457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21084365594991641896706437 3953318549060932855632457)
        ·
          refine ⟨2964988911795699641724343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3953318549060932855632457 2964988911795699641724343)
          ·
            refine ⟨4447483367693549462586515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2964988911795699641724343 4447483367693549462586515)
            ·
              refine ⟨6671225051540324193879773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4447483367693549462586515 6671225051540324193879773)
              ·
                refine ⟨2501709394327621572704915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6671225051540324193879773 2501709394327621572704915)
                ·
                  refine ⟨3752564091491432359057373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2501709394327621572704915 3752564091491432359057373)
                  ·
                    refine ⟨1407211534309287134646515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3752564091491432359057373 1407211534309287134646515)
                    ·
                      rfl

theorem cell22_4110802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 1, 3, 1, 3].length) (baseStart_4110802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4110802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4110802 prefixEnd_4110802 := by exact prefixLift 4110802
  have htrace : WordTrace (prefixWord ++ tailWord_4110802) baseStart_4110802 baseEnd_4110802 := by
    simpa [prefixWord, tailWord_4110802, baseEnd_4110802] using wordTrace_append hprefix tailTrace_4110802
  have hstable : (prefixWord ++ tailWord_4110802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4110802).length < 2 ^ (prefixWord ++ tailWord_4110802).sum := by decide
  have hdescent : baseEnd_4110802 < baseStart_4110802 := by decide
  rcases family_descends (prefixWord ++ tailWord_4110802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4110824 : List Nat := [2, 1, 4, 1, 1, 3, 2, 1, 4, 3]
def baseStart_4110824 : Nat := 118140960795 + 4110824 * 2 ^ 59
def prefixEnd_4110824 : Nat := 4983230072969 + 3 ^ 40 * 4110824 * 2
def baseEnd_4110824 : Nat := 1407219065358886410596447

theorem tailTrace_4110824 : CollatzResearch.WordTrace tailWord_4110824 prefixEnd_4110824 1407219065358886410596447 := by
  unfold tailWord_4110824
  simp only [CollatzResearch.WordTrace]
  refine ⟨74967034429597097844717763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99956045906129463792957017 74967034429597097844717763)
  ·
    refine ⟨112450551644395646767076645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74967034429597097844717763 112450551644395646767076645)
    ·
      refine ⟨21084478433324183768826871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112450551644395646767076645 21084478433324183768826871)
      ·
        refine ⟨31626717649986275653240307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21084478433324183768826871 31626717649986275653240307)
        ·
          refine ⟨47440076474979413479860461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31626717649986275653240307 47440076474979413479860461)
          ·
            refine ⟨17790028678117280054947673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47440076474979413479860461 17790028678117280054947673)
            ·
              refine ⟨13342521508587960041210755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17790028678117280054947673 13342521508587960041210755)
              ·
                refine ⟨20013782262881940061816133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13342521508587960041210755 20013782262881940061816133)
                ·
                  refine ⟨3752584174290363761590525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20013782262881940061816133 3752584174290363761590525)
                  ·
                    refine ⟨1407219065358886410596447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3752584174290363761590525 1407219065358886410596447)
                    ·
                      rfl

theorem cell22_4110824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 1, 4, 3].length) (baseStart_4110824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4110824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4110824 prefixEnd_4110824 := by exact prefixLift 4110824
  have htrace : WordTrace (prefixWord ++ tailWord_4110824) baseStart_4110824 baseEnd_4110824 := by
    simpa [prefixWord, tailWord_4110824, baseEnd_4110824] using wordTrace_append hprefix tailTrace_4110824
  have hstable : (prefixWord ++ tailWord_4110824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4110824).length < 2 ^ (prefixWord ++ tailWord_4110824).sum := by decide
  have hdescent : baseEnd_4110824 < baseStart_4110824 := by decide
  rcases family_descends (prefixWord ++ tailWord_4110824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4110841 : List Nat := [1, 2, 1, 3, 1, 2, 6, 1, 2, 3]
def baseStart_4110841 : Nat := 118140960795 + 4110841 * 2 ^ 59
def prefixEnd_4110841 : Nat := 4983230072969 + 3 ^ 40 * 4110841 * 2
def baseEnd_4110841 : Nat := 1407224884806304032921395

theorem tailTrace_4110841 : CollatzResearch.WordTrace tailWord_4110841 prefixEnd_4110841 1407224884806304032921395 := by
  unfold tailWord_4110841
  simp only [CollatzResearch.WordTrace]
  refine ⟨149934688900132607592804377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99956459266755071728536251 149934688900132607592804377)
  ·
    refine ⟨112451016675099455694603283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149934688900132607592804377 112451016675099455694603283)
    ·
      refine ⟨168676525012649183541904925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112451016675099455694603283 168676525012649183541904925)
      ·
        refine ⟨63253696879743443828214347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168676525012649183541904925 63253696879743443828214347)
        ·
          refine ⟨94880545319615165742321521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63253696879743443828214347 94880545319615165742321521)
          ·
            refine ⟨71160408989711374306741141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94880545319615165742321521 71160408989711374306741141)
            ·
              refine ⟨3335644171392720670628491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 71160408989711374306741141 3335644171392720670628491)
              ·
                refine ⟨5003466257089081005942737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3335644171392720670628491 5003466257089081005942737)
                ·
                  refine ⟨3752599692816810754457053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5003466257089081005942737 3752599692816810754457053)
                  ·
                    refine ⟨1407224884806304032921395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3752599692816810754457053 1407224884806304032921395)
                    ·
                      rfl

theorem cell22_4110841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 6, 1, 2, 3].length) (baseStart_4110841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4110841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4110841 prefixEnd_4110841 := by exact prefixLift 4110841
  have htrace : WordTrace (prefixWord ++ tailWord_4110841) baseStart_4110841 baseEnd_4110841 := by
    simpa [prefixWord, tailWord_4110841, baseEnd_4110841] using wordTrace_append hprefix tailTrace_4110841
  have hstable : (prefixWord ++ tailWord_4110841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4110841).length < 2 ^ (prefixWord ++ tailWord_4110841).sum := by decide
  have hdescent : baseEnd_4110841 < baseStart_4110841 := by decide
  rcases family_descends (prefixWord ++ tailWord_4110841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4110897 : List Nat := [1, 2, 2, 3, 1, 1, 3, 1, 1, 7]
def baseStart_4110897 : Nat := 118140960795 + 4110897 * 2 ^ 59
def prefixEnd_4110897 : Nat := 4983230072969 + 3 ^ 40 * 4110897 * 2
def baseEnd_4110897 : Nat := 1407244054750738553521223

theorem tailTrace_4110897 : CollatzResearch.WordTrace tailWord_4110897 prefixEnd_4110897 1407244054750738553521223 := by
  unfold tailWord_4110897
  simp only [CollatzResearch.WordTrace]
  refine ⟨149936731387929729156842945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99957820925286486104561963 149936731387929729156842945)
  ·
    refine ⟨112452548540947296867632209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149936731387929729156842945 112452548540947296867632209)
    ·
      refine ⟨84339411405710472650724157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112452548540947296867632209 84339411405710472650724157)
      ·
        refine ⟨31627279277141427244021559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84339411405710472650724157 31627279277141427244021559)
        ·
          refine ⟨47440918915712140866032339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31627279277141427244021559 47440918915712140866032339)
          ·
            refine ⟨71161378373568211299048509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47440918915712140866032339 71161378373568211299048509)
            ·
              refine ⟨26685516890088079237143191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71161378373568211299048509 26685516890088079237143191)
              ·
                refine ⟨40028275335132118855714787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26685516890088079237143191 40028275335132118855714787)
                ·
                  refine ⟨60042413002698178283572181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40028275335132118855714787 60042413002698178283572181)
                  ·
                    refine ⟨1407244054750738553521223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60042413002698178283572181 1407244054750738553521223)
                    ·
                      rfl

theorem cell22_4110897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 1, 1, 7].length) (baseStart_4110897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4110897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4110897 prefixEnd_4110897 := by exact prefixLift 4110897
  have htrace : WordTrace (prefixWord ++ tailWord_4110897) baseStart_4110897 baseEnd_4110897 := by
    simpa [prefixWord, tailWord_4110897, baseEnd_4110897] using wordTrace_append hprefix tailTrace_4110897
  have hstable : (prefixWord ++ tailWord_4110897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4110897).length < 2 ^ (prefixWord ++ tailWord_4110897).sum := by decide
  have hdescent : baseEnd_4110897 < baseStart_4110897 := by decide
  rcases family_descends (prefixWord ++ tailWord_4110897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4110959 : List Nat := [1, 1, 2, 1, 3, 2, 5, 1, 1, 5]
def baseStart_4110959 : Nat := 118140960795 + 4110959 * 2 ^ 59
def prefixEnd_4110959 : Nat := 4983230072969 + 3 ^ 40 * 4110959 * 2
def baseEnd_4110959 : Nat := 1407265278617791058471033

theorem tailTrace_4110959 : CollatzResearch.WordTrace tailWord_4110959 prefixEnd_4110959 1407265278617791058471033 := by
  unfold tailWord_4110959
  simp only [CollatzResearch.WordTrace]
  refine ⟨149938992713705113745599931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99959328475803409163733287 149938992713705113745599931)
  ·
    refine ⟨224908489070557670618399897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149938992713705113745599931 224908489070557670618399897)
    ·
      refine ⟨168681366802918252963799923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224908489070557670618399897 168681366802918252963799923)
      ·
        refine ⟨253022050204377379445699885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168681366802918252963799923 253022050204377379445699885)
        ·
          refine ⟨94883268826641517292137457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 253022050204377379445699885 94883268826641517292137457)
          ·
            refine ⟨71162451619981137969103093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94883268826641517292137457 71162451619981137969103093)
            ·
              refine ⟨6671479839373231684603415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71162451619981137969103093 6671479839373231684603415)
              ·
                refine ⟨10007219759059847526905123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6671479839373231684603415 10007219759059847526905123)
                ·
                  refine ⟨15010829638589771290357685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10007219759059847526905123 15010829638589771290357685)
                  ·
                    refine ⟨1407265278617791058471033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15010829638589771290357685 1407265278617791058471033)
                    ·
                      rfl

theorem cell22_4110959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 5, 1, 1, 5].length) (baseStart_4110959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4110959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4110959 prefixEnd_4110959 := by exact prefixLift 4110959
  have htrace : WordTrace (prefixWord ++ tailWord_4110959) baseStart_4110959 baseEnd_4110959 := by
    simpa [prefixWord, tailWord_4110959, baseEnd_4110959] using wordTrace_append hprefix tailTrace_4110959
  have hstable : (prefixWord ++ tailWord_4110959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4110959).length < 2 ^ (prefixWord ++ tailWord_4110959).sum := by decide
  have hdescent : baseEnd_4110959 < baseStart_4110959 := by decide
  rcases family_descends (prefixWord ++ tailWord_4110959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4111006 : List Nat := [4, 3, 1, 1, 1, 1, 4, 7]
def baseStart_4111006 : Nat := 118140960795 + 4111006 * 2 ^ 59
def prefixEnd_4111006 : Nat := 4983230072969 + 3 ^ 40 * 4111006 * 2
def baseEnd_4111006 : Nat := 156364596408699844727321

theorem tailTrace_4111006 : CollatzResearch.WordTrace tailWord_4111006 prefixEnd_4111006 156364596408699844727321 := by
  unfold tailWord_4111006
  simp only [CollatzResearch.WordTrace]
  refine ⟨18742588368066855096570109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99960471296356560515040581 18742588368066855096570109)
  ·
    refine ⟨7028470638025070661213791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18742588368066855096570109 7028470638025070661213791)
    ·
      refine ⟨10542705957037605991820687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7028470638025070661213791 10542705957037605991820687)
      ·
        refine ⟨15814058935556408987731031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10542705957037605991820687 15814058935556408987731031)
        ·
          refine ⟨23721088403334613481596547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15814058935556408987731031 23721088403334613481596547)
          ·
            refine ⟨35581632605001920222394821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23721088403334613481596547 35581632605001920222394821)
            ·
              refine ⟨6671556113437860041699029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35581632605001920222394821 6671556113437860041699029)
              ·
                refine ⟨156364596408699844727321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6671556113437860041699029 156364596408699844727321)
                ·
                  rfl

theorem cell22_4111006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 4, 7].length) (baseStart_4111006 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4111006 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4111006 prefixEnd_4111006 := by exact prefixLift 4111006
  have htrace : WordTrace (prefixWord ++ tailWord_4111006) baseStart_4111006 baseEnd_4111006 := by
    simpa [prefixWord, tailWord_4111006, baseEnd_4111006] using wordTrace_append hprefix tailTrace_4111006
  have hstable : (prefixWord ++ tailWord_4111006).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4111006).length < 2 ^ (prefixWord ++ tailWord_4111006).sum := by decide
  have hdescent : baseEnd_4111006 < baseStart_4111006 := by decide
  rcases family_descends (prefixWord ++ tailWord_4111006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4111046 : List Nat := [6, 1, 2, 1, 3, 1, 2, 2, 4]
def baseStart_4111046 : Nat := 118140960795 + 4111046 * 2 ^ 59
def prefixEnd_4111046 : Nat := 4983230072969 + 3 ^ 40 * 4111046 * 2
def baseEnd_4111046 : Nat := 469098353498583943848589

theorem tailTrace_4111046 : CollatzResearch.WordTrace tailWord_4111046 prefixEnd_4111046 469098353498583943848589 := by
  unfold tailWord_4111046
  simp only [CollatzResearch.WordTrace]
  refine ⟨4685692683262185237625531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 99961443909593285069344661 4685692683262185237625531)
  ·
    refine ⟨7028539024893277856438297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4685692683262185237625531 7028539024893277856438297)
    ·
      refine ⟨5271404268669958392328723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7028539024893277856438297 5271404268669958392328723)
      ·
        refine ⟨7907106403004937588493085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5271404268669958392328723 7907106403004937588493085)
        ·
          refine ⟨2965164901126851595684907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7907106403004937588493085 2965164901126851595684907)
          ·
            refine ⟨4447747351690277393527361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2965164901126851595684907 4447747351690277393527361)
            ·
              refine ⟨3335810513767708045145521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4447747351690277393527361 3335810513767708045145521)
              ·
                refine ⟨2501857885325781033859141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3335810513767708045145521 2501857885325781033859141)
                ·
                  refine ⟨469098353498583943848589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2501857885325781033859141 469098353498583943848589)
                  ·
                    rfl

theorem cell22_4111046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 2, 2, 4].length) (baseStart_4111046 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4111046 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4111046 prefixEnd_4111046 := by exact prefixLift 4111046
  have htrace : WordTrace (prefixWord ++ tailWord_4111046) baseStart_4111046 baseEnd_4111046 := by
    simpa [prefixWord, tailWord_4111046, baseEnd_4111046] using wordTrace_append hprefix tailTrace_4111046
  have hstable : (prefixWord ++ tailWord_4111046).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4111046).length < 2 ^ (prefixWord ++ tailWord_4111046).sum := by decide
  have hdescent : baseEnd_4111046 < baseStart_4111046 := by decide
  rcases family_descends (prefixWord ++ tailWord_4111046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4111068 : List Nat := [2, 2, 5, 1, 1, 1, 2, 3, 5]
def baseStart_4111068 : Nat := 118140960795 + 4111068 * 2 ^ 59
def prefixEnd_4111068 : Nat := 4983230072969 + 3 ^ 40 * 4111068 * 2
def baseEnd_4111068 : Nat := 469100863848450369165233

theorem tailTrace_4111068 : CollatzResearch.WordTrace tailWord_4111068 prefixEnd_4111068 469100863848450369165233 := by
  unfold tailWord_4111068
  simp only [CollatzResearch.WordTrace]
  refine ⟨74971484135155112680658929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99961978846873483574211905 74971484135155112680658929)
  ·
    refine ⟨56228613101366334510494197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74971484135155112680658929 56228613101366334510494197)
    ·
      refine ⟨5271432478253093860358831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 56228613101366334510494197 5271432478253093860358831)
      ·
        refine ⟨7907148717379640790538247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5271432478253093860358831 7907148717379640790538247)
        ·
          refine ⟨11860723076069461185807371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7907148717379640790538247 11860723076069461185807371)
          ·
            refine ⟨17791084614104191778711057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11860723076069461185807371 17791084614104191778711057)
            ·
              refine ⟨13343313460578143834033293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17791084614104191778711057 13343313460578143834033293)
              ·
                refine ⟨5003742547716803937762485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13343313460578143834033293 5003742547716803937762485)
                ·
                  refine ⟨469100863848450369165233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5003742547716803937762485 469100863848450369165233)
                  ·
                    rfl

theorem cell22_4111068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 3, 5].length) (baseStart_4111068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4111068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4111068 prefixEnd_4111068 := by exact prefixLift 4111068
  have htrace : WordTrace (prefixWord ++ tailWord_4111068) baseStart_4111068 baseEnd_4111068 := by
    simpa [prefixWord, tailWord_4111068, baseEnd_4111068] using wordTrace_append hprefix tailTrace_4111068
  have hstable : (prefixWord ++ tailWord_4111068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4111068).length < 2 ^ (prefixWord ++ tailWord_4111068).sum := by decide
  have hdescent : baseEnd_4111068 < baseStart_4111068 := by decide
  rcases family_descends (prefixWord ++ tailWord_4111068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4111098 : List Nat := [3, 1, 1, 1, 1, 3, 6, 1, 1, 4]
def baseStart_4111098 : Nat := 118140960795 + 4111098 * 2 ^ 59
def prefixEnd_4111098 : Nat := 4983230072969 + 3 ^ 40 * 4111098 * 2
def baseEnd_4111098 : Nat := 1407312861158441029245607

theorem tailTrace_4111098 : CollatzResearch.WordTrace tailWord_4111098 prefixEnd_4111098 1407312861158441029245607 := by
  unfold tailWord_4111098
  simp only [CollatzResearch.WordTrace]
  refine ⟨37486015615050385121227487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99962708306801026989939965 37486015615050385121227487)
  ·
    refine ⟨56229023422575577681841231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37486015615050385121227487 56229023422575577681841231)
    ·
      refine ⟨84343535133863366522761847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56229023422575577681841231 84343535133863366522761847)
      ·
        refine ⟨126515302700795049784142771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84343535133863366522761847 126515302700795049784142771)
        ·
          refine ⟨189772954051192574676214157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126515302700795049784142771 189772954051192574676214157)
          ·
            refine ⟨71164857769197215503580309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 189772954051192574676214157 71164857769197215503580309)
            ·
              refine ⟨3335852707931119476730327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 71164857769197215503580309 3335852707931119476730327)
              ·
                refine ⟨5003779061896679215095491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3335852707931119476730327 5003779061896679215095491)
                ·
                  refine ⟨7505668592845018822643237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5003779061896679215095491 7505668592845018822643237)
                  ·
                    refine ⟨1407312861158441029245607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7505668592845018822643237 1407312861158441029245607)
                    ·
                      rfl

theorem cell22_4111098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 6, 1, 1, 4].length) (baseStart_4111098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4111098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4111098 prefixEnd_4111098 := by exact prefixLift 4111098
  have htrace : WordTrace (prefixWord ++ tailWord_4111098) baseStart_4111098 baseEnd_4111098 := by
    simpa [prefixWord, tailWord_4111098, baseEnd_4111098] using wordTrace_append hprefix tailTrace_4111098
  have hstable : (prefixWord ++ tailWord_4111098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4111098).length < 2 ^ (prefixWord ++ tailWord_4111098).sum := by decide
  have hdescent : baseEnd_4111098 < baseStart_4111098 := by decide
  rcases family_descends (prefixWord ++ tailWord_4111098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4111139 : List Nat := [1, 1, 1, 4, 2, 1, 1, 1, 1, 9]
def baseStart_4111139 : Nat := 118140960795 + 4111139 * 2 ^ 59
def prefixEnd_4111139 : Nat := 4983230072969 + 3 ^ 40 * 4111139 * 2
def baseEnd_4111139 : Nat := 1407326896296330588970481

theorem tailTrace_4111139 : CollatzResearch.WordTrace tailWord_4111139 prefixEnd_4111139 1407326896296330588970481 := by
  unfold tailWord_4111139
  simp only [CollatzResearch.WordTrace]
  refine ⟨149945557853053004487152471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99963705235368669658101647 149945557853053004487152471)
  ·
    refine ⟨224918336779579506730728707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149945557853053004487152471 224918336779579506730728707)
    ·
      refine ⟨337377505169369260096093061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224918336779579506730728707 337377505169369260096093061)
      ·
        refine ⟨63258282219256736268017449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 337377505169369260096093061 63258282219256736268017449)
        ·
          refine ⟨47443711664442552201013087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63258282219256736268017449 47443711664442552201013087)
          ·
            refine ⟨71165567496663828301519631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47443711664442552201013087 71165567496663828301519631)
            ·
              refine ⟨106748351244995742452279447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71165567496663828301519631 106748351244995742452279447)
              ·
                refine ⟨160122526867493613678419171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106748351244995742452279447 160122526867493613678419171)
                ·
                  refine ⟨240183790301240420517628757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 160122526867493613678419171 240183790301240420517628757)
                  ·
                    refine ⟨1407326896296330588970481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 240183790301240420517628757 1407326896296330588970481)
                    ·
                      rfl

theorem cell22_4111139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 9].length) (baseStart_4111139 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4111139 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4111139 prefixEnd_4111139 := by exact prefixLift 4111139
  have htrace : WordTrace (prefixWord ++ tailWord_4111139) baseStart_4111139 baseEnd_4111139 := by
    simpa [prefixWord, tailWord_4111139, baseEnd_4111139] using wordTrace_append hprefix tailTrace_4111139
  have hstable : (prefixWord ++ tailWord_4111139).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4111139).length < 2 ^ (prefixWord ++ tailWord_4111139).sum := by decide
  have hdescent : baseEnd_4111139 < baseStart_4111139 := by decide
  rcases family_descends (prefixWord ++ tailWord_4111139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4111263 : List Nat := [1, 1, 2, 5, 2, 1, 2, 2, 1, 5]
def baseStart_4111263 : Nat := 118140960795 + 4111263 * 2 ^ 59
def prefixEnd_4111263 : Nat := 4983230072969 + 3 ^ 40 * 4111263 * 2
def baseEnd_4111263 : Nat := 1407369344030435598870101

theorem tailTrace_4111263 : CollatzResearch.WordTrace tailWord_4111263 prefixEnd_4111263 1407369344030435598870101 := by
  unfold tailWord_4111263
  simp only [CollatzResearch.WordTrace]
  refine ⟨149950080504603773664666443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99966720336402515776444295 149950080504603773664666443)
  ·
    refine ⟨224925120756905660496999665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149950080504603773664666443 224925120756905660496999665)
    ·
      refine ⟨168693840567679245372749749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224925120756905660496999665 168693840567679245372749749)
      ·
        refine ⟨15815047553219929253695289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 168693840567679245372749749 15815047553219929253695289)
        ·
          refine ⟨11861285664914946940271467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15815047553219929253695289 11861285664914946940271467)
          ·
            refine ⟨17791928497372420410407201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11861285664914946940271467 17791928497372420410407201)
            ·
              refine ⟨13343946373029315307805401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17791928497372420410407201 13343946373029315307805401)
              ·
                refine ⟨10007959779771986480854051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13343946373029315307805401 10007959779771986480854051)
                ·
                  refine ⟨15011939669657979721281077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10007959779771986480854051 15011939669657979721281077)
                  ·
                    refine ⟨1407369344030435598870101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15011939669657979721281077 1407369344030435598870101)
                    ·
                      rfl

theorem cell22_4111263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 2, 1, 5].length) (baseStart_4111263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4111263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4111263 prefixEnd_4111263 := by exact prefixLift 4111263
  have htrace : WordTrace (prefixWord ++ tailWord_4111263) baseStart_4111263 baseEnd_4111263 := by
    simpa [prefixWord, tailWord_4111263, baseEnd_4111263] using wordTrace_append hprefix tailTrace_4111263
  have hstable : (prefixWord ++ tailWord_4111263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4111263).length < 2 ^ (prefixWord ++ tailWord_4111263).sum := by decide
  have hdescent : baseEnd_4111263 < baseStart_4111263 := by decide
  rcases family_descends (prefixWord ++ tailWord_4111263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4111265 : List Nat := [1, 2, 3, 4, 1, 1, 1, 5, 4]
def baseStart_4111265 : Nat := 118140960795 + 4111265 * 2 ^ 59
def prefixEnd_4111265 : Nat := 4983230072969 + 3 ^ 40 * 4111265 * 2
def baseEnd_4111265 : Nat := 469123342890436086773365

theorem tailTrace_4111265 : CollatzResearch.WordTrace tailWord_4111265 prefixEnd_4111265 469123342890436086773365 := by
  unfold tailWord_4111265
  simp only [CollatzResearch.WordTrace]
  refine ⟨149950153450596528006239249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99966768967064352004159499 149950153450596528006239249)
  ·
    refine ⟨112462615087947396004679437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149950153450596528006239249 112462615087947396004679437)
    ·
      refine ⟨42173480657980273501754789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112462615087947396004679437 42173480657980273501754789)
      ·
        refine ⟨7907527623371301281579023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42173480657980273501754789 7907527623371301281579023)
        ·
          refine ⟨11861291435056951922368535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7907527623371301281579023 11861291435056951922368535)
          ·
            refine ⟨17791937152585427883552803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11861291435056951922368535 17791937152585427883552803)
            ·
              refine ⟨26687905728878141825329205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17791937152585427883552803 26687905728878141825329205)
              ·
                refine ⟨2501991162082325796124613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26687905728878141825329205 2501991162082325796124613)
                ·
                  refine ⟨469123342890436086773365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2501991162082325796124613 469123342890436086773365)
                  ·
                    rfl

theorem cell22_4111265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 5, 4].length) (baseStart_4111265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4111265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4111265 prefixEnd_4111265 := by exact prefixLift 4111265
  have htrace : WordTrace (prefixWord ++ tailWord_4111265) baseStart_4111265 baseEnd_4111265 := by
    simpa [prefixWord, tailWord_4111265, baseEnd_4111265] using wordTrace_append hprefix tailTrace_4111265
  have hstable : (prefixWord ++ tailWord_4111265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4111265).length < 2 ^ (prefixWord ++ tailWord_4111265).sum := by decide
  have hdescent : baseEnd_4111265 < baseStart_4111265 := by decide
  rcases family_descends (prefixWord ++ tailWord_4111265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4111310 : List Nat := [4, 1, 1, 1, 2, 5, 2, 6]
def baseStart_4111310 : Nat := 118140960795 + 4111310 * 2 ^ 59
def prefixEnd_4111310 : Nat := 4983230072969 + 3 ^ 40 * 4111310 * 2
def baseEnd_4111310 : Nat := 156376159232327015882773

theorem tailTrace_4111310 : CollatzResearch.WordTrace tailWord_4111310 prefixEnd_4111310 156376159232327015882773 := by
  unfold tailWord_4111310
  simp only [CollatzResearch.WordTrace]
  refine ⟨18743974341929187586453423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99967863156955667127751589 18743974341929187586453423)
  ·
    refine ⟨28115961512893781379680135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18743974341929187586453423 28115961512893781379680135)
    ·
      refine ⟨42173942269340672069520203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28115961512893781379680135 42173942269340672069520203)
      ·
        refine ⟨63260913404011008104280305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42173942269340672069520203 63260913404011008104280305)
        ·
          refine ⟨47445685053008256078210229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63260913404011008104280305 47445685053008256078210229)
          ·
            refine ⟨4448032973719524007332209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47445685053008256078210229 4448032973719524007332209)
            ·
              refine ⟨3336024730289643005499157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4448032973719524007332209 3336024730289643005499157)
              ·
                refine ⟨156376159232327015882773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3336024730289643005499157 156376159232327015882773)
                ·
                  rfl

theorem cell22_4111310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 2, 6].length) (baseStart_4111310 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4111310 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4111310 prefixEnd_4111310 := by exact prefixLift 4111310
  have htrace : WordTrace (prefixWord ++ tailWord_4111310) baseStart_4111310 baseEnd_4111310 := by
    simpa [prefixWord, tailWord_4111310, baseEnd_4111310] using wordTrace_append hprefix tailTrace_4111310
  have hstable : (prefixWord ++ tailWord_4111310).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4111310).length < 2 ^ (prefixWord ++ tailWord_4111310).sum := by decide
  have hdescent : baseEnd_4111310 < baseStart_4111310 := by decide
  rcases family_descends (prefixWord ++ tailWord_4111310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4111338 : List Nat := [3, 1, 3, 1, 2, 2, 2, 1, 7]
def baseStart_4111338 : Nat := 118140960795 + 4111338 * 2 ^ 59
def prefixEnd_4111338 : Nat := 4983230072969 + 3 ^ 40 * 4111338 * 2
def baseEnd_4111338 : Nat := 469131672687720134414957

theorem tailTrace_4111338 : CollatzResearch.WordTrace tailWord_4111338 prefixEnd_4111338 469131672687720134414957 := by
  unfold tailWord_4111338
  simp only [CollatzResearch.WordTrace]
  refine ⟨37488203994833015368411667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99968543986221374315764445 37488203994833015368411667)
  ·
    refine ⟨56232305992249523052617501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37488203994833015368411667 56232305992249523052617501)
    ·
      refine ⟨21087114747093571144731563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56232305992249523052617501 21087114747093571144731563)
      ·
        refine ⟨31630672120640356717097345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21087114747093571144731563 31630672120640356717097345)
        ·
          refine ⟨23723004090480267537823009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31630672120640356717097345 23723004090480267537823009)
          ·
            refine ⟨17792253067860200653367257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23723004090480267537823009 17792253067860200653367257)
            ·
              refine ⟨13344189800895150490025443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17792253067860200653367257 13344189800895150490025443)
              ·
                refine ⟨20016284701342725735038165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13344189800895150490025443 20016284701342725735038165)
                ·
                  refine ⟨469131672687720134414957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20016284701342725735038165 469131672687720134414957)
                  ·
                    rfl

theorem cell22_4111338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 1, 7].length) (baseStart_4111338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4111338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4111338 prefixEnd_4111338 := by exact prefixLift 4111338
  have htrace : WordTrace (prefixWord ++ tailWord_4111338) baseStart_4111338 baseEnd_4111338 := by
    simpa [prefixWord, tailWord_4111338, baseEnd_4111338] using wordTrace_append hprefix tailTrace_4111338
  have hstable : (prefixWord ++ tailWord_4111338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4111338).length < 2 ^ (prefixWord ++ tailWord_4111338).sum := by decide
  have hdescent : baseEnd_4111338 < baseStart_4111338 := by decide
  rcases family_descends (prefixWord ++ tailWord_4111338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4111348 : List Nat := [2, 6, 2, 1, 1, 1, 1, 3, 2, 3]
def baseStart_4111348 : Nat := 118140960795 + 4111348 * 2 ^ 59
def prefixEnd_4111348 : Nat := 4983230072969 + 3 ^ 40 * 4111348 * 2
def baseEnd_4111348 : Nat := 1407398441267523710494841

theorem tailTrace_4111348 : CollatzResearch.WordTrace tailWord_4111348 prefixEnd_4111348 1407398441267523710494841 := by
  unfold tailWord_4111348
  simp only [CollatzResearch.WordTrace]
  refine ⟨74976590354647916590755349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99968787139530555454340465 74976590354647916590755349)
  ·
    refine ⟨3514527672874121090191657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 74976590354647916590755349 3514527672874121090191657)
    ·
      refine ⟨2635895754655590817643743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3514527672874121090191657 2635895754655590817643743)
      ·
        refine ⟨3953843631983386226465615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2635895754655590817643743 3953843631983386226465615)
        ·
          refine ⟨5930765447975079339698423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3953843631983386226465615 5930765447975079339698423)
          ·
            refine ⟨8896148171962619009547635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5930765447975079339698423 8896148171962619009547635)
            ·
              refine ⟨13344222257943928514321453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8896148171962619009547635 13344222257943928514321453)
              ·
                refine ⟨5004083346728973192870545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13344222257943928514321453 5004083346728973192870545)
                ·
                  refine ⟨3753062510046729894652909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5004083346728973192870545 3753062510046729894652909)
                  ·
                    refine ⟨1407398441267523710494841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3753062510046729894652909 1407398441267523710494841)
                    ·
                      rfl

theorem cell22_4111348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_4111348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4111348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4111348 prefixEnd_4111348 := by exact prefixLift 4111348
  have htrace : WordTrace (prefixWord ++ tailWord_4111348) baseStart_4111348 baseEnd_4111348 := by
    simpa [prefixWord, tailWord_4111348, baseEnd_4111348] using wordTrace_append hprefix tailTrace_4111348
  have hstable : (prefixWord ++ tailWord_4111348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4111348).length < 2 ^ (prefixWord ++ tailWord_4111348).sum := by decide
  have hdescent : baseEnd_4111348 < baseStart_4111348 := by decide
  rcases family_descends (prefixWord ++ tailWord_4111348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4111413 : List Nat := [1, 3, 3, 1, 1, 1, 1, 4, 1, 6]
def baseStart_4111413 : Nat := 118140960795 + 4111413 * 2 ^ 59
def prefixEnd_4111413 : Nat := 4983230072969 + 3 ^ 40 * 4111413 * 2
def baseEnd_4111413 : Nat := 1407420692095885207619641

theorem tailTrace_4111413 : CollatzResearch.WordTrace tailWord_4111413 prefixEnd_4111413 1407420692095885207619641 := by
  unfold tailWord_4111413
  simp only [CollatzResearch.WordTrace]
  refine ⟨149955551454060349282626893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99970367636040232855084595 149955551454060349282626893)
  ·
    refine ⟨56233331795272630980985085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149955551454060349282626893 56233331795272630980985085)
    ·
      refine ⟨21087499423227236617869407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56233331795272630980985085 21087499423227236617869407)
      ·
        refine ⟨31631249134840854926804111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21087499423227236617869407 31631249134840854926804111)
        ·
          refine ⟨47446873702261282390206167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31631249134840854926804111 47446873702261282390206167)
          ·
            refine ⟨71170310553391923585309251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47446873702261282390206167 71170310553391923585309251)
            ·
              refine ⟨106755465830087885377963877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71170310553391923585309251 106755465830087885377963877)
              ·
                refine ⟨20016649843141478508368227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106755465830087885377963877 20016649843141478508368227)
                ·
                  refine ⟨30024974764712217762552341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20016649843141478508368227 30024974764712217762552341)
                  ·
                    refine ⟨1407420692095885207619641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30024974764712217762552341 1407420692095885207619641)
                    ·
                      rfl

theorem cell22_4111413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 4, 1, 6].length) (baseStart_4111413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4111413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4111413 prefixEnd_4111413 := by exact prefixLift 4111413
  have htrace : WordTrace (prefixWord ++ tailWord_4111413) baseStart_4111413 baseEnd_4111413 := by
    simpa [prefixWord, tailWord_4111413, baseEnd_4111413] using wordTrace_append hprefix tailTrace_4111413
  have hstable : (prefixWord ++ tailWord_4111413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4111413).length < 2 ^ (prefixWord ++ tailWord_4111413).sum := by decide
  have hdescent : baseEnd_4111413 < baseStart_4111413 := by decide
  rcases family_descends (prefixWord ++ tailWord_4111413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4111488 : List Nat := [2, 1, 1, 2, 1, 3, 2, 2, 1, 7]
def baseStart_4111488 : Nat := 118140960795 + 4111488 * 2 ^ 59
def prefixEnd_4111488 : Nat := 4983230072969 + 3 ^ 40 * 4111488 * 2
def baseEnd_4111488 : Nat := 1407446366128610011994411

theorem tailTrace_4111488 : CollatzResearch.WordTrace tailWord_4111488 prefixEnd_4111488 1407446366128610011994411 := by
  unfold tailWord_4111488
  simp only [CollatzResearch.WordTrace]
  refine ⟨74979143464394318545803559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99972191285859091394404745 74979143464394318545803559)
  ·
    refine ⟨112468715196591477818705339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74979143464394318545803559 112468715196591477818705339)
    ·
      refine ⟨168703072794887216728058009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112468715196591477818705339 168703072794887216728058009)
      ·
        refine ⟨126527304596165412546043507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168703072794887216728058009 126527304596165412546043507)
        ·
          refine ⟨189790956894248118819065261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126527304596165412546043507 189790956894248118819065261)
          ·
            refine ⟨71171608835343044557149473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 189790956894248118819065261 71171608835343044557149473)
            ·
              refine ⟨53378706626507283417862105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71171608835343044557149473 53378706626507283417862105)
              ·
                refine ⟨40034029969880462563396579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53378706626507283417862105 40034029969880462563396579)
                ·
                  refine ⟨60051044954820693845094869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40034029969880462563396579 60051044954820693845094869)
                  ·
                    refine ⟨1407446366128610011994411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60051044954820693845094869 1407446366128610011994411)
                    ·
                      rfl

theorem cell22_4111488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 2, 1, 7].length) (baseStart_4111488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4111488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4111488 prefixEnd_4111488 := by exact prefixLift 4111488
  have htrace : WordTrace (prefixWord ++ tailWord_4111488) baseStart_4111488 baseEnd_4111488 := by
    simpa [prefixWord, tailWord_4111488, baseEnd_4111488] using wordTrace_append hprefix tailTrace_4111488
  have hstable : (prefixWord ++ tailWord_4111488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4111488).length < 2 ^ (prefixWord ++ tailWord_4111488).sum := by decide
  have hdescent : baseEnd_4111488 < baseStart_4111488 := by decide
  rcases family_descends (prefixWord ++ tailWord_4111488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4111511 : List Nat := [1, 1, 3, 3, 3, 2, 3, 2, 1, 3]
def baseStart_4111511 : Nat := 118140960795 + 4111511 * 2 ^ 59
def prefixEnd_4111511 : Nat := 4983230072969 + 3 ^ 40 * 4111511 * 2
def baseEnd_4111511 : Nat := 1407454239498645618669341

theorem tailTrace_4111511 : CollatzResearch.WordTrace tailWord_4111511 prefixEnd_4111511 1407454239498645618669341 := by
  unfold tailWord_4111511
  simp only [CollatzResearch.WordTrace]
  refine ⟨149959125807705312019694387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99972750538470208013129591 149959125807705312019694387)
  ·
    refine ⟨224938688711557968029541581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149959125807705312019694387 224938688711557968029541581)
    ·
      refine ⟨84352008266834238011078093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224938688711557968029541581 84352008266834238011078093)
      ·
        refine ⟨31632003100062839254154285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84352008266834238011078093 31632003100062839254154285)
        ·
          refine ⟨11862001162523564720307857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31632003100062839254154285 11862001162523564720307857)
          ·
            refine ⟨8896500871892673540230893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11862001162523564720307857 8896500871892673540230893)
            ·
              refine ⟨3336187826959752577586585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8896500871892673540230893 3336187826959752577586585)
              ·
                refine ⟨2502140870219814433189939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3336187826959752577586585 2502140870219814433189939)
                ·
                  refine ⟨3753211305329721649784909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2502140870219814433189939 3753211305329721649784909)
                  ·
                    refine ⟨1407454239498645618669341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3753211305329721649784909 1407454239498645618669341)
                    ·
                      rfl

theorem cell22_4111511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 3, 2, 1, 3].length) (baseStart_4111511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4111511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4111511 prefixEnd_4111511 := by exact prefixLift 4111511
  have htrace : WordTrace (prefixWord ++ tailWord_4111511) baseStart_4111511 baseEnd_4111511 := by
    simpa [prefixWord, tailWord_4111511, baseEnd_4111511] using wordTrace_append hprefix tailTrace_4111511
  have hstable : (prefixWord ++ tailWord_4111511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4111511).length < 2 ^ (prefixWord ++ tailWord_4111511).sum := by decide
  have hdescent : baseEnd_4111511 < baseStart_4111511 := by decide
  rcases family_descends (prefixWord ++ tailWord_4111511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4111520 : List Nat := [2, 1, 1, 4, 2, 1, 2, 2, 3, 4]
def baseStart_4111520 : Nat := 118140960795 + 4111520 * 2 ^ 59
def prefixEnd_4111520 : Nat := 4983230072969 + 3 ^ 40 * 4111520 * 2
def baseEnd_4111520 : Nat := 1407457320382572595194313

theorem tailTrace_4111520 : CollatzResearch.WordTrace tailWord_4111520 prefixEnd_4111520 1407457320382572595194313 := by
  unfold tailWord_4111520
  simp only [CollatzResearch.WordTrace]
  refine ⟨74979727032336353278386007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99972969376448471037848009 74979727032336353278386007)
  ·
    refine ⟨112469590548504529917579011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74979727032336353278386007 112469590548504529917579011)
    ·
      refine ⟨168704385822756794876368517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112469590548504529917579011 168704385822756794876368517)
      ·
        refine ⟨31632072341766899039319097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 168704385822756794876368517 31632072341766899039319097)
        ·
          refine ⟨23724054256325174279489323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31632072341766899039319097 23724054256325174279489323)
          ·
            refine ⟨35586081384487761419233985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23724054256325174279489323 35586081384487761419233985)
            ·
              refine ⟨26689561038365821064425489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35586081384487761419233985 26689561038365821064425489)
              ·
                refine ⟨20017170778774365798319117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26689561038365821064425489 20017170778774365798319117)
                ·
                  refine ⟨7506439042040387174369669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20017170778774365798319117 7506439042040387174369669)
                  ·
                    refine ⟨1407457320382572595194313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7506439042040387174369669 1407457320382572595194313)
                    ·
                      rfl

theorem cell22_4111520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 2, 3, 4].length) (baseStart_4111520 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4111520 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4111520 prefixEnd_4111520 := by exact prefixLift 4111520
  have htrace : WordTrace (prefixWord ++ tailWord_4111520) baseStart_4111520 baseEnd_4111520 := by
    simpa [prefixWord, tailWord_4111520, baseEnd_4111520] using wordTrace_append hprefix tailTrace_4111520
  have hstable : (prefixWord ++ tailWord_4111520).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4111520).length < 2 ^ (prefixWord ++ tailWord_4111520).sum := by decide
  have hdescent : baseEnd_4111520 < baseStart_4111520 := by decide
  rcases family_descends (prefixWord ++ tailWord_4111520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4111524 : List Nat := [2, 3, 1, 2, 3, 3, 2, 1, 5]
def baseStart_4111524 : Nat := 118140960795 + 4111524 * 2 ^ 59
def prefixEnd_4111524 : Nat := 4983230072969 + 3 ^ 40 * 4111524 * 2
def baseEnd_4111524 : Nat := 469152896554772639364767

theorem tailTrace_4111524 : CollatzResearch.WordTrace tailWord_4111524 prefixEnd_4111524 469152896554772639364767 := by
  unfold tailWord_4111524
  simp only [CollatzResearch.WordTrace]
  refine ⟨74979799978329107619958813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99973066637772143493278417 74979799978329107619958813)
  ·
    refine ⟨28117424991873415357484555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74979799978329107619958813 28117424991873415357484555)
    ·
      refine ⟨42176137487810123036226833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28117424991873415357484555 42176137487810123036226833)
      ·
        refine ⟨31632103115857592277170125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42176137487810123036226833 31632103115857592277170125)
        ·
          refine ⟨11862038668446597103938797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31632103115857592277170125 11862038668446597103938797)
          ·
            refine ⟨4448264500667473913977049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11862038668446597103938797 4448264500667473913977049)
            ·
              refine ⟨3336198375500605435482787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4448264500667473913977049 3336198375500605435482787)
              ·
                refine ⟨5004297563250908153224181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3336198375500605435482787 5004297563250908153224181)
                ·
                  refine ⟨469152896554772639364767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5004297563250908153224181 469152896554772639364767)
                  ·
                    rfl

theorem cell22_4111524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 2, 1, 5].length) (baseStart_4111524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4111524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4111524 prefixEnd_4111524 := by exact prefixLift 4111524
  have htrace : WordTrace (prefixWord ++ tailWord_4111524) baseStart_4111524 baseEnd_4111524 := by
    simpa [prefixWord, tailWord_4111524, baseEnd_4111524] using wordTrace_append hprefix tailTrace_4111524
  have hstable : (prefixWord ++ tailWord_4111524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4111524).length < 2 ^ (prefixWord ++ tailWord_4111524).sum := by decide
  have hdescent : baseEnd_4111524 < baseStart_4111524 := by decide
  rcases family_descends (prefixWord ++ tailWord_4111524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4111537 : List Nat := [1, 2, 2, 5, 1, 2, 1, 1, 3, 4]
def baseStart_4111537 : Nat := 118140960795 + 4111537 * 2 ^ 59
def prefixEnd_4111537 : Nat := 4983230072969 + 3 ^ 40 * 4111537 * 2
def baseEnd_4111537 : Nat := 1407463139829990217519261

theorem tailTrace_4111537 : CollatzResearch.WordTrace tailWord_4111537 prefixEnd_4111537 1407463139829990217519261 := by
  unfold tailWord_4111537
  simp only [CollatzResearch.WordTrace]
  refine ⟨149960074105611118460140865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99973382737074078973427243 149960074105611118460140865)
  ·
    refine ⟨112470055579208338845105649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149960074105611118460140865 112470055579208338845105649)
    ·
      refine ⟨84352541684406254133829237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112470055579208338845105649 84352541684406254133829237)
      ·
        refine ⟨7908050782913086325046491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 84352541684406254133829237 7908050782913086325046491)
        ·
          refine ⟨11862076174369629487569737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7908050782913086325046491 11862076174369629487569737)
          ·
            refine ⟨8896557130777222115677303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11862076174369629487569737 8896557130777222115677303)
            ·
              refine ⟨13344835696165833173515955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8896557130777222115677303 13344835696165833173515955)
              ·
                refine ⟨20017253544248749760273933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13344835696165833173515955 20017253544248749760273933)
                ·
                  refine ⟨7506470079093281160102725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20017253544248749760273933 7506470079093281160102725)
                  ·
                    refine ⟨1407463139829990217519261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7506470079093281160102725 1407463139829990217519261)
                    ·
                      rfl

theorem cell22_4111537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 1, 3, 4].length) (baseStart_4111537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4111537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4111537 prefixEnd_4111537 := by exact prefixLift 4111537
  have htrace : WordTrace (prefixWord ++ tailWord_4111537) baseStart_4111537 baseEnd_4111537 := by
    simpa [prefixWord, tailWord_4111537, baseEnd_4111537] using wordTrace_append hprefix tailTrace_4111537
  have hstable : (prefixWord ++ tailWord_4111537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4111537).length < 2 ^ (prefixWord ++ tailWord_4111537).sum := by decide
  have hdescent : baseEnd_4111537 < baseStart_4111537 := by decide
  rcases family_descends (prefixWord ++ tailWord_4111537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4111558 : List Nat := [6, 1, 2, 2, 1, 1, 2, 2, 5]
def baseStart_4111558 : Nat := 118140960795 + 4111558 * 2 ^ 59
def prefixEnd_4111558 : Nat := 4983230072969 + 3 ^ 40 * 4111558 * 2
def baseEnd_4111558 : Nat := 469156776186384387581399

theorem tailTrace_4111558 : CollatzResearch.WordTrace tailWord_4111558 prefixEnd_4111558 469156776186384387581399 := by
  unfold tailWord_4111558
  simp only [CollatzResearch.WordTrace]
  refine ⟨4686276251204219970207979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 99973893359023359364436885 4686276251204219970207979)
  ·
    refine ⟨7029414376806329955311969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4686276251204219970207979 7029414376806329955311969)
    ·
      refine ⟨5272060782604747466483977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7029414376806329955311969 5272060782604747466483977)
      ·
        refine ⟨3954045586953560599862983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5272060782604747466483977 3954045586953560599862983)
        ·
          refine ⟨5931068380430340899794475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3954045586953560599862983 5931068380430340899794475)
          ·
            refine ⟨8896602570645511349691713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5931068380430340899794475 8896602570645511349691713)
            ·
              refine ⟨6672451927984133512268785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8896602570645511349691713 6672451927984133512268785)
              ·
                refine ⟨5004338945988100134201589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6672451927984133512268785 5004338945988100134201589)
                ·
                  refine ⟨469156776186384387581399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5004338945988100134201589 469156776186384387581399)
                  ·
                    rfl

theorem cell22_4111558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 2, 2, 5].length) (baseStart_4111558 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4111558 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4111558 prefixEnd_4111558 := by exact prefixLift 4111558
  have htrace : WordTrace (prefixWord ++ tailWord_4111558) baseStart_4111558 baseEnd_4111558 := by
    simpa [prefixWord, tailWord_4111558, baseEnd_4111558] using wordTrace_append hprefix tailTrace_4111558
  have hstable : (prefixWord ++ tailWord_4111558).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4111558).length < 2 ^ (prefixWord ++ tailWord_4111558).sum := by decide
  have hdescent : baseEnd_4111558 < baseStart_4111558 := by decide
  rcases family_descends (prefixWord ++ tailWord_4111558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4111599 : List Nat := [1, 1, 2, 1, 7, 2, 1, 1, 2, 4]
def baseStart_4111599 : Nat := 118140960795 + 4111599 * 2 ^ 59
def prefixEnd_4111599 : Nat := 4983230072969 + 3 ^ 40 * 4111599 * 2
def baseEnd_4111599 : Nat := 1407484363697042722469071

theorem tailTrace_4111599 : CollatzResearch.WordTrace tailWord_4111599 prefixEnd_4111599 1407484363697042722469071 := by
  unfold tailWord_4111599
  simp only [CollatzResearch.WordTrace]
  refine ⟨149962335431386503048897851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99974890287591002032598567 149962335431386503048897851)
  ·
    refine ⟨224943503147079754573346777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149962335431386503048897851 224943503147079754573346777)
    ·
      refine ⟨168707627360309815930010083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224943503147079754573346777 168707627360309815930010083)
      ·
        refine ⟨253061441040464723895015125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168707627360309815930010083 253061441040464723895015125)
        ·
          refine ⟨5931127524385891966289417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 253061441040464723895015125 5931127524385891966289417)
          ·
            refine ⟨4448345643289418974717063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5931127524385891966289417 4448345643289418974717063)
            ·
              refine ⟨6672518464934128462075595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4448345643289418974717063 6672518464934128462075595)
              ·
                refine ⟨10008777697401192693113393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6672518464934128462075595 10008777697401192693113393)
                ·
                  refine ⟨7506583273050894519835045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10008777697401192693113393 7506583273050894519835045)
                  ·
                    refine ⟨1407484363697042722469071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7506583273050894519835045 1407484363697042722469071)
                    ·
                      rfl

theorem cell22_4111599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 1, 1, 2, 4].length) (baseStart_4111599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4111599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4111599 prefixEnd_4111599 := by exact prefixLift 4111599
  have htrace : WordTrace (prefixWord ++ tailWord_4111599) baseStart_4111599 baseEnd_4111599 := by
    simpa [prefixWord, tailWord_4111599, baseEnd_4111599] using wordTrace_append hprefix tailTrace_4111599
  have hstable : (prefixWord ++ tailWord_4111599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4111599).length < 2 ^ (prefixWord ++ tailWord_4111599).sum := by decide
  have hdescent : baseEnd_4111599 < baseStart_4111599 := by decide
  rcases family_descends (prefixWord ++ tailWord_4111599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4111618 : List Nat := [3, 4, 1, 1, 3, 2, 1, 2, 2, 3]
def baseStart_4111618 : Nat := 118140960795 + 4111618 * 2 ^ 59
def prefixEnd_4111618 : Nat := 4983230072969 + 3 ^ 40 * 4111618 * 2
def baseEnd_4111618 : Nat := 1407490867785333006244013

theorem tailTrace_4111618 : CollatzResearch.WordTrace tailWord_4111618 prefixEnd_4111618 1407490867785333006244013 := by
  unfold tailWord_4111618
  simp only [CollatzResearch.WordTrace]
  refine ⟨37490757104579417323459877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99975352278878446195893005 37490757104579417323459877)
  ·
    refine ⟨7029516957108640748148727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37490757104579417323459877 7029516957108640748148727)
    ·
      refine ⟨10544275435662961122223091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7029516957108640748148727 10544275435662961122223091)
      ·
        refine ⟨15816413153494441683334637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10544275435662961122223091 15816413153494441683334637)
        ·
          refine ⟨5931154932560415631250489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15816413153494441683334637 5931154932560415631250489)
          ·
            refine ⟨4448366199420311723437867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5931154932560415631250489 4448366199420311723437867)
            ·
              refine ⟨6672549299130467585156801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4448366199420311723437867 6672549299130467585156801)
              ·
                refine ⟨5004411974347850688867601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6672549299130467585156801 5004411974347850688867601)
                ·
                  refine ⟨3753308980760888016650701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5004411974347850688867601 3753308980760888016650701)
                  ·
                    refine ⟨1407490867785333006244013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3753308980760888016650701 1407490867785333006244013)
                    ·
                      rfl

theorem cell22_4111618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 1, 2, 2, 3].length) (baseStart_4111618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4111618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4111618 prefixEnd_4111618 := by exact prefixLift 4111618
  have htrace : WordTrace (prefixWord ++ tailWord_4111618) baseStart_4111618 baseEnd_4111618 := by
    simpa [prefixWord, tailWord_4111618, baseEnd_4111618] using wordTrace_append hprefix tailTrace_4111618
  have hstable : (prefixWord ++ tailWord_4111618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4111618).length < 2 ^ (prefixWord ++ tailWord_4111618).sum := by decide
  have hdescent : baseEnd_4111618 < baseStart_4111618 := by decide
  rcases family_descends (prefixWord ++ tailWord_4111618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4111625 : List Nat := [1, 2, 1, 1, 3, 3, 3, 1, 7]
def baseStart_4111625 : Nat := 118140960795 + 4111625 * 2 ^ 59
def prefixEnd_4111625 : Nat := 4983230072969 + 3 ^ 40 * 4111625 * 2
def baseEnd_4111625 : Nat := 469164421342795773772997

theorem tailTrace_4111625 : CollatzResearch.WordTrace tailWord_4111625 prefixEnd_4111625 469164421342795773772997 := by
  unfold tailWord_4111625
  simp only [CollatzResearch.WordTrace]
  refine ⟨149963283729292309489344329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99975522486194872992896219 149963283729292309489344329)
  ·
    refine ⟨112472462796969232117008247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149963283729292309489344329 112472462796969232117008247)
    ·
      refine ⟨168708694195453848175512371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112472462796969232117008247 168708694195453848175512371)
      ·
        refine ⟨253063041293180772263268557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168708694195453848175512371 253063041293180772263268557)
        ·
          refine ⟨94898640484942789598725709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 253063041293180772263268557 94898640484942789598725709)
          ·
            refine ⟨35586990181853546099522141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94898640484942789598725709 35586990181853546099522141)
            ·
              refine ⟨13345121318195079787320803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35586990181853546099522141 13345121318195079787320803)
              ·
                refine ⟨20017681977292619680981205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13345121318195079787320803 20017681977292619680981205)
                ·
                  refine ⟨469164421342795773772997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20017681977292619680981205 469164421342795773772997)
                  ·
                    rfl

theorem cell22_4111625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 1, 7].length) (baseStart_4111625 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4111625 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4111625 prefixEnd_4111625 := by exact prefixLift 4111625
  have htrace : WordTrace (prefixWord ++ tailWord_4111625) baseStart_4111625 baseEnd_4111625 := by
    simpa [prefixWord, tailWord_4111625, baseEnd_4111625] using wordTrace_append hprefix tailTrace_4111625
  have hstable : (prefixWord ++ tailWord_4111625).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4111625).length < 2 ^ (prefixWord ++ tailWord_4111625).sum := by decide
  have hdescent : baseEnd_4111625 < baseStart_4111625 := by decide
  rcases family_descends (prefixWord ++ tailWord_4111625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4111687 : List Nat := [1, 1, 4, 1, 2, 3, 3, 1, 6]
def baseStart_4111687 : Nat := 118140960795 + 4111687 * 2 ^ 59
def prefixEnd_4111687 : Nat := 4983230072969 + 3 ^ 40 * 4111687 * 2
def baseEnd_4111687 : Nat := 469171495965146608756267

theorem tailTrace_4111687 : CollatzResearch.WordTrace tailWord_4111687 prefixEnd_4111687 469171495965146608756267 := by
  unfold tailWord_4111687
  simp only [CollatzResearch.WordTrace]
  refine ⟨149965545055067694078101315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99977030036711796052067543 149965545055067694078101315)
  ·
    refine ⟨224948317582601541117151973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149965545055067694078101315 224948317582601541117151973)
    ·
      refine ⟨42177809546737788959465995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 224948317582601541117151973 42177809546737788959465995)
      ·
        refine ⟨63266714320106683439198993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42177809546737788959465995 63266714320106683439198993)
        ·
          refine ⟨47450035740080012579399245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63266714320106683439198993 47450035740080012579399245)
          ·
            refine ⟨17793763402530004717274717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47450035740080012579399245 17793763402530004717274717)
            ·
              refine ⟨6672661275948751768978019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17793763402530004717274717 6672661275948751768978019)
              ·
                refine ⟨10008991913923127653467029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6672661275948751768978019 10008991913923127653467029)
                ·
                  refine ⟨469171495965146608756267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10008991913923127653467029 469171495965146608756267)
                  ·
                    rfl

theorem cell22_4111687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 3, 1, 6].length) (baseStart_4111687 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4111687 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4111687 prefixEnd_4111687 := by exact prefixLift 4111687
  have htrace : WordTrace (prefixWord ++ tailWord_4111687) baseStart_4111687 baseEnd_4111687 := by
    simpa [prefixWord, tailWord_4111687, baseEnd_4111687] using wordTrace_append hprefix tailTrace_4111687
  have hstable : (prefixWord ++ tailWord_4111687).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4111687).length < 2 ^ (prefixWord ++ tailWord_4111687).sum := by decide
  have hdescent : baseEnd_4111687 < baseStart_4111687 := by decide
  rcases family_descends (prefixWord ++ tailWord_4111687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4111719 : List Nat := [1, 1, 5, 1, 4, 1, 1, 2, 1, 5]
def baseStart_4111719 : Nat := 118140960795 + 4111719 * 2 ^ 59
def prefixEnd_4111719 : Nat := 4983230072969 + 3 ^ 40 * 4111719 * 2
def baseEnd_4111719 : Nat := 1407525442149402409468703

theorem tailTrace_4111719 : CollatzResearch.WordTrace tailWord_4111719 prefixEnd_4111719 1407525442149402409468703 := by
  unfold tailWord_4111719
  simp only [CollatzResearch.WordTrace]
  refine ⟨149966712190951763543266211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99977808127301175695510807 149966712190951763543266211)
  ·
    refine ⟨224950068286427645314899317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149966712190951763543266211 224950068286427645314899317)
    ·
      refine ⟨21089068901852591748271811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 224950068286427645314899317 21089068901852591748271811)
      ·
        refine ⟨31633603352778887622407717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21089068901852591748271811 31633603352778887622407717)
        ·
          refine ⟨5931300628646041429201447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31633603352778887622407717 5931300628646041429201447)
          ·
            refine ⟨8896950942969062143802171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5931300628646041429201447 8896950942969062143802171)
            ·
              refine ⟨13345426414453593215703257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8896950942969062143802171 13345426414453593215703257)
              ·
                refine ⟨10009069810840194911777443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13345426414453593215703257 10009069810840194911777443)
                ·
                  refine ⟨15013604716260292367666165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10009069810840194911777443 15013604716260292367666165)
                  ·
                    refine ⟨1407525442149402409468703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15013604716260292367666165 1407525442149402409468703)
                    ·
                      rfl

theorem cell22_4111719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 2, 1, 5].length) (baseStart_4111719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4111719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4111719 prefixEnd_4111719 := by exact prefixLift 4111719
  have htrace : WordTrace (prefixWord ++ tailWord_4111719) baseStart_4111719 baseEnd_4111719 := by
    simpa [prefixWord, tailWord_4111719, baseEnd_4111719] using wordTrace_append hprefix tailTrace_4111719
  have hstable : (prefixWord ++ tailWord_4111719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4111719).length < 2 ^ (prefixWord ++ tailWord_4111719).sum := by decide
  have hdescent : baseEnd_4111719 < baseStart_4111719 := by decide
  rcases family_descends (prefixWord ++ tailWord_4111719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4111768 : List Nat := [2, 1, 2, 5, 3, 1, 1, 1, 2, 4]
def baseStart_4111768 : Nat := 118140960795 + 4111768 * 2 ^ 59
def prefixEnd_4111768 : Nat := 4983230072969 + 3 ^ 40 * 4111768 * 2
def baseEnd_4111768 : Nat := 1407542215850782614993553

theorem tailTrace_4111768 : CollatzResearch.WordTrace tailWord_4111768 prefixEnd_4111768 1407542215850782614993553 := by
  unfold tailWord_4111768
  simp only [CollatzResearch.WordTrace]
  refine ⟨74984249683887122455899979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99978999578516163274533305 74984249683887122455899979)
  ·
    refine ⟨112476374525830683683849969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74984249683887122455899979 112476374525830683683849969)
    ·
      refine ⟨84357280894373012762887477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112476374525830683683849969 84357280894373012762887477)
      ·
        refine ⟨7908495083847469946520701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 84357280894373012762887477 7908495083847469946520701)
        ·
          refine ⟨2965685656442801229945263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7908495083847469946520701 2965685656442801229945263)
          ·
            refine ⟨4448528484664201844917895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2965685656442801229945263 4448528484664201844917895)
            ·
              refine ⟨6672792726996302767376843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4448528484664201844917895 6672792726996302767376843)
              ·
                refine ⟨10009189090494454151065265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6672792726996302767376843 10009189090494454151065265)
                ·
                  refine ⟨7506891817870840613298949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10009189090494454151065265 7506891817870840613298949)
                  ·
                    refine ⟨1407542215850782614993553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7506891817870840613298949 1407542215850782614993553)
                    ·
                      rfl

theorem cell22_4111768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 1, 1, 2, 4].length) (baseStart_4111768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4111768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4111768 prefixEnd_4111768 := by exact prefixLift 4111768
  have htrace : WordTrace (prefixWord ++ tailWord_4111768) baseStart_4111768 baseEnd_4111768 := by
    simpa [prefixWord, tailWord_4111768, baseEnd_4111768] using wordTrace_append hprefix tailTrace_4111768
  have hstable : (prefixWord ++ tailWord_4111768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4111768).length < 2 ^ (prefixWord ++ tailWord_4111768).sum := by decide
  have hdescent : baseEnd_4111768 < baseStart_4111768 := by decide
  rcases family_descends (prefixWord ++ tailWord_4111768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4111807 : List Nat := [1, 1, 2, 2, 2, 1, 1, 3, 5, 4]
def baseStart_4111807 : Nat := 118140960795 + 4111807 * 2 ^ 59
def prefixEnd_4111807 : Nat := 4983230072969 + 3 ^ 40 * 4111807 * 2
def baseEnd_4111807 : Nat := 1407555566347799513268433

theorem tailTrace_4111807 : CollatzResearch.WordTrace tailWord_4111807 prefixEnd_4111807 1407555566347799513268433 := by
  unfold tailWord_4111807
  simp only [CollatzResearch.WordTrace]
  refine ⟨149969921814632954572469675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99979947876421969714979783 149969921814632954572469675)
  ·
    refine ⟨224954882721949431858704513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149969921814632954572469675 224954882721949431858704513)
    ·
      refine ⟨168716162041462073894028385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224954882721949431858704513 168716162041462073894028385)
      ·
        refine ⟨126537121531096555420521289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168716162041462073894028385 126537121531096555420521289)
        ·
          refine ⟨94902841148322416565390967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126537121531096555420521289 94902841148322416565390967)
          ·
            refine ⟨142354261722483624848086451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94902841148322416565390967 142354261722483624848086451)
            ·
              refine ⟨213531392583725437272129677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142354261722483624848086451 213531392583725437272129677)
              ·
                refine ⟨80074272218897038977048629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 213531392583725437272129677 80074272218897038977048629)
                ·
                  refine ⟨7506963020521597404098309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 80074272218897038977048629 7506963020521597404098309)
                  ·
                    refine ⟨1407555566347799513268433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7506963020521597404098309 1407555566347799513268433)
                    ·
                      rfl

theorem cell22_4111807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 3, 5, 4].length) (baseStart_4111807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4111807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4111807 prefixEnd_4111807 := by exact prefixLift 4111807
  have htrace : WordTrace (prefixWord ++ tailWord_4111807) baseStart_4111807 baseEnd_4111807 := by
    simpa [prefixWord, tailWord_4111807, baseEnd_4111807] using wordTrace_append hprefix tailTrace_4111807
  have hstable : (prefixWord ++ tailWord_4111807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4111807).length < 2 ^ (prefixWord ++ tailWord_4111807).sum := by decide
  have hdescent : baseEnd_4111807 < baseStart_4111807 := by decide
  rcases family_descends (prefixWord ++ tailWord_4111807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4111852 : List Nat := [2, 2, 1, 1, 2, 1, 2, 2, 3, 6]
def baseStart_4111852 : Nat := 118140960795 + 4111852 * 2 ^ 59
def prefixEnd_4111852 : Nat := 4983230072969 + 3 ^ 40 * 4111852 * 2
def baseEnd_4111852 : Nat := 1407570970767434395893295

theorem tailTrace_4111852 : CollatzResearch.WordTrace tailWord_4111852 prefixEnd_4111852 1407570970767434395893295 := by
  unfold tailWord_4111852
  simp only [CollatzResearch.WordTrace]
  refine ⟨74985781549734963628928905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99981042066313284838571873 74985781549734963628928905)
  ·
    refine ⟨56239336162301222721696679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74985781549734963628928905 56239336162301222721696679)
    ·
      refine ⟨84359004243451834082545019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56239336162301222721696679 84359004243451834082545019)
      ·
        refine ⟨126538506365177751123817529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84359004243451834082545019 126538506365177751123817529)
        ·
          refine ⟨94903879773883313342863147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126538506365177751123817529 94903879773883313342863147)
          ·
            refine ⟨142355819660824970014294721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94903879773883313342863147 142355819660824970014294721)
            ·
              refine ⟨106766864745618727510721041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142355819660824970014294721 106766864745618727510721041)
              ·
                refine ⟨80075148559214045633040781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106766864745618727510721041 80075148559214045633040781)
                ·
                  refine ⟨30028180709705267112390293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80075148559214045633040781 30028180709705267112390293)
                  ·
                    refine ⟨1407570970767434395893295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30028180709705267112390293 1407570970767434395893295)
                    ·
                      rfl

theorem cell22_4111852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 6].length) (baseStart_4111852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4111852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4111852 prefixEnd_4111852 := by exact prefixLift 4111852
  have htrace : WordTrace (prefixWord ++ tailWord_4111852) baseStart_4111852 baseEnd_4111852 := by
    simpa [prefixWord, tailWord_4111852, baseEnd_4111852] using wordTrace_append hprefix tailTrace_4111852
  have hstable : (prefixWord ++ tailWord_4111852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4111852).length < 2 ^ (prefixWord ++ tailWord_4111852).sum := by decide
  have hdescent : baseEnd_4111852 < baseStart_4111852 := by decide
  rcases family_descends (prefixWord ++ tailWord_4111852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4111897 : List Nat := [1, 2, 1, 2, 1, 1, 2, 1, 3, 8]
def baseStart_4111897 : Nat := 118140960795 + 4111897 * 2 ^ 59
def prefixEnd_4111897 : Nat := 4983230072969 + 3 ^ 40 * 4111897 * 2
def baseEnd_4111897 : Nat := 1407586375187069278518157

theorem tailTrace_4111897 : CollatzResearch.WordTrace tailWord_4111897 prefixEnd_4111897 1407586375187069278518157 := by
  unfold tailWord_4111897
  simp only [CollatzResearch.WordTrace]
  refine ⟨149973204384306899943245945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99982136256204599962163963 149973204384306899943245945)
  ·
    refine ⟨112479903288230174957434459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149973204384306899943245945 112479903288230174957434459)
    ·
      refine ⟨168719854932345262436151689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112479903288230174957434459 168719854932345262436151689)
      ·
        refine ⟨126539891199258946827113767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168719854932345262436151689 126539891199258946827113767)
        ·
          refine ⟨189809836798888420240670651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126539891199258946827113767 189809836798888420240670651)
          ·
            refine ⟨284714755198332630361005977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189809836798888420240670651 284714755198332630361005977)
            ·
              refine ⟨213536066398749472770754483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 284714755198332630361005977 213536066398749472770754483)
              ·
                refine ⟨320304099598124209156131725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 213536066398749472770754483 320304099598124209156131725)
                ·
                  refine ⟨120114037349296578433549397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 320304099598124209156131725 120114037349296578433549397)
                  ·
                    refine ⟨1407586375187069278518157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 120114037349296578433549397 1407586375187069278518157)
                    ·
                      rfl

theorem cell22_4111897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 8].length) (baseStart_4111897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4111897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4111897 prefixEnd_4111897 := by exact prefixLift 4111897
  have htrace : WordTrace (prefixWord ++ tailWord_4111897) baseStart_4111897 baseEnd_4111897 := by
    simpa [prefixWord, tailWord_4111897, baseEnd_4111897] using wordTrace_append hprefix tailTrace_4111897
  have hstable : (prefixWord ++ tailWord_4111897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4111897).length < 2 ^ (prefixWord ++ tailWord_4111897).sum := by decide
  have hdescent : baseEnd_4111897 < baseStart_4111897 := by decide
  rcases family_descends (prefixWord ++ tailWord_4111897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4111914 : List Nat := [3, 1, 4, 1, 1, 1, 1, 1, 1, 8]
def baseStart_4111914 : Nat := 118140960795 + 4111914 * 2 ^ 59
def prefixEnd_4111914 : Nat := 4983230072969 + 3 ^ 40 * 4111914 * 2
def baseEnd_4111914 : Nat := 1407592194634486900843105

theorem tailTrace_4111914 : CollatzResearch.WordTrace tailWord_4111914 prefixEnd_4111914 1407592194634486900843105 := by
  unfold tailWord_4111914
  simp only [CollatzResearch.WordTrace]
  refine ⟨37493456106311327961653699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99982549616830207897743197 37493456106311327961653699)
  ·
    refine ⟨56240184159466991942480549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37493456106311327961653699 56240184159466991942480549)
    ·
      refine ⟨10545034529900060989215103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56240184159466991942480549 10545034529900060989215103)
      ·
        refine ⟨15817551794850091483822655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10545034529900060989215103 15817551794850091483822655)
        ·
          refine ⟨23726327692275137225733983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15817551794850091483822655 23726327692275137225733983)
          ·
            refine ⟨35589491538412705838600975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23726327692275137225733983 35589491538412705838600975)
            ·
              refine ⟨53384237307619058757901463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35589491538412705838600975 53384237307619058757901463)
              ·
                refine ⟨80076355961428588136852195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53384237307619058757901463 80076355961428588136852195)
                ·
                  refine ⟨120114533942142882205278293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80076355961428588136852195 120114533942142882205278293)
                  ·
                    refine ⟨1407592194634486900843105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 120114533942142882205278293 1407592194634486900843105)
                    ·
                      rfl

theorem cell22_4111914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_4111914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4111914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4111914 prefixEnd_4111914 := by exact prefixLift 4111914
  have htrace : WordTrace (prefixWord ++ tailWord_4111914) baseStart_4111914 baseEnd_4111914 := by
    simpa [prefixWord, tailWord_4111914, baseEnd_4111914] using wordTrace_append hprefix tailTrace_4111914
  have hstable : (prefixWord ++ tailWord_4111914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4111914).length < 2 ^ (prefixWord ++ tailWord_4111914).sum := by decide
  have hdescent : baseEnd_4111914 < baseStart_4111914 := by decide
  rcases family_descends (prefixWord ++ tailWord_4111914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4111933 : List Nat := [1, 4, 1, 3, 3, 1, 1, 2, 3, 3]
def baseStart_4111933 : Nat := 118140960795 + 4111933 * 2 ^ 59
def prefixEnd_4111933 : Nat := 4983230072969 + 3 ^ 40 * 4111933 * 2
def baseEnd_4111933 : Nat := 1407598698722777184618047

theorem tailTrace_4111933 : CollatzResearch.WordTrace tailWord_4111933 prefixEnd_4111933 1407598698722777184618047 := by
  unfold tailWord_4111933
  simp only [CollatzResearch.WordTrace]
  refine ⟨149974517412176478091556453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99983011608117652061037635 149974517412176478091556453)
  ·
    refine ⟨28120222014783089642166835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149974517412176478091556453 28120222014783089642166835)
    ·
      refine ⟨42180333022174634463250253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28120222014783089642166835 42180333022174634463250253)
      ·
        refine ⟨15817624883315487923718845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42180333022174634463250253 15817624883315487923718845)
        ·
          refine ⟨5931609331243307971394567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15817624883315487923718845 5931609331243307971394567)
          ·
            refine ⟨8897413996864961957091851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5931609331243307971394567 8897413996864961957091851)
            ·
              refine ⟨13346120995297442935637777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8897413996864961957091851 13346120995297442935637777)
              ·
                refine ⟨10009590746473082201728333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13346120995297442935637777 10009590746473082201728333)
                ·
                  refine ⟨3753596529927405825648125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10009590746473082201728333 3753596529927405825648125)
                  ·
                    refine ⟨1407598698722777184618047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3753596529927405825648125 1407598698722777184618047)
                    ·
                      rfl

theorem cell22_4111933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 2, 3, 3].length) (baseStart_4111933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4111933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4111933 prefixEnd_4111933 := by exact prefixLift 4111933
  have htrace : WordTrace (prefixWord ++ tailWord_4111933) baseStart_4111933 baseEnd_4111933 := by
    simpa [prefixWord, tailWord_4111933, baseEnd_4111933] using wordTrace_append hprefix tailTrace_4111933
  have hstable : (prefixWord ++ tailWord_4111933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4111933).length < 2 ^ (prefixWord ++ tailWord_4111933).sum := by decide
  have hdescent : baseEnd_4111933 < baseStart_4111933 := by decide
  rcases family_descends (prefixWord ++ tailWord_4111933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4112036 : List Nat := [2, 3, 1, 2, 2, 3, 2, 7]
def baseStart_4112036 : Nat := 118140960795 + 4112036 * 2 ^ 59
def prefixEnd_4112036 : Nat := 4983230072969 + 3 ^ 40 * 4112036 * 2
def baseEnd_4112036 : Nat := 156403773080857694365859

theorem tailTrace_4112036 : CollatzResearch.WordTrace tailWord_4112036 prefixEnd_4112036 156403773080857694365859 := by
  unfold tailWord_4112036
  simp only [CollatzResearch.WordTrace]
  refine ⟨74989137065401663341277981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99985516087202217788370641 74989137065401663341277981)
  ·
    refine ⟨28120926399525623752979243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74989137065401663341277981 28120926399525623752979243)
    ·
      refine ⟨42181389599288435629468865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28120926399525623752979243 42181389599288435629468865)
      ·
        refine ⟨31636042199466326722101649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42181389599288435629468865 31636042199466326722101649)
        ·
          refine ⟨23727031649599745041576237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31636042199466326722101649 23727031649599745041576237)
          ·
            refine ⟨8897636868599904390591089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23727031649599745041576237 8897636868599904390591089)
            ·
              refine ⟨6673227651449928292943317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8897636868599904390591089 6673227651449928292943317)
              ·
                refine ⟨156403773080857694365859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6673227651449928292943317 156403773080857694365859)
                ·
                  rfl

theorem cell22_4112036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 2, 7].length) (baseStart_4112036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4112036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4112036 prefixEnd_4112036 := by exact prefixLift 4112036
  have htrace : WordTrace (prefixWord ++ tailWord_4112036) baseStart_4112036 baseEnd_4112036 := by
    simpa [prefixWord, tailWord_4112036, baseEnd_4112036] using wordTrace_append hprefix tailTrace_4112036
  have hstable : (prefixWord ++ tailWord_4112036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4112036).length < 2 ^ (prefixWord ++ tailWord_4112036).sum := by decide
  have hdescent : baseEnd_4112036 < baseStart_4112036 := by decide
  rcases family_descends (prefixWord ++ tailWord_4112036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4112051 : List Nat := [1, 1, 1, 2, 3, 3, 2, 1, 5, 3]
def baseStart_4112051 : Nat := 118140960795 + 4112051 * 2 ^ 59
def prefixEnd_4112051 : Nat := 4983230072969 + 3 ^ 40 * 4112051 * 2
def baseEnd_4112051 : Nat := 1407639092534264210167685

theorem tailTrace_4112051 : CollatzResearch.WordTrace tailWord_4112051 prefixEnd_4112051 1407639092534264210167685 := by
  unfold tailWord_4112051
  simp only [CollatzResearch.WordTrace]
  refine ⟨149978821225748984244352007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99985880817165989496234671 149978821225748984244352007)
  ·
    refine ⟨224968231838623476366528011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149978821225748984244352007 224968231838623476366528011)
    ·
      refine ⟨337452347757935214549792017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224968231838623476366528011 337452347757935214549792017)
      ·
        refine ⟨253089260818451410912344013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 337452347757935214549792017 253089260818451410912344013)
        ·
          refine ⟨94908472806919279092129005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 253089260818451410912344013 94908472806919279092129005)
          ·
            refine ⟨35590677302594729659548377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94908472806919279092129005 35590677302594729659548377)
            ·
              refine ⟨26693007976946047244661283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35590677302594729659548377 26693007976946047244661283)
              ·
                refine ⟨40039511965419070866991925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26693007976946047244661283 40039511965419070866991925)
                ·
                  refine ⟨3753704246758037893780493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40039511965419070866991925 3753704246758037893780493)
                  ·
                    refine ⟨1407639092534264210167685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3753704246758037893780493 1407639092534264210167685)
                    ·
                      rfl

theorem cell22_4112051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 1, 5, 3].length) (baseStart_4112051 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4112051 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4112051 prefixEnd_4112051 := by exact prefixLift 4112051
  have htrace : WordTrace (prefixWord ++ tailWord_4112051) baseStart_4112051 baseEnd_4112051 := by
    simpa [prefixWord, tailWord_4112051, baseEnd_4112051] using wordTrace_append hprefix tailTrace_4112051
  have hstable : (prefixWord ++ tailWord_4112051).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4112051).length < 2 ^ (prefixWord ++ tailWord_4112051).sum := by decide
  have hdescent : baseEnd_4112051 < baseStart_4112051 := by decide
  rcases family_descends (prefixWord ++ tailWord_4112051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4112079 : List Nat := [1, 1, 2, 1, 1, 3, 1, 2, 3, 7]
def baseStart_4112079 : Nat := 118140960795 + 4112079 * 2 ^ 59
def prefixEnd_4112079 : Nat := 4983230072969 + 3 ^ 40 * 4112079 * 2
def baseEnd_4112079 : Nat := 1407648677506481470467599

theorem tailTrace_4112079 : CollatzResearch.WordTrace tailWord_4112079 prefixEnd_4112079 1407648677506481470467599 := by
  unfold tailWord_4112079
  simp only [CollatzResearch.WordTrace]
  refine ⟨149979842469647545026371291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99986561646431696684247527 149979842469647545026371291)
  ·
    refine ⟨224969763704471317539556937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149979842469647545026371291 224969763704471317539556937)
    ·
      refine ⟨168727322778353488154667703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224969763704471317539556937 168727322778353488154667703)
      ·
        refine ⟨253090984167530232232001555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168727322778353488154667703 253090984167530232232001555)
        ·
          refine ⟨379636476251295348348002333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253090984167530232232001555 379636476251295348348002333)
          ·
            refine ⟨142363678594235755630500875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 379636476251295348348002333 142363678594235755630500875)
            ·
              refine ⟨213545517891353633445751313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142363678594235755630500875 213545517891353633445751313)
              ·
                refine ⟨160159138418515225084313485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 213545517891353633445751313 160159138418515225084313485)
                ·
                  refine ⟨60059676906943209406617557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 160159138418515225084313485 60059676906943209406617557)
                  ·
                    refine ⟨1407648677506481470467599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60059676906943209406617557 1407648677506481470467599)
                    ·
                      rfl

theorem cell22_4112079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 3, 7].length) (baseStart_4112079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4112079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4112079 prefixEnd_4112079 := by exact prefixLift 4112079
  have htrace : WordTrace (prefixWord ++ tailWord_4112079) baseStart_4112079 baseEnd_4112079 := by
    simpa [prefixWord, tailWord_4112079, baseEnd_4112079] using wordTrace_append hprefix tailTrace_4112079
  have hstable : (prefixWord ++ tailWord_4112079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4112079).length < 2 ^ (prefixWord ++ tailWord_4112079).sum := by decide
  have hdescent : baseEnd_4112079 < baseStart_4112079 := by decide
  rcases family_descends (prefixWord ++ tailWord_4112079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4112081 : List Nat := [1, 2, 2, 1, 2, 4, 1, 4, 5]
def baseStart_4112081 : Nat := 118140960795 + 4112081 * 2 ^ 59
def prefixEnd_4112081 : Nat := 4983230072969 + 3 ^ 40 * 4112081 * 2
def baseEnd_4112081 : Nat := 469216454049118043972531

theorem tailTrace_4112081 : CollatzResearch.WordTrace tailWord_4112081 prefixEnd_4112081 469216454049118043972531 := by
  unfold tailWord_4112081
  simp only [CollatzResearch.WordTrace]
  refine ⟨149979915415640299367944097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99986610277093532911962731 149979915415640299367944097)
  ·
    refine ⟨112484936561730224525958073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149979915415640299367944097 112484936561730224525958073)
    ·
      refine ⟨84363702421297668394468555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112484936561730224525958073 84363702421297668394468555)
      ·
        refine ⟨126545553631946502591702833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84363702421297668394468555 126545553631946502591702833)
        ·
          refine ⟨94909165223959876943777125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126545553631946502591702833 94909165223959876943777125)
          ·
            refine ⟨17795468479492476926958211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94909165223959876943777125 17795468479492476926958211)
            ·
              refine ⟨26693202719238715390437317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17795468479492476926958211 26693202719238715390437317)
              ·
                refine ⟨5004975509857259135706997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26693202719238715390437317 5004975509857259135706997)
                ·
                  refine ⟨469216454049118043972531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5004975509857259135706997 469216454049118043972531)
                  ·
                    rfl

theorem cell22_4112081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 4, 5].length) (baseStart_4112081 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4112081 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4112081 prefixEnd_4112081 := by exact prefixLift 4112081
  have htrace : WordTrace (prefixWord ++ tailWord_4112081) baseStart_4112081 baseEnd_4112081 := by
    simpa [prefixWord, tailWord_4112081, baseEnd_4112081] using wordTrace_append hprefix tailTrace_4112081
  have hstable : (prefixWord ++ tailWord_4112081).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4112081).length < 2 ^ (prefixWord ++ tailWord_4112081).sum := by decide
  have hdescent : baseEnd_4112081 < baseStart_4112081 := by decide
  rcases family_descends (prefixWord ++ tailWord_4112081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4112111 : List Nat := [1, 1, 2, 1, 5, 1, 1, 3, 3, 4]
def baseStart_4112111 : Nat := 118140960795 + 4112111 * 2 ^ 59
def prefixEnd_4112111 : Nat := 4983230072969 + 3 ^ 40 * 4112111 * 2
def baseEnd_4112111 : Nat := 1407659631760444053667501

theorem tailTrace_4112111 : CollatzResearch.WordTrace tailWord_4112111 prefixEnd_4112111 1407659631760444053667501 := by
  unfold tailWord_4112111
  simp only [CollatzResearch.WordTrace]
  refine ⟨149981009605531614491536187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99987339737021076327690791 149981009605531614491536187)
  ·
    refine ⟨224971514408297421737304281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149981009605531614491536187 224971514408297421737304281)
    ·
      refine ⟨168728635806223066302978211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224971514408297421737304281 168728635806223066302978211)
      ·
        refine ⟨253092953709334599454467317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168728635806223066302978211 253092953709334599454467317)
        ·
          refine ⟨23727464410250118698856311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 253092953709334599454467317 23727464410250118698856311)
          ·
            refine ⟨35591196615375178048284467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23727464410250118698856311 35591196615375178048284467)
            ·
              refine ⟨53386794923062767072426701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35591196615375178048284467 53386794923062767072426701)
              ·
                refine ⟨20020048096148537652160013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53386794923062767072426701 20020048096148537652160013)
                ·
                  refine ⟨7507518036055701619560005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20020048096148537652160013 7507518036055701619560005)
                  ·
                    refine ⟨1407659631760444053667501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7507518036055701619560005 1407659631760444053667501)
                    ·
                      rfl

theorem cell22_4112111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 3, 3, 4].length) (baseStart_4112111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4112111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4112111 prefixEnd_4112111 := by exact prefixLift 4112111
  have htrace : WordTrace (prefixWord ++ tailWord_4112111) baseStart_4112111 baseEnd_4112111 := by
    simpa [prefixWord, tailWord_4112111, baseEnd_4112111] using wordTrace_append hprefix tailTrace_4112111
  have hstable : (prefixWord ++ tailWord_4112111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4112111).length < 2 ^ (prefixWord ++ tailWord_4112111).sum := by decide
  have hdescent : baseEnd_4112111 < baseStart_4112111 := by decide
  rcases family_descends (prefixWord ++ tailWord_4112111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4112156 : List Nat := [2, 2, 3, 1, 1, 2, 1, 1, 3, 6]
def baseStart_4112156 : Nat := 118140960795 + 4112156 * 2 ^ 59
def prefixEnd_4112156 : Nat := 4983230072969 + 3 ^ 40 * 4112156 * 2
def baseEnd_4112156 : Nat := 1407675036180078936292363

theorem tailTrace_4112156 : CollatzResearch.WordTrace tailWord_4112156 prefixEnd_4112156 1407675036180078936292363 := by
  unfold tailWord_4112156
  simp only [CollatzResearch.WordTrace]
  refine ⟨74991325445184293588462161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99988433926912391451282881 74991325445184293588462161)
  ·
    refine ⟨56243494083888220191346621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74991325445184293588462161 56243494083888220191346621)
    ·
      refine ⟨21091310281458082571754983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56243494083888220191346621 21091310281458082571754983)
      ·
        refine ⟨31636965422187123857632475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21091310281458082571754983 31636965422187123857632475)
        ·
          refine ⟨47455448133280685786448713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31636965422187123857632475 47455448133280685786448713)
          ·
            refine ⟨35591586099960514339836535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47455448133280685786448713 35591586099960514339836535)
            ·
              refine ⟨53387379149940771509754803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35591586099960514339836535 53387379149940771509754803)
              ·
                refine ⟨80081068724911157264632205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53387379149940771509754803 80081068724911157264632205)
                ·
                  refine ⟨30030400771841683974237077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80081068724911157264632205 30030400771841683974237077)
                  ·
                    refine ⟨1407675036180078936292363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30030400771841683974237077 1407675036180078936292363)
                    ·
                      rfl

theorem cell22_4112156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 1, 3, 6].length) (baseStart_4112156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4112156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4112156 prefixEnd_4112156 := by exact prefixLift 4112156
  have htrace : WordTrace (prefixWord ++ tailWord_4112156) baseStart_4112156 baseEnd_4112156 := by
    simpa [prefixWord, tailWord_4112156, baseEnd_4112156] using wordTrace_append hprefix tailTrace_4112156
  have hstable : (prefixWord ++ tailWord_4112156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4112156).length < 2 ^ (prefixWord ++ tailWord_4112156).sum := by decide
  have hdescent : baseEnd_4112156 < baseStart_4112156 := by decide
  rcases family_descends (prefixWord ++ tailWord_4112156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4112190 : List Nat := [4, 2, 1, 2, 2, 2, 1, 2, 2, 4]
def baseStart_4112190 : Nat := 118140960795 + 4112190 * 2 ^ 59
def prefixEnd_4112190 : Nat := 4983230072969 + 3 ^ 40 * 4112190 * 2
def baseEnd_4112190 : Nat := 1407686675074914180942259

theorem tailTrace_4112190 : CollatzResearch.WordTrace tailWord_4112190 prefixEnd_4112190 1407686675074914180942259 := by
  unfold tailWord_4112190
  simp only [CollatzResearch.WordTrace]
  refine ⟨18747986371530676372957753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99989260648163607322441349 18747986371530676372957753)
  ·
    refine ⟨14060989778648007279718315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18747986371530676372957753 14060989778648007279718315)
    ·
      refine ⟨21091484667972010919577473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14060989778648007279718315 21091484667972010919577473)
      ·
        refine ⟨15818613500979008189683105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21091484667972010919577473 15818613500979008189683105)
        ·
          refine ⟨11863960125734256142262329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15818613500979008189683105 11863960125734256142262329)
          ·
            refine ⟨8897970094300692106696747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11863960125734256142262329 8897970094300692106696747)
            ·
              refine ⟨13346955141451038160045121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8897970094300692106696747 13346955141451038160045121)
              ·
                refine ⟨10010216356088278620033841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13346955141451038160045121 10010216356088278620033841)
                ·
                  refine ⟨7507662267066208965025381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10010216356088278620033841 7507662267066208965025381)
                  ·
                    refine ⟨1407686675074914180942259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7507662267066208965025381 1407686675074914180942259)
                    ·
                      rfl

theorem cell22_4112190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 2, 2, 4].length) (baseStart_4112190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4112190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4112190 prefixEnd_4112190 := by exact prefixLift 4112190
  have htrace : WordTrace (prefixWord ++ tailWord_4112190) baseStart_4112190 baseEnd_4112190 := by
    simpa [prefixWord, tailWord_4112190, baseEnd_4112190] using wordTrace_append hprefix tailTrace_4112190
  have hstable : (prefixWord ++ tailWord_4112190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4112190).length < 2 ^ (prefixWord ++ tailWord_4112190).sum := by decide
  have hdescent : baseEnd_4112190 < baseStart_4112190 := by decide
  rcases family_descends (prefixWord ++ tailWord_4112190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4112201 : List Nat := [1, 2, 1, 1, 2, 4, 2, 1, 2, 6]
def baseStart_4112201 : Nat := 118140960795 + 4112201 * 2 ^ 59
def prefixEnd_4112201 : Nat := 4983230072969 + 3 ^ 40 * 4112201 * 2
def baseEnd_4112201 : Nat := 1407690440599713818917225

theorem tailTrace_4112201 : CollatzResearch.WordTrace tailWord_4112201 prefixEnd_4112201 1407690440599713818917225 := by
  unfold tailWord_4112201
  simp only [CollatzResearch.WordTrace]
  refine ⟨149984292175205559862312457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99989528116803706574874971 149984292175205559862312457)
  ·
    refine ⟨112488219131404169896734343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149984292175205559862312457 112488219131404169896734343)
    ·
      refine ⟨168732328697106254845101515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112488219131404169896734343 168732328697106254845101515)
      ·
        refine ⟨253098493045659382267652273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168732328697106254845101515 253098493045659382267652273)
        ·
          refine ⟨189823869784244536700739205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 253098493045659382267652273 189823869784244536700739205)
          ·
            refine ⟨35591975584545850631388601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 189823869784244536700739205 35591975584545850631388601)
            ·
              refine ⟨26693981688409387973541451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35591975584545850631388601 26693981688409387973541451)
              ·
                refine ⟨40040972532614081960312177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26693981688409387973541451 40040972532614081960312177)
                ·
                  refine ⟨30030729399460561470234133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40040972532614081960312177 30030729399460561470234133)
                  ·
                    refine ⟨1407690440599713818917225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30030729399460561470234133 1407690440599713818917225)
                    ·
                      rfl

theorem cell22_4112201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 1, 2, 6].length) (baseStart_4112201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4112201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4112201 prefixEnd_4112201 := by exact prefixLift 4112201
  have htrace : WordTrace (prefixWord ++ tailWord_4112201) baseStart_4112201 baseEnd_4112201 := by
    simpa [prefixWord, tailWord_4112201, baseEnd_4112201] using wordTrace_append hprefix tailTrace_4112201
  have hstable : (prefixWord ++ tailWord_4112201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4112201).length < 2 ^ (prefixWord ++ tailWord_4112201).sum := by decide
  have hdescent : baseEnd_4112201 < baseStart_4112201 := by decide
  rcases family_descends (prefixWord ++ tailWord_4112201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4112205 : List Nat := [1, 6, 1, 2, 1, 2, 2, 7]
def baseStart_4112205 : Nat := 118140960795 + 4112205 * 2 ^ 59
def prefixEnd_4112205 : Nat := 4983230072969 + 3 ^ 40 * 4112205 * 2
def baseEnd_4112205 : Nat := 156410201097939904646357

theorem tailTrace_4112205 : CollatzResearch.WordTrace tailWord_4112205 prefixEnd_4112205 156410201097939904646357 := by
  unfold tailWord_4112205
  simp only [CollatzResearch.WordTrace]
  refine ⟨149984438067191068545458069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99989625378127379030305379 149984438067191068545458069)
  ·
    refine ⟨7030520534399581338068347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 149984438067191068545458069 7030520534399581338068347)
    ·
      refine ⟨10545780801599372007102521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7030520534399581338068347 10545780801599372007102521)
      ·
        refine ⟨7909335601199529005326891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10545780801599372007102521 7909335601199529005326891)
        ·
          refine ⟨11864003401799293507990337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7909335601199529005326891 11864003401799293507990337)
          ·
            refine ⟨8898002551349470130992753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11864003401799293507990337 8898002551349470130992753)
            ·
              refine ⟨6673501913512102598244565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8898002551349470130992753 6673501913512102598244565)
              ·
                refine ⟨156410201097939904646357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6673501913512102598244565 156410201097939904646357)
                ·
                  rfl

theorem cell22_4112205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 2, 7].length) (baseStart_4112205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4112205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4112205 prefixEnd_4112205 := by exact prefixLift 4112205
  have htrace : WordTrace (prefixWord ++ tailWord_4112205) baseStart_4112205 baseEnd_4112205 := by
    simpa [prefixWord, tailWord_4112205, baseEnd_4112205] using wordTrace_append hprefix tailTrace_4112205
  have hstable : (prefixWord ++ tailWord_4112205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4112205).length < 2 ^ (prefixWord ++ tailWord_4112205).sum := by decide
  have hdescent : baseEnd_4112205 < baseStart_4112205 := by decide
  rcases family_descends (prefixWord ++ tailWord_4112205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4112368 : List Nat := [2, 1, 1, 1, 3, 2, 4, 1, 7]
def baseStart_4112368 : Nat := 118140960795 + 4112368 * 2 ^ 59
def prefixEnd_4112368 : Nat := 4983230072969 + 3 ^ 40 * 4112368 * 2
def baseEnd_4112368 : Nat := 469249202704193683330571

theorem tailTrace_4112368 : CollatzResearch.WordTrace tailWord_4112368 prefixEnd_4112368 469249202704193683330571 := by
  unfold tailWord_4112368
  simp only [CollatzResearch.WordTrace]
  refine ⟨74995191582800273691820879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99993588777067031589094505 74995191582800273691820879)
  ·
    refine ⟨112492787374200410537731319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74995191582800273691820879 112492787374200410537731319)
    ·
      refine ⟨168739181061300615806596979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112492787374200410537731319 168739181061300615806596979)
      ·
        refine ⟨253108771591950923709895469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168739181061300615806596979 253108771591950923709895469)
        ·
          refine ⟨94915789346981596391210801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 253108771591950923709895469 94915789346981596391210801)
          ·
            refine ⟨71186842010236197293408101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94915789346981596391210801 71186842010236197293408101)
            ·
              refine ⟨13347532876919286992514019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71186842010236197293408101 13347532876919286992514019)
              ·
                refine ⟨20021299315378930488771029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13347532876919286992514019 20021299315378930488771029)
                ·
                  refine ⟨469249202704193683330571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20021299315378930488771029 469249202704193683330571)
                  ·
                    rfl

theorem cell22_4112368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 1, 7].length) (baseStart_4112368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4112368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4112368 prefixEnd_4112368 := by exact prefixLift 4112368
  have htrace : WordTrace (prefixWord ++ tailWord_4112368) baseStart_4112368 baseEnd_4112368 := by
    simpa [prefixWord, tailWord_4112368, baseEnd_4112368] using wordTrace_append hprefix tailTrace_4112368
  have hstable : (prefixWord ++ tailWord_4112368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4112368).length < 2 ^ (prefixWord ++ tailWord_4112368).sum := by decide
  have hdescent : baseEnd_4112368 < baseStart_4112368 := by decide
  rcases family_descends (prefixWord ++ tailWord_4112368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4112383 : List Nat := [1, 1, 2, 2, 1, 2, 1, 5, 2, 5]
def baseStart_4112383 : Nat := 118140960795 + 4112383 * 2 ^ 59
def prefixEnd_4112383 : Nat := 4983230072969 + 3 ^ 40 * 4112383 * 2
def baseEnd_4112383 : Nat := 1407752742919126010866667

theorem tailTrace_4112383 : CollatzResearch.WordTrace tailWord_4112383 prefixEnd_4112383 1407752742919126010866667 := by
  unfold tailWord_4112383
  simp only [CollatzResearch.WordTrace]
  refine ⟨149990930260546204945437803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99993953507030803296958535 149990930260546204945437803)
  ·
    refine ⟨224986395390819307418156705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149990930260546204945437803 224986395390819307418156705)
    ·
      refine ⟨168739796543114480563617529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224986395390819307418156705 168739796543114480563617529)
      ·
        refine ⟨126554847407335860422713147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168739796543114480563617529 126554847407335860422713147)
        ·
          refine ⟨189832271111003790634069721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126554847407335860422713147 189832271111003790634069721)
          ·
            refine ⟨142374203333252842975552291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189832271111003790634069721 142374203333252842975552291)
            ·
              refine ⟨213561304999879264463328437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142374203333252842975552291 213561304999879264463328437)
              ·
                refine ⟨20021372343738681043437041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 213561304999879264463328437 20021372343738681043437041)
                ·
                  refine ⟨15016029257804010782577781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20021372343738681043437041 15016029257804010782577781)
                  ·
                    refine ⟨1407752742919126010866667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15016029257804010782577781 1407752742919126010866667)
                    ·
                      rfl

theorem cell22_4112383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 5, 2, 5].length) (baseStart_4112383 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4112383 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4112383 prefixEnd_4112383 := by exact prefixLift 4112383
  have htrace : WordTrace (prefixWord ++ tailWord_4112383) baseStart_4112383 baseEnd_4112383 := by
    simpa [prefixWord, tailWord_4112383, baseEnd_4112383] using wordTrace_append hprefix tailTrace_4112383
  have hstable : (prefixWord ++ tailWord_4112383).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4112383).length < 2 ^ (prefixWord ++ tailWord_4112383).sum := by decide
  have hdescent : baseEnd_4112383 < baseStart_4112383 := by decide
  rcases family_descends (prefixWord ++ tailWord_4112383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4112385 : List Nat := [1, 2, 4, 1, 2, 1, 3, 3, 5]
def baseStart_4112385 : Nat := 118140960795 + 4112385 * 2 ^ 59
def prefixEnd_4112385 : Nat := 4983230072969 + 3 ^ 40 * 4112385 * 2
def baseEnd_4112385 : Nat := 469251142519999557438887

theorem tailTrace_4112385 : CollatzResearch.WordTrace tailWord_4112385 prefixEnd_4112385 469251142519999557438887 := by
  unfold tailWord_4112385
  simp only [CollatzResearch.WordTrace]
  refine ⟨149991003206538959287010609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99994002137692639524673739 149991003206538959287010609)
  ·
    refine ⟨112493252404904219465257957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149991003206538959287010609 112493252404904219465257957)
    ·
      refine ⟨21092484825919541149735867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112493252404904219465257957 21092484825919541149735867)
      ·
        refine ⟨31638727238879311724603801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21092484825919541149735867 31638727238879311724603801)
        ·
          refine ⟨23729045429159483793452851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31638727238879311724603801 23729045429159483793452851)
          ·
            refine ⟨35593568143739225690179277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23729045429159483793452851 35593568143739225690179277)
            ·
              refine ⟨13347588053902209633817229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35593568143739225690179277 13347588053902209633817229)
              ·
                refine ⟨5005345520213328612681461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13347588053902209633817229 5005345520213328612681461)
                ·
                  refine ⟨469251142519999557438887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5005345520213328612681461 469251142519999557438887)
                  ·
                    rfl

theorem cell22_4112385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 3, 5].length) (baseStart_4112385 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4112385 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4112385 prefixEnd_4112385 := by exact prefixLift 4112385
  have htrace : WordTrace (prefixWord ++ tailWord_4112385) baseStart_4112385 baseEnd_4112385 := by
    simpa [prefixWord, tailWord_4112385, baseEnd_4112385] using wordTrace_append hprefix tailTrace_4112385
  have hstable : (prefixWord ++ tailWord_4112385).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4112385).length < 2 ^ (prefixWord ++ tailWord_4112385).sum := by decide
  have hdescent : baseEnd_4112385 < baseStart_4112385 := by decide
  rcases family_descends (prefixWord ++ tailWord_4112385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4112443 : List Nat := [1, 1, 1, 1, 1, 2, 1, 5, 3, 6]
def baseStart_4112443 : Nat := 118140960795 + 4112443 * 2 ^ 59
def prefixEnd_4112443 : Nat := 4983230072969 + 3 ^ 40 * 4112443 * 2
def baseEnd_4112443 : Nat := 1407773282145305854366483

theorem tailTrace_4112443 : CollatzResearch.WordTrace tailWord_4112443 prefixEnd_4112443 1407773282145305854366483 := by
  unfold tailWord_4112443
  simp only [CollatzResearch.WordTrace]
  refine ⟨149993118640328835192621983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99995412426885890128414655 149993118640328835192621983)
  ·
    refine ⟨224989677960493252788932975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149993118640328835192621983 224989677960493252788932975)
    ·
      refine ⟨337484516940739879183399463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224989677960493252788932975 337484516940739879183399463)
      ·
        refine ⟨506226775411109818775099195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337484516940739879183399463 506226775411109818775099195)
        ·
          refine ⟨759340163116664728162648793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 506226775411109818775099195 759340163116664728162648793)
          ·
            refine ⟨569505122337498546121986595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 759340163116664728162648793 569505122337498546121986595)
            ·
              refine ⟨854257683506247819182979893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 569505122337498546121986595 854257683506247819182979893)
              ·
                refine ⟨80086657828710733048404365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 854257683506247819182979893 80086657828710733048404365)
                ·
                  refine ⟨30032496685766524893151637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80086657828710733048404365 30032496685766524893151637)
                  ·
                    refine ⟨1407773282145305854366483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30032496685766524893151637 1407773282145305854366483)
                    ·
                      rfl

theorem cell22_4112443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 5, 3, 6].length) (baseStart_4112443 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4112443 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4112443 prefixEnd_4112443 := by exact prefixLift 4112443
  have htrace : WordTrace (prefixWord ++ tailWord_4112443) baseStart_4112443 baseEnd_4112443 := by
    simpa [prefixWord, tailWord_4112443, baseEnd_4112443] using wordTrace_append hprefix tailTrace_4112443
  have hstable : (prefixWord ++ tailWord_4112443).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4112443).length < 2 ^ (prefixWord ++ tailWord_4112443).sum := by decide
  have hdescent : baseEnd_4112443 < baseStart_4112443 := by decide
  rcases family_descends (prefixWord ++ tailWord_4112443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4112466 : List Nat := [3, 2, 2, 1, 4, 2, 2, 1, 1, 4]
def baseStart_4112466 : Nat := 118140960795 + 4112466 * 2 ^ 59
def prefixEnd_4112466 : Nat := 4983230072969 + 3 ^ 40 * 4112466 * 2
def baseEnd_4112466 : Nat := 1407781155515341461041413

theorem tailTrace_4112466 : CollatzResearch.WordTrace tailWord_4112466 prefixEnd_4112466 1407781155515341461041413 := by
  unfold tailWord_4112466
  simp only [CollatzResearch.WordTrace]
  refine ⟨37498489379811377530177313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99995971679497006747139501 37498489379811377530177313)
  ·
    refine ⟨28123867034858533147632985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37498489379811377530177313 28123867034858533147632985)
    ·
      refine ⟨21092900276143899860724739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28123867034858533147632985 21092900276143899860724739)
      ·
        refine ⟨31639350414215849791087109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21092900276143899860724739 31639350414215849791087109)
        ·
          refine ⟨5932378202665471835828833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31639350414215849791087109 5932378202665471835828833)
          ·
            refine ⟨4449283651999103876871625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5932378202665471835828833 4449283651999103876871625)
            ·
              refine ⟨3336962738999327907653719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4449283651999103876871625 3336962738999327907653719)
              ·
                refine ⟨5005444108498991861480579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3336962738999327907653719 5005444108498991861480579)
                ·
                  refine ⟨7508166162748487792220869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5005444108498991861480579 7508166162748487792220869)
                  ·
                    refine ⟨1407781155515341461041413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7508166162748487792220869 1407781155515341461041413)
                    ·
                      rfl

theorem cell22_4112466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 2, 1, 1, 4].length) (baseStart_4112466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4112466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4112466 prefixEnd_4112466 := by exact prefixLift 4112466
  have htrace : WordTrace (prefixWord ++ tailWord_4112466) baseStart_4112466 baseEnd_4112466 := by
    simpa [prefixWord, tailWord_4112466, baseEnd_4112466] using wordTrace_append hprefix tailTrace_4112466
  have hstable : (prefixWord ++ tailWord_4112466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4112466).length < 2 ^ (prefixWord ++ tailWord_4112466).sum := by decide
  have hdescent : baseEnd_4112466 < baseStart_4112466 := by decide
  rcases family_descends (prefixWord ++ tailWord_4112466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4112567 : List Nat := [1, 1, 3, 1, 4, 3, 1, 1, 3, 4]
def baseStart_4112567 : Nat := 118140960795 + 4112567 * 2 ^ 59
def prefixEnd_4112567 : Nat := 4983230072969 + 3 ^ 40 * 4112567 * 2
def baseEnd_4112567 : Nat := 1407815729879410864266103

theorem tailTrace_4112567 : CollatzResearch.WordTrace tailWord_4112567 prefixEnd_4112567 1407815729879410864266103 := by
  unfold tailWord_4112567
  simp only [CollatzResearch.WordTrace]
  refine ⟨149997641291879604370135955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99998427527919736246757303 149997641291879604370135955)
  ·
    refine ⟨224996461937819406555203933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149997641291879604370135955 224996461937819406555203933)
    ·
      refine ⟨84373673226682277458201475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224996461937819406555203933 84373673226682277458201475)
      ·
        refine ⟨126560509840023416187302213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84373673226682277458201475 126560509840023416187302213)
        ·
          refine ⟨23730095595004390535119165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 126560509840023416187302213 23730095595004390535119165)
          ·
            refine ⟨8898785848126646450669687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23730095595004390535119165 8898785848126646450669687)
            ·
              refine ⟨13348178772189969676004531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8898785848126646450669687 13348178772189969676004531)
              ·
                refine ⟨20022268158284954514006797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13348178772189969676004531 20022268158284954514006797)
                ·
                  refine ⟨7508350559356857942752549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20022268158284954514006797 7508350559356857942752549)
                  ·
                    refine ⟨1407815729879410864266103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7508350559356857942752549 1407815729879410864266103)
                    ·
                      rfl

theorem cell22_4112567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 1, 3, 4].length) (baseStart_4112567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4112567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4112567 prefixEnd_4112567 := by exact prefixLift 4112567
  have htrace : WordTrace (prefixWord ++ tailWord_4112567) baseStart_4112567 baseEnd_4112567 := by
    simpa [prefixWord, tailWord_4112567, baseEnd_4112567] using wordTrace_append hprefix tailTrace_4112567
  have hstable : (prefixWord ++ tailWord_4112567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4112567).length < 2 ^ (prefixWord ++ tailWord_4112567).sum := by decide
  have hdescent : baseEnd_4112567 < baseStart_4112567 := by decide
  rcases family_descends (prefixWord ++ tailWord_4112567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4112627 : List Nat := [1, 1, 1, 2, 2, 4, 5, 6]
def baseStart_4112627 : Nat := 118140960795 + 4112627 * 2 ^ 59
def prefixEnd_4112627 : Nat := 4983230072969 + 3 ^ 40 * 4112627 * 2
def baseEnd_4112627 : Nat := 156426252122843411973991

theorem tailTrace_4112627 : CollatzResearch.WordTrace tailWord_4112627 prefixEnd_4112627 156426252122843411973991 := by
  unfold tailWord_4112627
  simp only [CollatzResearch.WordTrace]
  refine ⟨149999829671662234617320135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99999886447774823078213423 149999829671662234617320135)
  ·
    refine ⟨224999744507493351925980203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149999829671662234617320135 224999744507493351925980203)
    ·
      refine ⟨337499616761240027888970305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224999744507493351925980203 337499616761240027888970305)
      ·
        refine ⟨253124712570930020916727729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 337499616761240027888970305 253124712570930020916727729)
        ·
          refine ⟨189843534428197515687545797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 253124712570930020916727729 189843534428197515687545797)
          ·
            refine ⟨35595662705287034191414837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 189843534428197515687545797 35595662705287034191414837)
            ·
              refine ⟨3337093378620659455445141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35595662705287034191414837 3337093378620659455445141)
              ·
                refine ⟨156426252122843411973991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3337093378620659455445141 156426252122843411973991)
                ·
                  rfl

theorem cell22_4112627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 5, 6].length) (baseStart_4112627 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4112627 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4112627 prefixEnd_4112627 := by exact prefixLift 4112627
  have htrace : WordTrace (prefixWord ++ tailWord_4112627) baseStart_4112627 baseEnd_4112627 := by
    simpa [prefixWord, tailWord_4112627, baseEnd_4112627] using wordTrace_append hprefix tailTrace_4112627
  have hstable : (prefixWord ++ tailWord_4112627).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4112627).length < 2 ^ (prefixWord ++ tailWord_4112627).sum := by decide
  have hdescent : baseEnd_4112627 < baseStart_4112627 := by decide
  rcases family_descends (prefixWord ++ tailWord_4112627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4112747 : List Nat := [1, 1, 1, 1, 2, 2, 2, 2, 6, 4]
def baseStart_4112747 : Nat := 118140960795 + 4112747 * 2 ^ 59
def prefixEnd_4112747 : Nat := 4983230072969 + 3 ^ 40 * 4112747 * 2
def baseEnd_4112747 : Nat := 1407877347557950394765551

theorem tailTrace_4112747 : CollatzResearch.WordTrace tailWord_4112747 prefixEnd_4112747 1407877347557950394765551 := by
  unfold tailWord_4112747
  simp only [CollatzResearch.WordTrace]
  refine ⟨150004206431227495111688495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100002804287484996741125663 150004206431227495111688495)
  ·
    refine ⟨225006309646841242667532743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150004206431227495111688495 225006309646841242667532743)
    ·
      refine ⟨337509464470261864001299115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225006309646841242667532743 337509464470261864001299115)
      ·
        refine ⟨506264196705392796001948673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337509464470261864001299115 506264196705392796001948673)
        ·
          refine ⟨379698147529044597001461505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 506264196705392796001948673 379698147529044597001461505)
          ·
            refine ⟨284773610646783447751096129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 379698147529044597001461505 284773610646783447751096129)
            ·
              refine ⟨213580207985087585813322097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 284773610646783447751096129 213580207985087585813322097)
              ·
                refine ⟨160185155988815689359991573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 213580207985087585813322097 160185155988815689359991573)
                ·
                  refine ⟨7508679186975735438749605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 160185155988815689359991573 7508679186975735438749605)
                  ·
                    refine ⟨1407877347557950394765551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7508679186975735438749605 1407877347557950394765551)
                    ·
                      rfl

theorem cell22_4112747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 6, 4].length) (baseStart_4112747 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4112747 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4112747 prefixEnd_4112747 := by exact prefixLift 4112747
  have htrace : WordTrace (prefixWord ++ tailWord_4112747) baseStart_4112747 baseEnd_4112747 := by
    simpa [prefixWord, tailWord_4112747, baseEnd_4112747] using wordTrace_append hprefix tailTrace_4112747
  have hstable : (prefixWord ++ tailWord_4112747).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4112747).length < 2 ^ (prefixWord ++ tailWord_4112747).sum := by decide
  have hdescent : baseEnd_4112747 < baseStart_4112747 := by decide
  rcases family_descends (prefixWord ++ tailWord_4112747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4112749 : List Nat := [1, 5, 1, 1, 1, 2, 3, 2, 1, 5]
def baseStart_4112749 : Nat := 118140960795 + 4112749 * 2 ^ 59
def prefixEnd_4112749 : Nat := 4983230072969 + 3 ^ 40 * 4112749 * 2
def baseEnd_4112749 : Nat := 1407878032198823056215545

theorem tailTrace_4112749 : CollatzResearch.WordTrace tailWord_4112749 prefixEnd_4112749 1407878032198823056215545 := by
  unfold tailWord_4112749
  simp only [CollatzResearch.WordTrace]
  refine ⟨150004279377220249453261301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100002852918146832968840867 150004279377220249453261301)
  ·
    refine ⟨14062901191614398386243247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 150004279377220249453261301 14062901191614398386243247)
    ·
      refine ⟨21094351787421597579364871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14062901191614398386243247 21094351787421597579364871)
      ·
        refine ⟨31641527681132396369047307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21094351787421597579364871 31641527681132396369047307)
        ·
          refine ⟨47462291521698594553570961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31641527681132396369047307 47462291521698594553570961)
          ·
            refine ⟨35596718641273945915178221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47462291521698594553570961 35596718641273945915178221)
            ·
              refine ⟨13348769490477729718191833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35596718641273945915178221 13348769490477729718191833)
              ·
                refine ⟨10011577117858297288643875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13348769490477729718191833 10011577117858297288643875)
                ·
                  refine ⟨15017365676787445932965813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10011577117858297288643875 15017365676787445932965813)
                  ·
                    refine ⟨1407878032198823056215545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15017365676787445932965813 1407878032198823056215545)
                    ·
                      rfl

theorem cell22_4112749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 2, 1, 5].length) (baseStart_4112749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4112749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4112749 prefixEnd_4112749 := by exact prefixLift 4112749
  have htrace : WordTrace (prefixWord ++ tailWord_4112749) baseStart_4112749 baseEnd_4112749 := by
    simpa [prefixWord, tailWord_4112749, baseEnd_4112749] using wordTrace_append hprefix tailTrace_4112749
  have hstable : (prefixWord ++ tailWord_4112749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4112749).length < 2 ^ (prefixWord ++ tailWord_4112749).sum := by decide
  have hdescent : baseEnd_4112749 < baseStart_4112749 := by decide
  rcases family_descends (prefixWord ++ tailWord_4112749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4112779 : List Nat := [1, 1, 1, 1, 4, 6, 1, 7]
def baseStart_4112779 : Nat := 118140960795 + 4112779 * 2 ^ 59
def prefixEnd_4112779 : Nat := 4983230072969 + 3 ^ 40 * 4112779 * 2
def baseEnd_4112779 : Nat := 156432033534656997551717

theorem tailTrace_4112779 : CollatzResearch.WordTrace tailWord_4112779 prefixEnd_4112779 156432033534656997551717 := by
  unfold tailWord_4112779
  simp only [CollatzResearch.WordTrace]
  refine ⟨150005373567111564576853391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100003582378074376384568927 150005373567111564576853391)
  ·
    refine ⟨225008060350667346865280087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150005373567111564576853391 225008060350667346865280087)
    ·
      refine ⟨337512090526001020297920131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225008060350667346865280087 337512090526001020297920131)
      ·
        refine ⟨506268135789001530446880197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337512090526001020297920131 506268135789001530446880197)
        ·
          refine ⟨94925275460437786958790037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 506268135789001530446880197 94925275460437786958790037)
          ·
            refine ⟨4449622287208021263693283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 94925275460437786958790037 4449622287208021263693283)
            ·
              refine ⟨6674433430812031895539925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4449622287208021263693283 6674433430812031895539925)
              ·
                refine ⟨156432033534656997551717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6674433430812031895539925 156432033534656997551717)
                ·
                  rfl

theorem cell22_4112779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 1, 7].length) (baseStart_4112779 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4112779 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4112779 prefixEnd_4112779 := by exact prefixLift 4112779
  have htrace : WordTrace (prefixWord ++ tailWord_4112779) baseStart_4112779 baseEnd_4112779 := by
    simpa [prefixWord, tailWord_4112779, baseEnd_4112779] using wordTrace_append hprefix tailTrace_4112779
  have hstable : (prefixWord ++ tailWord_4112779).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4112779).length < 2 ^ (prefixWord ++ tailWord_4112779).sum := by decide
  have hdescent : baseEnd_4112779 < baseStart_4112779 := by decide
  rcases family_descends (prefixWord ++ tailWord_4112779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4112798 : List Nat := [4, 3, 1, 2, 1, 1, 3, 1, 2, 4]
def baseStart_4112798 : Nat := 118140960795 + 4112798 * 2 ^ 59
def prefixEnd_4112798 : Nat := 4983230072969 + 3 ^ 40 * 4112798 * 2
def baseEnd_4112798 : Nat := 1407894805900203261740395

theorem tailTrace_4112798 : CollatzResearch.WordTrace tailWord_4112798 prefixEnd_4112798 1407894805900203261740395 := by
  unfold tailWord_4112798
  simp only [CollatzResearch.WordTrace]
  refine ⟨18750758319255341352724381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100004044369361820547863365 18750758319255341352724381)
  ·
    refine ⟨7031534369720753007271643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18750758319255341352724381 7031534369720753007271643)
    ·
      refine ⟨10547301554581129510907465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7031534369720753007271643 10547301554581129510907465)
      ·
        refine ⟨7910476165935847133180599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10547301554581129510907465 7910476165935847133180599)
        ·
          refine ⟨11865714248903770699770899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7910476165935847133180599 11865714248903770699770899)
          ·
            refine ⟨17798571373355656049656349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11865714248903770699770899 17798571373355656049656349)
            ·
              refine ⟨6674464265008371018621131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17798571373355656049656349 6674464265008371018621131)
              ·
                refine ⟨10011696397512556527931697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6674464265008371018621131 10011696397512556527931697)
                ·
                  refine ⟨7508772298134417395948773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10011696397512556527931697 7508772298134417395948773)
                  ·
                    refine ⟨1407894805900203261740395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7508772298134417395948773 1407894805900203261740395)
                    ·
                      rfl

theorem cell22_4112798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_4112798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4112798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4112798 prefixEnd_4112798 := by exact prefixLift 4112798
  have htrace : WordTrace (prefixWord ++ tailWord_4112798) baseStart_4112798 baseEnd_4112798 := by
    simpa [prefixWord, tailWord_4112798, baseEnd_4112798] using wordTrace_append hprefix tailTrace_4112798
  have hstable : (prefixWord ++ tailWord_4112798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4112798).length < 2 ^ (prefixWord ++ tailWord_4112798).sum := by decide
  have hdescent : baseEnd_4112798 < baseStart_4112798 := by decide
  rcases family_descends (prefixWord ++ tailWord_4112798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4112828 : List Nat := [2, 2, 2, 4, 1, 2, 2, 1, 3, 3]
def baseStart_4112828 : Nat := 118140960795 + 4112828 * 2 ^ 59
def prefixEnd_4112828 : Nat := 4983230072969 + 3 ^ 40 * 4112828 * 2
def baseEnd_4112828 : Nat := 1407905075513293183490303

theorem tailTrace_4112828 : CollatzResearch.WordTrace tailWord_4112828 prefixEnd_4112828 1407905075513293183490303 := by
  unfold tailWord_4112828
  simp only [CollatzResearch.WordTrace]
  refine ⟨75003580371967022972693569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100004773829289363963591425 75003580371967022972693569)
  ·
    refine ⟨56252685278975267229520177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75003580371967022972693569 56252685278975267229520177)
    ·
      refine ⟨42189513959231450422140133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56252685278975267229520177 42189513959231450422140133)
      ·
        refine ⟨7910533867355896954151275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42189513959231450422140133 7910533867355896954151275)
        ·
          refine ⟨11865800801033845431226913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7910533867355896954151275 11865800801033845431226913)
          ·
            refine ⟨8899350600775384073420185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11865800801033845431226913 8899350600775384073420185)
            ·
              refine ⟨6674512950581538055065139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8899350600775384073420185 6674512950581538055065139)
              ·
                refine ⟨10011769425872307082597709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6674512950581538055065139 10011769425872307082597709)
                ·
                  refine ⟨3754413534702115155974141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10011769425872307082597709 3754413534702115155974141)
                  ·
                    refine ⟨1407905075513293183490303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3754413534702115155974141 1407905075513293183490303)
                    ·
                      rfl

theorem cell22_4112828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 2, 1, 3, 3].length) (baseStart_4112828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4112828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4112828 prefixEnd_4112828 := by exact prefixLift 4112828
  have htrace : WordTrace (prefixWord ++ tailWord_4112828) baseStart_4112828 baseEnd_4112828 := by
    simpa [prefixWord, tailWord_4112828, baseEnd_4112828] using wordTrace_append hprefix tailTrace_4112828
  have hstable : (prefixWord ++ tailWord_4112828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4112828).length < 2 ^ (prefixWord ++ tailWord_4112828).sum := by decide
  have hdescent : baseEnd_4112828 < baseStart_4112828 := by decide
  rcases family_descends (prefixWord ++ tailWord_4112828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4112839 : List Nat := [1, 1, 4, 1, 1, 4, 2, 1, 2, 5]
def baseStart_4112839 : Nat := 118140960795 + 4112839 * 2 ^ 59
def prefixEnd_4112839 : Nat := 4983230072969 + 3 ^ 40 * 4112839 * 2
def baseEnd_4112839 : Nat := 1407908841038092821465269

theorem tailTrace_4112839 : CollatzResearch.WordTrace tailWord_4112839 prefixEnd_4112839 1407908841038092821465269 := by
  unfold tailWord_4112839
  simp only [CollatzResearch.WordTrace]
  refine ⟨150007561946894194824037571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100005041297929463216025047 150007561946894194824037571)
  ·
    refine ⟨225011342920341292236056357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150007561946894194824037571 225011342920341292236056357)
    ·
      refine ⟨42189626797563992294260567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 225011342920341292236056357 42189626797563992294260567)
      ·
        refine ⟨63284440196345988441390851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42189626797563992294260567 63284440196345988441390851)
        ·
          refine ⟨94926660294518982662086277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63284440196345988441390851 94926660294518982662086277)
          ·
            refine ⟨17798748805222309249141177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94926660294518982662086277 17798748805222309249141177)
            ·
              refine ⟨13349061603916731936855883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17798748805222309249141177 13349061603916731936855883)
              ·
                refine ⟨20023592405875097905283825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13349061603916731936855883 20023592405875097905283825)
                ·
                  refine ⟨15017694304406323428962869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20023592405875097905283825 15017694304406323428962869)
                  ·
                    refine ⟨1407908841038092821465269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15017694304406323428962869 1407908841038092821465269)
                    ·
                      rfl

theorem cell22_4112839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 1, 2, 5].length) (baseStart_4112839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4112839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4112839 prefixEnd_4112839 := by exact prefixLift 4112839
  have htrace : WordTrace (prefixWord ++ tailWord_4112839) baseStart_4112839 baseEnd_4112839 := by
    simpa [prefixWord, tailWord_4112839, baseEnd_4112839] using wordTrace_append hprefix tailTrace_4112839
  have hstable : (prefixWord ++ tailWord_4112839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4112839).length < 2 ^ (prefixWord ++ tailWord_4112839).sum := by decide
  have hdescent : baseEnd_4112839 < baseStart_4112839 := by decide
  rcases family_descends (prefixWord ++ tailWord_4112839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4112871 : List Nat := [1, 1, 5, 2, 1, 1, 1, 5, 1, 4]
def baseStart_4112871 : Nat := 118140960795 + 4112871 * 2 ^ 59
def prefixEnd_4112871 : Nat := 4983230072969 + 3 ^ 40 * 4112871 * 2
def baseEnd_4112871 : Nat := 1407919795292055404665171

theorem tailTrace_4112871 : CollatzResearch.WordTrace tailWord_4112871 prefixEnd_4112871 1407919795292055404665171 := by
  unfold tailWord_4112871
  simp only [CollatzResearch.WordTrace]
  refine ⟨150008729082778264289202467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100005819388518842859468311 150008729082778264289202467)
  ·
    refine ⟨225013093624167396433803701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150008729082778264289202467 225013093624167396433803701)
    ·
      refine ⟨21094977527265693415669097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 225013093624167396433803701 21094977527265693415669097)
      ·
        refine ⟨15821233145449270061751823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21094977527265693415669097 15821233145449270061751823)
        ·
          refine ⟨23731849718173905092627735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15821233145449270061751823 23731849718173905092627735)
          ·
            refine ⟨35597774577260857638941603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23731849718173905092627735 35597774577260857638941603)
            ·
              refine ⟨53396661865891286458412405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35597774577260857638941603 53396661865891286458412405)
              ·
                refine ⟨5005937049927308105476163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53396661865891286458412405 5005937049927308105476163)
                ·
                  refine ⟨7508905574890962158214245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5005937049927308105476163 7508905574890962158214245)
                  ·
                    refine ⟨1407919795292055404665171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7508905574890962158214245 1407919795292055404665171)
                    ·
                      rfl

theorem cell22_4112871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 5, 1, 4].length) (baseStart_4112871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4112871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4112871 prefixEnd_4112871 := by exact prefixLift 4112871
  have htrace : WordTrace (prefixWord ++ tailWord_4112871) baseStart_4112871 baseEnd_4112871 := by
    simpa [prefixWord, tailWord_4112871, baseEnd_4112871] using wordTrace_append hprefix tailTrace_4112871
  have hstable : (prefixWord ++ tailWord_4112871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4112871).length < 2 ^ (prefixWord ++ tailWord_4112871).sum := by decide
  have hdescent : baseEnd_4112871 < baseStart_4112871 := by decide
  rcases family_descends (prefixWord ++ tailWord_4112871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4112899 : List Nat := [1, 1, 1, 3, 2, 1, 3, 2, 4, 4]
def baseStart_4112899 : Nat := 118140960795 + 4112899 * 2 ^ 59
def prefixEnd_4112899 : Nat := 4983230072969 + 3 ^ 40 * 4112899 * 2
def baseEnd_4112899 : Nat := 1407929380264272664965085

theorem tailTrace_4112899 : CollatzResearch.WordTrace tailWord_4112899 prefixEnd_4112899 1407929380264272664965085 := by
  unfold tailWord_4112899
  simp only [CollatzResearch.WordTrace]
  refine ⟨150009750326676825071221751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100006500217784550047481167 150009750326676825071221751)
  ·
    refine ⟨225014625490015237606832627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150009750326676825071221751 225014625490015237606832627)
    ·
      refine ⟨337521938235022856410248941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225014625490015237606832627 337521938235022856410248941)
      ·
        refine ⟨126570726838133571153843353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 337521938235022856410248941 126570726838133571153843353)
        ·
          refine ⟨94928045128600178365382515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126570726838133571153843353 94928045128600178365382515)
          ·
            refine ⟨142392067692900267548073773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94928045128600178365382515 142392067692900267548073773)
            ·
              refine ⟨53397025384837600330527665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142392067692900267548073773 53397025384837600330527665)
              ·
                refine ⟨40047769038628200247895749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53397025384837600330527665 40047769038628200247895749)
                ·
                  refine ⟨7508956694742787546480453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40047769038628200247895749 7508956694742787546480453)
                  ·
                    refine ⟨1407929380264272664965085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7508956694742787546480453 1407929380264272664965085)
                    ·
                      rfl

theorem cell22_4112899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 2, 4, 4].length) (baseStart_4112899 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4112899 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4112899 prefixEnd_4112899 := by exact prefixLift 4112899
  have htrace : WordTrace (prefixWord ++ tailWord_4112899) baseStart_4112899 baseEnd_4112899 := by
    simpa [prefixWord, tailWord_4112899, baseEnd_4112899] using wordTrace_append hprefix tailTrace_4112899
  have hstable : (prefixWord ++ tailWord_4112899).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4112899).length < 2 ^ (prefixWord ++ tailWord_4112899).sum := by decide
  have hdescent : baseEnd_4112899 < baseStart_4112899 := by decide
  rcases family_descends (prefixWord ++ tailWord_4112899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4112944 : List Nat := [2, 1, 1, 1, 2, 3, 3, 1, 2, 6]
def baseStart_4112944 : Nat := 118140960795 + 4112944 * 2 ^ 59
def prefixEnd_4112944 : Nat := 4983230072969 + 3 ^ 40 * 4112944 * 2
def baseEnd_4112944 : Nat := 1407944784683907547589947

theorem tailTrace_4112944 : CollatzResearch.WordTrace tailWord_4112944 prefixEnd_4112944 1407944784683907547589947 := by
  unfold tailWord_4112944
  simp only [CollatzResearch.WordTrace]
  refine ⟨75005695805756898878304943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100007594407675865171073257 75005695805756898878304943)
  ·
    refine ⟨112508543708635348317457415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75005695805756898878304943 112508543708635348317457415)
    ·
      refine ⟨168762815562953022476186123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112508543708635348317457415 168762815562953022476186123)
      ·
        refine ⟨253144223344429533714279185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168762815562953022476186123 253144223344429533714279185)
        ·
          refine ⟨189858167508322150285709389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 253144223344429533714279185 189858167508322150285709389)
          ·
            refine ⟨71196812815620806357141021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 189858167508322150285709389 71196812815620806357141021)
            ·
              refine ⟨26698804805857802383927883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71196812815620806357141021 26698804805857802383927883)
              ·
                refine ⟨40048207208786703575891825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26698804805857802383927883 40048207208786703575891825)
                ·
                  refine ⟨30036155406590027681918869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40048207208786703575891825 30036155406590027681918869)
                  ·
                    refine ⟨1407944784683907547589947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30036155406590027681918869 1407944784683907547589947)
                    ·
                      rfl

theorem cell22_4112944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 1, 2, 6].length) (baseStart_4112944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4112944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4112944 prefixEnd_4112944 := by exact prefixLift 4112944
  have htrace : WordTrace (prefixWord ++ tailWord_4112944) baseStart_4112944 baseEnd_4112944 := by
    simpa [prefixWord, tailWord_4112944, baseEnd_4112944] using wordTrace_append hprefix tailTrace_4112944
  have hstable : (prefixWord ++ tailWord_4112944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4112944).length < 2 ^ (prefixWord ++ tailWord_4112944).sum := by decide
  have hdescent : baseEnd_4112944 < baseStart_4112944 := by decide
  rcases family_descends (prefixWord ++ tailWord_4112944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4112980 : List Nat := [2, 4, 1, 1, 1, 3, 1, 5, 1, 3]
def baseStart_4112980 : Nat := 118140960795 + 4112980 * 2 ^ 59
def prefixEnd_4112980 : Nat := 4983230072969 + 3 ^ 40 * 4112980 * 2
def baseEnd_4112980 : Nat := 1407957108219615453689837

theorem tailTrace_4112980 : CollatzResearch.WordTrace tailWord_4112980 prefixEnd_4112980 1407957108219615453689837 := by
  unfold tailWord_4112980
  simp only [CollatzResearch.WordTrace]
  refine ⟨75006352319691687952460197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100008469759588917269946929 75006352319691687952460197)
  ·
    refine ⟨14063691059942191491086287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75006352319691687952460197 14063691059942191491086287)
    ·
      refine ⟨21095536589913287236629431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14063691059942191491086287 21095536589913287236629431)
      ·
        refine ⟨31643304884869930854944147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21095536589913287236629431 31643304884869930854944147)
        ·
          refine ⟨47464957327304896282416221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31643304884869930854944147 47464957327304896282416221)
          ·
            refine ⟨17799358997739336105906083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47464957327304896282416221 17799358997739336105906083)
            ·
              refine ⟨26699038496609004158859125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17799358997739336105906083 26699038496609004158859125)
              ·
                refine ⟨2503034859057094139893043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26699038496609004158859125 2503034859057094139893043)
                ·
                  refine ⟨3754552288585641209839565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2503034859057094139893043 3754552288585641209839565)
                  ·
                    refine ⟨1407957108219615453689837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3754552288585641209839565 1407957108219615453689837)
                    ·
                      rfl

theorem cell22_4112980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 5, 1, 3].length) (baseStart_4112980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4112980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4112980 prefixEnd_4112980 := by exact prefixLift 4112980
  have htrace : WordTrace (prefixWord ++ tailWord_4112980) baseStart_4112980 baseEnd_4112980 := by
    simpa [prefixWord, tailWord_4112980, baseEnd_4112980] using wordTrace_append hprefix tailTrace_4112980
  have hstable : (prefixWord ++ tailWord_4112980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4112980).length < 2 ^ (prefixWord ++ tailWord_4112980).sum := by decide
  have hdescent : baseEnd_4112980 < baseStart_4112980 := by decide
  rcases family_descends (prefixWord ++ tailWord_4112980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4112993 : List Nat := [1, 2, 3, 1, 1, 6, 1, 2, 5]
def baseStart_4112993 : Nat := 118140960795 + 4112993 * 2 ^ 59
def prefixEnd_4112993 : Nat := 4983230072969 + 3 ^ 40 * 4112993 * 2
def baseEnd_4112993 : Nat := 469320519461762584371599

theorem tailTrace_4112993 : CollatzResearch.WordTrace tailWord_4112993 prefixEnd_4112993 469320519461762584371599 := by
  unfold tailWord_4112993
  simp only [CollatzResearch.WordTrace]
  refine ⟨150013178788336279125143633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100008785858890852750095755 150013178788336279125143633)
  ·
    refine ⟨112509884091252209343857725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150013178788336279125143633 112509884091252209343857725)
    ·
      refine ⟨42191206534219578503946647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112509884091252209343857725 42191206534219578503946647)
      ·
        refine ⟨63286809801329367755919971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42191206534219578503946647 63286809801329367755919971)
        ·
          refine ⟨94930214701994051633879957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63286809801329367755919971 94930214701994051633879957)
          ·
            refine ⟨4449853814155971170338123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 94930214701994051633879957 4449853814155971170338123)
            ·
              refine ⟨6674780721233956755507185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4449853814155971170338123 6674780721233956755507185)
              ·
                refine ⟨5006085540925467566630389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6674780721233956755507185 5006085540925467566630389)
                ·
                  refine ⟨469320519461762584371599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5006085540925467566630389 469320519461762584371599)
                  ·
                    rfl

theorem cell22_4112993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 1, 2, 5].length) (baseStart_4112993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4112993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4112993 prefixEnd_4112993 := by exact prefixLift 4112993
  have htrace : WordTrace (prefixWord ++ tailWord_4112993) baseStart_4112993 baseEnd_4112993 := by
    simpa [prefixWord, tailWord_4112993, baseEnd_4112993] using wordTrace_append hprefix tailTrace_4112993
  have hstable : (prefixWord ++ tailWord_4112993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4112993).length < 2 ^ (prefixWord ++ tailWord_4112993).sum := by decide
  have hdescent : baseEnd_4112993 < baseStart_4112993 := by decide
  rcases family_descends (prefixWord ++ tailWord_4112993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4113010 : List Nat := [3, 2, 1, 2, 4, 1, 3, 1, 5]
def baseStart_4113010 : Nat := 118140960795 + 4113010 * 2 ^ 59
def prefixEnd_4113010 : Nat := 4983230072969 + 3 ^ 40 * 4113010 * 2
def baseEnd_4113010 : Nat := 469322459277568458479915

theorem tailTrace_4113010 : CollatzResearch.WordTrace tailWord_4113010 prefixEnd_4113010 469322459277568458479915 := by
  unfold tailWord_4113010
  simp only [CollatzResearch.WordTrace]
  refine ⟨37503449707318672757128121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100009199219516460685674989 37503449707318672757128121)
  ·
    refine ⟨28127587280489004567846091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37503449707318672757128121 28127587280489004567846091)
    ·
      refine ⟨42191380920733506851769137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28127587280489004567846091 42191380920733506851769137)
      ·
        refine ⟨31643535690550130138826853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42191380920733506851769137 31643535690550130138826853)
        ·
          refine ⟨5933162941978149401030035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31643535690550130138826853 5933162941978149401030035)
          ·
            refine ⟨8899744412967224101545053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5933162941978149401030035 8899744412967224101545053)
            ·
              refine ⟨3337404154862709038079395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8899744412967224101545053 3337404154862709038079395)
              ·
                refine ⟨5006106232294063557119093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3337404154862709038079395 5006106232294063557119093)
                ·
                  refine ⟨469322459277568458479915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5006106232294063557119093 469322459277568458479915)
                  ·
                    rfl

theorem cell22_4113010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 3, 1, 5].length) (baseStart_4113010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4113010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4113010 prefixEnd_4113010 := by exact prefixLift 4113010
  have htrace : WordTrace (prefixWord ++ tailWord_4113010) baseStart_4113010 baseEnd_4113010 := by
    simpa [prefixWord, tailWord_4113010, baseEnd_4113010] using wordTrace_append hprefix tailTrace_4113010
  have hstable : (prefixWord ++ tailWord_4113010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4113010).length < 2 ^ (prefixWord ++ tailWord_4113010).sum := by decide
  have hdescent : baseEnd_4113010 < baseStart_4113010 := by decide
  rcases family_descends (prefixWord ++ tailWord_4113010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4113053 : List Nat := [1, 4, 2, 1, 1, 1, 4, 1, 4, 3]
def baseStart_4113053 : Nat := 118140960795 + 4113053 * 2 ^ 59
def prefixEnd_4113053 : Nat := 4983230072969 + 3 ^ 40 * 4113053 * 2
def baseEnd_4113053 : Nat := 1407982097611467596614613

theorem tailTrace_4113053 : CollatzResearch.WordTrace tailWord_4113053 prefixEnd_4113053 1407982097611467596614613 := by
  unfold tailWord_4113053
  simp only [CollatzResearch.WordTrace]
  refine ⟨150015367168118909372327813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100010244778745939581551875 150015367168118909372327813)
  ·
    refine ⟨28127881344022295507311465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 150015367168118909372327813 28127881344022295507311465)
    ·
      refine ⟨21095911008016721630483599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28127881344022295507311465 21095911008016721630483599)
      ·
        refine ⟨31643866512025082445725399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21095911008016721630483599 31643866512025082445725399)
        ·
          refine ⟨47465799768037623668588099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31643866512025082445725399 47465799768037623668588099)
          ·
            refine ⟨71198699652056435502882149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47465799768037623668588099 71198699652056435502882149)
            ·
              refine ⟨13349756184760581656790403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71198699652056435502882149 13349756184760581656790403)
              ·
                refine ⟨20024634277140872485185605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13349756184760581656790403 20024634277140872485185605)
                ·
                  refine ⟨3754618926963913590972301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20024634277140872485185605 3754618926963913590972301)
                  ·
                    refine ⟨1407982097611467596614613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3754618926963913590972301 1407982097611467596614613)
                    ·
                      rfl

theorem cell22_4113053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 1, 4, 3].length) (baseStart_4113053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4113053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4113053 prefixEnd_4113053 := by exact prefixLift 4113053
  have htrace : WordTrace (prefixWord ++ tailWord_4113053) baseStart_4113053 baseEnd_4113053 := by
    simpa [prefixWord, tailWord_4113053, baseEnd_4113053] using wordTrace_append hprefix tailTrace_4113053
  have hstable : (prefixWord ++ tailWord_4113053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4113053).length < 2 ^ (prefixWord ++ tailWord_4113053).sum := by decide
  have hdescent : baseEnd_4113053 < baseStart_4113053 := by decide
  rcases family_descends (prefixWord ++ tailWord_4113053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4113173 : List Nat := [1, 3, 2, 1, 2, 2, 4, 1, 6]
def baseStart_4113173 : Nat := 118140960795 + 4113173 * 2 ^ 59
def prefixEnd_4113173 : Nat := 4983230072969 + 3 ^ 40 * 4113173 * 2
def baseEnd_4113173 : Nat := 469341058687942427871415

theorem tailTrace_4113173 : CollatzResearch.WordTrace tailWord_4113173 prefixEnd_4113173 469341058687942427871415 := by
  unfold tailWord_4113173
  simp only [CollatzResearch.WordTrace]
  refine ⟨150019743927684169866696173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100013162618456113244464115 150019743927684169866696173)
  ·
    refine ⟨56257403972881563700011065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150019743927684169866696173 56257403972881563700011065)
    ·
      refine ⟨42193052979661172775008299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56257403972881563700011065 42193052979661172775008299)
      ·
        refine ⟨63289579469491759162512449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42193052979661172775008299 63289579469491759162512449)
        ·
          refine ⟨47467184602118819371884337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63289579469491759162512449 47467184602118819371884337)
          ·
            refine ⟨35600388451589114528913253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47467184602118819371884337 35600388451589114528913253)
            ·
              refine ⟨6675072834672958974171235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35600388451589114528913253 6675072834672958974171235)
              ·
                refine ⟨10012609252009438461256853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6675072834672958974171235 10012609252009438461256853)
                ·
                  refine ⟨469341058687942427871415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10012609252009438461256853 469341058687942427871415)
                  ·
                    rfl

theorem cell22_4113173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 4, 1, 6].length) (baseStart_4113173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4113173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4113173 prefixEnd_4113173 := by exact prefixLift 4113173
  have htrace : WordTrace (prefixWord ++ tailWord_4113173) baseStart_4113173 baseEnd_4113173 := by
    simpa [prefixWord, tailWord_4113173, baseEnd_4113173] using wordTrace_append hprefix tailTrace_4113173
  have hstable : (prefixWord ++ tailWord_4113173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4113173).length < 2 ^ (prefixWord ++ tailWord_4113173).sum := by decide
  have hdescent : baseEnd_4113173 < baseStart_4113173 := by decide
  rcases family_descends (prefixWord ++ tailWord_4113173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4113203 : List Nat := [1, 1, 1, 2, 6, 1, 2, 1, 1, 6]
def baseStart_4113203 : Nat := 118140960795 + 4113203 * 2 ^ 59
def prefixEnd_4113203 : Nat := 4983230072969 + 3 ^ 40 * 4113203 * 2
def baseEnd_4113203 : Nat := 1408033445676917205364153

theorem tailTrace_4113203 : CollatzResearch.WordTrace tailWord_4113203 prefixEnd_4113203 1408033445676917205364153 := by
  unfold tailWord_4113203
  simp only [CollatzResearch.WordTrace]
  refine ⟨150020838117575484990288263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100013892078383656660192175 150020838117575484990288263)
  ·
    refine ⟨225031257176363227485432395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150020838117575484990288263 225031257176363227485432395)
    ·
      refine ⟨337546885764544841228148593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225031257176363227485432395 337546885764544841228148593)
      ·
        refine ⟨253160164323408630921111445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 337546885764544841228148593 253160164323408630921111445)
        ·
          refine ⟨11866882702659779574427099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 253160164323408630921111445 11866882702659779574427099)
          ·
            refine ⟨17800324053989669361640649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11866882702659779574427099 17800324053989669361640649)
            ·
              refine ⟨13350243040492252021230487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17800324053989669361640649 13350243040492252021230487)
              ·
                refine ⟨20025364560738378031845731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13350243040492252021230487 20025364560738378031845731)
                ·
                  refine ⟨30038046841107567047768597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20025364560738378031845731 30038046841107567047768597)
                  ·
                    refine ⟨1408033445676917205364153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30038046841107567047768597 1408033445676917205364153)
                    ·
                      rfl

theorem cell22_4113203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 1, 1, 6].length) (baseStart_4113203 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4113203 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4113203 prefixEnd_4113203 := by exact prefixLift 4113203
  have htrace : WordTrace (prefixWord ++ tailWord_4113203) baseStart_4113203 baseEnd_4113203 := by
    simpa [prefixWord, tailWord_4113203, baseEnd_4113203] using wordTrace_append hprefix tailTrace_4113203
  have hstable : (prefixWord ++ tailWord_4113203).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4113203).length < 2 ^ (prefixWord ++ tailWord_4113203).sum := by decide
  have hdescent : baseEnd_4113203 < baseStart_4113203 := by decide
  rcases family_descends (prefixWord ++ tailWord_4113203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4113205 : List Nat := [1, 3, 3, 1, 3, 1, 1, 2, 4, 3]
def baseStart_4113205 : Nat := 118140960795 + 4113205 * 2 ^ 59
def prefixEnd_4113205 : Nat := 4983230072969 + 3 ^ 40 * 4113205 * 2
def baseEnd_4113205 : Nat := 1408034130317789866814147

theorem tailTrace_4113205 : CollatzResearch.WordTrace tailWord_4113205 prefixEnd_4113205 1408034130317789866814147 := by
  unfold tailWord_4113205
  simp only [CollatzResearch.WordTrace]
  refine ⟨150020911063568239331861069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100013940709045492887907379 150020911063568239331861069)
  ·
    refine ⟨56257841648838089749447901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150020911063568239331861069 56257841648838089749447901)
    ·
      refine ⟨21096690618314283656042963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56257841648838089749447901 21096690618314283656042963)
      ·
        refine ⟨31645035927471425484064445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21096690618314283656042963 31645035927471425484064445)
        ·
          refine ⟨11866888472801784556524167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31645035927471425484064445 11866888472801784556524167)
          ·
            refine ⟨17800332709202676834786251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11866888472801784556524167 17800332709202676834786251)
            ·
              refine ⟨26700499063804015252179377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17800332709202676834786251 26700499063804015252179377)
              ·
                refine ⟨20025374297853011439134533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26700499063804015252179377 20025374297853011439134533)
                ·
                  refine ⟨3754757680847439644837725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20025374297853011439134533 3754757680847439644837725)
                  ·
                    refine ⟨1408034130317789866814147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3754757680847439644837725 1408034130317789866814147)
                    ·
                      rfl

theorem cell22_4113205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 2, 4, 3].length) (baseStart_4113205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4113205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4113205 prefixEnd_4113205 := by exact prefixLift 4113205
  have htrace : WordTrace (prefixWord ++ tailWord_4113205) baseStart_4113205 baseEnd_4113205 := by
    simpa [prefixWord, tailWord_4113205, baseEnd_4113205] using wordTrace_append hprefix tailTrace_4113205
  have hstable : (prefixWord ++ tailWord_4113205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4113205).length < 2 ^ (prefixWord ++ tailWord_4113205).sum := by decide
  have hdescent : baseEnd_4113205 < baseStart_4113205 := by decide
  rcases family_descends (prefixWord ++ tailWord_4113205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4113239 : List Nat := [1, 1, 3, 2, 4, 3, 2, 1, 2, 3]
def baseStart_4113239 : Nat := 118140960795 + 4113239 * 2 ^ 59
def prefixEnd_4113239 : Nat := 4983230072969 + 3 ^ 40 * 4113239 * 2
def baseEnd_4113239 : Nat := 1408045769212625111464043

theorem tailTrace_4113239 : CollatzResearch.WordTrace tailWord_4113239 prefixEnd_4113239 1408045769212625111464043 := by
  unfold tailWord_4113239
  simp only [CollatzResearch.WordTrace]
  refine ⟨150022151145445063138598771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100014767430296708759065847 150022151145445063138598771)
  ·
    refine ⟨225033226718167594707898157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150022151145445063138598771 225033226718167594707898157)
    ·
      refine ⟨84387460019312848015461809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 225033226718167594707898157 84387460019312848015461809)
      ·
        refine ⟨63290595014484636011596357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84387460019312848015461809 63290595014484636011596357)
        ·
          refine ⟨11866986565215869252174317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63290595014484636011596357 11866986565215869252174317)
          ·
            refine ⟨4450119961955950969565369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11866986565215869252174317 4450119961955950969565369)
            ·
              refine ⟨3337589971466963227174027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4450119961955950969565369 3337589971466963227174027)
              ·
                refine ⟨5006384957200444840761041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3337589971466963227174027 5006384957200444840761041)
                ·
                  refine ⟨3754788717900333630570781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5006384957200444840761041 3754788717900333630570781)
                  ·
                    refine ⟨1408045769212625111464043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3754788717900333630570781 1408045769212625111464043)
                    ·
                      rfl

theorem cell22_4113239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 2, 1, 2, 3].length) (baseStart_4113239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4113239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4113239 prefixEnd_4113239 := by exact prefixLift 4113239
  have htrace : WordTrace (prefixWord ++ tailWord_4113239) baseStart_4113239 baseEnd_4113239 := by
    simpa [prefixWord, tailWord_4113239, baseEnd_4113239] using wordTrace_append hprefix tailTrace_4113239
  have hstable : (prefixWord ++ tailWord_4113239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4113239).length < 2 ^ (prefixWord ++ tailWord_4113239).sum := by decide
  have hdescent : baseEnd_4113239 < baseStart_4113239 := by decide
  rcases family_descends (prefixWord ++ tailWord_4113239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4113342 : List Nat := [4, 2, 1, 1, 1, 2, 1, 6, 4]
def baseStart_4113342 : Nat := 118140960795 + 4113342 * 2 ^ 59
def prefixEnd_4113342 : Nat := 4983230072969 + 3 ^ 40 * 4113342 * 2
def baseEnd_4113342 : Nat := 469360342739189058712909

theorem tailTrace_4113342 : CollatzResearch.WordTrace tailWord_4113342 prefixEnd_4113342 469360342739189058712909 := by
  unfold tailWord_4113342
  simp only [CollatzResearch.WordTrace]
  refine ⟨18753238483008988966199785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100017271909381274486398853 18753238483008988966199785)
  ·
    refine ⟨14064928862256741724649839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18753238483008988966199785 14064928862256741724649839)
    ·
      refine ⟨21097393293385112586974759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14064928862256741724649839 21097393293385112586974759)
      ·
        refine ⟨31646089940077668880462139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21097393293385112586974759 31646089940077668880462139)
        ·
          refine ⟨47469134910116503320693209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31646089940077668880462139 47469134910116503320693209)
          ·
            refine ⟨35601851182587377490519907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47469134910116503320693209 35601851182587377490519907)
            ·
              refine ⟨53402776773881066235779861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35601851182587377490519907 53402776773881066235779861)
              ·
                refine ⟨2503255161275674979802181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 53402776773881066235779861 2503255161275674979802181)
                ·
                  refine ⟨469360342739189058712909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2503255161275674979802181 469360342739189058712909)
                  ·
                    rfl

theorem cell22_4113342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 6, 4].length) (baseStart_4113342 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4113342 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4113342 prefixEnd_4113342 := by exact prefixLift 4113342
  have htrace : WordTrace (prefixWord ++ tailWord_4113342) baseStart_4113342 baseEnd_4113342 := by
    simpa [prefixWord, tailWord_4113342, baseEnd_4113342] using wordTrace_append hprefix tailTrace_4113342
  have hstable : (prefixWord ++ tailWord_4113342).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4113342).length < 2 ^ (prefixWord ++ tailWord_4113342).sum := by decide
  have hdescent : baseEnd_4113342 < baseStart_4113342 := by decide
  rcases family_descends (prefixWord ++ tailWord_4113342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4113370 : List Nat := [3, 1, 1, 2, 4, 2, 1, 8]
def baseStart_4113370 : Nat := 118140960795 + 4113370 * 2 ^ 59
def prefixEnd_4113370 : Nat := 4983230072969 + 3 ^ 40 * 4113370 * 2
def baseEnd_4113370 : Nat := 156454512576642715159849

theorem tailTrace_4113370 : CollatzResearch.WordTrace tailWord_4113370 prefixEnd_4113370 156454512576642715159849 := by
  unfold tailWord_4113370
  simp only [CollatzResearch.WordTrace]
  refine ⟨37506732276992618127904391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100017952738646981674411709 37506732276992618127904391)
  ·
    refine ⟨56260098415488927191856587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37506732276992618127904391 56260098415488927191856587)
    ·
      refine ⟨84390147623233390787784881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56260098415488927191856587 84390147623233390787784881)
      ·
        refine ⟨63292610717425043090838661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84390147623233390787784881 63292610717425043090838661)
        ·
          refine ⟨11867364509517195579532249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63292610717425043090838661 11867364509517195579532249)
          ·
            refine ⟨8900523382137896684649187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11867364509517195579532249 8900523382137896684649187)
            ·
              refine ⟨13350785073206845026973781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8900523382137896684649187 13350785073206845026973781)
              ·
                refine ⟨156454512576642715159849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13350785073206845026973781 156454512576642715159849)
                ·
                  rfl

theorem cell22_4113370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 8].length) (baseStart_4113370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4113370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4113370 prefixEnd_4113370 := by exact prefixLift 4113370
  have htrace : WordTrace (prefixWord ++ tailWord_4113370) baseStart_4113370 baseEnd_4113370 := by
    simpa [prefixWord, tailWord_4113370, baseEnd_4113370] using wordTrace_append hprefix tailTrace_4113370
  have hstable : (prefixWord ++ tailWord_4113370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4113370).length < 2 ^ (prefixWord ++ tailWord_4113370).sum := by decide
  have hdescent : baseEnd_4113370 < baseStart_4113370 := by decide
  rcases family_descends (prefixWord ++ tailWord_4113370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4113492 : List Nat := [2, 4, 1, 1, 1, 1, 4, 2, 1, 5]
def baseStart_4113492 : Nat := 118140960795 + 4113492 * 2 ^ 59
def prefixEnd_4113492 : Nat := 4983230072969 + 3 ^ 40 * 4113492 * 2
def baseEnd_4113492 : Nat := 1408132376283016784888267

theorem tailTrace_4113492 : CollatzResearch.WordTrace tailWord_4113492 prefixEnd_4113492 1408132376283016784888267 := by
  unfold tailWord_4113492
  simp only [CollatzResearch.WordTrace]
  refine ⟨75015689406764243673779365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100020919209018991565039153 75015689406764243673779365)
  ·
    refine ⟨14065441763768295688833631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75015689406764243673779365 14065441763768295688833631)
    ·
      refine ⟨21098162645652443533250447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14065441763768295688833631 21098162645652443533250447)
      ·
        refine ⟨31647243968478665299875671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21098162645652443533250447 31647243968478665299875671)
        ·
          refine ⟨47470865952717997949813507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31647243968478665299875671 47470865952717997949813507)
          ·
            refine ⟨71206298929076996924720261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47470865952717997949813507 71206298929076996924720261)
            ·
              refine ⟨13351181049201936923385049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71206298929076996924720261 13351181049201936923385049)
              ·
                refine ⟨10013385786901452692538787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13351181049201936923385049 10013385786901452692538787)
                ·
                  refine ⟨15020078680352179038808181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10013385786901452692538787 15020078680352179038808181)
                  ·
                    refine ⟨1408132376283016784888267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15020078680352179038808181 1408132376283016784888267)
                    ·
                      rfl

theorem cell22_4113492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 2, 1, 5].length) (baseStart_4113492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4113492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4113492 prefixEnd_4113492 := by exact prefixLift 4113492
  have htrace : WordTrace (prefixWord ++ tailWord_4113492) baseStart_4113492 baseEnd_4113492 := by
    simpa [prefixWord, tailWord_4113492, baseEnd_4113492] using wordTrace_append hprefix tailTrace_4113492
  have hstable : (prefixWord ++ tailWord_4113492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4113492).length < 2 ^ (prefixWord ++ tailWord_4113492).sum := by decide
  have hdescent : baseEnd_4113492 < baseStart_4113492 := by decide
  rcases family_descends (prefixWord ++ tailWord_4113492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4113644 : List Nat := [2, 2, 1, 1, 2, 5, 2, 1, 1, 5]
def baseStart_4113644 : Nat := 118140960795 + 4113644 * 2 ^ 59
def prefixEnd_4113644 : Nat := 4983230072969 + 3 ^ 40 * 4113644 * 2
def baseEnd_4113644 : Nat := 1408184408989339055087801

theorem tailTrace_4113644 : CollatzResearch.WordTrace tailWord_4113644 prefixEnd_4113644 1408184408989339055087801 := by
  unfold tailWord_4113644
  simp only [CollatzResearch.WordTrace]
  refine ⟨75018461354488908653545993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100024615139318544871394657 75018461354488908653545993)
  ·
    refine ⟨56263846015866681490159495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75018461354488908653545993 56263846015866681490159495)
    ·
      refine ⟨84395769023800022235239243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56263846015866681490159495 84395769023800022235239243)
      ·
        refine ⟨126593653535700033352858865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84395769023800022235239243 126593653535700033352858865)
        ·
          refine ⟨94945240151775025014644149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126593653535700033352858865 94945240151775025014644149)
          ·
            refine ⟨8901116264228908595122889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 94945240151775025014644149 8901116264228908595122889)
            ·
              refine ⟨6675837198171681446342167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8901116264228908595122889 6675837198171681446342167)
              ·
                refine ⟨10013755797257522169513251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6675837198171681446342167 10013755797257522169513251)
                ·
                  refine ⟨15020633695886283254269877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10013755797257522169513251 15020633695886283254269877)
                  ·
                    refine ⟨1408184408989339055087801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15020633695886283254269877 1408184408989339055087801)
                    ·
                      rfl

theorem cell22_4113644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 5].length) (baseStart_4113644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4113644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4113644 prefixEnd_4113644 := by exact prefixLift 4113644
  have htrace : WordTrace (prefixWord ++ tailWord_4113644) baseStart_4113644 baseEnd_4113644 := by
    simpa [prefixWord, tailWord_4113644, baseEnd_4113644] using wordTrace_append hprefix tailTrace_4113644
  have hstable : (prefixWord ++ tailWord_4113644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4113644).length < 2 ^ (prefixWord ++ tailWord_4113644).sum := by decide
  have hdescent : baseEnd_4113644 < baseStart_4113644 := by decide
  rcases family_descends (prefixWord ++ tailWord_4113644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4113678 : List Nat := [4, 1, 1, 2, 1, 5, 1, 2, 2, 3]
def baseStart_4113678 : Nat := 118140960795 + 4113678 * 2 ^ 59
def prefixEnd_4113678 : Nat := 4983230072969 + 3 ^ 40 * 4113678 * 2
def baseEnd_4113678 : Nat := 1408196047884174299737697

theorem tailTrace_4113678 : CollatzResearch.WordTrace tailWord_4113678 prefixEnd_4113678 1408196047884174299737697 := by
  unfold tailWord_4113678
  simp only [CollatzResearch.WordTrace]
  refine ⟨18754770348856830139228711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100025441860569760742553125 18754770348856830139228711)
  ·
    refine ⟨28132155523285245208843067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18754770348856830139228711 28132155523285245208843067)
    ·
      refine ⟨42198233284927867813264601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28132155523285245208843067 42198233284927867813264601)
      ·
        refine ⟨31648674963695900859948451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42198233284927867813264601 31648674963695900859948451)
        ·
          refine ⟨47473012445543851289922677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31648674963695900859948451 47473012445543851289922677)
          ·
            refine ⟨4450594916769736058430251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47473012445543851289922677 4450594916769736058430251)
            ·
              refine ⟨6675892375154604087645377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4450594916769736058430251 6675892375154604087645377)
              ·
                refine ⟨5006919281365953065734033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6675892375154604087645377 5006919281365953065734033)
                ·
                  refine ⟨3755189461024464799300525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5006919281365953065734033 3755189461024464799300525)
                  ·
                    refine ⟨1408196047884174299737697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3755189461024464799300525 1408196047884174299737697)
                    ·
                      rfl

theorem cell22_4113678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 1, 2, 2, 3].length) (baseStart_4113678 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4113678 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4113678 prefixEnd_4113678 := by exact prefixLift 4113678
  have htrace : WordTrace (prefixWord ++ tailWord_4113678) baseStart_4113678 baseEnd_4113678 := by
    simpa [prefixWord, tailWord_4113678, baseEnd_4113678] using wordTrace_append hprefix tailTrace_4113678
  have hstable : (prefixWord ++ tailWord_4113678).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4113678).length < 2 ^ (prefixWord ++ tailWord_4113678).sum := by decide
  have hdescent : baseEnd_4113678 < baseStart_4113678 := by decide
  rcases family_descends (prefixWord ++ tailWord_4113678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4113740 : List Nat := [2, 2, 1, 3, 2, 3, 3, 2, 1, 3]
def baseStart_4113740 : Nat := 118140960795 + 4113740 * 2 ^ 59
def prefixEnd_4113740 : Nat := 4983230072969 + 3 ^ 40 * 4113740 * 2
def baseEnd_4113740 : Nat := 1408217271751226804687507

theorem tailTrace_4113740 : CollatzResearch.WordTrace tailWord_4113740 prefixEnd_4113740 1408217271751226804687507 := by
  unfold tailWord_4113740
  simp only [CollatzResearch.WordTrace]
  refine ⟨75020212058315012851293337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100026949411086683801724449 75020212058315012851293337)
  ·
    refine ⟨56265159043736259638470003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75020212058315012851293337 56265159043736259638470003)
    ·
      refine ⟨84397738565604389457705005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56265159043736259638470003 84397738565604389457705005)
      ·
        refine ⟨31649151962101646046639377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84397738565604389457705005 31649151962101646046639377)
        ·
          refine ⟨23736863971576234534979533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31649151962101646046639377 23736863971576234534979533)
          ·
            refine ⟨8901323989341087950617325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23736863971576234534979533 8901323989341087950617325)
            ·
              refine ⟨3337996496002907981481497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8901323989341087950617325 3337996496002907981481497)
              ·
                refine ⟨2503497372002180986111123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3337996496002907981481497 2503497372002180986111123)
                ·
                  refine ⟨3755246058003271479166685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2503497372002180986111123 3755246058003271479166685)
                  ·
                    refine ⟨1408217271751226804687507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3755246058003271479166685 1408217271751226804687507)
                    ·
                      rfl

theorem cell22_4113740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 3, 2, 1, 3].length) (baseStart_4113740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4113740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4113740 prefixEnd_4113740 := by exact prefixLift 4113740
  have htrace : WordTrace (prefixWord ++ tailWord_4113740) baseStart_4113740 baseEnd_4113740 := by
    simpa [prefixWord, tailWord_4113740, baseEnd_4113740] using wordTrace_append hprefix tailTrace_4113740
  have hstable : (prefixWord ++ tailWord_4113740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4113740).length < 2 ^ (prefixWord ++ tailWord_4113740).sum := by decide
  have hdescent : baseEnd_4113740 < baseStart_4113740 := by decide
  rcases family_descends (prefixWord ++ tailWord_4113740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4113841 : List Nat := [1, 2, 2, 4, 1, 1, 1, 2, 5, 3]
def baseStart_4113841 : Nat := 118140960795 + 4113841 * 2 ^ 59
def prefixEnd_4113841 : Nat := 4983230072969 + 3 ^ 40 * 4113841 * 2
def baseEnd_4113841 : Nat := 1408251846115296207912197

theorem tailTrace_4113841 : CollatzResearch.WordTrace tailWord_4113841 prefixEnd_4113841 1408251846115296207912197 := by
  unfold tailWord_4113841
  simp only [CollatzResearch.WordTrace]
  refine ⟨150044107889264119952013377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100029405259509413301342251 150044107889264119952013377)
  ·
    refine ⟨112533080916948089964010033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150044107889264119952013377 112533080916948089964010033)
    ·
      refine ⟨84399810687711067473007525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112533080916948089964010033 84399810687711067473007525)
      ·
        refine ⟨15824964503945825151188911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84399810687711067473007525 15824964503945825151188911)
        ·
          refine ⟨23737446755918737726783367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15824964503945825151188911 23737446755918737726783367)
          ·
            refine ⟨35606170133878106590175051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23737446755918737726783367 35606170133878106590175051)
            ·
              refine ⟨53409255200817159885262577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35606170133878106590175051 53409255200817159885262577)
              ·
                refine ⟨40056941400612869913946933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53409255200817159885262577 40056941400612869913946933)
                ·
                  refine ⟨3755338256307456554432525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40056941400612869913946933 3755338256307456554432525)
                  ·
                    refine ⟨1408251846115296207912197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3755338256307456554432525 1408251846115296207912197)
                    ·
                      rfl

theorem cell22_4113841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 2, 5, 3].length) (baseStart_4113841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4113841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4113841 prefixEnd_4113841 := by exact prefixLift 4113841
  have htrace : WordTrace (prefixWord ++ tailWord_4113841) baseStart_4113841 baseEnd_4113841 := by
    simpa [prefixWord, tailWord_4113841, baseEnd_4113841] using wordTrace_append hprefix tailTrace_4113841
  have hstable : (prefixWord ++ tailWord_4113841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4113841).length < 2 ^ (prefixWord ++ tailWord_4113841).sum := by decide
  have hdescent : baseEnd_4113841 < baseStart_4113841 := by decide
  rcases family_descends (prefixWord ++ tailWord_4113841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4113909 : List Nat := [1, 3, 5, 1, 1, 2, 3, 2, 1, 3]
def baseStart_4113909 : Nat := 118140960795 + 4113909 * 2 ^ 59
def prefixEnd_4113909 : Nat := 4983230072969 + 3 ^ 40 * 4113909 * 2
def baseEnd_4113909 : Nat := 1408275123904966697211989

theorem tailTrace_4113909 : CollatzResearch.WordTrace tailWord_4113909 prefixEnd_4113909 1408275123904966697211989 := by
  unfold tailWord_4113909
  simp only [CollatzResearch.WordTrace]
  refine ⟨150046588053017767565488781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100031058702011845043659187 150046588053017767565488781)
  ·
    refine ⟨56267470519881662837058293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150046588053017767565488781 56267470519881662837058293)
    ·
      refine ⟨5275075361238905890974215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 56267470519881662837058293 5275075361238905890974215)
      ·
        refine ⟨7912613041858358836461323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5275075361238905890974215 7912613041858358836461323)
        ·
          refine ⟨11868919562787538254691985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7912613041858358836461323 11868919562787538254691985)
          ·
            refine ⟨8901689672090653691018989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11868919562787538254691985 8901689672090653691018989)
            ·
              refine ⟨3338133627033995134132121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8901689672090653691018989 3338133627033995134132121)
              ·
                refine ⟨2503600220275496350599091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3338133627033995134132121 2503600220275496350599091)
                ·
                  refine ⟨3755400330413244525898637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2503600220275496350599091 3755400330413244525898637)
                  ·
                    refine ⟨1408275123904966697211989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3755400330413244525898637 1408275123904966697211989)
                    ·
                      rfl

theorem cell22_4113909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_4113909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4113909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4113909 prefixEnd_4113909 := by exact prefixLift 4113909
  have htrace : WordTrace (prefixWord ++ tailWord_4113909) baseStart_4113909 baseEnd_4113909 := by
    simpa [prefixWord, tailWord_4113909, baseEnd_4113909] using wordTrace_append hprefix tailTrace_4113909
  have hstable : (prefixWord ++ tailWord_4113909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4113909).length < 2 ^ (prefixWord ++ tailWord_4113909).sum := by decide
  have hdescent : baseEnd_4113909 < baseStart_4113909 := by decide
  rcases family_descends (prefixWord ++ tailWord_4113909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4113916 : List Nat := [2, 2, 2, 1, 2, 1, 5, 1, 6]
def baseStart_4113916 : Nat := 118140960795 + 4113916 * 2 ^ 59
def prefixEnd_4113916 : Nat := 4983230072969 + 3 ^ 40 * 4113916 * 2
def baseEnd_4113916 : Nat := 469425840049340337428989

theorem tailTrace_4113916 : CollatzResearch.WordTrace tailWord_4113916 prefixEnd_4113916 469425840049340337428989 := by
  unfold tailWord_4113916
  simp only [CollatzResearch.WordTrace]
  refine ⟨75023421681996203880496801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100031228909328271840662401 75023421681996203880496801)
  ·
    refine ⟨56267566261497152910372601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75023421681996203880496801 56267566261497152910372601)
    ·
      refine ⟨42200674696122864682779451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56267566261497152910372601 42200674696122864682779451)
      ·
        refine ⟨63301012044184297024169177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42200674696122864682779451 63301012044184297024169177)
        ·
          refine ⟨47475759033138222768126883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63301012044184297024169177 47475759033138222768126883)
          ·
            refine ⟨71213638549707334152190325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47475759033138222768126883 71213638549707334152190325)
            ·
              refine ⟨6676278614035062576767843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71213638549707334152190325 6676278614035062576767843)
              ·
                refine ⟨10014417921052593865151765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6676278614035062576767843 10014417921052593865151765)
                ·
                  refine ⟨469425840049340337428989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10014417921052593865151765 469425840049340337428989)
                  ·
                    rfl

theorem cell22_4113916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 5, 1, 6].length) (baseStart_4113916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4113916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4113916 prefixEnd_4113916 := by exact prefixLift 4113916
  have htrace : WordTrace (prefixWord ++ tailWord_4113916) baseStart_4113916 baseEnd_4113916 := by
    simpa [prefixWord, tailWord_4113916, baseEnd_4113916] using wordTrace_append hprefix tailTrace_4113916
  have hstable : (prefixWord ++ tailWord_4113916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4113916).length < 2 ^ (prefixWord ++ tailWord_4113916).sum := by decide
  have hdescent : baseEnd_4113916 < baseStart_4113916 := by decide
  rcases family_descends (prefixWord ++ tailWord_4113916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4113922 : List Nat := [3, 4, 1, 2, 1, 3, 2, 1, 5]
def baseStart_4113922 : Nat := 118140960795 + 4113922 * 2 ^ 59
def prefixEnd_4113922 : Nat := 4983230072969 + 3 ^ 40 * 4113922 * 2
def baseEnd_4113922 : Nat := 469426524690212998878983

theorem tailTrace_4113922 : CollatzResearch.WordTrace tailWord_4113922 prefixEnd_4113922 469426524690212998878983 := by
  unfold tailWord_4113922
  simp only [CollatzResearch.WordTrace]
  refine ⟨37511765550492667696428005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100031374801313780523808013 37511765550492667696428005)
  ·
    refine ⟨7033456040717375193080251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37511765550492667696428005 7033456040717375193080251)
    ·
      refine ⟨10550184061076062789620377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7033456040717375193080251 10550184061076062789620377)
      ·
        refine ⟨7912638045807047092215283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10550184061076062789620377 7912638045807047092215283)
        ·
          refine ⟨11868957068710570638322925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7912638045807047092215283 11868957068710570638322925)
          ·
            refine ⟨4450858900766463989371097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11868957068710570638322925 4450858900766463989371097)
            ·
              refine ⟨3338144175574847992028323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4450858900766463989371097 3338144175574847992028323)
              ·
                refine ⟨5007216263362271988042485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3338144175574847992028323 5007216263362271988042485)
                ·
                  refine ⟨469426524690212998878983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5007216263362271988042485 469426524690212998878983)
                  ·
                    rfl

theorem cell22_4113922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 2, 1, 5].length) (baseStart_4113922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4113922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4113922 prefixEnd_4113922 := by exact prefixLift 4113922
  have htrace : WordTrace (prefixWord ++ tailWord_4113922) baseStart_4113922 baseEnd_4113922 := by
    simpa [prefixWord, tailWord_4113922, baseEnd_4113922] using wordTrace_append hprefix tailTrace_4113922
  have hstable : (prefixWord ++ tailWord_4113922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4113922).length < 2 ^ (prefixWord ++ tailWord_4113922).sum := by decide
  have hdescent : baseEnd_4113922 < baseStart_4113922 := by decide
  rcases family_descends (prefixWord ++ tailWord_4113922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4113997 : List Nat := [1, 6, 1, 1, 3, 2, 1, 1, 2, 4]
def baseStart_4113997 : Nat := 118140960795 + 4113997 * 2 ^ 59
def prefixEnd_4113997 : Nat := 4983230072969 + 3 ^ 40 * 4113997 * 2
def baseEnd_4113997 : Nat := 1408305248103363801011719

theorem tailTrace_4113997 : CollatzResearch.WordTrace tailWord_4113997 prefixEnd_4113997 1408305248103363801011719 := by
  unfold tailWord_4113997
  simp only [CollatzResearch.WordTrace]
  refine ⟨150049797676698958594692245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100033198451132639063128163 150049797676698958594692245)
  ·
    refine ⟨7033584266095263684126199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 150049797676698958594692245 7033584266095263684126199)
    ·
      refine ⟨10550376399142895526189299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7033584266095263684126199 10550376399142895526189299)
      ·
        refine ⟨15825564598714343289283949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10550376399142895526189299 15825564598714343289283949)
        ·
          refine ⟨5934586724517878733481481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15825564598714343289283949 5934586724517878733481481)
          ·
            refine ⟨4450940043388409050111111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5934586724517878733481481 4450940043388409050111111)
            ·
              refine ⟨6676410065082613575166667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4450940043388409050111111 6676410065082613575166667)
              ·
                refine ⟨10014615097623920362750001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6676410065082613575166667 10014615097623920362750001)
                ·
                  refine ⟨7510961323217940272062501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10014615097623920362750001 7510961323217940272062501)
                  ·
                    refine ⟨1408305248103363801011719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7510961323217940272062501 1408305248103363801011719)
                    ·
                      rfl

theorem cell22_4113997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 1, 1, 2, 4].length) (baseStart_4113997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4113997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4113997 prefixEnd_4113997 := by exact prefixLift 4113997
  have htrace : WordTrace (prefixWord ++ tailWord_4113997) baseStart_4113997 baseEnd_4113997 := by
    simpa [prefixWord, tailWord_4113997, baseEnd_4113997] using wordTrace_append hprefix tailTrace_4113997
  have hstable : (prefixWord ++ tailWord_4113997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4113997).length < 2 ^ (prefixWord ++ tailWord_4113997).sum := by decide
  have hdescent : baseEnd_4113997 < baseStart_4113997 := by decide
  rcases family_descends (prefixWord ++ tailWord_4113997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4114023 : List Nat := [1, 1, 5, 1, 1, 1, 5, 2, 5]
def baseStart_4114023 : Nat := 118140960795 + 4114023 * 2 ^ 59
def prefixEnd_4114023 : Nat := 4983230072969 + 3 ^ 40 * 4114023 * 2
def baseEnd_4114023 : Nat := 469438049478236133287213

theorem tailTrace_4114023 : CollatzResearch.WordTrace tailWord_4114023 prefixEnd_4114023 469438049478236133287213 := by
  unfold tailWord_4114023
  simp only [CollatzResearch.WordTrace]
  refine ⟨150050745974604765035138723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100033830649736510023425815 150050745974604765035138723)
  ·
    refine ⟨225076118961907147552708085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150050745974604765035138723 225076118961907147552708085)
    ·
      refine ⟨21100886152678795083066383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 225076118961907147552708085 21100886152678795083066383)
      ·
        refine ⟨31651329229018192624599575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21100886152678795083066383 31651329229018192624599575)
        ·
          refine ⟨47476993843527288936899363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31651329229018192624599575 47476993843527288936899363)
          ·
            refine ⟨71215490765290933405349045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47476993843527288936899363 71215490765290933405349045)
            ·
              refine ⟨6676452259246025006751473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71215490765290933405349045 6676452259246025006751473)
              ·
                refine ⟨5007339194434518755063605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6676452259246025006751473 5007339194434518755063605)
                ·
                  refine ⟨469438049478236133287213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5007339194434518755063605 469438049478236133287213)
                  ·
                    rfl

theorem cell22_4114023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 5, 2, 5].length) (baseStart_4114023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4114023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4114023 prefixEnd_4114023 := by exact prefixLift 4114023
  have htrace : WordTrace (prefixWord ++ tailWord_4114023) baseStart_4114023 baseEnd_4114023 := by
    simpa [prefixWord, tailWord_4114023, baseEnd_4114023] using wordTrace_append hprefix tailTrace_4114023
  have hstable : (prefixWord ++ tailWord_4114023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4114023).length < 2 ^ (prefixWord ++ tailWord_4114023).sum := by decide
  have hdescent : baseEnd_4114023 < baseStart_4114023 := by decide
  rcases family_descends (prefixWord ++ tailWord_4114023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4114083 : List Nat := [1, 1, 1, 4, 1, 1, 3, 3, 4, 3]
def baseStart_4114083 : Nat := 118140960795 + 4114083 * 2 ^ 59
def prefixEnd_4114083 : Nat := 4983230072969 + 3 ^ 40 * 4114083 * 2
def baseEnd_4114083 : Nat := 1408334687660888243361455

theorem tailTrace_4114083 : CollatzResearch.WordTrace tailWord_4114083 prefixEnd_4114083 1408334687660888243361455 := by
  unfold tailWord_4114083
  simp only [CollatzResearch.WordTrace]
  refine ⟨150052934354387395282322903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100035289569591596854881935 150052934354387395282322903)
  ·
    refine ⟨225079401531581092923484355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150052934354387395282322903 225079401531581092923484355)
    ·
      refine ⟨337619102297371639385226533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225079401531581092923484355 337619102297371639385226533)
      ·
        refine ⟨63303581680757182384729975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 337619102297371639385226533 63303581680757182384729975)
        ·
          refine ⟨94955372521135773577094963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63303581680757182384729975 94955372521135773577094963)
          ·
            refine ⟨142433058781703660365642445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94955372521135773577094963 142433058781703660365642445)
            ·
              refine ⟨53412397043138872637115917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142433058781703660365642445 53412397043138872637115917)
              ·
                refine ⟨20029648891177077238918469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53412397043138872637115917 20029648891177077238918469)
                ·
                  refine ⟨3755559167095701982297213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20029648891177077238918469 3755559167095701982297213)
                  ·
                    refine ⟨1408334687660888243361455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3755559167095701982297213 1408334687660888243361455)
                    ·
                      rfl

theorem cell22_4114083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 3, 4, 3].length) (baseStart_4114083 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4114083 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4114083 prefixEnd_4114083 := by exact prefixLift 4114083
  have htrace : WordTrace (prefixWord ++ tailWord_4114083) baseStart_4114083 baseEnd_4114083 := by
    simpa [prefixWord, tailWord_4114083, baseEnd_4114083] using wordTrace_append hprefix tailTrace_4114083
  have hstable : (prefixWord ++ tailWord_4114083).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4114083).length < 2 ^ (prefixWord ++ tailWord_4114083).sum := by decide
  have hdescent : baseEnd_4114083 < baseStart_4114083 := by decide
  rcases family_descends (prefixWord ++ tailWord_4114083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4114096 : List Nat := [2, 1, 1, 1, 2, 1, 5, 9]
def baseStart_4114096 : Nat := 118140960795 + 4114096 * 2 ^ 59
def prefixEnd_4114096 : Nat := 4983230072969 + 3 ^ 40 * 4114096 * 2
def baseEnd_4114096 : Nat := 156482126425173393642935

theorem tailTrace_4114096 : CollatzResearch.WordTrace tailWord_4114096 prefixEnd_4114096 156482126425173393642935 := by
  unfold tailWord_4114096
  simp only [CollatzResearch.WordTrace]
  refine ⟨75026704251670149251273071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100035605668893532335030761 75026704251670149251273071)
  ·
    refine ⟨112540056377505223876909607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75026704251670149251273071 112540056377505223876909607)
    ·
      refine ⟨168810084566257835815364411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112540056377505223876909607 168810084566257835815364411)
      ·
        refine ⟨253215126849386753723046617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168810084566257835815364411 253215126849386753723046617)
        ·
          refine ⟨189911345137040065292284963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 253215126849386753723046617 189911345137040065292284963)
          ·
            refine ⟨284867017705560097938427445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189911345137040065292284963 284867017705560097938427445)
            ·
              refine ⟨26706282909896259181727573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 284867017705560097938427445 26706282909896259181727573)
              ·
                refine ⟨156482126425173393642935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26706282909896259181727573 156482126425173393642935)
                ·
                  rfl

theorem cell22_4114096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 9].length) (baseStart_4114096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4114096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4114096 prefixEnd_4114096 := by exact prefixLift 4114096
  have htrace : WordTrace (prefixWord ++ tailWord_4114096) baseStart_4114096 baseEnd_4114096 := by
    simpa [prefixWord, tailWord_4114096, baseEnd_4114096] using wordTrace_append hprefix tailTrace_4114096
  have hstable : (prefixWord ++ tailWord_4114096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4114096).length < 2 ^ (prefixWord ++ tailWord_4114096).sum := by decide
  have hdescent : baseEnd_4114096 < baseStart_4114096 := by decide
  rcases family_descends (prefixWord ++ tailWord_4114096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4114128 : List Nat := [2, 1, 1, 1, 1, 2, 1, 3, 7, 3]
def baseStart_4114128 : Nat := 118140960795 + 4114128 * 2 ^ 59
def prefixEnd_4114128 : Nat := 4983230072969 + 3 ^ 40 * 4114128 * 2
def baseEnd_4114128 : Nat := 1408350092080523125986317

theorem tailTrace_4114128 : CollatzResearch.WordTrace tailWord_4114128 prefixEnd_4114128 1408350092080523125986317 := by
  unfold tailWord_4114128
  simp only [CollatzResearch.WordTrace]
  refine ⟨75027287819612183983855519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100036383759482911978474025 75027287819612183983855519)
  ·
    refine ⟨112540931729418275975783279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75027287819612183983855519 112540931729418275975783279)
    ·
      refine ⟨168811397594127413963674919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112540931729418275975783279 168811397594127413963674919)
      ·
        refine ⟨253217096391191120945512379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168811397594127413963674919 253217096391191120945512379)
        ·
          refine ⟨379825644586786681418268569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253217096391191120945512379 379825644586786681418268569)
          ·
            refine ⟨284869233440090011063701427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 379825644586786681418268569 284869233440090011063701427)
            ·
              refine ⟨427303850160135016595552141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 284869233440090011063701427 427303850160135016595552141)
              ·
                refine ⟨160238943810050631223332053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 427303850160135016595552141 160238943810050631223332053)
                ·
                  refine ⟨3755600245548061669296845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 160238943810050631223332053 3755600245548061669296845)
                  ·
                    refine ⟨1408350092080523125986317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3755600245548061669296845 1408350092080523125986317)
                    ·
                      rfl

theorem cell22_4114128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 7, 3].length) (baseStart_4114128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4114128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4114128 prefixEnd_4114128 := by exact prefixLift 4114128
  have htrace : WordTrace (prefixWord ++ tailWord_4114128) baseStart_4114128 baseEnd_4114128 := by
    simpa [prefixWord, tailWord_4114128, baseEnd_4114128] using wordTrace_append hprefix tailTrace_4114128
  have hstable : (prefixWord ++ tailWord_4114128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4114128).length < 2 ^ (prefixWord ++ tailWord_4114128).sum := by decide
  have hdescent : baseEnd_4114128 < baseStart_4114128 := by decide
  rcases family_descends (prefixWord ++ tailWord_4114128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4114147 : List Nat := [1, 1, 1, 7, 3, 1, 1, 7]
def baseStart_4114147 : Nat := 118140960795 + 4114147 * 2 ^ 59
def prefixEnd_4114147 : Nat := 4983230072969 + 3 ^ 40 * 4114147 * 2
def baseEnd_4114147 : Nat := 156484066240979267751251

theorem tailTrace_4114147 : CollatzResearch.WordTrace tailWord_4114147 prefixEnd_4114147 156484066240979267751251 := by
  unfold tailWord_4114147
  simp only [CollatzResearch.WordTrace]
  refine ⟨150055268626155534212652695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100036845750770356141768463 150055268626155534212652695)
  ·
    refine ⟨225082902939233301318979043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150055268626155534212652695 225082902939233301318979043)
    ·
      refine ⟨337624354408849951978468565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225082902939233301318979043 337624354408849951978468565)
      ·
        refine ⟨7913070806457420749495357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 337624354408849951978468565 7913070806457420749495357)
        ·
          refine ⟨2967401552421532781060759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7913070806457420749495357 2967401552421532781060759)
          ·
            refine ⟨4451102328632299171591139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2967401552421532781060759 4451102328632299171591139)
            ·
              refine ⟨6676653492948448757386709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4451102328632299171591139 6676653492948448757386709)
              ·
                refine ⟨156484066240979267751251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6676653492948448757386709 156484066240979267751251)
                ·
                  rfl

theorem cell22_4114147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 1, 7].length) (baseStart_4114147 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4114147 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4114147 prefixEnd_4114147 := by exact prefixLift 4114147
  have htrace : WordTrace (prefixWord ++ tailWord_4114147) baseStart_4114147 baseEnd_4114147 := by
    simpa [prefixWord, tailWord_4114147, baseEnd_4114147] using wordTrace_append hprefix tailTrace_4114147
  have hstable : (prefixWord ++ tailWord_4114147).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4114147).length < 2 ^ (prefixWord ++ tailWord_4114147).sum := by decide
  have hdescent : baseEnd_4114147 < baseStart_4114147 := by decide
  rcases family_descends (prefixWord ++ tailWord_4114147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4114164 : List Nat := [2, 6, 1, 1, 1, 2, 3, 6]
def baseStart_4114164 : Nat := 118140960795 + 4114164 * 2 ^ 59
def prefixEnd_4114164 : Nat := 4983230072969 + 3 ^ 40 * 4114164 * 2
def baseEnd_4114164 : Nat := 156484712846247892454023

theorem tailTrace_4114164 : CollatzResearch.WordTrace tailWord_4114164 prefixEnd_4114164 156484712846247892454023 := by
  unfold tailWord_4114164
  simp only [CollatzResearch.WordTrace]
  refine ⟨75027944333546973058010773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100037259111395964077347697 75027944333546973058010773)
  ·
    refine ⟨3516934890635014362094255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 75027944333546973058010773 3516934890635014362094255)
    ·
      refine ⟨5275402335952521543141383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3516934890635014362094255 5275402335952521543141383)
      ·
        refine ⟨7913103503928782314712075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5275402335952521543141383 7913103503928782314712075)
        ·
          refine ⟨11869655255893173472068113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7913103503928782314712075 11869655255893173472068113)
          ·
            refine ⟨8902241441919880104051085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11869655255893173472068113 8902241441919880104051085)
            ·
              refine ⟨3338340540719955039019157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8902241441919880104051085 3338340540719955039019157)
              ·
                refine ⟨156484712846247892454023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3338340540719955039019157 156484712846247892454023)
                ·
                  rfl

theorem cell22_4114164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 3, 6].length) (baseStart_4114164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4114164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4114164 prefixEnd_4114164 := by exact prefixLift 4114164
  have htrace : WordTrace (prefixWord ++ tailWord_4114164) baseStart_4114164 baseEnd_4114164 := by
    simpa [prefixWord, tailWord_4114164, baseEnd_4114164] using wordTrace_append hprefix tailTrace_4114164
  have hstable : (prefixWord ++ tailWord_4114164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4114164).length < 2 ^ (prefixWord ++ tailWord_4114164).sum := by decide
  have hdescent : baseEnd_4114164 < baseStart_4114164 := by decide
  rcases family_descends (prefixWord ++ tailWord_4114164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4114248 : List Nat := [2, 1, 3, 1, 1, 4, 10]
def baseStart_4114248 : Nat := 118140960795 + 4114248 * 2 ^ 59
def prefixEnd_4114248 : Nat := 4983230072969 + 3 ^ 40 * 4114248 * 2
def baseEnd_4114248 : Nat := 52162635945662326406887

theorem tailTrace_4114248 : CollatzResearch.WordTrace tailWord_4114248 prefixEnd_4114248 52162635945662326406887 := by
  unfold tailWord_4114248
  simp only [CollatzResearch.WordTrace]
  refine ⟨75029476199394814231039699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100039301599193085641386265 75029476199394814231039699)
  ·
    refine ⟨112544214299092221346559549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75029476199394814231039699 112544214299092221346559549)
    ·
      refine ⟨42204080362159583004959831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112544214299092221346559549 42204080362159583004959831)
      ·
        refine ⟨63306120543239374507439747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42204080362159583004959831 63306120543239374507439747)
        ·
          refine ⟨94959180814859061761159621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63306120543239374507439747 94959180814859061761159621)
          ·
            refine ⟨17804846402786074080217429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94959180814859061761159621 17804846402786074080217429)
            ·
              refine ⟨52162635945662326406887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 17804846402786074080217429 52162635945662326406887)
              ·
                rfl

theorem cell22_4114248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 10].length) (baseStart_4114248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4114248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4114248 prefixEnd_4114248 := by exact prefixLift 4114248
  have htrace : WordTrace (prefixWord ++ tailWord_4114248) baseStart_4114248 baseEnd_4114248 := by
    simpa [prefixWord, tailWord_4114248, baseEnd_4114248] using wordTrace_append hprefix tailTrace_4114248
  have hstable : (prefixWord ++ tailWord_4114248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4114248).length < 2 ^ (prefixWord ++ tailWord_4114248).sum := by decide
  have hdescent : baseEnd_4114248 < baseStart_4114248 := by decide
  rcases family_descends (prefixWord ++ tailWord_4114248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4114250 : List Nat := [3, 1, 2, 1, 1, 1, 5, 2, 2, 4]
def baseStart_4114250 : Nat := 118140960795 + 4114250 * 2 ^ 59
def prefixEnd_4114250 : Nat := 4983230072969 + 3 ^ 40 * 4114250 * 2
def baseEnd_4114250 : Nat := 1408391855173755474435943

theorem tailTrace_4114250 : CollatzResearch.WordTrace tailWord_4114250 prefixEnd_4114250 1408391855173755474435943 := by
  unfold tailWord_4114250
  simp only [CollatzResearch.WordTrace]
  refine ⟨37514756336195595700913051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100039350229854921869101469 37514756336195595700913051)
  ·
    refine ⟨56272134504293393551369577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37514756336195595700913051 56272134504293393551369577)
    ·
      refine ⟨42204100878220045163527183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56272134504293393551369577 42204100878220045163527183)
      ·
        refine ⟨63306151317330067745290775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42204100878220045163527183 63306151317330067745290775)
        ·
          refine ⟨94959226975995101617936163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63306151317330067745290775 94959226975995101617936163)
          ·
            refine ⟨142438840463992652426904245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94959226975995101617936163 142438840463992652426904245)
            ·
              refine ⟨13353641293499311165022273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 142438840463992652426904245 13353641293499311165022273)
              ·
                refine ⟨10015230970124483373766705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13353641293499311165022273 10015230970124483373766705)
                ·
                  refine ⟨7511423227593362530325029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10015230970124483373766705 7511423227593362530325029)
                  ·
                    refine ⟨1408391855173755474435943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7511423227593362530325029 1408391855173755474435943)
                    ·
                      rfl

theorem cell22_4114250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 2, 2, 4].length) (baseStart_4114250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4114250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4114250 prefixEnd_4114250 := by exact prefixLift 4114250
  have htrace : WordTrace (prefixWord ++ tailWord_4114250) baseStart_4114250 baseEnd_4114250 := by
    simpa [prefixWord, tailWord_4114250, baseEnd_4114250] using wordTrace_append hprefix tailTrace_4114250
  have hstable : (prefixWord ++ tailWord_4114250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4114250).length < 2 ^ (prefixWord ++ tailWord_4114250).sum := by decide
  have hdescent : baseEnd_4114250 < baseStart_4114250 := by decide
  rcases family_descends (prefixWord ++ tailWord_4114250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4114325 : List Nat := [1, 3, 2, 1, 1, 3, 3, 1, 2, 5]
def baseStart_4114325 : Nat := 118140960795 + 4114325 * 2 ^ 59
def prefixEnd_4114325 : Nat := 4983230072969 + 3 ^ 40 * 4114325 * 2
def baseEnd_4114325 : Nat := 1408417529206480278810713

theorem tailTrace_4114325 : CollatzResearch.WordTrace tailWord_4114325 prefixEnd_4114325 1408417529206480278810713 := by
  unfold tailWord_4114325
  simp only [CollatzResearch.WordTrace]
  refine ⟨150061760819510670612632429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100041173879673780408421619 150061760819510670612632429)
  ·
    refine ⟨56273160307316501479737161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150061760819510670612632429 56273160307316501479737161)
    ·
      refine ⟨42204870230487376109802871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56273160307316501479737161 42204870230487376109802871)
      ·
        refine ⟨63307305345731064164704307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42204870230487376109802871 63307305345731064164704307)
        ·
          refine ⟨94960958018596596247056461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63307305345731064164704307 94960958018596596247056461)
          ·
            refine ⟨35610359256973723592646173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94960958018596596247056461 35610359256973723592646173)
            ·
              refine ⟨13353884721365146347242315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35610359256973723592646173 13353884721365146347242315)
              ·
                refine ⟨20030827082047719520863473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13353884721365146347242315 20030827082047719520863473)
                ·
                  refine ⟨15023120311535789640647605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20030827082047719520863473 15023120311535789640647605)
                  ·
                    refine ⟨1408417529206480278810713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15023120311535789640647605 1408417529206480278810713)
                    ·
                      rfl

theorem cell22_4114325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 1, 2, 5].length) (baseStart_4114325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4114325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4114325 prefixEnd_4114325 := by exact prefixLift 4114325
  have htrace : WordTrace (prefixWord ++ tailWord_4114325) baseStart_4114325 baseEnd_4114325 := by
    simpa [prefixWord, tailWord_4114325, baseEnd_4114325] using wordTrace_append hprefix tailTrace_4114325
  have hstable : (prefixWord ++ tailWord_4114325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4114325).length < 2 ^ (prefixWord ++ tailWord_4114325).sum := by decide
  have hdescent : baseEnd_4114325 < baseStart_4114325 := by decide
  rcases family_descends (prefixWord ++ tailWord_4114325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4114385 : List Nat := [1, 2, 2, 1, 2, 1, 2, 1, 6, 4]
def baseStart_4114385 : Nat := 118140960795 + 4114385 * 2 ^ 59
def prefixEnd_4114385 : Nat := 4983230072969 + 3 ^ 40 * 4114385 * 2
def baseEnd_4114385 : Nat := 1408438068432660122310529

theorem tailTrace_4114385 : CollatzResearch.WordTrace tailWord_4114385 prefixEnd_4114385 1408438068432660122310529 := by
  unfold tailWord_4114385
  simp only [CollatzResearch.WordTrace]
  refine ⟨150063949199293300859816609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100042632799528867239877739 150063949199293300859816609)
  ·
    refine ⟨112547961899469975644862457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150063949199293300859816609 112547961899469975644862457)
    ·
      refine ⟨84410971424602481733646843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112547961899469975644862457 84410971424602481733646843)
      ·
        refine ⟨126616457136903722600470265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84410971424602481733646843 126616457136903722600470265)
        ·
          refine ⟨94962342852677791950352699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126616457136903722600470265 94962342852677791950352699)
          ·
            refine ⟨142443514279016687925529049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94962342852677791950352699 142443514279016687925529049)
            ·
              refine ⟨106832635709262515944146787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142443514279016687925529049 106832635709262515944146787)
              ·
                refine ⟨160248953563893773916220181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106832635709262515944146787 160248953563893773916220181)
                ·
                  refine ⟨7511669698307520652322821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 160248953563893773916220181 7511669698307520652322821)
                  ·
                    refine ⟨1408438068432660122310529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7511669698307520652322821 1408438068432660122310529)
                    ·
                      rfl

theorem cell22_4114385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 6, 4].length) (baseStart_4114385 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4114385 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4114385 prefixEnd_4114385 := by exact prefixLift 4114385
  have htrace : WordTrace (prefixWord ++ tailWord_4114385) baseStart_4114385 baseEnd_4114385 := by
    simpa [prefixWord, tailWord_4114385, baseEnd_4114385] using wordTrace_append hprefix tailTrace_4114385
  have hstable : (prefixWord ++ tailWord_4114385).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4114385).length < 2 ^ (prefixWord ++ tailWord_4114385).sum := by decide
  have hdescent : baseEnd_4114385 < baseStart_4114385 := by decide
  rcases family_descends (prefixWord ++ tailWord_4114385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4114417 : List Nat := [1, 2, 2, 2, 5, 2, 8]
def baseStart_4114417 : Nat := 118140960795 + 4114417 * 2 ^ 59
def prefixEnd_4114417 : Nat := 4983230072969 + 3 ^ 40 * 4114417 * 2
def baseEnd_4114417 : Nat := 52164778618023063167053

theorem tailTrace_4114417 : CollatzResearch.WordTrace tailWord_4114417 prefixEnd_4114417 52164778618023063167053 := by
  unfold tailWord_4114417
  simp only [CollatzResearch.WordTrace]
  refine ⟨150065116335177370324981505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100043410890118246883321003 150065116335177370324981505)
  ·
    refine ⟨112548837251383027743736129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150065116335177370324981505 112548837251383027743736129)
    ·
      refine ⟨84411627938537270807802097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112548837251383027743736129 84411627938537270807802097)
      ·
        refine ⟨63308720953902953105851573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84411627938537270807802097 63308720953902953105851573)
        ·
          refine ⟨5935192589428401853673585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 63308720953902953105851573 5935192589428401853673585)
          ·
            refine ⟨4451394442071301390255189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5935192589428401853673585 4451394442071301390255189)
            ·
              refine ⟨52164778618023063167053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4451394442071301390255189 52164778618023063167053)
              ·
                rfl

theorem cell22_4114417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 8].length) (baseStart_4114417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4114417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4114417 prefixEnd_4114417 := by exact prefixLift 4114417
  have htrace : WordTrace (prefixWord ++ tailWord_4114417) baseStart_4114417 baseEnd_4114417 := by
    simpa [prefixWord, tailWord_4114417, baseEnd_4114417] using wordTrace_append hprefix tailTrace_4114417
  have hstable : (prefixWord ++ tailWord_4114417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4114417).length < 2 ^ (prefixWord ++ tailWord_4114417).sum := by decide
  have hdescent : baseEnd_4114417 < baseStart_4114417 := by decide
  rcases family_descends (prefixWord ++ tailWord_4114417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4114432 : List Nat := [2, 1, 1, 2, 1, 1, 1, 7, 3, 3]
def baseStart_4114432 : Nat := 118140960795 + 4114432 * 2 ^ 59
def prefixEnd_4114432 : Nat := 4983230072969 + 3 ^ 40 * 4114432 * 2
def baseEnd_4114432 : Nat := 1408454157493167666385385

theorem tailTrace_4114432 : CollatzResearch.WordTrace tailWord_4114432 prefixEnd_4114432 1408454157493167666385385 := by
  unfold tailWord_4114432
  simp only [CollatzResearch.WordTrace]
  refine ⟨75032831715061513943388775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100043775620082018591185033 75032831715061513943388775)
  ·
    refine ⟨112549247572592270915083163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75032831715061513943388775 112549247572592270915083163)
    ·
      refine ⟨168823871358888406372624745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112549247572592270915083163 168823871358888406372624745)
      ·
        refine ⟨126617903519166304779468559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168823871358888406372624745 126617903519166304779468559)
        ·
          refine ⟨189926855278749457169202839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126617903519166304779468559 189926855278749457169202839)
          ·
            refine ⟨284890282918124185753804259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189926855278749457169202839 284890282918124185753804259)
            ·
              refine ⟨427335424377186278630706389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 284890282918124185753804259 427335424377186278630706389)
              ·
                refine ⟨10015674008840303405407181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 427335424377186278630706389 10015674008840303405407181)
                ·
                  refine ⟨3755877753315113777027693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10015674008840303405407181 3755877753315113777027693)
                  ·
                    refine ⟨1408454157493167666385385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3755877753315113777027693 1408454157493167666385385)
                    ·
                      rfl

theorem cell22_4114432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 7, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 7, 3, 3].length) (baseStart_4114432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4114432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4114432 prefixEnd_4114432 := by exact prefixLift 4114432
  have htrace : WordTrace (prefixWord ++ tailWord_4114432) baseStart_4114432 baseEnd_4114432 := by
    simpa [prefixWord, tailWord_4114432, baseEnd_4114432] using wordTrace_append hprefix tailTrace_4114432
  have hstable : (prefixWord ++ tailWord_4114432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4114432).length < 2 ^ (prefixWord ++ tailWord_4114432).sum := by decide
  have hdescent : baseEnd_4114432 < baseStart_4114432 := by decide
  rcases family_descends (prefixWord ++ tailWord_4114432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4114466 : List Nat := [3, 3, 1, 1, 1, 2, 2, 5, 1, 3]
def baseStart_4114466 : Nat := 118140960795 + 4114466 * 2 ^ 59
def prefixEnd_4114466 : Nat := 4983230072969 + 3 ^ 40 * 4114466 * 2
def baseEnd_4114466 : Nat := 1408465796388002911035281

theorem tailTrace_4114466 : CollatzResearch.WordTrace tailWord_4114466 prefixEnd_4114466 1408465796388002911035281 := by
  unfold tailWord_4114466
  simp only [CollatzResearch.WordTrace]
  refine ⟨37516725877999962923378813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100044602341333234462343501 37516725877999962923378813)
  ·
    refine ⟨14068772204249986096267055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37516725877999962923378813 14068772204249986096267055)
    ·
      refine ⟨21103158306374979144400583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14068772204249986096267055 21103158306374979144400583)
      ·
        refine ⟨31654737459562468716600875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21103158306374979144400583 31654737459562468716600875)
        ·
          refine ⟨47482106189343703074901313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31654737459562468716600875 47482106189343703074901313)
          ·
            refine ⟨35611579642007777306175985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47482106189343703074901313 35611579642007777306175985)
            ·
              refine ⟨26708684731505832979631989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35611579642007777306175985 26708684731505832979631989)
              ·
                refine ⟨2503939193578671841840499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26708684731505832979631989 2503939193578671841840499)
                ·
                  refine ⟨3755908790368007762760749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2503939193578671841840499 3755908790368007762760749)
                  ·
                    refine ⟨1408465796388002911035281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3755908790368007762760749 1408465796388002911035281)
                    ·
                      rfl

theorem cell22_4114466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 5, 1, 3].length) (baseStart_4114466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4114466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4114466 prefixEnd_4114466 := by exact prefixLift 4114466
  have htrace : WordTrace (prefixWord ++ tailWord_4114466) baseStart_4114466 baseEnd_4114466 := by
    simpa [prefixWord, tailWord_4114466, baseEnd_4114466] using wordTrace_append hprefix tailTrace_4114466
  have hstable : (prefixWord ++ tailWord_4114466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4114466).length < 2 ^ (prefixWord ++ tailWord_4114466).sum := by decide
  have hdescent : baseEnd_4114466 < baseStart_4114466 := by decide
  rcases family_descends (prefixWord ++ tailWord_4114466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4114492 : List Nat := [2, 2, 2, 2, 2, 1, 1, 1, 5, 4]
def baseStart_4114492 : Nat := 118140960795 + 4114492 * 2 ^ 59
def prefixEnd_4114492 : Nat := 4983230072969 + 3 ^ 40 * 4114492 * 2
def baseEnd_4114492 : Nat := 1408474696719347509885201

theorem tailTrace_4114492 : CollatzResearch.WordTrace tailWord_4114492 prefixEnd_4114492 1408474696719347509885201 := by
  unfold tailWord_4114492
  simp only [CollatzResearch.WordTrace]
  refine ⟨75033925904952829066980865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100045234539937105422641153 75033925904952829066980865)
  ·
    refine ⟨56275444428714621800235649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75033925904952829066980865 56275444428714621800235649)
    ·
      refine ⟨42206583321535966350176737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56275444428714621800235649 42206583321535966350176737)
      ·
        refine ⟨31654937491151974762632553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42206583321535966350176737 31654937491151974762632553)
        ·
          refine ⟨23741203118363981071974415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31654937491151974762632553 23741203118363981071974415)
          ·
            refine ⟨35611804677545971607961623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23741203118363981071974415 35611804677545971607961623)
            ·
              refine ⟨53417707016318957411942435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35611804677545971607961623 53417707016318957411942435)
              ·
                refine ⟨80126560524478436117913653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53417707016318957411942435 80126560524478436117913653)
                ·
                  refine ⟨7511865049169853386054405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 80126560524478436117913653 7511865049169853386054405)
                  ·
                    refine ⟨1408474696719347509885201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7511865049169853386054405 1408474696719347509885201)
                    ·
                      rfl

theorem cell22_4114492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 5, 4].length) (baseStart_4114492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4114492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4114492 prefixEnd_4114492 := by exact prefixLift 4114492
  have htrace : WordTrace (prefixWord ++ tailWord_4114492) baseStart_4114492 baseEnd_4114492 := by
    simpa [prefixWord, tailWord_4114492, baseEnd_4114492] using wordTrace_append hprefix tailTrace_4114492
  have hstable : (prefixWord ++ tailWord_4114492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4114492).length < 2 ^ (prefixWord ++ tailWord_4114492).sum := by decide
  have hdescent : baseEnd_4114492 < baseStart_4114492 := by decide
  rcases family_descends (prefixWord ++ tailWord_4114492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4114509 : List Nat := [1, 6, 1, 1, 1, 1, 1, 3, 3, 4]
def baseStart_4114509 : Nat := 118140960795 + 4114509 * 2 ^ 59
def prefixEnd_4114509 : Nat := 4983230072969 + 3 ^ 40 * 4114509 * 2
def baseEnd_4114509 : Nat := 1408480516166765132210149

theorem tailTrace_4114509 : CollatzResearch.WordTrace tailWord_4114509 prefixEnd_4114509 1408480516166765132210149 := by
  unfold tailWord_4114509
  simp only [CollatzResearch.WordTrace]
  refine ⟨150068471850844070037330581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100045647900562713358220387 150068471850844070037330581)
  ·
    refine ⟨7034459618008315782999871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 150068471850844070037330581 7034459618008315782999871)
    ·
      refine ⟨10551689427012473674499807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7034459618008315782999871 10551689427012473674499807)
      ·
        refine ⟨15827534140518710511749711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10551689427012473674499807 15827534140518710511749711)
        ·
          refine ⟨23741301210778065767624567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15827534140518710511749711 23741301210778065767624567)
          ·
            refine ⟨35611951816167098651436851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23741301210778065767624567 35611951816167098651436851)
            ·
              refine ⟨53417927724250647977155277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35611951816167098651436851 53417927724250647977155277)
              ·
                refine ⟨20031722896593992991433229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53417927724250647977155277 20031722896593992991433229)
                ·
                  refine ⟨7511896086222747371787461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20031722896593992991433229 7511896086222747371787461)
                  ·
                    refine ⟨1408480516166765132210149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7511896086222747371787461 1408480516166765132210149)
                    ·
                      rfl

theorem cell22_4114509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_4114509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4114509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4114509 prefixEnd_4114509 := by exact prefixLift 4114509
  have htrace : WordTrace (prefixWord ++ tailWord_4114509) baseStart_4114509 baseEnd_4114509 := by
    simpa [prefixWord, tailWord_4114509, baseEnd_4114509] using wordTrace_append hprefix tailTrace_4114509
  have hstable : (prefixWord ++ tailWord_4114509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4114509).length < 2 ^ (prefixWord ++ tailWord_4114509).sum := by decide
  have hdescent : baseEnd_4114509 < baseStart_4114509 := by decide
  rcases family_descends (prefixWord ++ tailWord_4114509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4114522 : List Nat := [3, 1, 1, 2, 1, 1, 3, 4, 1, 5]
def baseStart_4114522 : Nat := 118140960795 + 4114522 * 2 ^ 59
def prefixEnd_4114522 : Nat := 4983230072969 + 3 ^ 40 * 4114522 * 2
def baseEnd_4114522 : Nat := 1408484966332437431635109

theorem tailTrace_4114522 : CollatzResearch.WordTrace tailWord_4114522 prefixEnd_4114522 1408484966332437431635109 := by
  unfold tailWord_4114522
  simp only [CollatzResearch.WordTrace]
  refine ⟨37517236499949243314388455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100045963999864648838369213 37517236499949243314388455)
  ·
    refine ⟨56275854749923864971582683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37517236499949243314388455 56275854749923864971582683)
    ·
      refine ⟨84413782124885797457374025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56275854749923864971582683 84413782124885797457374025)
      ·
        refine ⟨63310336593664348093030519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84413782124885797457374025 63310336593664348093030519)
        ·
          refine ⟨94965504890496522139545779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63310336593664348093030519 94965504890496522139545779)
          ·
            refine ⟨142448257335744783209318669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94965504890496522139545779 142448257335744783209318669)
            ·
              refine ⟨53418096500904293703494501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142448257335744783209318669 53418096500904293703494501)
              ·
                refine ⟨10015893093919555069405219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53418096500904293703494501 10015893093919555069405219)
                ·
                  refine ⟨15023839640879332604107829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10015893093919555069405219 15023839640879332604107829)
                  ·
                    refine ⟨1408484966332437431635109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15023839640879332604107829 1408484966332437431635109)
                    ·
                      rfl

theorem cell22_4114522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 4, 1, 5].length) (baseStart_4114522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4114522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4114522 prefixEnd_4114522 := by exact prefixLift 4114522
  have htrace : WordTrace (prefixWord ++ tailWord_4114522) baseStart_4114522 baseEnd_4114522 := by
    simpa [prefixWord, tailWord_4114522, baseEnd_4114522] using wordTrace_append hprefix tailTrace_4114522
  have hstable : (prefixWord ++ tailWord_4114522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4114522).length < 2 ^ (prefixWord ++ tailWord_4114522).sum := by decide
  have hdescent : baseEnd_4114522 < baseStart_4114522 := by decide
  rcases family_descends (prefixWord ++ tailWord_4114522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4114537 : List Nat := [1, 2, 1, 1, 1, 5, 2, 1, 4, 4]
def baseStart_4114537 : Nat := 118140960795 + 4114537 * 2 ^ 59
def prefixEnd_4114537 : Nat := 4983230072969 + 3 ^ 40 * 4114537 * 2
def baseEnd_4114537 : Nat := 1408490101138982392510063

theorem tailTrace_4114537 : CollatzResearch.WordTrace tailWord_4114537 prefixEnd_4114537 1408490101138982392510063 := by
  unfold tailWord_4114537
  simp only [CollatzResearch.WordTrace]
  refine ⟨150069493094742630819349865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100046328729828420546233243 150069493094742630819349865)
  ·
    refine ⟨112552119821056973114512399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150069493094742630819349865 112552119821056973114512399)
    ·
      refine ⟨168828179731585459671768599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112552119821056973114512399 168828179731585459671768599)
      ·
        refine ⟨253242269597378189507652899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168828179731585459671768599 253242269597378189507652899)
        ·
          refine ⟨379863404396067284261479349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253242269597378189507652899 379863404396067284261479349)
          ·
            refine ⟨35612194162131307899513689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 379863404396067284261479349 35612194162131307899513689)
            ·
              refine ⟨26709145621598480924635267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35612194162131307899513689 26709145621598480924635267)
              ·
                refine ⟨40063718432397721386952901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26709145621598480924635267 40063718432397721386952901)
                ·
                  refine ⟨7511947206074572760053669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40063718432397721386952901 7511947206074572760053669)
                  ·
                    refine ⟨1408490101138982392510063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7511947206074572760053669 1408490101138982392510063)
                    ·
                      rfl

theorem cell22_4114537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 1, 4, 4].length) (baseStart_4114537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4114537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4114537 prefixEnd_4114537 := by exact prefixLift 4114537
  have htrace : WordTrace (prefixWord ++ tailWord_4114537) baseStart_4114537 baseEnd_4114537 := by
    simpa [prefixWord, tailWord_4114537, baseEnd_4114537] using wordTrace_append hprefix tailTrace_4114537
  have hstable : (prefixWord ++ tailWord_4114537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4114537).length < 2 ^ (prefixWord ++ tailWord_4114537).sum := by decide
  have hdescent : baseEnd_4114537 < baseStart_4114537 := by decide
  rcases family_descends (prefixWord ++ tailWord_4114537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4114586 : List Nat := [3, 1, 1, 5, 3, 1, 8]
def baseStart_4114586 : Nat := 118140960795 + 4114586 * 2 ^ 59
def prefixEnd_4114586 : Nat := 4983230072969 + 3 ^ 40 * 4114586 * 2
def baseEnd_4114586 : Nat := 52166921290383799927219

theorem tailTrace_4114586 : CollatzResearch.WordTrace tailWord_4114586 prefixEnd_4114586 52166921290383799927219 := by
  unfold tailWord_4114586
  simp only [CollatzResearch.WordTrace]
  refine ⟨37517820067891278046970903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100047520181043408125255741 37517820067891278046970903)
  ·
    refine ⟨56276730101836917070456355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37517820067891278046970903 56276730101836917070456355)
    ·
      refine ⟨84415095152755375605684533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56276730101836917070456355 84415095152755375605684533)
      ·
        refine ⟨7913915170570816463032925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 84415095152755375605684533 7913915170570816463032925)
        ·
          refine ⟨2967718188964056173637347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7913915170570816463032925 2967718188964056173637347)
          ·
            refine ⟨4451577283446084260456021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2967718188964056173637347 4451577283446084260456021)
            ·
              refine ⟨52166921290383799927219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4451577283446084260456021 52166921290383799927219)
              ·
                rfl

theorem cell22_4114586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 8].length) (baseStart_4114586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4114586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4114586 prefixEnd_4114586 := by exact prefixLift 4114586
  have htrace : WordTrace (prefixWord ++ tailWord_4114586) baseStart_4114586 baseEnd_4114586 := by
    simpa [prefixWord, tailWord_4114586, baseEnd_4114586] using wordTrace_append hprefix tailTrace_4114586
  have hstable : (prefixWord ++ tailWord_4114586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4114586).length < 2 ^ (prefixWord ++ tailWord_4114586).sum := by decide
  have hdescent : baseEnd_4114586 < baseStart_4114586 := by decide
  rcases family_descends (prefixWord ++ tailWord_4114586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4114597 : List Nat := [1, 3, 1, 2, 1, 3, 1, 3, 7]
def baseStart_4114597 : Nat := 118140960795 + 4114597 * 2 ^ 59
def prefixEnd_4114597 : Nat := 4983230072969 + 3 ^ 40 * 4114597 * 2
def baseEnd_4114597 : Nat := 469503546788387412003293

theorem tailTrace_4114597 : CollatzResearch.WordTrace tailWord_4114597 prefixEnd_4114597 469503546788387412003293 := by
  unfold tailWord_4114597
  simp only [CollatzResearch.WordTrace]
  refine ⟨150071681474525261066534045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100047787649683507377689363 150071681474525261066534045)
  ·
    refine ⟨56276880552946972899950267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150071681474525261066534045 56276880552946972899950267)
    ·
      refine ⟨84415320829420459349925401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56276880552946972899950267 84415320829420459349925401)
      ·
        refine ⟨63311490622065344512444051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84415320829420459349925401 63311490622065344512444051)
        ·
          refine ⟨94967235933098016768666077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63311490622065344512444051 94967235933098016768666077)
          ·
            refine ⟨35612713474911756288249779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94967235933098016768666077 35612713474911756288249779)
            ·
              refine ⟨53419070212367634432374669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35612713474911756288249779 53419070212367634432374669)
              ·
                refine ⟨20032151329637862912140501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53419070212367634432374669 20032151329637862912140501)
                ·
                  refine ⟨469503546788387412003293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20032151329637862912140501 469503546788387412003293)
                  ·
                    rfl

theorem cell22_4114597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 3, 7].length) (baseStart_4114597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4114597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4114597 prefixEnd_4114597 := by exact prefixLift 4114597
  have htrace : WordTrace (prefixWord ++ tailWord_4114597) baseStart_4114597 baseEnd_4114597 := by
    simpa [prefixWord, tailWord_4114597, baseEnd_4114597] using wordTrace_append hprefix tailTrace_4114597
  have hstable : (prefixWord ++ tailWord_4114597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4114597).length < 2 ^ (prefixWord ++ tailWord_4114597).sum := by decide
  have hdescent : baseEnd_4114597 < baseStart_4114597 := by decide
  rcases family_descends (prefixWord ++ tailWord_4114597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4114652 : List Nat := [2, 2, 5, 2, 1, 1, 1, 4, 1, 3]
def baseStart_4114652 : Nat := 118140960795 + 4114652 * 2 ^ 59
def prefixEnd_4114652 : Nat := 4983230072969 + 3 ^ 40 * 4114652 * 2
def baseEnd_4114652 : Nat := 1408529467989160425884711

theorem tailTrace_4114652 : CollatzResearch.WordTrace tailWord_4114652 prefixEnd_4114652 1408529467989160425884711 := by
  unfold tailWord_4114652
  simp only [CollatzResearch.WordTrace]
  refine ⟨75036843744663002729893105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100049124992884003639857473 75036843744663002729893105)
  ·
    refine ⟨56277632808497252047419829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75036843744663002729893105 56277632808497252047419829)
    ·
      refine ⟨5276028075796617379445609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 56277632808497252047419829 5276028075796617379445609)
      ·
        refine ⟨3957021056847463034584207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5276028075796617379445609 3957021056847463034584207)
        ·
          refine ⟨5935531585271194551876311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3957021056847463034584207 5935531585271194551876311)
          ·
            refine ⟨8903297377906791827814467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5935531585271194551876311 8903297377906791827814467)
            ·
              refine ⟨13354946066860187741721701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8903297377906791827814467 13354946066860187741721701)
              ·
                refine ⟨2504052387536285201572819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13354946066860187741721701 2504052387536285201572819)
                ·
                  refine ⟨3756078581304427802359229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2504052387536285201572819 3756078581304427802359229)
                  ·
                    refine ⟨1408529467989160425884711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3756078581304427802359229 1408529467989160425884711)
                    ·
                      rfl

theorem cell22_4114652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_4114652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4114652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4114652 prefixEnd_4114652 := by exact prefixLift 4114652
  have htrace : WordTrace (prefixWord ++ tailWord_4114652) baseStart_4114652 baseEnd_4114652 := by
    simpa [prefixWord, tailWord_4114652, baseEnd_4114652] using wordTrace_append hprefix tailTrace_4114652
  have hstable : (prefixWord ++ tailWord_4114652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4114652).length < 2 ^ (prefixWord ++ tailWord_4114652).sum := by decide
  have hdescent : baseEnd_4114652 < baseStart_4114652 := by decide
  rcases family_descends (prefixWord ++ tailWord_4114652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4114689 : List Nat := [1, 2, 4, 1, 1, 2, 3, 1, 1, 6]
def baseStart_4114689 : Nat := 118140960795 + 4114689 * 2 ^ 59
def prefixEnd_4114689 : Nat := 4983230072969 + 3 ^ 40 * 4114689 * 2
def baseEnd_4114689 : Nat := 1408542133845304662709597

theorem tailTrace_4114689 : CollatzResearch.WordTrace tailWord_4114689 prefixEnd_4114689 1408542133845304662709597 := by
  unfold tailWord_4114689
  simp only [CollatzResearch.WordTrace]
  refine ⟨150075036990191960778883121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100050024660127973852588747 150075036990191960778883121)
  ·
    refine ⟨112556277742643970584162341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150075036990191960778883121 112556277742643970584162341)
    ·
      refine ⟨21104302076745744484530439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112556277742643970584162341 21104302076745744484530439)
      ·
        refine ⟨31656453115118616726795659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21104302076745744484530439 31656453115118616726795659)
        ·
          refine ⟨47484679672677925090193489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31656453115118616726795659 47484679672677925090193489)
          ·
            refine ⟨35613509754508443817645117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47484679672677925090193489 35613509754508443817645117)
            ·
              refine ⟨13355066157940666431616919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35613509754508443817645117 13355066157940666431616919)
              ·
                refine ⟨20032599236910999647425379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13355066157940666431616919 20032599236910999647425379)
                ·
                  refine ⟨30048898855366499471138069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20032599236910999647425379 30048898855366499471138069)
                  ·
                    refine ⟨1408542133845304662709597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30048898855366499471138069 1408542133845304662709597)
                    ·
                      rfl

theorem cell22_4114689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 1, 1, 6].length) (baseStart_4114689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4114689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4114689 prefixEnd_4114689 := by exact prefixLift 4114689
  have htrace : WordTrace (prefixWord ++ tailWord_4114689) baseStart_4114689 baseEnd_4114689 := by
    simpa [prefixWord, tailWord_4114689, baseEnd_4114689] using wordTrace_append hprefix tailTrace_4114689
  have hstable : (prefixWord ++ tailWord_4114689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4114689).length < 2 ^ (prefixWord ++ tailWord_4114689).sum := by decide
  have hdescent : baseEnd_4114689 < baseStart_4114689 := by decide
  rcases family_descends (prefixWord ++ tailWord_4114689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4114725 : List Nat := [1, 3, 1, 2, 5, 1, 3, 1, 2, 3]
def baseStart_4114725 : Nat := 118140960795 + 4114725 * 2 ^ 59
def prefixEnd_4114725 : Nat := 4983230072969 + 3 ^ 40 * 4114725 * 2
def baseEnd_4114725 : Nat := 1408554457381012568809487

theorem tailTrace_4114725 : CollatzResearch.WordTrace tailWord_4114725 prefixEnd_4114725 1408554457381012568809487 := by
  unfold tailWord_4114725
  simp only [CollatzResearch.WordTrace]
  refine ⟨150076350018061538927193629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100050900012041025951462419 150076350018061538927193629)
  ·
    refine ⟨56278631256773077097697611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150076350018061538927193629 56278631256773077097697611)
    ·
      refine ⟨84417946885159615646546417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56278631256773077097697611 84417946885159615646546417)
      ·
        refine ⟨63313460163869711734909813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84417946885159615646546417 63313460163869711734909813)
        ·
          refine ⟨5935636890362785475147795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 63313460163869711734909813 5935636890362785475147795)
          ·
            refine ⟨8903455335544178212721693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5935636890362785475147795 8903455335544178212721693)
            ·
              refine ⟨3338795750829066829770635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8903455335544178212721693 3338795750829066829770635)
              ·
                refine ⟨5008193626243600244655953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3338795750829066829770635 5008193626243600244655953)
                ·
                  refine ⟨3756145219682700183491965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5008193626243600244655953 3756145219682700183491965)
                  ·
                    refine ⟨1408554457381012568809487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3756145219682700183491965 1408554457381012568809487)
                    ·
                      rfl

theorem cell22_4114725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 3, 1, 2, 3].length) (baseStart_4114725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4114725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4114725 prefixEnd_4114725 := by exact prefixLift 4114725
  have htrace : WordTrace (prefixWord ++ tailWord_4114725) baseStart_4114725 baseEnd_4114725 := by
    simpa [prefixWord, tailWord_4114725, baseEnd_4114725] using wordTrace_append hprefix tailTrace_4114725
  have hstable : (prefixWord ++ tailWord_4114725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4114725).length < 2 ^ (prefixWord ++ tailWord_4114725).sum := by decide
  have hdescent : baseEnd_4114725 < baseStart_4114725 := by decide
  rcases family_descends (prefixWord ++ tailWord_4114725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4114738 : List Nat := [3, 2, 1, 1, 5, 2, 2, 6]
def baseStart_4114738 : Nat := 118140960795 + 4114738 * 2 ^ 59
def prefixEnd_4114738 : Nat := 4983230072969 + 3 ^ 40 * 4114738 * 2
def baseEnd_4114738 : Nat := 156506545282964985359383

theorem tailTrace_4114738 : CollatzResearch.WordTrace tailWord_4114738 prefixEnd_4114738 156506545282964985359383 := by
  unfold tailWord_4114738
  simp only [CollatzResearch.WordTrace]
  refine ⟨37519206041753610536854217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100051216111342961431611245 37519206041753610536854217)
  ·
    refine ⟨28139404531315207902640663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37519206041753610536854217 28139404531315207902640663)
    ·
      refine ⟨42209106796972811853960995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28139404531315207902640663 42209106796972811853960995)
      ·
        refine ⟨63313660195459217780941493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42209106796972811853960995 63313660195459217780941493)
        ·
          refine ⟨5935655643324301666963265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 63313660195459217780941493 5935655643324301666963265)
          ·
            refine ⟨4451741732493226250222449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5935655643324301666963265 4451741732493226250222449)
            ·
              refine ⟨3338806299369919687666837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4451741732493226250222449 3338806299369919687666837)
              ·
                refine ⟨156506545282964985359383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3338806299369919687666837 156506545282964985359383)
                ·
                  rfl

theorem cell22_4114738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 2, 6].length) (baseStart_4114738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4114738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4114738 prefixEnd_4114738 := by exact prefixLift 4114738
  have htrace : WordTrace (prefixWord ++ tailWord_4114738) baseStart_4114738 baseEnd_4114738 := by
    simpa [prefixWord, tailWord_4114738, baseEnd_4114738] using wordTrace_append hprefix tailTrace_4114738
  have hstable : (prefixWord ++ tailWord_4114738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4114738).length < 2 ^ (prefixWord ++ tailWord_4114738).sum := by decide
  have hdescent : baseEnd_4114738 < baseStart_4114738 := by decide
  rcases family_descends (prefixWord ++ tailWord_4114738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4114828 : List Nat := [2, 2, 1, 2, 1, 5, 1, 4, 4]
def baseStart_4114828 : Nat := 118140960795 + 4114828 * 2 ^ 59
def prefixEnd_4114828 : Nat := 4983230072969 + 3 ^ 40 * 4114828 * 2
def baseEnd_4114828 : Nat := 469529905461984877828057

theorem tailTrace_4114828 : CollatzResearch.WordTrace tailWord_4114828 prefixEnd_4114828 469529905461984877828057 := by
  unfold tailWord_4114828
  simp only [CollatzResearch.WordTrace]
  refine ⟨75040053368344193759096569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100053404491125591678795425 75040053368344193759096569)
  ·
    refine ⟨56280040026258145319322427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75040053368344193759096569 56280040026258145319322427)
    ·
      refine ⟨84420060039387217978983641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56280040026258145319322427 84420060039387217978983641)
      ·
        refine ⟨63315045029540413484237731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84420060039387217978983641 63315045029540413484237731)
        ·
          refine ⟨94972567544310620226356597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63315045029540413484237731 94972567544310620226356597)
          ·
            refine ⟨8903678207279120646220931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 94972567544310620226356597 8903678207279120646220931)
            ·
              refine ⟨13355517310918680969331397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8903678207279120646220931 13355517310918680969331397)
              ·
                refine ⟨2504159495797252681749637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13355517310918680969331397 2504159495797252681749637)
                ·
                  refine ⟨469529905461984877828057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2504159495797252681749637 469529905461984877828057)
                  ·
                    rfl

theorem cell22_4114828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 4, 4].length) (baseStart_4114828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4114828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4114828 prefixEnd_4114828 := by exact prefixLift 4114828
  have htrace : WordTrace (prefixWord ++ tailWord_4114828) baseStart_4114828 baseEnd_4114828 := by
    simpa [prefixWord, tailWord_4114828, baseEnd_4114828] using wordTrace_append hprefix tailTrace_4114828
  have hstable : (prefixWord ++ tailWord_4114828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4114828).length < 2 ^ (prefixWord ++ tailWord_4114828).sum := by decide
  have hdescent : baseEnd_4114828 < baseStart_4114828 := by decide
  rcases family_descends (prefixWord ++ tailWord_4114828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4114888 : List Nat := [2, 1, 3, 1, 3, 2, 1, 3, 3, 3]
def baseStart_4114888 : Nat := 118140960795 + 4114888 * 2 ^ 59
def prefixEnd_4114888 : Nat := 4983230072969 + 3 ^ 40 * 4114888 * 2
def baseEnd_4114888 : Nat := 1408610255612134476983987

theorem tailTrace_4114888 : CollatzResearch.WordTrace tailWord_4114888 prefixEnd_4114888 1408610255612134476983987 := by
  unfold tailWord_4114888
  simp only [CollatzResearch.WordTrace]
  refine ⟨75041147558235508882688659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100054863410980678510251545 75041147558235508882688659)
  ·
    refine ⟨112561721337353263324032989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75041147558235508882688659 112561721337353263324032989)
    ·
      refine ⟨42210645501507473746512371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112561721337353263324032989 42210645501507473746512371)
      ·
        refine ⟨63315968252261210619768557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42210645501507473746512371 63315968252261210619768557)
        ·
          refine ⟨23743488094597953982413209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63315968252261210619768557 23743488094597953982413209)
          ·
            refine ⟨17807616070948465486809907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23743488094597953982413209 17807616070948465486809907)
            ·
              refine ⟨26711424106422698230214861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17807616070948465486809907 26711424106422698230214861)
              ·
                refine ⟨10016784039908511836330573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26711424106422698230214861 10016784039908511836330573)
                ·
                  refine ⟨3756294014965691938623965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10016784039908511836330573 3756294014965691938623965)
                  ·
                    refine ⟨1408610255612134476983987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3756294014965691938623965 1408610255612134476983987)
                    ·
                      rfl

theorem cell22_4114888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 3, 3, 3].length) (baseStart_4114888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4114888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4114888 prefixEnd_4114888 := by exact prefixLift 4114888
  have htrace : WordTrace (prefixWord ++ tailWord_4114888) baseStart_4114888 baseEnd_4114888 := by
    simpa [prefixWord, tailWord_4114888, baseEnd_4114888] using wordTrace_append hprefix tailTrace_4114888
  have hstable : (prefixWord ++ tailWord_4114888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4114888).length < 2 ^ (prefixWord ++ tailWord_4114888).sum := by decide
  have hdescent : baseEnd_4114888 < baseStart_4114888 := by decide
  rcases family_descends (prefixWord ++ tailWord_4114888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4114922 : List Nat := [3, 1, 3, 1, 3, 1, 3, 3, 1, 3]
def baseStart_4114922 : Nat := 118140960795 + 4114922 * 2 ^ 59
def prefixEnd_4114922 : Nat := 4983230072969 + 3 ^ 40 * 4114922 * 2
def baseEnd_4114922 : Nat := 1408621894506969721633883

theorem tailTrace_4114922 : CollatzResearch.WordTrace tailWord_4114922 prefixEnd_4114922 1408621894506969721633883 := by
  unfold tailWord_4114922
  simp only [CollatzResearch.WordTrace]
  refine ⟨37520883799586960393028755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100055690132231894381410013 37520883799586960393028755)
  ·
    refine ⟨56281325699380440589543133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37520883799586960393028755 56281325699380440589543133)
    ·
      refine ⟨21105497137267665221078675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56281325699380440589543133 21105497137267665221078675)
      ·
        refine ⟨31658245705901497831618013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21105497137267665221078675 31658245705901497831618013)
        ·
          refine ⟨11871842139713061686856755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31658245705901497831618013 11871842139713061686856755)
          ·
            refine ⟨17807763209569592530285133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11871842139713061686856755 17807763209569592530285133)
            ·
              refine ⟨6677911203588597198856925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17807763209569592530285133 6677911203588597198856925)
              ·
                refine ⟨2504216701345723949571347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6677911203588597198856925 2504216701345723949571347)
                ·
                  refine ⟨3756325052018585924357021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2504216701345723949571347 3756325052018585924357021)
                  ·
                    refine ⟨1408621894506969721633883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3756325052018585924357021 1408621894506969721633883)
                    ·
                      rfl

theorem cell22_4114922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 3, 3, 1, 3].length) (baseStart_4114922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4114922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4114922 prefixEnd_4114922 := by exact prefixLift 4114922
  have htrace : WordTrace (prefixWord ++ tailWord_4114922) baseStart_4114922 baseEnd_4114922 := by
    simpa [prefixWord, tailWord_4114922, baseEnd_4114922] using wordTrace_append hprefix tailTrace_4114922
  have hstable : (prefixWord ++ tailWord_4114922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4114922).length < 2 ^ (prefixWord ++ tailWord_4114922).sum := by decide
  have hdescent : baseEnd_4114922 < baseStart_4114922 := by decide
  rcases family_descends (prefixWord ++ tailWord_4114922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4114993 : List Nat := [1, 2, 2, 3, 1, 1, 4, 2, 2, 4]
def baseStart_4114993 : Nat := 118140960795 + 4114993 * 2 ^ 59
def prefixEnd_4114993 : Nat := 4983230072969 + 3 ^ 40 * 4114993 * 2
def baseEnd_4114993 : Nat := 1408646199257949203108665

theorem tailTrace_4114993 : CollatzResearch.WordTrace tailWord_4114993 prefixEnd_4114993 1408646199257949203108665 := by
  unfold tailWord_4114993
  simp only [CollatzResearch.WordTrace]
  refine ⟨150086124781090620697949633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100057416520727080465299755 150086124781090620697949633)
  ·
    refine ⟨112564593585817965523462225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150086124781090620697949633 112564593585817965523462225)
    ·
      refine ⟨84423445189363474142596669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112564593585817965523462225 84423445189363474142596669)
      ·
        refine ⟨31658791946011302803473751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84423445189363474142596669 31658791946011302803473751)
        ·
          refine ⟨47488187919016954205210627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31658791946011302803473751 47488187919016954205210627)
          ·
            refine ⟨71232281878525431307815941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47488187919016954205210627 71232281878525431307815941)
            ·
              refine ⟨13356052852223518370215489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71232281878525431307815941 13356052852223518370215489)
              ·
                refine ⟨10017039639167638777661617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13356052852223518370215489 10017039639167638777661617)
                ·
                  refine ⟨7512779729375729083246213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10017039639167638777661617 7512779729375729083246213)
                  ·
                    refine ⟨1408646199257949203108665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7512779729375729083246213 1408646199257949203108665)
                    ·
                      rfl

theorem cell22_4114993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 2, 2, 4].length) (baseStart_4114993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4114993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4114993 prefixEnd_4114993 := by exact prefixLift 4114993
  have htrace : WordTrace (prefixWord ++ tailWord_4114993) baseStart_4114993 baseEnd_4114993 := by
    simpa [prefixWord, tailWord_4114993, baseEnd_4114993] using wordTrace_append hprefix tailTrace_4114993
  have hstable : (prefixWord ++ tailWord_4114993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4114993).length < 2 ^ (prefixWord ++ tailWord_4114993).sum := by decide
  have hdescent : baseEnd_4114993 < baseStart_4114993 := by decide
  rcases family_descends (prefixWord ++ tailWord_4114993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4114995 : List Nat := [1, 1, 1, 2, 4, 2, 4, 2, 2, 3]
def baseStart_4114995 : Nat := 118140960795 + 4114995 * 2 ^ 59
def prefixEnd_4114995 : Nat := 4983230072969 + 3 ^ 40 * 4114995 * 2
def baseEnd_4114995 : Nat := 1408646883898821864558659

theorem tailTrace_4114995 : CollatzResearch.WordTrace tailWord_4114995 prefixEnd_4114995 1408646883898821864558659 := by
  unfold tailWord_4114995
  simp only [CollatzResearch.WordTrace]
  refine ⟨150086197727083375039522439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100057465151388916693014959 150086197727083375039522439)
  ·
    refine ⟨225129296590625062559283659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150086197727083375039522439 225129296590625062559283659)
    ·
      refine ⟨337693944885937593838925489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225129296590625062559283659 337693944885937593838925489)
      ·
        refine ⟨253270458664453195379194117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 337693944885937593838925489 253270458664453195379194117)
        ·
          refine ⟨47488210999584974133598897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 253270458664453195379194117 47488210999584974133598897)
          ·
            refine ⟨35616158249688730600199173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47488210999584974133598897 35616158249688730600199173)
            ·
              refine ⟨6678029671816636987537345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35616158249688730600199173 6678029671816636987537345)
              ·
                refine ⟨5008522253862477740653009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6678029671816636987537345 5008522253862477740653009)
                ·
                  refine ⟨3756391690396858305489757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5008522253862477740653009 3756391690396858305489757)
                  ·
                    refine ⟨1408646883898821864558659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3756391690396858305489757 1408646883898821864558659)
                    ·
                      rfl

theorem cell22_4114995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 4, 2, 2, 3].length) (baseStart_4114995 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4114995 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4114995 prefixEnd_4114995 := by exact prefixLift 4114995
  have htrace : WordTrace (prefixWord ++ tailWord_4114995) baseStart_4114995 baseEnd_4114995 := by
    simpa [prefixWord, tailWord_4114995, baseEnd_4114995] using wordTrace_append hprefix tailTrace_4114995
  have hstable : (prefixWord ++ tailWord_4114995).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4114995).length < 2 ^ (prefixWord ++ tailWord_4114995).sum := by decide
  have hdescent : baseEnd_4114995 < baseStart_4114995 := by decide
  rcases family_descends (prefixWord ++ tailWord_4114995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4115023 : List Nat := [1, 1, 2, 1, 1, 2, 5, 1, 5, 3]
def baseStart_4115023 : Nat := 118140960795 + 4115023 * 2 ^ 59
def prefixEnd_4115023 : Nat := 4983230072969 + 3 ^ 40 * 4115023 * 2
def baseEnd_4115023 : Nat := 1408656468871039124858573

theorem tailTrace_4115023 : CollatzResearch.WordTrace tailWord_4115023 prefixEnd_4115023 1408656468871039124858573 := by
  unfold tailWord_4115023
  simp only [CollatzResearch.WordTrace]
  refine ⟨150087218970981935821541723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100058145980654623881027815 150087218970981935821541723)
  ·
    refine ⟨225130828456472903732312585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150087218970981935821541723 225130828456472903732312585)
    ·
      refine ⟨168848121342354677799234439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225130828456472903732312585 168848121342354677799234439)
      ·
        refine ⟨253272182013532016698851659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168848121342354677799234439 253272182013532016698851659)
        ·
          refine ⟨379908273020298025048277489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253272182013532016698851659 379908273020298025048277489)
          ·
            refine ⟨284931204765223518786208117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 379908273020298025048277489 284931204765223518786208117)
            ·
              refine ⟨26712300446739704886207011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 284931204765223518786208117 26712300446739704886207011)
              ·
                refine ⟨40068450670109557329310517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26712300446739704886207011 40068450670109557329310517)
                ·
                  refine ⟨3756417250322770999622861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40068450670109557329310517 3756417250322770999622861)
                  ·
                    refine ⟨1408656468871039124858573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3756417250322770999622861 1408656468871039124858573)
                    ·
                      rfl

theorem cell22_4115023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 1, 5, 3].length) (baseStart_4115023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4115023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4115023 prefixEnd_4115023 := by exact prefixLift 4115023
  have htrace : WordTrace (prefixWord ++ tailWord_4115023) baseStart_4115023 baseEnd_4115023 := by
    simpa [prefixWord, tailWord_4115023, baseEnd_4115023] using wordTrace_append hprefix tailTrace_4115023
  have hstable : (prefixWord ++ tailWord_4115023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4115023).length < 2 ^ (prefixWord ++ tailWord_4115023).sum := by decide
  have hdescent : baseEnd_4115023 < baseStart_4115023 := by decide
  rcases family_descends (prefixWord ++ tailWord_4115023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4115068 : List Nat := [2, 2, 2, 1, 1, 2, 4, 1, 2, 5]
def baseStart_4115068 : Nat := 118140960795 + 4115068 * 2 ^ 59
def prefixEnd_4115068 : Nat := 4983230072969 + 3 ^ 40 * 4115068 * 2
def baseEnd_4115068 : Nat := 1408671873290674007483435

theorem tailTrace_4115068 : CollatzResearch.WordTrace tailWord_4115068 prefixEnd_4115068 1408671873290674007483435 := by
  unfold tailWord_4115068
  simp only [CollatzResearch.WordTrace]
  refine ⟨75044430127909454253464929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100059240170545939004619905 75044430127909454253464929)
  ·
    refine ⟨56283322595932090690098697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75044430127909454253464929 56283322595932090690098697)
    ·
      refine ⟨42212491946949068017574023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56283322595932090690098697 42212491946949068017574023)
      ·
        refine ⟨63318737920423602026361035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42212491946949068017574023 63318737920423602026361035)
        ·
          refine ⟨94978106880635403039541553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63318737920423602026361035 94978106880635403039541553)
          ·
            refine ⟨71233580160476552279656165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94978106880635403039541553 71233580160476552279656165)
            ·
              refine ⟨13356296280089353552435531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71233580160476552279656165 13356296280089353552435531)
              ·
                refine ⟨20034444420134030328653297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13356296280089353552435531 20034444420134030328653297)
                ·
                  refine ⟨15025833315100522746489973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20034444420134030328653297 15025833315100522746489973)
                  ·
                    refine ⟨1408671873290674007483435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15025833315100522746489973 1408671873290674007483435)
                    ·
                      rfl

theorem cell22_4115068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 1, 2, 5].length) (baseStart_4115068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4115068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4115068 prefixEnd_4115068 := by exact prefixLift 4115068
  have htrace : WordTrace (prefixWord ++ tailWord_4115068) baseStart_4115068 baseEnd_4115068 := by
    simpa [prefixWord, tailWord_4115068, baseEnd_4115068] using wordTrace_append hprefix tailTrace_4115068
  have hstable : (prefixWord ++ tailWord_4115068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4115068).length < 2 ^ (prefixWord ++ tailWord_4115068).sum := by decide
  have hdescent : baseEnd_4115068 < baseStart_4115068 := by decide
  rcases family_descends (prefixWord ++ tailWord_4115068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4115121 : List Nat := [1, 2, 2, 6, 2, 1, 2, 1, 5]
def baseStart_4115121 : Nat := 118140960795 + 4115121 * 2 ^ 59
def prefixEnd_4115121 : Nat := 4983230072969 + 3 ^ 40 * 4115121 * 2
def baseEnd_4115121 : Nat := 469563338757933178636091

theorem tailTrace_4115121 : CollatzResearch.WordTrace tailWord_4115121 prefixEnd_4115121 469563338757933178636091 := by
  unfold tailWord_4115121
  simp only [CollatzResearch.WordTrace]
  refine ⟨150090793324626898558609217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100060528883084599039072811 150090793324626898558609217)
  ·
    refine ⟨112568094993470173918956913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150090793324626898558609217 112568094993470173918956913)
    ·
      refine ⟨84426071245102630439217685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112568094993470173918956913 84426071245102630439217685)
      ·
        refine ⟨3957472089614185801838329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 84426071245102630439217685 3957472089614185801838329)
        ·
          refine ⟨2968104067210639351378747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3957472089614185801838329 2968104067210639351378747)
          ·
            refine ⟨4452156100815959027068121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2968104067210639351378747 4452156100815959027068121)
            ·
              refine ⟨3339117075611969270301091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4452156100815959027068121 3339117075611969270301091)
              ·
                refine ⟨5008675613417953905451637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3339117075611969270301091 5008675613417953905451637)
                ·
                  refine ⟨469563338757933178636091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5008675613417953905451637 469563338757933178636091)
                  ·
                    rfl

theorem cell22_4115121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 2, 1, 5].length) (baseStart_4115121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4115121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4115121 prefixEnd_4115121 := by exact prefixLift 4115121
  have htrace : WordTrace (prefixWord ++ tailWord_4115121) baseStart_4115121 baseEnd_4115121 := by
    simpa [prefixWord, tailWord_4115121, baseEnd_4115121] using wordTrace_append hprefix tailTrace_4115121
  have hstable : (prefixWord ++ tailWord_4115121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4115121).length < 2 ^ (prefixWord ++ tailWord_4115121).sum := by decide
  have hdescent : baseEnd_4115121 < baseStart_4115121 := by decide
  rcases family_descends (prefixWord ++ tailWord_4115121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4115164 : List Nat := [2, 2, 5, 1, 1, 1, 1, 4, 2, 3]
def baseStart_4115164 : Nat := 118140960795 + 4115164 * 2 ^ 59
def prefixEnd_4115164 : Nat := 4983230072969 + 3 ^ 40 * 4115164 * 2
def baseEnd_4115164 : Nat := 1408704736052561757083141

theorem tailTrace_4115164 : CollatzResearch.WordTrace tailWord_4115164 prefixEnd_4115164 1408704736052561757083141 := by
  unfold tailWord_4115164
  simp only [CollatzResearch.WordTrace]
  refine ⟨75046180831735558451212273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100061574442314077934949697 75046180831735558451212273)
  ·
    refine ⟨56284635623801668838409205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75046180831735558451212273 56284635623801668838409205)
    ·
      refine ⟨5276684589731406453600863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 56284635623801668838409205 5276684589731406453600863)
      ·
        refine ⟨7915026884597109680401295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5276684589731406453600863 7915026884597109680401295)
        ·
          refine ⟨11872540326895664520601943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7915026884597109680401295 11872540326895664520601943)
          ·
            refine ⟨17808810490343496780902915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11872540326895664520601943 17808810490343496780902915)
            ·
              refine ⟨26713215735515245171354373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17808810490343496780902915 26713215735515245171354373)
              ·
                refine ⟨5008727950409108469628945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26713215735515245171354373 5008727950409108469628945)
                ·
                  refine ⟨3756545962806831352221709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5008727950409108469628945 3756545962806831352221709)
                  ·
                    refine ⟨1408704736052561757083141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3756545962806831352221709 1408704736052561757083141)
                    ·
                      rfl

theorem cell22_4115164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_4115164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4115164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4115164 prefixEnd_4115164 := by exact prefixLift 4115164
  have htrace : WordTrace (prefixWord ++ tailWord_4115164) baseStart_4115164 baseEnd_4115164 := by
    simpa [prefixWord, tailWord_4115164, baseEnd_4115164] using wordTrace_append hprefix tailTrace_4115164
  have hstable : (prefixWord ++ tailWord_4115164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4115164).length < 2 ^ (prefixWord ++ tailWord_4115164).sum := by decide
  have hdescent : baseEnd_4115164 < baseStart_4115164 := by decide
  rcases family_descends (prefixWord ++ tailWord_4115164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4115190 : List Nat := [5, 1, 1, 1, 1, 2, 1, 2, 2, 6]
def baseStart_4115190 : Nat := 118140960795 + 4115190 * 2 ^ 59
def prefixEnd_4115190 : Nat := 4983230072969 + 3 ^ 40 * 4115190 * 2
def baseEnd_4115190 : Nat := 1408713636383906355933061

theorem tailTrace_4115190 : CollatzResearch.WordTrace tailWord_4115190 prefixEnd_4115190 1408713636383906355933061 := by
  unfold tailWord_4115190
  simp only [CollatzResearch.WordTrace]
  refine ⟨9380831872586057708929439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 100062206640917948895247349 9380831872586057708929439)
  ·
    refine ⟨14071247808879086563394159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9380831872586057708929439 14071247808879086563394159)
    ·
      refine ⟨21106871713318629845091239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14071247808879086563394159 21106871713318629845091239)
      ·
        refine ⟨31660307569977944767636859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21106871713318629845091239 31660307569977944767636859)
        ·
          refine ⟨47490461354966917151455289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31660307569977944767636859 47490461354966917151455289)
          ·
            refine ⟨35617846016225187863591467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47490461354966917151455289 35617846016225187863591467)
            ·
              refine ⟨53426769024337781795387201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35617846016225187863591467 53426769024337781795387201)
              ·
                refine ⟨40070076768253336346540401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53426769024337781795387201 40070076768253336346540401)
                ·
                  refine ⟨30052557576190002259905301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40070076768253336346540401 30052557576190002259905301)
                  ·
                    refine ⟨1408713636383906355933061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30052557576190002259905301 1408713636383906355933061)
                    ·
                      rfl

theorem cell22_4115190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 2, 2, 6].length) (baseStart_4115190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4115190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4115190 prefixEnd_4115190 := by exact prefixLift 4115190
  have htrace : WordTrace (prefixWord ++ tailWord_4115190) baseStart_4115190 baseEnd_4115190 := by
    simpa [prefixWord, tailWord_4115190, baseEnd_4115190] using wordTrace_append hprefix tailTrace_4115190
  have hstable : (prefixWord ++ tailWord_4115190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4115190).length < 2 ^ (prefixWord ++ tailWord_4115190).sum := by decide
  have hdescent : baseEnd_4115190 < baseStart_4115190 := by decide
  rcases family_descends (prefixWord ++ tailWord_4115190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4115203 : List Nat := [1, 1, 1, 3, 2, 2, 1, 1, 3, 7]
def baseStart_4115203 : Nat := 118140960795 + 4115203 * 2 ^ 59
def prefixEnd_4115203 : Nat := 4983230072969 + 3 ^ 40 * 4115203 * 2
def baseEnd_4115203 : Nat := 1408718086549578655358021

theorem tailTrace_4115203 : CollatzResearch.WordTrace tailWord_4115203 prefixEnd_4115203 1408718086549578655358021 := by
  unfold tailWord_4115203
  simp only [CollatzResearch.WordTrace]
  refine ⟨150093784110329826563094263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100062522740219884375396175 150093784110329826563094263)
  ·
    refine ⟨225140676165494739844641395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150093784110329826563094263 225140676165494739844641395)
    ·
      refine ⟨337711014248242109766962093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225140676165494739844641395 337711014248242109766962093)
      ·
        refine ⟨126641630343090791162610785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 337711014248242109766962093 126641630343090791162610785)
        ·
          refine ⟨94981222757318093371958089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126641630343090791162610785 94981222757318093371958089)
          ·
            refine ⟨71235917067988570028968567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94981222757318093371958089 71235917067988570028968567)
            ·
              refine ⟨106853875601982855043452851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71235917067988570028968567 106853875601982855043452851)
              ·
                refine ⟨160280813402974282565179277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106853875601982855043452851 160280813402974282565179277)
                ·
                  refine ⟨60105305026115355961942229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 160280813402974282565179277 60105305026115355961942229)
                  ·
                    refine ⟨1408718086549578655358021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60105305026115355961942229 1408718086549578655358021)
                    ·
                      rfl

theorem cell22_4115203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 3, 7].length) (baseStart_4115203 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4115203 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4115203 prefixEnd_4115203 := by exact prefixLift 4115203
  have htrace : WordTrace (prefixWord ++ tailWord_4115203) baseStart_4115203 baseEnd_4115203 := by
    simpa [prefixWord, tailWord_4115203, baseEnd_4115203] using wordTrace_append hprefix tailTrace_4115203
  have hstable : (prefixWord ++ tailWord_4115203).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4115203).length < 2 ^ (prefixWord ++ tailWord_4115203).sum := by decide
  have hdescent : baseEnd_4115203 < baseStart_4115203 := by decide
  rcases family_descends (prefixWord ++ tailWord_4115203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4115250 : List Nat := [3, 2, 1, 1, 3, 1, 1, 4, 6]
def baseStart_4115250 : Nat := 118140960795 + 4115250 * 2 ^ 59
def prefixEnd_4115250 : Nat := 4983230072969 + 3 ^ 40 * 4115250 * 2
def baseEnd_4115250 : Nat := 469578058536695399810959

theorem tailTrace_4115250 : CollatzResearch.WordTrace tailWord_4115250 prefixEnd_4115250 469578058536695399810959 := by
  unfold tailWord_4115250
  simp only [CollatzResearch.WordTrace]
  refine ⟨37523874585289888397513801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100063665560773035726703469 37523874585289888397513801)
  ·
    refine ⟨28142905938967416298135351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37523874585289888397513801 28142905938967416298135351)
    ·
      refine ⟨42214358908451124447203027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28142905938967416298135351 42214358908451124447203027)
      ·
        refine ⟨63321538362676686670804541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42214358908451124447203027 63321538362676686670804541)
        ·
          refine ⟨23745576886003757501551703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63321538362676686670804541 23745576886003757501551703)
          ·
            refine ⟨35618365329005636252327555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23745576886003757501551703 35618365329005636252327555)
            ·
              refine ⟨53427547993508454378491333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35618365329005636252327555 53427547993508454378491333)
              ·
                refine ⟨10017665248782835195967125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53427547993508454378491333 10017665248782835195967125)
                ·
                  refine ⟨469578058536695399810959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10017665248782835195967125 469578058536695399810959)
                  ·
                    rfl

theorem cell22_4115250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 4, 6].length) (baseStart_4115250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4115250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4115250 prefixEnd_4115250 := by exact prefixLift 4115250
  have htrace : WordTrace (prefixWord ++ tailWord_4115250) baseStart_4115250 baseEnd_4115250 := by
    simpa [prefixWord, tailWord_4115250, baseEnd_4115250] using wordTrace_append hprefix tailTrace_4115250
  have hstable : (prefixWord ++ tailWord_4115250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4115250).length < 2 ^ (prefixWord ++ tailWord_4115250).sum := by decide
  have hdescent : baseEnd_4115250 < baseStart_4115250 := by decide
  rcases family_descends (prefixWord ++ tailWord_4115250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4115280 : List Nat := [2, 1, 1, 1, 1, 4, 3, 1, 4, 4]
def baseStart_4115280 : Nat := 118140960795 + 4115280 * 2 ^ 59
def prefixEnd_4115280 : Nat := 4983230072969 + 3 ^ 40 * 4115280 * 2
def baseEnd_4115280 : Nat := 1408744445223176121182785

theorem tailTrace_4115280 : CollatzResearch.WordTrace tailWord_4115280 prefixEnd_4115280 1408744445223176121182785 := by
  unfold tailWord_4115280
  simp only [CollatzResearch.WordTrace]
  refine ⟨75048296265525434356823647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100064395020700579142431529 75048296265525434356823647)
  ·
    refine ⟨112572444398288151535235471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75048296265525434356823647 112572444398288151535235471)
    ·
      refine ⟨168858666597432227302853207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112572444398288151535235471 168858666597432227302853207)
      ·
        refine ⟨253287999896148340954279811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168858666597432227302853207 253287999896148340954279811)
        ·
          refine ⟨379931999844222511431419717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253287999896148340954279811 379931999844222511431419717)
          ·
            refine ⟨71237249970791720893391197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 379931999844222511431419717 71237249970791720893391197)
            ·
              refine ⟨26713968739046895335021699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71237249970791720893391197 26713968739046895335021699)
              ·
                refine ⟨40070953108570343002532549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26713968739046895335021699 40070953108570343002532549)
                ·
                  refine ⟨7513303707856939312974853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40070953108570343002532549 7513303707856939312974853)
                  ·
                    refine ⟨1408744445223176121182785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7513303707856939312974853 1408744445223176121182785)
                    ·
                      rfl

theorem cell22_4115280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 1, 4, 4].length) (baseStart_4115280 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4115280 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4115280 prefixEnd_4115280 := by exact prefixLift 4115280
  have htrace : WordTrace (prefixWord ++ tailWord_4115280) baseStart_4115280 baseEnd_4115280 := by
    simpa [prefixWord, tailWord_4115280, baseEnd_4115280] using wordTrace_append hprefix tailTrace_4115280
  have hstable : (prefixWord ++ tailWord_4115280).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4115280).length < 2 ^ (prefixWord ++ tailWord_4115280).sum := by decide
  have hdescent : baseEnd_4115280 < baseStart_4115280 := by decide
  rcases family_descends (prefixWord ++ tailWord_4115280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4115282 : List Nat := [3, 2, 2, 1, 1, 2, 1, 3, 4, 3]
def baseStart_4115282 : Nat := 118140960795 + 4115282 * 2 ^ 59
def prefixEnd_4115282 : Nat := 4983230072969 + 3 ^ 40 * 4115282 * 2
def baseEnd_4115282 : Nat := 1408745129864048782632779

theorem tailTrace_4115282 : CollatzResearch.WordTrace tailWord_4115282 prefixEnd_4115282 1408745129864048782632779 := by
  unfold tailWord_4115282
  simp only [CollatzResearch.WordTrace]
  refine ⟨37524166369260905763805025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100064443651362415370146733 37524166369260905763805025)
  ·
    refine ⟨28143124776945679322853769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37524166369260905763805025 28143124776945679322853769)
    ·
      refine ⟨21107343582709259492140327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28143124776945679322853769 21107343582709259492140327)
      ·
        refine ⟨31661015374063889238210491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21107343582709259492140327 31661015374063889238210491)
        ·
          refine ⟨47491523061095833857315737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31661015374063889238210491 47491523061095833857315737)
          ·
            refine ⟨35618642295821875392986803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47491523061095833857315737 35618642295821875392986803)
            ·
              refine ⟨53427963443732813089480205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35618642295821875392986803 53427963443732813089480205)
              ·
                refine ⟨20035486291399804908555077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53427963443732813089480205 20035486291399804908555077)
                ·
                  refine ⟨3756653679637463420354077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20035486291399804908555077 3756653679637463420354077)
                  ·
                    refine ⟨1408745129864048782632779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3756653679637463420354077 1408745129864048782632779)
                    ·
                      rfl

theorem cell22_4115282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 3, 4, 3].length) (baseStart_4115282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4115282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4115282 prefixEnd_4115282 := by exact prefixLift 4115282
  have htrace : WordTrace (prefixWord ++ tailWord_4115282) baseStart_4115282 baseEnd_4115282 := by
    simpa [prefixWord, tailWord_4115282, baseEnd_4115282] using wordTrace_append hprefix tailTrace_4115282
  have hstable : (prefixWord ++ tailWord_4115282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4115282).length < 2 ^ (prefixWord ++ tailWord_4115282).sum := by decide
  have hdescent : baseEnd_4115282 < baseStart_4115282 := by decide
  rcases family_descends (prefixWord ++ tailWord_4115282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4115284 : List Nat := [2, 4, 1, 1, 4, 2, 1, 1, 6]
def baseStart_4115284 : Nat := 118140960795 + 4115284 * 2 ^ 59
def prefixEnd_4115284 : Nat := 4983230072969 + 3 ^ 40 * 4115284 * 2
def baseEnd_4115284 : Nat := 469581938168307148027591

theorem tailTrace_4115284 : CollatzResearch.WordTrace tailWord_4115284 prefixEnd_4115284 469581938168307148027591 := by
  unfold tailWord_4115284
  simp only [CollatzResearch.WordTrace]
  refine ⟨75048369211518188698396453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100064492282024251597861937 75048369211518188698396453)
  ·
    refine ⟨14071569227159660380949335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75048369211518188698396453 14071569227159660380949335)
    ·
      refine ⟨21107353840739490571424003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14071569227159660380949335 21107353840739490571424003)
      ·
        refine ⟨31661030761109235857136005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21107353840739490571424003 31661030761109235857136005)
        ·
          refine ⟨5936443267707981723213001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31661030761109235857136005 5936443267707981723213001)
          ·
            refine ⟨4452332450780986292409751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5936443267707981723213001 4452332450780986292409751)
            ·
              refine ⟨6678498676171479438614627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4452332450780986292409751 6678498676171479438614627)
              ·
                refine ⟨10017748014257219157921941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6678498676171479438614627 10017748014257219157921941)
                ·
                  refine ⟨469581938168307148027591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10017748014257219157921941 469581938168307148027591)
                  ·
                    rfl

theorem cell22_4115284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 1, 1, 6].length) (baseStart_4115284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4115284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4115284 prefixEnd_4115284 := by exact prefixLift 4115284
  have htrace : WordTrace (prefixWord ++ tailWord_4115284) baseStart_4115284 baseEnd_4115284 := by
    simpa [prefixWord, tailWord_4115284, baseEnd_4115284] using wordTrace_append hprefix tailTrace_4115284
  have hstable : (prefixWord ++ tailWord_4115284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4115284).length < 2 ^ (prefixWord ++ tailWord_4115284).sum := by decide
  have hdescent : baseEnd_4115284 < baseStart_4115284 := by decide
  rcases family_descends (prefixWord ++ tailWord_4115284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4115295 : List Nat := [1, 1, 2, 3, 1, 3, 4, 7]
def baseStart_4115295 : Nat := 118140960795 + 4115295 * 2 ^ 59
def prefixEnd_4115295 : Nat := 4983230072969 + 3 ^ 40 * 4115295 * 2
def baseEnd_4115295 : Nat := 156527731114413453561971

theorem tailTrace_4115295 : CollatzResearch.WordTrace tailWord_4115295 prefixEnd_4115295 156527731114413453561971 := by
  unfold tailWord_4115295
  simp only [CollatzResearch.WordTrace]
  refine ⟨150097139625996526275443339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100064759750664350850295559 150097139625996526275443339)
  ·
    refine ⟨225145709438994789413165009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150097139625996526275443339 225145709438994789413165009)
    ·
      refine ⟨168859282079246092059873757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225145709438994789413165009 168859282079246092059873757)
      ·
        refine ⟨63322230779717284522452659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168859282079246092059873757 63322230779717284522452659)
        ·
          refine ⟨94983346169575926783678989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63322230779717284522452659 94983346169575926783678989)
          ·
            refine ⟨35618754813590972543879621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94983346169575926783678989 35618754813590972543879621)
            ·
              refine ⟨6678516527548307351977429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35618754813590972543879621 6678516527548307351977429)
              ·
                refine ⟨156527731114413453561971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6678516527548307351977429 156527731114413453561971)
                ·
                  rfl

theorem cell22_4115295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 4, 7].length) (baseStart_4115295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4115295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4115295 prefixEnd_4115295 := by exact prefixLift 4115295
  have htrace : WordTrace (prefixWord ++ tailWord_4115295) baseStart_4115295 baseEnd_4115295 := by
    simpa [prefixWord, tailWord_4115295, baseEnd_4115295] using wordTrace_append hprefix tailTrace_4115295
  have hstable : (prefixWord ++ tailWord_4115295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4115295).length < 2 ^ (prefixWord ++ tailWord_4115295).sum := by decide
  have hdescent : baseEnd_4115295 < baseStart_4115295 := by decide
  rcases family_descends (prefixWord ++ tailWord_4115295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4115299 : List Nat := [1, 1, 1, 5, 3, 2, 1, 3, 2, 3]
def baseStart_4115299 : Nat := 118140960795 + 4115299 * 2 ^ 59
def prefixEnd_4115299 : Nat := 4983230072969 + 3 ^ 40 * 4115299 * 2
def baseEnd_4115299 : Nat := 1408750949311466404957727

theorem tailTrace_4115299 : CollatzResearch.WordTrace tailWord_4115299 prefixEnd_4115299 1408750949311466404957727 := by
  unfold tailWord_4115299
  simp only [CollatzResearch.WordTrace]
  refine ⟨150097285517982034958588951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100064857011988023305725967 150097285517982034958588951)
  ·
    refine ⟨225145928276973052437883427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150097285517982034958588951 225145928276973052437883427)
    ·
      refine ⟨337718892415459578656825141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225145928276973052437883427 337718892415459578656825141)
      ·
        refine ⟨31661146163949335499077357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 337718892415459578656825141 31661146163949335499077357)
        ·
          refine ⟨11872929811481000812154009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31661146163949335499077357 11872929811481000812154009)
          ·
            refine ⟨8904697358610750609115507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11872929811481000812154009 8904697358610750609115507)
            ·
              refine ⟨13357046037916125913673261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8904697358610750609115507 13357046037916125913673261)
              ·
                refine ⟨5008892264218547217627473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13357046037916125913673261 5008892264218547217627473)
                ·
                  refine ⟨3756669198163910413220605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5008892264218547217627473 3756669198163910413220605)
                  ·
                    refine ⟨1408750949311466404957727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3756669198163910413220605 1408750949311466404957727)
                    ·
                      rfl

theorem cell22_4115299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 3, 2, 3].length) (baseStart_4115299 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4115299 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4115299 prefixEnd_4115299 := by exact prefixLift 4115299
  have htrace : WordTrace (prefixWord ++ tailWord_4115299) baseStart_4115299 baseEnd_4115299 := by
    simpa [prefixWord, tailWord_4115299, baseEnd_4115299] using wordTrace_append hprefix tailTrace_4115299
  have hstable : (prefixWord ++ tailWord_4115299).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4115299).length < 2 ^ (prefixWord ++ tailWord_4115299).sum := by decide
  have hdescent : baseEnd_4115299 < baseStart_4115299 := by decide
  rcases family_descends (prefixWord ++ tailWord_4115299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4115340 : List Nat := [2, 2, 1, 2, 1, 2, 2, 3, 7]
def baseStart_4115340 : Nat := 118140960795 + 4115340 * 2 ^ 59
def prefixEnd_4115340 : Nat := 4983230072969 + 3 ^ 40 * 4115340 * 2
def baseEnd_4115340 : Nat := 469588328149785321560867

theorem tailTrace_4115340 : CollatzResearch.WordTrace tailWord_4115340 prefixEnd_4115340 469588328149785321560867 := by
  unfold tailWord_4115340
  simp only [CollatzResearch.WordTrace]
  refine ⟨75049390455416749480415737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100065853940555665973887649 75049390455416749480415737)
  ·
    refine ⟨56287042841562562110311803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75049390455416749480415737 56287042841562562110311803)
    ·
      refine ⟨84430564262343843165467705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56287042841562562110311803 84430564262343843165467705)
      ·
        refine ⟨63322923196757882374100779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84430564262343843165467705 63322923196757882374100779)
        ·
          refine ⟨94984384795136823561151169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63322923196757882374100779 94984384795136823561151169)
          ·
            refine ⟨71238288596352617670863377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94984384795136823561151169 71238288596352617670863377)
            ·
              refine ⟨53428716447264463253147533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71238288596352617670863377 53428716447264463253147533)
              ·
                refine ⟨20035768667724173719930325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53428716447264463253147533 20035768667724173719930325)
                ·
                  refine ⟨469588328149785321560867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20035768667724173719930325 469588328149785321560867)
                  ·
                    rfl

theorem cell22_4115340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 3, 7].length) (baseStart_4115340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4115340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4115340 prefixEnd_4115340 := by exact prefixLift 4115340
  have htrace : WordTrace (prefixWord ++ tailWord_4115340) baseStart_4115340 baseEnd_4115340 := by
    simpa [prefixWord, tailWord_4115340, baseEnd_4115340] using wordTrace_append hprefix tailTrace_4115340
  have hstable : (prefixWord ++ tailWord_4115340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4115340).length < 2 ^ (prefixWord ++ tailWord_4115340).sum := by decide
  have hdescent : baseEnd_4115340 < baseStart_4115340 := by decide
  rcases family_descends (prefixWord ++ tailWord_4115340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4115346 : List Nat := [3, 2, 3, 2, 3, 1, 1, 7]
def baseStart_4115346 : Nat := 118140960795 + 4115346 * 2 ^ 59
def prefixEnd_4115346 : Nat := 4983230072969 + 3 ^ 40 * 4115346 * 2
def baseEnd_4115346 : Nat := 156529670930219327670287

theorem tailTrace_4115346 : CollatzResearch.WordTrace tailWord_4115346 prefixEnd_4115346 156529670930219327670287 := by
  unfold tailWord_4115346
  simp only [CollatzResearch.WordTrace]
  refine ⟨37524749937202940496387473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100065999832541174657033261 37524749937202940496387473)
  ·
    refine ⟨28143562452902205372290605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37524749937202940496387473 28143562452902205372290605)
    ·
      refine ⟨10553835919838327014608977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28143562452902205372290605 10553835919838327014608977)
      ·
        refine ⟨7915376939878745260956733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10553835919838327014608977 7915376939878745260956733)
        ·
          refine ⟨2968266352454529472858775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7915376939878745260956733 2968266352454529472858775)
          ·
            refine ⟨4452399528681794209288163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2968266352454529472858775 4452399528681794209288163)
            ·
              refine ⟨6678599293022691313932245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4452399528681794209288163 6678599293022691313932245)
              ·
                refine ⟨156529670930219327670287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6678599293022691313932245 156529670930219327670287)
                ·
                  rfl

theorem cell22_4115346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 1, 7].length) (baseStart_4115346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4115346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4115346 prefixEnd_4115346 := by exact prefixLift 4115346
  have htrace : WordTrace (prefixWord ++ tailWord_4115346) baseStart_4115346 baseEnd_4115346 := by
    simpa [prefixWord, tailWord_4115346, baseEnd_4115346] using wordTrace_append hprefix tailTrace_4115346
  have hstable : (prefixWord ++ tailWord_4115346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4115346).length < 2 ^ (prefixWord ++ tailWord_4115346).sum := by decide
  have hdescent : baseEnd_4115346 < baseStart_4115346 := by decide
  rcases family_descends (prefixWord ++ tailWord_4115346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4115357 : List Nat := [1, 4, 2, 1, 2, 1, 1, 5, 5]
def baseStart_4115357 : Nat := 118140960795 + 4115357 * 2 ^ 59
def prefixEnd_4115357 : Nat := 4983230072969 + 3 ^ 40 * 4115357 * 2
def baseEnd_4115357 : Nat := 469590267965591195669183

theorem tailTrace_4115357 : CollatzResearch.WordTrace tailWord_4115357 prefixEnd_4115357 469590267965591195669183 := by
  unfold tailWord_4115357
  simp only [CollatzResearch.WordTrace]
  refine ⟨150099400951771910864200325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100066267301181273909466883 150099400951771910864200325)
  ·
    refine ⟨28143637678457233287037561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 150099400951771910864200325 28143637678457233287037561)
    ·
      refine ⟨21107728258842924965278171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28143637678457233287037561 21107728258842924965278171)
      ·
        refine ⟨31661592388264387447917257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21107728258842924965278171 31661592388264387447917257)
        ·
          refine ⟨23746194291198290585937943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31661592388264387447917257 23746194291198290585937943)
          ·
            refine ⟨35619291436797435878906915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23746194291198290585937943 35619291436797435878906915)
            ·
              refine ⟨53428937155196153818360373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35619291436797435878906915 53428937155196153818360373)
              ·
                refine ⟨5008962858299639420471285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53428937155196153818360373 5008962858299639420471285)
                ·
                  refine ⟨469590267965591195669183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5008962858299639420471285 469590267965591195669183)
                  ·
                    rfl

theorem cell22_4115357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 5, 5].length) (baseStart_4115357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4115357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4115357 prefixEnd_4115357 := by exact prefixLift 4115357
  have htrace : WordTrace (prefixWord ++ tailWord_4115357) baseStart_4115357 baseEnd_4115357 := by
    simpa [prefixWord, tailWord_4115357, baseEnd_4115357] using wordTrace_append hprefix tailTrace_4115357
  have hstable : (prefixWord ++ tailWord_4115357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4115357).length < 2 ^ (prefixWord ++ tailWord_4115357).sum := by decide
  have hdescent : baseEnd_4115357 < baseStart_4115357 := by decide
  rcases family_descends (prefixWord ++ tailWord_4115357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4115421 : List Nat := [1, 4, 3, 1, 2, 2, 2, 2, 1, 4]
def baseStart_4115421 : Nat := 118140960795 + 4115421 * 2 ^ 59
def prefixEnd_4115421 : Nat := 4983230072969 + 3 ^ 40 * 4115421 * 2
def baseEnd_4115421 : Nat := 1408792712404698753407353

theorem tailTrace_4115421 : CollatzResearch.WordTrace tailWord_4115421 prefixEnd_4115421 1408792712404698753407353 := by
  unfold tailWord_4115421
  simp only [CollatzResearch.WordTrace]
  refine ⟨150101735223540049794530117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100067823482360033196353411 150101735223540049794530117)
  ·
    refine ⟨28144075354413759336474397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 150101735223540049794530117 28144075354413759336474397)
    ·
      refine ⟨10554028257905159751177899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28144075354413759336474397 10554028257905159751177899)
      ·
        refine ⟨15831042386857739626766849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10554028257905159751177899 15831042386857739626766849)
        ·
          refine ⟨11873281790143304720075137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15831042386857739626766849 11873281790143304720075137)
          ·
            refine ⟨8904961342607478540056353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11873281790143304720075137 8904961342607478540056353)
            ·
              refine ⟨6678721006955608905042265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8904961342607478540056353 6678721006955608905042265)
              ·
                refine ⟨5009040755216706678781699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6678721006955608905042265 5009040755216706678781699)
                ·
                  refine ⟨7513561132825060018172549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5009040755216706678781699 7513561132825060018172549)
                  ·
                    refine ⟨1408792712404698753407353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7513561132825060018172549 1408792712404698753407353)
                    ·
                      rfl

theorem cell22_4115421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_4115421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4115421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4115421 prefixEnd_4115421 := by exact prefixLift 4115421
  have htrace : WordTrace (prefixWord ++ tailWord_4115421) baseStart_4115421 baseEnd_4115421 := by
    simpa [prefixWord, tailWord_4115421, baseEnd_4115421] using wordTrace_append hprefix tailTrace_4115421
  have hstable : (prefixWord ++ tailWord_4115421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4115421).length < 2 ^ (prefixWord ++ tailWord_4115421).sum := by decide
  have hdescent : baseEnd_4115421 < baseStart_4115421 := by decide
  rcases family_descends (prefixWord ++ tailWord_4115421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4115432 : List Nat := [2, 1, 4, 1, 1, 1, 4, 1, 1, 6]
def baseStart_4115432 : Nat := 118140960795 + 4115432 * 2 ^ 59
def prefixEnd_4115432 : Nat := 4983230072969 + 3 ^ 40 * 4115432 * 2
def baseEnd_4115432 : Nat := 1408796477929498391382319

theorem tailTrace_4115432 : CollatzResearch.WordTrace tailWord_4115432 prefixEnd_4115432 1408796477929498391382319 := by
  unfold tailWord_4115432
  simp only [CollatzResearch.WordTrace]
  refine ⟨75051068213250099336590275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100068090951000132448787033 75051068213250099336590275)
  ·
    refine ⟨112576602319875149004885413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75051068213250099336590275 112576602319875149004885413)
    ·
      refine ⟨21108112934976590438416015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112576602319875149004885413 21108112934976590438416015)
      ·
        refine ⟨31662169402464885657624023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21108112934976590438416015 31662169402464885657624023)
        ·
          refine ⟨47493254103697328486436035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31662169402464885657624023 47493254103697328486436035)
          ·
            refine ⟨71239881155545992729654053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47493254103697328486436035 71239881155545992729654053)
            ·
              refine ⟨13357477716664873636810135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71239881155545992729654053 13357477716664873636810135)
              ·
                refine ⟨20036216574997310455215203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13357477716664873636810135 20036216574997310455215203)
                ·
                  refine ⟨30054324862495965682822805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20036216574997310455215203 30054324862495965682822805)
                  ·
                    refine ⟨1408796477929498391382319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30054324862495965682822805 1408796477929498391382319)
                    ·
                      rfl

theorem cell22_4115432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 1, 1, 6].length) (baseStart_4115432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4115432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4115432 prefixEnd_4115432 := by exact prefixLift 4115432
  have htrace : WordTrace (prefixWord ++ tailWord_4115432) baseStart_4115432 baseEnd_4115432 := by
    simpa [prefixWord, tailWord_4115432, baseEnd_4115432] using wordTrace_append hprefix tailTrace_4115432
  have hstable : (prefixWord ++ tailWord_4115432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4115432).length < 2 ^ (prefixWord ++ tailWord_4115432).sum := by decide
  have hdescent : baseEnd_4115432 < baseStart_4115432 := by decide
  rcases family_descends (prefixWord ++ tailWord_4115432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4115434 : List Nat := [3, 1, 3, 1, 2, 2, 1, 2, 4, 3]
def baseStart_4115434 : Nat := 118140960795 + 4115434 * 2 ^ 59
def prefixEnd_4115434 : Nat := 4983230072969 + 3 ^ 40 * 4115434 * 2
def baseEnd_4115434 : Nat := 1408797162570371052832313

theorem tailTrace_4115434 : CollatzResearch.WordTrace tailWord_4115434 prefixEnd_4115434 1408797162570371052832313 := by
  unfold tailWord_4115434
  simp only [CollatzResearch.WordTrace]
  refine ⟨37525552343123238253688339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100068139581661968676502237 37525552343123238253688339)
  ·
    refine ⟨56288328514684857380532509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37525552343123238253688339 56288328514684857380532509)
    ·
      refine ⟨21108123193006821517699691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56288328514684857380532509 21108123193006821517699691)
      ·
        refine ⟨31662184789510232276549537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21108123193006821517699691 31662184789510232276549537)
        ·
          refine ⟨23746638592132674207412153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31662184789510232276549537 23746638592132674207412153)
          ·
            refine ⟨17809978944099505655559115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23746638592132674207412153 17809978944099505655559115)
            ·
              refine ⟨26714968416149258483338673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17809978944099505655559115 26714968416149258483338673)
              ·
                refine ⟨20036226312111943862504005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26714968416149258483338673 20036226312111943862504005)
                ·
                  refine ⟨3756792433520989474219501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20036226312111943862504005 3756792433520989474219501)
                  ·
                    refine ⟨1408797162570371052832313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3756792433520989474219501 1408797162570371052832313)
                    ·
                      rfl

theorem cell22_4115434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 2, 4, 3].length) (baseStart_4115434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4115434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4115434 prefixEnd_4115434 := by exact prefixLift 4115434
  have htrace : WordTrace (prefixWord ++ tailWord_4115434) baseStart_4115434 baseEnd_4115434 := by
    simpa [prefixWord, tailWord_4115434, baseEnd_4115434] using wordTrace_append hprefix tailTrace_4115434
  have hstable : (prefixWord ++ tailWord_4115434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4115434).length < 2 ^ (prefixWord ++ tailWord_4115434).sum := by decide
  have hdescent : baseEnd_4115434 < baseStart_4115434 := by decide
  rcases family_descends (prefixWord ++ tailWord_4115434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4115468 : List Nat := [2, 2, 1, 2, 3, 4, 2, 1, 2, 3]
def baseStart_4115468 : Nat := 118140960795 + 4115468 * 2 ^ 59
def prefixEnd_4115468 : Nat := 4983230072969 + 3 ^ 40 * 4115468 * 2
def baseEnd_4115468 : Nat := 1408808801465206297482209

theorem tailTrace_4115468 : CollatzResearch.WordTrace tailWord_4115468 prefixEnd_4115468 1408808801465206297482209 := by
  unfold tailWord_4115468
  simp only [CollatzResearch.WordTrace]
  refine ⟨75051724727184888410745529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100068966302913184547660705 75051724727184888410745529)
  ·
    refine ⟨56288793545388666308059147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75051724727184888410745529 56288793545388666308059147)
    ·
      refine ⟨84433190318082999462088721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56288793545388666308059147 84433190318082999462088721)
      ·
        refine ⟨63324892738562249596566541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84433190318082999462088721 63324892738562249596566541)
        ·
          refine ⟨23746834776960843598712453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63324892738562249596566541 23746834776960843598712453)
          ·
            refine ⟨4452531520680158174758585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23746834776960843598712453 4452531520680158174758585)
            ·
              refine ⟨3339398640510118631068939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4452531520680158174758585 3339398640510118631068939)
              ·
                refine ⟨5009097960765177946603409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3339398640510118631068939 5009097960765177946603409)
                ·
                  refine ⟨3756823470573883459952557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5009097960765177946603409 3756823470573883459952557)
                  ·
                    refine ⟨1408808801465206297482209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3756823470573883459952557 1408808801465206297482209)
                    ·
                      rfl

theorem cell22_4115468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 2, 1, 2, 3].length) (baseStart_4115468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4115468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4115468 prefixEnd_4115468 := by exact prefixLift 4115468
  have htrace : WordTrace (prefixWord ++ tailWord_4115468) baseStart_4115468 baseEnd_4115468 := by
    simpa [prefixWord, tailWord_4115468, baseEnd_4115468] using wordTrace_append hprefix tailTrace_4115468
  have hstable : (prefixWord ++ tailWord_4115468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4115468).length < 2 ^ (prefixWord ++ tailWord_4115468).sum := by decide
  have hdescent : baseEnd_4115468 < baseStart_4115468 := by decide
  rcases family_descends (prefixWord ++ tailWord_4115468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4115507 : List Nat := [1, 1, 1, 2, 4, 1, 1, 4, 2, 5]
def baseStart_4115507 : Nat := 118140960795 + 4115507 * 2 ^ 59
def prefixEnd_4115507 : Nat := 4983230072969 + 3 ^ 40 * 4115507 * 2
def baseEnd_4115507 : Nat := 1408822151962223195757089

theorem tailTrace_4115507 : CollatzResearch.WordTrace tailWord_4115507 prefixEnd_4115507 1408822151962223195757089 := by
  unfold tailWord_4115507
  simp only [CollatzResearch.WordTrace]
  refine ⟨150104871901228486482160775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100069914600818990988107183 150104871901228486482160775)
  ·
    refine ⟨225157307851842729723241163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150104871901228486482160775 225157307851842729723241163)
    ·
      refine ⟨337735961777764094584861745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225157307851842729723241163 337735961777764094584861745)
      ·
        refine ⟨253301971333323070938646309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 337735961777764094584861745 253301971333323070938646309)
        ·
          refine ⟨47494119624998075800996183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 253301971333323070938646309 47494119624998075800996183)
          ·
            refine ⟨71241179437497113701494275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47494119624998075800996183 71241179437497113701494275)
            ·
              refine ⟨106861769156245670552241413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71241179437497113701494275 106861769156245670552241413)
              ·
                refine ⟨20036581716796063228545265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106861769156245670552241413 20036581716796063228545265)
                ·
                  refine ⟨15027436287597047421408949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20036581716796063228545265 15027436287597047421408949)
                  ·
                    refine ⟨1408822151962223195757089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15027436287597047421408949 1408822151962223195757089)
                    ·
                      rfl

theorem cell22_4115507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 4, 2, 5].length) (baseStart_4115507 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4115507 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4115507 prefixEnd_4115507 := by exact prefixLift 4115507
  have htrace : WordTrace (prefixWord ++ tailWord_4115507) baseStart_4115507 baseEnd_4115507 := by
    simpa [prefixWord, tailWord_4115507, baseEnd_4115507] using wordTrace_append hprefix tailTrace_4115507
  have hstable : (prefixWord ++ tailWord_4115507).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4115507).length < 2 ^ (prefixWord ++ tailWord_4115507).sum := by decide
  have hdescent : baseEnd_4115507 < baseStart_4115507 := by decide
  rcases family_descends (prefixWord ++ tailWord_4115507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4115513 : List Nat := [1, 2, 1, 5, 2, 2, 1, 4, 1, 3]
def baseStart_4115513 : Nat := 118140960795 + 4115513 * 2 ^ 59
def prefixEnd_4115513 : Nat := 4983230072969 + 3 ^ 40 * 4115513 * 2
def baseEnd_4115513 : Nat := 1408824205884841180107071

theorem tailTrace_4115513 : CollatzResearch.WordTrace tailWord_4115513 prefixEnd_4115513 1408824205884841180107071 := by
  unfold tailWord_4115513
  simp only [CollatzResearch.WordTrace]
  refine ⟨150105090739206749506879193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100070060492804499671252795 150105090739206749506879193)
  ·
    refine ⟨112578818054405062130159395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150105090739206749506879193 112578818054405062130159395)
    ·
      refine ⟨168868227081607593195239093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112578818054405062130159395 168868227081607593195239093)
      ·
        refine ⟨15831396288900711862053665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 168868227081607593195239093 15831396288900711862053665)
        ·
          refine ⟨11873547216675533896540249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15831396288900711862053665 11873547216675533896540249)
          ·
            refine ⟨8905160412506650422405187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11873547216675533896540249 8905160412506650422405187)
            ·
              refine ⟨13357740618759975633607781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8905160412506650422405187 13357740618759975633607781)
              ·
                refine ⟨2504576366017495431301459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13357740618759975633607781 2504576366017495431301459)
                ·
                  refine ⟨3756864549026243146952189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2504576366017495431301459 3756864549026243146952189)
                  ·
                    refine ⟨1408824205884841180107071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3756864549026243146952189 1408824205884841180107071)
                    ·
                      rfl

theorem cell22_4115513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 4, 1, 3].length) (baseStart_4115513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4115513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4115513 prefixEnd_4115513 := by exact prefixLift 4115513
  have htrace : WordTrace (prefixWord ++ tailWord_4115513) baseStart_4115513 baseEnd_4115513 := by
    simpa [prefixWord, tailWord_4115513, baseEnd_4115513] using wordTrace_append hprefix tailTrace_4115513
  have hstable : (prefixWord ++ tailWord_4115513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4115513).length < 2 ^ (prefixWord ++ tailWord_4115513).sum := by decide
  have hdescent : baseEnd_4115513 < baseStart_4115513 := by decide
  rcases family_descends (prefixWord ++ tailWord_4115513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4115537 : List Nat := [1, 2, 2, 1, 3, 1, 3, 1, 8]
def baseStart_4115537 : Nat := 118140960795 + 4115537 * 2 ^ 59
def prefixEnd_4115537 : Nat := 4983230072969 + 3 ^ 40 * 4115537 * 2
def baseEnd_4115537 : Nat := 469610807191771039168999

theorem tailTrace_4115537 : CollatzResearch.WordTrace tailWord_4115537 prefixEnd_4115537 469610807191771039168999 := by
  unfold tailWord_4115537
  simp only [CollatzResearch.WordTrace]
  refine ⟨150105966091119801605752865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100070644060746534403835243 150105966091119801605752865)
  ·
    refine ⟨112579474568339851204314649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150105966091119801605752865 112579474568339851204314649)
    ·
      refine ⟨84434605926254888403235987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112579474568339851204314649 84434605926254888403235987)
      ·
        refine ⟨126651908889382332604853981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84434605926254888403235987 126651908889382332604853981)
        ·
          refine ⟨47494465833518374726820243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126651908889382332604853981 47494465833518374726820243)
          ·
            refine ⟨71241698750277562090230365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47494465833518374726820243 71241698750277562090230365)
            ·
              refine ⟨26715637031354085783836387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71241698750277562090230365 26715637031354085783836387)
              ·
                refine ⟨40073455547031128675754581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26715637031354085783836387 40073455547031128675754581)
                ·
                  refine ⟨469610807191771039168999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40073455547031128675754581 469610807191771039168999)
                  ·
                    rfl

theorem cell22_4115537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 1, 8].length) (baseStart_4115537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4115537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4115537 prefixEnd_4115537 := by exact prefixLift 4115537
  have htrace : WordTrace (prefixWord ++ tailWord_4115537) baseStart_4115537 baseEnd_4115537 := by
    simpa [prefixWord, tailWord_4115537, baseEnd_4115537] using wordTrace_append hprefix tailTrace_4115537
  have hstable : (prefixWord ++ tailWord_4115537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4115537).length < 2 ^ (prefixWord ++ tailWord_4115537).sum := by decide
  have hdescent : baseEnd_4115537 < baseStart_4115537 := by decide
  rcases family_descends (prefixWord ++ tailWord_4115537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4115560 : List Nat := [2, 1, 4, 4, 2, 1, 1, 2, 5]
def baseStart_4115560 : Nat := 118140960795 + 4115560 * 2 ^ 59
def prefixEnd_4115560 : Nat := 4983230072969 + 3 ^ 40 * 4115560 * 2
def baseEnd_4115560 : Nat := 469613431648449574727309

theorem tailTrace_4115560 : CollatzResearch.WordTrace tailWord_4115560 prefixEnd_4115560 469613431648449574727309 := by
  unfold tailWord_4115560
  simp only [CollatzResearch.WordTrace]
  refine ⟨75053402485018238266920067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100071203313357651022560089 75053402485018238266920067)
  ·
    refine ⟨112580103727527357400380101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75053402485018238266920067 112580103727527357400380101)
    ·
      refine ⟨21108769448911379512571269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112580103727527357400380101 21108769448911379512571269)
      ·
        refine ⟨3957894271670883658607113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21108769448911379512571269 3957894271670883658607113)
        ·
          refine ⟨2968420703753162743955335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3957894271670883658607113 2968420703753162743955335)
          ·
            refine ⟨4452631055629744115933003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2968420703753162743955335 4452631055629744115933003)
            ·
              refine ⟨6678946583444616173899505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4452631055629744115933003 6678946583444616173899505)
              ·
                refine ⟨5009209937583462130424629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6678946583444616173899505 5009209937583462130424629)
                ·
                  refine ⟨469613431648449574727309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5009209937583462130424629 469613431648449574727309)
                  ·
                    rfl

theorem cell22_4115560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 1, 2, 5].length) (baseStart_4115560 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4115560 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4115560 prefixEnd_4115560 := by exact prefixLift 4115560
  have htrace : WordTrace (prefixWord ++ tailWord_4115560) baseStart_4115560 baseEnd_4115560 := by
    simpa [prefixWord, tailWord_4115560, baseEnd_4115560] using wordTrace_append hprefix tailTrace_4115560
  have hstable : (prefixWord ++ tailWord_4115560).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4115560).length < 2 ^ (prefixWord ++ tailWord_4115560).sum := by decide
  have hdescent : baseEnd_4115560 < baseStart_4115560 := by decide
  rcases family_descends (prefixWord ++ tailWord_4115560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4115618 : List Nat := [3, 3, 1, 3, 2, 1, 1, 2, 2, 4]
def baseStart_4115618 : Nat := 118140960795 + 4115618 * 2 ^ 59
def prefixEnd_4115618 : Nat := 4983230072969 + 3 ^ 40 * 4115618 * 2
def baseEnd_4115618 : Nat := 1408860149530655906231749

theorem tailTrace_4115618 : CollatzResearch.WordTrace tailWord_4115618 prefixEnd_4115618 1408860149530655906231749 := by
  unfold tailWord_4115618
  simp only [CollatzResearch.WordTrace]
  refine ⟨37527230100956588109862877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100072613602550901626301005 37527230100956588109862877)
  ·
    refine ⟨14072711287858720541198579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37527230100956588109862877 14072711287858720541198579)
    ·
      refine ⟨21109066931788080811797869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14072711287858720541198579 21109066931788080811797869)
      ·
        refine ⟨7915900099420530304424201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21109066931788080811797869 7915900099420530304424201)
        ·
          refine ⟨5936925074565397728318151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7915900099420530304424201 5936925074565397728318151)
          ·
            refine ⟨8905387611848096592477227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5936925074565397728318151 8905387611848096592477227)
            ·
              refine ⟨13358081417772144888715841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8905387611848096592477227 13358081417772144888715841)
              ·
                refine ⟨10018561063329108666536881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13358081417772144888715841 10018561063329108666536881)
                ·
                  refine ⟨7513920797496831499902661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10018561063329108666536881 7513920797496831499902661)
                  ·
                    refine ⟨1408860149530655906231749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7513920797496831499902661 1408860149530655906231749)
                    ·
                      rfl

theorem cell22_4115618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 2, 2, 4].length) (baseStart_4115618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4115618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4115618 prefixEnd_4115618 := by exact prefixLift 4115618
  have htrace : WordTrace (prefixWord ++ tailWord_4115618) baseStart_4115618 baseEnd_4115618 := by
    simpa [prefixWord, tailWord_4115618, baseEnd_4115618] using wordTrace_append hprefix tailTrace_4115618
  have hstable : (prefixWord ++ tailWord_4115618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4115618).length < 2 ^ (prefixWord ++ tailWord_4115618).sum := by decide
  have hdescent : baseEnd_4115618 < baseStart_4115618 := by decide
  rcases family_descends (prefixWord ++ tailWord_4115618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4115631 : List Nat := [1, 1, 2, 1, 2, 3, 5, 1, 3, 3]
def baseStart_4115631 : Nat := 118140960795 + 4115631 * 2 ^ 59
def prefixEnd_4115631 : Nat := 4983230072969 + 3 ^ 40 * 4115631 * 2
def baseEnd_4115631 : Nat := 1408864599696328205656709

theorem tailTrace_4115631 : CollatzResearch.WordTrace tailWord_4115631 prefixEnd_4115631 1408864599696328205656709 := by
  unfold tailWord_4115631
  simp only [CollatzResearch.WordTrace]
  refine ⟨150109394552779255659674747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100072929701852837106449831 150109394552779255659674747)
  ·
    refine ⟨225164091829168883489512121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150109394552779255659674747 225164091829168883489512121)
    ·
      refine ⟨168873068871876662617134091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225164091829168883489512121 168873068871876662617134091)
      ·
        refine ⟨253309603307814993925701137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168873068871876662617134091 253309603307814993925701137)
        ·
          refine ⟨189982202480861245444275853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 253309603307814993925701137 189982202480861245444275853)
          ·
            refine ⟨71243325930322967041603445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 189982202480861245444275853 71243325930322967041603445)
            ·
              refine ⟨6679061805967778160150323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71243325930322967041603445 6679061805967778160150323)
              ·
                refine ⟨10018592708951667240225485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6679061805967778160150323 10018592708951667240225485)
                ·
                  refine ⟨3756972265856875215084557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10018592708951667240225485 3756972265856875215084557)
                  ·
                    refine ⟨1408864599696328205656709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3756972265856875215084557 1408864599696328205656709)
                    ·
                      rfl

theorem cell22_4115631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 5, 1, 3, 3].length) (baseStart_4115631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4115631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4115631 prefixEnd_4115631 := by exact prefixLift 4115631
  have htrace : WordTrace (prefixWord ++ tailWord_4115631) baseStart_4115631 baseEnd_4115631 := by
    simpa [prefixWord, tailWord_4115631, baseEnd_4115631] using wordTrace_append hprefix tailTrace_4115631
  have hstable : (prefixWord ++ tailWord_4115631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4115631).length < 2 ^ (prefixWord ++ tailWord_4115631).sum := by decide
  have hdescent : baseEnd_4115631 < baseStart_4115631 := by decide
  rcases family_descends (prefixWord ++ tailWord_4115631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4115721 : List Nat := [1, 2, 1, 1, 3, 3, 2, 2, 4, 3]
def baseStart_4115721 : Nat := 118140960795 + 4115721 * 2 ^ 59
def prefixEnd_4115721 : Nat := 4983230072969 + 3 ^ 40 * 4115721 * 2
def baseEnd_4115721 : Nat := 1408895408535597970906433

theorem tailTrace_4115721 : CollatzResearch.WordTrace tailWord_4115721 prefixEnd_4115721 1408895408535597970906433 := by
  unfold tailWord_4115721
  simp only [CollatzResearch.WordTrace]
  refine ⟨150112677122453201030451017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100075118081635467353634011 150112677122453201030451017)
  ·
    refine ⟨112584507841839900772838263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150112677122453201030451017 112584507841839900772838263)
    ·
      refine ⟨168876761762759851159257395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112584507841839900772838263 168876761762759851159257395)
      ·
        refine ⟨253315142644139776738886093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168876761762759851159257395 253315142644139776738886093)
        ·
          refine ⟨94993178491552416277082285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 253315142644139776738886093 94993178491552416277082285)
          ·
            refine ⟨35622441934332156103905857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94993178491552416277082285 35622441934332156103905857)
            ·
              refine ⟨26716831450749117077929393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35622441934332156103905857 26716831450749117077929393)
              ·
                refine ⟨20037623588061837808447045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26716831450749117077929393 20037623588061837808447045)
                ·
                  refine ⟨3757054422761594589083821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20037623588061837808447045 3757054422761594589083821)
                  ·
                    refine ⟨1408895408535597970906433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3757054422761594589083821 1408895408535597970906433)
                    ·
                      rfl

theorem cell22_4115721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 2, 4, 3].length) (baseStart_4115721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4115721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4115721 prefixEnd_4115721 := by exact prefixLift 4115721
  have htrace : WordTrace (prefixWord ++ tailWord_4115721) baseStart_4115721 baseEnd_4115721 := by
    simpa [prefixWord, tailWord_4115721, baseEnd_4115721] using wordTrace_append hprefix tailTrace_4115721
  have hstable : (prefixWord ++ tailWord_4115721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4115721).length < 2 ^ (prefixWord ++ tailWord_4115721).sum := by decide
  have hdescent : baseEnd_4115721 < baseStart_4115721 := by decide
  rcases family_descends (prefixWord ++ tailWord_4115721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4115723 : List Nat := [1, 1, 1, 1, 5, 4, 2, 3, 4]
def baseStart_4115723 : Nat := 118140960795 + 4115723 * 2 ^ 59
def prefixEnd_4115723 : Nat := 4983230072969 + 3 ^ 40 * 4115723 * 2
def baseEnd_4115723 : Nat := 469632031058823544118809

theorem tailTrace_4115723 : CollatzResearch.WordTrace tailWord_4115723 prefixEnd_4115723 469632031058823544118809 := by
  unfold tailWord_4115723
  simp only [CollatzResearch.WordTrace]
  refine ⟨150112750068445955372023823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100075166712297303581349215 150112750068445955372023823)
  ·
    refine ⟨225169125102668933058035735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150112750068445955372023823 225169125102668933058035735)
    ·
      refine ⟨337753687654003399587053603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225169125102668933058035735 337753687654003399587053603)
      ·
        refine ⟨506630531481005099380580405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337753687654003399587053603 506630531481005099380580405)
        ·
          refine ⟨47496612326344228066929413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 506630531481005099380580405 47496612326344228066929413)
          ·
            refine ⟨8905614811189542762549265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47496612326344228066929413 8905614811189542762549265)
            ·
              refine ⟨6679211108392157071911949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8905614811189542762549265 6679211108392157071911949)
              ·
                refine ⟨2504704165647058901966981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6679211108392157071911949 2504704165647058901966981)
                ·
                  refine ⟨469632031058823544118809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2504704165647058901966981 469632031058823544118809)
                  ·
                    rfl

theorem cell22_4115723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 2, 3, 4].length) (baseStart_4115723 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4115723 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4115723 prefixEnd_4115723 := by exact prefixLift 4115723
  have htrace : WordTrace (prefixWord ++ tailWord_4115723) baseStart_4115723 baseEnd_4115723 := by
    simpa [prefixWord, tailWord_4115723, baseEnd_4115723] using wordTrace_append hprefix tailTrace_4115723
  have hstable : (prefixWord ++ tailWord_4115723).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4115723).length < 2 ^ (prefixWord ++ tailWord_4115723).sum := by decide
  have hdescent : baseEnd_4115723 < baseStart_4115723 := by decide
  rcases family_descends (prefixWord ++ tailWord_4115723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4115738 : List Nat := [3, 1, 1, 3, 3, 2, 1, 1, 4, 3]
def baseStart_4115738 : Nat := 118140960795 + 4115738 * 2 ^ 59
def prefixEnd_4115738 : Nat := 4983230072969 + 3 ^ 40 * 4115738 * 2
def baseEnd_4115738 : Nat := 1408901227983015593231381

theorem tailTrace_4115738 : CollatzResearch.WordTrace tailWord_4115738 prefixEnd_4115738 1408901227983015593231381 := by
  unfold tailWord_4115738
  simp only [CollatzResearch.WordTrace]
  refine ⟨37528324290847903233454967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100075531442261075289213245 37528324290847903233454967)
  ·
    refine ⟨56292486436271854850182451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37528324290847903233454967 56292486436271854850182451)
    ·
      refine ⟨84438729654407782275273677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56292486436271854850182451 84438729654407782275273677)
      ·
        refine ⟨31664523620402918353227629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84438729654407782275273677 31664523620402918353227629)
        ·
          refine ⟨11874196357651094382460361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31664523620402918353227629 11874196357651094382460361)
          ·
            refine ⟨8905647268238320786845271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11874196357651094382460361 8905647268238320786845271)
            ·
              refine ⟨13358470902357481180267907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8905647268238320786845271 13358470902357481180267907)
              ·
                refine ⟨20037706353536221770401861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13358470902357481180267907 20037706353536221770401861)
                ·
                  refine ⟨3757069941288041581950349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20037706353536221770401861 3757069941288041581950349)
                  ·
                    refine ⟨1408901227983015593231381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3757069941288041581950349 1408901227983015593231381)
                    ·
                      rfl

theorem cell22_4115738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 1, 4, 3].length) (baseStart_4115738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4115738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4115738 prefixEnd_4115738 := by exact prefixLift 4115738
  have htrace : WordTrace (prefixWord ++ tailWord_4115738) baseStart_4115738 baseEnd_4115738 := by
    simpa [prefixWord, tailWord_4115738, baseEnd_4115738] using wordTrace_append hprefix tailTrace_4115738
  have hstable : (prefixWord ++ tailWord_4115738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4115738).length < 2 ^ (prefixWord ++ tailWord_4115738).sum := by decide
  have hdescent : baseEnd_4115738 < baseStart_4115738 := by decide
  rcases family_descends (prefixWord ++ tailWord_4115738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4115796 : List Nat := [2, 4, 1, 1, 2, 1, 1, 3, 7]
def baseStart_4115796 : Nat := 118140960795 + 4115796 * 2 ^ 59
def prefixEnd_4115796 : Nat := 4983230072969 + 3 ^ 40 * 4115796 * 2
def baseEnd_4115796 : Nat := 469640360856107591760401

theorem tailTrace_4115796 : CollatzResearch.WordTrace tailWord_4115796 prefixEnd_4115796 469640360856107591760401 := by
  unfold tailWord_4115796
  simp only [CollatzResearch.WordTrace]
  refine ⟨75057706298590744419715621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100076941731454325892954161 75057706298590744419715621)
  ·
    refine ⟨14073319930985764578696679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75057706298590744419715621 14073319930985764578696679)
    ·
      refine ⟨21109979896478646868045019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14073319930985764578696679 21109979896478646868045019)
      ·
        refine ⟨31664969844717970302067529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21109979896478646868045019 31664969844717970302067529)
        ·
          refine ⟨23748727383538477726550647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31664969844717970302067529 23748727383538477726550647)
          ·
            refine ⟨35623091075307716589825971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23748727383538477726550647 35623091075307716589825971)
            ·
              refine ⟨53434636612961574884738957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35623091075307716589825971 53434636612961574884738957)
              ·
                refine ⟨20037988729860590581777109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53434636612961574884738957 20037988729860590581777109)
                ·
                  refine ⟨469640360856107591760401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20037988729860590581777109 469640360856107591760401)
                  ·
                    rfl

theorem cell22_4115796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 3, 7].length) (baseStart_4115796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4115796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4115796 prefixEnd_4115796 := by exact prefixLift 4115796
  have htrace : WordTrace (prefixWord ++ tailWord_4115796) baseStart_4115796 baseEnd_4115796 := by
    simpa [prefixWord, tailWord_4115796, baseEnd_4115796] using wordTrace_append hprefix tailTrace_4115796
  have hstable : (prefixWord ++ tailWord_4115796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4115796).length < 2 ^ (prefixWord ++ tailWord_4115796).sum := by decide
  have hdescent : baseEnd_4115796 < baseStart_4115796 := by decide
  rcases family_descends (prefixWord ++ tailWord_4115796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4115924 : List Nat := [2, 4, 1, 2, 3, 1, 3, 1, 2, 3]
def baseStart_4115924 : Nat := 118140960795 + 4115924 * 2 ^ 59
def prefixEnd_4115924 : Nat := 4983230072969 + 3 ^ 40 * 4115924 * 2
def baseEnd_4115924 : Nat := 1408964899584173108080811

theorem tailTrace_4115924 : CollatzResearch.WordTrace tailWord_4115924 prefixEnd_4115924 1408964899584173108080811 := by
  unfold tailWord_4115924
  simp only [CollatzResearch.WordTrace]
  refine ⟨75060040570358883350045413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100080054093811844466727217 75060040570358883350045413)
  ·
    refine ⟨14073757606942290628133515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75060040570358883350045413 14073757606942290628133515)
    ·
      refine ⟨21110636410413435942200273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14073757606942290628133515 21110636410413435942200273)
      ·
        refine ⟨15832977307810076956650205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21110636410413435942200273 15832977307810076956650205)
        ·
          refine ⟨5937366490428778858743827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15832977307810076956650205 5937366490428778858743827)
          ·
            refine ⟨8906049735643168288115741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5937366490428778858743827 8906049735643168288115741)
            ·
              refine ⟨3339768650866188108043403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8906049735643168288115741 3339768650866188108043403)
              ·
                refine ⟨5009652976299282162065105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3339768650866188108043403 5009652976299282162065105)
                ·
                  refine ⟨3757239732224461621548829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5009652976299282162065105 3757239732224461621548829)
                  ·
                    refine ⟨1408964899584173108080811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3757239732224461621548829 1408964899584173108080811)
                    ·
                      rfl

theorem cell22_4115924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 3, 1, 2, 3].length) (baseStart_4115924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4115924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4115924 prefixEnd_4115924 := by exact prefixLift 4115924
  have htrace : WordTrace (prefixWord ++ tailWord_4115924) baseStart_4115924 baseEnd_4115924 := by
    simpa [prefixWord, tailWord_4115924, baseEnd_4115924] using wordTrace_append hprefix tailTrace_4115924
  have hstable : (prefixWord ++ tailWord_4115924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4115924).length < 2 ^ (prefixWord ++ tailWord_4115924).sum := by decide
  have hdescent : baseEnd_4115924 < baseStart_4115924 := by decide
  rcases family_descends (prefixWord ++ tailWord_4115924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4115952 : List Nat := [2, 1, 1, 1, 3, 4, 3, 3, 1, 3]
def baseStart_4115952 : Nat := 118140960795 + 4115952 * 2 ^ 59
def prefixEnd_4115952 : Nat := 4983230072969 + 3 ^ 40 * 4115952 * 2
def baseEnd_4115952 : Nat := 1408974484556390368380725

theorem tailTrace_4115952 : CollatzResearch.WordTrace tailWord_4115952 prefixEnd_4115952 1408974484556390368380725 := by
  unfold tailWord_4115952
  simp only [CollatzResearch.WordTrace]
  refine ⟨75060551192308163741055055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100080734923077551654740073 75060551192308163741055055)
  ·
    refine ⟨112590826788462245611582583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75060551192308163741055055 112590826788462245611582583)
    ·
      refine ⟨168886240182693368417373875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112590826788462245611582583 168886240182693368417373875)
      ·
        refine ⟨253329360274040052626060813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168886240182693368417373875 253329360274040052626060813)
        ·
          refine ⟨94998510102765019734772805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 253329360274040052626060813 94998510102765019734772805)
          ·
            refine ⟨17812220644268441200269901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94998510102765019734772805 17812220644268441200269901)
            ·
              refine ⟨6679582741600665450101213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17812220644268441200269901 6679582741600665450101213)
              ·
                refine ⟨2504843528100249543787955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6679582741600665450101213 2504843528100249543787955)
                ·
                  refine ⟨3757265292150374315681933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2504843528100249543787955 3757265292150374315681933)
                  ·
                    refine ⟨1408974484556390368380725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3757265292150374315681933 1408974484556390368380725)
                    ·
                      rfl

theorem cell22_4115952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 3, 3, 1, 3].length) (baseStart_4115952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4115952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4115952 prefixEnd_4115952 := by exact prefixLift 4115952
  have htrace : WordTrace (prefixWord ++ tailWord_4115952) baseStart_4115952 baseEnd_4115952 := by
    simpa [prefixWord, tailWord_4115952, baseEnd_4115952] using wordTrace_append hprefix tailTrace_4115952
  have hstable : (prefixWord ++ tailWord_4115952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4115952).length < 2 ^ (prefixWord ++ tailWord_4115952).sum := by decide
  have hdescent : baseEnd_4115952 < baseStart_4115952 := by decide
  rcases family_descends (prefixWord ++ tailWord_4115952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4115969 : List Nat := [1, 2, 4, 1, 5, 1, 1, 1, 3, 3]
def baseStart_4115969 : Nat := 118140960795 + 4115969 * 2 ^ 59
def prefixEnd_4115969 : Nat := 4983230072969 + 3 ^ 40 * 4115969 * 2
def baseEnd_4115969 : Nat := 1408980304003807990705673

theorem tailTrace_4115969 : CollatzResearch.WordTrace tailWord_4115969 prefixEnd_4115969 1408980304003807990705673 := by
  unfold tailWord_4115969
  simp only [CollatzResearch.WordTrace]
  refine ⟨150121722425554739385478961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100081148283703159590319307 150121722425554739385478961)
  ·
    refine ⟨112591291819166054539109221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150121722425554739385478961 112591291819166054539109221)
    ·
      refine ⟨21110867216093635226082979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112591291819166054539109221 21110867216093635226082979)
      ·
        refine ⟨31666300824140452839124469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21110867216093635226082979 31666300824140452839124469)
        ·
          refine ⟨2968715702263167453667919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31666300824140452839124469 2968715702263167453667919)
          ·
            refine ⟨4453073553394751180501879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2968715702263167453667919 4453073553394751180501879)
            ·
              refine ⟨6679610330092126770752819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4453073553394751180501879 6679610330092126770752819)
              ·
                refine ⟨10019415495138190156129229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6679610330092126770752819 10019415495138190156129229)
                ·
                  refine ⟨3757280810676821308548461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10019415495138190156129229 3757280810676821308548461)
                  ·
                    refine ⟨1408980304003807990705673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3757280810676821308548461 1408980304003807990705673)
                    ·
                      rfl

theorem cell22_4115969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 1, 1, 3, 3].length) (baseStart_4115969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4115969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4115969 prefixEnd_4115969 := by exact prefixLift 4115969
  have htrace : WordTrace (prefixWord ++ tailWord_4115969) baseStart_4115969 baseEnd_4115969 := by
    simpa [prefixWord, tailWord_4115969, baseEnd_4115969] using wordTrace_append hprefix tailTrace_4115969
  have hstable : (prefixWord ++ tailWord_4115969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4115969).length < 2 ^ (prefixWord ++ tailWord_4115969).sum := by decide
  have hdescent : baseEnd_4115969 < baseStart_4115969 := by decide
  rcases family_descends (prefixWord ++ tailWord_4115969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4116055 : List Nat := [1, 1, 3, 2, 2, 4, 3, 6]
def baseStart_4116055 : Nat := 118140960795 + 4116055 * 2 ^ 59
def prefixEnd_4116055 : Nat := 4983230072969 + 3 ^ 40 * 4116055 * 2
def baseEnd_4116055 : Nat := 156556638173481381450601

theorem tailTrace_4116055 : CollatzResearch.WordTrace tailWord_4116055 prefixEnd_4116055 156556638173481381450601 := by
  unfold tailWord_4116055
  simp only [CollatzResearch.WordTrace]
  refine ⟨150124859103243176073109619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100083239402162117382073079 150124859103243176073109619)
  ·
    refine ⟨225187288654864764109664429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150124859103243176073109619 225187288654864764109664429)
    ·
      refine ⟨84445233245574286541124161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 225187288654864764109664429 84445233245574286541124161)
      ·
        refine ⟨63333924934180714905843121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84445233245574286541124161 63333924934180714905843121)
        ·
          refine ⟨47500443700635536179382341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63333924934180714905843121 47500443700635536179382341)
          ·
            refine ⟨8906333193869163033634189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47500443700635536179382341 8906333193869163033634189)
            ·
              refine ⟨3339874947700936137612821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8906333193869163033634189 3339874947700936137612821)
              ·
                refine ⟨156556638173481381450601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3339874947700936137612821 156556638173481381450601)
                ·
                  rfl

theorem cell22_4116055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 3, 6].length) (baseStart_4116055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4116055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4116055 prefixEnd_4116055 := by exact prefixLift 4116055
  have htrace : WordTrace (prefixWord ++ tailWord_4116055) baseStart_4116055 baseEnd_4116055 := by
    simpa [prefixWord, tailWord_4116055, baseEnd_4116055] using wordTrace_append hprefix tailTrace_4116055
  have hstable : (prefixWord ++ tailWord_4116055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4116055).length < 2 ^ (prefixWord ++ tailWord_4116055).sum := by decide
  have hdescent : baseEnd_4116055 < baseStart_4116055 := by decide
  rcases family_descends (prefixWord ++ tailWord_4116055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4116061 : List Nat := [1, 4, 4, 2, 1, 1, 2, 3, 4]
def baseStart_4116061 : Nat := 118140960795 + 4116061 * 2 ^ 59
def prefixEnd_4116061 : Nat := 4983230072969 + 3 ^ 40 * 4116061 * 2
def baseEnd_4116061 : Nat := 469670599161316805801797

theorem tailTrace_4116061 : CollatzResearch.WordTrace tailWord_4116061 prefixEnd_4116061 469670599161316805801797 := by
  unfold tailWord_4116061
  simp only [CollatzResearch.WordTrace]
  refine ⟨150125077941221439097828037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100083385294147626065218691 150125077941221439097828037)
  ·
    refine ⟨28148452113979019830842757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 150125077941221439097828037 28148452113979019830842757)
    ·
      refine ⟨5277834771371066218283017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28148452113979019830842757 5277834771371066218283017)
      ·
        refine ⟨3958376078528299663712263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5277834771371066218283017 3958376078528299663712263)
        ·
          refine ⟨5937564117792449495568395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3958376078528299663712263 5937564117792449495568395)
          ·
            refine ⟨8906346176688674243352593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5937564117792449495568395 8906346176688674243352593)
            ·
              refine ⟨6679759632516505682514445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8906346176688674243352593 6679759632516505682514445)
              ·
                refine ⟨2504909862193689630942917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6679759632516505682514445 2504909862193689630942917)
                ·
                  refine ⟨469670599161316805801797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2504909862193689630942917 469670599161316805801797)
                  ·
                    rfl

theorem cell22_4116061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 2, 3, 4].length) (baseStart_4116061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4116061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4116061 prefixEnd_4116061 := by exact prefixLift 4116061
  have htrace : WordTrace (prefixWord ++ tailWord_4116061) baseStart_4116061 baseEnd_4116061 := by
    simpa [prefixWord, tailWord_4116061, baseEnd_4116061] using wordTrace_append hprefix tailTrace_4116061
  have hstable : (prefixWord ++ tailWord_4116061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4116061).length < 2 ^ (prefixWord ++ tailWord_4116061).sum := by decide
  have hdescent : baseEnd_4116061 < baseStart_4116061 := by decide
  rcases family_descends (prefixWord ++ tailWord_4116061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4116160 : List Nat := [2, 1, 1, 2, 4, 1, 2, 3, 1, 5]
def baseStart_4116160 : Nat := 118140960795 + 4116160 * 2 ^ 59
def prefixEnd_4116160 : Nat := 4983230072969 + 3 ^ 40 * 4116160 * 2
def baseEnd_4116160 : Nat := 1409045687207147159180087

theorem tailTrace_4116160 : CollatzResearch.WordTrace tailWord_4116160 prefixEnd_4116160 1409045687207147159180087 := by
  unfold tailWord_4116160
  simp only [CollatzResearch.WordTrace]
  refine ⟨75064344383931389502840967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100085792511908519337121289 75064344383931389502840967)
  ·
    refine ⟨112596516575897084254261451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75064344383931389502840967 112596516575897084254261451)
    ·
      refine ⟨168894774863845626381392177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112596516575897084254261451 168894774863845626381392177)
      ·
        refine ⟨126671081147884219786044133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168894774863845626381392177 126671081147884219786044133)
        ·
          refine ⟨23750827715228291209883275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 126671081147884219786044133 23750827715228291209883275)
          ·
            refine ⟨35626241572842436814824913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23750827715228291209883275 35626241572842436814824913)
            ·
              refine ⟨26719681179631827611118685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35626241572842436814824913 26719681179631827611118685)
              ·
                refine ⟨10019880442361935354169507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26719681179631827611118685 10019880442361935354169507)
                ·
                  refine ⟨15029820663542903031254261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10019880442361935354169507 15029820663542903031254261)
                  ·
                    refine ⟨1409045687207147159180087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15029820663542903031254261 1409045687207147159180087)
                    ·
                      rfl

theorem cell22_4116160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 3, 1, 5].length) (baseStart_4116160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4116160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4116160 prefixEnd_4116160 := by exact prefixLift 4116160
  have htrace : WordTrace (prefixWord ++ tailWord_4116160) baseStart_4116160 baseEnd_4116160 := by
    simpa [prefixWord, tailWord_4116160, baseEnd_4116160] using wordTrace_append hprefix tailTrace_4116160
  have hstable : (prefixWord ++ tailWord_4116160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4116160).length < 2 ^ (prefixWord ++ tailWord_4116160).sum := by decide
  have hdescent : baseEnd_4116160 < baseStart_4116160 := by decide
  rcases family_descends (prefixWord ++ tailWord_4116160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4116220 : List Nat := [2, 2, 2, 1, 3, 1, 1, 2, 2, 6]
def baseStart_4116220 : Nat := 118140960795 + 4116220 * 2 ^ 59
def prefixEnd_4116220 : Nat := 4983230072969 + 3 ^ 40 * 4116220 * 2
def baseEnd_4116220 : Nat := 1409066226433327002679903

theorem tailTrace_4116220 : CollatzResearch.WordTrace tailWord_4116220 prefixEnd_4116220 1409066226433327002679903 := by
  unfold tailWord_4116220
  simp only [CollatzResearch.WordTrace]
  refine ⟨75065438573822704626433057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100087251431763606168577409 75065438573822704626433057)
  ·
    refine ⟨56299078930367028469824793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75065438573822704626433057 56299078930367028469824793)
    ·
      refine ⟨42224309197775271352368595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56299078930367028469824793 42224309197775271352368595)
      ·
        refine ⟨63336463796662907028552893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42224309197775271352368595 63336463796662907028552893)
        ·
          refine ⟨23751173923748590135707335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63336463796662907028552893 23751173923748590135707335)
          ·
            refine ⟨35626760885622885203561003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23751173923748590135707335 35626760885622885203561003)
            ·
              refine ⟨53440141328434327805341505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35626760885622885203561003 53440141328434327805341505)
              ·
                refine ⟨40080105996325745854006129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53440141328434327805341505 40080105996325745854006129)
                ·
                  refine ⟨30060079497244309390504597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40080105996325745854006129 30060079497244309390504597)
                  ·
                    refine ⟨1409066226433327002679903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30060079497244309390504597 1409066226433327002679903)
                    ·
                      rfl

theorem cell22_4116220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 2, 2, 6].length) (baseStart_4116220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4116220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4116220 prefixEnd_4116220 := by exact prefixLift 4116220
  have htrace : WordTrace (prefixWord ++ tailWord_4116220) baseStart_4116220 baseEnd_4116220 := by
    simpa [prefixWord, tailWord_4116220, baseEnd_4116220] using wordTrace_append hprefix tailTrace_4116220
  have hstable : (prefixWord ++ tailWord_4116220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4116220).length < 2 ^ (prefixWord ++ tailWord_4116220).sum := by decide
  have hdescent : baseEnd_4116220 < baseStart_4116220 := by decide
  rcases family_descends (prefixWord ++ tailWord_4116220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4116327 : List Nat := [1, 1, 5, 1, 2, 1, 1, 2, 4, 4]
def baseStart_4116327 : Nat := 118140960795 + 4116327 * 2 ^ 59
def prefixEnd_4116327 : Nat := 4983230072969 + 3 ^ 40 * 4116327 * 2
def baseEnd_4116327 : Nat := 1409102854720014390254575

theorem tailTrace_4116327 : CollatzResearch.WordTrace tailWord_4116327 prefixEnd_4116327 1409102854720014390254575 := by
  unfold tailWord_4116327
  simp only [CollatzResearch.WordTrace]
  refine ⟨150134779758257766527011235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100089853172171844351340823 150134779758257766527011235)
  ·
    refine ⟨225202169637386649790516853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150134779758257766527011235 225202169637386649790516853)
    ·
      refine ⟨21112703403504998417860955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 225202169637386649790516853 21112703403504998417860955)
      ·
        refine ⟨31669055105257497626791433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21112703403504998417860955 31669055105257497626791433)
        ·
          refine ⟨23751791328943123220093575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31669055105257497626791433 23751791328943123220093575)
          ·
            refine ⟨35627686993414684830140363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23751791328943123220093575 35627686993414684830140363)
            ·
              refine ⟨53441530490122027245210545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35627686993414684830140363 53441530490122027245210545)
              ·
                refine ⟨40081147867591520433907909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53441530490122027245210545 40081147867591520433907909)
                ·
                  refine ⟨7515215225173410081357733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40081147867591520433907909 7515215225173410081357733)
                  ·
                    refine ⟨1409102854720014390254575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7515215225173410081357733 1409102854720014390254575)
                    ·
                      rfl

theorem cell22_4116327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 2, 4, 4].length) (baseStart_4116327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4116327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4116327 prefixEnd_4116327 := by exact prefixLift 4116327
  have htrace : WordTrace (prefixWord ++ tailWord_4116327) baseStart_4116327 baseEnd_4116327 := by
    simpa [prefixWord, tailWord_4116327, baseEnd_4116327] using wordTrace_append hprefix tailTrace_4116327
  have hstable : (prefixWord ++ tailWord_4116327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4116327).length < 2 ^ (prefixWord ++ tailWord_4116327).sum := by decide
  have hdescent : baseEnd_4116327 < baseStart_4116327 := by decide
  rcases family_descends (prefixWord ++ tailWord_4116327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4116376 : List Nat := [2, 1, 2, 6, 1, 2, 1, 7]
def baseStart_4116376 : Nat := 118140960795 + 4116376 * 2 ^ 59
def prefixEnd_4116376 : Nat := 4983230072969 + 3 ^ 40 * 4116376 * 2
def baseEnd_4116376 : Nat := 156568847602377177308825

theorem tailTrace_4116376 : CollatzResearch.WordTrace tailWord_4116376 prefixEnd_4116376 156568847602377177308825 := by
  unfold tailWord_4116376
  simp only [CollatzResearch.WordTrace]
  refine ⟨75068283467540123947772491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100091044623386831930363321 75068283467540123947772491)
  ·
    refine ⟨112602425201310185921658737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75068283467540123947772491 112602425201310185921658737)
    ·
      refine ⟨84451818900982639441244053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112602425201310185921658737 84451818900982639441244053)
      ·
        refine ⟨3958679010983561223808315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 84451818900982639441244053 3958679010983561223808315)
        ·
          refine ⟨5938018516475341835712473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3958679010983561223808315 5938018516475341835712473)
          ·
            refine ⟨4453513887356506376784355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5938018516475341835712473 4453513887356506376784355)
            ·
              refine ⟨6680270831034759565176533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4453513887356506376784355 6680270831034759565176533)
              ·
                refine ⟨156568847602377177308825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6680270831034759565176533 156568847602377177308825)
                ·
                  rfl

theorem cell22_4116376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 1, 7].length) (baseStart_4116376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4116376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4116376 prefixEnd_4116376 := by exact prefixLift 4116376
  have htrace : WordTrace (prefixWord ++ tailWord_4116376) baseStart_4116376 baseEnd_4116376 := by
    simpa [prefixWord, tailWord_4116376, baseEnd_4116376] using wordTrace_append hprefix tailTrace_4116376
  have hstable : (prefixWord ++ tailWord_4116376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4116376).length < 2 ^ (prefixWord ++ tailWord_4116376).sum := by decide
  have hdescent : baseEnd_4116376 < baseStart_4116376 := by decide
  rcases family_descends (prefixWord ++ tailWord_4116376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4116391 : List Nat := [1, 1, 6, 1, 2, 2, 1, 2, 3, 3]
def baseStart_4116391 : Nat := 118140960795 + 4116391 * 2 ^ 59
def prefixEnd_4116391 : Nat := 4983230072969 + 3 ^ 40 * 4116391 * 2
def baseEnd_4116391 : Nat := 1409124763227939556654379

theorem tailTrace_4116391 : CollatzResearch.WordTrace tailWord_4116391 prefixEnd_4116391 1409124763227939556654379 := by
  unfold tailWord_4116391
  simp only [CollatzResearch.WordTrace]
  refine ⟨150137114030025905457341027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100091409353350603638227351 150137114030025905457341027)
  ·
    refine ⟨225205671045038858186011541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150137114030025905457341027 225205671045038858186011541)
    ·
      refine ⟨10556515830236196477469291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 225205671045038858186011541 10556515830236196477469291)
      ·
        refine ⟨15834773745354294716203937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10556515830236196477469291 15834773745354294716203937)
        ·
          refine ⟨11876080309015721037152953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15834773745354294716203937 11876080309015721037152953)
          ·
            refine ⟨8907060231761790777864715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11876080309015721037152953 8907060231761790777864715)
            ·
              refine ⟨13360590347642686166797073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8907060231761790777864715 13360590347642686166797073)
              ·
                refine ⟨10020442760732014625097805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13360590347642686166797073 10020442760732014625097805)
                ·
                  refine ⟨3757666035274505484411677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10020442760732014625097805 3757666035274505484411677)
                  ·
                    refine ⟨1409124763227939556654379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3757666035274505484411677 1409124763227939556654379)
                    ·
                      rfl

theorem cell22_4116391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 2, 3, 3].length) (baseStart_4116391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4116391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4116391 prefixEnd_4116391 := by exact prefixLift 4116391
  have htrace : WordTrace (prefixWord ++ tailWord_4116391) baseStart_4116391 baseEnd_4116391 := by
    simpa [prefixWord, tailWord_4116391, baseEnd_4116391] using wordTrace_append hprefix tailTrace_4116391
  have hstable : (prefixWord ++ tailWord_4116391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4116391).length < 2 ^ (prefixWord ++ tailWord_4116391).sum := by decide
  have hdescent : baseEnd_4116391 < baseStart_4116391 := by decide
  rcases family_descends (prefixWord ++ tailWord_4116391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4116432 : List Nat := [2, 1, 1, 1, 1, 2, 5, 3, 6]
def baseStart_4116432 : Nat := 118140960795 + 4116432 * 2 ^ 59
def prefixEnd_4116432 : Nat := 4983230072969 + 3 ^ 40 * 4116432 * 2
def baseEnd_4116432 : Nat := 469712932788609705459751

theorem tailTrace_4116432 : CollatzResearch.WordTrace tailWord_4116432 prefixEnd_4116432 469712932788609705459751 := by
  unfold tailWord_4116432
  simp only [CollatzResearch.WordTrace]
  refine ⟨75069304711438684729791775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100092406281918246306389033 75069304711438684729791775)
  ·
    refine ⟨112603957067158027094687663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75069304711438684729791775 112603957067158027094687663)
    ·
      refine ⟨168905935600737040642031495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112603957067158027094687663 168905935600737040642031495)
      ·
        refine ⟨253358903401105560963047243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168905935600737040642031495 253358903401105560963047243)
        ·
          refine ⟨380038355101658341444570865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253358903401105560963047243 380038355101658341444570865)
          ·
            refine ⟨285028766326243756083428149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 380038355101658341444570865 285028766326243756083428149)
            ·
              refine ⟨26721446843085352132821389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 285028766326243756083428149 26721446843085352132821389)
              ·
                refine ⟨10020542566157007049808021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26721446843085352132821389 10020542566157007049808021)
                ·
                  refine ⟨469712932788609705459751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10020542566157007049808021 469712932788609705459751)
                  ·
                    rfl

theorem cell22_4116432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 3, 6].length) (baseStart_4116432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4116432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4116432 prefixEnd_4116432 := by exact prefixLift 4116432
  have htrace : WordTrace (prefixWord ++ tailWord_4116432) baseStart_4116432 baseEnd_4116432 := by
    simpa [prefixWord, tailWord_4116432, baseEnd_4116432] using wordTrace_append hprefix tailTrace_4116432
  have hstable : (prefixWord ++ tailWord_4116432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4116432).length < 2 ^ (prefixWord ++ tailWord_4116432).sum := by decide
  have hdescent : baseEnd_4116432 < baseStart_4116432 := by decide
  rcases family_descends (prefixWord ++ tailWord_4116432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4116451 : List Nat := [1, 1, 1, 6, 1, 3, 2, 2, 1, 4]
def baseStart_4116451 : Nat := 118140960795 + 4116451 * 2 ^ 59
def prefixEnd_4116451 : Nat := 4983230072969 + 3 ^ 40 * 4116451 * 2
def baseEnd_4116451 : Nat := 1409145302454119400154195

theorem tailTrace_4116451 : CollatzResearch.WordTrace tailWord_4116451 prefixEnd_4116451 1409145302454119400154195 := by
  unfold tailWord_4116451
  simp only [CollatzResearch.WordTrace]
  refine ⟨150139302409808535704525207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100092868273205690469683471 150139302409808535704525207)
  ·
    refine ⟨225208953614712803556787811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150139302409808535704525207 225208953614712803556787811)
    ·
      refine ⟨337813430422069205335181717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225208953614712803556787811 337813430422069205335181717)
      ·
        refine ⟨15835004551034494000086643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 337813430422069205335181717 15835004551034494000086643)
        ·
          refine ⟨23752506826551741000129965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15835004551034494000086643 23752506826551741000129965)
          ·
            refine ⟨8907190059956902875048737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23752506826551741000129965 8907190059956902875048737)
            ·
              refine ⟨6680392544967677156286553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8907190059956902875048737 6680392544967677156286553)
              ·
                refine ⟨5010294408725757867214915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6680392544967677156286553 5010294408725757867214915)
                ·
                  refine ⟨7515441613088636800822373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5010294408725757867214915 7515441613088636800822373)
                  ·
                    refine ⟨1409145302454119400154195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7515441613088636800822373 1409145302454119400154195)
                    ·
                      rfl

theorem cell22_4116451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 2, 2, 1, 4].length) (baseStart_4116451 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4116451 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4116451 prefixEnd_4116451 := by exact prefixLift 4116451
  have htrace : WordTrace (prefixWord ++ tailWord_4116451) baseStart_4116451 baseEnd_4116451 := by
    simpa [prefixWord, tailWord_4116451, baseEnd_4116451] using wordTrace_append hprefix tailTrace_4116451
  have hstable : (prefixWord ++ tailWord_4116451).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4116451).length < 2 ^ (prefixWord ++ tailWord_4116451).sum := by decide
  have hdescent : baseEnd_4116451 < baseStart_4116451 := by decide
  rcases family_descends (prefixWord ++ tailWord_4116451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4116464 : List Nat := [2, 1, 1, 1, 3, 2, 3, 2, 4, 3]
def baseStart_4116464 : Nat := 118140960795 + 4116464 * 2 ^ 59
def prefixEnd_4116464 : Nat := 4983230072969 + 3 ^ 40 * 4116464 * 2
def baseEnd_4116464 : Nat := 1409149752619791699579155

theorem tailTrace_4116464 : CollatzResearch.WordTrace tailWord_4116464 prefixEnd_4116464 1409149752619791699579155 := by
  unfold tailWord_4116464
  simp only [CollatzResearch.WordTrace]
  refine ⟨75069888279380719462374223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100093184372507625949832297 75069888279380719462374223)
  ·
    refine ⟨112604832419071079193561335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75069888279380719462374223 112604832419071079193561335)
    ·
      refine ⟨168907248628606618790342003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112604832419071079193561335 168907248628606618790342003)
      ·
        refine ⟨253360872942909928185513005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168907248628606618790342003 253360872942909928185513005)
        ·
          refine ⟨95010327353591223069567377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 253360872942909928185513005 95010327353591223069567377)
          ·
            refine ⟨71257745515193417302175533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95010327353591223069567377 71257745515193417302175533)
            ·
              refine ⟨26721654568197531488315825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71257745515193417302175533 26721654568197531488315825)
              ·
                refine ⟨20041240926148148616236869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26721654568197531488315825 20041240926148148616236869)
                ·
                  refine ⟨3757732673652777865544413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20041240926148148616236869 3757732673652777865544413)
                  ·
                    refine ⟨1409149752619791699579155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3757732673652777865544413 1409149752619791699579155)
                    ·
                      rfl

theorem cell22_4116464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 2, 4, 3].length) (baseStart_4116464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4116464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4116464 prefixEnd_4116464 := by exact prefixLift 4116464
  have htrace : WordTrace (prefixWord ++ tailWord_4116464) baseStart_4116464 baseEnd_4116464 := by
    simpa [prefixWord, tailWord_4116464, baseEnd_4116464] using wordTrace_append hprefix tailTrace_4116464
  have hstable : (prefixWord ++ tailWord_4116464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4116464).length < 2 ^ (prefixWord ++ tailWord_4116464).sum := by decide
  have hdescent : baseEnd_4116464 < baseStart_4116464 := by decide
  rcases family_descends (prefixWord ++ tailWord_4116464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4116477 : List Nat := [1, 4, 1, 1, 1, 2, 12]
def baseStart_4116477 : Nat := 118140960795 + 4116477 * 2 ^ 59
def prefixEnd_4116477 : Nat := 4983230072969 + 3 ^ 40 * 4116477 * 2
def baseEnd_4116477 : Nat := 52190896399461629592745

theorem tailTrace_4116477 : CollatzResearch.WordTrace tailWord_4116477 prefixEnd_4116477 52190896399461629592745 := by
  unfold tailWord_4116477
  simp only [CollatzResearch.WordTrace]
  refine ⟨150140250707714342144971685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100093500471809561429981123 150140250707714342144971685)
  ·
    refine ⟨28151297007696439152182191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 150140250707714342144971685 28151297007696439152182191)
    ·
      refine ⟨42226945511544658728273287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28151297007696439152182191 42226945511544658728273287)
      ·
        refine ⟨63340418267316988092409931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42226945511544658728273287 63340418267316988092409931)
        ·
          refine ⟨95010627400975482138614897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63340418267316988092409931 95010627400975482138614897)
          ·
            refine ⟨71257970550731611603961173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95010627400975482138614897 71257970550731611603961173)
            ·
              refine ⟨52190896399461629592745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 71257970550731611603961173 52190896399461629592745)
              ·
                rfl

theorem cell22_4116477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 12].length) (baseStart_4116477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4116477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4116477 prefixEnd_4116477 := by exact prefixLift 4116477
  have htrace : WordTrace (prefixWord ++ tailWord_4116477) baseStart_4116477 baseEnd_4116477 := by
    simpa [prefixWord, tailWord_4116477, baseEnd_4116477] using wordTrace_append hprefix tailTrace_4116477
  have hstable : (prefixWord ++ tailWord_4116477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4116477).length < 2 ^ (prefixWord ++ tailWord_4116477).sum := by decide
  have hdescent : baseEnd_4116477 < baseStart_4116477 := by decide
  rcases family_descends (prefixWord ++ tailWord_4116477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4116481 : List Nat := [1, 2, 4, 1, 2, 1, 2, 4, 2, 3]
def baseStart_4116481 : Nat := 118140960795 + 4116481 * 2 ^ 59
def prefixEnd_4116481 : Nat := 4983230072969 + 3 ^ 40 * 4116481 * 2
def baseEnd_4116481 : Nat := 1409155572067209321904103

theorem tailTrace_4116481 : CollatzResearch.WordTrace tailWord_4116481 prefixEnd_4116481 1409155572067209321904103 := by
  unfold tailWord_4116481
  simp only [CollatzResearch.WordTrace]
  refine ⟨150140396599699850828117297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100093597733133233885411531 150140396599699850828117297)
  ·
    refine ⟨112605297449774888121087973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150140396599699850828117297 112605297449774888121087973)
    ·
      refine ⟨21113493271832791522703995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112605297449774888121087973 21113493271832791522703995)
      ·
        refine ⟨31670239907749187284055993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21113493271832791522703995 31670239907749187284055993)
        ·
          refine ⟨23752679930811890463041995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31670239907749187284055993 23752679930811890463041995)
          ·
            refine ⟨35629019896217835694562993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23752679930811890463041995 35629019896217835694562993)
            ·
              refine ⟨26721764922163376770922245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35629019896217835694562993 26721764922163376770922245)
              ·
                refine ⟨5010330922905633144547921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26721764922163376770922245 5010330922905633144547921)
                ·
                  refine ⟨3757748192179224858410941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5010330922905633144547921 3757748192179224858410941)
                  ·
                    refine ⟨1409155572067209321904103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3757748192179224858410941 1409155572067209321904103)
                    ·
                      rfl

theorem cell22_4116481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 4, 2, 3].length) (baseStart_4116481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4116481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4116481 prefixEnd_4116481 := by exact prefixLift 4116481
  have htrace : WordTrace (prefixWord ++ tailWord_4116481) baseStart_4116481 baseEnd_4116481 := by
    simpa [prefixWord, tailWord_4116481, baseEnd_4116481] using wordTrace_append hprefix tailTrace_4116481
  have hstable : (prefixWord ++ tailWord_4116481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4116481).length < 2 ^ (prefixWord ++ tailWord_4116481).sum := by decide
  have hdescent : baseEnd_4116481 < baseStart_4116481 := by decide
  rcases family_descends (prefixWord ++ tailWord_4116481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4116494 : List Nat := [4, 1, 1, 2, 2, 1, 4, 7]
def baseStart_4116494 : Nat := 118140960795 + 4116494 * 2 ^ 59
def prefixEnd_4116494 : Nat := 4983230072969 + 3 ^ 40 * 4116494 * 2
def baseEnd_4116494 : Nat := 156573335803653513481007

theorem tailTrace_4116494 : CollatzResearch.WordTrace tailWord_4116494 prefixEnd_4116494 156573335803653513481007 := by
  unfold tailWord_4116494
  simp only [CollatzResearch.WordTrace]
  refine ⟨18767608843581594256042567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100093913832435169365560357 18767608843581594256042567)
  ·
    refine ⟨28151413265372391384063851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18767608843581594256042567 28151413265372391384063851)
    ·
      refine ⟨42227119898058587076095777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28151413265372391384063851 42227119898058587076095777)
      ·
        refine ⟨31670339923543940307071833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42227119898058587076095777 31670339923543940307071833)
        ·
          refine ⟨23752754942657955230303875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31670339923543940307071833 23752754942657955230303875)
          ·
            refine ⟨35629132413986932845455813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23752754942657955230303875 35629132413986932845455813)
            ·
              refine ⟨6680462327622549908522965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35629132413986932845455813 6680462327622549908522965)
              ·
                refine ⟨156573335803653513481007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6680462327622549908522965 156573335803653513481007)
                ·
                  rfl

theorem cell22_4116494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 4, 7].length) (baseStart_4116494 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4116494 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4116494 prefixEnd_4116494 := by exact prefixLift 4116494
  have htrace : WordTrace (prefixWord ++ tailWord_4116494) baseStart_4116494 baseEnd_4116494 := by
    simpa [prefixWord, tailWord_4116494, baseEnd_4116494] using wordTrace_append hprefix tailTrace_4116494
  have hstable : (prefixWord ++ tailWord_4116494).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4116494).length < 2 ^ (prefixWord ++ tailWord_4116494).sum := by decide
  have hdescent : baseEnd_4116494 < baseStart_4116494 := by decide
  rcases family_descends (prefixWord ++ tailWord_4116494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4116507 : List Nat := [1, 1, 1, 1, 1, 1, 3, 3, 4, 6]
def baseStart_4116507 : Nat := 118140960795 + 4116507 * 2 ^ 59
def prefixEnd_4116507 : Nat := 4983230072969 + 3 ^ 40 * 4116507 * 2
def baseEnd_4116507 : Nat := 1409164472398553920754023

theorem tailTrace_4116507 : CollatzResearch.WordTrace tailWord_4116507 prefixEnd_4116507 1409164472398553920754023 := by
  unfold tailWord_4116507
  simp only [CollatzResearch.WordTrace]
  refine ⟨150141344897605657268563775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100094229931737104845709183 150141344897605657268563775)
  ·
    refine ⟨225212017346408485902845663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150141344897605657268563775 225212017346408485902845663)
    ·
      refine ⟨337818026019612728854268495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225212017346408485902845663 337818026019612728854268495)
      ·
        refine ⟨506727039029419093281402743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337818026019612728854268495 506727039029419093281402743)
        ·
          refine ⟨760090558544128639922104115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 506727039029419093281402743 760090558544128639922104115)
          ·
            refine ⟨1140135837816192959883156173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 760090558544128639922104115 1140135837816192959883156173)
            ·
              refine ⟨427550939181072359956183565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1140135837816192959883156173 427550939181072359956183565)
              ·
                refine ⟨160331602192902134983568837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 427550939181072359956183565 160331602192902134983568837)
                ·
                  refine ⟨30062175411169150309419157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 160331602192902134983568837 30062175411169150309419157)
                  ·
                    refine ⟨1409164472398553920754023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30062175411169150309419157 1409164472398553920754023)
                    ·
                      rfl

theorem cell22_4116507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 4, 6].length) (baseStart_4116507 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4116507 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4116507 prefixEnd_4116507 := by exact prefixLift 4116507
  have htrace : WordTrace (prefixWord ++ tailWord_4116507) baseStart_4116507 baseEnd_4116507 := by
    simpa [prefixWord, tailWord_4116507, baseEnd_4116507] using wordTrace_append hprefix tailTrace_4116507
  have hstable : (prefixWord ++ tailWord_4116507).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4116507).length < 2 ^ (prefixWord ++ tailWord_4116507).sum := by decide
  have hdescent : baseEnd_4116507 < baseStart_4116507 := by decide
  rcases family_descends (prefixWord ++ tailWord_4116507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4116569 : List Nat := [1, 2, 1, 2, 2, 1, 3, 3, 3, 4]
def baseStart_4116569 : Nat := 118140960795 + 4116569 * 2 ^ 59
def prefixEnd_4116569 : Nat := 4983230072969 + 3 ^ 40 * 4116569 * 2
def baseEnd_4116569 : Nat := 1409185696265606425703833

theorem tailTrace_4116569 : CollatzResearch.WordTrace tailWord_4116569 prefixEnd_4116569 1409185696265606425703833 := by
  unfold tailWord_4116569
  simp only [CollatzResearch.WordTrace]
  refine ⟨150143606223381041857320761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100095737482254027904880507 150143606223381041857320761)
  ·
    refine ⟨112607704667535781392990571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150143606223381041857320761 112607704667535781392990571)
    ·
      refine ⟨168911557001303672089485857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112607704667535781392990571 168911557001303672089485857)
      ·
        refine ⟨126683667750977754067114393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168911557001303672089485857 126683667750977754067114393)
        ·
          refine ⟨95012750813233315550335795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126683667750977754067114393 95012750813233315550335795)
          ·
            refine ⟨142519126219849973325503693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95012750813233315550335795 142519126219849973325503693)
            ·
              refine ⟨53444672332443739997063885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142519126219849973325503693 53444672332443739997063885)
              ·
                refine ⟨20041752124666402498898957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53444672332443739997063885 20041752124666402498898957)
                ·
                  refine ⟨7515657046749900937087109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20041752124666402498898957 7515657046749900937087109)
                  ·
                    refine ⟨1409185696265606425703833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7515657046749900937087109 1409185696265606425703833)
                    ·
                      rfl

theorem cell22_4116569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 3, 3, 4].length) (baseStart_4116569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4116569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4116569 prefixEnd_4116569 := by exact prefixLift 4116569
  have htrace : WordTrace (prefixWord ++ tailWord_4116569) baseStart_4116569 baseEnd_4116569 := by
    simpa [prefixWord, tailWord_4116569, baseEnd_4116569] using wordTrace_append hprefix tailTrace_4116569
  have hstable : (prefixWord ++ tailWord_4116569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4116569).length < 2 ^ (prefixWord ++ tailWord_4116569).sum := by decide
  have hdescent : baseEnd_4116569 < baseStart_4116569 := by decide
  rcases family_descends (prefixWord ++ tailWord_4116569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4116601 : List Nat := [1, 2, 1, 3, 4, 2, 2, 1, 6]
def baseStart_4116601 : Nat := 118140960795 + 4116601 * 2 ^ 59
def prefixEnd_4116601 : Nat := 4983230072969 + 3 ^ 40 * 4116601 * 2
def baseEnd_4116601 : Nat := 469732216839856336301245

theorem tailTrace_4116601 : CollatzResearch.WordTrace tailWord_4116601 prefixEnd_4116601 469732216839856336301245 := by
  unfold tailWord_4116601
  simp only [CollatzResearch.WordTrace]
  refine ⟨150144773359265111322485657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100096515572843407548323771 150144773359265111322485657)
  ·
    refine ⟨112608580019448833491864243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150144773359265111322485657 112608580019448833491864243)
    ·
      refine ⟨168912870029173250237796365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112608580019448833491864243 168912870029173250237796365)
      ·
        refine ⟨63342326260939968839173637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168912870029173250237796365 63342326260939968839173637)
        ·
          refine ⟨11876686173926244157345057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63342326260939968839173637 11876686173926244157345057)
          ·
            refine ⟨8907514630444683118008793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11876686173926244157345057 8907514630444683118008793)
            ·
              refine ⟨6680635972833512338506595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8907514630444683118008793 6680635972833512338506595)
              ·
                refine ⟨10020953959250268507759893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6680635972833512338506595 10020953959250268507759893)
                ·
                  refine ⟨469732216839856336301245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10020953959250268507759893 469732216839856336301245)
                  ·
                    rfl

theorem cell22_4116601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 2, 1, 6].length) (baseStart_4116601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4116601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4116601 prefixEnd_4116601 := by exact prefixLift 4116601
  have htrace : WordTrace (prefixWord ++ tailWord_4116601) baseStart_4116601 baseEnd_4116601 := by
    simpa [prefixWord, tailWord_4116601, baseEnd_4116601] using wordTrace_append hprefix tailTrace_4116601
  have hstable : (prefixWord ++ tailWord_4116601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4116601).length < 2 ^ (prefixWord ++ tailWord_4116601).sum := by decide
  have hdescent : baseEnd_4116601 < baseStart_4116601 := by decide
  rcases family_descends (prefixWord ++ tailWord_4116601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4116629 : List Nat := [1, 3, 2, 1, 1, 1, 5, 8]
def baseStart_4116629 : Nat := 118140960795 + 4116629 * 2 ^ 59
def prefixEnd_4116629 : Nat := 4983230072969 + 3 ^ 40 * 4116629 * 2
def baseEnd_4116629 : Nat := 156578470610198474355961

theorem tailTrace_4116629 : CollatzResearch.WordTrace tailWord_4116629 prefixEnd_4116629 156578470610198474355961 := by
  unfold tailWord_4116629
  simp only [CollatzResearch.WordTrace]
  refine ⟨150145794603163672104504941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100097196402109114736336627 150145794603163672104504941)
  ·
    refine ⟨56304672976186377039189353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150145794603163672104504941 56304672976186377039189353)
    ·
      refine ⟨42228504732139782779392015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56304672976186377039189353 42228504732139782779392015)
      ·
        refine ⟨63342757098209674169088023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42228504732139782779392015 63342757098209674169088023)
        ·
          refine ⟨95014135647314511253632035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63342757098209674169088023 95014135647314511253632035)
          ·
            refine ⟨142521203470971766880448053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95014135647314511253632035 142521203470971766880448053)
            ·
              refine ⟨13361362825403603145042005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 142521203470971766880448053 13361362825403603145042005)
              ·
                refine ⟨156578470610198474355961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13361362825403603145042005 156578470610198474355961)
                ·
                  rfl

theorem cell22_4116629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 8].length) (baseStart_4116629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4116629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4116629 prefixEnd_4116629 := by exact prefixLift 4116629
  have htrace : WordTrace (prefixWord ++ tailWord_4116629) baseStart_4116629 baseEnd_4116629 := by
    simpa [prefixWord, tailWord_4116629, baseEnd_4116629] using wordTrace_append hprefix tailTrace_4116629
  have hstable : (prefixWord ++ tailWord_4116629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4116629).length < 2 ^ (prefixWord ++ tailWord_4116629).sum := by decide
  have hdescent : baseEnd_4116629 < baseStart_4116629 := by decide
  rcases family_descends (prefixWord ++ tailWord_4116629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4116659 : List Nat := [1, 1, 1, 2, 3, 2, 1, 3, 2, 6]
def baseStart_4116659 : Nat := 118140960795 + 4116659 * 2 ^ 59
def prefixEnd_4116659 : Nat := 4983230072969 + 3 ^ 40 * 4116659 * 2
def baseEnd_4116659 : Nat := 1409216505104876190953557

theorem tailTrace_4116659 : CollatzResearch.WordTrace tailWord_4116659 prefixEnd_4116659 1409216505104876190953557 := by
  unfold tailWord_4116659
  simp only [CollatzResearch.WordTrace]
  refine ⟨150146888793054987228097031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100097925862036658152064687 150146888793054987228097031)
  ·
    refine ⟨225220333189582480842145547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150146888793054987228097031 225220333189582480842145547)
    ·
      refine ⟨337830499784373721263218321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225220333189582480842145547 337830499784373721263218321)
      ·
        refine ⟨253372874838280290947413741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 337830499784373721263218321 253372874838280290947413741)
        ·
          refine ⟨95014828064355109105280153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 253372874838280290947413741 95014828064355109105280153)
          ·
            refine ⟨71261121048266331828960115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95014828064355109105280153 71261121048266331828960115)
            ·
              refine ⟨106891681572399497743440173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71261121048266331828960115 106891681572399497743440173)
              ·
                refine ⟨40084380589649811653790065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106891681572399497743440173 40084380589649811653790065)
                ·
                  refine ⟨30063285442237358740342549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40084380589649811653790065 30063285442237358740342549)
                  ·
                    refine ⟨1409216505104876190953557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30063285442237358740342549 1409216505104876190953557)
                    ·
                      rfl

theorem cell22_4116659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 3, 2, 6].length) (baseStart_4116659 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4116659 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4116659 prefixEnd_4116659 := by exact prefixLift 4116659
  have htrace : WordTrace (prefixWord ++ tailWord_4116659) baseStart_4116659 baseEnd_4116659 := by
    simpa [prefixWord, tailWord_4116659, baseEnd_4116659] using wordTrace_append hprefix tailTrace_4116659
  have hstable : (prefixWord ++ tailWord_4116659).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4116659).length < 2 ^ (prefixWord ++ tailWord_4116659).sum := by decide
  have hdescent : baseEnd_4116659 < baseStart_4116659 := by decide
  rcases family_descends (prefixWord ++ tailWord_4116659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4116712 : List Nat := [2, 1, 4, 1, 2, 2, 4, 2, 1, 3]
def baseStart_4116712 : Nat := 118140960795 + 4116712 * 2 ^ 59
def prefixEnd_4116712 : Nat := 4983230072969 + 3 ^ 40 * 4116712 * 2
def baseEnd_4116712 : Nat := 1409234648088001719378395

theorem tailTrace_4116712 : CollatzResearch.WordTrace tailWord_4116712 prefixEnd_4116712 1409234648088001719378395 := by
  unfold tailWord_4116712
  simp only [CollatzResearch.WordTrace]
  refine ⟨75074410930931488639888195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100099214574575318186517593 75074410930931488639888195)
  ·
    refine ⟨112611616396397232959832293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75074410930931488639888195 112611616396397232959832293)
    ·
      refine ⟨21114678074324481179968555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112611616396397232959832293 21114678074324481179968555)
      ·
        refine ⟨31672017111486721769952833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21114678074324481179968555 31672017111486721769952833)
        ·
          refine ⟨23754012833615041327464625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31672017111486721769952833 23754012833615041327464625)
          ·
            refine ⟨17815509625211280995598469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23754012833615041327464625 17815509625211280995598469)
            ·
              refine ⟨3340408054727115186674713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17815509625211280995598469 3340408054727115186674713)
              ·
                refine ⟨2505306041045336390006035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3340408054727115186674713 2505306041045336390006035)
                ·
                  refine ⟨3757959061568004585009053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2505306041045336390006035 3757959061568004585009053)
                  ·
                    refine ⟨1409234648088001719378395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3757959061568004585009053 1409234648088001719378395)
                    ·
                      rfl

theorem cell22_4116712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 4, 2, 1, 3].length) (baseStart_4116712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4116712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4116712 prefixEnd_4116712 := by exact prefixLift 4116712
  have htrace : WordTrace (prefixWord ++ tailWord_4116712) baseStart_4116712 baseEnd_4116712 := by
    simpa [prefixWord, tailWord_4116712, baseEnd_4116712] using wordTrace_append hprefix tailTrace_4116712
  have hstable : (prefixWord ++ tailWord_4116712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4116712).length < 2 ^ (prefixWord ++ tailWord_4116712).sum := by decide
  have hdescent : baseEnd_4116712 < baseStart_4116712 := by decide
  rcases family_descends (prefixWord ++ tailWord_4116712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4116721 : List Nat := [1, 2, 2, 2, 2, 1, 3, 2, 3, 4]
def baseStart_4116721 : Nat := 118140960795 + 4116721 * 2 ^ 59
def prefixEnd_4116721 : Nat := 4983230072969 + 3 ^ 40 * 4116721 * 2
def baseEnd_4116721 : Nat := 1409237728971928695903367

theorem tailTrace_4116721 : CollatzResearch.WordTrace tailWord_4116721 prefixEnd_4116721 1409237728971928695903367 := by
  unfold tailWord_4116721
  simp only [CollatzResearch.WordTrace]
  refine ⟨150149150118830371816854017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100099433412553581211236011 150149150118830371816854017)
  ·
    refine ⟨112611862589122778862640513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150149150118830371816854017 112611862589122778862640513)
    ·
      refine ⟨84458896941842084146980385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112611862589122778862640513 84458896941842084146980385)
      ·
        refine ⟨63344172706381563110235289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84458896941842084146980385 63344172706381563110235289)
        ·
          refine ⟨47508129529786172332676467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63344172706381563110235289 47508129529786172332676467)
          ·
            refine ⟨71262194294679258499014701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47508129529786172332676467 71262194294679258499014701)
            ·
              refine ⟨26723322860504721937130513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71262194294679258499014701 26723322860504721937130513)
              ·
                refine ⟨20042492145378541452847885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26723322860504721937130513 20042492145378541452847885)
                ·
                  refine ⟨7515934554516953044817957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20042492145378541452847885 7515934554516953044817957)
                  ·
                    refine ⟨1409237728971928695903367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7515934554516953044817957 1409237728971928695903367)
                    ·
                      rfl

theorem cell22_4116721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 2, 3, 4].length) (baseStart_4116721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4116721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4116721 prefixEnd_4116721 := by exact prefixLift 4116721
  have htrace : WordTrace (prefixWord ++ tailWord_4116721) baseStart_4116721 baseEnd_4116721 := by
    simpa [prefixWord, tailWord_4116721, baseEnd_4116721] using wordTrace_append hprefix tailTrace_4116721
  have hstable : (prefixWord ++ tailWord_4116721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4116721).length < 2 ^ (prefixWord ++ tailWord_4116721).sum := by decide
  have hdescent : baseEnd_4116721 < baseStart_4116721 := by decide
  rcases family_descends (prefixWord ++ tailWord_4116721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4116753 : List Nat := [1, 2, 2, 1, 1, 5, 1, 5, 4]
def baseStart_4116753 : Nat := 118140960795 + 4116753 * 2 ^ 59
def prefixEnd_4116753 : Nat := 4983230072969 + 3 ^ 40 * 4116753 * 2
def baseEnd_4116753 : Nat := 469749561075297093034423

theorem tailTrace_4116753 : CollatzResearch.WordTrace tailWord_4116753 prefixEnd_4116753 469749561075297093034423 := by
  unfold tailWord_4116753
  simp only [CollatzResearch.WordTrace]
  refine ⟨150150317254714441282018913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100100211503142960854679275 150150317254714441282018913)
  ·
    refine ⟨112612737941035830961514185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150150317254714441282018913 112612737941035830961514185)
    ·
      refine ⟨84459553455776873221135639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112612737941035830961514185 84459553455776873221135639)
      ·
        refine ⟨126689330183665309831703459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84459553455776873221135639 126689330183665309831703459)
        ·
          refine ⟨190033995275497964747555189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126689330183665309831703459 190033995275497964747555189)
          ·
            refine ⟨17815687057077934195083299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 190033995275497964747555189 17815687057077934195083299)
            ·
              refine ⟨26723530585616901292624949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17815687057077934195083299 26723530585616901292624949)
              ·
                refine ⟨2505330992401584496183589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26723530585616901292624949 2505330992401584496183589)
                ·
                  refine ⟨469749561075297093034423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2505330992401584496183589 469749561075297093034423)
                  ·
                    rfl

theorem cell22_4116753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 5, 4].length) (baseStart_4116753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4116753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4116753 prefixEnd_4116753 := by exact prefixLift 4116753
  have htrace : WordTrace (prefixWord ++ tailWord_4116753) baseStart_4116753 baseEnd_4116753 := by
    simpa [prefixWord, tailWord_4116753, baseEnd_4116753] using wordTrace_append hprefix tailTrace_4116753
  have hstable : (prefixWord ++ tailWord_4116753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4116753).length < 2 ^ (prefixWord ++ tailWord_4116753).sum := by decide
  have hdescent : baseEnd_4116753 < baseStart_4116753 := by decide
  rcases family_descends (prefixWord ++ tailWord_4116753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4116770 : List Nat := [3, 3, 1, 1, 3, 1, 2, 4, 4]
def baseStart_4116770 : Nat := 118140960795 + 4116770 * 2 ^ 59
def prefixEnd_4116770 : Nat := 4983230072969 + 3 ^ 40 * 4116770 * 2
def baseEnd_4116770 : Nat := 469751500891102967142739

theorem tailTrace_4116770 : CollatzResearch.WordTrace tailWord_4116770 prefixEnd_4116770 469751500891102967142739 := by
  unfold tailWord_4116770
  simp only [CollatzResearch.WordTrace]
  refine ⟨37537734323913213296346941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100100624863768568790258509 37537734323913213296346941)
  ·
    refine ⟨14076650371467454986130103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37537734323913213296346941 14076650371467454986130103)
    ·
      refine ⟨21114975557201182479195155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14076650371467454986130103 21114975557201182479195155)
      ·
        refine ⟨31672463335801773718792733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21114975557201182479195155 31672463335801773718792733)
        ·
          refine ⟨11877173750925665144547275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31672463335801773718792733 11877173750925665144547275)
          ·
            refine ⟨17815760626388497716820913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11877173750925665144547275 17815760626388497716820913)
            ·
              refine ⟨13361820469791373287615685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17815760626388497716820913 13361820469791373287615685)
              ·
                refine ⟨2505341338085882491427941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13361820469791373287615685 2505341338085882491427941)
                ·
                  refine ⟨469751500891102967142739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2505341338085882491427941 469751500891102967142739)
                  ·
                    rfl

theorem cell22_4116770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 4, 4].length) (baseStart_4116770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4116770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4116770 prefixEnd_4116770 := by exact prefixLift 4116770
  have htrace : WordTrace (prefixWord ++ tailWord_4116770) baseStart_4116770 baseEnd_4116770 := by
    simpa [prefixWord, tailWord_4116770, baseEnd_4116770] using wordTrace_append hprefix tailTrace_4116770
  have hstable : (prefixWord ++ tailWord_4116770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4116770).length < 2 ^ (prefixWord ++ tailWord_4116770).sum := by decide
  have hdescent : baseEnd_4116770 < baseStart_4116770 := by decide
  rcases family_descends (prefixWord ++ tailWord_4116770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4116785 : List Nat := [1, 2, 2, 3, 4, 2, 1, 1, 1, 5]
def baseStart_4116785 : Nat := 118140960795 + 4116785 * 2 ^ 59
def prefixEnd_4116785 : Nat := 4983230072969 + 3 ^ 40 * 4116785 * 2
def baseEnd_4116785 : Nat := 1409259637479853862303171

theorem tailTrace_4116785 : CollatzResearch.WordTrace tailWord_4116785 prefixEnd_4116785 1409259637479853862303171 := by
  unfold tailWord_4116785
  simp only [CollatzResearch.WordTrace]
  refine ⟨150151484390598510747183809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100100989593732340498122539 150151484390598510747183809)
  ·
    refine ⟨112613613292948883060387857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150151484390598510747183809 112613613292948883060387857)
    ·
      refine ⟨84460209969711662295290893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112613613292948883060387857 84460209969711662295290893)
      ·
        refine ⟨31672578738641873360734085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84460209969711662295290893 31672578738641873360734085)
        ·
          refine ⟨5938608513495351255137641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31672578738641873360734085 5938608513495351255137641)
          ·
            refine ⟨4453956385121513441353231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5938608513495351255137641 4453956385121513441353231)
            ·
              refine ⟨6680934577682270162029847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4453956385121513441353231 6680934577682270162029847)
              ·
                refine ⟨10021401866523405243044771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6680934577682270162029847 10021401866523405243044771)
                ·
                  refine ⟨15032102799785107864567157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10021401866523405243044771 15032102799785107864567157)
                  ·
                    refine ⟨1409259637479853862303171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15032102799785107864567157 1409259637479853862303171)
                    ·
                      rfl

theorem cell22_4116785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 1, 1, 1, 5].length) (baseStart_4116785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4116785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4116785 prefixEnd_4116785 := by exact prefixLift 4116785
  have htrace : WordTrace (prefixWord ++ tailWord_4116785) baseStart_4116785 baseEnd_4116785 := by
    simpa [prefixWord, tailWord_4116785, baseEnd_4116785] using wordTrace_append hprefix tailTrace_4116785
  have hstable : (prefixWord ++ tailWord_4116785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4116785).length < 2 ^ (prefixWord ++ tailWord_4116785).sum := by decide
  have hdescent : baseEnd_4116785 < baseStart_4116785 := by decide
  rcases family_descends (prefixWord ++ tailWord_4116785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4116796 : List Nat := [2, 2, 2, 2, 1, 2, 1, 1, 2, 7]
def baseStart_4116796 : Nat := 118140960795 + 4116796 * 2 ^ 59
def prefixEnd_4116796 : Nat := 4983230072969 + 3 ^ 40 * 4116796 * 2
def baseEnd_4116796 : Nat := 1409263403004653500278137

theorem tailTrace_4116796 : CollatzResearch.WordTrace tailWord_4116796 prefixEnd_4116796 1409263403004653500278137 := by
  unfold tailWord_4116796
  simp only [CollatzResearch.WordTrace]
  refine ⟨75075942796779329812917121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100101257062372439750556161 75075942796779329812917121)
  ·
    refine ⟨56306957097584497359687841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75075942796779329812917121 56306957097584497359687841)
    ·
      refine ⟨42230217823188373019765881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56306957097584497359687841 42230217823188373019765881)
      ·
        refine ⟨31672663367391279764824411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42230217823188373019765881 31672663367391279764824411)
        ·
          refine ⟨47508995051086919647236617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31672663367391279764824411 47508995051086919647236617)
          ·
            refine ⟨35631746288315189735427463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47508995051086919647236617 35631746288315189735427463)
            ·
              refine ⟨53447619432472784603141195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35631746288315189735427463 53447619432472784603141195)
              ·
                refine ⟨80171429148709176904711793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53447619432472784603141195 80171429148709176904711793)
                ·
                  refine ⟨60128571861531882678533845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80171429148709176904711793 60128571861531882678533845)
                  ·
                    refine ⟨1409263403004653500278137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60128571861531882678533845 1409263403004653500278137)
                    ·
                      rfl

theorem cell22_4116796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 2, 7].length) (baseStart_4116796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4116796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4116796 prefixEnd_4116796 := by exact prefixLift 4116796
  have htrace : WordTrace (prefixWord ++ tailWord_4116796) baseStart_4116796 baseEnd_4116796 := by
    simpa [prefixWord, tailWord_4116796, baseEnd_4116796] using wordTrace_append hprefix tailTrace_4116796
  have hstable : (prefixWord ++ tailWord_4116796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4116796).length < 2 ^ (prefixWord ++ tailWord_4116796).sum := by decide
  have hdescent : baseEnd_4116796 < baseStart_4116796 := by decide
  rcases family_descends (prefixWord ++ tailWord_4116796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4116798 : List Nat := [4, 2, 1, 2, 1, 3, 1, 8]
def baseStart_4116798 : Nat := 118140960795 + 4116798 * 2 ^ 59
def prefixEnd_4116798 : Nat := 4983230072969 + 3 ^ 40 * 4116798 * 2
def baseEnd_4116798 : Nat := 156584898627280684636459

theorem tailTrace_4116798 : CollatzResearch.WordTrace tailWord_4116798 prefixEnd_4116798 156584898627280684636459 := by
  unfold tailWord_4116798
  simp only [CollatzResearch.WordTrace]
  refine ⟨18768994817443926745925881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100101305693034275978271365 18768994817443926745925881)
  ·
    refine ⟨14076746113082945059444411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18768994817443926745925881 14076746113082945059444411)
    ·
      refine ⟨21115119169624417589166617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14076746113082945059444411 21115119169624417589166617)
      ·
        refine ⟨15836339377218313191874963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21115119169624417589166617 15836339377218313191874963)
        ·
          refine ⟨23754509065827469787812445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15836339377218313191874963 23754509065827469787812445)
          ·
            refine ⟨8907940899685301170429667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23754509065827469787812445 8907940899685301170429667)
            ·
              refine ⟨13361911349527951755644501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8907940899685301170429667 13361911349527951755644501)
              ·
                refine ⟨156584898627280684636459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13361911349527951755644501 156584898627280684636459)
                ·
                  rfl

theorem cell22_4116798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 8].length) (baseStart_4116798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4116798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4116798 prefixEnd_4116798 := by exact prefixLift 4116798
  have htrace : WordTrace (prefixWord ++ tailWord_4116798) baseStart_4116798 baseEnd_4116798 := by
    simpa [prefixWord, tailWord_4116798, baseEnd_4116798] using wordTrace_append hprefix tailTrace_4116798
  have hstable : (prefixWord ++ tailWord_4116798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4116798).length < 2 ^ (prefixWord ++ tailWord_4116798).sum := by decide
  have hdescent : baseEnd_4116798 < baseStart_4116798 := by decide
  rcases family_descends (prefixWord ++ tailWord_4116798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4116804 : List Nat := [2, 3, 4, 1, 2, 2, 1, 3, 4]
def baseStart_4116804 : Nat := 118140960795 + 4116804 * 2 ^ 59
def prefixEnd_4116804 : Nat := 4983230072969 + 3 ^ 40 * 4116804 * 2
def baseEnd_4116804 : Nat := 469755380522714715359371

theorem tailTrace_4116804 : CollatzResearch.WordTrace tailWord_4116804 prefixEnd_4116804 469755380522714715359371 := by
  unfold tailWord_4116804
  simp only [CollatzResearch.WordTrace]
  refine ⟨75076088688764838496062733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100101451585019784661416977 75076088688764838496062733)
  ·
    refine ⟨28153533258286814436023525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75076088688764838496062733 28153533258286814436023525)
    ·
      refine ⟨5278787485928777706754411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28153533258286814436023525 5278787485928777706754411)
      ·
        refine ⟨7918181228893166560131617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5278787485928777706754411 7918181228893166560131617)
        ·
          refine ⟨5938635921669874920098713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7918181228893166560131617 5938635921669874920098713)
          ·
            refine ⟨4453976941252406190074035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5938635921669874920098713 4453976941252406190074035)
            ·
              refine ⟨6680965411878609285111053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4453976941252406190074035 6680965411878609285111053)
              ·
                refine ⟨2505362029454478481916645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6680965411878609285111053 2505362029454478481916645)
                ·
                  refine ⟨469755380522714715359371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2505362029454478481916645 469755380522714715359371)
                  ·
                    rfl

theorem cell22_4116804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 1, 3, 4].length) (baseStart_4116804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4116804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4116804 prefixEnd_4116804 := by exact prefixLift 4116804
  have htrace : WordTrace (prefixWord ++ tailWord_4116804) baseStart_4116804 baseEnd_4116804 := by
    simpa [prefixWord, tailWord_4116804, baseEnd_4116804] using wordTrace_append hprefix tailTrace_4116804
  have hstable : (prefixWord ++ tailWord_4116804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4116804).length < 2 ^ (prefixWord ++ tailWord_4116804).sum := by decide
  have hdescent : baseEnd_4116804 < baseStart_4116804 := by decide
  rcases family_descends (prefixWord ++ tailWord_4116804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4116841 : List Nat := [1, 2, 1, 1, 1, 3, 4, 1, 1, 7]
def baseStart_4116841 : Nat := 118140960795 + 4116841 * 2 ^ 59
def prefixEnd_4116841 : Nat := 4983230072969 + 3 ^ 40 * 4116841 * 2
def baseEnd_4116841 : Nat := 1409278807424288382902999

theorem tailTrace_4116841 : CollatzResearch.WordTrace tailWord_4116841 prefixEnd_4116841 1409278807424288382902999 := by
  unfold tailWord_4116841
  simp only [CollatzResearch.WordTrace]
  refine ⟨150153526878395632311222377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100102351252263754874148251 150153526878395632311222377)
  ·
    refine ⟨112615145158796724233416783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150153526878395632311222377 112615145158796724233416783)
    ·
      refine ⟨168922717738195086350125175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112615145158796724233416783 168922717738195086350125175)
      ·
        refine ⟨253384076607292629525187763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168922717738195086350125175 253384076607292629525187763)
        ·
          refine ⟨380076114910938944287781645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253384076607292629525187763 380076114910938944287781645)
          ·
            refine ⟨142528543091602104107918117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 380076114910938944287781645 142528543091602104107918117)
            ·
              refine ⟨26724101829675394520234647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 142528543091602104107918117 26724101829675394520234647)
              ·
                refine ⟨40086152744513091780351971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26724101829675394520234647 40086152744513091780351971)
                ·
                  refine ⟨60129229116769637670527957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40086152744513091780351971 60129229116769637670527957)
                  ·
                    refine ⟨1409278807424288382902999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60129229116769637670527957 1409278807424288382902999)
                    ·
                      rfl

theorem cell22_4116841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 1, 1, 7].length) (baseStart_4116841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4116841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4116841 prefixEnd_4116841 := by exact prefixLift 4116841
  have htrace : WordTrace (prefixWord ++ tailWord_4116841) baseStart_4116841 baseEnd_4116841 := by
    simpa [prefixWord, tailWord_4116841, baseEnd_4116841] using wordTrace_append hprefix tailTrace_4116841
  have hstable : (prefixWord ++ tailWord_4116841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4116841).length < 2 ^ (prefixWord ++ tailWord_4116841).sum := by decide
  have hdescent : baseEnd_4116841 < baseStart_4116841 := by decide
  rcases family_descends (prefixWord ++ tailWord_4116841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4116924 : List Nat := [2, 2, 2, 4, 1, 3, 2, 1, 1, 4]
def baseStart_4116924 : Nat := 118140960795 + 4116924 * 2 ^ 59
def prefixEnd_4116924 : Nat := 4983230072969 + 3 ^ 40 * 4116924 * 2
def baseEnd_4116924 : Nat := 1409307220020503833077745

theorem tailTrace_4116924 : CollatzResearch.WordTrace tailWord_4116924 prefixEnd_4116924 1409307220020503833077745 := by
  unfold tailWord_4116924
  simp only [CollatzResearch.WordTrace]
  refine ⟨75078277068547468743246913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100104369424729958324329217 75078277068547468743246913)
  ·
    refine ⟨56308707801410601557435185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75078277068547468743246913 56308707801410601557435185)
    ·
      refine ⟨42231530851057951168076389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56308707801410601557435185 42231530851057951168076389)
      ·
        refine ⟨7918412034573365844014323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42231530851057951168076389 7918412034573365844014323)
        ·
          refine ⟨11877618051860048766021485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7918412034573365844014323 11877618051860048766021485)
          ·
            refine ⟨4454106769447518287258057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11877618051860048766021485 4454106769447518287258057)
            ·
              refine ⟨3340580077085638715443543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4454106769447518287258057 3340580077085638715443543)
              ·
                refine ⟨5010870115628458073165315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3340580077085638715443543 5010870115628458073165315)
                ·
                  refine ⟨7516305173442687109747973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5010870115628458073165315 7516305173442687109747973)
                  ·
                    refine ⟨1409307220020503833077745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7516305173442687109747973 1409307220020503833077745)
                    ·
                      rfl

theorem cell22_4116924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 2, 1, 1, 4].length) (baseStart_4116924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4116924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4116924 prefixEnd_4116924 := by exact prefixLift 4116924
  have htrace : WordTrace (prefixWord ++ tailWord_4116924) baseStart_4116924 baseEnd_4116924 := by
    simpa [prefixWord, tailWord_4116924, baseEnd_4116924] using wordTrace_append hprefix tailTrace_4116924
  have hstable : (prefixWord ++ tailWord_4116924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4116924).length < 2 ^ (prefixWord ++ tailWord_4116924).sum := by decide
  have hdescent : baseEnd_4116924 < baseStart_4116924 := by decide
  rcases family_descends (prefixWord ++ tailWord_4116924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4116950 : List Nat := [5, 2, 1, 1, 1, 1, 2, 9]
def baseStart_4116950 : Nat := 118140960795 + 4116950 * 2 ^ 59
def prefixEnd_4116950 : Nat := 4983230072969 + 3 ^ 40 * 4116950 * 2
def baseEnd_4116950 : Nat := 156590680039094270214185

theorem tailTrace_4116950 : CollatzResearch.WordTrace tailWord_4116950 prefixEnd_4116950 156590680039094270214185 := by
  unfold tailWord_4116950
  simp only [CollatzResearch.WordTrace]
  refine ⟨9384843902187546495433769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 100105001623333829284626869 9384843902187546495433769)
  ·
    refine ⟨7038632926640659871575327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9384843902187546495433769 7038632926640659871575327)
    ·
      refine ⟨10557949389960989807362991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7038632926640659871575327 10557949389960989807362991)
      ·
        refine ⟨15836924084941484711044487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10557949389960989807362991 15836924084941484711044487)
        ·
          refine ⟨23755386127412227066566731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15836924084941484711044487 23755386127412227066566731)
          ·
            refine ⟨35633079191118340599850097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23755386127412227066566731 35633079191118340599850097)
            ·
              refine ⟨26724809393338755449887573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35633079191118340599850097 26724809393338755449887573)
              ·
                refine ⟨156590680039094270214185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26724809393338755449887573 156590680039094270214185)
                ·
                  rfl

theorem cell22_4116950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 9].length) (baseStart_4116950 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4116950 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4116950 prefixEnd_4116950 := by exact prefixLift 4116950
  have htrace : WordTrace (prefixWord ++ tailWord_4116950) baseStart_4116950 baseEnd_4116950 := by
    simpa [prefixWord, tailWord_4116950, baseEnd_4116950] using wordTrace_append hprefix tailTrace_4116950
  have hstable : (prefixWord ++ tailWord_4116950).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4116950).length < 2 ^ (prefixWord ++ tailWord_4116950).sum := by decide
  have hdescent : baseEnd_4116950 < baseStart_4116950 := by decide
  rcases family_descends (prefixWord ++ tailWord_4116950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4116999 : List Nat := [1, 1, 4, 3, 3, 2, 1, 1, 3, 3]
def baseStart_4116999 : Nat := 118140960795 + 4116999 * 2 ^ 59
def prefixEnd_4116999 : Nat := 4983230072969 + 3 ^ 40 * 4116999 * 2
def baseEnd_4116999 : Nat := 1409332894053228637452515

theorem tailTrace_4116999 : CollatzResearch.WordTrace tailWord_4116999 prefixEnd_4116999 1409332894053228637452515 := by
  unfold tailWord_4116999
  simp only [CollatzResearch.WordTrace]
  refine ⟨150159289611823225295474051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100106193074548816863649367 150159289611823225295474051)
  ·
    refine ⟨225238934417734837943211077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150159289611823225295474051 225238934417734837943211077)
    ·
      refine ⟨42232300203325282114352077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 225238934417734837943211077 42232300203325282114352077)
      ·
        refine ⟨15837112576246980792882029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42232300203325282114352077 15837112576246980792882029)
        ·
          refine ⟨5938917216092617797330761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15837112576246980792882029 5938917216092617797330761)
          ·
            refine ⟨4454187912069463347998071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5938917216092617797330761 4454187912069463347998071)
            ·
              refine ⟨6681281868104195021997107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4454187912069463347998071 6681281868104195021997107)
              ·
                refine ⟨10021922802156292532995661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6681281868104195021997107 10021922802156292532995661)
                ·
                  refine ⟨3758221050808609699873373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10021922802156292532995661 3758221050808609699873373)
                  ·
                    refine ⟨1409332894053228637452515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3758221050808609699873373 1409332894053228637452515)
                    ·
                      rfl

theorem cell22_4116999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 1, 1, 3, 3].length) (baseStart_4116999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4116999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4116999 prefixEnd_4116999 := by exact prefixLift 4116999
  have htrace : WordTrace (prefixWord ++ tailWord_4116999) baseStart_4116999 baseEnd_4116999 := by
    simpa [prefixWord, tailWord_4116999, baseEnd_4116999] using wordTrace_append hprefix tailTrace_4116999
  have hstable : (prefixWord ++ tailWord_4116999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4116999).length < 2 ^ (prefixWord ++ tailWord_4116999).sum := by decide
  have hdescent : baseEnd_4116999 < baseStart_4116999 := by decide
  rcases family_descends (prefixWord ++ tailWord_4116999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4117023 : List Nat := [1, 1, 2, 4, 1, 1, 1, 3, 8]
def baseStart_4117023 : Nat := 118140960795 + 4117023 * 2 ^ 59
def prefixEnd_4117023 : Nat := 4983230072969 + 3 ^ 40 * 4117023 * 2
def baseEnd_4117023 : Nat := 469780369914566858284147

theorem tailTrace_4117023 : CollatzResearch.WordTrace tailWord_4117023 prefixEnd_4117023 469780369914566858284147 := by
  unfold tailWord_4117023
  simp only [CollatzResearch.WordTrace]
  refine ⟨150160164963736277394347723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100106776642490851596231815 150160164963736277394347723)
  ·
    refine ⟨225240247445604416091521585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150160164963736277394347723 225240247445604416091521585)
    ·
      refine ⟨168930185584203312068641189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225240247445604416091521585 168930185584203312068641189)
      ·
        refine ⟨31674409797038121012870223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 168930185584203312068641189 31674409797038121012870223)
        ·
          refine ⟨47511614695557181519305335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31674409797038121012870223 47511614695557181519305335)
          ·
            refine ⟨71267422043335772278958003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47511614695557181519305335 71267422043335772278958003)
            ·
              refine ⟨106901133065003658418437005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71267422043335772278958003 106901133065003658418437005)
              ·
                refine ⟨40087924899376371906913877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106901133065003658418437005 40087924899376371906913877)
                ·
                  refine ⟨469780369914566858284147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40087924899376371906913877 469780369914566858284147)
                  ·
                    rfl

theorem cell22_4117023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 3, 8].length) (baseStart_4117023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4117023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4117023 prefixEnd_4117023 := by exact prefixLift 4117023
  have htrace : WordTrace (prefixWord ++ tailWord_4117023) baseStart_4117023 baseEnd_4117023 := by
    simpa [prefixWord, tailWord_4117023, baseEnd_4117023] using wordTrace_append hprefix tailTrace_4117023
  have hstable : (prefixWord ++ tailWord_4117023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4117023).length < 2 ^ (prefixWord ++ tailWord_4117023).sum := by decide
  have hdescent : baseEnd_4117023 < baseStart_4117023 := by decide
  rcases family_descends (prefixWord ++ tailWord_4117023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4117025 : List Nat := [1, 2, 3, 2, 2, 1, 3, 1, 3, 4]
def baseStart_4117025 : Nat := 118140960795 + 4117025 * 2 ^ 59
def prefixEnd_4117025 : Nat := 4983230072969 + 3 ^ 40 * 4117025 * 2
def baseEnd_4117025 : Nat := 1409341794384573236302435

theorem tailTrace_4117025 : CollatzResearch.WordTrace tailWord_4117025 prefixEnd_4117025 1409341794384573236302435 := by
  unfold tailWord_4117025
  simp only [CollatzResearch.WordTrace]
  refine ⟨150160237909729031735920529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100106825273152687823947019 150160237909729031735920529)
  ·
    refine ⟨112620178432296773801940397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150160237909729031735920529 112620178432296773801940397)
    ·
      refine ⟨42232566912111290175727649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112620178432296773801940397 42232566912111290175727649)
      ·
        refine ⟨31674425184083467631795737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42232566912111290175727649 31674425184083467631795737)
        ·
          refine ⟨23755818888062600723846803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31674425184083467631795737 23755818888062600723846803)
          ·
            refine ⟨35633728332093901085770205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23755818888062600723846803 35633728332093901085770205)
            ·
              refine ⟨13362648124535212907163827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35633728332093901085770205 13362648124535212907163827)
              ·
                refine ⟨20043972186802819360745741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13362648124535212907163827 20043972186802819360745741)
                ·
                  refine ⟨7516489570051057260279653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20043972186802819360745741 7516489570051057260279653)
                  ·
                    refine ⟨1409341794384573236302435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7516489570051057260279653 1409341794384573236302435)
                    ·
                      rfl

theorem cell22_4117025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 1, 3, 4].length) (baseStart_4117025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4117025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4117025 prefixEnd_4117025 := by exact prefixLift 4117025
  have htrace : WordTrace (prefixWord ++ tailWord_4117025) baseStart_4117025 baseEnd_4117025 := by
    simpa [prefixWord, tailWord_4117025, baseEnd_4117025] using wordTrace_append hprefix tailTrace_4117025
  have hstable : (prefixWord ++ tailWord_4117025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4117025).length < 2 ^ (prefixWord ++ tailWord_4117025).sum := by decide
  have hdescent : baseEnd_4117025 < baseStart_4117025 := by decide
  rcases family_descends (prefixWord ++ tailWord_4117025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4117070 : List Nat := [4, 1, 1, 1, 1, 2, 2, 2, 4, 4]
def baseStart_4117070 : Nat := 118140960795 + 4117070 * 2 ^ 59
def prefixEnd_4117070 : Nat := 4983230072969 + 3 ^ 40 * 4117070 * 2
def baseEnd_4117070 : Nat := 1409357198804208118927297

theorem tailTrace_4117070 : CollatzResearch.WordTrace tailWord_4117070 prefixEnd_4117070 1409357198804208118927297 := by
  unfold tailWord_4117070
  simp only [CollatzResearch.WordTrace]
  refine ⟨18770234899320750552663583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100107919463044002947539109 18770234899320750552663583)
  ·
    refine ⟨28155352348981125828995375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18770234899320750552663583 28155352348981125828995375)
    ·
      refine ⟨42233028523471688743493063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28155352348981125828995375 42233028523471688743493063)
      ·
        refine ⟨63349542785207533115239595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42233028523471688743493063 63349542785207533115239595)
        ·
          refine ⟨95024314177811299672859393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63349542785207533115239595 95024314177811299672859393)
          ·
            refine ⟨71268235633358474754644545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95024314177811299672859393 71268235633358474754644545)
            ·
              refine ⟨53451176725018856065983409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71268235633358474754644545 53451176725018856065983409)
              ·
                refine ⟨40088382543764142049487557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53451176725018856065983409 40088382543764142049487557)
                ·
                  refine ⟨7516571726955776634278917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40088382543764142049487557 7516571726955776634278917)
                  ·
                    refine ⟨1409357198804208118927297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7516571726955776634278917 1409357198804208118927297)
                    ·
                      rfl

theorem cell22_4117070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 2, 4, 4].length) (baseStart_4117070 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4117070 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4117070 prefixEnd_4117070 := by exact prefixLift 4117070
  have htrace : WordTrace (prefixWord ++ tailWord_4117070) baseStart_4117070 baseEnd_4117070 := by
    simpa [prefixWord, tailWord_4117070, baseEnd_4117070] using wordTrace_append hprefix tailTrace_4117070
  have hstable : (prefixWord ++ tailWord_4117070).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4117070).length < 2 ^ (prefixWord ++ tailWord_4117070).sum := by decide
  have hdescent : baseEnd_4117070 < baseStart_4117070 := by decide
  rcases family_descends (prefixWord ++ tailWord_4117070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4117106 : List Nat := [3, 2, 1, 2, 4, 2, 1, 2, 2, 3]
def baseStart_4117106 : Nat := 118140960795 + 4117106 * 2 ^ 59
def prefixEnd_4117106 : Nat := 4983230072969 + 3 ^ 40 * 4117106 * 2
def baseEnd_4117106 : Nat := 1409369522339916025027187

theorem tailTrace_4117106 : CollatzResearch.WordTrace tailWord_4117106 prefixEnd_4117106 1409369522339916025027187 := by
  unfold tailWord_4117106
  simp only [CollatzResearch.WordTrace]
  refine ⟨37540798055608895642404793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100108794814957055046412781 37540798055608895642404793)
  ·
    refine ⟨28155598541706671731803595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37540798055608895642404793 28155598541706671731803595)
    ·
      refine ⟨42233397812560007597705393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28155598541706671731803595 42233397812560007597705393)
      ·
        refine ⟨31675048359420005698279045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42233397812560007597705393 31675048359420005698279045)
        ·
          refine ⟨5939071567391251068427321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31675048359420005698279045 5939071567391251068427321)
          ·
            refine ⟨4454303675543438301320491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5939071567391251068427321 4454303675543438301320491)
            ·
              refine ⟨6681455513315157451980737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4454303675543438301320491 6681455513315157451980737)
              ·
                refine ⟨5011091634986368088985553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6681455513315157451980737 5011091634986368088985553)
                ·
                  refine ⟨3758318726239776066739165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5011091634986368088985553 3758318726239776066739165)
                  ·
                    refine ⟨1409369522339916025027187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3758318726239776066739165 1409369522339916025027187)
                    ·
                      rfl

theorem cell22_4117106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 1, 2, 2, 3].length) (baseStart_4117106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4117106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4117106 prefixEnd_4117106 := by exact prefixLift 4117106
  have htrace : WordTrace (prefixWord ++ tailWord_4117106) baseStart_4117106 baseEnd_4117106 := by
    simpa [prefixWord, tailWord_4117106, baseEnd_4117106] using wordTrace_append hprefix tailTrace_4117106
  have hstable : (prefixWord ++ tailWord_4117106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4117106).length < 2 ^ (prefixWord ++ tailWord_4117106).sum := by decide
  have hdescent : baseEnd_4117106 < baseStart_4117106 := by decide
  rcases family_descends (prefixWord ++ tailWord_4117106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4117194 : List Nat := [3, 1, 2, 1, 4, 1, 3, 2, 1, 4]
def baseStart_4117194 : Nat := 118140960795 + 4117194 * 2 ^ 59
def prefixEnd_4117194 : Nat := 4983230072969 + 3 ^ 40 * 4117194 * 2
def baseEnd_4117194 : Nat := 1409399646538313128826917

theorem tailTrace_4117194 : CollatzResearch.WordTrace tailWord_4117194 prefixEnd_4117194 1409399646538313128826917 := by
  unfold tailWord_4117194
  simp only [CollatzResearch.WordTrace]
  refine ⟨37541600461529193399705659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100110934564077849065881757 37541600461529193399705659)
  ·
    refine ⟨56312400692293790099558489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37541600461529193399705659 56312400692293790099558489)
    ·
      refine ⟨42234300519220342574668867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56312400692293790099558489 42234300519220342574668867)
      ·
        refine ⟨63351450778830513862003301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42234300519220342574668867 63351450778830513862003301)
        ·
          refine ⟨11878397021030721349125619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63351450778830513862003301 11878397021030721349125619)
          ·
            refine ⟨17817595531546082023688429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11878397021030721349125619 17817595531546082023688429)
            ·
              refine ⟨6681598324329780758883161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17817595531546082023688429 6681598324329780758883161)
              ·
                refine ⟨5011198743247335569162371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6681598324329780758883161 5011198743247335569162371)
                ·
                  refine ⟨7516798114871003353743557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5011198743247335569162371 7516798114871003353743557)
                  ·
                    refine ⟨1409399646538313128826917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7516798114871003353743557 1409399646538313128826917)
                    ·
                      rfl

theorem cell22_4117194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 3, 2, 1, 4].length) (baseStart_4117194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4117194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4117194 prefixEnd_4117194 := by exact prefixLift 4117194
  have htrace : WordTrace (prefixWord ++ tailWord_4117194) baseStart_4117194 baseEnd_4117194 := by
    simpa [prefixWord, tailWord_4117194, baseEnd_4117194] using wordTrace_append hprefix tailTrace_4117194
  have hstable : (prefixWord ++ tailWord_4117194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4117194).length < 2 ^ (prefixWord ++ tailWord_4117194).sum := by decide
  have hdescent : baseEnd_4117194 < baseStart_4117194 := by decide
  rcases family_descends (prefixWord ++ tailWord_4117194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4117207 : List Nat := [1, 1, 3, 2, 1, 5, 1, 2, 1, 5]
def baseStart_4117207 : Nat := 118140960795 + 4117207 * 2 ^ 59
def prefixEnd_4117207 : Nat := 4983230072969 + 3 ^ 40 * 4117207 * 2
def baseEnd_4117207 : Nat := 1409404096703985428251877

theorem tailTrace_4117207 : CollatzResearch.WordTrace tailWord_4117207 prefixEnd_4117207 1409404096703985428251877 := by
  unfold tailWord_4117207
  simp only [CollatzResearch.WordTrace]
  refine ⟨150166875995069676819045875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100111250663379784546030583 150166875995069676819045875)
  ·
    refine ⟨225250313992604515228568813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150166875995069676819045875 225250313992604515228568813)
    ·
      refine ⟨84468867747226693210713305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 225250313992604515228568813 84468867747226693210713305)
      ·
        refine ⟨63351650810420019908034979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84468867747226693210713305 63351650810420019908034979)
        ·
          refine ⟨95027476215630029862052469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63351650810420019908034979 95027476215630029862052469)
          ·
            refine ⟨8908825895215315299567419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 95027476215630029862052469 8908825895215315299567419)
            ·
              refine ⟨13363238842822972949351129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8908825895215315299567419 13363238842822972949351129)
              ·
                refine ⟨10022429132117229712013347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13363238842822972949351129 10022429132117229712013347)
                ·
                  refine ⟨15033643698175844568020021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10022429132117229712013347 15033643698175844568020021)
                  ·
                    refine ⟨1409404096703985428251877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15033643698175844568020021 1409404096703985428251877)
                    ·
                      rfl

theorem cell22_4117207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 2, 1, 5].length) (baseStart_4117207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4117207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4117207 prefixEnd_4117207 := by exact prefixLift 4117207
  have htrace : WordTrace (prefixWord ++ tailWord_4117207) baseStart_4117207 baseEnd_4117207 := by
    simpa [prefixWord, tailWord_4117207, baseEnd_4117207] using wordTrace_append hprefix tailTrace_4117207
  have hstable : (prefixWord ++ tailWord_4117207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4117207).length < 2 ^ (prefixWord ++ tailWord_4117207).sum := by decide
  have hdescent : baseEnd_4117207 < baseStart_4117207 := by decide
  rcases family_descends (prefixWord ++ tailWord_4117207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4117220 : List Nat := [2, 3, 1, 1, 1, 14]
def baseStart_4117220 : Nat := 118140960795 + 4117220 * 2 ^ 59
def prefixEnd_4117220 : Nat := 4983230072969 + 3 ^ 40 * 4117220 * 2
def baseEnd_4117220 : Nat := 17400105516909354662677

theorem tailTrace_4117220 : CollatzResearch.WordTrace tailWord_4117220 prefixEnd_4117220 17400105516909354662677 := by
  unfold tailWord_4117220
  simp only [CollatzResearch.WordTrace]
  refine ⟨75083675072011290019634557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100111566762681720026179409 75083675072011290019634557)
  ·
    refine ⟨28156378152004233757362959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75083675072011290019634557 28156378152004233757362959)
    ·
      refine ⟨42234567228006350636044439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28156378152004233757362959 42234567228006350636044439)
      ·
        refine ⟨63351850842009525954066659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42234567228006350636044439 63351850842009525954066659)
        ·
          refine ⟨95027776263014288931099989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63351850842009525954066659 95027776263014288931099989)
          ·
            refine ⟨17400105516909354662677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 95027776263014288931099989 17400105516909354662677)
            ·
              rfl

theorem cell22_4117220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 14].length) (baseStart_4117220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4117220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4117220 prefixEnd_4117220 := by exact prefixLift 4117220
  have htrace : WordTrace (prefixWord ++ tailWord_4117220) baseStart_4117220 baseEnd_4117220 := by
    simpa [prefixWord, tailWord_4117220, baseEnd_4117220] using wordTrace_append hprefix tailTrace_4117220
  have hstable : (prefixWord ++ tailWord_4117220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4117220).length < 2 ^ (prefixWord ++ tailWord_4117220).sum := by decide
  have hdescent : baseEnd_4117220 < baseStart_4117220 := by decide
  rcases family_descends (prefixWord ++ tailWord_4117220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4117235 : List Nat := [1, 1, 1, 2, 2, 3, 1, 2, 2, 7]
def baseStart_4117235 : Nat := 118140960795 + 4117235 * 2 ^ 59
def prefixEnd_4117235 : Nat := 4983230072969 + 3 ^ 40 * 4117235 * 2
def baseEnd_4117235 : Nat := 1409413681676202688551791

theorem tailTrace_4117235 : CollatzResearch.WordTrace tailWord_4117235 prefixEnd_4117235 1409413681676202688551791 := by
  unfold tailWord_4117235
  simp only [CollatzResearch.WordTrace]
  refine ⟨150167897238968237601065159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100111931492645491734043439 150167897238968237601065159)
  ·
    refine ⟨225251845858452356401597739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150167897238968237601065159 225251845858452356401597739)
    ·
      refine ⟨337877768787678534602396609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225251845858452356401597739 337877768787678534602396609)
      ·
        refine ⟨253408326590758900951797457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 337877768787678534602396609 253408326590758900951797457)
        ·
          refine ⟨190056244943069175713848093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 253408326590758900951797457 190056244943069175713848093)
          ·
            refine ⟨71271091853650940892693035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 190056244943069175713848093 71271091853650940892693035)
            ·
              refine ⟨106906637780476411339039553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71271091853650940892693035 106906637780476411339039553)
              ·
                refine ⟨80179978335357308504279665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106906637780476411339039553 80179978335357308504279665)
                ·
                  refine ⟨60134983751517981378209749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80179978335357308504279665 60134983751517981378209749)
                  ·
                    refine ⟨1409413681676202688551791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60134983751517981378209749 1409413681676202688551791)
                    ·
                      rfl

theorem cell22_4117235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 2, 2, 7].length) (baseStart_4117235 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4117235 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4117235 prefixEnd_4117235 := by exact prefixLift 4117235
  have htrace : WordTrace (prefixWord ++ tailWord_4117235) baseStart_4117235 baseEnd_4117235 := by
    simpa [prefixWord, tailWord_4117235, baseEnd_4117235] using wordTrace_append hprefix tailTrace_4117235
  have hstable : (prefixWord ++ tailWord_4117235).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4117235).length < 2 ^ (prefixWord ++ tailWord_4117235).sum := by decide
  have hdescent : baseEnd_4117235 < baseStart_4117235 := by decide
  rcases family_descends (prefixWord ++ tailWord_4117235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4117297 : List Nat := [1, 2, 2, 3, 2, 1, 1, 3, 2, 5]
def baseStart_4117297 : Nat := 118140960795 + 4117297 * 2 ^ 59
def prefixEnd_4117297 : Nat := 4983230072969 + 3 ^ 40 * 4117297 * 2
def baseEnd_4117297 : Nat := 1409434905543255193501601

theorem tailTrace_4117297 : CollatzResearch.WordTrace tailWord_4117297 prefixEnd_4117297 1409434905543255193501601 := by
  unfold tailWord_4117297
  simp only [CollatzResearch.WordTrace]
  refine ⟨150170158564743622189822145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100113439043162414793214763 150170158564743622189822145)
  ·
    refine ⟨112627618923557716642366609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150170158564743622189822145 112627618923557716642366609)
    ·
      refine ⟨84470714192668287481774957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112627618923557716642366609 84470714192668287481774957)
      ·
        refine ⟨31676517822250607805665609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84470714192668287481774957 31676517822250607805665609)
        ·
          refine ⟨23757388366687955854249207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31676517822250607805665609 23757388366687955854249207)
          ·
            refine ⟨35636082550031933781373811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23757388366687955854249207 35636082550031933781373811)
            ·
              refine ⟨53454123825047900672060717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35636082550031933781373811 53454123825047900672060717)
              ·
                refine ⟨20045296434392962752022769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53454123825047900672060717 20045296434392962752022769)
                ·
                  refine ⟨15033972325794722064017077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20045296434392962752022769 15033972325794722064017077)
                  ·
                    refine ⟨1409434905543255193501601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15033972325794722064017077 1409434905543255193501601)
                    ·
                      rfl

theorem cell22_4117297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 3, 2, 5].length) (baseStart_4117297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4117297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4117297 prefixEnd_4117297 := by exact prefixLift 4117297
  have htrace : WordTrace (prefixWord ++ tailWord_4117297) baseStart_4117297 baseEnd_4117297 := by
    simpa [prefixWord, tailWord_4117297, baseEnd_4117297] using wordTrace_append hprefix tailTrace_4117297
  have hstable : (prefixWord ++ tailWord_4117297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4117297).length < 2 ^ (prefixWord ++ tailWord_4117297).sum := by decide
  have hdescent : baseEnd_4117297 < baseStart_4117297 := by decide
  rcases family_descends (prefixWord ++ tailWord_4117297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4117312 : List Nat := [2, 1, 1, 2, 2, 1, 1, 5, 3, 4]
def baseStart_4117312 : Nat := 118140960795 + 4117312 * 2 ^ 59
def prefixEnd_4117312 : Nat := 4983230072969 + 3 ^ 40 * 4117312 * 2
def baseEnd_4117312 : Nat := 1409440040349800154376555

theorem tailTrace_4117312 : CollatzResearch.WordTrace tailWord_4117312 prefixEnd_4117312 1409440040349800154376555 := by
  unfold tailWord_4117312
  simp only [CollatzResearch.WordTrace]
  refine ⟨75085352829844639875809095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100113803773126186501078793 75085352829844639875809095)
  ·
    refine ⟨112628029244766959813713643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75085352829844639875809095 112628029244766959813713643)
    ·
      refine ⟨168942043867150439720570465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112628029244766959813713643 168942043867150439720570465)
      ·
        refine ⟨126706532900362829790427849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168942043867150439720570465 126706532900362829790427849)
        ·
          refine ⟨95029899675272122342820887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126706532900362829790427849 95029899675272122342820887)
          ·
            refine ⟨142544849512908183514231331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95029899675272122342820887 142544849512908183514231331)
            ·
              refine ⟨213817274269362275271346997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142544849512908183514231331 213817274269362275271346997)
              ·
                refine ⟨20045369462752713306688781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 213817274269362275271346997 20045369462752713306688781)
                ·
                  refine ⟨7517013548532267490008293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20045369462752713306688781 7517013548532267490008293)
                  ·
                    refine ⟨1409440040349800154376555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7517013548532267490008293 1409440040349800154376555)
                    ·
                      rfl

theorem cell22_4117312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 5, 3, 4].length) (baseStart_4117312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4117312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4117312 prefixEnd_4117312 := by exact prefixLift 4117312
  have htrace : WordTrace (prefixWord ++ tailWord_4117312) baseStart_4117312 baseEnd_4117312 := by
    simpa [prefixWord, tailWord_4117312, baseEnd_4117312] using wordTrace_append hprefix tailTrace_4117312
  have hstable : (prefixWord ++ tailWord_4117312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4117312).length < 2 ^ (prefixWord ++ tailWord_4117312).sum := by decide
  have hdescent : baseEnd_4117312 < baseStart_4117312 := by decide
  rcases family_descends (prefixWord ++ tailWord_4117312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
