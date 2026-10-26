import V185TrunkScan23Chunk0206

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1224319 : List Nat := [1, 1, 2, 2, 1, 1, 1, 2, 1, 11]
def baseStart_1224319 : Nat := 118140960795 + 1224319 * 2 ^ 59
def prefixEnd_1224319 : Nat := 4983230072969 + 3 ^ 40 * 1224319 * 2
def baseEnd_1224319 : Nat := 209554707144033526660655

theorem tailTrace_1224319 : CollatzResearch.WordTrace tailWord_1224319 prefixEnd_1224319 209554707144033526660655 := by
  unfold tailWord_1224319
  simp only [CollatzResearch.WordTrace]
  refine ⟨44654582451508834883244011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29769721634339223255496007 44654582451508834883244011)
  ·
    refine ⟨66981873677263252324866017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44654582451508834883244011 66981873677263252324866017)
    ·
      refine ⟨50236405257947439243649513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66981873677263252324866017 50236405257947439243649513)
      ·
        refine ⟨37677303943460579432737135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50236405257947439243649513 37677303943460579432737135)
        ·
          refine ⟨56515955915190869149105703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37677303943460579432737135 56515955915190869149105703)
          ·
            refine ⟨84773933872786303723658555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56515955915190869149105703 84773933872786303723658555)
            ·
              refine ⟨127160900809179455585487833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84773933872786303723658555 127160900809179455585487833)
              ·
                refine ⟨95370675606884591689115875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 127160900809179455585487833 95370675606884591689115875)
                ·
                  refine ⟨143056013410326887533673813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 95370675606884591689115875 143056013410326887533673813)
                  ·
                    refine ⟨209554707144033526660655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 143056013410326887533673813 209554707144033526660655)
                    ·
                      rfl

theorem cell23_1224319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 11].length) (baseStart_1224319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1224319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1224319 prefixEnd_1224319 := by exact prefixLift 1224319
  have htrace : WordTrace (prefixWord ++ tailWord_1224319) baseStart_1224319 baseEnd_1224319 := by
    simpa [prefixWord, tailWord_1224319, baseEnd_1224319] using wordTrace_append hprefix tailTrace_1224319
  have hstable : (prefixWord ++ tailWord_1224319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1224319).length < 2 ^ (prefixWord ++ tailWord_1224319).sum := by decide
  have hdescent : baseEnd_1224319 < baseStart_1224319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1224319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1224327 : List Nat := [1, 1, 4, 2, 1, 4, 3, 2, 1, 4]
def baseStart_1224327 : Nat := 118140960795 + 1224327 * 2 ^ 59
def prefixEnd_1224327 : Nat := 4983230072969 + 3 ^ 40 * 1224327 * 2
def baseEnd_1224327 : Nat := 209556076425778849560643

theorem tailTrace_1224327 : CollatzResearch.WordTrace tailWord_1224327 prefixEnd_1224327 209556076425778849560643 := by
  unfold tailWord_1224327
  simp only [CollatzResearch.WordTrace]
  refine ⟨44654874235479852249535235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29769916156986568166356823 44654874235479852249535235)
  ·
    refine ⟨66982311353219778374302853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44654874235479852249535235 66982311353219778374302853)
    ·
      refine ⟨12559183378728708445181785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66982311353219778374302853 12559183378728708445181785)
      ·
        refine ⟨9419387534046531333886339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12559183378728708445181785 9419387534046531333886339)
        ·
          refine ⟨14129081301069797000829509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9419387534046531333886339 14129081301069797000829509)
          ·
            refine ⟨2649202743950586937655533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14129081301069797000829509 2649202743950586937655533)
            ·
              refine ⟨993451028981470101620825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2649202743950586937655533 993451028981470101620825)
              ·
                refine ⟨745088271736102576215619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 993451028981470101620825 745088271736102576215619)
                ·
                  refine ⟨1117632407604153864323429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 745088271736102576215619 1117632407604153864323429)
                  ·
                    refine ⟨209556076425778849560643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1117632407604153864323429 209556076425778849560643)
                    ·
                      rfl

theorem cell23_1224327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 3, 2, 1, 4].length) (baseStart_1224327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1224327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1224327 prefixEnd_1224327 := by exact prefixLift 1224327
  have htrace : WordTrace (prefixWord ++ tailWord_1224327) baseStart_1224327 baseEnd_1224327 := by
    simpa [prefixWord, tailWord_1224327, baseEnd_1224327] using wordTrace_append hprefix tailTrace_1224327
  have hstable : (prefixWord ++ tailWord_1224327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1224327).length < 2 ^ (prefixWord ++ tailWord_1224327).sum := by decide
  have hdescent : baseEnd_1224327 < baseStart_1224327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1224327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1224340 : List Nat := [2, 4, 2, 2, 2, 1, 1, 3, 6]
def baseStart_1224340 : Nat := 118140960795 + 1224340 * 2 ^ 59
def prefixEnd_1224340 : Nat := 4983230072969 + 3 ^ 40 * 1224340 * 2
def baseEnd_1224340 : Nat := 69852767169538333091041

theorem tailTrace_1224340 : CollatzResearch.WordTrace tailWord_1224340 prefixEnd_1224340 69852767169538333091041 := by
  unfold tailWord_1224340
  simp only [CollatzResearch.WordTrace]
  refine ⟨22327674192216377734879237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29770232256288503646505649 22327674192216377734879237)
  ·
    refine ⟨4186438911040570825289857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22327674192216377734879237 4186438911040570825289857)
    ·
      refine ⟨3139829183280428118967393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4186438911040570825289857 3139829183280428118967393)
      ·
        refine ⟨2354871887460321089225545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3139829183280428118967393 2354871887460321089225545)
        ·
          refine ⟨1766153915595240816919159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2354871887460321089225545 1766153915595240816919159)
          ·
            refine ⟨2649230873392861225378739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1766153915595240816919159 2649230873392861225378739)
            ·
              refine ⟨3973846310089291838068109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2649230873392861225378739 3973846310089291838068109)
              ·
                refine ⟨1490192366283484439275541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3973846310089291838068109 1490192366283484439275541)
                ·
                  refine ⟨69852767169538333091041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1490192366283484439275541 69852767169538333091041)
                  ·
                    rfl

theorem cell23_1224340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 3, 6].length) (baseStart_1224340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1224340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1224340 prefixEnd_1224340 := by exact prefixLift 1224340
  have htrace : WordTrace (prefixWord ++ tailWord_1224340) baseStart_1224340 baseEnd_1224340 := by
    simpa [prefixWord, tailWord_1224340, baseEnd_1224340] using wordTrace_append hprefix tailTrace_1224340
  have hstable : (prefixWord ++ tailWord_1224340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1224340).length < 2 ^ (prefixWord ++ tailWord_1224340).sum := by decide
  have hdescent : baseEnd_1224340 < baseStart_1224340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1224340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1224353 : List Nat := [1, 2, 3, 3, 2, 2, 1, 1, 3, 5]
def baseStart_1224353 : Nat := 118140960795 + 1224353 * 2 ^ 59
def prefixEnd_1224353 : Nat := 4983230072969 + 3 ^ 40 * 1224353 * 2
def baseEnd_1224353 : Nat := 209560526591451148985603

theorem tailTrace_1224353 : CollatzResearch.WordTrace tailWord_1224353 prefixEnd_1224353 209560526591451148985603 := by
  unfold tailWord_1224353
  simp only [CollatzResearch.WordTrace]
  refine ⟨44655822533385658689981713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29770548355590439126654475 44655822533385658689981713)
  ·
    refine ⟨33491866900039244017486285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44655822533385658689981713 33491866900039244017486285)
    ·
      refine ⟨12559450087514716506557357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33491866900039244017486285 12559450087514716506557357)
      ·
        refine ⟨4709793782818018689959009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12559450087514716506557357 4709793782818018689959009)
        ·
          refine ⟨3532345337113514017469257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4709793782818018689959009 3532345337113514017469257)
          ·
            refine ⟨2649259002835135513101943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3532345337113514017469257 2649259002835135513101943)
            ·
              refine ⟨3973888504252703269652915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2649259002835135513101943 3973888504252703269652915)
              ·
                refine ⟨5960832756379054904479373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3973888504252703269652915 5960832756379054904479373)
                ·
                  refine ⟨2235312283642145589179765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5960832756379054904479373 2235312283642145589179765)
                  ·
                    refine ⟨209560526591451148985603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2235312283642145589179765 209560526591451148985603)
                    ·
                      rfl

theorem cell23_1224353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 1, 3, 5].length) (baseStart_1224353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1224353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1224353 prefixEnd_1224353 := by exact prefixLift 1224353
  have htrace : WordTrace (prefixWord ++ tailWord_1224353) baseStart_1224353 baseEnd_1224353 := by
    simpa [prefixWord, tailWord_1224353, baseEnd_1224353] using wordTrace_append hprefix tailTrace_1224353
  have hstable : (prefixWord ++ tailWord_1224353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1224353).length < 2 ^ (prefixWord ++ tailWord_1224353).sum := by decide
  have hdescent : baseEnd_1224353 < baseStart_1224353 := by decide
  rcases family_descends (prefixWord ++ tailWord_1224353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1224424 : List Nat := [2, 1, 4, 1, 3, 1, 1, 5, 1, 2, 2]
def baseStart_1224424 : Nat := 118140960795 + 1224424 * 2 ^ 59
def prefixEnd_1224424 : Nat := 4983230072969 + 3 ^ 40 * 1224424 * 2
def baseEnd_1224424 : Nat := 628718036900822669168983

theorem tailTrace_1224424 : CollatzResearch.WordTrace tailWord_1224424 prefixEnd_1224424 628718036900822669168983 := by
  unfold tailWord_1224424
  simp only [CollatzResearch.WordTrace]
  refine ⟨22329206058064218907908163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29772274744085625210544217 22329206058064218907908163)
  ·
    refine ⟨33493809087096328361862245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22329206058064218907908163 33493809087096328361862245)
    ·
      refine ⟨6280089203830561567849171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33493809087096328361862245 6280089203830561567849171)
      ·
        refine ⟨9420133805745842351773757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6280089203830561567849171 9420133805745842351773757)
        ·
          refine ⟨3532550177154690881915159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9420133805745842351773757 3532550177154690881915159)
          ·
            refine ⟨5298825265732036322872739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3532550177154690881915159 5298825265732036322872739)
            ·
              refine ⟨7948237898598054484309109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5298825265732036322872739 7948237898598054484309109)
              ·
                refine ⟨745147302993567607903979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7948237898598054484309109 745147302993567607903979)
                ·
                  refine ⟨1117720954490351411855969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 745147302993567607903979 1117720954490351411855969)
                  ·
                    refine ⟨838290715867763558891977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1117720954490351411855969 838290715867763558891977)
                    ·
                      refine ⟨628718036900822669168983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 838290715867763558891977 628718036900822669168983)
                      ·
                        rfl

theorem cell23_1224424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 5, 1, 2, 2].length) (baseStart_1224424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1224424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1224424 prefixEnd_1224424 := by exact prefixLift 1224424
  have htrace : WordTrace (prefixWord ++ tailWord_1224424) baseStart_1224424 baseEnd_1224424 := by
    simpa [prefixWord, tailWord_1224424, baseEnd_1224424] using wordTrace_append hprefix tailTrace_1224424
  have hstable : (prefixWord ++ tailWord_1224424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1224424).length < 2 ^ (prefixWord ++ tailWord_1224424).sum := by decide
  have hdescent : baseEnd_1224424 < baseStart_1224424 := by decide
  rcases family_descends (prefixWord ++ tailWord_1224424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1224440 : List Nat := [2, 1, 2, 1, 1, 2, 2, 6, 2, 1, 3]
def baseStart_1224440 : Nat := 118140960795 + 1224440 * 2 ^ 59
def prefixEnd_1224440 : Nat := 4983230072969 + 3 ^ 40 * 1224440 * 2
def baseEnd_1224440 : Nat := 628726252591294606568909

theorem tailTrace_1224440 : CollatzResearch.WordTrace tailWord_1224440 prefixEnd_1224440 628726252591294606568909 := by
  unfold tailWord_1224440
  simp only [CollatzResearch.WordTrace]
  refine ⟨22329497842035236274199387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29772663789380315032265849 22329497842035236274199387)
  ·
    refine ⟨33494246763052854411299081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22329497842035236274199387 33494246763052854411299081)
    ·
      refine ⟨25120685072289640808474311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33494246763052854411299081 25120685072289640808474311)
      ·
        refine ⟨37681027608434461212711467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25120685072289640808474311 37681027608434461212711467)
        ·
          refine ⟨56521541412651691819067201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37681027608434461212711467 56521541412651691819067201)
          ·
            refine ⟨42391156059488768864300401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56521541412651691819067201 42391156059488768864300401)
            ·
              refine ⟨31793367044616576648225301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42391156059488768864300401 31793367044616576648225301)
              ·
                refine ⟨1490314080216402030385561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 31793367044616576648225301 1490314080216402030385561)
                ·
                  refine ⟨1117735560162301522789171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1490314080216402030385561 1117735560162301522789171)
                  ·
                    refine ⟨1676603340243452284183757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1117735560162301522789171 1676603340243452284183757)
                    ·
                      refine ⟨628726252591294606568909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1676603340243452284183757 628726252591294606568909)
                      ·
                        rfl

theorem cell23_1224440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 6, 2, 1, 3].length) (baseStart_1224440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1224440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1224440 prefixEnd_1224440 := by exact prefixLift 1224440
  have htrace : WordTrace (prefixWord ++ tailWord_1224440) baseStart_1224440 baseEnd_1224440 := by
    simpa [prefixWord, tailWord_1224440, baseEnd_1224440] using wordTrace_append hprefix tailTrace_1224440
  have hstable : (prefixWord ++ tailWord_1224440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1224440).length < 2 ^ (prefixWord ++ tailWord_1224440).sum := by decide
  have hdescent : baseEnd_1224440 < baseStart_1224440 := by decide
  rcases family_descends (prefixWord ++ tailWord_1224440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1224480 : List Nat := [2, 1, 1, 5, 1, 1, 2, 1, 3, 4, 2]
def baseStart_1224480 : Nat := 118140960795 + 1224480 * 2 ^ 59
def prefixEnd_1224480 : Nat := 4983230072969 + 3 ^ 40 * 1224480 * 2
def baseEnd_1224480 : Nat := 628746791817474450068725

theorem tailTrace_1224480 : CollatzResearch.WordTrace tailWord_1224480 prefixEnd_1224480 628746791817474450068725 := by
  unfold tailWord_1224480
  simp only [CollatzResearch.WordTrace]
  refine ⟨22330227301962779689927447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29773636402617039586569929 22330227301962779689927447)
  ·
    refine ⟨33495340952944169534891171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22330227301962779689927447 33495340952944169534891171)
    ·
      refine ⟨50243011429416254302336757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33495340952944169534891171 50243011429416254302336757)
      ·
        refine ⟨4710282321507773840844071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 50243011429416254302336757 4710282321507773840844071)
        ·
          refine ⟨7065423482261660761266107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4710282321507773840844071 7065423482261660761266107)
          ·
            refine ⟨10598135223392491141899161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7065423482261660761266107 10598135223392491141899161)
            ·
              refine ⟨7948601417544368356424371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10598135223392491141899161 7948601417544368356424371)
              ·
                refine ⟨11922902126316552534636557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7948601417544368356424371 11922902126316552534636557)
                ·
                  refine ⟨4471088297368707200488709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11922902126316552534636557 4471088297368707200488709)
                  ·
                    refine ⟨838329055756632600091633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4471088297368707200488709 838329055756632600091633)
                    ·
                      refine ⟨628746791817474450068725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 838329055756632600091633 628746791817474450068725)
                      ·
                        rfl

theorem cell23_1224480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 1, 3, 4, 2].length) (baseStart_1224480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1224480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1224480 prefixEnd_1224480 := by exact prefixLift 1224480
  have htrace : WordTrace (prefixWord ++ tailWord_1224480) baseStart_1224480 baseEnd_1224480 := by
    simpa [prefixWord, tailWord_1224480, baseEnd_1224480] using wordTrace_append hprefix tailTrace_1224480
  have hstable : (prefixWord ++ tailWord_1224480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1224480).length < 2 ^ (prefixWord ++ tailWord_1224480).sum := by decide
  have hdescent : baseEnd_1224480 < baseStart_1224480 := by decide
  rcases family_descends (prefixWord ++ tailWord_1224480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1224497 : List Nat := [1, 2, 2, 3, 2, 2, 2, 1, 4, 2, 2]
def baseStart_1224497 : Nat := 118140960795 + 1224497 * 2 ^ 59
def prefixEnd_1224497 : Nat := 4983230072969 + 3 ^ 40 * 1224497 * 2
def baseEnd_1224497 : Nat := 628755520988600883556147

theorem tailTrace_1224497 : CollatzResearch.WordTrace tailWord_1224497 prefixEnd_1224497 628755520988600883556147 := by
  unfold tailWord_1224497
  simp only [CollatzResearch.WordTrace]
  refine ⟨44661074644863971283223745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29774049763242647522149163 44661074644863971283223745)
  ·
    refine ⟨33495805983647978462417809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44661074644863971283223745 33495805983647978462417809)
    ·
      refine ⟨25121854487735983846813357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33495805983647978462417809 25121854487735983846813357)
      ·
        refine ⟨9420695432900993942555009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25121854487735983846813357 9420695432900993942555009)
        ·
          refine ⟨7065521574675745456916257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9420695432900993942555009 7065521574675745456916257)
          ·
            refine ⟨5299141181006809092687193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7065521574675745456916257 5299141181006809092687193)
            ·
              refine ⟨3974355885755106819515395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5299141181006809092687193 3974355885755106819515395)
              ·
                refine ⟨5961533828632660229273093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3974355885755106819515395 5961533828632660229273093)
                ·
                  refine ⟨1117787592868623792988705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5961533828632660229273093 1117787592868623792988705)
                  ·
                    refine ⟨838340694651467844741529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1117787592868623792988705 838340694651467844741529)
                    ·
                      refine ⟨628755520988600883556147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 838340694651467844741529 628755520988600883556147)
                      ·
                        rfl

theorem cell23_1224497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 1, 4, 2, 2].length) (baseStart_1224497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1224497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1224497 prefixEnd_1224497 := by exact prefixLift 1224497
  have htrace : WordTrace (prefixWord ++ tailWord_1224497) baseStart_1224497 baseEnd_1224497 := by
    simpa [prefixWord, tailWord_1224497, baseEnd_1224497] using wordTrace_append hprefix tailTrace_1224497
  have hstable : (prefixWord ++ tailWord_1224497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1224497).length < 2 ^ (prefixWord ++ tailWord_1224497).sum := by decide
  have hdescent : baseEnd_1224497 < baseStart_1224497 := by decide
  rcases family_descends (prefixWord ++ tailWord_1224497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1224518 : List Nat := [6, 1, 1, 2, 1, 3, 1, 2, 1, 3, 2]
def baseStart_1224518 : Nat := 118140960795 + 1224518 * 2 ^ 59
def prefixEnd_1224518 : Nat := 4983230072969 + 3 ^ 40 * 1224518 * 2
def baseEnd_1224518 : Nat := 628766304082345301393551

theorem tailTrace_1224518 : CollatzResearch.WordTrace tailWord_1224518 prefixEnd_1224518 628766304082345301393551 := by
  unfold tailWord_1224518
  simp only [CollatzResearch.WordTrace]
  refine ⟨1395682518055871620929319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 29774560385191927913158805 1395682518055871620929319)
  ·
    refine ⟨2093523777083807431393979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1395682518055871620929319 2093523777083807431393979)
    ·
      refine ⟨3140285665625711147090969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2093523777083807431393979 3140285665625711147090969)
      ·
        refine ⟨2355214249219283360318227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3140285665625711147090969 2355214249219283360318227)
        ·
          refine ⟨3532821373828925040477341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2355214249219283360318227 3532821373828925040477341)
          ·
            refine ⟨1324808015185846890179003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3532821373828925040477341 1324808015185846890179003)
            ·
              refine ⟨1987212022778770335268505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1324808015185846890179003 1987212022778770335268505)
              ·
                refine ⟨1490409017084077751451379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1987212022778770335268505 1490409017084077751451379)
                ·
                  refine ⟨2235613525626116627177069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1490409017084077751451379 2235613525626116627177069)
                  ·
                    refine ⟨838355072109793735191401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2235613525626116627177069 838355072109793735191401)
                    ·
                      refine ⟨628766304082345301393551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 838355072109793735191401 628766304082345301393551)
                      ·
                        rfl

theorem cell23_1224518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 1, 2, 1, 3, 2].length) (baseStart_1224518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1224518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1224518 prefixEnd_1224518 := by exact prefixLift 1224518
  have htrace : WordTrace (prefixWord ++ tailWord_1224518) baseStart_1224518 baseEnd_1224518 := by
    simpa [prefixWord, tailWord_1224518, baseEnd_1224518] using wordTrace_append hprefix tailTrace_1224518
  have hstable : (prefixWord ++ tailWord_1224518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1224518).length < 2 ^ (prefixWord ++ tailWord_1224518).sum := by decide
  have hdescent : baseEnd_1224518 < baseStart_1224518 := by decide
  rcases family_descends (prefixWord ++ tailWord_1224518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1224543 : List Nat := [1, 1, 2, 3, 1, 4, 1, 2, 1, 2, 5]
def baseStart_1224543 : Nat := 118140960795 + 1224543 * 2 ^ 59
def prefixEnd_1224543 : Nat := 4983230072969 + 3 ^ 40 * 1224543 * 2
def baseEnd_1224543 : Nat := 628779141098707703580935

theorem tailTrace_1224543 : CollatzResearch.WordTrace tailWord_1224543 prefixEnd_1224543 628779141098707703580935 := by
  unfold tailWord_1224543
  simp only [CollatzResearch.WordTrace]
  refine ⟨44662752402697321139398283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29775168268464880759598855 44662752402697321139398283)
  ·
    refine ⟨66994128604045981709097425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44662752402697321139398283 66994128604045981709097425)
    ·
      refine ⟨50245596453034486281823069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66994128604045981709097425 50245596453034486281823069)
      ·
        refine ⟨18842098669887932355683651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50245596453034486281823069 18842098669887932355683651)
        ·
          refine ⟨28263148004831898533525477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18842098669887932355683651 28263148004831898533525477)
          ·
            refine ⟨5299340250905980975036027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28263148004831898533525477 5299340250905980975036027)
            ·
              refine ⟨7949010376358971462554041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5299340250905980975036027 7949010376358971462554041)
              ·
                refine ⟨5961757782269228596915531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7949010376358971462554041 5961757782269228596915531)
                ·
                  refine ⟨8942636673403842895373297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5961757782269228596915531 8942636673403842895373297)
                  ·
                    refine ⟨6706977505052882171529973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8942636673403842895373297 6706977505052882171529973)
                    ·
                      refine ⟨628779141098707703580935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6706977505052882171529973 628779141098707703580935)
                      ·
                        rfl

theorem cell23_1224543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 2, 1, 2, 5].length) (baseStart_1224543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1224543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1224543 prefixEnd_1224543 := by exact prefixLift 1224543
  have htrace : WordTrace (prefixWord ++ tailWord_1224543) baseStart_1224543 baseEnd_1224543 := by
    simpa [prefixWord, tailWord_1224543, baseEnd_1224543] using wordTrace_append hprefix tailTrace_1224543
  have hstable : (prefixWord ++ tailWord_1224543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1224543).length < 2 ^ (prefixWord ++ tailWord_1224543).sum := by decide
  have hdescent : baseEnd_1224543 < baseStart_1224543 := by decide
  rcases family_descends (prefixWord ++ tailWord_1224543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1224554 : List Nat := [3, 1, 3, 4, 1, 1, 1, 4, 5]
def baseStart_1224554 : Nat := 118140960795 + 1224554 * 2 ^ 59
def prefixEnd_1224554 : Nat := 4983230072969 + 3 ^ 40 * 1224554 * 2
def baseEnd_1224554 : Nat := 69864976598434128949265

theorem tailTrace_1224554 : CollatzResearch.WordTrace tailWord_1224554 prefixEnd_1224554 69864976598434128949265 := by
  unfold tailWord_1224554
  simp only [CollatzResearch.WordTrace]
  refine ⟨11165788401414367504512179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29775435737104980012032477 11165788401414367504512179)
  ·
    refine ⟨16748682602121551256768269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11165788401414367504512179 16748682602121551256768269)
    ·
      refine ⟨6280755975795581721288101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16748682602121551256768269 6280755975795581721288101)
      ·
        refine ⟨1177641745461671572741519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6280755975795581721288101 1177641745461671572741519)
        ·
          refine ⟨1766462618192507359112279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1177641745461671572741519 1766462618192507359112279)
          ·
            refine ⟨2649693927288761038668419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1766462618192507359112279 2649693927288761038668419)
            ·
              refine ⟨3974540890933141558002629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2649693927288761038668419 3974540890933141558002629)
              ·
                refine ⟨745226417049964042125493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3974540890933141558002629 745226417049964042125493)
                ·
                  refine ⟨69864976598434128949265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 745226417049964042125493 69864976598434128949265)
                  ·
                    rfl

theorem cell23_1224554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 4, 5].length) (baseStart_1224554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1224554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1224554 prefixEnd_1224554 := by exact prefixLift 1224554
  have htrace : WordTrace (prefixWord ++ tailWord_1224554) baseStart_1224554 baseEnd_1224554 := by
    simpa [prefixWord, tailWord_1224554, baseEnd_1224554] using wordTrace_append hprefix tailTrace_1224554
  have hstable : (prefixWord ++ tailWord_1224554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1224554).length < 2 ^ (prefixWord ++ tailWord_1224554).sum := by decide
  have hdescent : baseEnd_1224554 < baseStart_1224554 := by decide
  rcases family_descends (prefixWord ++ tailWord_1224554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1224570 : List Nat := [3, 1, 1, 1, 1, 1, 5, 1, 1, 6, 2]
def baseStart_1224570 : Nat := 118140960795 + 1224570 * 2 ^ 59
def prefixEnd_1224570 : Nat := 4983230072969 + 3 ^ 40 * 1224570 * 2
def baseEnd_1224570 : Nat := 628793005076379097943311

theorem tailTrace_1224570 : CollatzResearch.WordTrace tailWord_1224570 prefixEnd_1224570 628793005076379097943311 := by
  unfold tailWord_1224570
  simp only [CollatzResearch.WordTrace]
  refine ⟨11165934293399876187657791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29775824782399669833754109 11165934293399876187657791)
  ·
    refine ⟨16748901440099814281486687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11165934293399876187657791 16748901440099814281486687)
    ·
      refine ⟨25123352160149721422230031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16748901440099814281486687 25123352160149721422230031)
      ·
        refine ⟨37685028240224582133345047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25123352160149721422230031 37685028240224582133345047)
        ·
          refine ⟨56527542360336873200017571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37685028240224582133345047 56527542360336873200017571)
          ·
            refine ⟨84791313540505309800026357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56527542360336873200017571 84791313540505309800026357)
            ·
              refine ⟨7949185644422372793752471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 84791313540505309800026357 7949185644422372793752471)
              ·
                refine ⟨11923778466633559190628707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7949185644422372793752471 11923778466633559190628707)
                ·
                  refine ⟨17885667699950338785943061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11923778466633559190628707 17885667699950338785943061)
                  ·
                    refine ⟨838390673435172130591081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17885667699950338785943061 838390673435172130591081)
                    ·
                      refine ⟨628793005076379097943311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 838390673435172130591081 628793005076379097943311)
                      ·
                        rfl

theorem cell23_1224570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 1, 1, 6, 2].length) (baseStart_1224570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1224570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1224570 prefixEnd_1224570 := by exact prefixLift 1224570
  have htrace : WordTrace (prefixWord ++ tailWord_1224570) baseStart_1224570 baseEnd_1224570 := by
    simpa [prefixWord, tailWord_1224570, baseEnd_1224570] using wordTrace_append hprefix tailTrace_1224570
  have hstable : (prefixWord ++ tailWord_1224570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1224570).length < 2 ^ (prefixWord ++ tailWord_1224570).sum := by decide
  have hdescent : baseEnd_1224570 < baseStart_1224570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1224570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1224580 : List Nat := [2, 3, 2, 1, 1, 1, 3, 1, 5, 4]
def baseStart_1224580 : Nat := 118140960795 + 1224580 * 2 ^ 59
def prefixEnd_1224580 : Nat := 4983230072969 + 3 ^ 40 * 1224580 * 2
def baseEnd_1224580 : Nat := 209599379960974686272755

theorem tailTrace_1224580 : CollatzResearch.WordTrace tailWord_1224580 prefixEnd_1224580 209599379960974686272755 := by
  unfold tailWord_1224580
  simp only [CollatzResearch.WordTrace]
  refine ⟨22332050951781638229247597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29776067935708850972330129 22332050951781638229247597)
  ·
    refine ⟨8374519106918114335967849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22332050951781638229247597 8374519106918114335967849)
    ·
      refine ⟨6280889330188585751975887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8374519106918114335967849 6280889330188585751975887)
      ·
        refine ⟨9421333995282878627963831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6280889330188585751975887 9421333995282878627963831)
        ·
          refine ⟨14132000992924317941945747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9421333995282878627963831 14132000992924317941945747)
          ·
            refine ⟨21198001489386476912918621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14132000992924317941945747 21198001489386476912918621)
            ·
              refine ⟨7949250558519928842344483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21198001489386476912918621 7949250558519928842344483)
              ·
                refine ⟨11923875837779893263516725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7949250558519928842344483 11923875837779893263516725)
                ·
                  refine ⟨1117863359791864993454693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11923875837779893263516725 1117863359791864993454693)
                  ·
                    refine ⟨209599379960974686272755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1117863359791864993454693 209599379960974686272755)
                    ·
                      rfl

theorem cell23_1224580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 1, 5, 4].length) (baseStart_1224580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1224580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1224580 prefixEnd_1224580 := by exact prefixLift 1224580
  have htrace : WordTrace (prefixWord ++ tailWord_1224580) baseStart_1224580 baseEnd_1224580 := by
    simpa [prefixWord, tailWord_1224580, baseEnd_1224580] using wordTrace_append hprefix tailTrace_1224580
  have hstable : (prefixWord ++ tailWord_1224580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1224580).length < 2 ^ (prefixWord ++ tailWord_1224580).sum := by decide
  have hdescent : baseEnd_1224580 < baseStart_1224580 := by decide
  rcases family_descends (prefixWord ++ tailWord_1224580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1224584 : List Nat := [2, 1, 3, 3, 4, 1, 1, 1, 2, 5]
def baseStart_1224584 : Nat := 118140960795 + 1224584 * 2 ^ 59
def prefixEnd_1224584 : Nat := 4983230072969 + 3 ^ 40 * 1224584 * 2
def baseEnd_1224584 : Nat := 209600064601847347722749

theorem tailTrace_1224584 : CollatzResearch.WordTrace tailWord_1224584 prefixEnd_1224584 209600064601847347722749 := by
  unfold tailWord_1224584
  simp only [CollatzResearch.WordTrace]
  refine ⟨22332123897774392570820403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29776165197032523427760537 22332123897774392570820403)
  ·
    refine ⟨33498185846661588856230605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22332123897774392570820403 33498185846661588856230605)
    ·
      refine ⟨12561819692498095821086477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33498185846661588856230605 12561819692498095821086477)
      ·
        refine ⟨4710682384686785932907429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12561819692498095821086477 4710682384686785932907429)
        ·
          refine ⟨883252947128772362420143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4710682384686785932907429 883252947128772362420143)
          ·
            refine ⟨1324879420693158543630215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 883252947128772362420143 1324879420693158543630215)
            ·
              refine ⟨1987319131039737815445323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1324879420693158543630215 1987319131039737815445323)
              ·
                refine ⟨2980978696559606723167985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1987319131039737815445323 2980978696559606723167985)
                ·
                  refine ⟨2235734022419705042375989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2980978696559606723167985 2235734022419705042375989)
                  ·
                    refine ⟨209600064601847347722749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2235734022419705042375989 209600064601847347722749)
                    ·
                      rfl

theorem cell23_1224584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 1, 1, 2, 5].length) (baseStart_1224584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1224584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1224584 prefixEnd_1224584 := by exact prefixLift 1224584
  have htrace : WordTrace (prefixWord ++ tailWord_1224584) baseStart_1224584 baseEnd_1224584 := by
    simpa [prefixWord, tailWord_1224584, baseEnd_1224584] using wordTrace_append hprefix tailTrace_1224584
  have hstable : (prefixWord ++ tailWord_1224584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1224584).length < 2 ^ (prefixWord ++ tailWord_1224584).sum := by decide
  have hdescent : baseEnd_1224584 < baseStart_1224584 := by decide
  rcases family_descends (prefixWord ++ tailWord_1224584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1224647 : List Nat := [1, 1, 4, 1, 1, 2, 1, 5, 2, 3, 2]
def baseStart_1224647 : Nat := 118140960795 + 1224647 * 2 ^ 59
def prefixEnd_1224647 : Nat := 4983230072969 + 3 ^ 40 * 1224647 * 2
def baseEnd_1224647 : Nat := 628832543086775296680457

theorem tailTrace_1224647 : CollatzResearch.WordTrace tailWord_1224647 prefixEnd_1224647 628832543086775296680457 := by
  unfold tailWord_1224647
  simp only [CollatzResearch.WordTrace]
  refine ⟨44666545594320546901184195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29777697062880364600789463 44666545594320546901184195)
  ·
    refine ⟨66999818391480820351776293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44666545594320546901184195 66999818391480820351776293)
    ·
      refine ⟨12562465948402653815958055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66999818391480820351776293 12562465948402653815958055)
      ·
        refine ⟨18843698922603980723937083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12562465948402653815958055 18843698922603980723937083)
        ·
          refine ⟨28265548383905971085905625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18843698922603980723937083 28265548383905971085905625)
          ·
            refine ⟨21199161287929478314429219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28265548383905971085905625 21199161287929478314429219)
            ·
              refine ⟨31798741931894217471643829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21199161287929478314429219 31798741931894217471643829)
              ·
                refine ⟨2981132056115082887966609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31798741931894217471643829 2981132056115082887966609)
                ·
                  refine ⟨2235849042086312165974957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2981132056115082887966609 2235849042086312165974957)
                  ·
                    refine ⟨838443390782367062240609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2235849042086312165974957 838443390782367062240609)
                    ·
                      refine ⟨628832543086775296680457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 838443390782367062240609 628832543086775296680457)
                      ·
                        rfl

theorem cell23_1224647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 5, 2, 3, 2].length) (baseStart_1224647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1224647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1224647 prefixEnd_1224647 := by exact prefixLift 1224647
  have htrace : WordTrace (prefixWord ++ tailWord_1224647) baseStart_1224647 baseEnd_1224647 := by
    simpa [prefixWord, tailWord_1224647, baseEnd_1224647] using wordTrace_append hprefix tailTrace_1224647
  have hstable : (prefixWord ++ tailWord_1224647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1224647).length < 2 ^ (prefixWord ++ tailWord_1224647).sum := by decide
  have hdescent : baseEnd_1224647 < baseStart_1224647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1224647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1224680 : List Nat := [2, 1, 4, 1, 1, 1, 1, 1, 2, 6, 3]
def baseStart_1224680 : Nat := 118140960795 + 1224680 * 2 ^ 59
def prefixEnd_1224680 : Nat := 4983230072969 + 3 ^ 40 * 1224680 * 2
def baseEnd_1224680 : Nat := 628849487948373667567805

theorem tailTrace_1224680 : CollatzResearch.WordTrace tailWord_1224680 prefixEnd_1224680 628849487948373667567805 := by
  unfold tailWord_1224680
  simp only [CollatzResearch.WordTrace]
  refine ⟨22333874601600496768567747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29778499468800662358090329 22333874601600496768567747)
  ·
    refine ⟨33500811902400745152851621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22333874601600496768567747 33500811902400745152851621)
    ·
      refine ⟨6281402231700139716159679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33500811902400745152851621 6281402231700139716159679)
      ·
        refine ⟨9422103347550209574239519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6281402231700139716159679 9422103347550209574239519)
        ·
          refine ⟨14133155021325314361359279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9422103347550209574239519 14133155021325314361359279)
          ·
            refine ⟨21199732531987971542038919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14133155021325314361359279 21199732531987971542038919)
            ·
              refine ⟨31799598797981957313058379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21199732531987971542038919 31799598797981957313058379)
              ·
                refine ⟨47699398196972935969587569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31799598797981957313058379 47699398196972935969587569)
                ·
                  refine ⟨35774548647729701977190677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47699398196972935969587569 35774548647729701977190677)
                  ·
                    refine ⟨1676931967862329780180813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 35774548647729701977190677 1676931967862329780180813)
                    ·
                      refine ⟨628849487948373667567805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1676931967862329780180813 628849487948373667567805)
                      ·
                        rfl

theorem cell23_1224680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 2, 6, 3].length) (baseStart_1224680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1224680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1224680 prefixEnd_1224680 := by exact prefixLift 1224680
  have htrace : WordTrace (prefixWord ++ tailWord_1224680) baseStart_1224680 baseEnd_1224680 := by
    simpa [prefixWord, tailWord_1224680, baseEnd_1224680] using wordTrace_append hprefix tailTrace_1224680
  have hstable : (prefixWord ++ tailWord_1224680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1224680).length < 2 ^ (prefixWord ++ tailWord_1224680).sum := by decide
  have hdescent : baseEnd_1224680 < baseStart_1224680 := by decide
  rcases family_descends (prefixWord ++ tailWord_1224680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1224687 : List Nat := [1, 1, 2, 1, 4, 2, 3, 3, 2, 4]
def baseStart_1224687 : Nat := 118140960795 + 1224687 * 2 ^ 59
def prefixEnd_1224687 : Nat := 4983230072969 + 3 ^ 40 * 1224687 * 2
def baseEnd_1224687 : Nat := 209617694104318380060091

theorem tailTrace_1224687 : CollatzResearch.WordTrace tailWord_1224687 prefixEnd_1224687 209617694104318380060091 := by
  unfold tailWord_1224687
  simp only [CollatzResearch.WordTrace]
  refine ⟨44668004514175633732640315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29778669676117089155093543 44668004514175633732640315)
  ·
    refine ⟨67002006771263450598960473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44668004514175633732640315 67002006771263450598960473)
    ·
      refine ⟨50251505078447587949220355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67002006771263450598960473 50251505078447587949220355)
      ·
        refine ⟨75377257617671381923830533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50251505078447587949220355 75377257617671381923830533)
        ·
          refine ⟨14133235803313384110718225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 75377257617671381923830533 14133235803313384110718225)
          ·
            refine ⟨10599926852485038083038669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14133235803313384110718225 10599926852485038083038669)
            ·
              refine ⟨3974972569681889281139501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10599926852485038083038669 3974972569681889281139501)
              ·
                refine ⟨1490614713630708480427313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3974972569681889281139501 1490614713630708480427313)
                ·
                  refine ⟨1117961035223031360320485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1490614713630708480427313 1117961035223031360320485)
                  ·
                    refine ⟨209617694104318380060091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1117961035223031360320485 209617694104318380060091)
                    ·
                      rfl

theorem cell23_1224687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 3, 2, 4].length) (baseStart_1224687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1224687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1224687 prefixEnd_1224687 := by exact prefixLift 1224687
  have htrace : WordTrace (prefixWord ++ tailWord_1224687) baseStart_1224687 baseEnd_1224687 := by
    simpa [prefixWord, tailWord_1224687, baseEnd_1224687] using wordTrace_append hprefix tailTrace_1224687
  have hstable : (prefixWord ++ tailWord_1224687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1224687).length < 2 ^ (prefixWord ++ tailWord_1224687).sum := by decide
  have hdescent : baseEnd_1224687 < baseStart_1224687 := by decide
  rcases family_descends (prefixWord ++ tailWord_1224687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1224694 : List Nat := [5, 1, 1, 1, 4, 1, 1, 1, 3, 1, 4]
def baseStart_1224694 : Nat := 118140960795 + 1224694 * 2 ^ 59
def prefixEnd_1224694 : Nat := 4983230072969 + 3 ^ 40 * 1224694 * 2
def baseEnd_1224694 : Nat := 628856676677536612792741

theorem tailTrace_1224694 : CollatzResearch.WordTrace tailWord_1224694 prefixEnd_1224694 628856676677536612792741 := by
  unfold tailWord_1224694
  simp only [CollatzResearch.WordTrace]
  refine ⟨2791766239071892120509071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 29778839883433515952096757 2791766239071892120509071)
  ·
    refine ⟨4187649358607838180763607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2791766239071892120509071 4187649358607838180763607)
    ·
      refine ⟨6281474037911757271145411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4187649358607838180763607 6281474037911757271145411)
      ·
        refine ⟨9422211056867635906718117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6281474037911757271145411 9422211056867635906718117)
        ·
          refine ⟨1766664573162681732509647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9422211056867635906718117 1766664573162681732509647)
          ·
            refine ⟨2649996859744022598764471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1766664573162681732509647 2649996859744022598764471)
            ·
              refine ⟨3974995289616033898146707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2649996859744022598764471 3974995289616033898146707)
              ·
                refine ⟨5962492934424050847220061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3974995289616033898146707 5962492934424050847220061)
                ·
                  refine ⟨2235934850409019067707523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5962492934424050847220061 2235934850409019067707523)
                  ·
                    refine ⟨3353902275613528601561285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2235934850409019067707523 3353902275613528601561285)
                    ·
                      refine ⟨628856676677536612792741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3353902275613528601561285 628856676677536612792741)
                      ·
                        rfl

theorem cell23_1224694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 1, 3, 1, 4].length) (baseStart_1224694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1224694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1224694 prefixEnd_1224694 := by exact prefixLift 1224694
  have htrace : WordTrace (prefixWord ++ tailWord_1224694) baseStart_1224694 baseEnd_1224694 := by
    simpa [prefixWord, tailWord_1224694, baseEnd_1224694] using wordTrace_append hprefix tailTrace_1224694
  have hstable : (prefixWord ++ tailWord_1224694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1224694).length < 2 ^ (prefixWord ++ tailWord_1224694).sum := by decide
  have hdescent : baseEnd_1224694 < baseStart_1224694 := by decide
  rcases family_descends (prefixWord ++ tailWord_1224694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1224697 : List Nat := [1, 2, 1, 3, 1, 5, 1, 1, 3, 2, 3]
def baseStart_1224697 : Nat := 118140960795 + 1224697 * 2 ^ 59
def prefixEnd_1224697 : Nat := 4983230072969 + 3 ^ 40 * 1224697 * 2
def baseEnd_1224697 : Nat := 628858217119500101055227

theorem tailTrace_1224697 : CollatzResearch.WordTrace tailWord_1224697 prefixEnd_1224697 628858217119500101055227 := by
  unfold tailWord_1224697
  simp only [CollatzResearch.WordTrace]
  refine ⟨44668369244139405440504345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29778912829426270293669563 44668369244139405440504345)
  ·
    refine ⟨33501276933104554080378259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44668369244139405440504345 33501276933104554080378259)
    ·
      refine ⟨50251915399656831120567389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33501276933104554080378259 50251915399656831120567389)
      ·
        refine ⟨18844468274871311670212771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50251915399656831120567389 18844468274871311670212771)
        ·
          refine ⟨28266702412306967505319157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18844468274871311670212771 28266702412306967505319157)
          ·
            refine ⟨2650003351153778203623671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28266702412306967505319157 2650003351153778203623671)
            ·
              refine ⟨3975005026730667305435507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2650003351153778203623671 3975005026730667305435507)
              ·
                refine ⟨5962507540096000958153261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3975005026730667305435507 5962507540096000958153261)
                ·
                  refine ⟨2235940327536000359307473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5962507540096000958153261 2235940327536000359307473)
                  ·
                    refine ⟨1676955245652000269480605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2235940327536000359307473 1676955245652000269480605)
                    ·
                      refine ⟨628858217119500101055227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1676955245652000269480605 628858217119500101055227)
                      ·
                        rfl

theorem cell23_1224697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 1, 3, 2, 3].length) (baseStart_1224697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1224697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1224697 prefixEnd_1224697 := by exact prefixLift 1224697
  have htrace : WordTrace (prefixWord ++ tailWord_1224697) baseStart_1224697 baseEnd_1224697 := by
    simpa [prefixWord, tailWord_1224697, baseEnd_1224697] using wordTrace_append hprefix tailTrace_1224697
  have hstable : (prefixWord ++ tailWord_1224697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1224697).length < 2 ^ (prefixWord ++ tailWord_1224697).sum := by decide
  have hdescent : baseEnd_1224697 < baseStart_1224697 := by decide
  rcases family_descends (prefixWord ++ tailWord_1224697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1224714 : List Nat := [3, 1, 2, 2, 4, 2, 1, 1, 1, 1, 5]
def baseStart_1224714 : Nat := 118140960795 + 1224714 * 2 ^ 59
def prefixEnd_1224714 : Nat := 4983230072969 + 3 ^ 40 * 1224714 * 2
def baseEnd_1224714 : Nat := 628866946290626534542649

theorem tailTrace_1224714 : CollatzResearch.WordTrace tailWord_1224714 prefixEnd_1224714 628866946290626534542649 := by
  unfold tailWord_1224714
  simp only [CollatzResearch.WordTrace]
  refine ⟨11167247321269454335968299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29779326190051878229248797 11167247321269454335968299)
  ·
    refine ⟨16750870981904181503952449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11167247321269454335968299 16750870981904181503952449)
    ·
      refine ⟨12563153236428136127964337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16750870981904181503952449 12563153236428136127964337)
      ·
        refine ⟨9422364927321102095973253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12563153236428136127964337 9422364927321102095973253)
        ·
          refine ⟨1766693423872706642994985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9422364927321102095973253 1766693423872706642994985)
          ·
            refine ⟨1325020067904529982246239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1766693423872706642994985 1325020067904529982246239)
            ·
              refine ⟨1987530101856794973369359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1325020067904529982246239 1987530101856794973369359)
              ·
                refine ⟨2981295152785192460054039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1987530101856794973369359 2981295152785192460054039)
                ·
                  refine ⟨4471942729177788690081059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2981295152785192460054039 4471942729177788690081059)
                  ·
                    refine ⟨6707914093766683035121589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4471942729177788690081059 6707914093766683035121589)
                    ·
                      refine ⟨628866946290626534542649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6707914093766683035121589 628866946290626534542649)
                      ·
                        rfl

theorem cell23_1224714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 1, 1, 1, 1, 5].length) (baseStart_1224714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1224714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1224714 prefixEnd_1224714 := by exact prefixLift 1224714
  have htrace : WordTrace (prefixWord ++ tailWord_1224714) baseStart_1224714 baseEnd_1224714 := by
    simpa [prefixWord, tailWord_1224714, baseEnd_1224714] using wordTrace_append hprefix tailTrace_1224714
  have hstable : (prefixWord ++ tailWord_1224714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1224714).length < 2 ^ (prefixWord ++ tailWord_1224714).sum := by decide
  have hdescent : baseEnd_1224714 < baseStart_1224714 := by decide
  rcases family_descends (prefixWord ++ tailWord_1224714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1224730 : List Nat := [3, 1, 1, 3, 1, 3, 1, 1, 2, 7]
def baseStart_1224730 : Nat := 118140960795 + 1224730 * 2 ^ 59
def prefixEnd_1224730 : Nat := 4983230072969 + 3 ^ 40 * 1224730 * 2
def baseEnd_1224730 : Nat := 209625053993699490647525

theorem tailTrace_1224730 : CollatzResearch.WordTrace tailWord_1224730 prefixEnd_1224730 209625053993699490647525 := by
  unfold tailWord_1224730
  simp only [CollatzResearch.WordTrace]
  refine ⟨11167393213254963019113911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29779715235346568050970429 11167393213254963019113911)
  ·
    refine ⟨16751089819882444528670867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11167393213254963019113911 16751089819882444528670867)
    ·
      refine ⟨25126634729823666793006301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16751089819882444528670867 25126634729823666793006301)
      ·
        refine ⟨9422488023683875047377363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25126634729823666793006301 9422488023683875047377363)
        ·
          refine ⟨14133732035525812571066045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9422488023683875047377363 14133732035525812571066045)
          ·
            refine ⟨5300149513322179714149767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14133732035525812571066045 5300149513322179714149767)
            ·
              refine ⟨7950224269983269571224651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5300149513322179714149767 7950224269983269571224651)
              ·
                refine ⟨11925336404974904356836977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7950224269983269571224651 11925336404974904356836977)
                ·
                  refine ⟨8944002303731178267627733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11925336404974904356836977 8944002303731178267627733)
                  ·
                    refine ⟨209625053993699490647525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8944002303731178267627733 209625053993699490647525)
                    ·
                      rfl

theorem cell23_1224730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 1, 2, 7].length) (baseStart_1224730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1224730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1224730 prefixEnd_1224730 := by exact prefixLift 1224730
  have htrace : WordTrace (prefixWord ++ tailWord_1224730) baseStart_1224730 baseEnd_1224730 := by
    simpa [prefixWord, tailWord_1224730, baseEnd_1224730] using wordTrace_append hprefix tailTrace_1224730
  have hstable : (prefixWord ++ tailWord_1224730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1224730).length < 2 ^ (prefixWord ++ tailWord_1224730).sum := by decide
  have hdescent : baseEnd_1224730 < baseStart_1224730 := by decide
  rcases family_descends (prefixWord ++ tailWord_1224730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1224754 : List Nat := [3, 2, 1, 1, 2, 3, 2, 1, 3, 3, 2]
def baseStart_1224754 : Nat := 118140960795 + 1224754 * 2 ^ 59
def prefixEnd_1224754 : Nat := 4983230072969 + 3 ^ 40 * 1224754 * 2
def baseEnd_1224754 : Nat := 628887485516806378042465

theorem tailTrace_1224754 : CollatzResearch.WordTrace tailWord_1224754 prefixEnd_1224754 628887485516806378042465 := by
  unfold tailWord_1224754
  simp only [CollatzResearch.WordTrace]
  refine ⟨11167612051233226043832329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29780298803288602783552877 11167612051233226043832329)
  ·
    refine ⟨8375709038424919532874247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11167612051233226043832329 8375709038424919532874247)
    ·
      refine ⟨12563563557637379299311371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8375709038424919532874247 12563563557637379299311371)
      ·
        refine ⟨18845345336456068948967057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12563563557637379299311371 18845345336456068948967057)
        ·
          refine ⟨14134009002342051711725293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18845345336456068948967057 14134009002342051711725293)
          ·
            refine ⟨5300253375878269391896985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14134009002342051711725293 5300253375878269391896985)
            ·
              refine ⟨3975190031908702043922739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5300253375878269391896985 3975190031908702043922739)
              ·
                refine ⟨5962785047863053065884109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3975190031908702043922739 5962785047863053065884109)
                ·
                  refine ⟨2236044392948644899706541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5962785047863053065884109 2236044392948644899706541)
                  ·
                    refine ⟨838516647355741837389953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2236044392948644899706541 838516647355741837389953)
                    ·
                      refine ⟨628887485516806378042465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 838516647355741837389953 628887485516806378042465)
                      ·
                        rfl

theorem cell23_1224754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 1, 3, 3, 2].length) (baseStart_1224754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1224754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1224754 prefixEnd_1224754 := by exact prefixLift 1224754
  have htrace : WordTrace (prefixWord ++ tailWord_1224754) baseStart_1224754 baseEnd_1224754 := by
    simpa [prefixWord, tailWord_1224754, baseEnd_1224754] using wordTrace_append hprefix tailTrace_1224754
  have hstable : (prefixWord ++ tailWord_1224754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1224754).length < 2 ^ (prefixWord ++ tailWord_1224754).sum := by decide
  have hdescent : baseEnd_1224754 < baseStart_1224754 := by decide
  rcases family_descends (prefixWord ++ tailWord_1224754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1224827 : List Nat := [1, 1, 1, 1, 1, 4, 1, 1, 3, 7, 2]
def baseStart_1224827 : Nat := 118140960795 + 1224827 * 2 ^ 59
def prefixEnd_1224827 : Nat := 4983230072969 + 3 ^ 40 * 1224827 * 2
def baseEnd_1224827 : Nat := 628924969604584592429629

theorem tailTrace_1224827 : CollatzResearch.WordTrace tailWord_1224827 prefixEnd_1224827 628924969604584592429629 := by
  unfold tailWord_1224827
  simp only [CollatzResearch.WordTrace]
  refine ⟨44673110733668437642736735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29782073822445625095157823 44673110733668437642736735)
  ·
    refine ⟨67009666100502656464105103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44673110733668437642736735 67009666100502656464105103)
    ·
      refine ⟨100514499150753984696157655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67009666100502656464105103 100514499150753984696157655)
      ·
        refine ⟨150771748726130977044236483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100514499150753984696157655 150771748726130977044236483)
        ·
          refine ⟨226157623089196465566354725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150771748726130977044236483 226157623089196465566354725)
          ·
            refine ⟨42404554329224337293691511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 226157623089196465566354725 42404554329224337293691511)
            ·
              refine ⟨63606831493836505940537267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42404554329224337293691511 63606831493836505940537267)
              ·
                refine ⟨95410247240754758910805901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63606831493836505940537267 95410247240754758910805901)
                ·
                  refine ⟨35778842715283034591552213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 95410247240754758910805901 35778842715283034591552213)
                  ·
                    refine ⟨838566626139446123239505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35778842715283034591552213 838566626139446123239505)
                    ·
                      refine ⟨628924969604584592429629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 838566626139446123239505 628924969604584592429629)
                      ·
                        rfl

theorem cell23_1224827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 3, 7, 2].length) (baseStart_1224827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1224827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1224827 prefixEnd_1224827 := by exact prefixLift 1224827
  have htrace : WordTrace (prefixWord ++ tailWord_1224827) baseStart_1224827 baseEnd_1224827 := by
    simpa [prefixWord, tailWord_1224827, baseEnd_1224827] using wordTrace_append hprefix tailTrace_1224827
  have hstable : (prefixWord ++ tailWord_1224827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1224827).length < 2 ^ (prefixWord ++ tailWord_1224827).sum := by decide
  have hdescent : baseEnd_1224827 < baseStart_1224827 := by decide
  rcases family_descends (prefixWord ++ tailWord_1224827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1224837 : List Nat := [1, 3, 1, 1, 5, 1, 1, 1, 4, 5]
def baseStart_1224837 : Nat := 118140960795 + 1224837 * 2 ^ 59
def prefixEnd_1224837 : Nat := 4983230072969 + 3 ^ 40 * 1224837 * 2
def baseEnd_1224837 : Nat := 209643368137043184434861

theorem tailTrace_1224837 : CollatzResearch.WordTrace tailWord_1224837 prefixEnd_1224837 209643368137043184434861 := by
  unfold tailWord_1224837
  simp only [CollatzResearch.WordTrace]
  refine ⟨44673475463632209350600765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29782316975754806233733843 44673475463632209350600765)
  ·
    refine ⟨16752553298862078506475287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44673475463632209350600765 16752553298862078506475287)
    ·
      refine ⟨25128829948293117759712931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16752553298862078506475287 25128829948293117759712931)
      ·
        refine ⟨37693244922439676639569397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25128829948293117759712931 37693244922439676639569397)
        ·
          refine ⟨3533741711478719684959631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 37693244922439676639569397 3533741711478719684959631)
          ·
            refine ⟨5300612567218079527439447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3533741711478719684959631 5300612567218079527439447)
            ·
              refine ⟨7950918850827119291159171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5300612567218079527439447 7950918850827119291159171)
              ·
                refine ⟨11926378276240678936738757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7950918850827119291159171 11926378276240678936738757)
                ·
                  refine ⟨2236195926795127300638517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11926378276240678936738757 2236195926795127300638517)
                  ·
                    refine ⟨209643368137043184434861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2236195926795127300638517 209643368137043184434861)
                    ·
                      rfl

theorem cell23_1224837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 1, 4, 5].length) (baseStart_1224837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1224837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1224837 prefixEnd_1224837 := by exact prefixLift 1224837
  have htrace : WordTrace (prefixWord ++ tailWord_1224837) baseStart_1224837 baseEnd_1224837 := by
    simpa [prefixWord, tailWord_1224837, baseEnd_1224837] using wordTrace_append hprefix tailTrace_1224837
  have hstable : (prefixWord ++ tailWord_1224837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1224837).length < 2 ^ (prefixWord ++ tailWord_1224837).sum := by decide
  have hdescent : baseEnd_1224837 < baseStart_1224837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1224837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1224871 : List Nat := [1, 1, 6, 2, 2, 1, 2, 1, 2, 5]
def baseStart_1224871 : Nat := 118140960795 + 1224871 * 2 ^ 59
def prefixEnd_1224871 : Nat := 4983230072969 + 3 ^ 40 * 1224871 * 2
def baseEnd_1224871 : Nat := 209649187584460806759809

theorem tailTrace_1224871 : CollatzResearch.WordTrace tailWord_1224871 prefixEnd_1224871 209649187584460806759809 := by
  unfold tailWord_1224871
  simp only [CollatzResearch.WordTrace]
  refine ⟨44674715545509033157338467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29783143697006022104892311 44674715545509033157338467)
  ·
    refine ⟨67012073318263549736007701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44674715545509033157338467 67012073318263549736007701)
    ·
      refine ⟨3141190936793603893875361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 67012073318263549736007701 3141190936793603893875361)
      ·
        refine ⟨2355893202595202920406521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3141190936793603893875361 2355893202595202920406521)
        ·
          refine ⟨1766919901946402190304891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2355893202595202920406521 1766919901946402190304891)
          ·
            refine ⟨2650379852919603285457337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1766919901946402190304891 2650379852919603285457337)
            ·
              refine ⟨1987784889689702464093003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2650379852919603285457337 1987784889689702464093003)
              ·
                refine ⟨2981677334534553696139505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1987784889689702464093003 2981677334534553696139505)
                ·
                  refine ⟨2236258000900915272104629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2981677334534553696139505 2236258000900915272104629)
                  ·
                    refine ⟨209649187584460806759809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2236258000900915272104629 209649187584460806759809)
                    ·
                      rfl

theorem cell23_1224871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 2, 1, 2, 5].length) (baseStart_1224871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1224871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1224871 prefixEnd_1224871 := by exact prefixLift 1224871
  have htrace : WordTrace (prefixWord ++ tailWord_1224871) baseStart_1224871 baseEnd_1224871 := by
    simpa [prefixWord, tailWord_1224871, baseEnd_1224871] using wordTrace_append hprefix tailTrace_1224871
  have hstable : (prefixWord ++ tailWord_1224871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1224871).length < 2 ^ (prefixWord ++ tailWord_1224871).sum := by decide
  have hdescent : baseEnd_1224871 < baseStart_1224871 := by decide
  rcases family_descends (prefixWord ++ tailWord_1224871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1224908 : List Nat := [2, 2, 1, 6, 1, 1, 1, 1, 2, 4, 2]
def baseStart_1224908 : Nat := 118140960795 + 1224908 * 2 ^ 59
def prefixEnd_1224908 : Nat := 4983230072969 + 3 ^ 40 * 1224908 * 2
def baseEnd_1224908 : Nat := 628966561537598775516757

theorem tailTrace_1224908 : CollatzResearch.WordTrace tailWord_1224908 prefixEnd_1224908 628966561537598775516757 := by
  unfold tailWord_1224908
  simp only [CollatzResearch.WordTrace]
  refine ⟨22338032523187494238217689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29784043364249992317623585 22338032523187494238217689)
  ·
    refine ⟨16753524392390620678663267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22338032523187494238217689 16753524392390620678663267)
    ·
      refine ⟨25130286588585931017994901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16753524392390620678663267 25130286588585931017994901)
      ·
        refine ⟨1177982183839965516468511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 25130286588585931017994901 1177982183839965516468511)
        ·
          refine ⟨1766973275759948274702767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1177982183839965516468511 1766973275759948274702767)
          ·
            refine ⟨2650459913639922412054151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1766973275759948274702767 2650459913639922412054151)
            ·
              refine ⟨3975689870459883618081227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2650459913639922412054151 3975689870459883618081227)
              ·
                refine ⟨5963534805689825427121841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3975689870459883618081227 5963534805689825427121841)
                ·
                  refine ⟨4472651104267369070341381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5963534805689825427121841 4472651104267369070341381)
                  ·
                    refine ⟨838622082050131700689009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4472651104267369070341381 838622082050131700689009)
                    ·
                      refine ⟨628966561537598775516757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 838622082050131700689009 628966561537598775516757)
                      ·
                        rfl

theorem cell23_1224908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_1224908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1224908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1224908 prefixEnd_1224908 := by exact prefixLift 1224908
  have htrace : WordTrace (prefixWord ++ tailWord_1224908) baseStart_1224908 baseEnd_1224908 := by
    simpa [prefixWord, tailWord_1224908, baseEnd_1224908] using wordTrace_append hprefix tailTrace_1224908
  have hstable : (prefixWord ++ tailWord_1224908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1224908).length < 2 ^ (prefixWord ++ tailWord_1224908).sum := by decide
  have hdescent : baseEnd_1224908 < baseStart_1224908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1224908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1224914 : List Nat := [3, 2, 2, 2, 1, 2, 2, 3, 6]
def baseStart_1224914 : Nat := 118140960795 + 1224914 * 2 ^ 59
def prefixEnd_1224914 : Nat := 4983230072969 + 3 ^ 40 * 1224914 * 2
def baseEnd_1224914 : Nat := 69885515824613972449081

theorem tailTrace_1224914 : CollatzResearch.WordTrace tailWord_1224914 prefixEnd_1224914 69885515824613972449081 := by
  unfold tailWord_1224914
  simp only [CollatzResearch.WordTrace]
  refine ⟨11169070971088312875288449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29784189256235501000769197 11169070971088312875288449)
  ·
    refine ⟨8376803228316234656466337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11169070971088312875288449 8376803228316234656466337)
    ·
      refine ⟨6282602421237175992349753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8376803228316234656466337 6282602421237175992349753)
      ·
        refine ⟨4711951815927881994262315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6282602421237175992349753 4711951815927881994262315)
        ·
          refine ⟨7067927723891822991393473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4711951815927881994262315 7067927723891822991393473)
          ·
            refine ⟨5300945792918867243545105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7067927723891822991393473 5300945792918867243545105)
            ·
              refine ⟨3975709344689150432658829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5300945792918867243545105 3975709344689150432658829)
              ·
                refine ⟨1490891004258431412247061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3975709344689150432658829 1490891004258431412247061)
                ·
                  refine ⟨69885515824613972449081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1490891004258431412247061 69885515824613972449081)
                  ·
                    rfl

theorem cell23_1224914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 3, 6].length) (baseStart_1224914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1224914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1224914 prefixEnd_1224914 := by exact prefixLift 1224914
  have htrace : WordTrace (prefixWord ++ tailWord_1224914) baseStart_1224914 baseEnd_1224914 := by
    simpa [prefixWord, tailWord_1224914, baseEnd_1224914] using wordTrace_append hprefix tailTrace_1224914
  have hstable : (prefixWord ++ tailWord_1224914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1224914).length < 2 ^ (prefixWord ++ tailWord_1224914).sum := by decide
  have hdescent : baseEnd_1224914 < baseStart_1224914 := by decide
  rcases family_descends (prefixWord ++ tailWord_1224914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1224918 : List Nat := [5, 2, 1, 2, 1, 2, 1, 2, 3, 4]
def baseStart_1224918 : Nat := 118140960795 + 1224918 * 2 ^ 59
def prefixEnd_1224918 : Nat := 4983230072969 + 3 ^ 40 * 1224918 * 2
def baseEnd_1224918 : Nat := 209657232114714578797237

theorem tailTrace_1224918 : CollatzResearch.WordTrace tailWord_1224918 prefixEnd_1224918 209657232114714578797237 := by
  unfold tailWord_1224918
  simp only [CollatzResearch.WordTrace]
  refine ⟨2792276861021172511518713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 29784286517559173456199605 2792276861021172511518713)
  ·
    refine ⟨2094207645765879383639035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2792276861021172511518713 2094207645765879383639035)
    ·
      refine ⟨3141311468648819075458553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2094207645765879383639035 3141311468648819075458553)
      ·
        refine ⟨2355983601486614306593915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3141311468648819075458553 2355983601486614306593915)
        ·
          refine ⟨3533975402229921459890873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2355983601486614306593915 3533975402229921459890873)
          ·
            refine ⟨2650481551672441094918155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3533975402229921459890873 2650481551672441094918155)
            ·
              refine ⟨3975722327508661642377233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2650481551672441094918155 3975722327508661642377233)
              ·
                refine ⟨2981791745631496231782925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3975722327508661642377233 2981791745631496231782925)
                ·
                  refine ⟨1118171904611811086918597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2981791745631496231782925 1118171904611811086918597)
                  ·
                    refine ⟨209657232114714578797237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1118171904611811086918597 209657232114714578797237)
                    ·
                      rfl

theorem cell23_1224918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 2, 3, 4].length) (baseStart_1224918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1224918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1224918 prefixEnd_1224918 := by exact prefixLift 1224918
  have htrace : WordTrace (prefixWord ++ tailWord_1224918) baseStart_1224918 baseEnd_1224918 := by
    simpa [prefixWord, tailWord_1224918, baseEnd_1224918] using wordTrace_append hprefix tailTrace_1224918
  have hstable : (prefixWord ++ tailWord_1224918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1224918).length < 2 ^ (prefixWord ++ tailWord_1224918).sum := by decide
  have hdescent : baseEnd_1224918 < baseStart_1224918 := by decide
  rcases family_descends (prefixWord ++ tailWord_1224918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1224957 : List Nat := [1, 4, 1, 1, 1, 1, 1, 4, 3, 6]
def baseStart_1224957 : Nat := 118140960795 + 1224957 * 2 ^ 59
def prefixEnd_1224957 : Nat := 4983230072969 + 3 ^ 40 * 1224957 * 2
def baseEnd_1224957 : Nat := 209663907363223027934677

theorem tailTrace_1224957 : CollatzResearch.WordTrace tailWord_1224957 prefixEnd_1224957 209663907363223027934677 := by
  unfold tailWord_1224957
  simp only [CollatzResearch.WordTrace]
  refine ⟨44677852223197469844969125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29785234815464979896646083 44677852223197469844969125)
  ·
    refine ⟨8377097291849525595931711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44677852223197469844969125 8377097291849525595931711)
    ·
      refine ⟨12565645937774288393897567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8377097291849525595931711 12565645937774288393897567)
      ·
        refine ⟨18848468906661432590846351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12565645937774288393897567 18848468906661432590846351)
        ·
          refine ⟨28272703359992148886269527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18848468906661432590846351 28272703359992148886269527)
          ·
            refine ⟨42409055039988223329404291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28272703359992148886269527 42409055039988223329404291)
            ·
              refine ⟨63613582559982334994106437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42409055039988223329404291 63613582559982334994106437)
              ·
                refine ⟨11927546729996687811394957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 63613582559982334994106437 11927546729996687811394957)
                ·
                  refine ⟨4472830023748757929273109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11927546729996687811394957 4472830023748757929273109)
                  ·
                    refine ⟨209663907363223027934677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4472830023748757929273109 209663907363223027934677)
                    ·
                      rfl

theorem cell23_1224957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 4, 3, 6].length) (baseStart_1224957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1224957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1224957 prefixEnd_1224957 := by exact prefixLift 1224957
  have htrace : WordTrace (prefixWord ++ tailWord_1224957) baseStart_1224957 baseEnd_1224957 := by
    simpa [prefixWord, tailWord_1224957, baseEnd_1224957] using wordTrace_append hprefix tailTrace_1224957
  have hstable : (prefixWord ++ tailWord_1224957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1224957).length < 2 ^ (prefixWord ++ tailWord_1224957).sum := by decide
  have hdescent : baseEnd_1224957 < baseStart_1224957 := by decide
  rcases family_descends (prefixWord ++ tailWord_1224957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1224958 : List Nat := [4, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3]
def baseStart_1224958 : Nat := 118140960795 + 1224958 * 2 ^ 59
def prefixEnd_1224958 : Nat := 4983230072969 + 3 ^ 40 * 1224958 * 2
def baseEnd_1224958 : Nat := 628992235570323579891527

theorem tailTrace_1224958 : CollatzResearch.WordTrace tailWord_1224958 prefixEnd_1224958 628992235570323579891527 := by
  unfold tailWord_1224958
  simp only [CollatzResearch.WordTrace]
  refine ⟨5584736087024230876969441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29785259130795898010503685 5584736087024230876969441)
  ·
    refine ⟨4188552065268173157727081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5584736087024230876969441 4188552065268173157727081)
    ·
      refine ⟨3141414048951129868295311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4188552065268173157727081 3141414048951129868295311)
      ·
        refine ⟨4712121073426694802442967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3141414048951129868295311 4712121073426694802442967)
        ·
          refine ⟨7068181610140042203664451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4712121073426694802442967 7068181610140042203664451)
          ·
            refine ⟨10602272415210063305496677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7068181610140042203664451 10602272415210063305496677)
            ·
              refine ⟨1987926077851886869780627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10602272415210063305496677 1987926077851886869780627)
              ·
                refine ⟨2981889116777830304670941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1987926077851886869780627 2981889116777830304670941)
                ·
                  refine ⟨1118208418791686364251603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2981889116777830304670941 1118208418791686364251603)
                  ·
                    refine ⟨1677312628187529546377405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1118208418791686364251603 1677312628187529546377405)
                    ·
                      refine ⟨628992235570323579891527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1677312628187529546377405 628992235570323579891527)
                      ·
                        rfl

theorem cell23_1224958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3].length) (baseStart_1224958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1224958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1224958 prefixEnd_1224958 := by exact prefixLift 1224958
  have htrace : WordTrace (prefixWord ++ tailWord_1224958) baseStart_1224958 baseEnd_1224958 := by
    simpa [prefixWord, tailWord_1224958, baseEnd_1224958] using wordTrace_append hprefix tailTrace_1224958
  have hstable : (prefixWord ++ tailWord_1224958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1224958).length < 2 ^ (prefixWord ++ tailWord_1224958).sum := by decide
  have hdescent : baseEnd_1224958 < baseStart_1224958 := by decide
  rcases family_descends (prefixWord ++ tailWord_1224958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1225052 : List Nat := [2, 2, 4, 3, 1, 1, 3, 1, 1, 2, 3]
def baseStart_1225052 : Nat := 118140960795 + 1225052 * 2 ^ 59
def prefixEnd_1225052 : Nat := 4983230072969 + 3 ^ 40 * 1225052 * 2
def baseEnd_1225052 : Nat := 629040502751846212116095

theorem tailTrace_1225052 : CollatzResearch.WordTrace tailWord_1225052 prefixEnd_1225052 629040502751846212116095 := by
  unfold tailWord_1225052
  simp only [CollatzResearch.WordTrace]
  refine ⟨22340658578926650534838705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29787544771902200713118273 22340658578926650534838705)
  ·
    refine ⟨16755493934194987901129029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22340658578926650534838705 16755493934194987901129029)
    ·
      refine ⟨3141655112661560231461693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16755493934194987901129029 3141655112661560231461693)
      ·
        refine ⟨1178120667248085086798135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3141655112661560231461693 1178120667248085086798135)
        ·
          refine ⟨1767181000872127630197203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1178120667248085086798135 1767181000872127630197203)
          ·
            refine ⟨2650771501308191445295805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1767181000872127630197203 2650771501308191445295805)
            ·
              refine ⟨994039312990571791985927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2650771501308191445295805 994039312990571791985927)
              ·
                refine ⟨1491058969485857687978891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 994039312990571791985927 1491058969485857687978891)
                ·
                  refine ⟨2236588454228786531968337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1491058969485857687978891 2236588454228786531968337)
                  ·
                    refine ⟨1677441340671589898976253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2236588454228786531968337 1677441340671589898976253)
                    ·
                      refine ⟨629040502751846212116095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1677441340671589898976253 629040502751846212116095)
                      ·
                        rfl

theorem cell23_1225052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_1225052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1225052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1225052 prefixEnd_1225052 := by exact prefixLift 1225052
  have htrace : WordTrace (prefixWord ++ tailWord_1225052) baseStart_1225052 baseEnd_1225052 := by
    simpa [prefixWord, tailWord_1225052, baseEnd_1225052] using wordTrace_append hprefix tailTrace_1225052
  have hstable : (prefixWord ++ tailWord_1225052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1225052).length < 2 ^ (prefixWord ++ tailWord_1225052).sum := by decide
  have hdescent : baseEnd_1225052 < baseStart_1225052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1225052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1225111 : List Nat := [1, 1, 3, 3, 1, 1, 3, 5, 5]
def baseStart_1225111 : Nat := 118140960795 + 1225111 * 2 ^ 59
def prefixEnd_1225111 : Nat := 4983230072969 + 3 ^ 40 * 1225111 * 2
def baseEnd_1225111 : Nat := 69896755345606831253147

theorem tailTrace_1225111 : CollatzResearch.WordTrace tailWord_1225111 prefixEnd_1225111 69896755345606831253147 := by
  unfold tailWord_1225111
  simp only [CollatzResearch.WordTrace]
  refine ⟨44683469064639554146075187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29788979376426369430716791 44683469064639554146075187)
  ·
    refine ⟨67025203596959331219112781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44683469064639554146075187 67025203596959331219112781)
    ·
      refine ⟨25134451348859749207167293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67025203596959331219112781 25134451348859749207167293)
      ·
        refine ⟨9425419255822405952687735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25134451348859749207167293 9425419255822405952687735)
        ·
          refine ⟨14138128883733608929031603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9425419255822405952687735 14138128883733608929031603)
          ·
            refine ⟨21207193325600413393547405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14138128883733608929031603 21207193325600413393547405)
            ·
              refine ⟨7952697497100155022580277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21207193325600413393547405 7952697497100155022580277)
              ·
                refine ⟨745565390353139533366901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7952697497100155022580277 745565390353139533366901)
                ·
                  refine ⟨69896755345606831253147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 745565390353139533366901 69896755345606831253147)
                  ·
                    rfl

theorem cell23_1225111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 5, 5].length) (baseStart_1225111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1225111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1225111 prefixEnd_1225111 := by exact prefixLift 1225111
  have htrace : WordTrace (prefixWord ++ tailWord_1225111) baseStart_1225111 baseEnd_1225111 := by
    simpa [prefixWord, tailWord_1225111, baseEnd_1225111] using wordTrace_append hprefix tailTrace_1225111
  have hstable : (prefixWord ++ tailWord_1225111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1225111).length < 2 ^ (prefixWord ++ tailWord_1225111).sum := by decide
  have hdescent : baseEnd_1225111 < baseStart_1225111 := by decide
  rcases family_descends (prefixWord ++ tailWord_1225111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1225118 : List Nat := [4, 3, 1, 2, 1, 1, 1, 2, 2, 2, 4]
def baseStart_1225118 : Nat := 118140960795 + 1225118 * 2 ^ 59
def prefixEnd_1225118 : Nat := 4983230072969 + 3 ^ 40 * 1225118 * 2
def baseEnd_1225118 : Nat := 629074392475042953890791

theorem tailTrace_1225118 : CollatzResearch.WordTrace tailWord_1225118 prefixEnd_1225118 629074392475042953890791 := by
  unfold tailWord_1225118
  simp only [CollatzResearch.WordTrace]
  refine ⟨5585465546951774292697501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29789149583742796227720005 5585465546951774292697501)
  ·
    refine ⟨2094549580106915359761563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5585465546951774292697501 2094549580106915359761563)
    ·
      refine ⟨3141824370160373039642345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2094549580106915359761563 3141824370160373039642345)
      ·
        refine ⟨2356368277620279779731759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3141824370160373039642345 2356368277620279779731759)
        ·
          refine ⟨3534552416430419669597639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2356368277620279779731759 3534552416430419669597639)
          ·
            refine ⟨5301828624645629504396459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3534552416430419669597639 5301828624645629504396459)
            ·
              refine ⟨7952742936968444256594689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5301828624645629504396459 7952742936968444256594689)
              ·
                refine ⟨5964557202726333192446017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7952742936968444256594689 5964557202726333192446017)
                ·
                  refine ⟨4473417902044749894334513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5964557202726333192446017 4473417902044749894334513)
                  ·
                    refine ⟨3355063426533562420750885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4473417902044749894334513 3355063426533562420750885)
                    ·
                      refine ⟨629074392475042953890791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3355063426533562420750885 629074392475042953890791)
                      ·
                        rfl

theorem cell23_1225118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_1225118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1225118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1225118 prefixEnd_1225118 := by exact prefixLift 1225118
  have htrace : WordTrace (prefixWord ++ tailWord_1225118) baseStart_1225118 baseEnd_1225118 := by
    simpa [prefixWord, tailWord_1225118, baseEnd_1225118] using wordTrace_append hprefix tailTrace_1225118
  have hstable : (prefixWord ++ tailWord_1225118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1225118).length < 2 ^ (prefixWord ++ tailWord_1225118).sum := by decide
  have hdescent : baseEnd_1225118 < baseStart_1225118 := by decide
  rcases family_descends (prefixWord ++ tailWord_1225118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1225128 : List Nat := [2, 1, 6, 1, 1, 2, 2, 1, 7]
def baseStart_1225128 : Nat := 118140960795 + 1225128 * 2 ^ 59
def prefixEnd_1225128 : Nat := 4983230072969 + 3 ^ 40 * 1225128 * 2
def baseEnd_1225128 : Nat := 69897725253509768307305

theorem tailTrace_1225128 : CollatzResearch.WordTrace tailWord_1225128 prefixEnd_1225128 69897725253509768307305 := by
  unfold tailWord_1225128
  simp only [CollatzResearch.WordTrace]
  refine ⟨22342044552788983024722019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29789392737051977366296025 22342044552788983024722019)
  ·
    refine ⟨33513066829183474537083029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22342044552788983024722019 33513066829183474537083029)
    ·
      refine ⟨1570925007617975368925767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 33513066829183474537083029 1570925007617975368925767)
      ·
        refine ⟨2356387511426963053388651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1570925007617975368925767 2356387511426963053388651)
        ·
          refine ⟨3534581267140444580082977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2356387511426963053388651 3534581267140444580082977)
          ·
            refine ⟨2650935950355333435062233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3534581267140444580082977 2650935950355333435062233)
            ·
              refine ⟨1988201962766500076296675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2650935950355333435062233 1988201962766500076296675)
              ·
                refine ⟨2982302944149750114445013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1988201962766500076296675 2982302944149750114445013)
                ·
                  refine ⟨69897725253509768307305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2982302944149750114445013 69897725253509768307305)
                  ·
                    rfl

theorem cell23_1225128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 2, 1, 7].length) (baseStart_1225128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1225128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1225128 prefixEnd_1225128 := by exact prefixLift 1225128
  have htrace : WordTrace (prefixWord ++ tailWord_1225128) baseStart_1225128 baseEnd_1225128 := by
    simpa [prefixWord, tailWord_1225128, baseEnd_1225128] using wordTrace_append hprefix tailTrace_1225128
  have hstable : (prefixWord ++ tailWord_1225128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1225128).length < 2 ^ (prefixWord ++ tailWord_1225128).sum := by decide
  have hdescent : baseEnd_1225128 < baseStart_1225128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1225128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1225161 : List Nat := [1, 2, 1, 1, 2, 1, 4, 2, 1, 6, 2]
def baseStart_1225161 : Nat := 118140960795 + 1225161 * 2 ^ 59
def prefixEnd_1225161 : Nat := 4983230072969 + 3 ^ 40 * 1225161 * 2
def baseEnd_1225161 : Nat := 629096472143186285653093

theorem tailTrace_1225161 : CollatzResearch.WordTrace tailWord_1225161 prefixEnd_1225161 629096472143186285653093 := by
  unfold tailWord_1225161
  simp only [CollatzResearch.WordTrace]
  refine ⟨44685292714458412685395337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29790195142972275123596891 44685292714458412685395337)
  ·
    refine ⟨33513969535843809514046503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44685292714458412685395337 33513969535843809514046503)
    ·
      refine ⟨50270954303765714271069755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33513969535843809514046503 50270954303765714271069755)
      ·
        refine ⟨75406431455648571406604633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50270954303765714271069755 75406431455648571406604633)
        ·
          refine ⟨56554823591736428554953475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75406431455648571406604633 56554823591736428554953475)
          ·
            refine ⟨84832235387604642832430213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56554823591736428554953475 84832235387604642832430213)
            ·
              refine ⟨15906044135175870531080665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 84832235387604642832430213 15906044135175870531080665)
              ·
                refine ⟨11929533101381902898310499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15906044135175870531080665 11929533101381902898310499)
                ·
                  refine ⟨17894299652072854347465749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11929533101381902898310499 17894299652072854347465749)
                  ·
                    refine ⟨838795296190915047537457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17894299652072854347465749 838795296190915047537457)
                    ·
                      refine ⟨629096472143186285653093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 838795296190915047537457 629096472143186285653093)
                      ·
                        rfl

theorem cell23_1225161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 2, 1, 6, 2].length) (baseStart_1225161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1225161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1225161 prefixEnd_1225161 := by exact prefixLift 1225161
  have htrace : WordTrace (prefixWord ++ tailWord_1225161) baseStart_1225161 baseEnd_1225161 := by
    simpa [prefixWord, tailWord_1225161, baseEnd_1225161] using wordTrace_append hprefix tailTrace_1225161
  have hstable : (prefixWord ++ tailWord_1225161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1225161).length < 2 ^ (prefixWord ++ tailWord_1225161).sum := by decide
  have hdescent : baseEnd_1225161 < baseStart_1225161 := by decide
  rcases family_descends (prefixWord ++ tailWord_1225161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1225184 : List Nat := [2, 1, 1, 3, 1, 1, 3, 3, 8]
def baseStart_1225184 : Nat := 118140960795 + 1225184 * 2 ^ 59
def prefixEnd_1225184 : Nat := 4983230072969 + 3 ^ 40 * 1225184 * 2
def baseEnd_1225184 : Nat := 69900920244248855073943

theorem tailTrace_1225184 : CollatzResearch.WordTrace tailWord_1225184 prefixEnd_1225184 69900920244248855073943 := by
  unfold tailWord_1225184
  simp only [CollatzResearch.WordTrace]
  refine ⟨22343065796687543806741303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29790754395583391742321737 22343065796687543806741303)
  ·
    refine ⟨33514598695031315710111955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22343065796687543806741303 33514598695031315710111955)
    ·
      refine ⟨50271898042546973565167933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33514598695031315710111955 50271898042546973565167933)
      ·
        refine ⟨18851961765955115086937975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50271898042546973565167933 18851961765955115086937975)
        ·
          refine ⟨28277942648932672630406963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18851961765955115086937975 28277942648932672630406963)
          ·
            refine ⟨42416913973399008945610445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28277942648932672630406963 42416913973399008945610445)
            ·
              refine ⟨15906342740024628354603917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42416913973399008945610445 15906342740024628354603917)
              ·
                refine ⟨5964878527509235632976469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15906342740024628354603917 5964878527509235632976469)
                ·
                  refine ⟨69900920244248855073943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5964878527509235632976469 69900920244248855073943)
                  ·
                    rfl

theorem cell23_1225184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 3, 8].length) (baseStart_1225184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1225184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1225184 prefixEnd_1225184 := by exact prefixLift 1225184
  have htrace : WordTrace (prefixWord ++ tailWord_1225184) baseStart_1225184 baseEnd_1225184 := by
    simpa [prefixWord, tailWord_1225184, baseEnd_1225184] using wordTrace_append hprefix tailTrace_1225184
  have hstable : (prefixWord ++ tailWord_1225184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1225184).length < 2 ^ (prefixWord ++ tailWord_1225184).sum := by decide
  have hdescent : baseEnd_1225184 < baseStart_1225184 := by decide
  rcases family_descends (prefixWord ++ tailWord_1225184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1225201 : List Nat := [1, 2, 2, 2, 3, 1, 3, 3, 6]
def baseStart_1225201 : Nat := 118140960795 + 1225201 * 2 ^ 59
def prefixEnd_1225201 : Nat := 4983230072969 + 3 ^ 40 * 1225201 * 2
def baseEnd_1225201 : Nat := 69901890152151792128101

theorem tailTrace_1225201 : CollatzResearch.WordTrace tailWord_1225201 prefixEnd_1225201 69901890152151792128101 := by
  unfold tailWord_1225201
  simp only [CollatzResearch.WordTrace]
  refine ⟨44686751634313499516851457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29791167756208999677900971 44686751634313499516851457)
  ·
    refine ⟨33515063725735124637638593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44686751634313499516851457 33515063725735124637638593)
    ·
      refine ⟨25136297794301343478228945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33515063725735124637638593 25136297794301343478228945)
      ·
        refine ⟨18852223345726007608671709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25136297794301343478228945 18852223345726007608671709)
        ·
          refine ⟨7069583754647252853251891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18852223345726007608671709 7069583754647252853251891)
          ·
            refine ⟨10604375631970879279877837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7069583754647252853251891 10604375631970879279877837)
            ·
              refine ⟨3976640861989079729954189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10604375631970879279877837 3976640861989079729954189)
              ·
                refine ⟨1491240323245904898732821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3976640861989079729954189 1491240323245904898732821)
                ·
                  refine ⟨69901890152151792128101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1491240323245904898732821 69901890152151792128101)
                  ·
                    rfl

theorem cell23_1225201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 3, 6].length) (baseStart_1225201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1225201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1225201 prefixEnd_1225201 := by exact prefixLift 1225201
  have htrace : WordTrace (prefixWord ++ tailWord_1225201) baseStart_1225201 baseEnd_1225201 := by
    simpa [prefixWord, tailWord_1225201, baseEnd_1225201] using wordTrace_append hprefix tailTrace_1225201
  have hstable : (prefixWord ++ tailWord_1225201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1225201).length < 2 ^ (prefixWord ++ tailWord_1225201).sum := by decide
  have hdescent : baseEnd_1225201 < baseStart_1225201 := by decide
  rcases family_descends (prefixWord ++ tailWord_1225201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1225262 : List Nat := [4, 1, 3, 1, 3, 1, 1, 2, 3, 1, 3]
def baseStart_1225262 : Nat := 118140960795 + 1225262 * 2 ^ 59
def prefixEnd_1225262 : Nat := 4983230072969 + 3 ^ 40 * 1225262 * 2
def baseEnd_1225262 : Nat := 629148333689290390490129

theorem tailTrace_1225262 : CollatzResearch.WordTrace tailWord_1225262 prefixEnd_1225262 629148333689290390490129 := by
  unfold tailWord_1225262
  simp only [CollatzResearch.WordTrace]
  refine ⟨5586122060886563366852755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29792650991395004623214693 5586122060886563366852755)
  ·
    refine ⟨8379183091329845050279133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5586122060886563366852755 8379183091329845050279133)
    ·
      refine ⟨3142193659248691893854675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8379183091329845050279133 3142193659248691893854675)
      ·
        refine ⟨4713290488873037840782013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3142193659248691893854675 4713290488873037840782013)
        ·
          refine ⟨1767483933327389190293255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4713290488873037840782013 1767483933327389190293255)
          ·
            refine ⟨2651225899991083785439883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1767483933327389190293255 2651225899991083785439883)
            ·
              refine ⟨3976838849986625678159825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2651225899991083785439883 3976838849986625678159825)
              ·
                refine ⟨2982629137489969258619869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3976838849986625678159825 2982629137489969258619869)
                ·
                  refine ⟨1118485926558738471982451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2982629137489969258619869 1118485926558738471982451)
                  ·
                    refine ⟨1677728889838107707973677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1118485926558738471982451 1677728889838107707973677)
                    ·
                      refine ⟨629148333689290390490129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1677728889838107707973677 629148333689290390490129)
                      ·
                        rfl

theorem cell23_1225262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 2, 3, 1, 3].length) (baseStart_1225262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1225262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1225262 prefixEnd_1225262 := by exact prefixLift 1225262
  have htrace : WordTrace (prefixWord ++ tailWord_1225262) baseStart_1225262 baseEnd_1225262 := by
    simpa [prefixWord, tailWord_1225262, baseEnd_1225262] using wordTrace_append hprefix tailTrace_1225262
  have hstable : (prefixWord ++ tailWord_1225262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1225262).length < 2 ^ (prefixWord ++ tailWord_1225262).sum := by decide
  have hdescent : baseEnd_1225262 < baseStart_1225262 := by decide
  rcases family_descends (prefixWord ++ tailWord_1225262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1225285 : List Nat := [1, 3, 1, 1, 1, 5, 4, 1, 1, 1, 4]
def baseStart_1225285 : Nat := 118140960795 + 1225285 * 2 ^ 59
def prefixEnd_1225285 : Nat := 4983230072969 + 3 ^ 40 * 1225285 * 2
def baseEnd_1225285 : Nat := 629160143744343800502523

theorem tailTrace_1225285 : CollatzResearch.WordTrace tailWord_1225285 prefixEnd_1225285 629160143744343800502523 := by
  unfold tailWord_1225285
  simp only [CollatzResearch.WordTrace]
  refine ⟨44689815366009181862909309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29793210244006121241939539 44689815366009181862909309)
  ·
    refine ⟨16758680762253443198590991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44689815366009181862909309 16758680762253443198590991)
    ·
      refine ⟨25138021143380164797886487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16758680762253443198590991 25138021143380164797886487)
      ·
        refine ⟨37707031715070247196829731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25138021143380164797886487 37707031715070247196829731)
        ·
          refine ⟨56560547572605370795244597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37707031715070247196829731 56560547572605370795244597)
          ·
            refine ⟨5302551334931753512054181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 56560547572605370795244597 5302551334931753512054181)
            ·
              refine ⟨994228375299703783510159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5302551334931753512054181 994228375299703783510159)
              ·
                refine ⟨1491342562949555675265239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 994228375299703783510159 1491342562949555675265239)
                ·
                  refine ⟨2237013844424333512897859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1491342562949555675265239 2237013844424333512897859)
                  ·
                    refine ⟨3355520766636500269346789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2237013844424333512897859 3355520766636500269346789)
                    ·
                      refine ⟨629160143744343800502523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3355520766636500269346789 629160143744343800502523)
                      ·
                        rfl

theorem cell23_1225285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 4, 1, 1, 1, 4].length) (baseStart_1225285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1225285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1225285 prefixEnd_1225285 := by exact prefixLift 1225285
  have htrace : WordTrace (prefixWord ++ tailWord_1225285) baseStart_1225285 baseEnd_1225285 := by
    simpa [prefixWord, tailWord_1225285, baseEnd_1225285] using wordTrace_append hprefix tailTrace_1225285
  have hstable : (prefixWord ++ tailWord_1225285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1225285).length < 2 ^ (prefixWord ++ tailWord_1225285).sum := by decide
  have hdescent : baseEnd_1225285 < baseStart_1225285 := by decide
  rcases family_descends (prefixWord ++ tailWord_1225285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1225325 : List Nat := [1, 5, 1, 1, 3, 3, 2, 7]
def baseStart_1225325 : Nat := 118140960795 + 1225325 * 2 ^ 59
def prefixEnd_1225325 : Nat := 4983230072969 + 3 ^ 40 * 1225325 * 2
def baseEnd_1225325 : Nat := 23302988258167542370457

theorem tailTrace_1225325 : CollatzResearch.WordTrace tailWord_1225325 prefixEnd_1225325 23302988258167542370457 := by
  unfold tailWord_1225325
  simp only [CollatzResearch.WordTrace]
  refine ⟨44691274285864268694365429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29794182857242845796243619 44691274285864268694365429)
  ·
    refine ⟨4189806964299775190096759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 44691274285864268694365429 4189806964299775190096759)
    ·
      refine ⟨6284710446449662785145139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4189806964299775190096759 6284710446449662785145139)
      ·
        refine ⟨9427065669674494177717709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6284710446449662785145139 9427065669674494177717709)
        ·
          refine ⟨3535149626127935316644141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9427065669674494177717709 3535149626127935316644141)
          ·
            refine ⟨1325681109797975743741553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3535149626127935316644141 1325681109797975743741553)
            ·
              refine ⟨994260832348481807806165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1325681109797975743741553 994260832348481807806165)
              ·
                refine ⟨23302988258167542370457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 994260832348481807806165 23302988258167542370457)
                ·
                  rfl

theorem cell23_1225325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 2, 7].length) (baseStart_1225325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1225325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1225325 prefixEnd_1225325 := by exact prefixLift 1225325
  have htrace : WordTrace (prefixWord ++ tailWord_1225325) baseStart_1225325 baseEnd_1225325 := by
    simpa [prefixWord, tailWord_1225325, baseEnd_1225325] using wordTrace_append hprefix tailTrace_1225325
  have hstable : (prefixWord ++ tailWord_1225325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1225325).length < 2 ^ (prefixWord ++ tailWord_1225325).sum := by decide
  have hdescent : baseEnd_1225325 < baseStart_1225325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1225325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1225358 : List Nat := [4, 1, 1, 3, 1, 1, 2, 1, 2, 3, 4]
def baseStart_1225358 : Nat := 118140960795 + 1225358 * 2 ^ 59
def prefixEnd_1225358 : Nat := 4983230072969 + 3 ^ 40 * 1225358 * 2
def baseEnd_1225358 : Nat := 629197627832122014889687

theorem tailTrace_1225358 : CollatzResearch.WordTrace tailWord_1225358 prefixEnd_1225358 629197627832122014889687 := by
  unfold tailWord_1225358
  simp only [CollatzResearch.WordTrace]
  refine ⟨5586559736843089416289591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29794985263163143553544485 5586559736843089416289591)
  ·
    refine ⟨8379839605264634124434387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5586559736843089416289591 8379839605264634124434387)
    ·
      refine ⟨12569759407896951186651581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8379839605264634124434387 12569759407896951186651581)
      ·
        refine ⟨4713659777961356694994343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12569759407896951186651581 4713659777961356694994343)
        ·
          refine ⟨7070489666942035042491515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4713659777961356694994343 7070489666942035042491515)
          ·
            refine ⟨10605734500413052563737273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7070489666942035042491515 10605734500413052563737273)
            ·
              refine ⟨7954300875309789422802955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10605734500413052563737273 7954300875309789422802955)
              ·
                refine ⟨11931451312964684134204433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7954300875309789422802955 11931451312964684134204433)
                ·
                  refine ⟨8948588484723513100653325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11931451312964684134204433 8948588484723513100653325)
                  ·
                    refine ⟨3355720681771317412744997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8948588484723513100653325 3355720681771317412744997)
                    ·
                      refine ⟨629197627832122014889687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3355720681771317412744997 629197627832122014889687)
                      ·
                        rfl

theorem cell23_1225358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_1225358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1225358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1225358 prefixEnd_1225358 := by exact prefixLift 1225358
  have htrace : WordTrace (prefixWord ++ tailWord_1225358) baseStart_1225358 baseEnd_1225358 := by
    simpa [prefixWord, tailWord_1225358, baseEnd_1225358] using wordTrace_append hprefix tailTrace_1225358
  have hstable : (prefixWord ++ tailWord_1225358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1225358).length < 2 ^ (prefixWord ++ tailWord_1225358).sum := by decide
  have hdescent : baseEnd_1225358 < baseStart_1225358 := by decide
  rcases family_descends (prefixWord ++ tailWord_1225358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1225371 : List Nat := [1, 1, 1, 1, 1, 1, 2, 2, 5, 4, 4]
def baseStart_1225371 : Nat := 118140960795 + 1225371 * 2 ^ 59
def prefixEnd_1225371 : Nat := 4983230072969 + 3 ^ 40 * 1225371 * 2
def baseEnd_1225371 : Nat := 629204303080630464027127

theorem tailTrace_1225371 : CollatzResearch.WordTrace tailWord_1225371 prefixEnd_1225371 629204303080630464027127 := by
  unfold tailWord_1225371
  simp only [CollatzResearch.WordTrace]
  refine ⟨44692952043697618550539967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29795301362465079033693311 44692952043697618550539967)
  ·
    refine ⟨67039428065546427825809951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44692952043697618550539967 67039428065546427825809951)
    ·
      refine ⟨100559142098319641738714927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67039428065546427825809951 100559142098319641738714927)
      ·
        refine ⟨150838713147479462608072391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100559142098319641738714927 150838713147479462608072391)
        ·
          refine ⟨226258069721219193912108587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150838713147479462608072391 226258069721219193912108587)
          ·
            refine ⟨339387104581828790868162881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 226258069721219193912108587 339387104581828790868162881)
            ·
              refine ⟨254540328436371593151122161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 339387104581828790868162881 254540328436371593151122161)
              ·
                refine ⟨190905246327278694863341621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 254540328436371593151122161 190905246327278694863341621)
                ·
                  refine ⟨17897366843182377643438277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 190905246327278694863341621 17897366843182377643438277)
                  ·
                    refine ⟨3355756283096695808144677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17897366843182377643438277 3355756283096695808144677)
                    ·
                      refine ⟨629204303080630464027127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3355756283096695808144677 629204303080630464027127)
                      ·
                        rfl

theorem cell23_1225371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5, 4, 4].length) (baseStart_1225371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1225371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1225371 prefixEnd_1225371 := by exact prefixLift 1225371
  have htrace : WordTrace (prefixWord ++ tailWord_1225371) baseStart_1225371 baseEnd_1225371 := by
    simpa [prefixWord, tailWord_1225371, baseEnd_1225371] using wordTrace_append hprefix tailTrace_1225371
  have hstable : (prefixWord ++ tailWord_1225371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1225371).length < 2 ^ (prefixWord ++ tailWord_1225371).sum := by decide
  have hdescent : baseEnd_1225371 < baseStart_1225371 := by decide
  rcases family_descends (prefixWord ++ tailWord_1225371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1225381 : List Nat := [1, 3, 1, 2, 1, 2, 1, 3, 9]
def baseStart_1225381 : Nat := 118140960795 + 1225381 * 2 ^ 59
def prefixEnd_1225381 : Nat := 4983230072969 + 3 ^ 40 * 1225381 * 2
def baseEnd_1225381 : Nat := 69912159765241713878009

theorem tailTrace_1225381 : CollatzResearch.WordTrace tailWord_1225381 prefixEnd_1225381 69912159765241713878009 := by
  unfold tailWord_1225381
  simp only [CollatzResearch.WordTrace]
  refine ⟨44693316773661390258403997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29795544515774260172269331 44693316773661390258403997)
  ·
    refine ⟨16759993790123021346901499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44693316773661390258403997 16759993790123021346901499)
    ·
      refine ⟨25139990685184532020352249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16759993790123021346901499 25139990685184532020352249)
      ·
        refine ⟨18854993013888399015264187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25139990685184532020352249 18854993013888399015264187)
        ·
          refine ⟨28282489520832598522896281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18854993013888399015264187 28282489520832598522896281)
          ·
            refine ⟨21211867140624448892172211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28282489520832598522896281 21211867140624448892172211)
            ·
              refine ⟨31817800710936673338258317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21211867140624448892172211 31817800710936673338258317)
              ·
                refine ⟨11931675266601252501846869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31817800710936673338258317 11931675266601252501846869)
                ·
                  refine ⟨69912159765241713878009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 11931675266601252501846869 69912159765241713878009)
                  ·
                    rfl

theorem cell23_1225381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 3, 9].length) (baseStart_1225381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1225381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1225381 prefixEnd_1225381 := by exact prefixLift 1225381
  have htrace : WordTrace (prefixWord ++ tailWord_1225381) baseStart_1225381 baseEnd_1225381 := by
    simpa [prefixWord, tailWord_1225381, baseEnd_1225381] using wordTrace_append hprefix tailTrace_1225381
  have hstable : (prefixWord ++ tailWord_1225381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1225381).length < 2 ^ (prefixWord ++ tailWord_1225381).sum := by decide
  have hdescent : baseEnd_1225381 < baseStart_1225381 := by decide
  rcases family_descends (prefixWord ++ tailWord_1225381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1225445 : List Nat := [1, 3, 1, 4, 1, 2, 3, 1, 2, 5]
def baseStart_1225445 : Nat := 118140960795 + 1225445 * 2 ^ 59
def prefixEnd_1225445 : Nat := 4983230072969 + 3 ^ 40 * 1225445 * 2
def baseEnd_1225445 : Nat := 209747433549687724833929

theorem tailTrace_1225445 : CollatzResearch.WordTrace tailWord_1225445 prefixEnd_1225445 209747433549687724833929 := by
  unfold tailWord_1225445
  simp only [CollatzResearch.WordTrace]
  refine ⟨44695651045429529188733789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29797100696953019459155859 44695651045429529188733789)
  ·
    refine ⟨16760869142036073445775171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44695651045429529188733789 16760869142036073445775171)
    ·
      refine ⟨25141303713054110168662757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16760869142036073445775171 25141303713054110168662757)
      ·
        refine ⟨4713994446197645656624267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25141303713054110168662757 4713994446197645656624267)
        ·
          refine ⟨7070991669296468484936401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4713994446197645656624267 7070991669296468484936401)
          ·
            refine ⟨5303243751972351363702301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7070991669296468484936401 5303243751972351363702301)
            ·
              refine ⟨1988716406989631761388363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5303243751972351363702301 1988716406989631761388363)
              ·
                refine ⟨2983074610484447642082545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1988716406989631761388363 2983074610484447642082545)
                ·
                  refine ⟨2237305957863335731561909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2983074610484447642082545 2237305957863335731561909)
                  ·
                    refine ⟨209747433549687724833929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2237305957863335731561909 209747433549687724833929)
                    ·
                      rfl

theorem cell23_1225445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 3, 1, 2, 5].length) (baseStart_1225445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1225445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1225445 prefixEnd_1225445 := by exact prefixLift 1225445
  have htrace : WordTrace (prefixWord ++ tailWord_1225445) baseStart_1225445 baseEnd_1225445 := by
    simpa [prefixWord, tailWord_1225445, baseEnd_1225445] using wordTrace_append hprefix tailTrace_1225445
  have hstable : (prefixWord ++ tailWord_1225445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1225445).length < 2 ^ (prefixWord ++ tailWord_1225445).sum := by decide
  have hdescent : baseEnd_1225445 < baseStart_1225445 := by decide
  rcases family_descends (prefixWord ++ tailWord_1225445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1225460 : List Nat := [2, 6, 1, 1, 2, 2, 1, 2, 2, 2, 2]
def baseStart_1225460 : Nat := 118140960795 + 1225460 * 2 ^ 59
def prefixEnd_1225460 : Nat := 4983230072969 + 3 ^ 40 * 1225460 * 2
def baseEnd_1225460 : Nat := 629250002858880615814219

theorem tailTrace_1225460 : CollatzResearch.WordTrace tailWord_1225460 prefixEnd_1225460 629250002858880615814219 := by
  unfold tailWord_1225460
  simp only [CollatzResearch.WordTrace]
  refine ⟨22348099070187593375264917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29797465426916791167019889 22348099070187593375264917)
  ·
    refine ⟨1047567143915043439465543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 22348099070187593375264917 1047567143915043439465543)
    ·
      refine ⟨1571350715872565159198315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1047567143915043439465543 1571350715872565159198315)
      ·
        refine ⟨2357026073808847738797473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1571350715872565159198315 2357026073808847738797473)
        ·
          refine ⟨1767769555356635804098105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2357026073808847738797473 1767769555356635804098105)
          ·
            refine ⟨1325827166517476853073579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1767769555356635804098105 1325827166517476853073579)
            ·
              refine ⟨1988740749776215279610369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1325827166517476853073579 1988740749776215279610369)
              ·
                refine ⟨1491555562332161459707777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1988740749776215279610369 1491555562332161459707777)
                ·
                  refine ⟨1118666671749121094780833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1491555562332161459707777 1118666671749121094780833)
                  ·
                    refine ⟨839000003811840821085625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1118666671749121094780833 839000003811840821085625)
                    ·
                      refine ⟨629250002858880615814219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 839000003811840821085625 629250002858880615814219)
                      ·
                        rfl

theorem cell23_1225460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 1, 2, 2, 2, 2].length) (baseStart_1225460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1225460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1225460 prefixEnd_1225460 := by exact prefixLift 1225460
  have htrace : WordTrace (prefixWord ++ tailWord_1225460) baseStart_1225460 baseEnd_1225460 := by
    simpa [prefixWord, tailWord_1225460, baseEnd_1225460] using wordTrace_append hprefix tailTrace_1225460
  have hstable : (prefixWord ++ tailWord_1225460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1225460).length < 2 ^ (prefixWord ++ tailWord_1225460).sum := by decide
  have hdescent : baseEnd_1225460 < baseStart_1225460 := by decide
  rcases family_descends (prefixWord ++ tailWord_1225460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1225515 : List Nat := [1, 1, 1, 1, 2, 1, 2, 3, 7, 1, 3]
def baseStart_1225515 : Nat := 118140960795 + 1225515 * 2 ^ 59
def prefixEnd_1225515 : Nat := 4983230072969 + 3 ^ 40 * 1225515 * 2
def baseEnd_1225515 : Nat := 629278244294877900626465

theorem tailTrace_1225515 : CollatzResearch.WordTrace tailWord_1225515 prefixEnd_1225515 629278244294877900626465 := by
  unfold tailWord_1225515
  simp only [CollatzResearch.WordTrace]
  refine ⟨44698204155175931143781999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29798802770117287429187999 44698204155175931143781999)
  ·
    refine ⟨67047306232763896715672999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44698204155175931143781999 67047306232763896715672999)
    ·
      refine ⟨100570959349145845073509499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67047306232763896715672999 100570959349145845073509499)
      ·
        refine ⟨150856439023718767610264249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100570959349145845073509499 150856439023718767610264249)
        ·
          refine ⟨113142329267789075707698187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 150856439023718767610264249 113142329267789075707698187)
          ·
            refine ⟨169713493901683613561547281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113142329267789075707698187 169713493901683613561547281)
            ·
              refine ⟨127285120426262710171160461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 169713493901683613561547281 127285120426262710171160461)
              ·
                refine ⟨47731920159848516314185173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 127285120426262710171160461 47731920159848516314185173)
                ·
                  refine ⟨1118716878746449601113715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 47731920159848516314185173 1118716878746449601113715)
                  ·
                    refine ⟨1678075318119674401670573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1118716878746449601113715 1678075318119674401670573)
                    ·
                      refine ⟨629278244294877900626465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1678075318119674401670573 629278244294877900626465)
                      ·
                        rfl

theorem cell23_1225515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 7, 1, 3].length) (baseStart_1225515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1225515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1225515 prefixEnd_1225515 := by exact prefixLift 1225515
  have htrace : WordTrace (prefixWord ++ tailWord_1225515) baseStart_1225515 baseEnd_1225515 := by
    simpa [prefixWord, tailWord_1225515, baseEnd_1225515] using wordTrace_append hprefix tailTrace_1225515
  have hstable : (prefixWord ++ tailWord_1225515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1225515).length < 2 ^ (prefixWord ++ tailWord_1225515).sum := by decide
  have hdescent : baseEnd_1225515 < baseStart_1225515 := by decide
  rcases family_descends (prefixWord ++ tailWord_1225515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1225526 : List Nat := [5, 1, 2, 2, 2, 2, 1, 1, 3, 4]
def baseStart_1225526 : Nat := 118140960795 + 1225526 * 2 ^ 59
def prefixEnd_1225526 : Nat := 4983230072969 + 3 ^ 40 * 1225526 * 2
def baseEnd_1225526 : Nat := 209761297527359119196305

theorem tailTrace_1225526 : CollatzResearch.WordTrace tailWord_1225526 prefixEnd_1225526 209761297527359119196305 := by
  unfold tailWord_1225526
  simp only [CollatzResearch.WordTrace]
  refine ⟨2793662834883505001402027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 29799070238757386681621621 2793662834883505001402027)
  ·
    refine ⟨4190494252325257502103041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2793662834883505001402027 4190494252325257502103041)
    ·
      refine ⟨3142870689243943126577281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4190494252325257502103041 3142870689243943126577281)
      ·
        refine ⟨2357153016932957344932961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3142870689243943126577281 2357153016932957344932961)
        ·
          refine ⟨1767864762699718008699721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2357153016932957344932961 1767864762699718008699721)
          ·
            refine ⟨1325898572024788506524791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1767864762699718008699721 1325898572024788506524791)
            ·
              refine ⟨1988847858037182759787187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1325898572024788506524791 1988847858037182759787187)
              ·
                refine ⟨2983271787055774139680781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1988847858037182759787187 2983271787055774139680781)
                ·
                  refine ⟨1118726920145915302380293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2983271787055774139680781 1118726920145915302380293)
                  ·
                    refine ⟨209761297527359119196305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1118726920145915302380293 209761297527359119196305)
                    ·
                      rfl

theorem cell23_1225526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 1, 1, 3, 4].length) (baseStart_1225526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1225526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1225526 prefixEnd_1225526 := by exact prefixLift 1225526
  have htrace : WordTrace (prefixWord ++ tailWord_1225526) baseStart_1225526 baseEnd_1225526 := by
    simpa [prefixWord, tailWord_1225526, baseEnd_1225526] using wordTrace_append hprefix tailTrace_1225526
  have hstable : (prefixWord ++ tailWord_1225526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1225526).length < 2 ^ (prefixWord ++ tailWord_1225526).sum := by decide
  have hdescent : baseEnd_1225526 < baseStart_1225526 := by decide
  rcases family_descends (prefixWord ++ tailWord_1225526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1225555 : List Nat := [1, 1, 1, 2, 1, 1, 3, 3, 2, 6, 2]
def baseStart_1225555 : Nat := 118140960795 + 1225555 * 2 ^ 59
def prefixEnd_1225555 : Nat := 4983230072969 + 3 ^ 40 * 1225555 * 2
def baseEnd_1225555 : Nat := 629298783521057744126281

theorem tailTrace_1225555 : CollatzResearch.WordTrace tailWord_1225555 prefixEnd_1225555 629298783521057744126281 := by
  unfold tailWord_1225555
  simp only [CollatzResearch.WordTrace]
  refine ⟨44699663075031017975238119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29799775383354011983492079 44699663075031017975238119)
  ·
    refine ⟨67049494612546526962857179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44699663075031017975238119 67049494612546526962857179)
    ·
      refine ⟨100574241918819790444285769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67049494612546526962857179 100574241918819790444285769)
      ·
        refine ⟨75430681439114842833214327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100574241918819790444285769 75430681439114842833214327)
        ·
          refine ⟨113146022158672264249821491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75430681439114842833214327 113146022158672264249821491)
          ·
            refine ⟨169719033238008396374732237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113146022158672264249821491 169719033238008396374732237)
            ·
              refine ⟨63644637464253148640524589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 169719033238008396374732237 63644637464253148640524589)
              ·
                refine ⟨23866739049094930740196721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63644637464253148640524589 23866739049094930740196721)
                ·
                  refine ⟨17900054286821198055147541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23866739049094930740196721 17900054286821198055147541)
                  ·
                    refine ⟨839065044694743658835041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17900054286821198055147541 839065044694743658835041)
                    ·
                      refine ⟨629298783521057744126281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 839065044694743658835041 629298783521057744126281)
                      ·
                        rfl

theorem cell23_1225555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 3, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 3, 2, 6, 2].length) (baseStart_1225555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1225555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1225555 prefixEnd_1225555 := by exact prefixLift 1225555
  have htrace : WordTrace (prefixWord ++ tailWord_1225555) baseStart_1225555 baseEnd_1225555 := by
    simpa [prefixWord, tailWord_1225555, baseEnd_1225555] using wordTrace_append hprefix tailTrace_1225555
  have hstable : (prefixWord ++ tailWord_1225555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1225555).length < 2 ^ (prefixWord ++ tailWord_1225555).sum := by decide
  have hdescent : baseEnd_1225555 < baseStart_1225555 := by decide
  rcases family_descends (prefixWord ++ tailWord_1225555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1225559 : List Nat := [1, 1, 3, 2, 4, 2, 2, 1, 2, 3, 2]
def baseStart_1225559 : Nat := 118140960795 + 1225559 * 2 ^ 59
def prefixEnd_1225559 : Nat := 4983230072969 + 3 ^ 40 * 1225559 * 2
def baseEnd_1225559 : Nat := 629300837443675728476263

theorem tailTrace_1225559 : CollatzResearch.WordTrace tailWord_1225559 prefixEnd_1225559 629300837443675728476263 := by
  unfold tailWord_1225559
  simp only [CollatzResearch.WordTrace]
  refine ⟨44699808967016526658383731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29799872644677684438922487 44699808967016526658383731)
  ·
    refine ⟨67049713450524789987575597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44699808967016526658383731 67049713450524789987575597)
    ·
      refine ⟨25143642543946796245340849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67049713450524789987575597 25143642543946796245340849)
      ·
        refine ⟨18857731907960097184005637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25143642543946796245340849 18857731907960097184005637)
        ·
          refine ⟨3535824732742518222001057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18857731907960097184005637 3535824732742518222001057)
          ·
            refine ⟨2651868549556888666500793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3535824732742518222001057 2651868549556888666500793)
            ·
              refine ⟨1988901412167666499875595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2651868549556888666500793 1988901412167666499875595)
              ·
                refine ⟨2983352118251499749813393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1988901412167666499875595 2983352118251499749813393)
                ·
                  refine ⟨2237514088688624812360045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2983352118251499749813393 2237514088688624812360045)
                  ·
                    refine ⟨839067783258234304635017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2237514088688624812360045 839067783258234304635017)
                    ·
                      refine ⟨629300837443675728476263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 839067783258234304635017 629300837443675728476263)
                      ·
                        rfl

theorem cell23_1225559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 2, 1, 2, 3, 2].length) (baseStart_1225559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1225559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1225559 prefixEnd_1225559 := by exact prefixLift 1225559
  have htrace : WordTrace (prefixWord ++ tailWord_1225559) baseStart_1225559 baseEnd_1225559 := by
    simpa [prefixWord, tailWord_1225559, baseEnd_1225559] using wordTrace_append hprefix tailTrace_1225559
  have hstable : (prefixWord ++ tailWord_1225559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1225559).length < 2 ^ (prefixWord ++ tailWord_1225559).sum := by decide
  have hdescent : baseEnd_1225559 < baseStart_1225559 := by decide
  rcases family_descends (prefixWord ++ tailWord_1225559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1225578 : List Nat := [3, 1, 3, 16]
def baseStart_1225578 : Nat := 118140960795 + 1225578 * 2 ^ 59
def prefixEnd_1225578 : Nat := 4983230072969 + 3 ^ 40 * 1225578 * 2
def baseEnd_1225578 : Nat := 287750614346644332025

theorem tailTrace_1225578 : CollatzResearch.WordTrace tailWord_1225578 prefixEnd_1225578 287750614346644332025 := by
  unfold tailWord_1225578
  simp only [CollatzResearch.WordTrace]
  refine ⟨11175125488486923225831347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29800334635965128602216925 11175125488486923225831347)
  ·
    refine ⟨16762688232730384838747021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11175125488486923225831347 16762688232730384838747021)
    ·
      refine ⟨6286008087273894314530133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16762688232730384838747021 6286008087273894314530133)
      ·
        refine ⟨287750614346644332025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 16 6286008087273894314530133 287750614346644332025)
        ·
          rfl

theorem cell23_1225578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 16].length) (baseStart_1225578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1225578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1225578 prefixEnd_1225578 := by exact prefixLift 1225578
  have htrace : WordTrace (prefixWord ++ tailWord_1225578) baseStart_1225578 baseEnd_1225578 := by
    simpa [prefixWord, tailWord_1225578, baseEnd_1225578] using wordTrace_append hprefix tailTrace_1225578
  have hstable : (prefixWord ++ tailWord_1225578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1225578).length < 2 ^ (prefixWord ++ tailWord_1225578).sum := by decide
  have hdescent : baseEnd_1225578 < baseStart_1225578 := by decide
  rcases family_descends (prefixWord ++ tailWord_1225578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1225655 : List Nat := [1, 1, 3, 1, 3, 1, 4, 1, 2, 6]
def baseStart_1225655 : Nat := 118140960795 + 1225655 * 2 ^ 59
def prefixEnd_1225655 : Nat := 4983230072969 + 3 ^ 40 * 1225655 * 2
def baseEnd_1225655 : Nat := 209783377195502450958607

theorem tailTrace_1225655 : CollatzResearch.WordTrace tailWord_1225655 prefixEnd_1225655 209783377195502450958607 := by
  unfold tailWord_1225655
  simp only [CollatzResearch.WordTrace]
  refine ⟨44703310374668735053878419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29802206916445823369252279 44703310374668735053878419)
  ·
    refine ⟨67054965562003102580817629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44703310374668735053878419 67054965562003102580817629)
    ·
      refine ⟨25145612085751163467806611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67054965562003102580817629 25145612085751163467806611)
      ·
        refine ⟨37718418128626745201709917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25145612085751163467806611 37718418128626745201709917)
        ·
          refine ⟨14144406798235029450641219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37718418128626745201709917 14144406798235029450641219)
          ·
            refine ⟨21216610197352544175961829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14144406798235029450641219 21216610197352544175961829)
            ·
              refine ⟨3978114412003602032992843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21216610197352544175961829 3978114412003602032992843)
              ·
                refine ⟨5967171618005403049489265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3978114412003602032992843 5967171618005403049489265)
                ·
                  refine ⟨4475378713504052287116949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5967171618005403049489265 4475378713504052287116949)
                  ·
                    refine ⟨209783377195502450958607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4475378713504052287116949 209783377195502450958607)
                    ·
                      rfl

theorem cell23_1225655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 1, 2, 6].length) (baseStart_1225655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1225655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1225655 prefixEnd_1225655 := by exact prefixLift 1225655
  have htrace : WordTrace (prefixWord ++ tailWord_1225655) baseStart_1225655 baseEnd_1225655 := by
    simpa [prefixWord, tailWord_1225655, baseEnd_1225655] using wordTrace_append hprefix tailTrace_1225655
  have hstable : (prefixWord ++ tailWord_1225655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1225655).length < 2 ^ (prefixWord ++ tailWord_1225655).sum := by decide
  have hdescent : baseEnd_1225655 < baseStart_1225655 := by decide
  rcases family_descends (prefixWord ++ tailWord_1225655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1225656 : List Nat := [2, 1, 2, 1, 2, 5, 3, 1, 2, 1, 3]
def baseStart_1225656 : Nat := 118140960795 + 1225656 * 2 ^ 59
def prefixEnd_1225656 : Nat := 4983230072969 + 3 ^ 40 * 1225656 * 2
def baseEnd_1225656 : Nat := 629350645067161848963317

theorem tailTrace_1225656 : CollatzResearch.WordTrace tailWord_1225656 prefixEnd_1225656 629350645067161848963317 := by
  unfold tailWord_1225656
  simp only [CollatzResearch.WordTrace]
  refine ⟨22351673423832556112332411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29802231231776741483109881 22351673423832556112332411)
  ·
    refine ⟨33527510135748834168498617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22351673423832556112332411 33527510135748834168498617)
    ·
      refine ⟨25145632601811625626373963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33527510135748834168498617 25145632601811625626373963)
      ·
        refine ⟨37718448902717438439560945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25145632601811625626373963 37718448902717438439560945)
        ·
          refine ⟨28288836677038078829670709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37718448902717438439560945 28288836677038078829670709)
          ·
            refine ⟨2652078438472319890281629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28288836677038078829670709 2652078438472319890281629)
            ·
              refine ⟨994529414427119958855611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2652078438472319890281629 994529414427119958855611)
              ·
                refine ⟨1491794121640679938283417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 994529414427119958855611 1491794121640679938283417)
                ·
                  refine ⟨1118845591230509953712563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1491794121640679938283417 1118845591230509953712563)
                  ·
                    refine ⟨1678268386845764930568845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1118845591230509953712563 1678268386845764930568845)
                    ·
                      refine ⟨629350645067161848963317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1678268386845764930568845 629350645067161848963317)
                      ·
                        rfl

theorem cell23_1225656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 3, 1, 2, 1, 3].length) (baseStart_1225656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1225656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1225656 prefixEnd_1225656 := by exact prefixLift 1225656
  have htrace : WordTrace (prefixWord ++ tailWord_1225656) baseStart_1225656 baseEnd_1225656 := by
    simpa [prefixWord, tailWord_1225656, baseEnd_1225656] using wordTrace_append hprefix tailTrace_1225656
  have hstable : (prefixWord ++ tailWord_1225656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1225656).length < 2 ^ (prefixWord ++ tailWord_1225656).sum := by decide
  have hdescent : baseEnd_1225656 < baseStart_1225656 := by decide
  rcases family_descends (prefixWord ++ tailWord_1225656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1225679 : List Nat := [1, 1, 2, 1, 1, 6, 1, 2, 4, 2, 2]
def baseStart_1225679 : Nat := 118140960795 + 1225679 * 2 ^ 59
def prefixEnd_1225679 : Nat := 4983230072969 + 3 ^ 40 * 1225679 * 2
def baseEnd_1225679 : Nat := 629362455122215258975711

theorem tailTrace_1225679 : CollatzResearch.WordTrace tailWord_1225679 prefixEnd_1225679 629362455122215258975711 := by
  unfold tailWord_1225679
  simp only [CollatzResearch.WordTrace]
  refine ⟨44704185726581787152752091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29802790484387858101834727 44704185726581787152752091)
  ·
    refine ⟨67056278589872680729128137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44704185726581787152752091 67056278589872680729128137)
    ·
      refine ⟨50292208942404510546846103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67056278589872680729128137 50292208942404510546846103)
      ·
        refine ⟨75438313413606765820269155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50292208942404510546846103 75438313413606765820269155)
        ·
          refine ⟨113157470120410148730403733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75438313413606765820269155 113157470120410148730403733)
          ·
            refine ⟨5304256411894225721737675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 113157470120410148730403733 5304256411894225721737675)
            ·
              refine ⟨7956384617841338582606513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5304256411894225721737675 7956384617841338582606513)
              ·
                refine ⟨5967288463381003936954885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7956384617841338582606513 5967288463381003936954885)
                ·
                  refine ⟨1118866586883938238179041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5967288463381003936954885 1118866586883938238179041)
                  ·
                    refine ⟨839149940162953678634281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1118866586883938238179041 839149940162953678634281)
                    ·
                      refine ⟨629362455122215258975711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 839149940162953678634281 629362455122215258975711)
                      ·
                        rfl

theorem cell23_1225679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 2, 4, 2, 2].length) (baseStart_1225679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1225679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1225679 prefixEnd_1225679 := by exact prefixLift 1225679
  have htrace : WordTrace (prefixWord ++ tailWord_1225679) baseStart_1225679 baseEnd_1225679 := by
    simpa [prefixWord, tailWord_1225679, baseEnd_1225679] using wordTrace_append hprefix tailTrace_1225679
  have hstable : (prefixWord ++ tailWord_1225679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1225679).length < 2 ^ (prefixWord ++ tailWord_1225679).sum := by decide
  have hdescent : baseEnd_1225679 < baseStart_1225679 := by decide
  rcases family_descends (prefixWord ++ tailWord_1225679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1225682 : List Nat := [3, 2, 2, 3, 1, 1, 1, 1, 1, 3, 5]
def baseStart_1225682 : Nat := 118140960795 + 1225682 * 2 ^ 59
def prefixEnd_1225682 : Nat := 4983230072969 + 3 ^ 40 * 1225682 * 2
def baseEnd_1225682 : Nat := 629363995564178747238197

theorem tailTrace_1225682 : CollatzResearch.WordTrace tailWord_1225682 prefixEnd_1225682 629363995564178747238197 := by
  unfold tailWord_1225682
  simp only [CollatzResearch.WordTrace]
  refine ⟨11176073786392729666277825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29802863430380612443407533 11176073786392729666277825)
  ·
    refine ⟨8382055339794547249708369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11176073786392729666277825 8382055339794547249708369)
    ·
      refine ⟨6286541504845910437281277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8382055339794547249708369 6286541504845910437281277)
      ·
        refine ⟨2357453064317216413980479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6286541504845910437281277 2357453064317216413980479)
        ·
          refine ⟨3536179596475824620970719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2357453064317216413980479 3536179596475824620970719)
          ·
            refine ⟨5304269394713736931456079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3536179596475824620970719 5304269394713736931456079)
            ·
              refine ⟨7956404092070605397184119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5304269394713736931456079 7956404092070605397184119)
              ·
                refine ⟨11934606138105908095776179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7956404092070605397184119 11934606138105908095776179)
                ·
                  refine ⟨17901909207158862143664269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11934606138105908095776179 17901909207158862143664269)
                  ·
                    refine ⟨6713215952684573303874101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17901909207158862143664269 6713215952684573303874101)
                    ·
                      refine ⟨629363995564178747238197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6713215952684573303874101 629363995564178747238197)
                      ·
                        rfl

theorem cell23_1225682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_1225682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1225682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1225682 prefixEnd_1225682 := by exact prefixLift 1225682
  have htrace : WordTrace (prefixWord ++ tailWord_1225682) baseStart_1225682 baseEnd_1225682 := by
    simpa [prefixWord, tailWord_1225682, baseEnd_1225682] using wordTrace_append hprefix tailTrace_1225682
  have hstable : (prefixWord ++ tailWord_1225682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1225682).length < 2 ^ (prefixWord ++ tailWord_1225682).sum := by decide
  have hdescent : baseEnd_1225682 < baseStart_1225682 := by decide
  rcases family_descends (prefixWord ++ tailWord_1225682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1225713 : List Nat := [1, 2, 2, 2, 4, 1, 4, 1, 2, 2, 2]
def baseStart_1225713 : Nat := 118140960795 + 1225713 * 2 ^ 59
def prefixEnd_1225713 : Nat := 4983230072969 + 3 ^ 40 * 1225713 * 2
def baseEnd_1225713 : Nat := 629379913464468125950555

theorem tailTrace_1225713 : CollatzResearch.WordTrace tailWord_1225713 prefixEnd_1225713 629379913464468125950555 := by
  unfold tailWord_1225713
  simp only [CollatzResearch.WordTrace]
  refine ⟨44705425808458610959489793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29803617205639073972993195 44705425808458610959489793)
  ·
    refine ⟨33529069356343958219617345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44705425808458610959489793 33529069356343958219617345)
    ·
      refine ⟨25146802017257968664713009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33529069356343958219617345 25146802017257968664713009)
      ·
        refine ⟨18860101512943476498534757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25146802017257968664713009 18860101512943476498534757)
        ·
          refine ⟨3536269033676901843475267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18860101512943476498534757 3536269033676901843475267)
          ·
            refine ⟨5304403550515352765212901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3536269033676901843475267 5304403550515352765212901)
            ·
              refine ⟨994575665721628643477419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5304403550515352765212901 994575665721628643477419)
              ·
                refine ⟨1491863498582442965216129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 994575665721628643477419 1491863498582442965216129)
                ·
                  refine ⟨1118897623936832223912097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1491863498582442965216129 1118897623936832223912097)
                  ·
                    refine ⟨839173217952624167934073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1118897623936832223912097 839173217952624167934073)
                    ·
                      refine ⟨629379913464468125950555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 839173217952624167934073 629379913464468125950555)
                      ·
                        rfl

theorem cell23_1225713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 4, 1, 2, 2, 2].length) (baseStart_1225713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1225713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1225713 prefixEnd_1225713 := by exact prefixLift 1225713
  have htrace : WordTrace (prefixWord ++ tailWord_1225713) baseStart_1225713 baseEnd_1225713 := by
    simpa [prefixWord, tailWord_1225713, baseEnd_1225713] using wordTrace_append hprefix tailTrace_1225713
  have hstable : (prefixWord ++ tailWord_1225713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1225713).length < 2 ^ (prefixWord ++ tailWord_1225713).sum := by decide
  have hdescent : baseEnd_1225713 < baseStart_1225713 := by decide
  rcases family_descends (prefixWord ++ tailWord_1225713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1225717 : List Nat := [1, 3, 5, 2, 2, 1, 1, 2, 1, 3, 2]
def baseStart_1225717 : Nat := 118140960795 + 1225717 * 2 ^ 59
def prefixEnd_1225717 : Nat := 4983230072969 + 3 ^ 40 * 1225717 * 2
def baseEnd_1225717 : Nat := 629381967387086110300537

theorem tailTrace_1225717 : CollatzResearch.WordTrace tailWord_1225717 prefixEnd_1225717 629381967387086110300537 := by
  unfold tailWord_1225717
  simp only [CollatzResearch.WordTrace]
  refine ⟨44705571700444119642635405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29803714466962746428423603 44705571700444119642635405)
  ·
    refine ⟨16764589387666544865988277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44705571700444119642635405 16764589387666544865988277)
    ·
      refine ⟨1571680255093738581186401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16764589387666544865988277 1571680255093738581186401)
      ·
        refine ⟨1178760191320303935889801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1571680255093738581186401 1178760191320303935889801)
        ·
          refine ⟨884070143490227951917351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1178760191320303935889801 884070143490227951917351)
          ·
            refine ⟨1326105215235341927876027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 884070143490227951917351 1326105215235341927876027)
            ·
              refine ⟨1989157822853012891814041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1326105215235341927876027 1989157822853012891814041)
              ·
                refine ⟨1491868367139759668860531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1989157822853012891814041 1491868367139759668860531)
                ·
                  refine ⟨2237802550709639503290797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1491868367139759668860531 2237802550709639503290797)
                  ·
                    refine ⟨839175956516114813734049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2237802550709639503290797 839175956516114813734049)
                    ·
                      refine ⟨629381967387086110300537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 839175956516114813734049 629381967387086110300537)
                      ·
                        rfl

theorem cell23_1225717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_1225717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1225717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1225717 prefixEnd_1225717 := by exact prefixLift 1225717
  have htrace : WordTrace (prefixWord ++ tailWord_1225717) baseStart_1225717 baseEnd_1225717 := by
    simpa [prefixWord, tailWord_1225717, baseEnd_1225717] using wordTrace_append hprefix tailTrace_1225717
  have hstable : (prefixWord ++ tailWord_1225717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1225717).length < 2 ^ (prefixWord ++ tailWord_1225717).sum := by decide
  have hdescent : baseEnd_1225717 < baseStart_1225717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1225717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1225725 : List Nat := [1, 4, 1, 1, 1, 2, 1, 1, 3, 1, 7]
def baseStart_1225725 : Nat := 118140960795 + 1225725 * 2 ^ 59
def prefixEnd_1225725 : Nat := 4983230072969 + 3 ^ 40 * 1225725 * 2
def baseEnd_1225725 : Nat := 629386075232322079000499

theorem tailTrace_1225725 : CollatzResearch.WordTrace tailWord_1225725 prefixEnd_1225725 629386075232322079000499 := by
  unfold tailWord_1225725
  simp only [CollatzResearch.WordTrace]
  refine ⟨44705863484415137008926629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29803908989610091339284419 44705863484415137008926629)
  ·
    refine ⟨8382349403327838189173743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44705863484415137008926629 8382349403327838189173743)
    ·
      refine ⟨12573524104991757283760615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8382349403327838189173743 12573524104991757283760615)
      ·
        refine ⟨18860286157487635925640923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12573524104991757283760615 18860286157487635925640923)
        ·
          refine ⟨28290429236231453888461385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18860286157487635925640923 28290429236231453888461385)
          ·
            refine ⟨21217821927173590416346039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28290429236231453888461385 21217821927173590416346039)
            ·
              refine ⟨31826732890760385624519059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21217821927173590416346039 31826732890760385624519059)
              ·
                refine ⟨47740099336140578436778589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31826732890760385624519059 47740099336140578436778589)
                ·
                  refine ⟨17902537251052716913791971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47740099336140578436778589 17902537251052716913791971)
                  ·
                    refine ⟨26853805876579075370687957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17902537251052716913791971 26853805876579075370687957)
                    ·
                      refine ⟨629386075232322079000499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 26853805876579075370687957 629386075232322079000499)
                      ·
                        rfl

theorem cell23_1225725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 3, 1, 7].length) (baseStart_1225725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1225725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1225725 prefixEnd_1225725 := by exact prefixLift 1225725
  have htrace : WordTrace (prefixWord ++ tailWord_1225725) baseStart_1225725 baseEnd_1225725 := by
    simpa [prefixWord, tailWord_1225725, baseEnd_1225725] using wordTrace_append hprefix tailTrace_1225725
  have hstable : (prefixWord ++ tailWord_1225725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1225725).length < 2 ^ (prefixWord ++ tailWord_1225725).sum := by decide
  have hdescent : baseEnd_1225725 < baseStart_1225725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1225725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1225742 : List Nat := [4, 1, 1, 2, 2, 2, 1, 2, 1, 2, 5]
def baseStart_1225742 : Nat := 118140960795 + 1225742 * 2 ^ 59
def prefixEnd_1225742 : Nat := 4983230072969 + 3 ^ 40 * 1225742 * 2
def baseEnd_1225742 : Nat := 629394804403448512487921

theorem tailTrace_1225742 : CollatzResearch.WordTrace tailWord_1225742 prefixEnd_1225742 629394804403448512487921 := by
  unfold tailWord_1225742
  simp only [CollatzResearch.WordTrace]
  refine ⟨5588310440669193614036935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29804322350235699274863653 5588310440669193614036935)
  ·
    refine ⟨8382465661003790421055403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5588310440669193614036935 8382465661003790421055403)
    ·
      refine ⟨12573698491505685631583105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8382465661003790421055403 12573698491505685631583105)
      ·
        refine ⟨9430273868629264223687329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12573698491505685631583105 9430273868629264223687329)
        ·
          refine ⟨7072705401471948167765497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9430273868629264223687329 7072705401471948167765497)
          ·
            refine ⟨5304529051103961125824123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7072705401471948167765497 5304529051103961125824123)
            ·
              refine ⟨7956793576655941688736185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5304529051103961125824123 7956793576655941688736185)
              ·
                refine ⟨5967595182491956266552139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7956793576655941688736185 5967595182491956266552139)
                ·
                  refine ⟨8951392773737934399828209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5967595182491956266552139 8951392773737934399828209)
                  ·
                    refine ⟨6713544580303450799871157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8951392773737934399828209 6713544580303450799871157)
                    ·
                      refine ⟨629394804403448512487921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6713544580303450799871157 629394804403448512487921)
                      ·
                        rfl

theorem cell23_1225742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 2, 1, 2, 5].length) (baseStart_1225742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1225742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1225742 prefixEnd_1225742 := by exact prefixLift 1225742
  have htrace : WordTrace (prefixWord ++ tailWord_1225742) baseStart_1225742 baseEnd_1225742 := by
    simpa [prefixWord, tailWord_1225742, baseEnd_1225742] using wordTrace_append hprefix tailTrace_1225742
  have hstable : (prefixWord ++ tailWord_1225742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1225742).length < 2 ^ (prefixWord ++ tailWord_1225742).sum := by decide
  have hdescent : baseEnd_1225742 < baseStart_1225742 := by decide
  rcases family_descends (prefixWord ++ tailWord_1225742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1225772 : List Nat := [2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 3]
def baseStart_1225772 : Nat := 118140960795 + 1225772 * 2 ^ 59
def prefixEnd_1225772 : Nat := 4983230072969 + 3 ^ 40 * 1225772 * 2
def baseEnd_1225772 : Nat := 629410208823083395112783

theorem tailTrace_1225772 : CollatzResearch.WordTrace tailWord_1225772 prefixEnd_1225772 629410208823083395112783 := by
  unfold tailWord_1225772
  simp only [CollatzResearch.WordTrace]
  refine ⟨22353788857622432017943785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29805051810163242690591713 22353788857622432017943785)
  ·
    refine ⟨16765341643216824013457839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22353788857622432017943785 16765341643216824013457839)
    ·
      refine ⟨25148012464825236020186759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16765341643216824013457839 25148012464825236020186759)
      ·
        refine ⟨37722018697237854030280139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25148012464825236020186759 37722018697237854030280139)
        ·
          refine ⟨56583028045856781045420209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37722018697237854030280139 56583028045856781045420209)
          ·
            refine ⟨42437271034392585784065157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56583028045856781045420209 42437271034392585784065157)
            ·
              refine ⟨7956988318948609834512217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42437271034392585784065157 7956988318948609834512217)
              ·
                refine ⟨5967741239211457375884163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7956988318948609834512217 5967741239211457375884163)
                ·
                  refine ⟨8951611858817186063826245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5967741239211457375884163 8951611858817186063826245)
                  ·
                    refine ⟨1678427223528222386967421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8951611858817186063826245 1678427223528222386967421)
                    ·
                      refine ⟨629410208823083395112783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1678427223528222386967421 629410208823083395112783)
                      ·
                        rfl

theorem cell23_1225772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 3].length) (baseStart_1225772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1225772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1225772 prefixEnd_1225772 := by exact prefixLift 1225772
  have htrace : WordTrace (prefixWord ++ tailWord_1225772) baseStart_1225772 baseEnd_1225772 := by
    simpa [prefixWord, tailWord_1225772, baseEnd_1225772] using wordTrace_append hprefix tailTrace_1225772
  have hstable : (prefixWord ++ tailWord_1225772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1225772).length < 2 ^ (prefixWord ++ tailWord_1225772).sum := by decide
  have hdescent : baseEnd_1225772 < baseStart_1225772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1225772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1225789 : List Nat := [1, 4, 1, 3, 1, 3, 1, 1, 1, 4, 3]
def baseStart_1225789 : Nat := 118140960795 + 1225789 * 2 ^ 59
def prefixEnd_1225789 : Nat := 4983230072969 + 3 ^ 40 * 1225789 * 2
def baseEnd_1225789 : Nat := 629418937994209828600205

theorem tailTrace_1225789 : CollatzResearch.WordTrace tailWord_1225789 prefixEnd_1225789 629418937994209828600205 := by
  unfold tailWord_1225789
  simp only [CollatzResearch.WordTrace]
  refine ⟨44708197756183275939256421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29805465170788850626170947 44708197756183275939256421)
  ·
    refine ⟨8382787079284364238610579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44708197756183275939256421 8382787079284364238610579)
    ·
      refine ⟨12574180618926546357915869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8382787079284364238610579 12574180618926546357915869)
      ·
        refine ⟨4715317732097454884218451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12574180618926546357915869 4715317732097454884218451)
        ·
          refine ⟨7072976598146182326327677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4715317732097454884218451 7072976598146182326327677)
          ·
            refine ⟨2652366224304818372372879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7072976598146182326327677 2652366224304818372372879)
            ·
              refine ⟨3978549336457227558559319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2652366224304818372372879 3978549336457227558559319)
              ·
                refine ⟨5967824004685841337838979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3978549336457227558559319 5967824004685841337838979)
                ·
                  refine ⟨8951736007028762006758469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5967824004685841337838979 8951736007028762006758469)
                  ·
                    refine ⟨1678450501317892876267213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8951736007028762006758469 1678450501317892876267213)
                    ·
                      refine ⟨629418937994209828600205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1678450501317892876267213 629418937994209828600205)
                      ·
                        rfl

theorem cell23_1225789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 1, 1, 4, 3].length) (baseStart_1225789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1225789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1225789 prefixEnd_1225789 := by exact prefixLift 1225789
  have htrace : WordTrace (prefixWord ++ tailWord_1225789) baseStart_1225789 baseEnd_1225789 := by
    simpa [prefixWord, tailWord_1225789, baseEnd_1225789] using wordTrace_append hprefix tailTrace_1225789
  have hstable : (prefixWord ++ tailWord_1225789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1225789).length < 2 ^ (prefixWord ++ tailWord_1225789).sum := by decide
  have hdescent : baseEnd_1225789 < baseStart_1225789 := by decide
  rcases family_descends (prefixWord ++ tailWord_1225789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1225812 : List Nat := [2, 4, 1, 1, 1, 1, 3, 1, 1, 2, 6]
def baseStart_1225812 : Nat := 118140960795 + 1225812 * 2 ^ 59
def prefixEnd_1225812 : Nat := 4983230072969 + 3 ^ 40 * 1225812 * 2
def baseEnd_1225812 : Nat := 629430748049263238612599

theorem tailTrace_1225812 : CollatzResearch.WordTrace tailWord_1225812 prefixEnd_1225812 629430748049263238612599 := by
  unfold tailWord_1225812
  simp only [CollatzResearch.WordTrace]
  refine ⟨22354518317549975433671845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29806024423399967244895793 22354518317549975433671845)
  ·
    refine ⟨4191472184540620393813471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22354518317549975433671845 4191472184540620393813471)
    ·
      refine ⟨6287208276810930590720207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4191472184540620393813471 6287208276810930590720207)
      ·
        refine ⟨9430812415216395886080311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6287208276810930590720207 9430812415216395886080311)
        ·
          refine ⟨14146218622824593829120467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9430812415216395886080311 14146218622824593829120467)
          ·
            refine ⟨21219327934236890743680701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14146218622824593829120467 21219327934236890743680701)
            ·
              refine ⟨7957247975338834028880263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21219327934236890743680701 7957247975338834028880263)
              ·
                refine ⟨11935871963008251043320395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7957247975338834028880263 11935871963008251043320395)
                ·
                  refine ⟨17903807944512376564980593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11935871963008251043320395 17903807944512376564980593)
                  ·
                    refine ⟨13427855958384282423735445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17903807944512376564980593 13427855958384282423735445)
                    ·
                      refine ⟨629430748049263238612599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13427855958384282423735445 629430748049263238612599)
                      ·
                        rfl

theorem cell23_1225812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 1, 1, 2, 6].length) (baseStart_1225812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1225812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1225812 prefixEnd_1225812 := by exact prefixLift 1225812
  have htrace : WordTrace (prefixWord ++ tailWord_1225812) baseStart_1225812 baseEnd_1225812 := by
    simpa [prefixWord, tailWord_1225812, baseEnd_1225812] using wordTrace_append hprefix tailTrace_1225812
  have hstable : (prefixWord ++ tailWord_1225812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1225812).length < 2 ^ (prefixWord ++ tailWord_1225812).sum := by decide
  have hdescent : baseEnd_1225812 < baseStart_1225812 := by decide
  rcases family_descends (prefixWord ++ tailWord_1225812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1225829 : List Nat := [1, 3, 1, 3, 2, 1, 1, 1, 3, 5, 2]
def baseStart_1225829 : Nat := 118140960795 + 1225829 * 2 ^ 59
def prefixEnd_1225829 : Nat := 4983230072969 + 3 ^ 40 * 1225829 * 2
def baseEnd_1225829 : Nat := 629439477220389672100021

theorem tailTrace_1225829 : CollatzResearch.WordTrace tailWord_1225829 prefixEnd_1225829 629439477220389672100021 := by
  unfold tailWord_1225829
  simp only [CollatzResearch.WordTrace]
  refine ⟨44709656676038362770712541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29806437784025575180475027 44709656676038362770712541)
  ·
    refine ⟨16766121253514386039017203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44709656676038362770712541 16766121253514386039017203)
    ·
      refine ⟨25149181880271579058525805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16766121253514386039017203 25149181880271579058525805)
      ·
        refine ⟨9430943205101842146947177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25149181880271579058525805 9430943205101842146947177)
        ·
          refine ⟨7073207403826381610210383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9430943205101842146947177 7073207403826381610210383)
          ·
            refine ⟨10609811105739572415315575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7073207403826381610210383 10609811105739572415315575)
            ·
              refine ⟨15914716658609358622973363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10609811105739572415315575 15914716658609358622973363)
              ·
                refine ⟨23872074987914037934460045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15914716658609358622973363 23872074987914037934460045)
                ·
                  refine ⟨8952028120467764225422517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23872074987914037934460045 8952028120467764225422517)
                  ·
                    refine ⟨839252636293852896133361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8952028120467764225422517 839252636293852896133361)
                    ·
                      refine ⟨629439477220389672100021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 839252636293852896133361 629439477220389672100021)
                      ·
                        rfl

theorem cell23_1225829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 1, 3, 5, 2].length) (baseStart_1225829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1225829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1225829 prefixEnd_1225829 := by exact prefixLift 1225829
  have htrace : WordTrace (prefixWord ++ tailWord_1225829) baseStart_1225829 baseEnd_1225829 := by
    simpa [prefixWord, tailWord_1225829, baseEnd_1225829] using wordTrace_append hprefix tailTrace_1225829
  have hstable : (prefixWord ++ tailWord_1225829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1225829).length < 2 ^ (prefixWord ++ tailWord_1225829).sum := by decide
  have hdescent : baseEnd_1225829 < baseStart_1225829 := by decide
  rcases family_descends (prefixWord ++ tailWord_1225829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1225839 : List Nat := [1, 1, 2, 1, 3, 3, 4, 2, 1, 5]
def baseStart_1225839 : Nat := 118140960795 + 1225839 * 2 ^ 59
def prefixEnd_1225839 : Nat := 4983230072969 + 3 ^ 40 * 1225839 * 2
def baseEnd_1225839 : Nat := 209814870675644877658325

theorem tailTrace_1225839 : CollatzResearch.WordTrace tailWord_1225839 prefixEnd_1225839 209814870675644877658325 := by
  unfold tailWord_1225839
  simp only [CollatzResearch.WordTrace]
  refine ⟨44710021406002134478576571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29806680937334756319051047 44710021406002134478576571)
  ·
    refine ⟨67065032109003201717864857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44710021406002134478576571 67065032109003201717864857)
    ·
      refine ⟨50298774081752401288398643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67065032109003201717864857 50298774081752401288398643)
      ·
        refine ⟨75448161122628601932597965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50298774081752401288398643 75448161122628601932597965)
        ·
          refine ⟨28293060420985725724724237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75448161122628601932597965 28293060420985725724724237)
          ·
            refine ⟨10609897657869647146771589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28293060420985725724724237 10609897657869647146771589)
            ·
              refine ⟨1989355810850558840019673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10609897657869647146771589 1989355810850558840019673)
              ·
                refine ⟨1492016858137919130014755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1989355810850558840019673 1492016858137919130014755)
                ·
                  refine ⟨2238025287206878695022133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1492016858137919130014755 2238025287206878695022133)
                  ·
                    refine ⟨209814870675644877658325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2238025287206878695022133 209814870675644877658325)
                    ·
                      rfl

theorem cell23_1225839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 4, 2, 1, 5].length) (baseStart_1225839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1225839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1225839 prefixEnd_1225839 := by exact prefixLift 1225839
  have htrace : WordTrace (prefixWord ++ tailWord_1225839) baseStart_1225839 baseEnd_1225839 := by
    simpa [prefixWord, tailWord_1225839, baseEnd_1225839] using wordTrace_append hprefix tailTrace_1225839
  have hstable : (prefixWord ++ tailWord_1225839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1225839).length < 2 ^ (prefixWord ++ tailWord_1225839).sum := by decide
  have hdescent : baseEnd_1225839 < baseStart_1225839 := by decide
  rcases family_descends (prefixWord ++ tailWord_1225839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1225846 : List Nat := [5, 1, 1, 2, 1, 1, 1, 3, 1, 5, 2]
def baseStart_1225846 : Nat := 118140960795 + 1225846 * 2 ^ 59
def prefixEnd_1225846 : Nat := 4983230072969 + 3 ^ 40 * 1225846 * 2
def baseEnd_1225846 : Nat := 629448206391516105587443

theorem tailTrace_1225846 : CollatzResearch.WordTrace tailWord_1225846 prefixEnd_1225846 629448206391516105587443 := by
  unfold tailWord_1225846
  simp only [CollatzResearch.WordTrace]
  refine ⟨2794392294811048417130087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 29806851144651183116054261 2794392294811048417130087)
  ·
    refine ⟨4191588442216572625695131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2794392294811048417130087 4191588442216572625695131)
    ·
      refine ⟨6287382663324858938542697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4191588442216572625695131 6287382663324858938542697)
      ·
        refine ⟨4715536997493644203907023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6287382663324858938542697 4715536997493644203907023)
        ·
          refine ⟨7073305496240466305860535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4715536997493644203907023 7073305496240466305860535)
          ·
            refine ⟨10609958244360699458790803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7073305496240466305860535 10609958244360699458790803)
            ·
              refine ⟨15914937366541049188186205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10609958244360699458790803 15914937366541049188186205)
              ·
                refine ⟨5968101512452893445569827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15914937366541049188186205 5968101512452893445569827)
                ·
                  refine ⟨8952152268679340168354741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5968101512452893445569827 8952152268679340168354741)
                  ·
                    refine ⟨839264275188688140783257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8952152268679340168354741 839264275188688140783257)
                    ·
                      refine ⟨629448206391516105587443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 839264275188688140783257 629448206391516105587443)
                      ·
                        rfl

theorem cell23_1225846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 3, 1, 5, 2].length) (baseStart_1225846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1225846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1225846 prefixEnd_1225846 := by exact prefixLift 1225846
  have htrace : WordTrace (prefixWord ++ tailWord_1225846) baseStart_1225846 baseEnd_1225846 := by
    simpa [prefixWord, tailWord_1225846, baseEnd_1225846] using wordTrace_append hprefix tailTrace_1225846
  have hstable : (prefixWord ++ tailWord_1225846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1225846).length < 2 ^ (prefixWord ++ tailWord_1225846).sum := by decide
  have hdescent : baseEnd_1225846 < baseStart_1225846 := by decide
  rcases family_descends (prefixWord ++ tailWord_1225846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1225852 : List Nat := [2, 2, 2, 1, 1, 3, 2, 1, 3, 6]
def baseStart_1225852 : Nat := 118140960795 + 1225852 * 2 ^ 59
def prefixEnd_1225852 : Nat := 4983230072969 + 3 ^ 40 * 1225852 * 2
def baseEnd_1225852 : Nat := 209817095758481027370805

theorem tailTrace_1225852 : CollatzResearch.WordTrace tailWord_1225852 prefixEnd_1225852 209817095758481027370805 := by
  unfold tailWord_1225852
  simp only [CollatzResearch.WordTrace]
  refine ⟨22355247777477518849399905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29806997036636691799199873 22355247777477518849399905)
  ·
    refine ⟨16766435833108139137049929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22355247777477518849399905 16766435833108139137049929)
    ·
      refine ⟨12574826874831104352787447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16766435833108139137049929 12574826874831104352787447)
      ·
        refine ⟨18862240312246656529181171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12574826874831104352787447 18862240312246656529181171)
        ·
          refine ⟨28293360468369984793771757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18862240312246656529181171 28293360468369984793771757)
          ·
            refine ⟨10610010175638744297664409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28293360468369984793771757 10610010175638744297664409)
            ·
              refine ⟨7957507631729058223248307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10610010175638744297664409 7957507631729058223248307)
              ·
                refine ⟨11936261447593587334872461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7957507631729058223248307 11936261447593587334872461)
                ·
                  refine ⟨4476098042847595250577173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11936261447593587334872461 4476098042847595250577173)
                  ·
                    refine ⟨209817095758481027370805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4476098042847595250577173 209817095758481027370805)
                    ·
                      rfl

theorem cell23_1225852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 1, 3, 6].length) (baseStart_1225852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1225852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1225852 prefixEnd_1225852 := by exact prefixLift 1225852
  have htrace : WordTrace (prefixWord ++ tailWord_1225852) baseStart_1225852 baseEnd_1225852 := by
    simpa [prefixWord, tailWord_1225852, baseEnd_1225852] using wordTrace_append hprefix tailTrace_1225852
  have hstable : (prefixWord ++ tailWord_1225852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1225852).length < 2 ^ (prefixWord ++ tailWord_1225852).sum := by decide
  have hdescent : baseEnd_1225852 < baseStart_1225852 := by decide
  rcases family_descends (prefixWord ++ tailWord_1225852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1225859 : List Nat := [1, 1, 1, 3, 3, 2, 1, 5, 1, 1, 4]
def baseStart_1225859 : Nat := 118140960795 + 1225859 * 2 ^ 59
def prefixEnd_1225859 : Nat := 4983230072969 + 3 ^ 40 * 1225859 * 2
def baseEnd_1225859 : Nat := 629454881640024554724883

theorem tailTrace_1225859 : CollatzResearch.WordTrace tailWord_1225859 prefixEnd_1225859 629454881640024554724883 := by
  unfold tailWord_1225859
  simp only [CollatzResearch.WordTrace]
  refine ⟨44710750865929677894304631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29807167243953118596203087 44710750865929677894304631)
  ·
    refine ⟨67066126298894516841456947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44710750865929677894304631 67066126298894516841456947)
    ·
      refine ⟨100599189448341775262185421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67066126298894516841456947 100599189448341775262185421)
      ·
        refine ⟨37724696043128165723319533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100599189448341775262185421 37724696043128165723319533)
        ·
          refine ⟨14146761016173062146244825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37724696043128165723319533 14146761016173062146244825)
          ·
            refine ⟨10610070762129796609683619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14146761016173062146244825 10610070762129796609683619)
            ·
              refine ⟨15915106143194694914525429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10610070762129796609683619 15915106143194694914525429)
              ·
                refine ⟨1492041200924502648236759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15915106143194694914525429 1492041200924502648236759)
                ·
                  refine ⟨2238061801386753972355139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1492041200924502648236759 2238061801386753972355139)
                  ·
                    refine ⟨3357092702080130958532709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2238061801386753972355139 3357092702080130958532709)
                    ·
                      refine ⟨629454881640024554724883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3357092702080130958532709 629454881640024554724883)
                      ·
                        rfl

theorem cell23_1225859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 5, 1, 1, 4].length) (baseStart_1225859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1225859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1225859 prefixEnd_1225859 := by exact prefixLift 1225859
  have htrace : WordTrace (prefixWord ++ tailWord_1225859) baseStart_1225859 baseEnd_1225859 := by
    simpa [prefixWord, tailWord_1225859, baseEnd_1225859] using wordTrace_append hprefix tailTrace_1225859
  have hstable : (prefixWord ++ tailWord_1225859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1225859).length < 2 ^ (prefixWord ++ tailWord_1225859).sum := by decide
  have hdescent : baseEnd_1225859 < baseStart_1225859 := by decide
  rcases family_descends (prefixWord ++ tailWord_1225859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1225872 : List Nat := [2, 1, 1, 1, 1, 1, 4, 1, 5, 2, 4]
def baseStart_1225872 : Nat := 118140960795 + 1225872 * 2 ^ 59
def prefixEnd_1225872 : Nat := 4983230072969 + 3 ^ 40 * 1225872 * 2
def baseEnd_1225872 : Nat := 629461556888533003862323

theorem tailTrace_1225872 : CollatzResearch.WordTrace tailWord_1225872 prefixEnd_1225872 629461556888533003862323 := by
  unfold tailWord_1225872
  simp only [CollatzResearch.WordTrace]
  refine ⟨22355612507441290557263935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29807483343255054076351913 22355612507441290557263935)
  ·
    refine ⟨33533418761161935835895903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22355612507441290557263935 33533418761161935835895903)
    ·
      refine ⟨50300128141742903753843855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33533418761161935835895903 50300128141742903753843855)
      ·
        refine ⟨75450192212614355630765783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50300128141742903753843855 75450192212614355630765783)
        ·
          refine ⟨113175288318921533446148675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75450192212614355630765783 113175288318921533446148675)
          ·
            refine ⟨169762932478382300169223013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113175288318921533446148675 169762932478382300169223013)
            ·
              refine ⟨31830549839696681281729315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 169762932478382300169223013 31830549839696681281729315)
              ·
                refine ⟨47745824759545021922593973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31830549839696681281729315 47745824759545021922593973)
                ·
                  refine ⟨4476171071207345805243185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47745824759545021922593973 4476171071207345805243185)
                  ·
                    refine ⟨3357128303405509353932389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4476171071207345805243185 3357128303405509353932389)
                    ·
                      refine ⟨629461556888533003862323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3357128303405509353932389 629461556888533003862323)
                      ·
                        rfl

theorem cell23_1225872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 5, 2, 4].length) (baseStart_1225872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1225872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1225872 prefixEnd_1225872 := by exact prefixLift 1225872
  have htrace : WordTrace (prefixWord ++ tailWord_1225872) baseStart_1225872 baseEnd_1225872 := by
    simpa [prefixWord, tailWord_1225872, baseEnd_1225872] using wordTrace_append hprefix tailTrace_1225872
  have hstable : (prefixWord ++ tailWord_1225872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1225872).length < 2 ^ (prefixWord ++ tailWord_1225872).sum := by decide
  have hdescent : baseEnd_1225872 < baseStart_1225872 := by decide
  rcases family_descends (prefixWord ++ tailWord_1225872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1225879 : List Nat := [1, 1, 3, 3, 3, 1, 2, 2, 1, 1, 5]
def baseStart_1225879 : Nat := 118140960795 + 1225879 * 2 ^ 59
def prefixEnd_1225879 : Nat := 4983230072969 + 3 ^ 40 * 1225879 * 2
def baseEnd_1225879 : Nat := 629465151253114476474791

theorem tailTrace_1225879 : CollatzResearch.WordTrace tailWord_1225879 prefixEnd_1225879 629465151253114476474791 := by
  unfold tailWord_1225879
  simp only [CollatzResearch.WordTrace]
  refine ⟨44711480325857221310032691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29807653550571480873355127 44711480325857221310032691)
  ·
    refine ⟨67067220488785831965049037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44711480325857221310032691 67067220488785831965049037)
    ·
      refine ⟨25150207683294686986893389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67067220488785831965049037 25150207683294686986893389)
      ·
        refine ⟨9431327881235507620085021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25150207683294686986893389 9431327881235507620085021)
        ·
          refine ⟨3536747955463315357531883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9431327881235507620085021 3536747955463315357531883)
          ·
            refine ⟨5305121933194973036297825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3536747955463315357531883 5305121933194973036297825)
            ·
              refine ⟨3978841449896229777223369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5305121933194973036297825 3978841449896229777223369)
              ·
                refine ⟨2984131087422172332917527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3978841449896229777223369 2984131087422172332917527)
                ·
                  refine ⟨4476196631133258499376291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2984131087422172332917527 4476196631133258499376291)
                  ·
                    refine ⟨6714294946699887749064437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4476196631133258499376291 6714294946699887749064437)
                    ·
                      refine ⟨629465151253114476474791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6714294946699887749064437 629465151253114476474791)
                      ·
                        rfl

theorem cell23_1225879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 2, 1, 1, 5].length) (baseStart_1225879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1225879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1225879 prefixEnd_1225879 := by exact prefixLift 1225879
  have htrace : WordTrace (prefixWord ++ tailWord_1225879) baseStart_1225879 baseEnd_1225879 := by
    simpa [prefixWord, tailWord_1225879, baseEnd_1225879] using wordTrace_append hprefix tailTrace_1225879
  have hstable : (prefixWord ++ tailWord_1225879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1225879).length < 2 ^ (prefixWord ++ tailWord_1225879).sum := by decide
  have hdescent : baseEnd_1225879 < baseStart_1225879 := by decide
  rcases family_descends (prefixWord ++ tailWord_1225879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1225889 : List Nat := [1, 2, 3, 3, 1, 1, 2, 3, 1, 2, 4]
def baseStart_1225889 : Nat := 118140960795 + 1225889 * 2 ^ 59
def prefixEnd_1225889 : Nat := 4983230072969 + 3 ^ 40 * 1225889 * 2
def baseEnd_1225889 : Nat := 629470286059659437349745

theorem tailTrace_1225889 : CollatzResearch.WordTrace tailWord_1225889 prefixEnd_1225889 629470286059659437349745 := by
  unfold tailWord_1225889
  simp only [CollatzResearch.WordTrace]
  refine ⟨44711845055820993017896721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29807896703880662011931147 44711845055820993017896721)
  ·
    refine ⟨33533883791865744763422541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44711845055820993017896721 33533883791865744763422541)
    ·
      refine ⟨12575206421949654286283453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33533883791865744763422541 12575206421949654286283453)
      ·
        refine ⟨4715702408231120357356295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12575206421949654286283453 4715702408231120357356295)
        ·
          refine ⟨7073553612346680536034443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4715702408231120357356295 7073553612346680536034443)
          ·
            refine ⟨10610330418520020804051665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7073553612346680536034443 10610330418520020804051665)
            ·
              refine ⟨7957747813890015603038749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10610330418520020804051665 7957747813890015603038749)
              ·
                refine ⟨2984155430208755851139531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7957747813890015603038749 2984155430208755851139531)
                ·
                  refine ⟨4476233145313133776709297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2984155430208755851139531 4476233145313133776709297)
                  ·
                    refine ⟨3357174858984850332531973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4476233145313133776709297 3357174858984850332531973)
                    ·
                      refine ⟨629470286059659437349745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3357174858984850332531973 629470286059659437349745)
                      ·
                        rfl

theorem cell23_1225889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_1225889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1225889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1225889 prefixEnd_1225889 := by exact prefixLift 1225889
  have htrace : WordTrace (prefixWord ++ tailWord_1225889) baseStart_1225889 baseEnd_1225889 := by
    simpa [prefixWord, tailWord_1225889, baseEnd_1225889] using wordTrace_append hprefix tailTrace_1225889
  have hstable : (prefixWord ++ tailWord_1225889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1225889).length < 2 ^ (prefixWord ++ tailWord_1225889).sum := by decide
  have hdescent : baseEnd_1225889 < baseStart_1225889 := by decide
  rcases family_descends (prefixWord ++ tailWord_1225889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1225890 : List Nat := [3, 3, 1, 3, 3, 1, 1, 2, 1, 5]
def baseStart_1225890 : Nat := 118140960795 + 1225890 * 2 ^ 59
def prefixEnd_1225890 : Nat := 4983230072969 + 3 ^ 40 * 1225890 * 2
def baseEnd_1225890 : Nat := 209823599846771311145747

theorem tailTrace_1225890 : CollatzResearch.WordTrace tailWord_1225890 prefixEnd_1225890 209823599846771311145747 := by
  unfold tailWord_1225890
  simp only [CollatzResearch.WordTrace]
  refine ⟨11177970382204342547170781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29807921019211580125788749 11177970382204342547170781)
  ·
    refine ⟨4191738893326628455189043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11177970382204342547170781 4191738893326628455189043)
    ·
      refine ⟨6287608339989942682783565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4191738893326628455189043 6287608339989942682783565)
      ·
        refine ⟨2357853127496228506043837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6287608339989942682783565 2357853127496228506043837)
        ·
          refine ⟨884194922811085689766439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2357853127496228506043837 884194922811085689766439)
          ·
            refine ⟨1326292384216628534649659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 884194922811085689766439 1326292384216628534649659)
            ·
              refine ⟨1989438576324942801974489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1326292384216628534649659 1989438576324942801974489)
              ·
                refine ⟨1492078932243707101480867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1989438576324942801974489 1492078932243707101480867)
                ·
                  refine ⟨2238118398365560652221301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1492078932243707101480867 2238118398365560652221301)
                  ·
                    refine ⟨209823599846771311145747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2238118398365560652221301 209823599846771311145747)
                    ·
                      rfl

theorem cell23_1225890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 1, 2, 1, 5].length) (baseStart_1225890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1225890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1225890 prefixEnd_1225890 := by exact prefixLift 1225890
  have htrace : WordTrace (prefixWord ++ tailWord_1225890) baseStart_1225890 baseEnd_1225890 := by
    simpa [prefixWord, tailWord_1225890, baseEnd_1225890] using wordTrace_append hprefix tailTrace_1225890
  have hstable : (prefixWord ++ tailWord_1225890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1225890).length < 2 ^ (prefixWord ++ tailWord_1225890).sum := by decide
  have hdescent : baseEnd_1225890 < baseStart_1225890 := by decide
  rcases family_descends (prefixWord ++ tailWord_1225890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1225913 : List Nat := [1, 2, 1, 4, 1, 4, 3, 1, 1, 2, 3]
def baseStart_1225913 : Nat := 118140960795 + 1225913 * 2 ^ 59
def prefixEnd_1225913 : Nat := 4983230072969 + 3 ^ 40 * 1225913 * 2
def baseEnd_1225913 : Nat := 629482609595367343449635

theorem tailTrace_1225913 : CollatzResearch.WordTrace tailWord_1225913 prefixEnd_1225913 629482609595367343449635 := by
  unfold tailWord_1225913
  simp only [CollatzResearch.WordTrace]
  refine ⟨44712720407734045116770393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29808480271822696744513595 44712720407734045116770393)
  ·
    refine ⟨33534540305800533837577795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44712720407734045116770393 33534540305800533837577795)
    ·
      refine ⟨50301810458700800756366693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33534540305800533837577795 50301810458700800756366693)
      ·
        refine ⟨9431589461006400141818755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50301810458700800756366693 9431589461006400141818755)
        ·
          refine ⟨14147384191509600212728133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9431589461006400141818755 14147384191509600212728133)
          ·
            refine ⟨2652634535908050039886525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14147384191509600212728133 2652634535908050039886525)
            ·
              refine ⟨994737950965518764957447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2652634535908050039886525 994737950965518764957447)
              ·
                refine ⟨1492106926448278147436171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 994737950965518764957447 1492106926448278147436171)
                ·
                  refine ⟨2238160389672417221154257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1492106926448278147436171 2238160389672417221154257)
                  ·
                    refine ⟨1678620292254312915865693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2238160389672417221154257 1678620292254312915865693)
                    ·
                      refine ⟨629482609595367343449635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1678620292254312915865693 629482609595367343449635)
                      ·
                        rfl

theorem cell23_1225913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 3, 1, 1, 2, 3].length) (baseStart_1225913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1225913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1225913 prefixEnd_1225913 := by exact prefixLift 1225913
  have htrace : WordTrace (prefixWord ++ tailWord_1225913) baseStart_1225913 baseEnd_1225913 := by
    simpa [prefixWord, tailWord_1225913, baseEnd_1225913] using wordTrace_append hprefix tailTrace_1225913
  have hstable : (prefixWord ++ tailWord_1225913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1225913).length < 2 ^ (prefixWord ++ tailWord_1225913).sum := by decide
  have hdescent : baseEnd_1225913 < baseStart_1225913 := by decide
  rcases family_descends (prefixWord ++ tailWord_1225913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1225970 : List Nat := [3, 2, 1, 3, 3, 1, 1, 3, 1, 3, 2]
def baseStart_1225970 : Nat := 118140960795 + 1225970 * 2 ^ 59
def prefixEnd_1225970 : Nat := 4983230072969 + 3 ^ 40 * 1225970 * 2
def baseEnd_1225970 : Nat := 629511877992673620436873

theorem tailTrace_1225970 : CollatzResearch.WordTrace tailWord_1225970 prefixEnd_1225970 629511877992673620436873 := by
  unfold tailWord_1225970
  simp only [CollatzResearch.WordTrace]
  refine ⟨11178699842131885962898841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29809866245685029234396909 11178699842131885962898841)
  ·
    refine ⟨8384024881598914472174131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11178699842131885962898841 8384024881598914472174131)
    ·
      refine ⟨12576037322398371708261197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8384024881598914472174131 12576037322398371708261197)
      ·
        refine ⟨4716013995899389390597949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12576037322398371708261197 4716013995899389390597949)
        ·
          refine ⟨1768505248462271021474231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4716013995899389390597949 1768505248462271021474231)
          ·
            refine ⟨2652757872693406532211347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1768505248462271021474231 2652757872693406532211347)
            ·
              refine ⟨3979136809040109798317021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2652757872693406532211347 3979136809040109798317021)
              ·
                refine ⟨1492176303390041174368883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3979136809040109798317021 1492176303390041174368883)
                ·
                  refine ⟨2238264455085061761553325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1492176303390041174368883 2238264455085061761553325)
                  ·
                    refine ⟨839349170656898160582497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2238264455085061761553325 839349170656898160582497)
                    ·
                      refine ⟨629511877992673620436873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 839349170656898160582497 629511877992673620436873)
                      ·
                        rfl

theorem cell23_1225970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 3, 1, 3, 2].length) (baseStart_1225970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1225970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1225970 prefixEnd_1225970 := by exact prefixLift 1225970
  have htrace : WordTrace (prefixWord ++ tailWord_1225970) baseStart_1225970 baseEnd_1225970 := by
    simpa [prefixWord, tailWord_1225970, baseEnd_1225970] using wordTrace_append hprefix tailTrace_1225970
  have hstable : (prefixWord ++ tailWord_1225970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1225970).length < 2 ^ (prefixWord ++ tailWord_1225970).sum := by decide
  have hdescent : baseEnd_1225970 < baseStart_1225970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1225970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1225983 : List Nat := [1, 1, 2, 2, 1, 6, 1, 1, 4, 2, 2]
def baseStart_1225983 : Nat := 118140960795 + 1225983 * 2 ^ 59
def prefixEnd_1225983 : Nat := 4983230072969 + 3 ^ 40 * 1225983 * 2
def baseEnd_1225983 : Nat := 629518553241182069574313

theorem tailTrace_1225983 : CollatzResearch.WordTrace tailWord_1225983 prefixEnd_1225983 629518553241182069574313 := by
  unfold tailWord_1225983
  simp only [CollatzResearch.WordTrace]
  refine ⟨44715273517480447071818603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29810182344986964714545735 44715273517480447071818603)
  ·
    refine ⟨67072910276220670607727905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44715273517480447071818603 67072910276220670607727905)
    ·
      refine ⟨50304682707165502955795929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67072910276220670607727905 50304682707165502955795929)
      ·
        refine ⟨37728512030374127216846947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50304682707165502955795929 37728512030374127216846947)
        ·
          refine ⟨56592768045561190825270421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37728512030374127216846947 56592768045561190825270421)
          ·
            refine ⟨2652786002135680819934551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 56592768045561190825270421 2652786002135680819934551)
            ·
              refine ⟨3979179003203521229901827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2652786002135680819934551 3979179003203521229901827)
              ·
                refine ⟨5968768504805281844852741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3979179003203521229901827 5968768504805281844852741)
                ·
                  refine ⟨1119144094650990345909889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5968768504805281844852741 1119144094650990345909889)
                  ·
                    refine ⟨839358070988242759432417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1119144094650990345909889 839358070988242759432417)
                    ·
                      refine ⟨629518553241182069574313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 839358070988242759432417 629518553241182069574313)
                      ·
                        rfl

theorem cell23_1225983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 1, 4, 2, 2].length) (baseStart_1225983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1225983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1225983 prefixEnd_1225983 := by exact prefixLift 1225983
  have htrace : WordTrace (prefixWord ++ tailWord_1225983) baseStart_1225983 baseEnd_1225983 := by
    simpa [prefixWord, tailWord_1225983, baseEnd_1225983] using wordTrace_append hprefix tailTrace_1225983
  have hstable : (prefixWord ++ tailWord_1225983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1225983).length < 2 ^ (prefixWord ++ tailWord_1225983).sum := by decide
  have hdescent : baseEnd_1225983 < baseStart_1225983 := by decide
  rcases family_descends (prefixWord ++ tailWord_1225983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1225989 : List Nat := [1, 3, 1, 1, 2, 1, 6, 1, 7]
def baseStart_1225989 : Nat := 118140960795 + 1225989 * 2 ^ 59
def prefixEnd_1225989 : Nat := 4983230072969 + 3 ^ 40 * 1225989 * 2
def baseEnd_1225989 : Nat := 69946848236123227344365

theorem tailTrace_1225989 : CollatzResearch.WordTrace tailWord_1225989 prefixEnd_1225989 69946848236123227344365 := by
  unfold tailWord_1225989
  simp only [CollatzResearch.WordTrace]
  refine ⟨44715492355458710096537021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29810328236972473397691347 44715492355458710096537021)
  ·
    refine ⟨16768309633297016286201383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44715492355458710096537021 16768309633297016286201383)
    ·
      refine ⟨25152464449945524429302075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16768309633297016286201383 25152464449945524429302075)
      ·
        refine ⟨37728696674918286643953113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25152464449945524429302075 37728696674918286643953113)
        ·
          refine ⟨28296522506188714982964835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37728696674918286643953113 28296522506188714982964835)
          ·
            refine ⟨42444783759283072474447253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28296522506188714982964835 42444783759283072474447253)
            ·
              refine ⟨1989599238716394022239715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 42444783759283072474447253 1989599238716394022239715)
              ·
                refine ⟨2984398858074591033359573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1989599238716394022239715 2984398858074591033359573)
                ·
                  refine ⟨69946848236123227344365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2984398858074591033359573 69946848236123227344365)
                  ·
                    rfl

theorem cell23_1225989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 6, 1, 7].length) (baseStart_1225989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1225989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1225989 prefixEnd_1225989 := by exact prefixLift 1225989
  have htrace : WordTrace (prefixWord ++ tailWord_1225989) baseStart_1225989 baseEnd_1225989 := by
    simpa [prefixWord, tailWord_1225989, baseEnd_1225989] using wordTrace_append hprefix tailTrace_1225989
  have hstable : (prefixWord ++ tailWord_1225989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1225989).length < 2 ^ (prefixWord ++ tailWord_1225989).sum := by decide
  have hdescent : baseEnd_1225989 < baseStart_1225989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1225989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1226019 : List Nat := [1, 1, 1, 4, 2, 3, 2, 1, 1, 7]
def baseStart_1226019 : Nat := 118140960795 + 1226019 * 2 ^ 59
def prefixEnd_1226019 : Nat := 4983230072969 + 3 ^ 40 * 1226019 * 2
def baseEnd_1226019 : Nat := 209845679514914642908049

theorem tailTrace_1226019 : CollatzResearch.WordTrace tailWord_1226019 prefixEnd_1226019 209845679514914642908049 := by
  unfold tailWord_1226019
  simp only [CollatzResearch.WordTrace]
  refine ⟨44716586545350025220129111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29811057696900016813419407 44716586545350025220129111)
  ·
    refine ⟨67074879818025037830193667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44716586545350025220129111 67074879818025037830193667)
    ·
      refine ⟨100612319727037556745290501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67074879818025037830193667 100612319727037556745290501)
      ·
        refine ⟨18864809948819541889741969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 100612319727037556745290501 18864809948819541889741969)
        ·
          refine ⟨14148607461614656417306477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18864809948819541889741969 14148607461614656417306477)
          ·
            refine ⟨5305727798105496156489929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14148607461614656417306477 5305727798105496156489929)
            ·
              refine ⟨3979295848579122117367447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5305727798105496156489929 3979295848579122117367447)
              ·
                refine ⟨5968943772868683176051171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3979295848579122117367447 5968943772868683176051171)
                ·
                  refine ⟨8953415659303024764076757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5968943772868683176051171 8953415659303024764076757)
                  ·
                    refine ⟨209845679514914642908049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8953415659303024764076757 209845679514914642908049)
                    ·
                      rfl

theorem cell23_1226019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 1, 1, 7].length) (baseStart_1226019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1226019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1226019 prefixEnd_1226019 := by exact prefixLift 1226019
  have htrace : WordTrace (prefixWord ++ tailWord_1226019) baseStart_1226019 baseEnd_1226019 := by
    simpa [prefixWord, tailWord_1226019, baseEnd_1226019] using wordTrace_append hprefix tailTrace_1226019
  have hstable : (prefixWord ++ tailWord_1226019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1226019).length < 2 ^ (prefixWord ++ tailWord_1226019).sum := by decide
  have hdescent : baseEnd_1226019 < baseStart_1226019 := by decide
  rcases family_descends (prefixWord ++ tailWord_1226019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1226046 : List Nat := [4, 2, 1, 2, 1, 1, 3, 1, 1, 2, 5]
def baseStart_1226046 : Nat := 118140960795 + 1226046 * 2 ^ 59
def prefixEnd_1226046 : Nat := 4983230072969 + 3 ^ 40 * 1226046 * 2
def baseEnd_1226046 : Nat := 629550902522415323086523

theorem tailTrace_1226046 : CollatzResearch.WordTrace tailWord_1226046 prefixEnd_1226046 629550902522415323086523 := by
  unfold tailWord_1226046
  simp only [CollatzResearch.WordTrace]
  refine ⟨5589696414531526103920249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29811714210834805887574661 5589696414531526103920249)
  ·
    refine ⟨4192272310898644577940187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5589696414531526103920249 4192272310898644577940187)
    ·
      refine ⟨6288408466347966866910281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4192272310898644577940187 6288408466347966866910281)
      ·
        refine ⟨4716306349760975150182711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6288408466347966866910281 4716306349760975150182711)
        ·
          refine ⟨7074459524641462725274067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4716306349760975150182711 7074459524641462725274067)
          ·
            refine ⟨10611689286962194087911101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7074459524641462725274067 10611689286962194087911101)
            ·
              refine ⟨3979383482610822782966663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10611689286962194087911101 3979383482610822782966663)
              ·
                refine ⟨5969075223916234174449995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3979383482610822782966663 5969075223916234174449995)
                ·
                  refine ⟨8953612835874351261674993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5969075223916234174449995 8953612835874351261674993)
                  ·
                    refine ⟨6715209626905763446256245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8953612835874351261674993 6715209626905763446256245)
                    ·
                      refine ⟨629550902522415323086523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6715209626905763446256245 629550902522415323086523)
                      ·
                        rfl

theorem cell23_1226046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_1226046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1226046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1226046 prefixEnd_1226046 := by exact prefixLift 1226046
  have htrace : WordTrace (prefixWord ++ tailWord_1226046) baseStart_1226046 baseEnd_1226046 := by
    simpa [prefixWord, tailWord_1226046, baseEnd_1226046] using wordTrace_append hprefix tailTrace_1226046
  have hstable : (prefixWord ++ tailWord_1226046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1226046).length < 2 ^ (prefixWord ++ tailWord_1226046).sum := by decide
  have hdescent : baseEnd_1226046 < baseStart_1226046 := by decide
  rcases family_descends (prefixWord ++ tailWord_1226046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1226056 : List Nat := [2, 1, 3, 1, 1, 2, 1, 3, 1, 6, 2]
def baseStart_1226056 : Nat := 118140960795 + 1226056 * 2 ^ 59
def prefixEnd_1226056 : Nat := 4983230072969 + 3 ^ 40 * 1226056 * 2
def baseEnd_1226056 : Nat := 629556037328960283961477

theorem tailTrace_1226056 : CollatzResearch.WordTrace tailWord_1226056 prefixEnd_1226056 629556037328960283961477 := by
  unfold tailWord_1226056
  simp only [CollatzResearch.WordTrace]
  refine ⟨22358968023107990269613011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29811957364143987026150681 22358968023107990269613011)
  ·
    refine ⟨33538452034661985404419517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22358968023107990269613011 33538452034661985404419517)
    ·
      refine ⟨12576919512998244526657319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33538452034661985404419517 12576919512998244526657319)
      ·
        refine ⟨18865379269497366789985979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12576919512998244526657319 18865379269497366789985979)
        ·
          refine ⟨28298068904246050184978969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18865379269497366789985979 28298068904246050184978969)
          ·
            refine ⟨21223551678184537638734227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28298068904246050184978969 21223551678184537638734227)
            ·
              refine ⟨31835327517276806458101341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21223551678184537638734227 31835327517276806458101341)
              ·
                refine ⟨11938247818978802421788003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31835327517276806458101341 11938247818978802421788003)
                ·
                  refine ⟨17907371728468203632682005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11938247818978802421788003 17907371728468203632682005)
                  ·
                    refine ⟨839408049771947045281969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17907371728468203632682005 839408049771947045281969)
                    ·
                      refine ⟨629556037328960283961477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 839408049771947045281969 629556037328960283961477)
                      ·
                        rfl

theorem cell23_1226056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 3, 1, 6, 2].length) (baseStart_1226056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1226056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1226056 prefixEnd_1226056 := by exact prefixLift 1226056
  have htrace : WordTrace (prefixWord ++ tailWord_1226056) baseStart_1226056 baseEnd_1226056 := by
    simpa [prefixWord, tailWord_1226056, baseEnd_1226056] using wordTrace_append hprefix tailTrace_1226056
  have hstable : (prefixWord ++ tailWord_1226056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1226056).length < 2 ^ (prefixWord ++ tailWord_1226056).sum := by decide
  have hdescent : baseEnd_1226056 < baseStart_1226056 := by decide
  rcases family_descends (prefixWord ++ tailWord_1226056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1226066 : List Nat := [3, 2, 2, 1, 1, 1, 1, 3, 5, 4]
def baseStart_1226066 : Nat := 118140960795 + 1226066 * 2 ^ 59
def prefixEnd_1226066 : Nat := 4983230072969 + 3 ^ 40 * 1226066 * 2
def baseEnd_1226066 : Nat := 209853724045168414945477

theorem tailTrace_1226066 : CollatzResearch.WordTrace tailWord_1226066 prefixEnd_1226066 209853724045168414945477 := by
  unfold tailWord_1226066
  simp only [CollatzResearch.WordTrace]
  refine ⟨11179575194044938061772513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29812200517453168164726701 11179575194044938061772513)
  ·
    refine ⟨8384681395533703546329385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11179575194044938061772513 8384681395533703546329385)
    ·
      refine ⟨6288511046650277659747039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8384681395533703546329385 6288511046650277659747039)
      ·
        refine ⟨9432766569975416489620559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6288511046650277659747039 9432766569975416489620559)
        ·
          refine ⟨14149149854963124734430839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9432766569975416489620559 14149149854963124734430839)
          ·
            refine ⟨21223724782444687101646259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14149149854963124734430839 21223724782444687101646259)
            ·
              refine ⟨31835587173667030652469389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21223724782444687101646259 31835587173667030652469389)
              ·
                refine ⟨11938345190125136494676021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31835587173667030652469389 11938345190125136494676021)
                ·
                  refine ⟨1119219861574231546375877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11938345190125136494676021 1119219861574231546375877)
                  ·
                    refine ⟨209853724045168414945477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1119219861574231546375877 209853724045168414945477)
                    ·
                      rfl

theorem cell23_1226066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 3, 5, 4].length) (baseStart_1226066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1226066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1226066 prefixEnd_1226066 := by exact prefixLift 1226066
  have htrace : WordTrace (prefixWord ++ tailWord_1226066) baseStart_1226066 baseEnd_1226066 := by
    simpa [prefixWord, tailWord_1226066, baseEnd_1226066] using wordTrace_append hprefix tailTrace_1226066
  have hstable : (prefixWord ++ tailWord_1226066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1226066).length < 2 ^ (prefixWord ++ tailWord_1226066).sum := by decide
  have hdescent : baseEnd_1226066 < baseStart_1226066 := by decide
  rcases family_descends (prefixWord ++ tailWord_1226066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1226093 : List Nat := [1, 5, 1, 1, 1, 3, 2, 2, 2, 2, 3]
def baseStart_1226093 : Nat := 118140960795 + 1226093 * 2 ^ 59
def prefixEnd_1226093 : Nat := 4983230072969 + 3 ^ 40 * 1226093 * 2
def baseEnd_1226093 : Nat := 629575036113176639198807

theorem tailTrace_1226093 : CollatzResearch.WordTrace tailWord_1226093 prefixEnd_1226093 629575036113176639198807 := by
  unfold tailWord_1226093
  simp only [CollatzResearch.WordTrace]
  refine ⟨44719285547081935858322933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29812857031387957238881955 44719285547081935858322933)
  ·
    refine ⟨4192433020038931486717775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 44719285547081935858322933 4192433020038931486717775)
    ·
      refine ⟨6288649530058397230076663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4192433020038931486717775 6288649530058397230076663)
      ·
        refine ⟨9432974295087595845114995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6288649530058397230076663 9432974295087595845114995)
        ·
          refine ⟨14149461442631393767672493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9432974295087595845114995 14149461442631393767672493)
          ·
            refine ⟨5306048040986772662877185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14149461442631393767672493 5306048040986772662877185)
            ·
              refine ⟨3979536030740079497157889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5306048040986772662877185 3979536030740079497157889)
              ·
                refine ⟨2984652023055059622868417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3979536030740079497157889 2984652023055059622868417)
                ·
                  refine ⟨2238489017291294717151313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2984652023055059622868417 2238489017291294717151313)
                  ·
                    refine ⟨1678866762968471037863485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2238489017291294717151313 1678866762968471037863485)
                    ·
                      refine ⟨629575036113176639198807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1678866762968471037863485 629575036113176639198807)
                      ·
                        rfl

theorem cell23_1226093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 2, 2, 2, 3].length) (baseStart_1226093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1226093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1226093 prefixEnd_1226093 := by exact prefixLift 1226093
  have htrace : WordTrace (prefixWord ++ tailWord_1226093) baseStart_1226093 baseEnd_1226093 := by
    simpa [prefixWord, tailWord_1226093, baseEnd_1226093] using wordTrace_append hprefix tailTrace_1226093
  have hstable : (prefixWord ++ tailWord_1226093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1226093).length < 2 ^ (prefixWord ++ tailWord_1226093).sum := by decide
  have hdescent : baseEnd_1226093 < baseStart_1226093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1226093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1226096 : List Nat := [2, 1, 1, 1, 4, 2, 4, 2, 6]
def baseStart_1226096 : Nat := 118140960795 + 1226096 * 2 ^ 59
def prefixEnd_1226096 : Nat := 4983230072969 + 3 ^ 40 * 1226096 * 2
def baseEnd_1226096 : Nat := 69952952950571125273477

theorem tailTrace_1226096 : CollatzResearch.WordTrace tailWord_1226096 prefixEnd_1226096 69952952950571125273477 := by
  unfold tailWord_1226096
  simp only [CollatzResearch.WordTrace]
  refine ⟨22359697483035533685341071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29812929977380711580454761 22359697483035533685341071)
  ·
    refine ⟨33539546224553300528011607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22359697483035533685341071 33539546224553300528011607)
    ·
      refine ⟨50309319336829950792017411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33539546224553300528011607 50309319336829950792017411)
      ·
        refine ⟨75463979005244926188026117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50309319336829950792017411 75463979005244926188026117)
        ·
          refine ⟨14149496063483423660254897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 75463979005244926188026117 14149496063483423660254897)
          ·
            refine ⟨10612122047612567745191173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14149496063483423660254897 10612122047612567745191173)
            ·
              refine ⟨1989772883927356452223345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10612122047612567745191173 1989772883927356452223345)
              ·
                refine ⟨1492329662945517339167509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1989772883927356452223345 1492329662945517339167509)
                ·
                  refine ⟨69952952950571125273477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1492329662945517339167509 69952952950571125273477)
                  ·
                    rfl

theorem cell23_1226096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 4, 2, 6].length) (baseStart_1226096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1226096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1226096 prefixEnd_1226096 := by exact prefixLift 1226096
  have htrace : WordTrace (prefixWord ++ tailWord_1226096) baseStart_1226096 baseEnd_1226096 := by
    simpa [prefixWord, tailWord_1226096, baseEnd_1226096] using wordTrace_append hprefix tailTrace_1226096
  have hstable : (prefixWord ++ tailWord_1226096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1226096).length < 2 ^ (prefixWord ++ tailWord_1226096).sum := by decide
  have hdescent : baseEnd_1226096 < baseStart_1226096 := by decide
  rcases family_descends (prefixWord ++ tailWord_1226096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1226123 : List Nat := [1, 1, 1, 1, 4, 3, 3, 2, 3, 1, 3]
def baseStart_1226123 : Nat := 118140960795 + 1226123 * 2 ^ 59
def prefixEnd_1226123 : Nat := 4983230072969 + 3 ^ 40 * 1226123 * 2
def baseEnd_1226123 : Nat := 629590440532811521823669

theorem tailTrace_1226123 : CollatzResearch.WordTrace tailWord_1226123 prefixEnd_1226123 629590440532811521823669 := by
  unfold tailWord_1226123
  simp only [CollatzResearch.WordTrace]
  refine ⟨44720379736973250981915023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29813586491315500654610015 44720379736973250981915023)
  ·
    refine ⟨67080569605459876472872535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44720379736973250981915023 67080569605459876472872535)
    ·
      refine ⟨100620854408189814709308803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67080569605459876472872535 100620854408189814709308803)
      ·
        refine ⟨150931281612284722063963205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100620854408189814709308803 150931281612284722063963205)
        ·
          refine ⟨28299615302303385386993101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 150931281612284722063963205 28299615302303385386993101)
          ·
            refine ⟨10612355738363769520122413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28299615302303385386993101 10612355738363769520122413)
            ·
              refine ⟨3979633401886413570045905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10612355738363769520122413 3979633401886413570045905)
              ·
                refine ⟨2984725051414810177534429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3979633401886413570045905 2984725051414810177534429)
                ·
                  refine ⟨1119271894280553816575411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2984725051414810177534429 1119271894280553816575411)
                  ·
                    refine ⟨1678907841420830724863117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1119271894280553816575411 1678907841420830724863117)
                    ·
                      refine ⟨629590440532811521823669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1678907841420830724863117 629590440532811521823669)
                      ·
                        rfl

theorem cell23_1226123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 2, 3, 1, 3].length) (baseStart_1226123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1226123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1226123 prefixEnd_1226123 := by exact prefixLift 1226123
  have htrace : WordTrace (prefixWord ++ tailWord_1226123) baseStart_1226123 baseEnd_1226123 := by
    simpa [prefixWord, tailWord_1226123, baseEnd_1226123] using wordTrace_append hprefix tailTrace_1226123
  have hstable : (prefixWord ++ tailWord_1226123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1226123).length < 2 ^ (prefixWord ++ tailWord_1226123).sum := by decide
  have hdescent : baseEnd_1226123 < baseStart_1226123 := by decide
  rcases family_descends (prefixWord ++ tailWord_1226123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1226143 : List Nat := [1, 1, 2, 5, 1, 3, 1, 3, 1, 5]
def baseStart_1226143 : Nat := 118140960795 + 1226143 * 2 ^ 59
def prefixEnd_1226143 : Nat := 4983230072969 + 3 ^ 40 * 1226143 * 2
def baseEnd_1226143 : Nat := 209866903381967147857859

theorem tailTrace_1226143 : CollatzResearch.WordTrace tailWord_1226143 prefixEnd_1226143 209866903381967147857859 := by
  unfold tailWord_1226143
  simp only [CollatzResearch.WordTrace]
  refine ⟨44721109196900794397643083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29814072797933862931762055 44721109196900794397643083)
  ·
    refine ⟨67081663795351191596464625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44721109196900794397643083 67081663795351191596464625)
    ·
      refine ⟨50311247846513393697348469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67081663795351191596464625 50311247846513393697348469)
      ·
        refine ⟨4716679485610630659126419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 50311247846513393697348469 4716679485610630659126419)
        ·
          refine ⟨7075019228415945988689629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4716679485610630659126419 7075019228415945988689629)
          ·
            refine ⟨2653132210655979745758611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7075019228415945988689629 2653132210655979745758611)
            ·
              refine ⟨3979698315983969618637917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2653132210655979745758611 3979698315983969618637917)
              ·
                refine ⟨1492386868493988606989219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3979698315983969618637917 1492386868493988606989219)
                ·
                  refine ⟨2238580302740982910483829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1492386868493988606989219 2238580302740982910483829)
                  ·
                    refine ⟨209866903381967147857859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2238580302740982910483829 209866903381967147857859)
                    ·
                      rfl

theorem cell23_1226143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 3, 1, 5].length) (baseStart_1226143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1226143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1226143 prefixEnd_1226143 := by exact prefixLift 1226143
  have htrace : WordTrace (prefixWord ++ tailWord_1226143) baseStart_1226143 baseEnd_1226143 := by
    simpa [prefixWord, tailWord_1226143, baseEnd_1226143] using wordTrace_append hprefix tailTrace_1226143
  have hstable : (prefixWord ++ tailWord_1226143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1226143).length < 2 ^ (prefixWord ++ tailWord_1226143).sum := by decide
  have hdescent : baseEnd_1226143 < baseStart_1226143 := by decide
  rcases family_descends (prefixWord ++ tailWord_1226143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1226157 : List Nat := [1, 5, 2, 2, 1, 2, 2, 1, 3, 1, 3]
def baseStart_1226157 : Nat := 118140960795 + 1226157 * 2 ^ 59
def prefixEnd_1226157 : Nat := 4983230072969 + 3 ^ 40 * 1226157 * 2
def baseEnd_1226157 : Nat := 629607898875064388798513

theorem tailTrace_1226157 : CollatzResearch.WordTrace tailWord_1226157 prefixEnd_1226157 629607898875064388798513 := by
  unfold tailWord_1226157
  simp only [CollatzResearch.WordTrace]
  refine ⟨44721619818850074788652725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29814413212566716525768483 44721619818850074788652725)
  ·
    refine ⟨4192651858017194511436193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 44721619818850074788652725 4192651858017194511436193)
    ·
      refine ⟨3144488893512895883577145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4192651858017194511436193 3144488893512895883577145)
      ·
        refine ⟨2358366670134671912682859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3144488893512895883577145 2358366670134671912682859)
        ·
          refine ⟨3537550005202007869024289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2358366670134671912682859 3537550005202007869024289)
          ·
            refine ⟨2653162503901505901768217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3537550005202007869024289 2653162503901505901768217)
            ·
              refine ⟨1989871877926129426326163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2653162503901505901768217 1989871877926129426326163)
              ·
                refine ⟨2984807816889194139489245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1989871877926129426326163 2984807816889194139489245)
                ·
                  refine ⟨1119302931333447802308467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2984807816889194139489245 1119302931333447802308467)
                  ·
                    refine ⟨1678954397000171703462701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1119302931333447802308467 1678954397000171703462701)
                    ·
                      refine ⟨629607898875064388798513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1678954397000171703462701 629607898875064388798513)
                      ·
                        rfl

theorem cell23_1226157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_1226157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1226157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1226157 prefixEnd_1226157 := by exact prefixLift 1226157
  have htrace : WordTrace (prefixWord ++ tailWord_1226157) baseStart_1226157 baseEnd_1226157 := by
    simpa [prefixWord, tailWord_1226157, baseEnd_1226157] using wordTrace_append hprefix tailTrace_1226157
  have hstable : (prefixWord ++ tailWord_1226157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1226157).length < 2 ^ (prefixWord ++ tailWord_1226157).sum := by decide
  have hdescent : baseEnd_1226157 < baseStart_1226157 := by decide
  rcases family_descends (prefixWord ++ tailWord_1226157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1226180 : List Nat := [2, 3, 3, 2, 1, 1, 1, 4, 1, 1, 4]
def baseStart_1226180 : Nat := 118140960795 + 1226180 * 2 ^ 59
def prefixEnd_1226180 : Nat := 4983230072969 + 3 ^ 40 * 1226180 * 2
def baseEnd_1226180 : Nat := 629619708930117798810907

theorem tailTrace_1226180 : CollatzResearch.WordTrace tailWord_1226180 prefixEnd_1226180 629619708930117798810907 := by
  unfold tailWord_1226180
  simp only [CollatzResearch.WordTrace]
  refine ⟨22361229348883374858369997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29814972465177833144493329 22361229348883374858369997)
  ·
    refine ⟨8385461005831265571888749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22361229348883374858369997 8385461005831265571888749)
    ·
      refine ⟨3144547877186724589458281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8385461005831265571888749 3144547877186724589458281)
      ·
        refine ⟨2358410907890043442093711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3144547877186724589458281 2358410907890043442093711)
        ·
          refine ⟨3537616361835065163140567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2358410907890043442093711 3537616361835065163140567)
          ·
            refine ⟨5306424542752597744710851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3537616361835065163140567 5306424542752597744710851)
            ·
              refine ⟨7959636814128896617066277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5306424542752597744710851 7959636814128896617066277)
              ·
                refine ⟨1492431902649168115699927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7959636814128896617066277 1492431902649168115699927)
                ·
                  refine ⟨2238647853973752173549891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1492431902649168115699927 2238647853973752173549891)
                  ·
                    refine ⟨3357971780960628260324837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2238647853973752173549891 3357971780960628260324837)
                    ·
                      refine ⟨629619708930117798810907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3357971780960628260324837 629619708930117798810907)
                      ·
                        rfl

theorem cell23_1226180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_1226180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1226180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1226180 prefixEnd_1226180 := by exact prefixLift 1226180
  have htrace : WordTrace (prefixWord ++ tailWord_1226180) baseStart_1226180 baseEnd_1226180 := by
    simpa [prefixWord, tailWord_1226180, baseEnd_1226180] using wordTrace_append hprefix tailTrace_1226180
  have hstable : (prefixWord ++ tailWord_1226180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1226180).length < 2 ^ (prefixWord ++ tailWord_1226180).sum := by decide
  have hdescent : baseEnd_1226180 < baseStart_1226180 := by decide
  rcases family_descends (prefixWord ++ tailWord_1226180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1226186 : List Nat := [3, 1, 2, 1, 2, 4, 1, 9]
def baseStart_1226186 : Nat := 118140960795 + 1226186 * 2 ^ 59
def prefixEnd_1226186 : Nat := 4983230072969 + 3 ^ 40 * 1226186 * 2
def baseEnd_1226186 : Nat := 23319362585705362049477

theorem tailTrace_1226186 : CollatzResearch.WordTrace tailWord_1226186 prefixEnd_1226186 23319362585705362049477 := by
  unfold tailWord_1226186
  simp only [CollatzResearch.WordTrace]
  refine ⟨11180669383936253185364603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29815118357163341827638941 11180669383936253185364603)
  ·
    refine ⟨16771004075904379778046905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11180669383936253185364603 16771004075904379778046905)
    ·
      refine ⟨12578253056928284833535179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16771004075904379778046905 12578253056928284833535179)
      ·
        refine ⟨18867379585392427250302769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12578253056928284833535179 18867379585392427250302769)
        ·
          refine ⟨14150534689044320437727077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18867379585392427250302769 14150534689044320437727077)
          ·
            refine ⟨2653225254195810082073827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14150534689044320437727077 2653225254195810082073827)
            ·
              refine ⟨3979837881293715123110741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2653225254195810082073827 3979837881293715123110741)
              ·
                refine ⟨23319362585705362049477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3979837881293715123110741 23319362585705362049477)
                ·
                  rfl

theorem cell23_1226186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 9].length) (baseStart_1226186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1226186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1226186 prefixEnd_1226186 := by exact prefixLift 1226186
  have htrace : WordTrace (prefixWord ++ tailWord_1226186) baseStart_1226186 baseEnd_1226186 := by
    simpa [prefixWord, tailWord_1226186, baseEnd_1226186] using wordTrace_append hprefix tailTrace_1226186
  have hstable : (prefixWord ++ tailWord_1226186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1226186).length < 2 ^ (prefixWord ++ tailWord_1226186).sum := by decide
  have hdescent : baseEnd_1226186 < baseStart_1226186 := by decide
  rcases family_descends (prefixWord ++ tailWord_1226186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1226216 : List Nat := [2, 1, 4, 1, 1, 2, 2, 1, 2, 7]
def baseStart_1226216 : Nat := 118140960795 + 1226216 * 2 ^ 59
def prefixEnd_1226216 : Nat := 4983230072969 + 3 ^ 40 * 1226216 * 2
def baseEnd_1226216 : Nat := 209879398077893219320247

theorem tailTrace_1226216 : CollatzResearch.WordTrace tailWord_1226216 prefixEnd_1226216 209879398077893219320247 := by
  unfold tailWord_1226216
  simp only [CollatzResearch.WordTrace]
  refine ⟨22361885862818163932525251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29815847817090885243367001 22361885862818163932525251)
  ·
    refine ⟨33542828794227245898787877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22361885862818163932525251 33542828794227245898787877)
    ·
      refine ⟨6289280398917608606022727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33542828794227245898787877 6289280398917608606022727)
      ·
        refine ⟨9433920598376412909034091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6289280398917608606022727 9433920598376412909034091)
        ·
          refine ⟨14150880897564619363551137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9433920598376412909034091 14150880897564619363551137)
          ·
            refine ⟨10613160673173464522663353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14150880897564619363551137 10613160673173464522663353)
            ·
              refine ⟨7959870504880098391997515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10613160673173464522663353 7959870504880098391997515)
              ·
                refine ⟨11939805757320147587996273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7959870504880098391997515 11939805757320147587996273)
                ·
                  refine ⟨8954854317990110690997205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11939805757320147587996273 8954854317990110690997205)
                  ·
                    refine ⟨209879398077893219320247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8954854317990110690997205 209879398077893219320247)
                    ·
                      rfl

theorem cell23_1226216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 1, 2, 7].length) (baseStart_1226216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1226216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1226216 prefixEnd_1226216 := by exact prefixLift 1226216
  have htrace : WordTrace (prefixWord ++ tailWord_1226216) baseStart_1226216 baseEnd_1226216 := by
    simpa [prefixWord, tailWord_1226216, baseEnd_1226216] using wordTrace_append hprefix tailTrace_1226216
  have hstable : (prefixWord ++ tailWord_1226216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1226216).length < 2 ^ (prefixWord ++ tailWord_1226216).sum := by decide
  have hdescent : baseEnd_1226216 < baseStart_1226216 := by decide
  rcases family_descends (prefixWord ++ tailWord_1226216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1226257 : List Nat := [1, 2, 2, 1, 1, 2, 7, 1, 1, 3, 2]
def baseStart_1226257 : Nat := 118140960795 + 1226257 * 2 ^ 59
def prefixEnd_1226257 : Nat := 4983230072969 + 3 ^ 40 * 1226257 * 2
def baseEnd_1226257 : Nat := 629659246940513997548053

theorem tailTrace_1226257 : CollatzResearch.WordTrace tailWord_1226257 prefixEnd_1226257 629659246940513997548053 := by
  unfold tailWord_1226257
  simp only [CollatzResearch.WordTrace]
  refine ⟨44725267118487791867293025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29816844745658527911528683 44725267118487791867293025)
  ·
    refine ⟨33543950338865843900469769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44725267118487791867293025 33543950338865843900469769)
    ·
      refine ⟨25157962754149382925352327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33543950338865843900469769 25157962754149382925352327)
      ·
        refine ⟨37736944131224074388028491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25157962754149382925352327 37736944131224074388028491)
        ·
          refine ⟨56605416196836111582042737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37736944131224074388028491 56605416196836111582042737)
          ·
            refine ⟨42454062147627083686532053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56605416196836111582042737 42454062147627083686532053)
            ·
              refine ⟨995017081585009773903095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 42454062147627083686532053 995017081585009773903095)
              ·
                refine ⟨1492525622377514660854643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 995017081585009773903095 1492525622377514660854643)
                ·
                  refine ⟨2238788433566271991281965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1492525622377514660854643 2238788433566271991281965)
                  ·
                    refine ⟨839545662587351996730737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2238788433566271991281965 839545662587351996730737)
                    ·
                      refine ⟨629659246940513997548053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 839545662587351996730737 629659246940513997548053)
                      ·
                        rfl

theorem cell23_1226257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 7, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 7, 1, 1, 3, 2].length) (baseStart_1226257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1226257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1226257 prefixEnd_1226257 := by exact prefixLift 1226257
  have htrace : WordTrace (prefixWord ++ tailWord_1226257) baseStart_1226257 baseEnd_1226257 := by
    simpa [prefixWord, tailWord_1226257, baseEnd_1226257] using wordTrace_append hprefix tailTrace_1226257
  have hstable : (prefixWord ++ tailWord_1226257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1226257).length < 2 ^ (prefixWord ++ tailWord_1226257).sum := by decide
  have hdescent : baseEnd_1226257 < baseStart_1226257 := by decide
  rcases family_descends (prefixWord ++ tailWord_1226257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1226266 : List Nat := [3, 1, 1, 3, 1, 1, 1, 1, 2, 3, 6]
def baseStart_1226266 : Nat := 118140960795 + 1226266 * 2 ^ 59
def prefixEnd_1226266 : Nat := 4983230072969 + 3 ^ 40 * 1226266 * 2
def baseEnd_1226266 : Nat := 629663868266404462335511

theorem tailTrace_1226266 : CollatzResearch.WordTrace tailWord_1226266 prefixEnd_1226266 629663868266404462335511 := by
  unfold tailWord_1226266
  simp only [CollatzResearch.WordTrace]
  refine ⟨11181398843863796601092663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29817063583636790936247101 11181398843863796601092663)
  ·
    refine ⟨16772098265795694901638995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11181398843863796601092663 16772098265795694901638995)
    ·
      refine ⟨25158147398693542352458493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16772098265795694901638995 25158147398693542352458493)
      ·
        refine ⟨9434305274510078382171935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25158147398693542352458493 9434305274510078382171935)
        ·
          refine ⟨14151457911765117573257903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9434305274510078382171935 14151457911765117573257903)
          ·
            refine ⟨21227186867647676359886855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14151457911765117573257903 21227186867647676359886855)
            ·
              refine ⟨31840780301471514539830283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21227186867647676359886855 31840780301471514539830283)
              ·
                refine ⟨47761170452207271809745425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31840780301471514539830283 47761170452207271809745425)
                ·
                  refine ⟨35820877839155453857309069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47761170452207271809745425 35820877839155453857309069)
                  ·
                    refine ⟨13432829189683295196490901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35820877839155453857309069 13432829189683295196490901)
                    ·
                      refine ⟨629663868266404462335511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13432829189683295196490901 629663868266404462335511)
                      ·
                        rfl

theorem cell23_1226266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 2, 3, 6].length) (baseStart_1226266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1226266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1226266 prefixEnd_1226266 := by exact prefixLift 1226266
  have htrace : WordTrace (prefixWord ++ tailWord_1226266) baseStart_1226266 baseEnd_1226266 := by
    simpa [prefixWord, tailWord_1226266, baseEnd_1226266] using wordTrace_append hprefix tailTrace_1226266
  have hstable : (prefixWord ++ tailWord_1226266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1226266).length < 2 ^ (prefixWord ++ tailWord_1226266).sum := by decide
  have hdescent : baseEnd_1226266 < baseStart_1226266 := by decide
  rcases family_descends (prefixWord ++ tailWord_1226266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1226273 : List Nat := [1, 2, 3, 2, 2, 2, 1, 1, 2, 4, 3]
def baseStart_1226273 : Nat := 118140960795 + 1226273 * 2 ^ 59
def prefixEnd_1226273 : Nat := 4983230072969 + 3 ^ 40 * 1226273 * 2
def baseEnd_1226273 : Nat := 629667462630985934947979

theorem tailTrace_1226273 : CollatzResearch.WordTrace tailWord_1226273 prefixEnd_1226273 629667462630985934947979 := by
  unfold tailWord_1226273
  simp only [CollatzResearch.WordTrace]
  refine ⟨44725850686429826599875473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29817233790953217733250315 44725850686429826599875473)
  ·
    refine ⟨33544388014822369949906605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44725850686429826599875473 33544388014822369949906605)
    ·
      refine ⟨12579145505558388731214977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33544388014822369949906605 12579145505558388731214977)
      ·
        refine ⟨9434359129168791548411233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12579145505558388731214977 9434359129168791548411233)
        ·
          refine ⟨7075769346876593661308425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9434359129168791548411233 7075769346876593661308425)
          ·
            refine ⟨5306827010157445245981319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7075769346876593661308425 5306827010157445245981319)
            ·
              refine ⟨7960240515236167868971979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5306827010157445245981319 7960240515236167868971979)
              ·
                refine ⟨11940360772854251803457969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7960240515236167868971979 11940360772854251803457969)
                ·
                  refine ⟨8955270579640688852593477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11940360772854251803457969 8955270579640688852593477)
                  ·
                    refine ⟨1679113233682629159861277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8955270579640688852593477 1679113233682629159861277)
                    ·
                      refine ⟨629667462630985934947979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1679113233682629159861277 629667462630985934947979)
                      ·
                        rfl

theorem cell23_1226273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 1, 2, 4, 3].length) (baseStart_1226273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1226273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1226273 prefixEnd_1226273 := by exact prefixLift 1226273
  have htrace : WordTrace (prefixWord ++ tailWord_1226273) baseStart_1226273 baseEnd_1226273 := by
    simpa [prefixWord, tailWord_1226273, baseEnd_1226273] using wordTrace_append hprefix tailTrace_1226273
  have hstable : (prefixWord ++ tailWord_1226273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1226273).length < 2 ^ (prefixWord ++ tailWord_1226273).sum := by decide
  have hdescent : baseEnd_1226273 < baseStart_1226273 := by decide
  rcases family_descends (prefixWord ++ tailWord_1226273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1226280 : List Nat := [2, 1, 5, 2, 2, 1, 1, 1, 2, 6]
def baseStart_1226280 : Nat := 118140960795 + 1226280 * 2 ^ 59
def prefixEnd_1226280 : Nat := 4983230072969 + 3 ^ 40 * 1226280 * 2
def baseEnd_1226280 : Nat := 209890352331855802520149

theorem tailTrace_1226280 : CollatzResearch.WordTrace tailWord_1226280 prefixEnd_1226280 209890352331855802520149 := by
  unfold tailWord_1226280
  simp only [CollatzResearch.WordTrace]
  refine ⟨22363052998702233397690147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29817403998269644530253529 22363052998702233397690147)
  ·
    refine ⟨33544579498053350096535221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22363052998702233397690147 33544579498053350096535221)
    ·
      refine ⟨3144804327942501571550177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 33544579498053350096535221 3144804327942501571550177)
      ·
        refine ⟨2358603245956876178662633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3144804327942501571550177 2358603245956876178662633)
        ·
          refine ⟨1768952434467657133996975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2358603245956876178662633 1768952434467657133996975)
          ·
            refine ⟨2653428651701485700995463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1768952434467657133996975 2653428651701485700995463)
            ·
              refine ⟨3980142977552228551493195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2653428651701485700995463 3980142977552228551493195)
              ·
                refine ⟨5970214466328342827239793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3980142977552228551493195 5970214466328342827239793)
                ·
                  refine ⟨4477660849746257120429845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5970214466328342827239793 4477660849746257120429845)
                  ·
                    refine ⟨209890352331855802520149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4477660849746257120429845 209890352331855802520149)
                    ·
                      rfl

theorem cell23_1226280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 1, 2, 6].length) (baseStart_1226280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1226280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1226280 prefixEnd_1226280 := by exact prefixLift 1226280
  have htrace : WordTrace (prefixWord ++ tailWord_1226280) baseStart_1226280 baseEnd_1226280 := by
    simpa [prefixWord, tailWord_1226280, baseEnd_1226280] using wordTrace_append hprefix tailTrace_1226280
  have hstable : (prefixWord ++ tailWord_1226280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1226280).length < 2 ^ (prefixWord ++ tailWord_1226280).sum := by decide
  have hdescent : baseEnd_1226280 < baseStart_1226280 := by decide
  rcases family_descends (prefixWord ++ tailWord_1226280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1226293 : List Nat := [1, 3, 3, 1, 1, 4, 1, 2, 7]
def baseStart_1226293 : Nat := 118140960795 + 1226293 * 2 ^ 59
def prefixEnd_1226293 : Nat := 4983230072969 + 3 ^ 40 * 1226293 * 2
def baseEnd_1226293 : Nat := 69964192471563984077543

theorem tailTrace_1226293 : CollatzResearch.WordTrace tailWord_1226293 prefixEnd_1226293 69964192471563984077543 := by
  unfold tailWord_1226293
  simp only [CollatzResearch.WordTrace]
  refine ⟨44726580146357370015603533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29817720097571580010402355 44726580146357370015603533)
  ·
    refine ⟨16772467554884013755851325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44726580146357370015603533 16772467554884013755851325)
    ·
      refine ⟨6289675333081505158444247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16772467554884013755851325 6289675333081505158444247)
      ·
        refine ⟨9434512999622257737666371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6289675333081505158444247 9434512999622257737666371)
        ·
          refine ⟨14151769499433386606499557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9434512999622257737666371 14151769499433386606499557)
          ·
            refine ⟨2653456781143759988718667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14151769499433386606499557 2653456781143759988718667)
            ·
              refine ⟨3980185171715639983078001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2653456781143759988718667 3980185171715639983078001)
              ·
                refine ⟨2985138878786729987308501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3980185171715639983078001 2985138878786729987308501)
                ·
                  refine ⟨69964192471563984077543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2985138878786729987308501 69964192471563984077543)
                  ·
                    rfl

theorem cell23_1226293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 2, 7].length) (baseStart_1226293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1226293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1226293 prefixEnd_1226293 := by exact prefixLift 1226293
  have htrace : WordTrace (prefixWord ++ tailWord_1226293) baseStart_1226293 baseEnd_1226293 := by
    simpa [prefixWord, tailWord_1226293, baseEnd_1226293] using wordTrace_append hprefix tailTrace_1226293
  have hstable : (prefixWord ++ tailWord_1226293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1226293).length < 2 ^ (prefixWord ++ tailWord_1226293).sum := by decide
  have hdescent : baseEnd_1226293 < baseStart_1226293 := by decide
  rcases family_descends (prefixWord ++ tailWord_1226293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1226343 : List Nat := [1, 1, 5, 1, 1, 1, 3, 2, 1, 3, 4]
def baseStart_1226343 : Nat := 118140960795 + 1226343 * 2 ^ 59
def prefixEnd_1226343 : Nat := 4983230072969 + 3 ^ 40 * 1226343 * 2
def baseEnd_1226343 : Nat := 629703406276800661072657

theorem tailTrace_1226343 : CollatzResearch.WordTrace tailWord_1226343 prefixEnd_1226343 629703406276800661072657 := by
  unfold tailWord_1226343
  simp only [CollatzResearch.WordTrace]
  refine ⟨44728403796176228554923683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29818935864117485703282455 44728403796176228554923683)
  ·
    refine ⟨67092605694264342832385525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44728403796176228554923683 67092605694264342832385525)
    ·
      refine ⟨6289931783837282140536143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 67092605694264342832385525 6289931783837282140536143)
      ·
        refine ⟨9434897675755923210804215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6289931783837282140536143 9434897675755923210804215)
        ·
          refine ⟨14152346513633884816206323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9434897675755923210804215 14152346513633884816206323)
          ·
            refine ⟨21228519770450827224309485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14152346513633884816206323 21228519770450827224309485)
            ·
              refine ⟨7960694913919060209116057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21228519770450827224309485 7960694913919060209116057)
              ·
                refine ⟨5970521185439295156837043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7960694913919060209116057 5970521185439295156837043)
                ·
                  refine ⟨8955781778158942735255565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5970521185439295156837043 8955781778158942735255565)
                  ·
                    refine ⟨3358418166809603525720837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8955781778158942735255565 3358418166809603525720837)
                    ·
                      refine ⟨629703406276800661072657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3358418166809603525720837 629703406276800661072657)
                      ·
                        rfl

theorem cell23_1226343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 2, 1, 3, 4].length) (baseStart_1226343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1226343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1226343 prefixEnd_1226343 := by exact prefixLift 1226343
  have htrace : WordTrace (prefixWord ++ tailWord_1226343) baseStart_1226343 baseEnd_1226343 := by
    simpa [prefixWord, tailWord_1226343, baseEnd_1226343] using wordTrace_append hprefix tailTrace_1226343
  have hstable : (prefixWord ++ tailWord_1226343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1226343).length < 2 ^ (prefixWord ++ tailWord_1226343).sum := by decide
  have hdescent : baseEnd_1226343 < baseStart_1226343 := by decide
  rcases family_descends (prefixWord ++ tailWord_1226343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1226363 : List Nat := [1, 1, 1, 1, 1, 4, 3, 3, 1, 4, 3]
def baseStart_1226363 : Nat := 118140960795 + 1226363 * 2 ^ 59
def prefixEnd_1226363 : Nat := 4983230072969 + 3 ^ 40 * 1226363 * 2
def baseEnd_1226363 : Nat := 629713675889890582822565

theorem tailTrace_1226363 : CollatzResearch.WordTrace tailWord_1226363 prefixEnd_1226363 629713675889890582822565 := by
  unfold tailWord_1226363
  simp only [CollatzResearch.WordTrace]
  refine ⟨44729133256103771970651743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29819422170735847980434495 44729133256103771970651743)
  ·
    refine ⟨67093699884155657955977615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44729133256103771970651743 67093699884155657955977615)
    ·
      refine ⟨100640549826233486933966423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67093699884155657955977615 100640549826233486933966423)
      ·
        refine ⟨150960824739350230400949635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100640549826233486933966423 150960824739350230400949635)
        ·
          refine ⟨226441237109025345601424453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150960824739350230400949635 226441237109025345601424453)
          ·
            refine ⟨42457731957942252300267085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 226441237109025345601424453 42457731957942252300267085)
            ·
              refine ⟨15921649484228344612600157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42457731957942252300267085 15921649484228344612600157)
              ·
                refine ⟨5970618556585629229725059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15921649484228344612600157 5970618556585629229725059)
                ·
                  refine ⟨8955927834878443844587589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5970618556585629229725059 8955927834878443844587589)
                  ·
                    refine ⟨1679236469039708220860173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8955927834878443844587589 1679236469039708220860173)
                    ·
                      refine ⟨629713675889890582822565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1679236469039708220860173 629713675889890582822565)
                      ·
                        rfl

theorem cell23_1226363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 3, 1, 4, 3].length) (baseStart_1226363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1226363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1226363 prefixEnd_1226363 := by exact prefixLift 1226363
  have htrace : WordTrace (prefixWord ++ tailWord_1226363) baseStart_1226363 baseEnd_1226363 := by
    simpa [prefixWord, tailWord_1226363, baseEnd_1226363] using wordTrace_append hprefix tailTrace_1226363
  have hstable : (prefixWord ++ tailWord_1226363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1226363).length < 2 ^ (prefixWord ++ tailWord_1226363).sum := by decide
  have hdescent : baseEnd_1226363 < baseStart_1226363 := by decide
  rcases family_descends (prefixWord ++ tailWord_1226363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1226380 : List Nat := [2, 2, 1, 2, 1, 1, 5, 2, 2, 2, 3]
def baseStart_1226380 : Nat := 118140960795 + 1226380 * 2 ^ 59
def prefixEnd_1226380 : Nat := 4983230072969 + 3 ^ 40 * 1226380 * 2
def baseEnd_1226380 : Nat := 629722405061017016309987

theorem tailTrace_1226380 : CollatzResearch.WordTrace tailWord_1226380 prefixEnd_1226380 629722405061017016309987 := by
  unfold tailWord_1226380
  simp only [CollatzResearch.WordTrace]
  refine ⟨22364876648521091937010297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29819835531361455916013729 22364876648521091937010297)
  ·
    refine ⟨16773657486390818952757723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22364876648521091937010297 16773657486390818952757723)
    ·
      refine ⟨25160486229586228429136585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16773657486390818952757723 25160486229586228429136585)
      ·
        refine ⟨18870364672189671321852439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25160486229586228429136585 18870364672189671321852439)
        ·
          refine ⟨28305547008284506982778659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18870364672189671321852439 28305547008284506982778659)
          ·
            refine ⟨42458320512426760474167989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28305547008284506982778659 42458320512426760474167989)
            ·
              refine ⟨3980467548040008794453249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42458320512426760474167989 3980467548040008794453249)
              ·
                refine ⟨2985350661030006595839937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3980467548040008794453249 2985350661030006595839937)
                ·
                  refine ⟨2239012995772504946879953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2985350661030006595839937 2239012995772504946879953)
                  ·
                    refine ⟨1679259746829378710159965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2239012995772504946879953 1679259746829378710159965)
                    ·
                      refine ⟨629722405061017016309987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1679259746829378710159965 629722405061017016309987)
                      ·
                        rfl

theorem cell23_1226380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 2, 2, 2, 3].length) (baseStart_1226380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1226380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1226380 prefixEnd_1226380 := by exact prefixLift 1226380
  have htrace : WordTrace (prefixWord ++ tailWord_1226380) baseStart_1226380 baseEnd_1226380 := by
    simpa [prefixWord, tailWord_1226380, baseEnd_1226380] using wordTrace_append hprefix tailTrace_1226380
  have hstable : (prefixWord ++ tailWord_1226380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1226380).length < 2 ^ (prefixWord ++ tailWord_1226380).sum := by decide
  have hdescent : baseEnd_1226380 < baseStart_1226380 := by decide
  rcases family_descends (prefixWord ++ tailWord_1226380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1226393 : List Nat := [1, 2, 1, 2, 1, 2, 2, 2, 2, 5, 3]
def baseStart_1226393 : Nat := 118140960795 + 1226393 * 2 ^ 59
def prefixEnd_1226393 : Nat := 4983230072969 + 3 ^ 40 * 1226393 * 2
def baseEnd_1226393 : Nat := 629729080309525465447427

theorem tailTrace_1226393 : CollatzResearch.WordTrace tailWord_1226393 prefixEnd_1226393 629729080309525465447427 := by
  unfold tailWord_1226393
  simp only [CollatzResearch.WordTrace]
  refine ⟨44730227445995087094243833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29820151630663391396162555 44730227445995087094243833)
  ·
    refine ⟨33547670584496315320682875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44730227445995087094243833 33547670584496315320682875)
    ·
      refine ⟨50321505876744472981024313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33547670584496315320682875 50321505876744472981024313)
      ·
        refine ⟨37741129407558354735768235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50321505876744472981024313 37741129407558354735768235)
        ·
          refine ⟨56611694111337532103652353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37741129407558354735768235 56611694111337532103652353)
          ·
            refine ⟨42458770583503149077739265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56611694111337532103652353 42458770583503149077739265)
            ·
              refine ⟨31844077937627361808304449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42458770583503149077739265 31844077937627361808304449)
              ·
                refine ⟨23883058453220521356228337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31844077937627361808304449 23883058453220521356228337)
                ·
                  refine ⟨17912293839915391017171253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23883058453220521356228337 17912293839915391017171253)
                  ·
                    refine ⟨1679277547492067907859805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17912293839915391017171253 1679277547492067907859805)
                    ·
                      refine ⟨629729080309525465447427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1679277547492067907859805 629729080309525465447427)
                      ·
                        rfl

theorem cell23_1226393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 2, 5, 3].length) (baseStart_1226393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1226393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1226393 prefixEnd_1226393 := by exact prefixLift 1226393
  have htrace : WordTrace (prefixWord ++ tailWord_1226393) baseStart_1226393 baseEnd_1226393 := by
    simpa [prefixWord, tailWord_1226393, baseEnd_1226393] using wordTrace_append hprefix tailTrace_1226393
  have hstable : (prefixWord ++ tailWord_1226393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1226393).length < 2 ^ (prefixWord ++ tailWord_1226393).sum := by decide
  have hdescent : baseEnd_1226393 < baseStart_1226393 := by decide
  rcases family_descends (prefixWord ++ tailWord_1226393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1226400 : List Nat := [2, 1, 1, 4, 3, 2, 1, 3, 6]
def baseStart_1226400 : Nat := 118140960795 + 1226400 * 2 ^ 59
def prefixEnd_1226400 : Nat := 4983230072969 + 3 ^ 40 * 1226400 * 2
def baseEnd_1226400 : Nat := 69970297186011882006655

theorem tailTrace_1226400 : CollatzResearch.WordTrace tailWord_1226400 prefixEnd_1226400 69970297186011882006655 := by
  unfold tailWord_1226400
  simp only [CollatzResearch.WordTrace]
  refine ⟨22365241378484863644874327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29820321837979818193165769 22365241378484863644874327)
  ·
    refine ⟨33547862067727295467311491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22365241378484863644874327 33547862067727295467311491)
    ·
      refine ⟨50321793101590943200967237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33547862067727295467311491 50321793101590943200967237)
      ·
        refine ⟨9435336206548301850181357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50321793101590943200967237 9435336206548301850181357)
        ·
          refine ⟨3538251077455613193818009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9435336206548301850181357 3538251077455613193818009)
          ·
            refine ⟨2653688308091709895363507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3538251077455613193818009 2653688308091709895363507)
            ·
              refine ⟨3980532462137564843045261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2653688308091709895363507 3980532462137564843045261)
              ·
                refine ⟨1492699673301586816141973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3980532462137564843045261 1492699673301586816141973)
                ·
                  refine ⟨69970297186011882006655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1492699673301586816141973 69970297186011882006655)
                  ·
                    rfl

theorem cell23_1226400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 3, 6].length) (baseStart_1226400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1226400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1226400 prefixEnd_1226400 := by exact prefixLift 1226400
  have htrace : WordTrace (prefixWord ++ tailWord_1226400) baseStart_1226400 baseEnd_1226400 := by
    simpa [prefixWord, tailWord_1226400, baseEnd_1226400] using wordTrace_append hprefix tailTrace_1226400
  have hstable : (prefixWord ++ tailWord_1226400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1226400).length < 2 ^ (prefixWord ++ tailWord_1226400).sum := by decide
  have hdescent : baseEnd_1226400 < baseStart_1226400 := by decide
  rcases family_descends (prefixWord ++ tailWord_1226400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1226438 : List Nat := [6, 1, 2, 1, 1, 2, 1, 4, 1, 4]
def baseStart_1226438 : Nat := 118140960795 + 1226438 * 2 ^ 59
def prefixEnd_1226438 : Nat := 4983230072969 + 3 ^ 40 * 1226438 * 2
def baseEnd_1226438 : Nat := 209917395646325929794907

theorem tailTrace_1226438 : CollatzResearch.WordTrace tailWord_1226438 prefixEnd_1226438 209917395646325929794907 := by
  unfold tailWord_1226438
  simp only [CollatzResearch.WordTrace]
  refine ⟨1397870897838501868113499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 29821245820554706519754645 1397870897838501868113499)
  ·
    refine ⟨2096806346757752802170249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1397870897838501868113499 2096806346757752802170249)
    ·
      refine ⟨1572604760068314601627687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2096806346757752802170249 1572604760068314601627687)
      ·
        refine ⟨2358907140102471902441531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1572604760068314601627687 2358907140102471902441531)
        ·
          refine ⟨3538360710153707853662297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2358907140102471902441531 3538360710153707853662297)
          ·
            refine ⟨2653770532615280890246723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3538360710153707853662297 2653770532615280890246723)
            ·
              refine ⟨3980655798922921335370085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2653770532615280890246723 3980655798922921335370085)
              ·
                refine ⟨746372962298047750381891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3980655798922921335370085 746372962298047750381891)
                ·
                  refine ⟨1119559443447071625572837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 746372962298047750381891 1119559443447071625572837)
                  ·
                    refine ⟨209917395646325929794907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1119559443447071625572837 209917395646325929794907)
                    ·
                      rfl

theorem cell23_1226438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_1226438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1226438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1226438 prefixEnd_1226438 := by exact prefixLift 1226438
  have htrace : WordTrace (prefixWord ++ tailWord_1226438) baseStart_1226438 baseEnd_1226438 := by
    simpa [prefixWord, tailWord_1226438, baseEnd_1226438] using wordTrace_append hprefix tailTrace_1226438
  have hstable : (prefixWord ++ tailWord_1226438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1226438).length < 2 ^ (prefixWord ++ tailWord_1226438).sum := by decide
  have hdescent : baseEnd_1226438 < baseStart_1226438 := by decide
  rcases family_descends (prefixWord ++ tailWord_1226438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1226461 : List Nat := [1, 4, 3, 3, 1, 1, 1, 2, 3, 1, 3]
def baseStart_1226461 : Nat := 118140960795 + 1226461 * 2 ^ 59
def prefixEnd_1226461 : Nat := 4983230072969 + 3 ^ 40 * 1226461 * 2
def baseEnd_1226461 : Nat := 629763996994031199397115

theorem tailTrace_1226461 : CollatzResearch.WordTrace tailWord_1226461 prefixEnd_1226461 629763996994031199397115 := by
  unfold tailWord_1226461
  simp only [CollatzResearch.WordTrace]
  refine ⟨44732707609748734707719237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29821805073165823138479491 44732707609748734707719237)
  ·
    refine ⟨8387382676827887757697357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44732707609748734707719237 8387382676827887757697357)
    ·
      refine ⟨3145268503810457909136509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8387382676827887757697357 3145268503810457909136509)
      ·
        refine ⟨1179475688928921715926191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3145268503810457909136509 1179475688928921715926191)
        ·
          refine ⟨1769213533393382573889287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1179475688928921715926191 1769213533393382573889287)
          ·
            refine ⟨2653820300090073860833931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1769213533393382573889287 2653820300090073860833931)
            ·
              refine ⟨3980730450135110791250897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2653820300090073860833931 3980730450135110791250897)
              ·
                refine ⟨2985547837601333093438173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3980730450135110791250897 2985547837601333093438173)
                ·
                  refine ⟨1119580439100499910039315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2985547837601333093438173 1119580439100499910039315)
                  ·
                    refine ⟨1679370658650749865058973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1119580439100499910039315 1679370658650749865058973)
                    ·
                      refine ⟨629763996994031199397115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1679370658650749865058973 629763996994031199397115)
                      ·
                        rfl

theorem cell23_1226461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_1226461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1226461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1226461 prefixEnd_1226461 := by exact prefixLift 1226461
  have htrace : WordTrace (prefixWord ++ tailWord_1226461) baseStart_1226461 baseEnd_1226461 := by
    simpa [prefixWord, tailWord_1226461, baseEnd_1226461] using wordTrace_append hprefix tailTrace_1226461
  have hstable : (prefixWord ++ tailWord_1226461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1226461).length < 2 ^ (prefixWord ++ tailWord_1226461).sum := by decide
  have hdescent : baseEnd_1226461 < baseStart_1226461 := by decide
  rcases family_descends (prefixWord ++ tailWord_1226461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1226494 : List Nat := [4, 2, 2, 1, 3, 1, 1, 1, 4, 4]
def baseStart_1226494 : Nat := 118140960795 + 1226494 * 2 ^ 59
def prefixEnd_1226494 : Nat := 4983230072969 + 3 ^ 40 * 1226494 * 2
def baseEnd_1226494 : Nat := 209926980618543190094821

theorem tailTrace_1226494 : CollatzResearch.WordTrace tailWord_1226494 prefixEnd_1226494 209926980618543190094821 := by
  unfold tailWord_1226494
  simp only [CollatzResearch.WordTrace]
  refine ⟨5591738902328647667958817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29822607479086120895780357 5591738902328647667958817)
  ·
    refine ⟨4193804176746485750969113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5591738902328647667958817 4193804176746485750969113)
    ·
      refine ⟨3145353132559864313226835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4193804176746485750969113 3145353132559864313226835)
      ·
        refine ⟨4718029698839796469840253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3145353132559864313226835 4718029698839796469840253)
        ·
          refine ⟨1769261137064923676190095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4718029698839796469840253 1769261137064923676190095)
          ·
            refine ⟨2653891705597385514285143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1769261137064923676190095 2653891705597385514285143)
            ·
              refine ⟨3980837558396078271427715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2653891705597385514285143 3980837558396078271427715)
              ·
                refine ⟨5971256337594117407141573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3980837558396078271427715 5971256337594117407141573)
                ·
                  refine ⟨1119610563298897013839045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5971256337594117407141573 1119610563298897013839045)
                  ·
                    refine ⟨209926980618543190094821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1119610563298897013839045 209926980618543190094821)
                    ·
                      rfl

theorem cell23_1226494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 1, 4, 4].length) (baseStart_1226494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1226494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1226494 prefixEnd_1226494 := by exact prefixLift 1226494
  have htrace : WordTrace (prefixWord ++ tailWord_1226494) baseStart_1226494 baseEnd_1226494 := by
    simpa [prefixWord, tailWord_1226494, baseEnd_1226494] using wordTrace_append hprefix tailTrace_1226494
  have hstable : (prefixWord ++ tailWord_1226494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1226494).length < 2 ^ (prefixWord ++ tailWord_1226494).sum := by decide
  have hdescent : baseEnd_1226494 < baseStart_1226494 := by decide
  rcases family_descends (prefixWord ++ tailWord_1226494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1226514 : List Nat := [3, 2, 4, 1, 1, 1, 3, 1, 1, 2, 4]
def baseStart_1226514 : Nat := 118140960795 + 1226514 * 2 ^ 59
def prefixEnd_1226514 : Nat := 4983230072969 + 3 ^ 40 * 1226514 * 2
def baseEnd_1226514 : Nat := 629791211468719492034371

theorem tailTrace_1226514 : CollatzResearch.WordTrace tailWord_1226514 prefixEnd_1226514 629791211468719492034371 := by
  unfold tailWord_1226514
  simp only [CollatzResearch.WordTrace]
  refine ⟨11183660169639181189849649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29823093785704483172932397 11183660169639181189849649)
  ·
    refine ⟨8387745127229385892387237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11183660169639181189849649 8387745127229385892387237)
    ·
      refine ⟨1572702211355509854822607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8387745127229385892387237 1572702211355509854822607)
      ·
        refine ⟨2359053317033264782233911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1572702211355509854822607 2359053317033264782233911)
        ·
          refine ⟨3538579975549897173350867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2359053317033264782233911 3538579975549897173350867)
          ·
            refine ⟨5307869963324845760026301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3538579975549897173350867 5307869963324845760026301)
            ·
              refine ⟨1990451236246817160009863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5307869963324845760026301 1990451236246817160009863)
              ·
                refine ⟨2985676854370225740014795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1990451236246817160009863 2985676854370225740014795)
                ·
                  refine ⟨4478515281555338610022193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2985676854370225740014795 4478515281555338610022193)
                  ·
                    refine ⟨3358886461166503957516645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4478515281555338610022193 3358886461166503957516645)
                    ·
                      refine ⟨629791211468719492034371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3358886461166503957516645 629791211468719492034371)
                      ·
                        rfl

theorem cell23_1226514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_1226514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1226514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1226514 prefixEnd_1226514 := by exact prefixLift 1226514
  have htrace : WordTrace (prefixWord ++ tailWord_1226514) baseStart_1226514 baseEnd_1226514 := by
    simpa [prefixWord, tailWord_1226514, baseEnd_1226514] using wordTrace_append hprefix tailTrace_1226514
  have hstable : (prefixWord ++ tailWord_1226514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1226514).length < 2 ^ (prefixWord ++ tailWord_1226514).sum := by decide
  have hdescent : baseEnd_1226514 < baseStart_1226514 := by decide
  rcases family_descends (prefixWord ++ tailWord_1226514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1226517 : List Nat := [1, 3, 2, 1, 2, 3, 3, 1, 1, 3, 3]
def baseStart_1226517 : Nat := 118140960795 + 1226517 * 2 ^ 59
def prefixEnd_1226517 : Nat := 4983230072969 + 3 ^ 40 * 1226517 * 2
def baseEnd_1226517 : Nat := 629792751910682980296857

theorem tailTrace_1226517 : CollatzResearch.WordTrace tailWord_1226517 prefixEnd_1226517 629792751910682980296857 := by
  unfold tailWord_1226517
  simp only [CollatzResearch.WordTrace]
  refine ⟨44734750097545856271757805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29823166731697237514505203 44734750097545856271757805)
  ·
    refine ⟨16775531286579696101909177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44734750097545856271757805 16775531286579696101909177)
    ·
      refine ⟨12581648464934772076431883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16775531286579696101909177 12581648464934772076431883)
      ·
        refine ⟨18872472697402158114647825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12581648464934772076431883 18872472697402158114647825)
        ·
          refine ⟨14154354523051618585985869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18872472697402158114647825 14154354523051618585985869)
          ·
            refine ⟨5307882946144356969744701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14154354523051618585985869 5307882946144356969744701)
            ·
              refine ⟨1990456104804133863654263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5307882946144356969744701 1990456104804133863654263)
              ·
                refine ⟨2985684157206200795481395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1990456104804133863654263 2985684157206200795481395)
                ·
                  refine ⟨4478526235809301193222093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2985684157206200795481395 4478526235809301193222093)
                  ·
                    refine ⟨1679447338428487947458285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4478526235809301193222093 1679447338428487947458285)
                    ·
                      refine ⟨629792751910682980296857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1679447338428487947458285 629792751910682980296857)
                      ·
                        rfl

theorem cell23_1226517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 3, 1, 1, 3, 3].length) (baseStart_1226517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1226517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1226517 prefixEnd_1226517 := by exact prefixLift 1226517
  have htrace : WordTrace (prefixWord ++ tailWord_1226517) baseStart_1226517 baseEnd_1226517 := by
    simpa [prefixWord, tailWord_1226517, baseEnd_1226517] using wordTrace_append hprefix tailTrace_1226517
  have hstable : (prefixWord ++ tailWord_1226517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1226517).length < 2 ^ (prefixWord ++ tailWord_1226517).sum := by decide
  have hdescent : baseEnd_1226517 < baseStart_1226517 := by decide
  rcases family_descends (prefixWord ++ tailWord_1226517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1226530 : List Nat := [3, 3, 1, 1, 2, 1, 1, 1, 1, 4, 5]
def baseStart_1226530 : Nat := 118140960795 + 1226530 * 2 ^ 59
def prefixEnd_1226530 : Nat := 4983230072969 + 3 ^ 40 * 1226530 * 2
def baseEnd_1226530 : Nat := 629799427159191429434297

theorem tailTrace_1226530 : CollatzResearch.WordTrace tailWord_1226530 prefixEnd_1226530 629799427159191429434297 := by
  unfold tailWord_1226530
  simp only [CollatzResearch.WordTrace]
  refine ⟨11183806061624689872995261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29823482830999172994654029 11183806061624689872995261)
  ·
    refine ⟨4193927273109258702373223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11183806061624689872995261 4193927273109258702373223)
    ·
      refine ⟨6290890909663888053559835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4193927273109258702373223 6290890909663888053559835)
      ·
        refine ⟨9436336364495832080339753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6290890909663888053559835 9436336364495832080339753)
        ·
          refine ⟨7077252273371874060254815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9436336364495832080339753 7077252273371874060254815)
          ·
            refine ⟨10615878410057811090382223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7077252273371874060254815 10615878410057811090382223)
            ·
              refine ⟨15923817615086716635573335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10615878410057811090382223 15923817615086716635573335)
              ·
                refine ⟨23885726422630074953360003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15923817615086716635573335 23885726422630074953360003)
                ·
                  refine ⟨35828589633945112430040005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23885726422630074953360003 35828589633945112430040005)
                  ·
                    refine ⟨6717860556364708580632501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35828589633945112430040005 6717860556364708580632501)
                    ·
                      refine ⟨629799427159191429434297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6717860556364708580632501 629799427159191429434297)
                      ·
                        rfl

theorem cell23_1226530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 1, 1, 4, 5].length) (baseStart_1226530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1226530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1226530 prefixEnd_1226530 := by exact prefixLift 1226530
  have htrace : WordTrace (prefixWord ++ tailWord_1226530) baseStart_1226530 baseEnd_1226530 := by
    simpa [prefixWord, tailWord_1226530, baseEnd_1226530] using wordTrace_append hprefix tailTrace_1226530
  have hstable : (prefixWord ++ tailWord_1226530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1226530).length < 2 ^ (prefixWord ++ tailWord_1226530).sum := by decide
  have hdescent : baseEnd_1226530 < baseStart_1226530 := by decide
  rcases family_descends (prefixWord ++ tailWord_1226530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1226570 : List Nat := [3, 1, 2, 1, 1, 1, 4, 1, 1, 4, 4]
def baseStart_1226570 : Nat := 118140960795 + 1226570 * 2 ^ 59
def prefixEnd_1226570 : Nat := 4983230072969 + 3 ^ 40 * 1226570 * 2
def baseEnd_1226570 : Nat := 629819966385371272934113

theorem tailTrace_1226570 : CollatzResearch.WordTrace tailWord_1226570 prefixEnd_1226570 629819966385371272934113 := by
  unfold tailWord_1226570
  simp only [CollatzResearch.WordTrace]
  refine ⟨11184170791588461580859291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29824455444235897548958109 11184170791588461580859291)
  ·
    refine ⟨16776256187382692371288937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11184170791588461580859291 16776256187382692371288937)
    ·
      refine ⟨12582192140537019278466703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16776256187382692371288937 12582192140537019278466703)
      ·
        refine ⟨18873288210805528917700055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12582192140537019278466703 18873288210805528917700055)
        ·
          refine ⟨28309932316208293376550083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18873288210805528917700055 28309932316208293376550083)
          ·
            refine ⟨42464898474312440064825125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28309932316208293376550083 42464898474312440064825125)
            ·
              refine ⟨7962168463933582512154711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42464898474312440064825125 7962168463933582512154711)
              ·
                refine ⟨11943252695900373768232067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7962168463933582512154711 11943252695900373768232067)
                ·
                  refine ⟨17914879043850560652348101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11943252695900373768232067 17914879043850560652348101)
                  ·
                    refine ⟨3359039820721980122315269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17914879043850560652348101 3359039820721980122315269)
                    ·
                      refine ⟨629819966385371272934113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3359039820721980122315269 629819966385371272934113)
                      ·
                        rfl

theorem cell23_1226570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 1, 1, 4, 4].length) (baseStart_1226570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1226570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1226570 prefixEnd_1226570 := by exact prefixLift 1226570
  have htrace : WordTrace (prefixWord ++ tailWord_1226570) baseStart_1226570 baseEnd_1226570 := by
    simpa [prefixWord, tailWord_1226570, baseEnd_1226570] using wordTrace_append hprefix tailTrace_1226570
  have hstable : (prefixWord ++ tailWord_1226570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1226570).length < 2 ^ (prefixWord ++ tailWord_1226570).sum := by decide
  have hdescent : baseEnd_1226570 < baseStart_1226570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1226570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1226597 : List Nat := [1, 3, 1, 3, 1, 1, 1, 7, 5]
def baseStart_1226597 : Nat := 118140960795 + 1226597 * 2 ^ 59
def prefixEnd_1226597 : Nat := 4983230072969 + 3 ^ 40 * 1226597 * 2
def baseEnd_1226597 : Nat := 69981536707004740810721

theorem tailTrace_1226597 : CollatzResearch.WordTrace tailWord_1226597 prefixEnd_1226597 69981536707004740810721 := by
  unfold tailWord_1226597
  simp only [CollatzResearch.WordTrace]
  refine ⟨44737667937256029934670045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29825111958170686623113363 44737667937256029934670045)
  ·
    refine ⟨16776625476471011225501267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44737667937256029934670045 16776625476471011225501267)
    ·
      refine ⟨25164938214706516838251901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16776625476471011225501267 25164938214706516838251901)
      ·
        refine ⟨9436851830514943814344463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25164938214706516838251901 9436851830514943814344463)
        ·
          refine ⟨14155277745772415721516695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9436851830514943814344463 14155277745772415721516695)
          ·
            refine ⟨21232916618658623582275043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14155277745772415721516695 21232916618658623582275043)
            ·
              refine ⟨31849374927987935373412565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21232916618658623582275043 31849374927987935373412565)
              ·
                refine ⟨746469724874717235314357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 31849374927987935373412565 746469724874717235314357)
                ·
                  refine ⟨69981536707004740810721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 746469724874717235314357 69981536707004740810721)
                  ·
                    rfl

theorem cell23_1226597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 7, 5].length) (baseStart_1226597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1226597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1226597 prefixEnd_1226597 := by exact prefixLift 1226597
  have htrace : WordTrace (prefixWord ++ tailWord_1226597) baseStart_1226597 baseEnd_1226597 := by
    simpa [prefixWord, tailWord_1226597, baseEnd_1226597] using wordTrace_append hprefix tailTrace_1226597
  have hstable : (prefixWord ++ tailWord_1226597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1226597).length < 2 ^ (prefixWord ++ tailWord_1226597).sum := by decide
  have hdescent : baseEnd_1226597 < baseStart_1226597 := by decide
  rcases family_descends (prefixWord ++ tailWord_1226597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1226610 : List Nat := [3, 2, 1, 2, 1, 1, 1, 2, 3, 7]
def baseStart_1226610 : Nat := 118140960795 + 1226610 * 2 ^ 59
def prefixEnd_1226610 : Nat := 4983230072969 + 3 ^ 40 * 1226610 * 2
def baseEnd_1226610 : Nat := 209946835203850372144643

theorem tailTrace_1226610 : CollatzResearch.WordTrace tailWord_1226610 prefixEnd_1226610 209946835203850372144643 := by
  unfold tailWord_1226610
  simp only [CollatzResearch.WordTrace]
  refine ⟨11184535521552233288723321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29825428057472622103262189 11184535521552233288723321)
  ·
    refine ⟨8388401641164174966542491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11184535521552233288723321 8388401641164174966542491)
    ·
      refine ⟨12582602461746262449813737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8388401641164174966542491 12582602461746262449813737)
      ·
        refine ⟨9436951846309696837360303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12582602461746262449813737 9436951846309696837360303)
        ·
          refine ⟨14155427769464545256040455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9436951846309696837360303 14155427769464545256040455)
          ·
            refine ⟨21233141654196817884060683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14155427769464545256040455 21233141654196817884060683)
            ·
              refine ⟨31849712481295226826091025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21233141654196817884060683 31849712481295226826091025)
              ·
                refine ⟨23887284360971420119568269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31849712481295226826091025 23887284360971420119568269)
                ·
                  refine ⟨8957731635364282544838101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23887284360971420119568269 8957731635364282544838101)
                  ·
                    refine ⟨209946835203850372144643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8957731635364282544838101 209946835203850372144643)
                    ·
                      rfl

theorem cell23_1226610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 2, 3, 7].length) (baseStart_1226610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1226610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1226610 prefixEnd_1226610 := by exact prefixLift 1226610
  have htrace : WordTrace (prefixWord ++ tailWord_1226610) baseStart_1226610 baseEnd_1226610 := by
    simpa [prefixWord, tailWord_1226610, baseEnd_1226610] using wordTrace_append hprefix tailTrace_1226610
  have hstable : (prefixWord ++ tailWord_1226610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1226610).length < 2 ^ (prefixWord ++ tailWord_1226610).sum := by decide
  have hdescent : baseEnd_1226610 < baseStart_1226610 := by decide
  rcases family_descends (prefixWord ++ tailWord_1226610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1226617 : List Nat := [1, 2, 1, 3, 2, 2, 1, 1, 1, 7, 2]
def baseStart_1226617 : Nat := 118140960795 + 1226617 * 2 ^ 59
def prefixEnd_1226617 : Nat := 4983230072969 + 3 ^ 40 * 1226617 * 2
def baseEnd_1226617 : Nat := 629844099976132589046397

theorem tailTrace_1226617 : CollatzResearch.WordTrace tailWord_1226617 prefixEnd_1226617 629844099976132589046397 := by
  unfold tailWord_1226617
  simp only [CollatzResearch.WordTrace]
  refine ⟨44738397397183573350398105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29825598264789048900265403 44738397397183573350398105)
  ·
    refine ⟨33553798047887680012798579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44738397397183573350398105 33553798047887680012798579)
    ·
      refine ⟨50330697071831520019197869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33553798047887680012798579 50330697071831520019197869)
      ·
        refine ⟨18874011401936820007199201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50330697071831520019197869 18874011401936820007199201)
        ·
          refine ⟨14155508551452615005399401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18874011401936820007199201 14155508551452615005399401)
          ·
            refine ⟨10616631413589461254049551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14155508551452615005399401 10616631413589461254049551)
            ·
              refine ⟨15924947120384191881074327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10616631413589461254049551 15924947120384191881074327)
              ·
                refine ⟨23887420680576287821611491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15924947120384191881074327 23887420680576287821611491)
                ·
                  refine ⟨35831131020864431732417237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23887420680576287821611491 35831131020864431732417237)
                  ·
                    refine ⟨839792133301510118728529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35831131020864431732417237 839792133301510118728529)
                    ·
                      refine ⟨629844099976132589046397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 839792133301510118728529 629844099976132589046397)
                      ·
                        rfl

theorem cell23_1226617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 1, 1, 7, 2].length) (baseStart_1226617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1226617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1226617 prefixEnd_1226617 := by exact prefixLift 1226617
  have htrace : WordTrace (prefixWord ++ tailWord_1226617) baseStart_1226617 baseEnd_1226617 := by
    simpa [prefixWord, tailWord_1226617, baseEnd_1226617] using wordTrace_append hprefix tailTrace_1226617
  have hstable : (prefixWord ++ tailWord_1226617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1226617).length < 2 ^ (prefixWord ++ tailWord_1226617).sum := by decide
  have hdescent : baseEnd_1226617 < baseStart_1226617 := by decide
  rcases family_descends (prefixWord ++ tailWord_1226617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1226644 : List Nat := [2, 4, 2, 1, 1, 2, 3, 1, 2, 5]
def baseStart_1226644 : Nat := 118140960795 + 1226644 * 2 ^ 59
def prefixEnd_1226644 : Nat := 4983230072969 + 3 ^ 40 * 1226644 * 2
def baseEnd_1226644 : Nat := 209952654651267994469591

theorem tailTrace_1226644 : CollatzResearch.WordTrace tailWord_1226644 prefixEnd_1226644 209952654651267994469591 := by
  unfold tailWord_1226644
  simp only [CollatzResearch.WordTrace]
  refine ⟨22369691084042878480815493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29826254778723837974420657 22369691084042878480815493)
  ·
    refine ⟨4194317078258039715152905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22369691084042878480815493 4194317078258039715152905)
    ·
      refine ⟨3145737808693529786364679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4194317078258039715152905 3145737808693529786364679)
      ·
        refine ⟨4718606713040294679547019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3145737808693529786364679 4718606713040294679547019)
        ·
          refine ⟨7077910069560442019320529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4718606713040294679547019 7077910069560442019320529)
          ·
            refine ⟨5308432552170331514490397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7077910069560442019320529 5308432552170331514490397)
            ·
              refine ⟨1990662207063874317933899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5308432552170331514490397 1990662207063874317933899)
              ·
                refine ⟨2985993310595811476900849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1990662207063874317933899 2985993310595811476900849)
                ·
                  refine ⟨2239494982946858607675637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2985993310595811476900849 2239494982946858607675637)
                  ·
                    refine ⟨209952654651267994469591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2239494982946858607675637 209952654651267994469591)
                    ·
                      rfl

theorem cell23_1226644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 3, 1, 2, 5].length) (baseStart_1226644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1226644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1226644 prefixEnd_1226644 := by exact prefixLift 1226644
  have htrace : WordTrace (prefixWord ++ tailWord_1226644) baseStart_1226644 baseEnd_1226644 := by
    simpa [prefixWord, tailWord_1226644, baseEnd_1226644] using wordTrace_append hprefix tailTrace_1226644
  have hstable : (prefixWord ++ tailWord_1226644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1226644).length < 2 ^ (prefixWord ++ tailWord_1226644).sum := by decide
  have hdescent : baseEnd_1226644 < baseStart_1226644 := by decide
  rcases family_descends (prefixWord ++ tailWord_1226644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1226647 : List Nat := [1, 1, 3, 3, 1, 4, 1, 1, 1, 3, 4]
def baseStart_1226647 : Nat := 118140960795 + 1226647 * 2 ^ 59
def prefixEnd_1226647 : Nat := 4983230072969 + 3 ^ 40 * 1226647 * 2
def baseEnd_1226647 : Nat := 629859504395767471671259

theorem tailTrace_1226647 : CollatzResearch.WordTrace tailWord_1226647 prefixEnd_1226647 629859504395767471671259 := by
  unfold tailWord_1226647
  simp only [CollatzResearch.WordTrace]
  refine ⟨44739491587074888473990195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29826327724716592315993463 44739491587074888473990195)
  ·
    refine ⟨67109237380612332710985293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44739491587074888473990195 67109237380612332710985293)
    ·
      refine ⟨25165964017729624766619485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67109237380612332710985293 25165964017729624766619485)
      ·
        refine ⟨9437236506648609287482307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25165964017729624766619485 9437236506648609287482307)
        ·
          refine ⟨14155854759972913931223461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9437236506648609287482307 14155854759972913931223461)
          ·
            refine ⟨2654222767494921362104399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14155854759972913931223461 2654222767494921362104399)
            ·
              refine ⟨3981334151242382043156599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2654222767494921362104399 3981334151242382043156599)
              ·
                refine ⟨5972001226863573064734899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3981334151242382043156599 5972001226863573064734899)
                ·
                  refine ⟨8958001840295359597102349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5972001226863573064734899 8958001840295359597102349)
                  ·
                    refine ⟨3359250690110759848913381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8958001840295359597102349 3359250690110759848913381)
                    ·
                      refine ⟨629859504395767471671259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3359250690110759848913381 629859504395767471671259)
                      ·
                        rfl

theorem cell23_1226647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 1, 1, 3, 4].length) (baseStart_1226647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1226647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1226647 prefixEnd_1226647 := by exact prefixLift 1226647
  have htrace : WordTrace (prefixWord ++ tailWord_1226647) baseStart_1226647 baseEnd_1226647 := by
    simpa [prefixWord, tailWord_1226647, baseEnd_1226647] using wordTrace_append hprefix tailTrace_1226647
  have hstable : (prefixWord ++ tailWord_1226647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1226647).length < 2 ^ (prefixWord ++ tailWord_1226647).sum := by decide
  have hdescent : baseEnd_1226647 < baseStart_1226647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1226647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1226731 : List Nat := [1, 1, 1, 1, 2, 3, 1, 8, 1, 1, 3]
def baseStart_1226731 : Nat := 118140960795 + 1226731 * 2 ^ 59
def prefixEnd_1226731 : Nat := 4983230072969 + 3 ^ 40 * 1226731 * 2
def baseEnd_1226731 : Nat := 629902636770745143020873

theorem tailTrace_1226731 : CollatzResearch.WordTrace tailWord_1226731 prefixEnd_1226731 629902636770745143020873 := by
  unfold tailWord_1226731
  simp only [CollatzResearch.WordTrace]
  refine ⟨44742555318770570820048047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29828370212513713880032031 44742555318770570820048047)
  ·
    refine ⟨67113832978155856230072071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44742555318770570820048047 67113832978155856230072071)
    ·
      refine ⟨100670749467233784345108107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67113832978155856230072071 100670749467233784345108107)
      ·
        refine ⟨151006124200850676517662161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100670749467233784345108107 151006124200850676517662161)
        ·
          refine ⟨113254593150638007388246621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 151006124200850676517662161 113254593150638007388246621)
          ·
            refine ⟨42470472431489252770592483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 113254593150638007388246621 42470472431489252770592483)
            ·
              refine ⟨63705708647233879155888725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42470472431489252770592483 63705708647233879155888725)
              ·
                refine ⟨746551273209772021358071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 63705708647233879155888725 746551273209772021358071)
                ·
                  refine ⟨1119826909814658032037107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 746551273209772021358071 1119826909814658032037107)
                  ·
                    refine ⟨1679740364721987048055661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1119826909814658032037107 1679740364721987048055661)
                    ·
                      refine ⟨629902636770745143020873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1679740364721987048055661 629902636770745143020873)
                      ·
                        rfl

theorem cell23_1226731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 8, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 8, 1, 1, 3].length) (baseStart_1226731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1226731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1226731 prefixEnd_1226731 := by exact prefixLift 1226731
  have htrace : WordTrace (prefixWord ++ tailWord_1226731) baseStart_1226731 baseEnd_1226731 := by
    simpa [prefixWord, tailWord_1226731, baseEnd_1226731] using wordTrace_append hprefix tailTrace_1226731
  have hstable : (prefixWord ++ tailWord_1226731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1226731).length < 2 ^ (prefixWord ++ tailWord_1226731).sum := by decide
  have hdescent : baseEnd_1226731 < baseStart_1226731 := by decide
  rcases family_descends (prefixWord ++ tailWord_1226731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1226781 : List Nat := [1, 4, 2, 2, 2, 1, 1, 4, 2, 4]
def baseStart_1226781 : Nat := 118140960795 + 1226781 * 2 ^ 59
def prefixEnd_1226781 : Nat := 4983230072969 + 3 ^ 40 * 1226781 * 2
def baseEnd_1226781 : Nat := 209976103601156649131881

theorem tailTrace_1226781 : CollatzResearch.WordTrace tailWord_1226781 prefixEnd_1226781 209976103601156649131881 := by
  unfold tailWord_1226781
  simp only [CollatzResearch.WordTrace]
  refine ⟨44744378968589429359368197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29829585979059619572912131 44744378968589429359368197)
  ·
    refine ⟨8389571056610518004881537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44744378968589429359368197 8389571056610518004881537)
    ·
      refine ⟨6292178292457888503661153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8389571056610518004881537 6292178292457888503661153)
      ·
        refine ⟨4719133719343416377745865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6292178292457888503661153 4719133719343416377745865)
        ·
          refine ⟨3539350289507562283309399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4719133719343416377745865 3539350289507562283309399)
          ·
            refine ⟨5309025434261343424964099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3539350289507562283309399 5309025434261343424964099)
            ·
              refine ⟨7963538151392015137446149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5309025434261343424964099 7963538151392015137446149)
              ·
                refine ⟨1493163403386002838271153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7963538151392015137446149 1493163403386002838271153)
                ·
                  refine ⟨1119872552539502128703365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1493163403386002838271153 1119872552539502128703365)
                  ·
                    refine ⟨209976103601156649131881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1119872552539502128703365 209976103601156649131881)
                    ·
                      rfl

theorem cell23_1226781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 4, 2, 4].length) (baseStart_1226781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1226781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1226781 prefixEnd_1226781 := by exact prefixLift 1226781
  have htrace : WordTrace (prefixWord ++ tailWord_1226781) baseStart_1226781 baseEnd_1226781 := by
    simpa [prefixWord, tailWord_1226781, baseEnd_1226781] using wordTrace_append hprefix tailTrace_1226781
  have hstable : (prefixWord ++ tailWord_1226781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1226781).length < 2 ^ (prefixWord ++ tailWord_1226781).sum := by decide
  have hdescent : baseEnd_1226781 < baseStart_1226781 := by decide
  rcases family_descends (prefixWord ++ tailWord_1226781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1226794 : List Nat := [3, 1, 4, 1, 2, 1, 3, 8]
def baseStart_1226794 : Nat := 118140960795 + 1226794 * 2 ^ 59
def prefixEnd_1226794 : Nat := 4983230072969 + 3 ^ 40 * 1226794 * 2
def baseEnd_1226794 : Nat := 23330925409332533204929

theorem tailTrace_1226794 : CollatzResearch.WordTrace tailWord_1226794 prefixEnd_1226794 23330925409332533204929 := by
  unfold tailWord_1226794
  simp only [CollatzResearch.WordTrace]
  refine ⟨11186213279385583144897859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29829902078361555053060957 11186213279385583144897859)
  ·
    refine ⟨16779319919078374717346789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11186213279385583144897859 16779319919078374717346789)
    ·
      refine ⟨3146122484827195259502523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16779319919078374717346789 3146122484827195259502523)
      ·
        refine ⟨4719183727240792889253785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3146122484827195259502523 4719183727240792889253785)
        ·
          refine ⟨3539387795430594666940339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4719183727240792889253785 3539387795430594666940339)
          ·
            refine ⟨5309081693145892000410509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3539387795430594666940339 5309081693145892000410509)
            ·
              refine ⟨1990905634929709500153941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5309081693145892000410509 1990905634929709500153941)
              ·
                refine ⟨23330925409332533204929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1990905634929709500153941 23330925409332533204929)
                ·
                  rfl

theorem cell23_1226794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 3, 8].length) (baseStart_1226794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1226794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1226794 prefixEnd_1226794 := by exact prefixLift 1226794
  have htrace : WordTrace (prefixWord ++ tailWord_1226794) baseStart_1226794 baseEnd_1226794 := by
    simpa [prefixWord, tailWord_1226794, baseEnd_1226794] using wordTrace_append hprefix tailTrace_1226794
  have hstable : (prefixWord ++ tailWord_1226794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1226794).length < 2 ^ (prefixWord ++ tailWord_1226794).sum := by decide
  have hdescent : baseEnd_1226794 < baseStart_1226794 := by decide
  rcases family_descends (prefixWord ++ tailWord_1226794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1226827 : List Nat := [1, 1, 1, 1, 3, 1, 2, 2, 4, 3, 4]
def baseStart_1226827 : Nat := 118140960795 + 1226827 * 2 ^ 59
def prefixEnd_1226827 : Nat := 4983230072969 + 3 ^ 40 * 1226827 * 2
def baseEnd_1226827 : Nat := 629951930913576767420431

theorem tailTrace_1226827 : CollatzResearch.WordTrace tailWord_1226827 prefixEnd_1226827 629951930913576767420431 := by
  unfold tailWord_1226827
  simp only [CollatzResearch.WordTrace]
  refine ⟨44746056726422779215542735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29830704484281852810361823 44746056726422779215542735)
  ·
    refine ⟨67119085089634168823314103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44746056726422779215542735 67119085089634168823314103)
    ·
      refine ⟨100678627634451253234971155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67119085089634168823314103 100678627634451253234971155)
      ·
        refine ⟨151017941451676879852456733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100678627634451253234971155 151017941451676879852456733)
        ·
          refine ⟨56631728044378829944671275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 151017941451676879852456733 56631728044378829944671275)
          ·
            refine ⟨84947592066568244917006913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56631728044378829944671275 84947592066568244917006913)
            ·
              refine ⟨63710694049926183687755185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84947592066568244917006913 63710694049926183687755185)
              ·
                refine ⟨47783020537444637765816389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63710694049926183687755185 47783020537444637765816389)
                ·
                  refine ⟨8959316350770869581090573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47783020537444637765816389 8959316350770869581090573)
                  ·
                    refine ⟨3359743631539076092908965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8959316350770869581090573 3359743631539076092908965)
                    ·
                      refine ⟨629951930913576767420431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3359743631539076092908965 629951930913576767420431)
                      ·
                        rfl

theorem cell23_1226827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 4, 3, 4].length) (baseStart_1226827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1226827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1226827 prefixEnd_1226827 := by exact prefixLift 1226827
  have htrace : WordTrace (prefixWord ++ tailWord_1226827) baseStart_1226827 baseEnd_1226827 := by
    simpa [prefixWord, tailWord_1226827, baseEnd_1226827] using wordTrace_append hprefix tailTrace_1226827
  have hstable : (prefixWord ++ tailWord_1226827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1226827).length < 2 ^ (prefixWord ++ tailWord_1226827).sum := by decide
  have hdescent : baseEnd_1226827 < baseStart_1226827 := by decide
  rcases family_descends (prefixWord ++ tailWord_1226827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1226831 : List Nat := [1, 1, 2, 1, 1, 2, 2, 7, 1, 3, 2]
def baseStart_1226831 : Nat := 118140960795 + 1226831 * 2 ^ 59
def prefixEnd_1226831 : Nat := 4983230072969 + 3 ^ 40 * 1226831 * 2
def baseEnd_1226831 : Nat := 629953984836194751770413

theorem tailTrace_1226831 : CollatzResearch.WordTrace tailWord_1226831 prefixEnd_1226831 629953984836194751770413 := by
  unfold tailWord_1226831
  simp only [CollatzResearch.WordTrace]
  refine ⟨44746202618408287898688347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29830801745605525265792231 44746202618408287898688347)
  ·
    refine ⟨67119303927612431848032521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44746202618408287898688347 67119303927612431848032521)
    ·
      refine ⟨50339477945709323886024391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67119303927612431848032521 50339477945709323886024391)
      ·
        refine ⟨75509216918563985829036587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50339477945709323886024391 75509216918563985829036587)
        ·
          refine ⟨113263825377845978743554881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75509216918563985829036587 113263825377845978743554881)
          ·
            refine ⟨84947869033384484057666161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113263825377845978743554881 84947869033384484057666161)
            ·
              refine ⟨63710901775038363043249621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84947869033384484057666161 63710901775038363043249621)
              ·
                refine ⟨1493224260352461633826163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 63710901775038363043249621 1493224260352461633826163)
                ·
                  refine ⟨2239836390528692450739245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1493224260352461633826163 2239836390528692450739245)
                  ·
                    refine ⟨839938646448259669027217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2239836390528692450739245 839938646448259669027217)
                    ·
                      refine ⟨629953984836194751770413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 839938646448259669027217 629953984836194751770413)
                      ·
                        rfl

theorem cell23_1226831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 7, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 7, 1, 3, 2].length) (baseStart_1226831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1226831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1226831 prefixEnd_1226831 := by exact prefixLift 1226831
  have htrace : WordTrace (prefixWord ++ tailWord_1226831) baseStart_1226831 baseEnd_1226831 := by
    simpa [prefixWord, tailWord_1226831, baseEnd_1226831] using wordTrace_append hprefix tailTrace_1226831
  have hstable : (prefixWord ++ tailWord_1226831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1226831).length < 2 ^ (prefixWord ++ tailWord_1226831).sum := by decide
  have hdescent : baseEnd_1226831 < baseStart_1226831 := by decide
  rcases family_descends (prefixWord ++ tailWord_1226831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1226847 : List Nat := [1, 1, 2, 3, 1, 1, 2, 1, 3, 3, 5]
def baseStart_1226847 : Nat := 118140960795 + 1226847 * 2 ^ 59
def prefixEnd_1226847 : Nat := 4983230072969 + 3 ^ 40 * 1226847 * 2
def baseEnd_1226847 : Nat := 629962200526666689170339

theorem tailTrace_1226847 : CollatzResearch.WordTrace tailWord_1226847 prefixEnd_1226847 629962200526666689170339 := by
  unfold tailWord_1226847
  simp only [CollatzResearch.WordTrace]
  refine ⟨44746786186350322631270795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29831190790900215087513863 44746786186350322631270795)
  ·
    refine ⟨67120179279525483946906193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44746786186350322631270795 67120179279525483946906193)
    ·
      refine ⟨50340134459644112960179645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67120179279525483946906193 50340134459644112960179645)
      ·
        refine ⟨18877550422366542360067367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50340134459644112960179645 18877550422366542360067367)
        ·
          refine ⟨28316325633549813540101051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18877550422366542360067367 28316325633549813540101051)
          ·
            refine ⟨42474488450324720310151577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28316325633549813540101051 42474488450324720310151577)
            ·
              refine ⟨31855866337743540232613683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42474488450324720310151577 31855866337743540232613683)
              ·
                refine ⟨47783799506615310348920525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31855866337743540232613683 47783799506615310348920525)
                ·
                  refine ⟨17918924814980741380845197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47783799506615310348920525 17918924814980741380845197)
                  ·
                    refine ⟨6719596805617778017816949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17918924814980741380845197 6719596805617778017816949)
                    ·
                      refine ⟨629962200526666689170339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6719596805617778017816949 629962200526666689170339)
                      ·
                        rfl

theorem cell23_1226847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 3, 3, 5].length) (baseStart_1226847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1226847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1226847 prefixEnd_1226847 := by exact prefixLift 1226847
  have htrace : WordTrace (prefixWord ++ tailWord_1226847) baseStart_1226847 baseEnd_1226847 := by
    simpa [prefixWord, tailWord_1226847, baseEnd_1226847] using wordTrace_append hprefix tailTrace_1226847
  have hstable : (prefixWord ++ tailWord_1226847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1226847).length < 2 ^ (prefixWord ++ tailWord_1226847).sum := by decide
  have hdescent : baseEnd_1226847 < baseStart_1226847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1226847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1226881 : List Nat := [1, 2, 4, 2, 3, 1, 1, 1, 2, 1, 5]
def baseStart_1226881 : Nat := 118140960795 + 1226881 * 2 ^ 59
def prefixEnd_1226881 : Nat := 4983230072969 + 3 ^ 40 * 1226881 * 2
def baseEnd_1226881 : Nat := 629979658868919556145183

theorem tailTrace_1226881 : CollatzResearch.WordTrace tailWord_1226881 prefixEnd_1226881 629979658868919556145183 := by
  unfold tailWord_1226881
  simp only [CollatzResearch.WordTrace]
  refine ⟨44748026268227146438008497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29832017512151430958672331 44748026268227146438008497)
  ·
    refine ⟨33561019701170359828506373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44748026268227146438008497 33561019701170359828506373)
    ·
      refine ⟨6292691193969442467844945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33561019701170359828506373 6292691193969442467844945)
      ·
        refine ⟨4719518395477081850883709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6292691193969442467844945 4719518395477081850883709)
        ·
          refine ⟨1769819398303905694081391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4719518395477081850883709 1769819398303905694081391)
          ·
            refine ⟨2654729097455858541122087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1769819398303905694081391 2654729097455858541122087)
            ·
              refine ⟨3982093646183787811683131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2654729097455858541122087 3982093646183787811683131)
              ·
                refine ⟨5973140469275681717524697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3982093646183787811683131 5973140469275681717524697)
                ·
                  refine ⟨4479855351956761288143523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5973140469275681717524697 4479855351956761288143523)
                  ·
                    refine ⟨6719783027935141932215285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4479855351956761288143523 6719783027935141932215285)
                    ·
                      refine ⟨629979658868919556145183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6719783027935141932215285 629979658868919556145183)
                      ·
                        rfl

theorem cell23_1226881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 1, 2, 1, 5].length) (baseStart_1226881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1226881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1226881 prefixEnd_1226881 := by exact prefixLift 1226881
  have htrace : WordTrace (prefixWord ++ tailWord_1226881) baseStart_1226881 baseEnd_1226881 := by
    simpa [prefixWord, tailWord_1226881, baseEnd_1226881] using wordTrace_append hprefix tailTrace_1226881
  have hstable : (prefixWord ++ tailWord_1226881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1226881).length < 2 ^ (prefixWord ++ tailWord_1226881).sum := by decide
  have hdescent : baseEnd_1226881 < baseStart_1226881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1226881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1226897 : List Nat := [1, 2, 2, 1, 1, 1, 1, 1, 2, 11]
def baseStart_1226897 : Nat := 118140960795 + 1226897 * 2 ^ 59
def prefixEnd_1226897 : Nat := 4983230072969 + 3 ^ 40 * 1226897 * 2
def baseEnd_1226897 : Nat := 209995958186463831181703

theorem tailTrace_1226897 : CollatzResearch.WordTrace tailWord_1226897 prefixEnd_1226897 209995958186463831181703 := by
  unfold tailWord_1226897
  simp only [CollatzResearch.WordTrace]
  refine ⟨44748609836169181170590945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29832406557446120780393963 44748609836169181170590945)
  ·
    refine ⟨33561457377126885877943209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44748609836169181170590945 33561457377126885877943209)
    ·
      refine ⟨25171093032845164408457407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33561457377126885877943209 25171093032845164408457407)
      ·
        refine ⟨37756639549267746612686111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25171093032845164408457407 37756639549267746612686111)
        ·
          refine ⟨56634959323901619919029167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37756639549267746612686111 56634959323901619919029167)
          ·
            refine ⟨84952438985852429878543751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56634959323901619919029167 84952438985852429878543751)
            ·
              refine ⟨127428658478778644817815627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84952438985852429878543751 127428658478778644817815627)
              ·
                refine ⟨191142987718167967226723441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 127428658478778644817815627 191142987718167967226723441)
                ·
                  refine ⟨143357240788625975420042581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 191142987718167967226723441 143357240788625975420042581)
                  ·
                    refine ⟨209995958186463831181703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 143357240788625975420042581 209995958186463831181703)
                    ·
                      rfl

theorem cell23_1226897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 11].length) (baseStart_1226897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1226897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1226897 prefixEnd_1226897 := by exact prefixLift 1226897
  have htrace : WordTrace (prefixWord ++ tailWord_1226897) baseStart_1226897 baseEnd_1226897 := by
    simpa [prefixWord, tailWord_1226897, baseEnd_1226897] using wordTrace_append hprefix tailTrace_1226897
  have hstable : (prefixWord ++ tailWord_1226897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1226897).length < 2 ^ (prefixWord ++ tailWord_1226897).sum := by decide
  have hdescent : baseEnd_1226897 < baseStart_1226897 := by decide
  rcases family_descends (prefixWord ++ tailWord_1226897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1226912 : List Nat := [2, 1, 1, 4, 2, 4, 2, 1, 2, 2, 2]
def baseStart_1226912 : Nat := 118140960795 + 1226912 * 2 ^ 59
def prefixEnd_1226912 : Nat := 4983230072969 + 3 ^ 40 * 1226912 * 2
def baseEnd_1226912 : Nat := 629995576769208934857541

theorem tailTrace_1226912 : CollatzResearch.WordTrace tailWord_1226912 prefixEnd_1226912 629995576769208934857541 := by
  unfold tailWord_1226912
  simp only [CollatzResearch.WordTrace]
  refine ⟨22374578465557419366193495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29832771287409892488257993 22374578465557419366193495)
  ·
    refine ⟨33561867698336129049290243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22374578465557419366193495 33561867698336129049290243)
    ·
      refine ⟨50342801547504193573935365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33561867698336129049290243 50342801547504193573935365)
      ·
        refine ⟨9439275290157036295112881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50342801547504193573935365 9439275290157036295112881)
        ·
          refine ⟨7079456467617777221334661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9439275290157036295112881 7079456467617777221334661)
          ·
            refine ⟨1327398087678333229000249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7079456467617777221334661 1327398087678333229000249)
            ·
              refine ⟨995548565758749921750187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1327398087678333229000249 995548565758749921750187)
              ·
                refine ⟨1493322848638124882625281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 995548565758749921750187 1493322848638124882625281)
                ·
                  refine ⟨1119992136478593661968961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1493322848638124882625281 1119992136478593661968961)
                  ·
                    refine ⟨839994102358945246476721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1119992136478593661968961 839994102358945246476721)
                    ·
                      refine ⟨629995576769208934857541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 839994102358945246476721 629995576769208934857541)
                      ·
                        rfl

theorem cell23_1226912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 2, 1, 2, 2, 2].length) (baseStart_1226912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1226912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1226912 prefixEnd_1226912 := by exact prefixLift 1226912
  have htrace : WordTrace (prefixWord ++ tailWord_1226912) baseStart_1226912 baseEnd_1226912 := by
    simpa [prefixWord, tailWord_1226912, baseEnd_1226912] using wordTrace_append hprefix tailTrace_1226912
  have hstable : (prefixWord ++ tailWord_1226912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1226912).length < 2 ^ (prefixWord ++ tailWord_1226912).sum := by decide
  have hdescent : baseEnd_1226912 < baseStart_1226912 := by decide
  rcases family_descends (prefixWord ++ tailWord_1226912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1226954 : List Nat := [3, 1, 2, 1, 3, 1, 1, 1, 2, 3, 5]
def baseStart_1226954 : Nat := 118140960795 + 1226954 * 2 ^ 59
def prefixEnd_1226954 : Nat := 4983230072969 + 3 ^ 40 * 1226954 * 2
def baseEnd_1226954 : Nat := 630017142956697770532347

theorem tailTrace_1226954 : CollatzResearch.WordTrace tailWord_1226954 prefixEnd_1226954 630017142956697770532347 := by
  unfold tailWord_1226954
  simp only [CollatzResearch.WordTrace]
  refine ⟨11187672199240669976353979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29833792531308453270277277 11187672199240669976353979)
  ·
    refine ⟨16781508298861004964530969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11187672199240669976353979 16781508298861004964530969)
    ·
      refine ⟨12586131224145753723398227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16781508298861004964530969 12586131224145753723398227)
      ·
        refine ⟨18879196836218630585097341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12586131224145753723398227 18879196836218630585097341)
        ·
          refine ⟨7079698813581986469411503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18879196836218630585097341 7079698813581986469411503)
          ·
            refine ⟨10619548220372979704117255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7079698813581986469411503 10619548220372979704117255)
            ·
              refine ⟨15929322330559469556175883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10619548220372979704117255 15929322330559469556175883)
              ·
                refine ⟨23893983495839204334263825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15929322330559469556175883 23893983495839204334263825)
                ·
                  refine ⟨17920487621879403250697869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23893983495839204334263825 17920487621879403250697869)
                  ·
                    refine ⟨6720182858204776219011701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17920487621879403250697869 6720182858204776219011701)
                    ·
                      refine ⟨630017142956697770532347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6720182858204776219011701 630017142956697770532347)
                      ·
                        rfl

theorem cell23_1226954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 1, 2, 3, 5].length) (baseStart_1226954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1226954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1226954 prefixEnd_1226954 := by exact prefixLift 1226954
  have htrace : WordTrace (prefixWord ++ tailWord_1226954) baseStart_1226954 baseEnd_1226954 := by
    simpa [prefixWord, tailWord_1226954, baseEnd_1226954] using wordTrace_append hprefix tailTrace_1226954
  have hstable : (prefixWord ++ tailWord_1226954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1226954).length < 2 ^ (prefixWord ++ tailWord_1226954).sum := by decide
  have hdescent : baseEnd_1226954 < baseStart_1226954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1226954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1226968 : List Nat := [2, 1, 2, 2, 4, 2, 1, 1, 2, 4, 2]
def baseStart_1226968 : Nat := 118140960795 + 1226968 * 2 ^ 59
def prefixEnd_1226968 : Nat := 4983230072969 + 3 ^ 40 * 1226968 * 2
def baseEnd_1226968 : Nat := 630024331685860715757283

theorem tailTrace_1226968 : CollatzResearch.WordTrace tailWord_1226968 prefixEnd_1226968 630024331685860715757283 := by
  unfold tailWord_1226968
  simp only [CollatzResearch.WordTrace]
  refine ⟨22375599709455980148212779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29834132945941306864283705 22375599709455980148212779)
  ·
    refine ⟨33563399564183970222319169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22375599709455980148212779 33563399564183970222319169)
    ·
      refine ⟨25172549673137977666739377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33563399564183970222319169 25172549673137977666739377)
      ·
        refine ⟨18879412254853483250054533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25172549673137977666739377 18879412254853483250054533)
        ·
          refine ⟨3539889797785028109385225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18879412254853483250054533 3539889797785028109385225)
          ·
            refine ⟨2654917348338771082038919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3539889797785028109385225 2654917348338771082038919)
            ·
              refine ⟨3982376022508156623058379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2654917348338771082038919 3982376022508156623058379)
              ·
                refine ⟨5973564033762234934587569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3982376022508156623058379 5973564033762234934587569)
                ·
                  refine ⟨4480173025321676200940677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5973564033762234934587569 4480173025321676200940677)
                  ·
                    refine ⟨840032442247814287676377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4480173025321676200940677 840032442247814287676377)
                    ·
                      refine ⟨630024331685860715757283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 840032442247814287676377 630024331685860715757283)
                      ·
                        rfl

theorem cell23_1226968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 1, 2, 4, 2].length) (baseStart_1226968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1226968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1226968 prefixEnd_1226968 := by exact prefixLift 1226968
  have htrace : WordTrace (prefixWord ++ tailWord_1226968) baseStart_1226968 baseEnd_1226968 := by
    simpa [prefixWord, tailWord_1226968, baseEnd_1226968] using wordTrace_append hprefix tailTrace_1226968
  have hstable : (prefixWord ++ tailWord_1226968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1226968).length < 2 ^ (prefixWord ++ tailWord_1226968).sum := by decide
  have hdescent : baseEnd_1226968 < baseStart_1226968 := by decide
  rcases family_descends (prefixWord ++ tailWord_1226968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1227018 : List Nat := [3, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3]
def baseStart_1227018 : Nat := 118140960795 + 1227018 * 2 ^ 59
def prefixEnd_1227018 : Nat := 4983230072969 + 3 ^ 40 * 1227018 * 2
def baseEnd_1227018 : Nat := 630050005718585520132053

theorem tailTrace_1227018 : CollatzResearch.WordTrace tailWord_1227018 prefixEnd_1227018 630050005718585520132053 := by
  unfold tailWord_1227018
  simp only [CollatzResearch.WordTrace]
  refine ⟨11188255767182704708936427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29835348712487212557163805 11188255767182704708936427)
  ·
    refine ⟨16782383650774057063404641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11188255767182704708936427 16782383650774057063404641)
    ·
      refine ⟨12586787738080542797553481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16782383650774057063404641 12586787738080542797553481)
      ·
        refine ⟨9440090803560407098165111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12586787738080542797553481 9440090803560407098165111)
        ·
          refine ⟨14160136205340610647247667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9440090803560407098165111 14160136205340610647247667)
          ·
            refine ⟨21240204308010915970871501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14160136205340610647247667 21240204308010915970871501)
            ·
              refine ⟨7965076615504093489076813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21240204308010915970871501 7965076615504093489076813)
              ·
                refine ⟨2986903730814035058403805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7965076615504093489076813 2986903730814035058403805)
                ·
                  refine ⟨1120088899055263146901427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2986903730814035058403805 1120088899055263146901427)
                  ·
                    refine ⟨1680133348582894720352141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1120088899055263146901427 1680133348582894720352141)
                    ·
                      refine ⟨630050005718585520132053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1680133348582894720352141 630050005718585520132053)
                      ·
                        rfl

theorem cell23_1227018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3].length) (baseStart_1227018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1227018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1227018 prefixEnd_1227018 := by exact prefixLift 1227018
  have htrace : WordTrace (prefixWord ++ tailWord_1227018) baseStart_1227018 baseEnd_1227018 := by
    simpa [prefixWord, tailWord_1227018, baseEnd_1227018] using wordTrace_append hprefix tailTrace_1227018
  have hstable : (prefixWord ++ tailWord_1227018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1227018).length < 2 ^ (prefixWord ++ tailWord_1227018).sum := by decide
  have hdescent : baseEnd_1227018 < baseStart_1227018 := by decide
  rcases family_descends (prefixWord ++ tailWord_1227018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1227041 : List Nat := [1, 2, 3, 2, 1, 1, 2, 3, 3, 1, 4]
def baseStart_1227041 : Nat := 118140960795 + 1227041 * 2 ^ 59
def prefixEnd_1227041 : Nat := 4983230072969 + 3 ^ 40 * 1227041 * 2
def baseEnd_1227041 : Nat := 630061815773638930144447

theorem tailTrace_1227041 : CollatzResearch.WordTrace tailWord_1227041 prefixEnd_1227041 630061815773638930144447 := by
  unfold tailWord_1227041
  simp only [CollatzResearch.WordTrace]
  refine ⟨44753861947647493763832977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29835907965098329175888651 44753861947647493763832977)
  ·
    refine ⟨33565396460735620322874733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44753861947647493763832977 33565396460735620322874733)
    ·
      refine ⟨12587023672775857621078025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33565396460735620322874733 12587023672775857621078025)
      ·
        refine ⟨9440267754581893215808519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12587023672775857621078025 9440267754581893215808519)
        ·
          refine ⟨14160401631872839823712779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9440267754581893215808519 14160401631872839823712779)
          ·
            refine ⟨21240602447809259735569169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14160401631872839823712779 21240602447809259735569169)
            ·
              refine ⟨15930451835856944801676877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21240602447809259735569169 15930451835856944801676877)
              ·
                refine ⟨5973919438446354300628829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15930451835856944801676877 5973919438446354300628829)
                ·
                  refine ⟨2240219789417382862735811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5973919438446354300628829 2240219789417382862735811)
                  ·
                    refine ⟨3360329684126074294103717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2240219789417382862735811 3360329684126074294103717)
                    ·
                      refine ⟨630061815773638930144447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3360329684126074294103717 630061815773638930144447)
                      ·
                        rfl

theorem cell23_1227041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 3, 3, 1, 4].length) (baseStart_1227041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1227041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1227041 prefixEnd_1227041 := by exact prefixLift 1227041
  have htrace : WordTrace (prefixWord ++ tailWord_1227041) baseStart_1227041 baseEnd_1227041 := by
    simpa [prefixWord, tailWord_1227041, baseEnd_1227041] using wordTrace_append hprefix tailTrace_1227041
  have hstable : (prefixWord ++ tailWord_1227041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1227041).length < 2 ^ (prefixWord ++ tailWord_1227041).sum := by decide
  have hdescent : baseEnd_1227041 < baseStart_1227041 := by decide
  rcases family_descends (prefixWord ++ tailWord_1227041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1227064 : List Nat := [2, 1, 2, 1, 3, 1, 13]
def baseStart_1227064 : Nat := 118140960795 + 1227064 * 2 ^ 59
def prefixEnd_1227064 : Nat := 4983230072969 + 3 ^ 40 * 1227064 * 2
def baseEnd_1227064 : Nat := 7778686738625831359961

theorem tailTrace_1227064 : CollatzResearch.WordTrace tailWord_1227064 prefixEnd_1227064 7778686738625831359961 := by
  unfold tailWord_1227064
  simp only [CollatzResearch.WordTrace]
  refine ⟨22377350413282084345960123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29836467217709445794613497 22377350413282084345960123)
  ·
    refine ⟨33566025619923126518940185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22377350413282084345960123 33566025619923126518940185)
    ·
      refine ⟨25174519214942344889205139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33566025619923126518940185 25174519214942344889205139)
      ·
        refine ⟨37761778822413517333807709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25174519214942344889205139 37761778822413517333807709)
        ·
          refine ⟨14160667058405069000177891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37761778822413517333807709 14160667058405069000177891)
          ·
            refine ⟨21241000587607603500266837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14160667058405069000177891 21241000587607603500266837)
            ·
              refine ⟨7778686738625831359961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 21241000587607603500266837 7778686738625831359961)
              ·
                rfl

theorem cell23_1227064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 13].length) (baseStart_1227064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1227064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1227064 prefixEnd_1227064 := by exact prefixLift 1227064
  have htrace : WordTrace (prefixWord ++ tailWord_1227064) baseStart_1227064 baseEnd_1227064 := by
    simpa [prefixWord, tailWord_1227064, baseEnd_1227064] using wordTrace_append hprefix tailTrace_1227064
  have hstable : (prefixWord ++ tailWord_1227064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1227064).length < 2 ^ (prefixWord ++ tailWord_1227064).sum := by decide
  have hdescent : baseEnd_1227064 < baseStart_1227064 := by decide
  rcases family_descends (prefixWord ++ tailWord_1227064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1227068 : List Nat := [2, 2, 2, 2, 1, 2, 2, 4, 2, 4]
def baseStart_1227068 : Nat := 118140960795 + 1227068 * 2 ^ 59
def prefixEnd_1227068 : Nat := 4983230072969 + 3 ^ 40 * 1227068 * 2
def baseEnd_1227068 : Nat := 210025226583770108168941

theorem tailTrace_1227068 : CollatzResearch.WordTrace tailWord_1227068 prefixEnd_1227068 210025226583770108168941 := by
  unfold tailWord_1227068
  simp only [CollatzResearch.WordTrace]
  refine ⟨22377423359274838687532929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29836564479033118250043905 22377423359274838687532929)
  ·
    refine ⟨16783067519456129015649697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22377423359274838687532929 16783067519456129015649697)
    ·
      refine ⟨12587300639592096761737273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16783067519456129015649697 12587300639592096761737273)
      ·
        refine ⟨9440475479694072571302955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12587300639592096761737273 9440475479694072571302955)
        ·
          refine ⟨14160713219541108856954433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9440475479694072571302955 14160713219541108856954433)
          ·
            refine ⟨10620534914655831642715825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14160713219541108856954433 10620534914655831642715825)
            ·
              refine ⟨7965401185991873732036869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10620534914655831642715825 7965401185991873732036869)
              ·
                refine ⟨1493512722373476324756913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7965401185991873732036869 1493512722373476324756913)
                ·
                  refine ⟨1120134541780107243567685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1493512722373476324756913 1120134541780107243567685)
                  ·
                    refine ⟨210025226583770108168941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1120134541780107243567685 210025226583770108168941)
                    ·
                      rfl

theorem cell23_1227068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 4, 2, 4].length) (baseStart_1227068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1227068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1227068 prefixEnd_1227068 := by exact prefixLift 1227068
  have htrace : WordTrace (prefixWord ++ tailWord_1227068) baseStart_1227068 baseEnd_1227068 := by
    simpa [prefixWord, tailWord_1227068, baseEnd_1227068] using wordTrace_append hprefix tailTrace_1227068
  have hstable : (prefixWord ++ tailWord_1227068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1227068).length < 2 ^ (prefixWord ++ tailWord_1227068).sum := by decide
  have hdescent : baseEnd_1227068 < baseStart_1227068 := by decide
  rcases family_descends (prefixWord ++ tailWord_1227068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1227075 : List Nat := [1, 1, 1, 3, 1, 3, 5, 1, 3, 2, 2]
def baseStart_1227075 : Nat := 118140960795 + 1227075 * 2 ^ 59
def prefixEnd_1227075 : Nat := 4983230072969 + 3 ^ 40 * 1227075 * 2
def baseEnd_1227075 : Nat := 630079274115891797119291

theorem tailTrace_1227075 : CollatzResearch.WordTrace tailWord_1227075 prefixEnd_1227075 630079274115891797119291 := by
  unfold tailWord_1227075
  simp only [CollatzResearch.WordTrace]
  refine ⟨44755102029524317570570679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29836734686349545047047119 44755102029524317570570679)
  ·
    refine ⟨67132653044286476355856019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44755102029524317570570679 67132653044286476355856019)
    ·
      refine ⟨100698979566429714533784029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67132653044286476355856019 100698979566429714533784029)
      ·
        refine ⟨37762117337411142950169011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100698979566429714533784029 37762117337411142950169011)
        ·
          refine ⟨56643176006116714425253517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37762117337411142950169011 56643176006116714425253517)
          ·
            refine ⟨21241191002293767909470069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56643176006116714425253517 21241191002293767909470069)
            ·
              refine ⟨1991361656465040741512819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21241191002293767909470069 1991361656465040741512819)
              ·
                refine ⟨2987042484697561112269229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1991361656465040741512819 2987042484697561112269229)
                ·
                  refine ⟨1120140931761585417100961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2987042484697561112269229 1120140931761585417100961)
                  ·
                    refine ⟨840105698821189062825721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1120140931761585417100961 840105698821189062825721)
                    ·
                      refine ⟨630079274115891797119291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 840105698821189062825721 630079274115891797119291)
                      ·
                        rfl

theorem cell23_1227075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 5, 1, 3, 2, 2].length) (baseStart_1227075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1227075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1227075 prefixEnd_1227075 := by exact prefixLift 1227075
  have htrace : WordTrace (prefixWord ++ tailWord_1227075) baseStart_1227075 baseEnd_1227075 := by
    simpa [prefixWord, tailWord_1227075, baseEnd_1227075] using wordTrace_append hprefix tailTrace_1227075
  have hstable : (prefixWord ++ tailWord_1227075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1227075).length < 2 ^ (prefixWord ++ tailWord_1227075).sum := by decide
  have hdescent : baseEnd_1227075 < baseStart_1227075 := by decide
  rcases family_descends (prefixWord ++ tailWord_1227075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1227108 : List Nat := [2, 3, 1, 1, 3, 1, 3, 2, 1, 3, 3]
def baseStart_1227108 : Nat := 118140960795 + 1227108 * 2 ^ 59
def prefixEnd_1227108 : Nat := 4983230072969 + 3 ^ 40 * 1227108 * 2
def baseEnd_1227108 : Nat := 630096218977490168006639

theorem tailTrace_1227108 : CollatzResearch.WordTrace tailWord_1227108 prefixEnd_1227108 630096218977490168006639 := by
  unfold tailWord_1227108
  simp only [CollatzResearch.WordTrace]
  refine ⟨22378152819202382103260989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29837537092269842804347985 22378152819202382103260989)
  ·
    refine ⟨8391807307200893288722871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22378152819202382103260989 8391807307200893288722871)
    ·
      refine ⟨12587710960801339933084307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8391807307200893288722871 12587710960801339933084307)
      ·
        refine ⟨18881566441202009899626461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12587710960801339933084307 18881566441202009899626461)
        ·
          refine ⟨7080587415450753712359923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18881566441202009899626461 7080587415450753712359923)
          ·
            refine ⟨10620881123176130568539885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7080587415450753712359923 10620881123176130568539885)
            ·
              refine ⟨3982830421191048963202457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10620881123176130568539885 3982830421191048963202457)
              ·
                refine ⟨2987122815893286722401843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3982830421191048963202457 2987122815893286722401843)
                ·
                  refine ⟨4480684223839930083602765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2987122815893286722401843 4480684223839930083602765)
                  ·
                    refine ⟨1680256583939973781351037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4480684223839930083602765 1680256583939973781351037)
                    ·
                      refine ⟨630096218977490168006639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1680256583939973781351037 630096218977490168006639)
                      ·
                        rfl

theorem cell23_1227108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 2, 1, 3, 3].length) (baseStart_1227108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1227108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1227108 prefixEnd_1227108 := by exact prefixLift 1227108
  have htrace : WordTrace (prefixWord ++ tailWord_1227108) baseStart_1227108 baseEnd_1227108 := by
    simpa [prefixWord, tailWord_1227108, baseEnd_1227108] using wordTrace_append hprefix tailTrace_1227108
  have hstable : (prefixWord ++ tailWord_1227108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1227108).length < 2 ^ (prefixWord ++ tailWord_1227108).sum := by decide
  have hdescent : baseEnd_1227108 < baseStart_1227108 := by decide
  rcases family_descends (prefixWord ++ tailWord_1227108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1227112 : List Nat := [2, 1, 4, 2, 2, 2, 3, 1, 1, 2, 3]
def baseStart_1227112 : Nat := 118140960795 + 1227112 * 2 ^ 59
def prefixEnd_1227112 : Nat := 4983230072969 + 3 ^ 40 * 1227112 * 2
def baseEnd_1227112 : Nat := 630098272900108152356621

theorem tailTrace_1227112 : CollatzResearch.WordTrace tailWord_1227112 prefixEnd_1227112 630098272900108152356621 := by
  unfold tailWord_1227112
  simp only [CollatzResearch.WordTrace]
  refine ⟨22378225765195136444833795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29837634353593515259778393 22378225765195136444833795)
  ·
    refine ⟨33567338647792704667250693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22378225765195136444833795 33567338647792704667250693)
    ·
      refine ⟨6293875996461132125109505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33567338647792704667250693 6293875996461132125109505)
      ·
        refine ⟨4720406997345849093832129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6293875996461132125109505 4720406997345849093832129)
        ·
          refine ⟨3540305248009386820374097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4720406997345849093832129 3540305248009386820374097)
          ·
            refine ⟨2655228936007040115280573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3540305248009386820374097 2655228936007040115280573)
            ·
              refine ⟨995710851002640043230215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2655228936007040115280573 995710851002640043230215)
              ·
                refine ⟨1493566276503960064845323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 995710851002640043230215 1493566276503960064845323)
                ·
                  refine ⟨2240349414755940097267985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1493566276503960064845323 2240349414755940097267985)
                  ·
                    refine ⟨1680262061066955072950989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2240349414755940097267985 1680262061066955072950989)
                    ·
                      refine ⟨630098272900108152356621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1680262061066955072950989 630098272900108152356621)
                      ·
                        rfl

theorem cell23_1227112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 3, 1, 1, 2, 3].length) (baseStart_1227112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1227112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1227112 prefixEnd_1227112 := by exact prefixLift 1227112
  have htrace : WordTrace (prefixWord ++ tailWord_1227112) baseStart_1227112 baseEnd_1227112 := by
    simpa [prefixWord, tailWord_1227112, baseEnd_1227112] using wordTrace_append hprefix tailTrace_1227112
  have hstable : (prefixWord ++ tailWord_1227112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1227112).length < 2 ^ (prefixWord ++ tailWord_1227112).sum := by decide
  have hdescent : baseEnd_1227112 < baseStart_1227112 := by decide
  rcases family_descends (prefixWord ++ tailWord_1227112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1227131 : List Nat := [1, 1, 1, 1, 1, 7, 1, 1, 2, 3, 4]
def baseStart_1227131 : Nat := 118140960795 + 1227131 * 2 ^ 59
def prefixEnd_1227131 : Nat := 4983230072969 + 3 ^ 40 * 1227131 * 2
def baseEnd_1227131 : Nat := 630108029032543578019033

theorem tailTrace_1227131 : CollatzResearch.WordTrace tailWord_1227131 prefixEnd_1227131 630108029032543578019033 := by
  unfold tailWord_1227131
  simp only [CollatzResearch.WordTrace]
  refine ⟨44757144517321439134609247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29838096344880959423072831 44757144517321439134609247)
  ·
    refine ⟨67135716775982158701913871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44757144517321439134609247 67135716775982158701913871)
    ·
      refine ⟨100703575163973238052870807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67135716775982158701913871 100703575163973238052870807)
      ·
        refine ⟨151055362745959857079306211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100703575163973238052870807 151055362745959857079306211)
        ·
          refine ⟨226583044118939785618959317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151055362745959857079306211 226583044118939785618959317)
          ·
            refine ⟨5310540096537651225444359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 226583044118939785618959317 5310540096537651225444359)
            ·
              refine ⟨7965810144806476838166539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5310540096537651225444359 7965810144806476838166539)
              ·
                refine ⟨11948715217209715257249809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7965810144806476838166539 11948715217209715257249809)
                ·
                  refine ⟨8961536412907286442937357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11948715217209715257249809 8961536412907286442937357)
                  ·
                    refine ⟨3360576154840232416101509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8961536412907286442937357 3360576154840232416101509)
                    ·
                      refine ⟨630108029032543578019033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3360576154840232416101509 630108029032543578019033)
                      ·
                        rfl

theorem cell23_1227131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 1, 2, 3, 4].length) (baseStart_1227131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1227131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1227131 prefixEnd_1227131 := by exact prefixLift 1227131
  have htrace : WordTrace (prefixWord ++ tailWord_1227131) baseStart_1227131 baseEnd_1227131 := by
    simpa [prefixWord, tailWord_1227131, baseEnd_1227131] using wordTrace_append hprefix tailTrace_1227131
  have hstable : (prefixWord ++ tailWord_1227131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1227131).length < 2 ^ (prefixWord ++ tailWord_1227131).sum := by decide
  have hdescent : baseEnd_1227131 < baseStart_1227131 := by decide
  rcases family_descends (prefixWord ++ tailWord_1227131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1227161 : List Nat := [1, 2, 1, 2, 1, 4, 1, 2, 1, 4, 4]
def baseStart_1227161 : Nat := 118140960795 + 1227161 * 2 ^ 59
def prefixEnd_1227161 : Nat := 4983230072969 + 3 ^ 40 * 1227161 * 2
def baseEnd_1227161 : Nat := 630123433452178460643895

theorem tailTrace_1227161 : CollatzResearch.WordTrace tailWord_1227161 prefixEnd_1227161 630123433452178460643895 := by
  unfold tailWord_1227161
  simp only [CollatzResearch.WordTrace]
  refine ⟨44758238707212754258201337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29838825804808502838800891 44758238707212754258201337)
  ·
    refine ⟨33568679030409565693651003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44758238707212754258201337 33568679030409565693651003)
    ·
      refine ⟨50353018545614348540476505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33568679030409565693651003 50353018545614348540476505)
      ·
        refine ⟨37764763909210761405357379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50353018545614348540476505 37764763909210761405357379)
        ·
          refine ⟨56647145863816142108036069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37764763909210761405357379 56647145863816142108036069)
          ·
            refine ⟨10621339849465526645256763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56647145863816142108036069 10621339849465526645256763)
            ·
              refine ⟨15932009774198289967885145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10621339849465526645256763 15932009774198289967885145)
              ·
                refine ⟨11949007330648717475913859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15932009774198289967885145 11949007330648717475913859)
                ·
                  refine ⟨17923510995973076213870789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11949007330648717475913859 17923510995973076213870789)
                  ·
                    refine ⟨3360658311744951790100773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17923510995973076213870789 3360658311744951790100773)
                    ·
                      refine ⟨630123433452178460643895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3360658311744951790100773 630123433452178460643895)
                      ·
                        rfl

theorem cell23_1227161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 2, 1, 4, 4].length) (baseStart_1227161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1227161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1227161 prefixEnd_1227161 := by exact prefixLift 1227161
  have htrace : WordTrace (prefixWord ++ tailWord_1227161) baseStart_1227161 baseEnd_1227161 := by
    simpa [prefixWord, tailWord_1227161, baseEnd_1227161] using wordTrace_append hprefix tailTrace_1227161
  have hstable : (prefixWord ++ tailWord_1227161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1227161).length < 2 ^ (prefixWord ++ tailWord_1227161).sum := by decide
  have hdescent : baseEnd_1227161 < baseStart_1227161 := by decide
  rcases family_descends (prefixWord ++ tailWord_1227161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1227169 : List Nat := [1, 2, 3, 5, 1, 1, 1, 3, 1, 3, 2]
def baseStart_1227169 : Nat := 118140960795 + 1227169 * 2 ^ 59
def prefixEnd_1227169 : Nat := 4983230072969 + 3 ^ 40 * 1227169 * 2
def baseEnd_1227169 : Nat := 630127541297414429343859

theorem tailTrace_1227169 : CollatzResearch.WordTrace tailWord_1227169 prefixEnd_1227169 630127541297414429343859 := by
  unfold tailWord_1227169
  simp only [CollatzResearch.WordTrace]
  refine ⟨44758530491183771624492561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29839020327455847749661707 44758530491183771624492561)
  ·
    refine ⟨33568897868387828718369421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44758530491183771624492561 33568897868387828718369421)
    ·
      refine ⟨12588336700645435769388533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33568897868387828718369421 12588336700645435769388533)
      ·
        refine ⟨1180156565685509603380175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12588336700645435769388533 1180156565685509603380175)
        ·
          refine ⟨1770234848528264405070263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1180156565685509603380175 1770234848528264405070263)
          ·
            refine ⟨2655352272792396607605395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1770234848528264405070263 2655352272792396607605395)
            ·
              refine ⟨3983028409188594911408093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2655352272792396607605395 3983028409188594911408093)
              ·
                refine ⟨1493635653445723091778035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3983028409188594911408093 1493635653445723091778035)
                ·
                  refine ⟨2240453480168584637667053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1493635653445723091778035 2240453480168584637667053)
                  ·
                    refine ⟨840170055063219239125145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2240453480168584637667053 840170055063219239125145)
                    ·
                      refine ⟨630127541297414429343859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 840170055063219239125145 630127541297414429343859)
                      ·
                        rfl

theorem cell23_1227169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_1227169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1227169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1227169 prefixEnd_1227169 := by exact prefixLift 1227169
  have htrace : WordTrace (prefixWord ++ tailWord_1227169) baseStart_1227169 baseEnd_1227169 := by
    simpa [prefixWord, tailWord_1227169, baseEnd_1227169] using wordTrace_append hprefix tailTrace_1227169
  have hstable : (prefixWord ++ tailWord_1227169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1227169).length < 2 ^ (prefixWord ++ tailWord_1227169).sum := by decide
  have hdescent : baseEnd_1227169 < baseStart_1227169 := by decide
  rcases family_descends (prefixWord ++ tailWord_1227169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1227211 : List Nat := [1, 1, 1, 1, 3, 3, 1, 2, 3, 2, 5]
def baseStart_1227211 : Nat := 118140960795 + 1227211 * 2 ^ 59
def prefixEnd_1227211 : Nat := 4983230072969 + 3 ^ 40 * 1227211 * 2
def baseEnd_1227211 : Nat := 630149107484903265018665

theorem tailTrace_1227211 : CollatzResearch.WordTrace tailWord_1227211 prefixEnd_1227211 630149107484903265018665 := by
  unfold tailWord_1227211
  simp only [CollatzResearch.WordTrace]
  refine ⟨44760062357031612797521487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29840041571354408531680991 44760062357031612797521487)
  ·
    refine ⟨67140093535547419196282231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44760062357031612797521487 67140093535547419196282231)
    ·
      refine ⟨100710140303321128794423347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67140093535547419196282231 100710140303321128794423347)
      ·
        refine ⟨151065210454981693191635021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100710140303321128794423347 151065210454981693191635021)
        ·
          refine ⟨56649453920618134946863133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 151065210454981693191635021 56649453920618134946863133)
          ·
            refine ⟨21243545220231800605073675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56649453920618134946863133 21243545220231800605073675)
            ·
              refine ⟨31865317830347700907610513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21243545220231800605073675 31865317830347700907610513)
              ·
                refine ⟨23898988372760775680707885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31865317830347700907610513 23898988372760775680707885)
                ·
                  refine ⟨8962120639785290880265457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23898988372760775680707885 8962120639785290880265457)
                  ·
                    refine ⟨6721590479838968160199093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8962120639785290880265457 6721590479838968160199093)
                    ·
                      refine ⟨630149107484903265018665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6721590479838968160199093 630149107484903265018665)
                      ·
                        rfl

theorem cell23_1227211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 2, 3, 2, 5].length) (baseStart_1227211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1227211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1227211 prefixEnd_1227211 := by exact prefixLift 1227211
  have htrace : WordTrace (prefixWord ++ tailWord_1227211) baseStart_1227211 baseEnd_1227211 := by
    simpa [prefixWord, tailWord_1227211, baseEnd_1227211] using wordTrace_append hprefix tailTrace_1227211
  have hstable : (prefixWord ++ tailWord_1227211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1227211).length < 2 ^ (prefixWord ++ tailWord_1227211).sum := by decide
  have hdescent : baseEnd_1227211 < baseStart_1227211 := by decide
  rcases family_descends (prefixWord ++ tailWord_1227211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1227235 : List Nat := [1, 1, 1, 6, 3, 1, 1, 2, 2, 5]
def baseStart_1227235 : Nat := 118140960795 + 1227235 * 2 ^ 59
def prefixEnd_1227235 : Nat := 4983230072969 + 3 ^ 40 * 1227235 * 2
def baseEnd_1227235 : Nat := 210053810340203723706185

theorem tailTrace_1227235 : CollatzResearch.WordTrace tailWord_1227235 prefixEnd_1227235 210053810340203723706185 := by
  unfold tailWord_1227235
  simp only [CollatzResearch.WordTrace]
  refine ⟨44760937708944664896395159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29840625139296443264263439 44760937708944664896395159)
  ·
    refine ⟨67141406563416997344592739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44760937708944664896395159 67141406563416997344592739)
    ·
      refine ⟨100712109845125496016889109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67141406563416997344592739 100712109845125496016889109)
      ·
        refine ⟨4720880148990257625791677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 100712109845125496016889109 4720880148990257625791677)
        ·
          refine ⟨1770330055871346609671879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4720880148990257625791677 1770330055871346609671879)
          ·
            refine ⟨2655495083807019914507819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1770330055871346609671879 2655495083807019914507819)
            ·
              refine ⟨3983242625710529871761729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2655495083807019914507819 3983242625710529871761729)
              ·
                refine ⟨2987431969282897403821297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3983242625710529871761729 2987431969282897403821297)
                ·
                  refine ⟨2240573976962173052865973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2987431969282897403821297 2240573976962173052865973)
                  ·
                    refine ⟨210053810340203723706185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2240573976962173052865973 210053810340203723706185)
                    ·
                      rfl

theorem cell23_1227235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 2, 2, 5].length) (baseStart_1227235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1227235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1227235 prefixEnd_1227235 := by exact prefixLift 1227235
  have htrace : WordTrace (prefixWord ++ tailWord_1227235) baseStart_1227235 baseEnd_1227235 := by
    simpa [prefixWord, tailWord_1227235, baseEnd_1227235] using wordTrace_append hprefix tailTrace_1227235
  have hstable : (prefixWord ++ tailWord_1227235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1227235).length < 2 ^ (prefixWord ++ tailWord_1227235).sum := by decide
  have hdescent : baseEnd_1227235 < baseStart_1227235 := by decide
  rcases family_descends (prefixWord ++ tailWord_1227235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1227241 : List Nat := [1, 2, 1, 1, 1, 2, 1, 3, 1, 5, 5]
def baseStart_1227241 : Nat := 118140960795 + 1227241 * 2 ^ 59
def prefixEnd_1227241 : Nat := 4983230072969 + 3 ^ 40 * 1227241 * 2
def baseEnd_1227241 : Nat := 630164511904538147643527

theorem tailTrace_1227241 : CollatzResearch.WordTrace tailWord_1227241 prefixEnd_1227241 630164511904538147643527 := by
  unfold tailWord_1227241
  simp only [CollatzResearch.WordTrace]
  refine ⟨44761156546922927921113577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29840771031281951947409051 44761156546922927921113577)
  ·
    refine ⟨33570867410192195940835183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44761156546922927921113577 33570867410192195940835183)
    ·
      refine ⟨50356301115288293911252775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33570867410192195940835183 50356301115288293911252775)
      ·
        refine ⟨75534451672932440866879163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50356301115288293911252775 75534451672932440866879163)
        ·
          refine ⟨113301677509398661300318745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75534451672932440866879163 113301677509398661300318745)
          ·
            refine ⟨84976258132048995975239059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113301677509398661300318745 84976258132048995975239059)
            ·
              refine ⟨127464387198073493962858589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84976258132048995975239059 127464387198073493962858589)
              ·
                refine ⟨47799145199277560236071971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 127464387198073493962858589 47799145199277560236071971)
                ·
                  refine ⟨71698717798916340354107957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47799145199277560236071971 71698717798916340354107957)
                  ·
                    refine ⟨6721754793648406908197621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 71698717798916340354107957 6721754793648406908197621)
                    ·
                      refine ⟨630164511904538147643527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6721754793648406908197621 630164511904538147643527)
                      ·
                        rfl

theorem cell23_1227241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 5, 5].length) (baseStart_1227241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1227241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1227241 prefixEnd_1227241 := by exact prefixLift 1227241
  have htrace : WordTrace (prefixWord ++ tailWord_1227241) baseStart_1227241 baseEnd_1227241 := by
    simpa [prefixWord, tailWord_1227241, baseEnd_1227241] using wordTrace_append hprefix tailTrace_1227241
  have hstable : (prefixWord ++ tailWord_1227241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1227241).length < 2 ^ (prefixWord ++ tailWord_1227241).sum := by decide
  have hdescent : baseEnd_1227241 < baseStart_1227241 := by decide
  rcases family_descends (prefixWord ++ tailWord_1227241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1227245 : List Nat := [1, 5, 1, 3, 1, 2, 1, 1, 1, 2, 5]
def baseStart_1227245 : Nat := 118140960795 + 1227245 * 2 ^ 59
def prefixEnd_1227245 : Nat := 4983230072969 + 3 ^ 40 * 1227245 * 2
def baseEnd_1227245 : Nat := 630166565827156131993509

theorem tailTrace_1227245 : CollatzResearch.WordTrace tailWord_1227245 prefixEnd_1227245 630166565827156131993509 := by
  unfold tailWord_1227245
  simp only [CollatzResearch.WordTrace]
  refine ⟨44761302438908436604259189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29840868292605624402839459 44761302438908436604259189)
  ·
    refine ⟨4196372103647665931649299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 44761302438908436604259189 4196372103647665931649299)
    ·
      refine ⟨6294558155471498897473949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4196372103647665931649299 6294558155471498897473949)
      ·
        refine ⟨2360459308301812086552731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6294558155471498897473949 2360459308301812086552731)
        ·
          refine ⟨3540688962452718129829097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2360459308301812086552731 3540688962452718129829097)
          ·
            refine ⟨2655516721839538597371823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3540688962452718129829097 2655516721839538597371823)
            ·
              refine ⟨3983275082759307896057735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2655516721839538597371823 3983275082759307896057735)
              ·
                refine ⟨5974912624138961844086603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3983275082759307896057735 5974912624138961844086603)
                ·
                  refine ⟨8962368936208442766129905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5974912624138961844086603 8962368936208442766129905)
                  ·
                    refine ⟨6721776702156332074597429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8962368936208442766129905 6721776702156332074597429)
                    ·
                      refine ⟨630166565827156131993509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6721776702156332074597429 630166565827156131993509)
                      ·
                        rfl

theorem cell23_1227245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_1227245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1227245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1227245 prefixEnd_1227245 := by exact prefixLift 1227245
  have htrace : WordTrace (prefixWord ++ tailWord_1227245) baseStart_1227245 baseEnd_1227245 := by
    simpa [prefixWord, tailWord_1227245, baseEnd_1227245] using wordTrace_append hprefix tailTrace_1227245
  have hstable : (prefixWord ++ tailWord_1227245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1227245).length < 2 ^ (prefixWord ++ tailWord_1227245).sum := by decide
  have hdescent : baseEnd_1227245 < baseStart_1227245 := by decide
  rcases family_descends (prefixWord ++ tailWord_1227245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1227258 : List Nat := [3, 1, 1, 1, 1, 2, 2, 4, 1, 4, 3]
def baseStart_1227258 : Nat := 118140960795 + 1227258 * 2 ^ 59
def prefixEnd_1227258 : Nat := 4983230072969 + 3 ^ 40 * 1227258 * 2
def baseEnd_1227258 : Nat := 630173241075664581130949

theorem tailTrace_1227258 : CollatzResearch.WordTrace tailWord_1227258 prefixEnd_1227258 630173241075664581130949 := by
  unfold tailWord_1227258
  simp only [CollatzResearch.WordTrace]
  refine ⟨11190444146965334956120607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29841184391907559882988285 11190444146965334956120607)
  ·
    refine ⟨16785666220448002434180911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11190444146965334956120607 16785666220448002434180911)
    ·
      refine ⟨25178499330672003651271367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16785666220448002434180911 25178499330672003651271367)
      ·
        refine ⟨37767748996008005476907051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25178499330672003651271367 37767748996008005476907051)
        ·
          refine ⟨56651623494012008215360577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37767748996008005476907051 56651623494012008215360577)
          ·
            refine ⟨42488717620509006161520433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56651623494012008215360577 42488717620509006161520433)
            ·
              refine ⟨31866538215381754621140325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42488717620509006161520433 31866538215381754621140325)
              ·
                refine ⟨5974975915384078991463811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31866538215381754621140325 5974975915384078991463811)
                ·
                  refine ⟨8962463873076118487195717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5974975915384078991463811 8962463873076118487195717)
                  ·
                    refine ⟨1680461976201772216349197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8962463873076118487195717 1680461976201772216349197)
                    ·
                      refine ⟨630173241075664581130949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1680461976201772216349197 630173241075664581130949)
                      ·
                        rfl

theorem cell23_1227258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 4, 1, 4, 3].length) (baseStart_1227258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1227258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1227258 prefixEnd_1227258 := by exact prefixLift 1227258
  have htrace : WordTrace (prefixWord ++ tailWord_1227258) baseStart_1227258 baseEnd_1227258 := by
    simpa [prefixWord, tailWord_1227258, baseEnd_1227258] using wordTrace_append hprefix tailTrace_1227258
  have hstable : (prefixWord ++ tailWord_1227258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1227258).length < 2 ^ (prefixWord ++ tailWord_1227258).sum := by decide
  have hdescent : baseEnd_1227258 < baseStart_1227258 := by decide
  rcases family_descends (prefixWord ++ tailWord_1227258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1227275 : List Nat := [1, 1, 1, 1, 7, 1, 1, 3, 2, 2, 3]
def baseStart_1227275 : Nat := 118140960795 + 1227275 * 2 ^ 59
def prefixEnd_1227275 : Nat := 4983230072969 + 3 ^ 40 * 1227275 * 2
def baseEnd_1227275 : Nat := 630181970246791014618371

theorem tailTrace_1227275 : CollatzResearch.WordTrace tailWord_1227275 prefixEnd_1227275 630181970246791014618371 := by
  unfold tailWord_1227275
  simp only [CollatzResearch.WordTrace]
  refine ⟨44762396628799751727851279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29841597752533167818567519 44762396628799751727851279)
  ·
    refine ⟨67143594943199627591776919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44762396628799751727851279 67143594943199627591776919)
    ·
      refine ⟨100715392414799441387665379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67143594943199627591776919 100715392414799441387665379)
      ·
        refine ⟨151073088622199162081498069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100715392414799441387665379 151073088622199162081498069)
        ·
          refine ⟨3540775514582792861285111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 151073088622199162081498069 3540775514582792861285111)
          ·
            refine ⟨5311163271874189291927667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3540775514582792861285111 5311163271874189291927667)
            ·
              refine ⟨7966744907811283937891501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5311163271874189291927667 7966744907811283937891501)
              ·
                refine ⟨2987529340429231476709313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7966744907811283937891501 2987529340429231476709313)
                ·
                  refine ⟨2240647005321923607531985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2987529340429231476709313 2240647005321923607531985)
                  ·
                    refine ⟨1680485253991442705648989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2240647005321923607531985 1680485253991442705648989)
                    ·
                      refine ⟨630181970246791014618371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1680485253991442705648989 630181970246791014618371)
                      ·
                        rfl

theorem cell23_1227275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 3, 2, 2, 3].length) (baseStart_1227275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1227275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1227275 prefixEnd_1227275 := by exact prefixLift 1227275
  have htrace : WordTrace (prefixWord ++ tailWord_1227275) baseStart_1227275 baseEnd_1227275 := by
    simpa [prefixWord, tailWord_1227275, baseEnd_1227275] using wordTrace_append hprefix tailTrace_1227275
  have hstable : (prefixWord ++ tailWord_1227275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1227275).length < 2 ^ (prefixWord ++ tailWord_1227275).sum := by decide
  have hdescent : baseEnd_1227275 < baseStart_1227275 := by decide
  rcases family_descends (prefixWord ++ tailWord_1227275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1227298 : List Nat := [3, 3, 1, 1, 1, 1, 1, 3, 1, 2, 6]
def baseStart_1227298 : Nat := 118140960795 + 1227298 * 2 ^ 59
def prefixEnd_1227298 : Nat := 4983230072969 + 3 ^ 40 * 1227298 * 2
def baseEnd_1227298 : Nat := 630193780301844424630765

theorem tailTrace_1227298 : CollatzResearch.WordTrace tailWord_1227298 prefixEnd_1227298 630193780301844424630765 := by
  unfold tailWord_1227298
  simp only [CollatzResearch.WordTrace]
  refine ⟨11190808876929106663984637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29842157005144284437292365 11190808876929106663984637)
  ·
    refine ⟨4196553328848414998994239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11190808876929106663984637 4196553328848414998994239)
    ·
      refine ⟨6294829993272622498491359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4196553328848414998994239 6294829993272622498491359)
      ·
        refine ⟨9442244989908933747737039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6294829993272622498491359 9442244989908933747737039)
        ·
          refine ⟨14163367484863400621605559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9442244989908933747737039 14163367484863400621605559)
          ·
            refine ⟨21245051227295100932408339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14163367484863400621605559 21245051227295100932408339)
            ·
              refine ⟨31867576840942651398612509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21245051227295100932408339 31867576840942651398612509)
              ·
                refine ⟨11950341315353494274479691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31867576840942651398612509 11950341315353494274479691)
                ·
                  refine ⟨17925511973030241411719537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11950341315353494274479691 17925511973030241411719537)
                  ·
                    refine ⟨13444133979772681058789653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17925511973030241411719537 13444133979772681058789653)
                    ·
                      refine ⟨630193780301844424630765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13444133979772681058789653 630193780301844424630765)
                      ·
                        rfl

theorem cell23_1227298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 3, 1, 2, 6].length) (baseStart_1227298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1227298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1227298 prefixEnd_1227298 := by exact prefixLift 1227298
  have htrace : WordTrace (prefixWord ++ tailWord_1227298) baseStart_1227298 baseEnd_1227298 := by
    simpa [prefixWord, tailWord_1227298, baseEnd_1227298] using wordTrace_append hprefix tailTrace_1227298
  have hstable : (prefixWord ++ tailWord_1227298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1227298).length < 2 ^ (prefixWord ++ tailWord_1227298).sum := by decide
  have hdescent : baseEnd_1227298 < baseStart_1227298 := by decide
  rcases family_descends (prefixWord ++ tailWord_1227298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1227299 : List Nat := [1, 1, 1, 4, 4, 1, 4, 2, 1, 4]
def baseStart_1227299 : Nat := 118140960795 + 1227299 * 2 ^ 59
def prefixEnd_1227299 : Nat := 4983230072969 + 3 ^ 40 * 1227299 * 2
def baseEnd_1227299 : Nat := 210064764594166306906087

theorem tailTrace_1227299 : CollatzResearch.WordTrace tailWord_1227299 prefixEnd_1227299 210064764594166306906087 := by
  unfold tailWord_1227299
  simp only [CollatzResearch.WordTrace]
  refine ⟨44763271980712803826724951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29842181320475202551149967 44763271980712803826724951)
  ·
    refine ⟨67144907971069205740087427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44763271980712803826724951 67144907971069205740087427)
    ·
      refine ⟨100717361956603808610131141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67144907971069205740087427 100717361956603808610131141)
      ·
        refine ⟨18884505366863214114399589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 100717361956603808610131141 18884505366863214114399589)
        ·
          refine ⟨3540844756286852646449923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18884505366863214114399589 3540844756286852646449923)
          ·
            refine ⟨5311267134430278969674885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3540844756286852646449923 5311267134430278969674885)
            ·
              refine ⟨995862587705677306814041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5311267134430278969674885 995862587705677306814041)
              ·
                refine ⟨746896940779257980110531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 995862587705677306814041 746896940779257980110531)
                ·
                  refine ⟨1120345411168886970165797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 746896940779257980110531 1120345411168886970165797)
                  ·
                    refine ⟨210064764594166306906087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1120345411168886970165797 210064764594166306906087)
                    ·
                      rfl

theorem cell23_1227299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 4, 2, 1, 4].length) (baseStart_1227299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1227299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1227299 prefixEnd_1227299 := by exact prefixLift 1227299
  have htrace : WordTrace (prefixWord ++ tailWord_1227299) baseStart_1227299 baseEnd_1227299 := by
    simpa [prefixWord, tailWord_1227299, baseEnd_1227299] using wordTrace_append hprefix tailTrace_1227299
  have hstable : (prefixWord ++ tailWord_1227299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1227299).length < 2 ^ (prefixWord ++ tailWord_1227299).sum := by decide
  have hdescent : baseEnd_1227299 < baseStart_1227299 := by decide
  rcases family_descends (prefixWord ++ tailWord_1227299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1227315 : List Nat := [1, 1, 1, 2, 4, 2, 2, 2, 1, 5, 2]
def baseStart_1227315 : Nat := 118140960795 + 1227315 * 2 ^ 59
def prefixEnd_1227315 : Nat := 4983230072969 + 3 ^ 40 * 1227315 * 2
def baseEnd_1227315 : Nat := 630202509472970858118187

theorem tailTrace_1227315 : CollatzResearch.WordTrace tailWord_1227315 prefixEnd_1227315 630202509472970858118187 := by
  unfold tailWord_1227315
  simp only [CollatzResearch.WordTrace]
  refine ⟨44763855548654838559307399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29842570365769892372871599 44763855548654838559307399)
  ·
    refine ⟨67145783322982257838961099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44763855548654838559307399 67145783322982257838961099)
    ·
      refine ⟨100718674984473386758441649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67145783322982257838961099 100718674984473386758441649)
      ·
        refine ⟨75539006238355040068831237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100718674984473386758441649 75539006238355040068831237)
        ·
          refine ⟨14163563669691570012905857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 75539006238355040068831237 14163563669691570012905857)
          ·
            refine ⟨10622672752268677509679393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14163563669691570012905857 10622672752268677509679393)
            ·
              refine ⟨7967004564201508132259545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10622672752268677509679393 7967004564201508132259545)
              ·
                refine ⟨5975253423151131099194659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7967004564201508132259545 5975253423151131099194659)
                ·
                  refine ⟨8962880134726696648791989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5975253423151131099194659 8962880134726696648791989)
                  ·
                    refine ⟨840270012630627810824249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8962880134726696648791989 840270012630627810824249)
                    ·
                      refine ⟨630202509472970858118187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 840270012630627810824249 630202509472970858118187)
                      ·
                        rfl

theorem cell23_1227315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 2, 1, 5, 2].length) (baseStart_1227315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1227315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1227315 prefixEnd_1227315 := by exact prefixLift 1227315
  have htrace : WordTrace (prefixWord ++ tailWord_1227315) baseStart_1227315 baseEnd_1227315 := by
    simpa [prefixWord, tailWord_1227315, baseEnd_1227315] using wordTrace_append hprefix tailTrace_1227315
  have hstable : (prefixWord ++ tailWord_1227315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1227315).length < 2 ^ (prefixWord ++ tailWord_1227315).sum := by decide
  have hdescent : baseEnd_1227315 < baseStart_1227315 := by decide
  rcases family_descends (prefixWord ++ tailWord_1227315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1227322 : List Nat := [3, 1, 1, 1, 3, 4, 1, 2, 3, 1, 3]
def baseStart_1227322 : Nat := 118140960795 + 1227322 * 2 ^ 59
def prefixEnd_1227322 : Nat := 4983230072969 + 3 ^ 40 * 1227322 * 2
def baseEnd_1227322 : Nat := 630206103837552330730655

theorem tailTrace_1227322 : CollatzResearch.WordTrace tailWord_1227322 prefixEnd_1227322 630206103837552330730655 := by
  unfold tailWord_1227322
  simp only [CollatzResearch.WordTrace]
  refine ⟨11191027714907369688703055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29842740573086319169874813 11191027714907369688703055)
  ·
    refine ⟨16786541572361054533054583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11191027714907369688703055 16786541572361054533054583)
    ·
      refine ⟨25179812358541581799581875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16786541572361054533054583 25179812358541581799581875)
      ·
        refine ⟨37769718537812372699372813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25179812358541581799581875 37769718537812372699372813)
        ·
          refine ⟨14163644451679639762264805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37769718537812372699372813 14163644451679639762264805)
          ·
            refine ⟨2655683334689932455424651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14163644451679639762264805 2655683334689932455424651)
            ·
              refine ⟨3983525002034898683136977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2655683334689932455424651 3983525002034898683136977)
              ·
                refine ⟨2987643751526174012352733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3983525002034898683136977 2987643751526174012352733)
                ·
                  refine ⟨1120366406822315254632275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2987643751526174012352733 1120366406822315254632275)
                  ·
                    refine ⟨1680549610233472881948413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1120366406822315254632275 1680549610233472881948413)
                    ·
                      refine ⟨630206103837552330730655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1680549610233472881948413 630206103837552330730655)
                      ·
                        rfl

theorem cell23_1227322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 2, 3, 1, 3].length) (baseStart_1227322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1227322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1227322 prefixEnd_1227322 := by exact prefixLift 1227322
  have htrace : WordTrace (prefixWord ++ tailWord_1227322) baseStart_1227322 baseEnd_1227322 := by
    simpa [prefixWord, tailWord_1227322, baseEnd_1227322] using wordTrace_append hprefix tailTrace_1227322
  have hstable : (prefixWord ++ tailWord_1227322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1227322).length < 2 ^ (prefixWord ++ tailWord_1227322).sum := by decide
  have hdescent : baseEnd_1227322 < baseStart_1227322 := by decide
  rcases family_descends (prefixWord ++ tailWord_1227322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1227325 : List Nat := [1, 4, 1, 3, 2, 1, 2, 1, 3, 5]
def baseStart_1227325 : Nat := 118140960795 + 1227325 * 2 ^ 59
def prefixEnd_1227325 : Nat := 4983230072969 + 3 ^ 40 * 1227325 * 2
def baseEnd_1227325 : Nat := 210069214759838606331047

theorem tailTrace_1227325 : CollatzResearch.WordTrace tailWord_1227325 prefixEnd_1227325 210069214759838606331047 := by
  unfold tailWord_1227325
  simp only [CollatzResearch.WordTrace]
  refine ⟨44764220278618610267171429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29842813519079073511447619 44764220278618610267171429)
  ·
    refine ⟨8393291302240989425094643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44764220278618610267171429 8393291302240989425094643)
    ·
      refine ⟨12589936953361484137641965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8393291302240989425094643 12589936953361484137641965)
      ·
        refine ⟨4721226357510556551615737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12589936953361484137641965 4721226357510556551615737)
        ·
          refine ⟨3540919768132917413711803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4721226357510556551615737 3540919768132917413711803)
          ·
            refine ⟨5311379652199376120567705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3540919768132917413711803 5311379652199376120567705)
            ·
              refine ⟨3983534739149532090425779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5311379652199376120567705 3983534739149532090425779)
              ·
                refine ⟨5975302108724298135638669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3983534739149532090425779 5975302108724298135638669)
                ·
                  refine ⟨2240738290771611800864501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5975302108724298135638669 2240738290771611800864501)
                  ·
                    refine ⟨210069214759838606331047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2240738290771611800864501 210069214759838606331047)
                    ·
                      rfl

theorem cell23_1227325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 1, 3, 5].length) (baseStart_1227325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1227325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1227325 prefixEnd_1227325 := by exact prefixLift 1227325
  have htrace : WordTrace (prefixWord ++ tailWord_1227325) baseStart_1227325 baseEnd_1227325 := by
    simpa [prefixWord, tailWord_1227325, baseEnd_1227325] using wordTrace_append hprefix tailTrace_1227325
  have hstable : (prefixWord ++ tailWord_1227325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1227325).length < 2 ^ (prefixWord ++ tailWord_1227325).sum := by decide
  have hdescent : baseEnd_1227325 < baseStart_1227325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1227325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1227326 : List Nat := [4, 2, 1, 4, 1, 2, 1, 1, 2, 2, 3]
def baseStart_1227326 : Nat := 118140960795 + 1227326 * 2 ^ 59
def prefixEnd_1227326 : Nat := 4983230072969 + 3 ^ 40 * 1227326 * 2
def baseEnd_1227326 : Nat := 630208157760170315080637

theorem tailTrace_1227326 : CollatzResearch.WordTrace tailWord_1227326 prefixEnd_1227326 630208157760170315080637 := by
  unfold tailWord_1227326
  simp only [CollatzResearch.WordTrace]
  refine ⟨5595532093951873429744729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29842837834409991625305221 5595532093951873429744729)
  ·
    refine ⟨4196649070463905072308547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5595532093951873429744729 4196649070463905072308547)
    ·
      refine ⟨6294973605695857608462821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4196649070463905072308547 6294973605695857608462821)
      ·
        refine ⟨1180307551067973301586779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6294973605695857608462821 1180307551067973301586779)
        ·
          refine ⟨1770461326601959952380169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1180307551067973301586779 1770461326601959952380169)
          ·
            refine ⟨1327845994951469964285127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1770461326601959952380169 1327845994951469964285127)
            ·
              refine ⟨1991768992427204946427691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1327845994951469964285127 1991768992427204946427691)
              ·
                refine ⟨2987653488640807419641537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1991768992427204946427691 2987653488640807419641537)
                ·
                  refine ⟨2240740116480605564731153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2987653488640807419641537 2240740116480605564731153)
                  ·
                    refine ⟨1680555087360454173548365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2240740116480605564731153 1680555087360454173548365)
                    ·
                      refine ⟨630208157760170315080637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1680555087360454173548365 630208157760170315080637)
                      ·
                        rfl

theorem cell23_1227326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_1227326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1227326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1227326 prefixEnd_1227326 := by exact prefixLift 1227326
  have htrace : WordTrace (prefixWord ++ tailWord_1227326) baseStart_1227326 baseEnd_1227326 := by
    simpa [prefixWord, tailWord_1227326, baseEnd_1227326] using wordTrace_append hprefix tailTrace_1227326
  have hstable : (prefixWord ++ tailWord_1227326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1227326).length < 2 ^ (prefixWord ++ tailWord_1227326).sum := by decide
  have hdescent : baseEnd_1227326 < baseStart_1227326 := by decide
  rcases family_descends (prefixWord ++ tailWord_1227326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1227342 : List Nat := [4, 1, 1, 1, 1, 2, 6, 1, 1, 5]
def baseStart_1227342 : Nat := 118140960795 + 1227342 * 2 ^ 59
def prefixEnd_1227342 : Nat := 4983230072969 + 3 ^ 40 * 1227342 * 2
def baseEnd_1227342 : Nat := 210072124483547417493521

theorem tailTrace_1227342 : CollatzResearch.WordTrace tailWord_1227342 prefixEnd_1227342 210072124483547417493521 := by
  unfold tailWord_1227342
  simp only [CollatzResearch.WordTrace]
  refine ⟨5595605039944627771317535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29843226879704681447026853 5595605039944627771317535)
  ·
    refine ⟨8393407559916941656976303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5595605039944627771317535 8393407559916941656976303)
    ·
      refine ⟨12590111339875412485464455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8393407559916941656976303 12590111339875412485464455)
      ·
        refine ⟨18885167009813118728196683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12590111339875412485464455 18885167009813118728196683)
        ·
          refine ⟨28327750514719678092295025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18885167009813118728196683 28327750514719678092295025)
          ·
            refine ⟨21245812886039758569221269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28327750514719678092295025 21245812886039758569221269)
            ·
              refine ⟨995897479033113682932247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 21245812886039758569221269 995897479033113682932247)
              ·
                refine ⟨1493846218549670524398371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 995897479033113682932247 1493846218549670524398371)
                ·
                  refine ⟨2240769327824505786597557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1493846218549670524398371 2240769327824505786597557)
                  ·
                    refine ⟨210072124483547417493521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2240769327824505786597557 210072124483547417493521)
                    ·
                      rfl

theorem cell23_1227342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 6, 1, 1, 5].length) (baseStart_1227342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1227342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1227342 prefixEnd_1227342 := by exact prefixLift 1227342
  have htrace : WordTrace (prefixWord ++ tailWord_1227342) baseStart_1227342 baseEnd_1227342 := by
    simpa [prefixWord, tailWord_1227342, baseEnd_1227342] using wordTrace_append hprefix tailTrace_1227342
  have hstable : (prefixWord ++ tailWord_1227342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1227342).length < 2 ^ (prefixWord ++ tailWord_1227342).sum := by decide
  have hdescent : baseEnd_1227342 < baseStart_1227342 := by decide
  rcases family_descends (prefixWord ++ tailWord_1227342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1227375 : List Nat := [1, 1, 2, 1, 3, 2, 5, 1, 1, 2, 4]
def baseStart_1227375 : Nat := 118140960795 + 1227375 * 2 ^ 59
def prefixEnd_1227375 : Nat := 4983230072969 + 3 ^ 40 * 1227375 * 2
def baseEnd_1227375 : Nat := 630233318312240623367911

theorem tailTrace_1227375 : CollatzResearch.WordTrace tailWord_1227375 prefixEnd_1227375 630233318312240623367911 := by
  unfold tailWord_1227375
  simp only [CollatzResearch.WordTrace]
  refine ⟨44766043928437468806491579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29844029285624979204327719 44766043928437468806491579)
  ·
    refine ⟨67149065892656203209737369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44766043928437468806491579 67149065892656203209737369)
    ·
      refine ⟨50361799419492152407303027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67149065892656203209737369 50361799419492152407303027)
      ·
        refine ⟨75542699129238228610954541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50361799419492152407303027 75542699129238228610954541)
        ·
          refine ⟨28328512173464335729107953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75542699129238228610954541 28328512173464335729107953)
          ·
            refine ⟨21246384130098251796830965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28328512173464335729107953 21246384130098251796830965)
            ·
              refine ⟨1991848512196711105952903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21246384130098251796830965 1991848512196711105952903)
              ·
                refine ⟨2987772768295066658929355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1991848512196711105952903 2987772768295066658929355)
                ·
                  refine ⟨4481659152442599988394033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2987772768295066658929355 4481659152442599988394033)
                  ·
                    refine ⟨3361244364331949991295525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4481659152442599988394033 3361244364331949991295525)
                    ·
                      refine ⟨630233318312240623367911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3361244364331949991295525 630233318312240623367911)
                      ·
                        rfl

theorem cell23_1227375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 5, 1, 1, 2, 4].length) (baseStart_1227375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1227375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1227375 prefixEnd_1227375 := by exact prefixLift 1227375
  have htrace : WordTrace (prefixWord ++ tailWord_1227375) baseStart_1227375 baseEnd_1227375 := by
    simpa [prefixWord, tailWord_1227375, baseEnd_1227375] using wordTrace_append hprefix tailTrace_1227375
  have hstable : (prefixWord ++ tailWord_1227375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1227375).length < 2 ^ (prefixWord ++ tailWord_1227375).sum := by decide
  have hdescent : baseEnd_1227375 < baseStart_1227375 := by decide
  rcases family_descends (prefixWord ++ tailWord_1227375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1227385 : List Nat := [1, 2, 1, 3, 3, 2, 4, 7]
def baseStart_1227385 : Nat := 118140960795 + 1227385 * 2 ^ 59
def prefixEnd_1227385 : Nat := 4983230072969 + 3 ^ 40 * 1227385 * 2
def baseEnd_1227385 : Nat := 23342164930325392008995

theorem tailTrace_1227385 : CollatzResearch.WordTrace tailWord_1227385 prefixEnd_1227385 23342164930325392008995 := by
  unfold tailWord_1227385
  simp only [CollatzResearch.WordTrace]
  refine ⟨44766408658401240514355609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29844272438934160342903739 44766408658401240514355609)
  ·
    refine ⟨33574806493800930385766707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44766408658401240514355609 33574806493800930385766707)
    ·
      refine ⟨50362209740701395578650061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33574806493800930385766707 50362209740701395578650061)
      ·
        refine ⟨18885828652763023341993773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50362209740701395578650061 18885828652763023341993773)
        ·
          refine ⟨7082185744786133753247665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18885828652763023341993773 7082185744786133753247665)
          ·
            refine ⟨5311639308589600314935749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7082185744786133753247665 5311639308589600314935749)
            ·
              refine ⟨995932370360550059050453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5311639308589600314935749 995932370360550059050453)
              ·
                refine ⟨23342164930325392008995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 995932370360550059050453 23342164930325392008995)
                ·
                  rfl

theorem cell23_1227385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 4, 7].length) (baseStart_1227385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1227385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1227385 prefixEnd_1227385 := by exact prefixLift 1227385
  have htrace : WordTrace (prefixWord ++ tailWord_1227385) baseStart_1227385 baseEnd_1227385 := by
    simpa [prefixWord, tailWord_1227385, baseEnd_1227385] using wordTrace_append hprefix tailTrace_1227385
  have hstable : (prefixWord ++ tailWord_1227385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1227385).length < 2 ^ (prefixWord ++ tailWord_1227385).sum := by decide
  have hdescent : baseEnd_1227385 < baseStart_1227385 := by decide
  rcases family_descends (prefixWord ++ tailWord_1227385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1227395 : List Nat := [1, 1, 1, 3, 3, 1, 2, 4, 1, 3, 3]
def baseStart_1227395 : Nat := 118140960795 + 1227395 * 2 ^ 59
def prefixEnd_1227395 : Nat := 4983230072969 + 3 ^ 40 * 1227395 * 2
def baseEnd_1227395 : Nat := 630243587925330545117819

theorem tailTrace_1227395 : CollatzResearch.WordTrace tailWord_1227395 prefixEnd_1227395 630243587925330545117819 := by
  unfold tailWord_1227395
  simp only [CollatzResearch.WordTrace]
  refine ⟨44766773388365012222219639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29844515592243341481479759 44766773388365012222219639)
  ·
    refine ⟨67150160082547518333329459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44766773388365012222219639 67150160082547518333329459)
    ·
      refine ⟨100725240123821277499994189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67150160082547518333329459 100725240123821277499994189)
      ·
        refine ⟨37771965046432979062497821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100725240123821277499994189 37771965046432979062497821)
        ·
          refine ⟨14164486892412367148436683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37771965046432979062497821 14164486892412367148436683)
          ·
            refine ⟨21246730338618550722655025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14164486892412367148436683 21246730338618550722655025)
            ·
              refine ⟨15935047753963913041991269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21246730338618550722655025 15935047753963913041991269)
              ·
                refine ⟨2987821453868233695373363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15935047753963913041991269 2987821453868233695373363)
                ·
                  refine ⟨4481732180802350543060045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2987821453868233695373363 4481732180802350543060045)
                  ·
                    refine ⟨1680649567800881453647517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4481732180802350543060045 1680649567800881453647517)
                    ·
                      refine ⟨630243587925330545117819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1680649567800881453647517 630243587925330545117819)
                      ·
                        rfl

theorem cell23_1227395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 4, 1, 3, 3].length) (baseStart_1227395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1227395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1227395 prefixEnd_1227395 := by exact prefixLift 1227395
  have htrace : WordTrace (prefixWord ++ tailWord_1227395) baseStart_1227395 baseEnd_1227395 := by
    simpa [prefixWord, tailWord_1227395, baseEnd_1227395] using wordTrace_append hprefix tailTrace_1227395
  have hstable : (prefixWord ++ tailWord_1227395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1227395).length < 2 ^ (prefixWord ++ tailWord_1227395).sum := by decide
  have hdescent : baseEnd_1227395 < baseStart_1227395 := by decide
  rcases family_descends (prefixWord ++ tailWord_1227395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1227402 : List Nat := [3, 1, 2, 3, 4, 1, 9]
def baseStart_1227402 : Nat := 118140960795 + 1227402 * 2 ^ 59
def prefixEnd_1227402 : Nat := 4983230072969 + 3 ^ 40 * 1227402 * 2
def baseEnd_1227402 : Nat := 7780829410986568120127

theorem tailTrace_1227402 : CollatzResearch.WordTrace tailWord_1227402 prefixEnd_1227402 7780829410986568120127 := by
  unfold tailWord_1227402
  simp only [CollatzResearch.WordTrace]
  refine ⟨11191757174834913104431115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29844685799559768278482973 11191757174834913104431115)
  ·
    refine ⟨16787635762252369656646673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11191757174834913104431115 16787635762252369656646673)
    ·
      refine ⟨12590726821689277242485005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16787635762252369656646673 12590726821689277242485005)
      ·
        refine ⟨4721522558133478965931877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12590726821689277242485005 4721522558133478965931877)
        ·
          refine ⟨885285479650027306112227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4721522558133478965931877 885285479650027306112227)
          ·
            refine ⟨1327928219475040959168341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 885285479650027306112227 1327928219475040959168341)
            ·
              refine ⟨7780829410986568120127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1327928219475040959168341 7780829410986568120127)
              ·
                rfl

theorem cell23_1227402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 9].length) (baseStart_1227402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1227402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1227402 prefixEnd_1227402 := by exact prefixLift 1227402
  have htrace : WordTrace (prefixWord ++ tailWord_1227402) baseStart_1227402 baseEnd_1227402 := by
    simpa [prefixWord, tailWord_1227402, baseEnd_1227402] using wordTrace_append hprefix tailTrace_1227402
  have hstable : (prefixWord ++ tailWord_1227402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1227402).length < 2 ^ (prefixWord ++ tailWord_1227402).sum := by decide
  have hdescent : baseEnd_1227402 < baseStart_1227402 := by decide
  rcases family_descends (prefixWord ++ tailWord_1227402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1227439 : List Nat := [1, 1, 2, 1, 2, 5, 3, 2, 1, 3, 2]
def baseStart_1227439 : Nat := 118140960795 + 1227439 * 2 ^ 59
def prefixEnd_1227439 : Nat := 4983230072969 + 3 ^ 40 * 1227439 * 2
def baseEnd_1227439 : Nat := 630266181074128372967617

theorem tailTrace_1227439 : CollatzResearch.WordTrace tailWord_1227439 prefixEnd_1227439 630266181074128372967617 := by
  unfold tailWord_1227439
  simp only [CollatzResearch.WordTrace]
  refine ⟨44768378200205607736821371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29845585466803738491214247 44768378200205607736821371)
  ·
    refine ⟨67152567300308411605232057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44768378200205607736821371 67152567300308411605232057)
    ·
      refine ⟨50364425475231308703924043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67152567300308411605232057 50364425475231308703924043)
      ·
        refine ⟨75546638212846963055886065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50364425475231308703924043 75546638212846963055886065)
        ·
          refine ⟨56659978659635222291914549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75546638212846963055886065 56659978659635222291914549)
          ·
            refine ⟨5311872999340802089866989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 56659978659635222291914549 5311872999340802089866989)
            ·
              refine ⟨1991952374752800783700121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5311872999340802089866989 1991952374752800783700121)
              ·
                refine ⟨1493964281064600587775091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1991952374752800783700121 1493964281064600587775091)
                ·
                  refine ⟨2240946421596900881662637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1493964281064600587775091 2240946421596900881662637)
                  ·
                    refine ⟨840354908098837830623489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2240946421596900881662637 840354908098837830623489)
                    ·
                      refine ⟨630266181074128372967617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 840354908098837830623489 630266181074128372967617)
                      ·
                        rfl

theorem cell23_1227439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 3, 2, 1, 3, 2].length) (baseStart_1227439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1227439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1227439 prefixEnd_1227439 := by exact prefixLift 1227439
  have htrace : WordTrace (prefixWord ++ tailWord_1227439) baseStart_1227439 baseEnd_1227439 := by
    simpa [prefixWord, tailWord_1227439, baseEnd_1227439] using wordTrace_append hprefix tailTrace_1227439
  have hstable : (prefixWord ++ tailWord_1227439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1227439).length < 2 ^ (prefixWord ++ tailWord_1227439).sum := by decide
  have hdescent : baseEnd_1227439 < baseStart_1227439 := by decide
  rcases family_descends (prefixWord ++ tailWord_1227439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1227446 : List Nat := [5, 1, 3, 1, 2, 1, 1, 2, 1, 3, 3]
def baseStart_1227446 : Nat := 118140960795 + 1227446 * 2 ^ 59
def prefixEnd_1227446 : Nat := 4983230072969 + 3 ^ 40 * 1227446 * 2
def baseEnd_1227446 : Nat := 630269775438709845580085

theorem tailTrace_1227446 : CollatzResearch.WordTrace tailWord_1227446 prefixEnd_1227446 630269775438709845580085 := by
  unfold tailWord_1227446
  simp only [CollatzResearch.WordTrace]
  refine ⟨2798039594448765495770387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 29845755674120165288217461 2798039594448765495770387)
  ·
    refine ⟨4197059391673148243655581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2798039594448765495770387 4197059391673148243655581)
    ·
      refine ⟨1573897271877430591370843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4197059391673148243655581 1573897271877430591370843)
      ·
        refine ⟨2360845907816145887056265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1573897271877430591370843 2360845907816145887056265)
        ·
          refine ⟨1770634430862109415292199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2360845907816145887056265 1770634430862109415292199)
          ·
            refine ⟨2655951646293164122938299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1770634430862109415292199 2655951646293164122938299)
            ·
              refine ⟨3983927469439746184407449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2655951646293164122938299 3983927469439746184407449)
              ·
                refine ⟨2987945602079809638305587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3983927469439746184407449 2987945602079809638305587)
                ·
                  refine ⟨4481918403119714457458381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2987945602079809638305587 4481918403119714457458381)
                  ·
                    refine ⟨1680719401169892921546893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4481918403119714457458381 1680719401169892921546893)
                    ·
                      refine ⟨630269775438709845580085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1680719401169892921546893 630269775438709845580085)
                      ·
                        rfl

theorem cell23_1227446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_1227446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1227446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1227446 prefixEnd_1227446 := by exact prefixLift 1227446
  have htrace : WordTrace (prefixWord ++ tailWord_1227446) baseStart_1227446 baseEnd_1227446 := by
    simpa [prefixWord, tailWord_1227446, baseEnd_1227446] using wordTrace_append hprefix tailTrace_1227446
  have hstable : (prefixWord ++ tailWord_1227446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1227446).length < 2 ^ (prefixWord ++ tailWord_1227446).sum := by decide
  have hdescent : baseEnd_1227446 < baseStart_1227446 := by decide
  rcases family_descends (prefixWord ++ tailWord_1227446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1227455 : List Nat := [1, 1, 2, 2, 2, 4, 2, 1, 2, 1, 5]
def baseStart_1227455 : Nat := 118140960795 + 1227455 * 2 ^ 59
def prefixEnd_1227455 : Nat := 4983230072969 + 3 ^ 40 * 1227455 * 2
def baseEnd_1227455 : Nat := 630274396764600310367543

theorem tailTrace_1227455 : CollatzResearch.WordTrace tailWord_1227455 prefixEnd_1227455 630274396764600310367543 := by
  unfold tailWord_1227455
  simp only [CollatzResearch.WordTrace]
  refine ⟨44768961768147642469403819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29845974512098428312935879 44768961768147642469403819)
  ·
    refine ⟨67153442652221463704105729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44768961768147642469403819 67153442652221463704105729)
    ·
      refine ⟨50365081989166097778079297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67153442652221463704105729 50365081989166097778079297)
      ·
        refine ⟨37773811491874573333559473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50365081989166097778079297 37773811491874573333559473)
        ·
          refine ⟨28330358618905930000169605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37773811491874573333559473 28330358618905930000169605)
          ·
            refine ⟨5311942241044861875031801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28330358618905930000169605 5311942241044861875031801)
            ·
              refine ⟨3983956680783646406273851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5311942241044861875031801 3983956680783646406273851)
              ·
                refine ⟨5975935021175469609410777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3983956680783646406273851 5975935021175469609410777)
                ·
                  refine ⟨4481951265881602207058083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5975935021175469609410777 4481951265881602207058083)
                  ·
                    refine ⟨6722926898822403310587125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4481951265881602207058083 6722926898822403310587125)
                    ·
                      refine ⟨630274396764600310367543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6722926898822403310587125 630274396764600310367543)
                      ·
                        rfl

theorem cell23_1227455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 1, 2, 1, 5].length) (baseStart_1227455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1227455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1227455 prefixEnd_1227455 := by exact prefixLift 1227455
  have htrace : WordTrace (prefixWord ++ tailWord_1227455) baseStart_1227455 baseEnd_1227455 := by
    simpa [prefixWord, tailWord_1227455, baseEnd_1227455] using wordTrace_append hprefix tailTrace_1227455
  have hstable : (prefixWord ++ tailWord_1227455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1227455).length < 2 ^ (prefixWord ++ tailWord_1227455).sum := by decide
  have hdescent : baseEnd_1227455 < baseStart_1227455 := by decide
  rcases family_descends (prefixWord ++ tailWord_1227455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1227456 : List Nat := [2, 1, 1, 2, 4, 3, 3, 1, 1, 3, 2]
def baseStart_1227456 : Nat := 118140960795 + 1227456 * 2 ^ 59
def prefixEnd_1227456 : Nat := 4983230072969 + 3 ^ 40 * 1227456 * 2
def baseEnd_1227456 : Nat := 630274910245254806455039

theorem tailTrace_1227456 : CollatzResearch.WordTrace tailWord_1227456 prefixEnd_1227456 630274910245254806455039 := by
  unfold tailWord_1227456
  simp only [CollatzResearch.WordTrace]
  refine ⟨22384499120572009820095111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29845998827429346426793481 22384499120572009820095111)
  ·
    refine ⟨33576748680858014730142667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22384499120572009820095111 33576748680858014730142667)
    ·
      refine ⟨50365123021287022095214001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33576748680858014730142667 50365123021287022095214001)
      ·
        refine ⟨37773842265965266571410501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50365123021287022095214001 37773842265965266571410501)
        ·
          refine ⟨7082595424868487482139469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37773842265965266571410501 7082595424868487482139469)
          ·
            refine ⟨2655973284325682805802301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7082595424868487482139469 2655973284325682805802301)
            ·
              refine ⟨995989981622131052175863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2655973284325682805802301 995989981622131052175863)
              ·
                refine ⟨1493984972433196578263795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 995989981622131052175863 1493984972433196578263795)
                ·
                  refine ⟨2240977458649794867395693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1493984972433196578263795 2240977458649794867395693)
                  ·
                    refine ⟨840366546993673075273385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2240977458649794867395693 840366546993673075273385)
                    ·
                      refine ⟨630274910245254806455039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 840366546993673075273385 630274910245254806455039)
                      ·
                        rfl

theorem cell23_1227456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 3, 1, 1, 3, 2].length) (baseStart_1227456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1227456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1227456 prefixEnd_1227456 := by exact prefixLift 1227456
  have htrace : WordTrace (prefixWord ++ tailWord_1227456) baseStart_1227456 baseEnd_1227456 := by
    simpa [prefixWord, tailWord_1227456, baseEnd_1227456] using wordTrace_append hprefix tailTrace_1227456
  have hstable : (prefixWord ++ tailWord_1227456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1227456).length < 2 ^ (prefixWord ++ tailWord_1227456).sum := by decide
  have hdescent : baseEnd_1227456 < baseStart_1227456 := by decide
  rcases family_descends (prefixWord ++ tailWord_1227456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1227505 : List Nat := [1, 2, 2, 2, 2, 2, 3, 1, 1, 7]
def baseStart_1227505 : Nat := 118140960795 + 1227505 * 2 ^ 59
def prefixEnd_1227505 : Nat := 4983230072969 + 3 ^ 40 * 1227505 * 2
def baseEnd_1227505 : Nat := 210100023599108371580771

theorem tailTrace_1227505 : CollatzResearch.WordTrace tailWord_1227505 prefixEnd_1227505 210100023599108371580771 := by
  unfold tailWord_1227505
  simp only [CollatzResearch.WordTrace]
  refine ⟨44770785417966501008723969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29847190278644334005815979 44770785417966501008723969)
  ·
    refine ⟨33578089063474875756542977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44770785417966501008723969 33578089063474875756542977)
    ·
      refine ⟨25183566797606156817407233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33578089063474875756542977 25183566797606156817407233)
      ·
        refine ⟨18887675098204617613055425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25183566797606156817407233 18887675098204617613055425)
        ·
          refine ⟨14165756323653463209791569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18887675098204617613055425 14165756323653463209791569)
          ·
            refine ⟨10624317242740097407343677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14165756323653463209791569 10624317242740097407343677)
            ·
              refine ⟨3984118966027536527753879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10624317242740097407343677 3984118966027536527753879)
              ·
                refine ⟨5976178449041304791630819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3984118966027536527753879 5976178449041304791630819)
                ·
                  refine ⟨8964267673561957187446229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5976178449041304791630819 8964267673561957187446229)
                  ·
                    refine ⟨210100023599108371580771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8964267673561957187446229 210100023599108371580771)
                    ·
                      rfl

theorem cell23_1227505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 1, 1, 7].length) (baseStart_1227505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1227505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1227505 prefixEnd_1227505 := by exact prefixLift 1227505
  have htrace : WordTrace (prefixWord ++ tailWord_1227505) baseStart_1227505 baseEnd_1227505 := by
    simpa [prefixWord, tailWord_1227505, baseEnd_1227505] using wordTrace_append hprefix tailTrace_1227505
  have hstable : (prefixWord ++ tailWord_1227505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1227505).length < 2 ^ (prefixWord ++ tailWord_1227505).sum := by decide
  have hdescent : baseEnd_1227505 < baseStart_1227505 := by decide
  rcases family_descends (prefixWord ++ tailWord_1227505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1227555 : List Nat := [1, 1, 1, 4, 2, 1, 1, 1, 1, 6, 4]
def baseStart_1227555 : Nat := 118140960795 + 1227555 * 2 ^ 59
def prefixEnd_1227555 : Nat := 4983230072969 + 3 ^ 40 * 1227555 * 2
def baseEnd_1227555 : Nat := 630325744830049919117083

theorem tailTrace_1227555 : CollatzResearch.WordTrace tailWord_1227555 prefixEnd_1227555 630325744830049919117083 := by
  unfold tailWord_1227555
  simp only [CollatzResearch.WordTrace]
  refine ⟨44772609067785359548044119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29848406045190239698696079 44772609067785359548044119)
  ·
    refine ⟨67158913601678039322066179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44772609067785359548044119 67158913601678039322066179)
    ·
      refine ⟨100738370402517058983099269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67158913601678039322066179 100738370402517058983099269)
      ·
        refine ⟨18888444450471948559331113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 100738370402517058983099269 18888444450471948559331113)
        ·
          refine ⟨14166333337853961419498335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18888444450471948559331113 14166333337853961419498335)
          ·
            refine ⟨21249500006780942129247503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14166333337853961419498335 21249500006780942129247503)
            ·
              refine ⟨31874250010171413193871255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21249500006780942129247503 31874250010171413193871255)
              ·
                refine ⟨47811375015257119790806883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31874250010171413193871255 47811375015257119790806883)
                ·
                  refine ⟨71717062522885679686210325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47811375015257119790806883 71717062522885679686210325)
                  ·
                    refine ⟨3361737305760266235291109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 71717062522885679686210325 3361737305760266235291109)
                    ·
                      refine ⟨630325744830049919117083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3361737305760266235291109 630325744830049919117083)
                      ·
                        rfl

theorem cell23_1227555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 6, 4].length) (baseStart_1227555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1227555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1227555 prefixEnd_1227555 := by exact prefixLift 1227555
  have htrace : WordTrace (prefixWord ++ tailWord_1227555) baseStart_1227555 baseEnd_1227555 := by
    simpa [prefixWord, tailWord_1227555, baseEnd_1227555] using wordTrace_append hprefix tailTrace_1227555
  have hstable : (prefixWord ++ tailWord_1227555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1227555).length < 2 ^ (prefixWord ++ tailWord_1227555).sum := by decide
  have hdescent : baseEnd_1227555 < baseStart_1227555 := by decide
  rcases family_descends (prefixWord ++ tailWord_1227555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1227643 : List Nat := [1, 1, 1, 1, 1, 5, 6, 2, 1, 1, 3]
def baseStart_1227643 : Nat := 118140960795 + 1227643 * 2 ^ 59
def prefixEnd_1227643 : Nat := 4983230072969 + 3 ^ 40 * 1227643 * 2
def baseEnd_1227643 : Nat := 630370931127645574816679

theorem tailTrace_1227643 : CollatzResearch.WordTrace tailWord_1227643 prefixEnd_1227643 630370931127645574816679 := by
  unfold tailWord_1227643
  simp only [CollatzResearch.WordTrace]
  refine ⟨44775818691466550577247583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29850545794311033718165055 44775818691466550577247583)
  ·
    refine ⟨67163728037199825865871375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44775818691466550577247583 67163728037199825865871375)
    ·
      refine ⟨100745592055799738798807063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67163728037199825865871375 100745592055799738798807063)
      ·
        refine ⟨151118388083699608198210595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100745592055799738798807063 151118388083699608198210595)
        ·
          refine ⟨226677582125549412297315893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151118388083699608198210595 226677582125549412297315893)
          ·
            refine ⟨21251023324270257402873365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 226677582125549412297315893 21251023324270257402873365)
            ·
              refine ⟨996141718325168315759689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 21251023324270257402873365 996141718325168315759689)
              ·
                refine ⟨747106288743876236819767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 996141718325168315759689 747106288743876236819767)
                ·
                  refine ⟨1120659433115814355229651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 747106288743876236819767 1120659433115814355229651)
                  ·
                    refine ⟨1680989149673721532844477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1120659433115814355229651 1680989149673721532844477)
                    ·
                      refine ⟨630370931127645574816679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1680989149673721532844477 630370931127645574816679)
                      ·
                        rfl

theorem cell23_1227643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 6, 2, 1, 1, 3].length) (baseStart_1227643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1227643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1227643 prefixEnd_1227643 := by exact prefixLift 1227643
  have htrace : WordTrace (prefixWord ++ tailWord_1227643) baseStart_1227643 baseEnd_1227643 := by
    simpa [prefixWord, tailWord_1227643, baseEnd_1227643] using wordTrace_append hprefix tailTrace_1227643
  have hstable : (prefixWord ++ tailWord_1227643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1227643).length < 2 ^ (prefixWord ++ tailWord_1227643).sum := by decide
  have hdescent : baseEnd_1227643 < baseStart_1227643 := by decide
  rcases family_descends (prefixWord ++ tailWord_1227643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1227652 : List Nat := [2, 3, 2, 1, 1, 1, 1, 3, 3, 1, 5]
def baseStart_1227652 : Nat := 118140960795 + 1227652 * 2 ^ 59
def prefixEnd_1227652 : Nat := 4983230072969 + 3 ^ 40 * 1227652 * 2
def baseEnd_1227652 : Nat := 630375552453536039604137

theorem tailTrace_1227652 : CollatzResearch.WordTrace tailWord_1227652 prefixEnd_1227652 630375552453536039604137 := by
  unfold tailWord_1227652
  simp only [CollatzResearch.WordTrace]
  refine ⟨22388073474216972557162605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29850764632289296742883473 22388073474216972557162605)
  ·
    refine ⟨8395527552831364708935977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22388073474216972557162605 8395527552831364708935977)
    ·
      refine ⟨6296645664623523531701983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8395527552831364708935977 6296645664623523531701983)
      ·
        refine ⟨9444968496935285297552975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6296645664623523531701983 9444968496935285297552975)
        ·
          refine ⟨14167452745402927946329463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9444968496935285297552975 14167452745402927946329463)
          ·
            refine ⟨21251179118104391919494195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14167452745402927946329463 21251179118104391919494195)
            ·
              refine ⟨31876768677156587879241293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21251179118104391919494195 31876768677156587879241293)
              ·
                refine ⟨11953788253933720454715485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31876768677156587879241293 11953788253933720454715485)
                ·
                  refine ⟨4482670595225145170518307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11953788253933720454715485 4482670595225145170518307)
                  ·
                    refine ⟨6724005892837717755777461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4482670595225145170518307 6724005892837717755777461)
                    ·
                      refine ⟨630375552453536039604137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6724005892837717755777461 630375552453536039604137)
                      ·
                        rfl

theorem cell23_1227652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 3, 3, 1, 5].length) (baseStart_1227652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1227652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1227652 prefixEnd_1227652 := by exact prefixLift 1227652
  have htrace : WordTrace (prefixWord ++ tailWord_1227652) baseStart_1227652 baseEnd_1227652 := by
    simpa [prefixWord, tailWord_1227652, baseEnd_1227652] using wordTrace_append hprefix tailTrace_1227652
  have hstable : (prefixWord ++ tailWord_1227652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1227652).length < 2 ^ (prefixWord ++ tailWord_1227652).sum := by decide
  have hdescent : baseEnd_1227652 < baseStart_1227652 := by decide
  rcases family_descends (prefixWord ++ tailWord_1227652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1227659 : List Nat := [1, 1, 1, 1, 4, 2, 4, 3, 2, 4]
def baseStart_1227659 : Nat := 118140960795 + 1227659 * 2 ^ 59
def prefixEnd_1227659 : Nat := 4983230072969 + 3 ^ 40 * 1227659 * 2
def baseEnd_1227659 : Nat := 210126382272705837405535

theorem tailTrace_1227659 : CollatzResearch.WordTrace tailWord_1227659 prefixEnd_1227659 210126382272705837405535 := by
  unfold tailWord_1227659
  simp only [CollatzResearch.WordTrace]
  refine ⟨44776402259408585309830031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29850934839605723539886687 44776402259408585309830031)
  ·
    refine ⟨67164603389112877964745047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44776402259408585309830031 67164603389112877964745047)
    ·
      refine ⟨100746905083669316947117571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67164603389112877964745047 100746905083669316947117571)
      ·
        refine ⟨151120357625503975420676357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100746905083669316947117571 151120357625503975420676357)
        ·
          refine ⟨28335067054781995391376817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 151120357625503975420676357 28335067054781995391376817)
          ·
            refine ⟨21251300291086496543532613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28335067054781995391376817 21251300291086496543532613)
            ·
              refine ⟨3984618804578718101912365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21251300291086496543532613 3984618804578718101912365)
              ·
                refine ⟨1494232051717019288217137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3984618804578718101912365 1494232051717019288217137)
                ·
                  refine ⟨1120674038787764466162853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1494232051717019288217137 1120674038787764466162853)
                  ·
                    refine ⟨210126382272705837405535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1120674038787764466162853 210126382272705837405535)
                    ·
                      rfl

theorem cell23_1227659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 3, 2, 4].length) (baseStart_1227659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1227659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1227659 prefixEnd_1227659 := by exact prefixLift 1227659
  have htrace : WordTrace (prefixWord ++ tailWord_1227659) baseStart_1227659 baseEnd_1227659 := by
    simpa [prefixWord, tailWord_1227659, baseEnd_1227659] using wordTrace_append hprefix tailTrace_1227659
  have hstable : (prefixWord ++ tailWord_1227659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1227659).length < 2 ^ (prefixWord ++ tailWord_1227659).sum := by decide
  have hdescent : baseEnd_1227659 < baseStart_1227659 := by decide
  rcases family_descends (prefixWord ++ tailWord_1227659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1227669 : List Nat := [1, 3, 2, 1, 1, 4, 2, 1, 3, 2, 3]
def baseStart_1227669 : Nat := 118140960795 + 1227669 * 2 ^ 59
def prefixEnd_1227669 : Nat := 4983230072969 + 3 ^ 40 * 1227669 * 2
def baseEnd_1227669 : Nat := 630384281624662473091559

theorem tailTrace_1227669 : CollatzResearch.WordTrace tailWord_1227669 prefixEnd_1227669 630384281624662473091559 := by
  unfold tailWord_1227669
  simp only [CollatzResearch.WordTrace]
  refine ⟨44776766989372357017694061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29851177992914904678462707 44776766989372357017694061)
  ·
    refine ⟨16791287621014633881635273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44776766989372357017694061 16791287621014633881635273)
    ·
      refine ⟨12593465715760975411226455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16791287621014633881635273 12593465715760975411226455)
      ·
        refine ⟨18890198573641463116839683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12593465715760975411226455 18890198573641463116839683)
        ·
          refine ⟨28335297860462194675259525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18890198573641463116839683 28335297860462194675259525)
          ·
            refine ⟨5312868348836661501611161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28335297860462194675259525 5312868348836661501611161)
            ·
              refine ⟨3984651261627496126208371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5312868348836661501611161 3984651261627496126208371)
              ·
                refine ⟨5976976892441244189312557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3984651261627496126208371 5976976892441244189312557)
                ·
                  refine ⟨2241366334665466570992209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5976976892441244189312557 2241366334665466570992209)
                  ·
                    refine ⟨1681024750999099928244157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2241366334665466570992209 1681024750999099928244157)
                    ·
                      refine ⟨630384281624662473091559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1681024750999099928244157 630384281624662473091559)
                      ·
                        rfl

theorem cell23_1227669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 1, 3, 2, 3].length) (baseStart_1227669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1227669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1227669 prefixEnd_1227669 := by exact prefixLift 1227669
  have htrace : WordTrace (prefixWord ++ tailWord_1227669) baseStart_1227669 baseEnd_1227669 := by
    simpa [prefixWord, tailWord_1227669, baseEnd_1227669] using wordTrace_append hprefix tailTrace_1227669
  have hstable : (prefixWord ++ tailWord_1227669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1227669).length < 2 ^ (prefixWord ++ tailWord_1227669).sum := by decide
  have hdescent : baseEnd_1227669 < baseStart_1227669 := by decide
  rcases family_descends (prefixWord ++ tailWord_1227669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1227670 : List Nat := [5, 3, 1, 1, 1, 2, 1, 1, 1, 5, 2]
def baseStart_1227670 : Nat := 118140960795 + 1227670 * 2 ^ 59
def prefixEnd_1227670 : Nat := 4983230072969 + 3 ^ 40 * 1227670 * 2
def baseEnd_1227670 : Nat := 630384795105316969179055

theorem tailTrace_1227670 : CollatzResearch.WordTrace tailWord_1227670 prefixEnd_1227670 630384795105316969179055 := by
  unfold tailWord_1227670
  simp only [CollatzResearch.WordTrace]
  refine ⟨2798550216398045886780029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 29851202308245822792320309 2798550216398045886780029)
  ·
    refine ⟨1049456331149267207542511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2798550216398045886780029 1049456331149267207542511)
    ·
      refine ⟨1574184496723900811313767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1049456331149267207542511 1574184496723900811313767)
      ·
        refine ⟨2361276745085851216970651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1574184496723900811313767 2361276745085851216970651)
        ·
          refine ⟨3541915117628776825455977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2361276745085851216970651 3541915117628776825455977)
          ·
            refine ⟨2656436338221582619091983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3541915117628776825455977 2656436338221582619091983)
            ·
              refine ⟨3984654507332373928637975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2656436338221582619091983 3984654507332373928637975)
              ·
                refine ⟨5976981760998560892956963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3984654507332373928637975 5976981760998560892956963)
                ·
                  refine ⟨8965472641497841339435445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5976981760998560892956963 8965472641497841339435445)
                  ·
                    refine ⟨840513060140422625572073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8965472641497841339435445 840513060140422625572073)
                    ·
                      refine ⟨630384795105316969179055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 840513060140422625572073 630384795105316969179055)
                      ·
                        rfl

theorem cell23_1227670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 1, 1, 5, 2].length) (baseStart_1227670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1227670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1227670 prefixEnd_1227670 := by exact prefixLift 1227670
  have htrace : WordTrace (prefixWord ++ tailWord_1227670) baseStart_1227670 baseEnd_1227670 := by
    simpa [prefixWord, tailWord_1227670, baseEnd_1227670] using wordTrace_append hprefix tailTrace_1227670
  have hstable : (prefixWord ++ tailWord_1227670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1227670).length < 2 ^ (prefixWord ++ tailWord_1227670).sum := by decide
  have hdescent : baseEnd_1227670 < baseStart_1227670 := by decide
  rcases family_descends (prefixWord ++ tailWord_1227670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1227679 : List Nat := [1, 1, 2, 5, 2, 1, 2, 2, 1, 2, 4]
def baseStart_1227679 : Nat := 118140960795 + 1227679 * 2 ^ 59
def prefixEnd_1227679 : Nat := 4983230072969 + 3 ^ 40 * 1227679 * 2
def baseEnd_1227679 : Nat := 630389416431207433966513

theorem tailTrace_1227679 : CollatzResearch.WordTrace tailWord_1227679 prefixEnd_1227679 630389416431207433966513 := by
  unfold tailWord_1227679
  simp only [CollatzResearch.WordTrace]
  refine ⟨44777131719336128725558091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29851421146224085817038727 44777131719336128725558091)
  ·
    refine ⟨67165697579004193088337137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44777131719336128725558091 67165697579004193088337137)
    ·
      refine ⟨50374273184253144816252853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67165697579004193088337137 50374273184253144816252853)
      ·
        refine ⟨4722588111023732326523705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 50374273184253144816252853 4722588111023732326523705)
        ·
          refine ⟨3541941083267799244892779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4722588111023732326523705 3541941083267799244892779)
          ·
            refine ⟨5312911624901698867339169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3541941083267799244892779 5312911624901698867339169)
            ·
              refine ⟨3984683718676274150504377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5312911624901698867339169 3984683718676274150504377)
              ·
                refine ⟨2988512789007205612878283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3984683718676274150504377 2988512789007205612878283)
                ·
                  refine ⟨4482769183510808419317425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2988512789007205612878283 4482769183510808419317425)
                  ·
                    refine ⟨3362076887633106314488069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4482769183510808419317425 3362076887633106314488069)
                    ·
                      refine ⟨630389416431207433966513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3362076887633106314488069 630389416431207433966513)
                      ·
                        rfl

theorem cell23_1227679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_1227679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1227679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1227679 prefixEnd_1227679 := by exact prefixLift 1227679
  have htrace : WordTrace (prefixWord ++ tailWord_1227679) baseStart_1227679 baseEnd_1227679 := by
    simpa [prefixWord, tailWord_1227679, baseEnd_1227679] using wordTrace_append hprefix tailTrace_1227679
  have hstable : (prefixWord ++ tailWord_1227679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1227679).length < 2 ^ (prefixWord ++ tailWord_1227679).sum := by decide
  have hdescent : baseEnd_1227679 < baseStart_1227679 := by decide
  rcases family_descends (prefixWord ++ tailWord_1227679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1227683 : List Nat := [1, 1, 1, 4, 1, 2, 3, 5, 1, 2, 2]
def baseStart_1227683 : Nat := 118140960795 + 1227683 * 2 ^ 59
def prefixEnd_1227683 : Nat := 4983230072969 + 3 ^ 40 * 1227683 * 2
def baseEnd_1227683 : Nat := 630391470353825418316495

theorem tailTrace_1227683 : CollatzResearch.WordTrace tailWord_1227683 prefixEnd_1227683 630391470353825418316495 := by
  unfold tailWord_1227683
  simp only [CollatzResearch.WordTrace]
  refine ⟨44777277611321637408703703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29851518407547758272469135 44777277611321637408703703)
  ·
    refine ⟨67165916416982456113055555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44777277611321637408703703 67165916416982456113055555)
    ·
      refine ⟨100748874625473684169583333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67165916416982456113055555 100748874625473684169583333)
      ·
        refine ⟨18890413992276315781796875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 100748874625473684169583333 18890413992276315781796875)
        ·
          refine ⟨28335620988414473672695313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18890413992276315781796875 28335620988414473672695313)
          ·
            refine ⟨21251715741310855254521485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28335620988414473672695313 21251715741310855254521485)
            ·
              refine ⟨7969393402991570720445557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21251715741310855254521485 7969393402991570720445557)
              ·
                refine ⟨747130631530459755041771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7969393402991570720445557 747130631530459755041771)
                ·
                  refine ⟨1120695947295689632562657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 747130631530459755041771 1120695947295689632562657)
                  ·
                    refine ⟨840521960471767224421993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1120695947295689632562657 840521960471767224421993)
                    ·
                      refine ⟨630391470353825418316495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 840521960471767224421993 630391470353825418316495)
                      ·
                        rfl

theorem cell23_1227683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 5, 1, 2, 2].length) (baseStart_1227683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1227683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1227683 prefixEnd_1227683 := by exact prefixLift 1227683
  have htrace : WordTrace (prefixWord ++ tailWord_1227683) baseStart_1227683 baseEnd_1227683 := by
    simpa [prefixWord, tailWord_1227683, baseEnd_1227683] using wordTrace_append hprefix tailTrace_1227683
  have hstable : (prefixWord ++ tailWord_1227683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1227683).length < 2 ^ (prefixWord ++ tailWord_1227683).sum := by decide
  have hdescent : baseEnd_1227683 < baseStart_1227683 := by decide
  rcases family_descends (prefixWord ++ tailWord_1227683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1227693 : List Nat := [1, 5, 2, 3, 1, 1, 1, 1, 4, 4]
def baseStart_1227693 : Nat := 118140960795 + 1227693 * 2 ^ 59
def prefixEnd_1227693 : Nat := 4983230072969 + 3 ^ 40 * 1227693 * 2
def baseEnd_1227693 : Nat := 210132201720123459730483

theorem tailTrace_1227693 : CollatzResearch.WordTrace tailWord_1227693 prefixEnd_1227693 210132201720123459730483 := by
  unfold tailWord_1227693
  simp only [CollatzResearch.WordTrace]
  refine ⟨44777642341285409116567733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29851761560856939411045155 44777642341285409116567733)
  ·
    refine ⟨4197903969495507104678225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 44777642341285409116567733 4197903969495507104678225)
    ·
      refine ⟨3148427977121630328508669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4197903969495507104678225 3148427977121630328508669)
      ·
        refine ⟨1180660491420611373190751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3148427977121630328508669 1180660491420611373190751)
        ·
          refine ⟨1770990737130917059786127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1180660491420611373190751 1770990737130917059786127)
          ·
            refine ⟨2656486105696375589679191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1770990737130917059786127 2656486105696375589679191)
            ·
              refine ⟨3984729158544563384518787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2656486105696375589679191 3984729158544563384518787)
              ·
                refine ⟨5977093737816845076778181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3984729158544563384518787 5977093737816845076778181)
                ·
                  refine ⟨1120705075840658451895909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5977093737816845076778181 1120705075840658451895909)
                  ·
                    refine ⟨210132201720123459730483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1120705075840658451895909 210132201720123459730483)
                    ·
                      rfl

theorem cell23_1227693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 1, 4, 4].length) (baseStart_1227693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1227693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1227693 prefixEnd_1227693 := by exact prefixLift 1227693
  have htrace : WordTrace (prefixWord ++ tailWord_1227693) baseStart_1227693 baseEnd_1227693 := by
    simpa [prefixWord, tailWord_1227693, baseEnd_1227693] using wordTrace_append hprefix tailTrace_1227693
  have hstable : (prefixWord ++ tailWord_1227693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1227693).length < 2 ^ (prefixWord ++ tailWord_1227693).sum := by decide
  have hdescent : baseEnd_1227693 < baseStart_1227693 := by decide
  rcases family_descends (prefixWord ++ tailWord_1227693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1227700 : List Nat := [2, 5, 2, 1, 1, 1, 1, 3, 3, 2, 2]
def baseStart_1227700 : Nat := 118140960795 + 1227700 * 2 ^ 59
def prefixEnd_1227700 : Nat := 4983230072969 + 3 ^ 40 * 1227700 * 2
def baseEnd_1227700 : Nat := 630400199524951851803917

theorem tailTrace_1227700 : CollatzResearch.WordTrace tailWord_1227700 prefixEnd_1227700 630400199524951851803917 := by
  unfold tailWord_1227700
  simp only [CollatzResearch.WordTrace]
  refine ⟨22388948826130024656036277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29851931768173366208048369 22388948826130024656036277)
  ·
    refine ⟨2098963952449689811503401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22388948826130024656036277 2098963952449689811503401)
    ·
      refine ⟨1574222964337267358627551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2098963952449689811503401 1574222964337267358627551)
      ·
        refine ⟨2361334446505901037941327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1574222964337267358627551 2361334446505901037941327)
        ·
          refine ⟨3542001669758851556911991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2361334446505901037941327 3542001669758851556911991)
          ·
            refine ⟨5313002504638277335367987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3542001669758851556911991 5313002504638277335367987)
            ·
              refine ⟨7969503756957416003051981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5313002504638277335367987 7969503756957416003051981)
              ·
                refine ⟨2988563908859031001144493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7969503756957416003051981 2988563908859031001144493)
                ·
                  refine ⟨1120711465822136625429185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2988563908859031001144493 1120711465822136625429185)
                  ·
                    refine ⟨840533599366602469071889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1120711465822136625429185 840533599366602469071889)
                    ·
                      refine ⟨630400199524951851803917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 840533599366602469071889 630400199524951851803917)
                      ·
                        rfl

theorem cell23_1227700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 3, 3, 2, 2].length) (baseStart_1227700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1227700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1227700 prefixEnd_1227700 := by exact prefixLift 1227700
  have htrace : WordTrace (prefixWord ++ tailWord_1227700) baseStart_1227700 baseEnd_1227700 := by
    simpa [prefixWord, tailWord_1227700, baseEnd_1227700] using wordTrace_append hprefix tailTrace_1227700
  have hstable : (prefixWord ++ tailWord_1227700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1227700).length < 2 ^ (prefixWord ++ tailWord_1227700).sum := by decide
  have hdescent : baseEnd_1227700 < baseStart_1227700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1227700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1227734 : List Nat := [5, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2]
def baseStart_1227734 : Nat := 118140960795 + 1227734 * 2 ^ 59
def prefixEnd_1227734 : Nat := 4983230072969 + 3 ^ 40 * 1227734 * 2
def baseEnd_1227734 : Nat := 630417657867204718778761

theorem tailTrace_1227734 : CollatzResearch.WordTrace tailWord_1227734 prefixEnd_1227734 630417657867204718778761 := by
  unfold tailWord_1227734
  simp only [CollatzResearch.WordTrace]
  refine ⟨2798696108383554569925641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 29852758489424582079206837 2798696108383554569925641)
  ·
    refine ⟨2099022081287665927444231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2798696108383554569925641 2099022081287665927444231)
    ·
      refine ⟨3148533121931498891166347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2099022081287665927444231 3148533121931498891166347)
      ·
        refine ⟨4722799682897248336749521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3148533121931498891166347 4722799682897248336749521)
        ·
          refine ⟨3542099762172936252562141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4722799682897248336749521 3542099762172936252562141)
          ·
            refine ⟨1328287410814851094710803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3542099762172936252562141 1328287410814851094710803)
            ·
              refine ⟨1992431116222276642066205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1328287410814851094710803 1992431116222276642066205)
              ·
                refine ⟨747161668583353740774827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1992431116222276642066205 747161668583353740774827)
                ·
                  refine ⟨1120742502875030611162241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 747161668583353740774827 1120742502875030611162241)
                  ·
                    refine ⟨840556877156272958371681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1120742502875030611162241 840556877156272958371681)
                    ·
                      refine ⟨630417657867204718778761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 840556877156272958371681 630417657867204718778761)
                      ·
                        rfl

theorem cell23_1227734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2].length) (baseStart_1227734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1227734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1227734 prefixEnd_1227734 := by exact prefixLift 1227734
  have htrace : WordTrace (prefixWord ++ tailWord_1227734) baseStart_1227734 baseEnd_1227734 := by
    simpa [prefixWord, tailWord_1227734, baseEnd_1227734] using wordTrace_append hprefix tailTrace_1227734
  have hstable : (prefixWord ++ tailWord_1227734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1227734).length < 2 ^ (prefixWord ++ tailWord_1227734).sum := by decide
  have hdescent : baseEnd_1227734 < baseStart_1227734 := by decide
  rcases family_descends (prefixWord ++ tailWord_1227734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1227829 : List Nat := [1, 3, 3, 1, 1, 1, 1, 4, 1, 3, 4]
def baseStart_1227829 : Nat := 118140960795 + 1227829 * 2 ^ 59
def prefixEnd_1227829 : Nat := 4983230072969 + 3 ^ 40 * 1227829 * 2
def baseEnd_1227829 : Nat := 630466438529381847090823

theorem tailTrace_1227829 : CollatzResearch.WordTrace tailWord_1227829 prefixEnd_1227829 630466438529381847090823 := by
  unfold tailWord_1227829
  simp only [CollatzResearch.WordTrace]
  refine ⟨44782602668792704343518541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29855068445861802895679027 44782602668792704343518541)
  ·
    refine ⟨16793476000797264128819453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44782602668792704343518541 16793476000797264128819453)
    ·
      refine ⟨6297553500298974048307295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16793476000797264128819453 6297553500298974048307295)
      ·
        refine ⟨9446330250448461072460943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6297553500298974048307295 9446330250448461072460943)
        ·
          refine ⟨14169495375672691608691415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9446330250448461072460943 14169495375672691608691415)
          ·
            refine ⟨21254243063509037413037123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14169495375672691608691415 21254243063509037413037123)
            ·
              refine ⟨31881364595263556119555685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21254243063509037413037123 31881364595263556119555685)
              ·
                refine ⟨5977755861611916772416691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31881364595263556119555685 5977755861611916772416691)
                ·
                  refine ⟨8966633792417875158625037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5977755861611916772416691 8966633792417875158625037)
                  ·
                    refine ⟨3362487672156703184484389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8966633792417875158625037 3362487672156703184484389)
                    ·
                      refine ⟨630466438529381847090823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3362487672156703184484389 630466438529381847090823)
                      ·
                        rfl

theorem cell23_1227829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 4, 1, 3, 4].length) (baseStart_1227829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1227829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1227829 prefixEnd_1227829 := by exact prefixLift 1227829
  have htrace : WordTrace (prefixWord ++ tailWord_1227829) baseStart_1227829 baseEnd_1227829 := by
    simpa [prefixWord, tailWord_1227829, baseEnd_1227829] using wordTrace_append hprefix tailTrace_1227829
  have hstable : (prefixWord ++ tailWord_1227829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1227829).length < 2 ^ (prefixWord ++ tailWord_1227829).sum := by decide
  have hdescent : baseEnd_1227829 < baseStart_1227829 := by decide
  rcases family_descends (prefixWord ++ tailWord_1227829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1227873 : List Nat := [1, 2, 3, 1, 1, 2, 4, 4, 1, 4]
def baseStart_1227873 : Nat := 118140960795 + 1227873 * 2 ^ 59
def prefixEnd_1227873 : Nat := 4983230072969 + 3 ^ 40 * 1227873 * 2
def baseEnd_1227873 : Nat := 210163010559393224980207

theorem tailTrace_1227873 : CollatzResearch.WordTrace tailWord_1227873 prefixEnd_1227873 210163010559393224980207 := by
  unfold tailWord_1227873
  simp only [CollatzResearch.WordTrace]
  refine ⟨44784207480633299858120273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29856138320422199905413515 44784207480633299858120273)
  ·
    refine ⟨33588155610474974893590205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44784207480633299858120273 33588155610474974893590205)
    ·
      refine ⟨12595558353928115585096327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33588155610474974893590205 12595558353928115585096327)
      ·
        refine ⟨18893337530892173377644491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12595558353928115585096327 18893337530892173377644491)
        ·
          refine ⟨28340006296338260066466737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18893337530892173377644491 28340006296338260066466737)
          ·
            refine ⟨21255004722253695049850053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28340006296338260066466737 21255004722253695049850053)
            ·
              refine ⟨3985313385422567821846885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21255004722253695049850053 3985313385422567821846885)
              ·
                refine ⟨747246259766731466596291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3985313385422567821846885 747246259766731466596291)
                ·
                  refine ⟨1120869389650097199894437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 747246259766731466596291 1120869389650097199894437)
                  ·
                    refine ⟨210163010559393224980207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1120869389650097199894437 210163010559393224980207)
                    ·
                      rfl

theorem cell23_1227873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 4, 1, 4].length) (baseStart_1227873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1227873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1227873 prefixEnd_1227873 := by exact prefixLift 1227873
  have htrace : WordTrace (prefixWord ++ tailWord_1227873) baseStart_1227873 baseEnd_1227873 := by
    simpa [prefixWord, tailWord_1227873, baseEnd_1227873] using wordTrace_append hprefix tailTrace_1227873
  have hstable : (prefixWord ++ tailWord_1227873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1227873).length < 2 ^ (prefixWord ++ tailWord_1227873).sum := by decide
  have hdescent : baseEnd_1227873 < baseStart_1227873 := by decide
  rcases family_descends (prefixWord ++ tailWord_1227873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1227899 : List Nat := [1, 1, 1, 1, 1, 4, 1, 5, 3, 5]
def baseStart_1227899 : Nat := 118140960795 + 1227899 * 2 ^ 59
def prefixEnd_1227899 : Nat := 4983230072969 + 3 ^ 40 * 1227899 * 2
def baseEnd_1227899 : Nat := 210167460725065524405167

theorem tailTrace_1227899 : CollatzResearch.WordTrace tailWord_1227899 prefixEnd_1227899 210167460725065524405167 := by
  unfold tailWord_1227899
  simp only [CollatzResearch.WordTrace]
  refine ⟨44785155778539106298566751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29856770519026070865711167 44785155778539106298566751)
  ·
    refine ⟨67177733667808659447850127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44785155778539106298566751 67177733667808659447850127)
    ·
      refine ⟨100766600501712989171775191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67177733667808659447850127 100766600501712989171775191)
      ·
        refine ⟨151149900752569483757662787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100766600501712989171775191 151149900752569483757662787)
        ·
          refine ⟨226724851128854225636494181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151149900752569483757662787 226724851128854225636494181)
          ·
            refine ⟨42510909586660167306842659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 226724851128854225636494181 42510909586660167306842659)
            ·
              refine ⟨63766364379990250960263989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42510909586660167306842659 63766364379990250960263989)
              ·
                refine ⟨5978096660624086027524749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 63766364379990250960263989 5978096660624086027524749)
                ·
                  refine ⟨2241786247734032260321781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5978096660624086027524749 2241786247734032260321781)
                  ·
                    refine ⟨210167460725065524405167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2241786247734032260321781 210167460725065524405167)
                    ·
                      rfl

theorem cell23_1227899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 5, 3, 5].length) (baseStart_1227899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1227899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1227899 prefixEnd_1227899 := by exact prefixLift 1227899
  have htrace : WordTrace (prefixWord ++ tailWord_1227899) baseStart_1227899 baseEnd_1227899 := by
    simpa [prefixWord, tailWord_1227899, baseEnd_1227899] using wordTrace_append hprefix tailTrace_1227899
  have hstable : (prefixWord ++ tailWord_1227899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1227899).length < 2 ^ (prefixWord ++ tailWord_1227899).sum := by decide
  have hdescent : baseEnd_1227899 < baseStart_1227899 := by decide
  rcases family_descends (prefixWord ++ tailWord_1227899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1227930 : List Nat := [3, 1, 1, 5, 1, 1, 3, 1, 3, 1, 3]
def baseStart_1227930 : Nat := 118140960795 + 1227930 * 2 ^ 59
def prefixEnd_1227930 : Nat := 4983230072969 + 3 ^ 40 * 1227930 * 2
def baseEnd_1227930 : Nat := 630518300075485951927859

theorem tailTrace_1227930 : CollatzResearch.WordTrace tailWord_1227930 prefixEnd_1227930 630518300075485951927859 := by
  unfold tailWord_1227930
  simp only [CollatzResearch.WordTrace]
  refine ⟨11196571610356699648236311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29857524294284532395296829 11196571610356699648236311)
  ·
    refine ⟨16794857415535049472354467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11196571610356699648236311 16794857415535049472354467)
    ·
      refine ⟨25192286123302574208531701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16794857415535049472354467 25192286123302574208531701)
      ·
        refine ⟨2361776824059616332049847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25192286123302574208531701 2361776824059616332049847)
        ·
          refine ⟨3542665236089424498074771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2361776824059616332049847 3542665236089424498074771)
          ·
            refine ⟨5313997854134136747112157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3542665236089424498074771 5313997854134136747112157)
            ·
              refine ⟨1992749195300301280167059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5313997854134136747112157 1992749195300301280167059)
              ·
                refine ⟨2989123792950451920250589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1992749195300301280167059 2989123792950451920250589)
                ·
                  refine ⟨1120921422356419470093971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2989123792950451920250589 1120921422356419470093971)
                  ·
                    refine ⟨1681382133534629205140957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1120921422356419470093971 1681382133534629205140957)
                    ·
                      refine ⟨630518300075485951927859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1681382133534629205140957 630518300075485951927859)
                      ·
                        rfl

theorem cell23_1227930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_1227930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1227930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1227930 prefixEnd_1227930 := by exact prefixLift 1227930
  have htrace : WordTrace (prefixWord ++ tailWord_1227930) baseStart_1227930 baseEnd_1227930 := by
    simpa [prefixWord, tailWord_1227930, baseEnd_1227930] using wordTrace_append hprefix tailTrace_1227930
  have hstable : (prefixWord ++ tailWord_1227930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1227930).length < 2 ^ (prefixWord ++ tailWord_1227930).sum := by decide
  have hdescent : baseEnd_1227930 < baseStart_1227930 := by decide
  rcases family_descends (prefixWord ++ tailWord_1227930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1227936 : List Nat := [2, 1, 1, 4, 2, 1, 2, 2, 3, 1, 4]
def baseStart_1227936 : Nat := 118140960795 + 1227936 * 2 ^ 59
def prefixEnd_1227936 : Nat := 4983230072969 + 3 ^ 40 * 1227936 * 2
def baseEnd_1227936 : Nat := 630521380959412928452831

theorem tailTrace_1227936 : CollatzResearch.WordTrace tailWord_1227936 prefixEnd_1227936 630521380959412928452831 := by
  unfold tailWord_1227936
  simp only [CollatzResearch.WordTrace]
  refine ⟨22393252639702530808831831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29857670186270041078442441 22393252639702530808831831)
  ·
    refine ⟨33589878959553796213247747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22393252639702530808831831 33589878959553796213247747)
    ·
      refine ⟨50384818439330694319871621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33589878959553796213247747 50384818439330694319871621)
      ·
        refine ⟨9447153457374505184975929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50384818439330694319871621 9447153457374505184975929)
        ·
          refine ⟨7085365093030878888731947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9447153457374505184975929 7085365093030878888731947)
          ·
            refine ⟨10628047639546318333097921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7085365093030878888731947 10628047639546318333097921)
            ·
              refine ⟨7971035729659738749823441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10628047639546318333097921 7971035729659738749823441)
              ·
                refine ⟨5978276797244804062367581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7971035729659738749823441 5978276797244804062367581)
                ·
                  refine ⟨2241853798966801523387843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5978276797244804062367581 2241853798966801523387843)
                  ·
                    refine ⟨3362780698450202285081765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2241853798966801523387843 3362780698450202285081765)
                    ·
                      refine ⟨630521380959412928452831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3362780698450202285081765 630521380959412928452831)
                      ·
                        rfl

theorem cell23_1227936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 2, 3, 1, 4].length) (baseStart_1227936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1227936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1227936 prefixEnd_1227936 := by exact prefixLift 1227936
  have htrace : WordTrace (prefixWord ++ tailWord_1227936) baseStart_1227936 baseEnd_1227936 := by
    simpa [prefixWord, tailWord_1227936, baseEnd_1227936] using wordTrace_append hprefix tailTrace_1227936
  have hstable : (prefixWord ++ tailWord_1227936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1227936).length < 2 ^ (prefixWord ++ tailWord_1227936).sum := by decide
  have hdescent : baseEnd_1227936 < baseStart_1227936 := by decide
  rcases family_descends (prefixWord ++ tailWord_1227936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1227953 : List Nat := [1, 2, 2, 5, 1, 2, 1, 1, 3, 1, 4]
def baseStart_1227953 : Nat := 118140960795 + 1227953 * 2 ^ 59
def prefixEnd_1227953 : Nat := 4983230072969 + 3 ^ 40 * 1227953 * 2
def baseEnd_1227953 : Nat := 630530110130539361940253

theorem tailTrace_1227953 : CollatzResearch.WordTrace tailWord_1227953 prefixEnd_1227953 630530110130539361940253 := by
  unfold tailWord_1227953
  simp only [CollatzResearch.WordTrace]
  refine ⟨44787125320343473521032513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29858083546895649014021675 44787125320343473521032513)
  ·
    refine ⟨33590343990257605140774385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44787125320343473521032513 33590343990257605140774385)
    ·
      refine ⟨25192757992693203855580789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33590343990257605140774385 25192757992693203855580789)
      ·
        refine ⟨2361821061814987861460699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25192757992693203855580789 2361821061814987861460699)
        ·
          refine ⟨3542731592722481792191049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2361821061814987861460699 3542731592722481792191049)
          ·
            refine ⟨2657048694541861344143287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3542731592722481792191049 2657048694541861344143287)
            ·
              refine ⟨3985573041812792016214931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2657048694541861344143287 3985573041812792016214931)
              ·
                refine ⟨5978359562719188024322397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3985573041812792016214931 5978359562719188024322397)
                ·
                  refine ⟨2241884836019695509120899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5978359562719188024322397 2241884836019695509120899)
                  ·
                    refine ⟨3362827254029543263681349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2241884836019695509120899 3362827254029543263681349)
                    ·
                      refine ⟨630530110130539361940253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3362827254029543263681349 630530110130539361940253)
                      ·
                        rfl

theorem cell23_1227953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_1227953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1227953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1227953 prefixEnd_1227953 := by exact prefixLift 1227953
  have htrace : WordTrace (prefixWord ++ tailWord_1227953) baseStart_1227953 baseEnd_1227953 := by
    simpa [prefixWord, tailWord_1227953, baseEnd_1227953] using wordTrace_append hprefix tailTrace_1227953
  have hstable : (prefixWord ++ tailWord_1227953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1227953).length < 2 ^ (prefixWord ++ tailWord_1227953).sum := by decide
  have hdescent : baseEnd_1227953 < baseStart_1227953 := by decide
  rcases family_descends (prefixWord ++ tailWord_1227953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1227959 : List Nat := [1, 1, 3, 1, 4, 1, 1, 11]
def baseStart_1227959 : Nat := 118140960795 + 1227959 * 2 ^ 59
def prefixEnd_1227959 : Nat := 4983230072969 + 3 ^ 40 * 1227959 * 2
def baseEnd_1227959 : Nat := 23353081148683938461675

theorem tailTrace_1227959 : CollatzResearch.WordTrace tailWord_1227959 prefixEnd_1227959 23353081148683938461675 := by
  unfold tailWord_1227959
  simp only [CollatzResearch.WordTrace]
  refine ⟨44787344158321736545750931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29858229438881157697167287 44787344158321736545750931)
  ·
    refine ⟨67181016237482604818626397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44787344158321736545750931 67181016237482604818626397)
    ·
      refine ⟨25192881089055976806984899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67181016237482604818626397 25192881089055976806984899)
      ·
        refine ⟨37789321633583965210477349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25192881089055976806984899 37789321633583965210477349)
        ·
          refine ⟨7085497806296993476964503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37789321633583965210477349 7085497806296993476964503)
          ·
            refine ⟨10628246709445490215446755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7085497806296993476964503 10628246709445490215446755)
            ·
              refine ⟨15942370064168235323170133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10628246709445490215446755 15942370064168235323170133)
              ·
                refine ⟨23353081148683938461675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 15942370064168235323170133 23353081148683938461675)
                ·
                  rfl

theorem cell23_1227959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 11].length) (baseStart_1227959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1227959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1227959 prefixEnd_1227959 := by exact prefixLift 1227959
  have htrace : WordTrace (prefixWord ++ tailWord_1227959) baseStart_1227959 baseEnd_1227959 := by
    simpa [prefixWord, tailWord_1227959, baseEnd_1227959] using wordTrace_append hprefix tailTrace_1227959
  have hstable : (prefixWord ++ tailWord_1227959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1227959).length < 2 ^ (prefixWord ++ tailWord_1227959).sum := by decide
  have hdescent : baseEnd_1227959 < baseStart_1227959 := by decide
  rcases family_descends (prefixWord ++ tailWord_1227959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1227979 : List Nat := [1, 1, 1, 1, 3, 2, 2, 2, 2, 2, 6]
def baseStart_1227979 : Nat := 118140960795 + 1227979 * 2 ^ 59
def prefixEnd_1227979 : Nat := 4983230072969 + 3 ^ 40 * 1227979 * 2
def baseEnd_1227979 : Nat := 630543460627556260215133

theorem tailTrace_1227979 : CollatzResearch.WordTrace tailWord_1227979 prefixEnd_1227979 630543460627556260215133 := by
  unfold tailWord_1227979
  simp only [CollatzResearch.WordTrace]
  refine ⟨44788073618249279961478991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29858715745499519974319327 44788073618249279961478991)
  ·
    refine ⟨67182110427373919942218487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44788073618249279961478991 67182110427373919942218487)
    ·
      refine ⟨100773165641060879913327731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67182110427373919942218487 100773165641060879913327731)
      ·
        refine ⟨151159748461591319869991597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100773165641060879913327731 151159748461591319869991597)
        ·
          refine ⟨56684905673096744951246849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 151159748461591319869991597 56684905673096744951246849)
          ·
            refine ⟨42513679254822558713435137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56684905673096744951246849 42513679254822558713435137)
            ·
              refine ⟨31885259441116919035076353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42513679254822558713435137 31885259441116919035076353)
              ·
                refine ⟨23913944580837689276307265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31885259441116919035076353 23913944580837689276307265)
                ·
                  refine ⟨17935458435628266957230449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23913944580837689276307265 17935458435628266957230449)
                  ·
                    refine ⟨13451593826721200217922837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17935458435628266957230449 13451593826721200217922837)
                    ·
                      refine ⟨630543460627556260215133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13451593826721200217922837 630543460627556260215133)
                      ·
                        rfl

theorem cell23_1227979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 2, 2, 2, 6].length) (baseStart_1227979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1227979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1227979 prefixEnd_1227979 := by exact prefixLift 1227979
  have htrace : WordTrace (prefixWord ++ tailWord_1227979) baseStart_1227979 baseEnd_1227979 := by
    simpa [prefixWord, tailWord_1227979, baseEnd_1227979] using wordTrace_append hprefix tailTrace_1227979
  have hstable : (prefixWord ++ tailWord_1227979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1227979).length < 2 ^ (prefixWord ++ tailWord_1227979).sum := by decide
  have hdescent : baseEnd_1227979 < baseStart_1227979 := by decide
  rcases family_descends (prefixWord ++ tailWord_1227979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1227981 : List Nat := [1, 6, 2, 2, 1, 1, 1, 4, 1, 1, 3]
def baseStart_1227981 : Nat := 118140960795 + 1227981 * 2 ^ 59
def prefixEnd_1227981 : Nat := 4983230072969 + 3 ^ 40 * 1227981 * 2
def baseEnd_1227981 : Nat := 630544487588865252390125

theorem tailTrace_1227981 : CollatzResearch.WordTrace tailWord_1227981 prefixEnd_1227981 630544487588865252390125 := by
  unfold tailWord_1227981
  simp only [CollatzResearch.WordTrace]
  refine ⟨44788146564242034303051797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29858764376161356202034531 44788146564242034303051797)
  ·
    refine ⟨2099444370198845357955553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 44788146564242034303051797 2099444370198845357955553)
    ·
      refine ⟨1574583277649134018466665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2099444370198845357955553 1574583277649134018466665)
      ·
        refine ⟨1180937458236850513849999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1574583277649134018466665 1180937458236850513849999)
        ·
          refine ⟨1771406187355275770774999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1180937458236850513849999 1771406187355275770774999)
          ·
            refine ⟨2657109281032913656162499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1771406187355275770774999 2657109281032913656162499)
            ·
              refine ⟨3985663921549370484243749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2657109281032913656162499 3985663921549370484243749)
              ·
                refine ⟨747311985290506965795703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3985663921549370484243749 747311985290506965795703)
                ·
                  refine ⟨1120967977935760448693555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 747311985290506965795703 1120967977935760448693555)
                  ·
                    refine ⟨1681451966903640673040333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1120967977935760448693555 1681451966903640673040333)
                    ·
                      refine ⟨630544487588865252390125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1681451966903640673040333 630544487588865252390125)
                      ·
                        rfl

theorem cell23_1227981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 4, 1, 1, 3].length) (baseStart_1227981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1227981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1227981 prefixEnd_1227981 := by exact prefixLift 1227981
  have htrace : WordTrace (prefixWord ++ tailWord_1227981) baseStart_1227981 baseEnd_1227981 := by
    simpa [prefixWord, tailWord_1227981, baseEnd_1227981] using wordTrace_append hprefix tailTrace_1227981
  have hstable : (prefixWord ++ tailWord_1227981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1227981).length < 2 ^ (prefixWord ++ tailWord_1227981).sum := by decide
  have hdescent : baseEnd_1227981 < baseStart_1227981 := by decide
  rcases family_descends (prefixWord ++ tailWord_1227981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1228009 : List Nat := [1, 2, 1, 1, 1, 2, 2, 1, 1, 1, 10]
def baseStart_1228009 : Nat := 118140960795 + 1228009 * 2 ^ 59
def prefixEnd_1228009 : Nat := 4983230072969 + 3 ^ 40 * 1228009 * 2
def baseEnd_1228009 : Nat := 630558865047191142839995

theorem tailTrace_1228009 : CollatzResearch.WordTrace tailWord_1228009 prefixEnd_1228009 630558865047191142839995 := by
  unfold tailWord_1228009
  simp only [CollatzResearch.WordTrace]
  refine ⟨44789167808140595085071081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29859445205427063390047387 44789167808140595085071081)
  ·
    refine ⟨33591875856105446313803311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44789167808140595085071081 33591875856105446313803311)
    ·
      refine ⟨50387813784158169470704967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33591875856105446313803311 50387813784158169470704967)
      ·
        refine ⟨75581720676237254206057451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50387813784158169470704967 75581720676237254206057451)
        ·
          refine ⟨113372581014355881309086177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75581720676237254206057451 113372581014355881309086177)
          ·
            refine ⟨85029435760766910981814633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113372581014355881309086177 85029435760766910981814633)
            ·
              refine ⟨63772076820575183236360975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85029435760766910981814633 63772076820575183236360975)
              ·
                refine ⟨95658115230862774854541463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63772076820575183236360975 95658115230862774854541463)
                ·
                  refine ⟨143487172846294162281812195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 95658115230862774854541463 143487172846294162281812195)
                  ·
                    refine ⟨215230759269441243422718293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 143487172846294162281812195 215230759269441243422718293)
                    ·
                      refine ⟨630558865047191142839995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 215230759269441243422718293 630558865047191142839995)
                      ·
                        rfl

theorem cell23_1228009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 1, 10].length) (baseStart_1228009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1228009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1228009 prefixEnd_1228009 := by exact prefixLift 1228009
  have htrace : WordTrace (prefixWord ++ tailWord_1228009) baseStart_1228009 baseEnd_1228009 := by
    simpa [prefixWord, tailWord_1228009, baseEnd_1228009] using wordTrace_append hprefix tailTrace_1228009
  have hstable : (prefixWord ++ tailWord_1228009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1228009).length < 2 ^ (prefixWord ++ tailWord_1228009).sum := by decide
  have hdescent : baseEnd_1228009 < baseStart_1228009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1228009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1228060 : List Nat := [2, 2, 3, 1, 1, 1, 5, 1, 1, 4, 2]
def baseStart_1228060 : Nat := 118140960795 + 1228060 * 2 ^ 59
def prefixEnd_1228060 : Nat := 4983230072969 + 3 ^ 40 * 1228060 * 2
def baseEnd_1228060 : Nat := 630585052560570443302261

theorem tailTrace_1228060 : CollatzResearch.WordTrace tailWord_1228060 prefixEnd_1228060 630585052560570443302261 := by
  unfold tailWord_1228060
  simp only [CollatzResearch.WordTrace]
  refine ⟨22395513965477915397588817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29860685287303887196785089 22395513965477915397588817)
  ·
    refine ⟨16796635474108436548191613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22395513965477915397588817 16796635474108436548191613)
    ·
      refine ⟨6298738302790663705571855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16796635474108436548191613 6298738302790663705571855)
      ·
        refine ⟨9448107454185995558357783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6298738302790663705571855 9448107454185995558357783)
        ·
          refine ⟨14172161181278993337536675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9448107454185995558357783 14172161181278993337536675)
          ·
            refine ⟨21258241771918490006305013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14172161181278993337536675 21258241771918490006305013)
            ·
              refine ⟨1992960166117358438091095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21258241771918490006305013 1992960166117358438091095)
              ·
                refine ⟨2989440249176037657136643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1992960166117358438091095 2989440249176037657136643)
                ·
                  refine ⟨4484160373764056485704965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2989440249176037657136643 4484160373764056485704965)
                  ·
                    refine ⟨840780070080760591069681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4484160373764056485704965 840780070080760591069681)
                    ·
                      refine ⟨630585052560570443302261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 840780070080760591069681 630585052560570443302261)
                      ·
                        rfl

theorem cell23_1228060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 5, 1, 1, 4, 2].length) (baseStart_1228060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1228060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1228060 prefixEnd_1228060 := by exact prefixLift 1228060
  have htrace : WordTrace (prefixWord ++ tailWord_1228060) baseStart_1228060 baseEnd_1228060 := by
    simpa [prefixWord, tailWord_1228060, baseEnd_1228060] using wordTrace_append hprefix tailTrace_1228060
  have hstable : (prefixWord ++ tailWord_1228060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1228060).length < 2 ^ (prefixWord ++ tailWord_1228060).sum := by decide
  have hdescent : baseEnd_1228060 < baseStart_1228060 := by decide
  rcases family_descends (prefixWord ++ tailWord_1228060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1228100 : List Nat := [2, 3, 4, 1, 1, 1, 3, 1, 7]
def baseStart_1228100 : Nat := 118140960795 + 1228100 * 2 ^ 59
def prefixEnd_1228100 : Nat := 4983230072969 + 3 ^ 40 * 1228100 * 2
def baseEnd_1228100 : Nat := 70067287976305587422453

theorem tailTrace_1228100 : CollatzResearch.WordTrace tailWord_1228100 prefixEnd_1228100 70067287976305587422453 := by
  unfold tailWord_1228100
  simp only [CollatzResearch.WordTrace]
  refine ⟨22396243425405458813316877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29861657900540611751089169 22396243425405458813316877)
  ·
    refine ⟨8398591284527047054993829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22396243425405458813316877 8398591284527047054993829)
    ·
      refine ⟨1574735865848821322811343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8398591284527047054993829 1574735865848821322811343)
      ·
        refine ⟨2362103798773231984217015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1574735865848821322811343 2362103798773231984217015)
        ·
          refine ⟨3543155698159847976325523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2362103798773231984217015 3543155698159847976325523)
          ·
            refine ⟨5314733547239771964488285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3543155698159847976325523 5314733547239771964488285)
            ·
              refine ⟨1993025080214914486683107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5314733547239771964488285 1993025080214914486683107)
              ·
                refine ⟨2989537620322371730024661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1993025080214914486683107 2989537620322371730024661)
                ·
                  refine ⟨70067287976305587422453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2989537620322371730024661 70067287976305587422453)
                  ·
                    rfl

theorem cell23_1228100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 3, 1, 7].length) (baseStart_1228100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1228100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1228100 prefixEnd_1228100 := by exact prefixLift 1228100
  have htrace : WordTrace (prefixWord ++ tailWord_1228100) baseStart_1228100 baseEnd_1228100 := by
    simpa [prefixWord, tailWord_1228100, baseEnd_1228100] using wordTrace_append hprefix tailTrace_1228100
  have hstable : (prefixWord ++ tailWord_1228100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1228100).length < 2 ^ (prefixWord ++ tailWord_1228100).sum := by decide
  have hdescent : baseEnd_1228100 < baseStart_1228100 := by decide
  rcases family_descends (prefixWord ++ tailWord_1228100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1228130 : List Nat := [3, 3, 2, 1, 1, 1, 4, 1, 2, 5]
def baseStart_1228130 : Nat := 118140960795 + 1228130 * 2 ^ 59
def prefixEnd_1228130 : Nat := 4983230072969 + 3 ^ 40 * 1228130 * 2
def baseEnd_1228130 : Nat := 210206998735461723142313

theorem tailTrace_1228130 : CollatzResearch.WordTrace tailWord_1228130 prefixEnd_1228130 210206998735461723142313 := by
  unfold tailWord_1228130
  simp only [CollatzResearch.WordTrace]
  refine ⟨11198395260175558187556461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29862387360468155166817229 11198395260175558187556461)
  ·
    refine ⟨4199398222565834320333673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11198395260175558187556461 4199398222565834320333673)
    ·
      refine ⟨3149548666924375740250255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4199398222565834320333673 3149548666924375740250255)
      ·
        refine ⟨4724323000386563610375383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3149548666924375740250255 4724323000386563610375383)
        ·
          refine ⟨7086484500579845415563075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4724323000386563610375383 7086484500579845415563075)
          ·
            refine ⟨10629726750869768123344613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7086484500579845415563075 10629726750869768123344613)
            ·
              refine ⟨1993073765788081523127115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10629726750869768123344613 1993073765788081523127115)
              ·
                refine ⟨2989610648682122284690673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1993073765788081523127115 2989610648682122284690673)
                ·
                  refine ⟨2242207986511591713518005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2989610648682122284690673 2242207986511591713518005)
                  ·
                    refine ⟨210206998735461723142313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2242207986511591713518005 210206998735461723142313)
                    ·
                      rfl

theorem cell23_1228130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 4, 1, 2, 5].length) (baseStart_1228130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1228130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1228130 prefixEnd_1228130 := by exact prefixLift 1228130
  have htrace : WordTrace (prefixWord ++ tailWord_1228130) baseStart_1228130 baseEnd_1228130 := by
    simpa [prefixWord, tailWord_1228130, baseEnd_1228130] using wordTrace_append hprefix tailTrace_1228130
  have hstable : (prefixWord ++ tailWord_1228130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1228130).length < 2 ^ (prefixWord ++ tailWord_1228130).sum := by decide
  have hdescent : baseEnd_1228130 < baseStart_1228130 := by decide
  rcases family_descends (prefixWord ++ tailWord_1228130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1228184 : List Nat := [2, 1, 2, 5, 3, 1, 1, 1, 2, 1, 4]
def baseStart_1228184 : Nat := 118140960795 + 1228184 * 2 ^ 59
def prefixEnd_1228184 : Nat := 4983230072969 + 3 ^ 40 * 1228184 * 2
def baseEnd_1228184 : Nat := 630648724161727958151691

theorem tailTrace_1228184 : CollatzResearch.WordTrace tailWord_1228184 prefixEnd_1228184 630648724161727958151691 := by
  unfold tailWord_1228184
  simp only [CollatzResearch.WordTrace]
  refine ⟨22397775291253299986345803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29863700388337733315127737 22397775291253299986345803)
  ·
    refine ⟨33596662936879949979518705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22397775291253299986345803 33596662936879949979518705)
    ·
      refine ⟨25197497202659962484639029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33596662936879949979518705 25197497202659962484639029)
      ·
        refine ⟨2362265362749371482934909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25197497202659962484639029 2362265362749371482934909)
        ·
          refine ⟨885849511031014306100591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2362265362749371482934909 885849511031014306100591)
          ·
            refine ⟨1328774266546521459150887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 885849511031014306100591 1328774266546521459150887)
            ·
              refine ⟨1993161399819782188726331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1328774266546521459150887 1993161399819782188726331)
              ·
                refine ⟨2989742099729673283089497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1993161399819782188726331 2989742099729673283089497)
                ·
                  refine ⟨2242306574797254962317123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2989742099729673283089497 2242306574797254962317123)
                  ·
                    refine ⟨3363459862195882443475685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2242306574797254962317123 3363459862195882443475685)
                    ·
                      refine ⟨630648724161727958151691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3363459862195882443475685 630648724161727958151691)
                      ·
                        rfl

theorem cell23_1228184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 1, 1, 2, 1, 4].length) (baseStart_1228184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1228184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1228184 prefixEnd_1228184 := by exact prefixLift 1228184
  have htrace : WordTrace (prefixWord ++ tailWord_1228184) baseStart_1228184 baseEnd_1228184 := by
    simpa [prefixWord, tailWord_1228184, baseEnd_1228184] using wordTrace_append hprefix tailTrace_1228184
  have hstable : (prefixWord ++ tailWord_1228184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1228184).length < 2 ^ (prefixWord ++ tailWord_1228184).sum := by decide
  have hdescent : baseEnd_1228184 < baseStart_1228184 := by decide
  rcases family_descends (prefixWord ++ tailWord_1228184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1228194 : List Nat := [3, 3, 1, 2, 1, 3, 2, 3, 1, 4]
def baseStart_1228194 : Nat := 118140960795 + 1228194 * 2 ^ 59
def prefixEnd_1228194 : Nat := 4983230072969 + 3 ^ 40 * 1228194 * 2
def baseEnd_1228194 : Nat := 210217952989424306342215

theorem tailTrace_1228194 : CollatzResearch.WordTrace tailWord_1228194 prefixEnd_1228194 210217952989424306342215 := by
  unfold tailWord_1228194
  simp only [CollatzResearch.WordTrace]
  refine ⟨11198978828117592920138909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29863943541646914453703757 11198978828117592920138909)
  ·
    refine ⟨4199617060544097345052091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11198978828117592920138909 4199617060544097345052091)
    ·
      refine ⟨6299425590816146017578137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4199617060544097345052091 6299425590816146017578137)
      ·
        refine ⟨4724569193112109513183603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6299425590816146017578137 4724569193112109513183603)
        ·
          refine ⟨7086853789668164269775405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4724569193112109513183603 7086853789668164269775405)
          ·
            refine ⟨2657570171125561601165777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7086853789668164269775405 2657570171125561601165777)
            ·
              refine ⟨1993177628344171200874333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2657570171125561601165777 1993177628344171200874333)
              ·
                refine ⟨747441610629064200327875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1993177628344171200874333 747441610629064200327875)
                ·
                  refine ⟨1121162415943596300491813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 747441610629064200327875 1121162415943596300491813)
                  ·
                    refine ⟨210217952989424306342215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1121162415943596300491813 210217952989424306342215)
                    ·
                      rfl

theorem cell23_1228194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 2, 3, 1, 4].length) (baseStart_1228194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1228194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1228194 prefixEnd_1228194 := by exact prefixLift 1228194
  have htrace : WordTrace (prefixWord ++ tailWord_1228194) baseStart_1228194 baseEnd_1228194 := by
    simpa [prefixWord, tailWord_1228194, baseEnd_1228194] using wordTrace_append hprefix tailTrace_1228194
  have hstable : (prefixWord ++ tailWord_1228194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1228194).length < 2 ^ (prefixWord ++ tailWord_1228194).sum := by decide
  have hdescent : baseEnd_1228194 < baseStart_1228194 := by decide
  rcases family_descends (prefixWord ++ tailWord_1228194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1228223 : List Nat := [1, 1, 2, 2, 2, 1, 1, 3, 5, 1, 4]
def baseStart_1228223 : Nat := 118140960795 + 1228223 * 2 ^ 59
def prefixEnd_1228223 : Nat := 4983230072969 + 3 ^ 40 * 1228223 * 2
def baseEnd_1228223 : Nat := 630668749907253305564011

theorem tailTrace_1228223 : CollatzResearch.WordTrace tailWord_1228223 prefixEnd_1228223 630668749907253305564011 := by
  unfold tailWord_1228223
  simp only [CollatzResearch.WordTrace]
  refine ⟨44796973029365309633361323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29864648686243539755574215 44796973029365309633361323)
  ·
    refine ⟨67195459544047964450041985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44796973029365309633361323 67195459544047964450041985)
    ·
      refine ⟨50396594658035973337531489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67195459544047964450041985 50396594658035973337531489)
      ·
        refine ⟨37797445993526980003148617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50396594658035973337531489 37797445993526980003148617)
        ·
          refine ⟨28348084495145235002361463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37797445993526980003148617 28348084495145235002361463)
          ·
            refine ⟨42522126742717852503542195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28348084495145235002361463 42522126742717852503542195)
            ·
              refine ⟨63783190114076778755313293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42522126742717852503542195 63783190114076778755313293)
              ·
                refine ⟨23918696292778792033242485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63783190114076778755313293 23918696292778792033242485)
                ·
                  refine ⟨2242377777448011753116483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23918696292778792033242485 2242377777448011753116483)
                  ·
                    refine ⟨3363566666172017629674725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2242377777448011753116483 3363566666172017629674725)
                    ·
                      refine ⟨630668749907253305564011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3363566666172017629674725 630668749907253305564011)
                      ·
                        rfl

theorem cell23_1228223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 3, 5, 1, 4].length) (baseStart_1228223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1228223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1228223 prefixEnd_1228223 := by exact prefixLift 1228223
  have htrace : WordTrace (prefixWord ++ tailWord_1228223) baseStart_1228223 baseEnd_1228223 := by
    simpa [prefixWord, tailWord_1228223, baseEnd_1228223] using wordTrace_append hprefix tailTrace_1228223
  have hstable : (prefixWord ++ tailWord_1228223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1228223).length < 2 ^ (prefixWord ++ tailWord_1228223).sum := by decide
  have hdescent : baseEnd_1228223 < baseStart_1228223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1228223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1228250 : List Nat := [3, 1, 1, 2, 3, 2, 1, 2, 4, 4]
def baseStart_1228250 : Nat := 118140960795 + 1228250 * 2 ^ 59
def prefixEnd_1228250 : Nat := 4983230072969 + 3 ^ 40 * 1228250 * 2
def baseEnd_1228250 : Nat := 210227537961641566642129

theorem tailTrace_1228250 : CollatzResearch.WordTrace tailWord_1228250 prefixEnd_1228250 210227537961641566642129 := by
  unfold tailWord_1228250
  simp only [CollatzResearch.WordTrace]
  refine ⟨11199489450066873311148551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29865305200178328829729469 11199489450066873311148551)
  ·
    refine ⟨16799234175100309966722827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11199489450066873311148551 16799234175100309966722827)
    ·
      refine ⟨25198851262650464950084241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16799234175100309966722827 25198851262650464950084241)
      ·
        refine ⟨18899138446987848712563181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25198851262650464950084241 18899138446987848712563181)
        ·
          refine ⟨7087176917620443267211193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18899138446987848712563181 7087176917620443267211193)
          ·
            refine ⟨5315382688215332450408395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7087176917620443267211193 5315382688215332450408395)
            ·
              refine ⟨7973074032322998675612593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5315382688215332450408395 7973074032322998675612593)
              ·
                refine ⟨5979805524242249006709445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7973074032322998675612593 5979805524242249006709445)
                ·
                  refine ⟨1121213535795421688758021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5979805524242249006709445 1121213535795421688758021)
                  ·
                    refine ⟨210227537961641566642129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1121213535795421688758021 210227537961641566642129)
                    ·
                      rfl

theorem cell23_1228250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 2, 4, 4].length) (baseStart_1228250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1228250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1228250 prefixEnd_1228250 := by exact prefixLift 1228250
  have htrace : WordTrace (prefixWord ++ tailWord_1228250) baseStart_1228250 baseEnd_1228250 := by
    simpa [prefixWord, tailWord_1228250, baseEnd_1228250] using wordTrace_append hprefix tailTrace_1228250
  have hstable : (prefixWord ++ tailWord_1228250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1228250).length < 2 ^ (prefixWord ++ tailWord_1228250).sum := by decide
  have hdescent : baseEnd_1228250 < baseStart_1228250 := by decide
  rcases family_descends (prefixWord ++ tailWord_1228250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1228263 : List Nat := [1, 1, 5, 2, 1, 2, 11]
def baseStart_1228263 : Nat := 118140960795 + 1228263 * 2 ^ 59
def prefixEnd_1228263 : Nat := 4983230072969 + 3 ^ 40 * 1228263 * 2
def baseEnd_1228263 : Nat := 7786287520165841346467

theorem tailTrace_1228263 : CollatzResearch.WordTrace tailWord_1228263 prefixEnd_1228263 7786287520165841346467 := by
  unfold tailWord_1228263
  simp only [CollatzResearch.WordTrace]
  refine ⟨44798431949220396464817443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29865621299480264309878295 44798431949220396464817443)
  ·
    refine ⟨67197647923830594697226165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44798431949220396464817443 67197647923830594697226165)
    ·
      refine ⟨6299779492859118252864953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 67197647923830594697226165 6299779492859118252864953)
      ·
        refine ⟨4724834619644338689648715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6299779492859118252864953 4724834619644338689648715)
        ·
          refine ⟨7087251929466508034473073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4724834619644338689648715 7087251929466508034473073)
          ·
            refine ⟨5315438947099881025854805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7087251929466508034473073 5315438947099881025854805)
            ·
              refine ⟨7786287520165841346467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 5315438947099881025854805 7786287520165841346467)
              ·
                rfl

theorem cell23_1228263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 11].length) (baseStart_1228263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1228263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1228263 prefixEnd_1228263 := by exact prefixLift 1228263
  have htrace : WordTrace (prefixWord ++ tailWord_1228263) baseStart_1228263 baseEnd_1228263 := by
    simpa [prefixWord, tailWord_1228263, baseEnd_1228263] using wordTrace_append hprefix tailTrace_1228263
  have hstable : (prefixWord ++ tailWord_1228263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1228263).length < 2 ^ (prefixWord ++ tailWord_1228263).sum := by decide
  have hdescent : baseEnd_1228263 < baseStart_1228263 := by decide
  rcases family_descends (prefixWord ++ tailWord_1228263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1228277 : List Nat := [1, 3, 5, 1, 1, 1, 2, 2, 1, 1, 5]
def baseStart_1228277 : Nat := 118140960795 + 1228277 * 2 ^ 59
def prefixEnd_1228277 : Nat := 4983230072969 + 3 ^ 40 * 1228277 * 2
def baseEnd_1228277 : Nat := 630696477862596094288763

theorem tailTrace_1228277 : CollatzResearch.WordTrace tailWord_1228277 prefixEnd_1228277 630696477862596094288763 := by
  unfold tailWord_1228277
  simp only [CollatzResearch.WordTrace]
  refine ⟨44798942571169676855827085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29865961714113117903884723 44798942571169676855827085)
  ·
    refine ⟨16799603464188628820935157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44798942571169676855827085 16799603464188628820935157)
    ·
      refine ⟨1574962824767683951962671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16799603464188628820935157 1574962824767683951962671)
      ·
        refine ⟨2362444237151525927944007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1574962824767683951962671 2362444237151525927944007)
        ·
          refine ⟨3543666355727288891916011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2362444237151525927944007 3543666355727288891916011)
          ·
            refine ⟨5315499533590933337874017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3543666355727288891916011 5315499533590933337874017)
            ·
              refine ⟨3986624650193200003405513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5315499533590933337874017 3986624650193200003405513)
              ·
                refine ⟨2989968487644900002554135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3986624650193200003405513 2989968487644900002554135)
                ·
                  refine ⟨4484952731467350003831203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2989968487644900002554135 4484952731467350003831203)
                  ·
                    refine ⟨6727429097201025005746805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4484952731467350003831203 6727429097201025005746805)
                    ·
                      refine ⟨630696477862596094288763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6727429097201025005746805 630696477862596094288763)
                      ·
                        rfl

theorem cell23_1228277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_1228277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1228277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1228277 prefixEnd_1228277 := by exact prefixLift 1228277
  have htrace : WordTrace (prefixWord ++ tailWord_1228277) baseStart_1228277 baseEnd_1228277 := by
    simpa [prefixWord, tailWord_1228277, baseEnd_1228277] using wordTrace_append hprefix tailTrace_1228277
  have hstable : (prefixWord ++ tailWord_1228277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1228277).length < 2 ^ (prefixWord ++ tailWord_1228277).sum := by decide
  have hdescent : baseEnd_1228277 < baseStart_1228277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1228277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1228313 : List Nat := [1, 2, 1, 2, 1, 1, 2, 1, 3, 5, 4]
def baseStart_1228313 : Nat := 118140960795 + 1228313 * 2 ^ 59
def prefixEnd_1228313 : Nat := 4983230072969 + 3 ^ 40 * 1228313 * 2
def baseEnd_1228313 : Nat := 630714963166157953438597

theorem tailTrace_1228313 : CollatzResearch.WordTrace tailWord_1228313 prefixEnd_1228313 630714963166157953438597 := by
  unfold tailWord_1228313
  simp only [CollatzResearch.WordTrace]
  refine ⟨44800255599039255004137593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29866837066026170002758395 44800255599039255004137593)
  ·
    refine ⟨33600191699279441253103195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44800255599039255004137593 33600191699279441253103195)
    ·
      refine ⟨50400287548919161879654793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33600191699279441253103195 50400287548919161879654793)
      ·
        refine ⟨37800215661689371409741095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50400287548919161879654793 37800215661689371409741095)
        ·
          refine ⟨56700323492534057114611643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37800215661689371409741095 56700323492534057114611643)
          ·
            refine ⟨85050485238801085671917465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56700323492534057114611643 85050485238801085671917465)
            ·
              refine ⟨63787863929100814253938099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85050485238801085671917465 63787863929100814253938099)
              ·
                refine ⟨95681795893651221380907149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63787863929100814253938099 95681795893651221380907149)
                ·
                  refine ⟨35880673460119208017840181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 95681795893651221380907149 35880673460119208017840181)
                  ·
                    refine ⟨3363813136886175751672517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35880673460119208017840181 3363813136886175751672517)
                    ·
                      refine ⟨630714963166157953438597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3363813136886175751672517 630714963166157953438597)
                      ·
                        rfl

theorem cell23_1228313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 5, 4].length) (baseStart_1228313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1228313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1228313 prefixEnd_1228313 := by exact prefixLift 1228313
  have htrace : WordTrace (prefixWord ++ tailWord_1228313) baseStart_1228313 baseEnd_1228313 := by
    simpa [prefixWord, tailWord_1228313, baseEnd_1228313] using wordTrace_append hprefix tailTrace_1228313
  have hstable : (prefixWord ++ tailWord_1228313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1228313).length < 2 ^ (prefixWord ++ tailWord_1228313).sum := by decide
  have hdescent : baseEnd_1228313 < baseStart_1228313 := by decide
  rcases family_descends (prefixWord ++ tailWord_1228313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1228330 : List Nat := [3, 1, 4, 1, 1, 1, 1, 1, 1, 5, 4]
def baseStart_1228330 : Nat := 118140960795 + 1228330 * 2 ^ 59
def prefixEnd_1228330 : Nat := 4983230072969 + 3 ^ 40 * 1228330 * 2
def baseEnd_1228330 : Nat := 630723692337284386926019

theorem tailTrace_1228330 : CollatzResearch.WordTrace tailWord_1228330 prefixEnd_1228330 630723692337284386926019 := by
  unfold tailWord_1228330
  simp only [CollatzResearch.WordTrace]
  refine ⟨11200218909994416726876611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29867250426651777938337629 11200218909994416726876611)
  ·
    refine ⟨16800328364991625090314917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11200218909994416726876611 16800328364991625090314917)
    ·
      refine ⟨3150061568435929704434047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16800328364991625090314917 3150061568435929704434047)
      ·
        refine ⟨4725092352653894556651071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3150061568435929704434047 4725092352653894556651071)
        ·
          refine ⟨7087638528980841834976607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4725092352653894556651071 7087638528980841834976607)
          ·
            refine ⟨10631457793471262752464911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7087638528980841834976607 10631457793471262752464911)
            ·
              refine ⟨15947186690206894128697367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10631457793471262752464911 15947186690206894128697367)
              ·
                refine ⟨23920780035310341193046051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15947186690206894128697367 23920780035310341193046051)
                ·
                  refine ⟨35881170052965511789569077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23920780035310341193046051 35881170052965511789569077)
                  ·
                    refine ⟨3363859692465516730272101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35881170052965511789569077 3363859692465516730272101)
                    ·
                      refine ⟨630723692337284386926019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3363859692465516730272101 630723692337284386926019)
                      ·
                        rfl

theorem cell23_1228330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_1228330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1228330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1228330 prefixEnd_1228330 := by exact prefixLift 1228330
  have htrace : WordTrace (prefixWord ++ tailWord_1228330) baseStart_1228330 baseEnd_1228330 := by
    simpa [prefixWord, tailWord_1228330, baseEnd_1228330] using wordTrace_append hprefix tailTrace_1228330
  have hstable : (prefixWord ++ tailWord_1228330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1228330).length < 2 ^ (prefixWord ++ tailWord_1228330).sum := by decide
  have hdescent : baseEnd_1228330 < baseStart_1228330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1228330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1228334 : List Nat := [4, 1, 3, 1, 2, 1, 1, 2, 3, 3, 2]
def baseStart_1228334 : Nat := 118140960795 + 1228334 * 2 ^ 59
def prefixEnd_1228334 : Nat := 4983230072969 + 3 ^ 40 * 1228334 * 2
def baseEnd_1228334 : Nat := 630725746259902371276001

theorem tailTrace_1228334 : CollatzResearch.WordTrace tailWord_1228334 prefixEnd_1228334 630725746259902371276001 := by
  unfold tailWord_1228334
  simp only [CollatzResearch.WordTrace]
  refine ⟨5600127691495396948831507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29867347687975450393768037 5600127691495396948831507)
  ·
    refine ⟨8400191537243095423247261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5600127691495396948831507 8400191537243095423247261)
    ·
      refine ⟨3150071826466160783717723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8400191537243095423247261 3150071826466160783717723)
      ·
        refine ⟨4725107739699241175576585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3150071826466160783717723 4725107739699241175576585)
        ·
          refine ⟨3543830804774430881682439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4725107739699241175576585 3543830804774430881682439)
          ·
            refine ⟨5315746207161646322523659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3543830804774430881682439 5315746207161646322523659)
            ·
              refine ⟨7973619310742469483785489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5315746207161646322523659 7973619310742469483785489)
              ·
                refine ⟨5980214483056852112839117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7973619310742469483785489 5980214483056852112839117)
                ·
                  refine ⟨2242580431146319542314669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5980214483056852112839117 2242580431146319542314669)
                  ·
                    refine ⟨840967661679869828368001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2242580431146319542314669 840967661679869828368001)
                    ·
                      refine ⟨630725746259902371276001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 840967661679869828368001 630725746259902371276001)
                      ·
                        rfl

theorem cell23_1228334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 2, 3, 3, 2].length) (baseStart_1228334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1228334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1228334 prefixEnd_1228334 := by exact prefixLift 1228334
  have htrace : WordTrace (prefixWord ++ tailWord_1228334) baseStart_1228334 baseEnd_1228334 := by
    simpa [prefixWord, tailWord_1228334, baseEnd_1228334] using wordTrace_append hprefix tailTrace_1228334
  have hstable : (prefixWord ++ tailWord_1228334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1228334).length < 2 ^ (prefixWord ++ tailWord_1228334).sum := by decide
  have hdescent : baseEnd_1228334 < baseStart_1228334 := by decide
  rcases family_descends (prefixWord ++ tailWord_1228334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1228363 : List Nat := [1, 1, 1, 1, 3, 1, 3, 2, 1, 2, 7]
def baseStart_1228363 : Nat := 118140960795 + 1228363 * 2 ^ 59
def prefixEnd_1228363 : Nat := 4983230072969 + 3 ^ 40 * 1228363 * 2
def baseEnd_1228363 : Nat := 630740637198882757813367

theorem tailTrace_1228363 : CollatzResearch.WordTrace tailWord_1228363 prefixEnd_1228363 630740637198882757813367 := by
  unfold tailWord_1228363
  simp only [CollatzResearch.WordTrace]
  refine ⟨44802079248858113543457743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29868052832572075695638495 44802079248858113543457743)
  ·
    refine ⟨67203118873287170315186615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44802079248858113543457743 67203118873287170315186615)
    ·
      refine ⟨100804678309930755472779923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67203118873287170315186615 100804678309930755472779923)
      ·
        refine ⟨151207017464896133209169885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100804678309930755472779923 151207017464896133209169885)
        ·
          refine ⟨56702631549336049953438707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 151207017464896133209169885 56702631549336049953438707)
          ·
            refine ⟨85053947324004074930158061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56702631549336049953438707 85053947324004074930158061)
            ·
              refine ⟨31895230246501528098809273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85053947324004074930158061 31895230246501528098809273)
              ·
                refine ⟨23921422684876146074106955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31895230246501528098809273 23921422684876146074106955)
                ·
                  refine ⟨35882134027314219111160433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23921422684876146074106955 35882134027314219111160433)
                  ·
                    refine ⟨26911600520485664333370325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35882134027314219111160433 26911600520485664333370325)
                    ·
                      refine ⟨630740637198882757813367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 26911600520485664333370325 630740637198882757813367)
                      ·
                        rfl

theorem cell23_1228363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 1, 2, 7].length) (baseStart_1228363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1228363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1228363 prefixEnd_1228363 := by exact prefixLift 1228363
  have htrace : WordTrace (prefixWord ++ tailWord_1228363) baseStart_1228363 baseEnd_1228363 := by
    simpa [prefixWord, tailWord_1228363, baseEnd_1228363] using wordTrace_append hprefix tailTrace_1228363
  have hstable : (prefixWord ++ tailWord_1228363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1228363).length < 2 ^ (prefixWord ++ tailWord_1228363).sum := by decide
  have hdescent : baseEnd_1228363 < baseStart_1228363 := by decide
  rcases family_descends (prefixWord ++ tailWord_1228363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1228387 : List Nat := [1, 1, 1, 5, 1, 3, 2, 4, 5]
def baseStart_1228387 : Nat := 118140960795 + 1228387 * 2 ^ 59
def prefixEnd_1228387 : Nat := 4983230072969 + 3 ^ 40 * 1228387 * 2
def baseEnd_1228387 : Nat := 70083662303843407101473

theorem tailTrace_1228387 : CollatzResearch.WordTrace tailWord_1228387 prefixEnd_1228387 70083662303843407101473 := by
  unfold tailWord_1228387
  simp only [CollatzResearch.WordTrace]
  refine ⟨44802954600771165642331415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29868636400514110428220943 44802954600771165642331415)
  ·
    refine ⟨67204431901156748463497123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44802954600771165642331415 67204431901156748463497123)
    ·
      refine ⟨100806647851735122695245685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67204431901156748463497123 100806647851735122695245685)
      ·
        refine ⟨9450623236100167752679283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 100806647851735122695245685 9450623236100167752679283)
        ·
          refine ⟨14175934854150251629018925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9450623236100167752679283 14175934854150251629018925)
          ·
            refine ⟨5315975570306344360882097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14175934854150251629018925 5315975570306344360882097)
            ·
              refine ⟨3986981677729758270661573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5315975570306344360882097 3986981677729758270661573)
              ·
                refine ⟨747559064574329675749045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3986981677729758270661573 747559064574329675749045)
                ·
                  refine ⟨70083662303843407101473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 747559064574329675749045 70083662303843407101473)
                  ·
                    rfl

theorem cell23_1228387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 4, 5].length) (baseStart_1228387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1228387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1228387 prefixEnd_1228387 := by exact prefixLift 1228387
  have htrace : WordTrace (prefixWord ++ tailWord_1228387) baseStart_1228387 baseEnd_1228387 := by
    simpa [prefixWord, tailWord_1228387, baseEnd_1228387] using wordTrace_append hprefix tailTrace_1228387
  have hstable : (prefixWord ++ tailWord_1228387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1228387).length < 2 ^ (prefixWord ++ tailWord_1228387).sum := by decide
  have hdescent : baseEnd_1228387 < baseStart_1228387 := by decide
  rcases family_descends (prefixWord ++ tailWord_1228387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1228398 : List Nat := [4, 1, 2, 2, 4, 1, 1, 1, 1, 4, 2]
def baseStart_1228398 : Nat := 118140960795 + 1228398 * 2 ^ 59
def prefixEnd_1228398 : Nat := 4983230072969 + 3 ^ 40 * 1228398 * 2
def baseEnd_1228398 : Nat := 630758609021790120875707

theorem tailTrace_1228398 : CollatzResearch.WordTrace tailWord_1228398 prefixEnd_1228398 630758609021790120875707 := by
  unfold tailWord_1228398
  simp only [CollatzResearch.WordTrace]
  refine ⟨5600419475466414315122731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29868903869154209680654565 5600419475466414315122731)
  ·
    refine ⟨8400629213199621472684097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5600419475466414315122731 8400629213199621472684097)
    ·
      refine ⟨6300471909899716104513073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8400629213199621472684097 6300471909899716104513073)
      ·
        refine ⟨4725353932424787078384805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6300471909899716104513073 4725353932424787078384805)
        ·
          refine ⟨886003862329647577197151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4725353932424787078384805 886003862329647577197151)
          ·
            refine ⟨1329005793494471365795727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 886003862329647577197151 1329005793494471365795727)
            ·
              refine ⟨1993508690241707048693591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1329005793494471365795727 1993508690241707048693591)
              ·
                refine ⟨2990263035362560573040387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1993508690241707048693591 2990263035362560573040387)
                ·
                  refine ⟨4485394553043840859560581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2990263035362560573040387 4485394553043840859560581)
                  ·
                    refine ⟨841011478695720161167609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4485394553043840859560581 841011478695720161167609)
                    ·
                      refine ⟨630758609021790120875707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 841011478695720161167609 630758609021790120875707)
                      ·
                        rfl

theorem cell23_1228398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 1, 1, 1, 4, 2].length) (baseStart_1228398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1228398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1228398 prefixEnd_1228398 := by exact prefixLift 1228398
  have htrace : WordTrace (prefixWord ++ tailWord_1228398) baseStart_1228398 baseEnd_1228398 := by
    simpa [prefixWord, tailWord_1228398, baseEnd_1228398] using wordTrace_append hprefix tailTrace_1228398
  have hstable : (prefixWord ++ tailWord_1228398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1228398).length < 2 ^ (prefixWord ++ tailWord_1228398).sum := by decide
  have hdescent : baseEnd_1228398 < baseStart_1228398 := by decide
  rcases family_descends (prefixWord ++ tailWord_1228398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1228400 : List Nat := [2, 1, 1, 1, 6, 1, 1, 2, 1, 7]
def baseStart_1228400 : Nat := 118140960795 + 1228400 * 2 ^ 59
def prefixEnd_1228400 : Nat := 4983230072969 + 3 ^ 40 * 1228400 * 2
def baseEnd_1228400 : Nat := 210253211994366371016899

theorem tailTrace_1228400 : CollatzResearch.WordTrace tailWord_1228400 prefixEnd_1228400 210253211994366371016899 := by
  unfold tailWord_1228400
  simp only [CollatzResearch.WordTrace]
  refine ⟨22401714374862034431277327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29868952499816045908369769 22401714374862034431277327)
  ·
    refine ⟨33602571562293051646915991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22401714374862034431277327 33602571562293051646915991)
    ·
      refine ⟨50403857343439577470373987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33602571562293051646915991 50403857343439577470373987)
      ·
        refine ⟨75605786015159366205560981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50403857343439577470373987 75605786015159366205560981)
        ·
          refine ⟨3544021219460595290885671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 75605786015159366205560981 3544021219460595290885671)
          ·
            refine ⟨5316031829190892936328507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3544021219460595290885671 5316031829190892936328507)
            ·
              refine ⟨7974047743786339404492761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5316031829190892936328507 7974047743786339404492761)
              ·
                refine ⟨5980535807839754553369571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7974047743786339404492761 5980535807839754553369571)
                ·
                  refine ⟨8970803711759631830054357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5980535807839754553369571 8970803711759631830054357)
                  ·
                    refine ⟨210253211994366371016899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8970803711759631830054357 210253211994366371016899)
                    ·
                      rfl

theorem cell23_1228400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 2, 1, 7].length) (baseStart_1228400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1228400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1228400 prefixEnd_1228400 := by exact prefixLift 1228400
  have htrace : WordTrace (prefixWord ++ tailWord_1228400) baseStart_1228400 baseEnd_1228400 := by
    simpa [prefixWord, tailWord_1228400, baseEnd_1228400] using wordTrace_append hprefix tailTrace_1228400
  have hstable : (prefixWord ++ tailWord_1228400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1228400).length < 2 ^ (prefixWord ++ tailWord_1228400).sum := by decide
  have hdescent : baseEnd_1228400 < baseStart_1228400 := by decide
  rcases family_descends (prefixWord ++ tailWord_1228400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1228434 : List Nat := [3, 2, 3, 1, 3, 1, 1, 2, 2, 5]
def baseStart_1228434 : Nat := 118140960795 + 1228434 * 2 ^ 59
def prefixEnd_1228434 : Nat := 4983230072969 + 3 ^ 40 * 1228434 * 2
def baseEnd_1228434 : Nat := 210259031441783993341847

theorem tailTrace_1228434 : CollatzResearch.WordTrace tailWord_1228434 prefixEnd_1228434 210259031441783993341847 := by
  unfold tailWord_1228434
  simp only [CollatzResearch.WordTrace]
  refine ⟨11201167207900223167323089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29869779221067261779528237 11201167207900223167323089)
  ·
    refine ⟨8400875405925167375492317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11201167207900223167323089 8400875405925167375492317)
    ·
      refine ⟨3150328277221937765809619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8400875405925167375492317 3150328277221937765809619)
      ·
        refine ⟨4725492415832906648714429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3150328277221937765809619 4725492415832906648714429)
        ·
          refine ⟨1772059655937339993267911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4725492415832906648714429 1772059655937339993267911)
          ·
            refine ⟨2658089483906009989901867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1772059655937339993267911 2658089483906009989901867)
            ·
              refine ⟨3987134225859014984852801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2658089483906009989901867 3987134225859014984852801)
              ·
                refine ⟨2990350669394261238639601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3987134225859014984852801 2990350669394261238639601)
                ·
                  refine ⟨2242763002045695928979701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2990350669394261238639601 2242763002045695928979701)
                  ·
                    refine ⟨210259031441783993341847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2242763002045695928979701 210259031441783993341847)
                    ·
                      rfl

theorem cell23_1228434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 2, 2, 5].length) (baseStart_1228434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1228434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1228434 prefixEnd_1228434 := by exact prefixLift 1228434
  have htrace : WordTrace (prefixWord ++ tailWord_1228434) baseStart_1228434 baseEnd_1228434 := by
    simpa [prefixWord, tailWord_1228434, baseEnd_1228434] using wordTrace_append hprefix tailTrace_1228434
  have hstable : (prefixWord ++ tailWord_1228434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1228434).length < 2 ^ (prefixWord ++ tailWord_1228434).sum := by decide
  have hdescent : baseEnd_1228434 < baseStart_1228434 := by decide
  rcases family_descends (prefixWord ++ tailWord_1228434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1228437 : List Nat := [1, 3, 2, 1, 1, 1, 1, 3, 4, 4, 2]
def baseStart_1228437 : Nat := 118140960795 + 1228437 * 2 ^ 59
def prefixEnd_1228437 : Nat := 4983230072969 + 3 ^ 40 * 1228437 * 2
def baseEnd_1228437 : Nat := 630778634767315468288027

theorem tailTrace_1228437 : CollatzResearch.WordTrace tailWord_1228437 prefixEnd_1228437 630778634767315468288027 := by
  unfold tailWord_1228437
  simp only [CollatzResearch.WordTrace]
  refine ⟨44804778250590024181651565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29869852167060016121101043 44804778250590024181651565)
  ·
    refine ⟨16801791843971259068119337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44804778250590024181651565 16801791843971259068119337)
    ·
      refine ⟨12601343882978444301089503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16801791843971259068119337 12601343882978444301089503)
      ·
        refine ⟨18902015824467666451634255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12601343882978444301089503 18902015824467666451634255)
        ·
          refine ⟨28353023736701499677451383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18902015824467666451634255 28353023736701499677451383)
          ·
            refine ⟨42529535605052249516177075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28353023736701499677451383 42529535605052249516177075)
            ·
              refine ⟨63794303407578374274265613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42529535605052249516177075 63794303407578374274265613)
              ·
                refine ⟨23922863777841890352849605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63794303407578374274265613 23922863777841890352849605)
                ·
                  refine ⟨4485536958345354441159301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23922863777841890352849605 4485536958345354441159301)
                  ·
                    refine ⟨841038179689753957717369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4485536958345354441159301 841038179689753957717369)
                    ·
                      refine ⟨630778634767315468288027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 841038179689753957717369 630778634767315468288027)
                      ·
                        rfl

theorem cell23_1228437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 3, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 3, 4, 4, 2].length) (baseStart_1228437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1228437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1228437 prefixEnd_1228437 := by exact prefixLift 1228437
  have htrace : WordTrace (prefixWord ++ tailWord_1228437) baseStart_1228437 baseEnd_1228437 := by
    simpa [prefixWord, tailWord_1228437, baseEnd_1228437] using wordTrace_append hprefix tailTrace_1228437
  have hstable : (prefixWord ++ tailWord_1228437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1228437).length < 2 ^ (prefixWord ++ tailWord_1228437).sum := by decide
  have hdescent : baseEnd_1228437 < baseStart_1228437 := by decide
  rcases family_descends (prefixWord ++ tailWord_1228437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1228474 : List Nat := [3, 1, 1, 1, 2, 5, 2, 1, 2, 2, 3]
def baseStart_1228474 : Nat := 118140960795 + 1228474 * 2 ^ 59
def prefixEnd_1228474 : Nat := 4983230072969 + 3 ^ 40 * 1228474 * 2
def baseEnd_1228474 : Nat := 630797633551531823525357

theorem tailTrace_1228474 : CollatzResearch.WordTrace tailWord_1228474 prefixEnd_1228474 630797633551531823525357 := by
  unfold tailWord_1228474
  simp only [CollatzResearch.WordTrace]
  refine ⟨11201531937863994875187119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29870751834303986333832317 11201531937863994875187119)
  ·
    refine ⟨16802297906795992312780679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11201531937863994875187119 16802297906795992312780679)
    ·
      refine ⟨25203446860193988469171019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16802297906795992312780679 25203446860193988469171019)
      ·
        refine ⟨37805170290290982703756529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25203446860193988469171019 37805170290290982703756529)
        ·
          refine ⟨28353877717718237027817397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37805170290290982703756529 28353877717718237027817397)
          ·
            refine ⟨2658176036036084721357881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28353877717718237027817397 2658176036036084721357881)
            ·
              refine ⟨1993632027027063541018411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2658176036036084721357881 1993632027027063541018411)
              ·
                refine ⟨2990448040540595311527617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1993632027027063541018411 2990448040540595311527617)
                ·
                  refine ⟨2242836030405446483645713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2990448040540595311527617 2242836030405446483645713)
                  ·
                    refine ⟨1682127022804084862734285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2242836030405446483645713 1682127022804084862734285)
                    ·
                      refine ⟨630797633551531823525357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1682127022804084862734285 630797633551531823525357)
                      ·
                        rfl

theorem cell23_1228474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 2, 1, 2, 2, 3].length) (baseStart_1228474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1228474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1228474 prefixEnd_1228474 := by exact prefixLift 1228474
  have htrace : WordTrace (prefixWord ++ tailWord_1228474) baseStart_1228474 baseEnd_1228474 := by
    simpa [prefixWord, tailWord_1228474, baseEnd_1228474] using wordTrace_append hprefix tailTrace_1228474
  have hstable : (prefixWord ++ tailWord_1228474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1228474).length < 2 ^ (prefixWord ++ tailWord_1228474).sum := by decide
  have hdescent : baseEnd_1228474 < baseStart_1228474 := by decide
  rcases family_descends (prefixWord ++ tailWord_1228474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1228498 : List Nat := [3, 2, 2, 2, 2, 1, 4, 2, 1, 4]
def baseStart_1228498 : Nat := 118140960795 + 1228498 * 2 ^ 59
def prefixEnd_1228498 : Nat := 4983230072969 + 3 ^ 40 * 1228498 * 2
def baseEnd_1228498 : Nat := 210269985695746576541749

theorem tailTrace_1228498 : CollatzResearch.WordTrace tailWord_1228498 prefixEnd_1228498 210269985695746576541749 := by
  unfold tailWord_1228498
  simp only [CollatzResearch.WordTrace]
  refine ⟨11201750775842257899905537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29871335402246021066414765 11201750775842257899905537)
  ·
    refine ⟨8401313081881693424929153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11201750775842257899905537 8401313081881693424929153)
    ·
      refine ⟨6300984811411270068696865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8401313081881693424929153 6300984811411270068696865)
      ·
        refine ⟨4725738608558452551522649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6300984811411270068696865 4725738608558452551522649)
        ·
          refine ⟨3544303956418839413641987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4725738608558452551522649 3544303956418839413641987)
          ·
            refine ⟨5316455934628259120462981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3544303956418839413641987 5316455934628259120462981)
            ·
              refine ⟨996835487742798585086809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5316455934628259120462981 996835487742798585086809)
              ·
                refine ⟨747626615807098938815107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 996835487742798585086809 747626615807098938815107)
                ·
                  refine ⟨1121439923710648408222661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 747626615807098938815107 1121439923710648408222661)
                  ·
                    refine ⟨210269985695746576541749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1121439923710648408222661 210269985695746576541749)
                    ·
                      rfl

theorem cell23_1228498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 4, 2, 1, 4].length) (baseStart_1228498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1228498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1228498 prefixEnd_1228498 := by exact prefixLift 1228498
  have htrace : WordTrace (prefixWord ++ tailWord_1228498) baseStart_1228498 baseEnd_1228498 := by
    simpa [prefixWord, tailWord_1228498, baseEnd_1228498] using wordTrace_append hprefix tailTrace_1228498
  have hstable : (prefixWord ++ tailWord_1228498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1228498).length < 2 ^ (prefixWord ++ tailWord_1228498).sum := by decide
  have hdescent : baseEnd_1228498 < baseStart_1228498 := by decide
  rcases family_descends (prefixWord ++ tailWord_1228498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1228504 : List Nat := [2, 1, 2, 2, 3, 1, 2, 3, 3, 1, 3]
def baseStart_1228504 : Nat := 118140960795 + 1228504 * 2 ^ 59
def prefixEnd_1228504 : Nat := 4983230072969 + 3 ^ 40 * 1228504 * 2
def baseEnd_1228504 : Nat := 630813037971166706150219

theorem tailTrace_1228504 : CollatzResearch.WordTrace tailWord_1228504 prefixEnd_1228504 630813037971166706150219 := by
  unfold tailWord_1228504
  simp only [CollatzResearch.WordTrace]
  refine ⟨22403610970673647312170283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29871481294231529749560377 22403610970673647312170283)
  ·
    refine ⟨33605416456010470968255425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22403610970673647312170283 33605416456010470968255425)
    ·
      refine ⟨25204062342007853226191569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33605416456010470968255425 25204062342007853226191569)
      ·
        refine ⟨18903046756505889919643677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25204062342007853226191569 18903046756505889919643677)
        ·
          refine ⟨7088642533689708719866379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18903046756505889919643677 7088642533689708719866379)
          ·
            refine ⟨10632963800534563079799569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7088642533689708719866379 10632963800534563079799569)
            ·
              refine ⟨7974722850400922309849677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10632963800534563079799569 7974722850400922309849677)
              ·
                refine ⟨2990521068900345866193629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7974722850400922309849677 2990521068900345866193629)
                ·
                  refine ⟨1121445400837629699822611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2990521068900345866193629 1121445400837629699822611)
                  ·
                    refine ⟨1682168101256444549733917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1121445400837629699822611 1682168101256444549733917)
                    ·
                      refine ⟨630813037971166706150219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1682168101256444549733917 630813037971166706150219)
                      ·
                        rfl

theorem cell23_1228504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 3, 3, 1, 3].length) (baseStart_1228504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1228504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1228504 prefixEnd_1228504 := by exact prefixLift 1228504
  have htrace : WordTrace (prefixWord ++ tailWord_1228504) baseStart_1228504 baseEnd_1228504 := by
    simpa [prefixWord, tailWord_1228504, baseEnd_1228504] using wordTrace_append hprefix tailTrace_1228504
  have hstable : (prefixWord ++ tailWord_1228504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1228504).length < 2 ^ (prefixWord ++ tailWord_1228504).sum := by decide
  have hdescent : baseEnd_1228504 < baseStart_1228504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1228504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1228527 : List Nat := [1, 1, 2, 1, 5, 1, 1, 3, 3, 1, 4]
def baseStart_1228527 : Nat := 118140960795 + 1228527 * 2 ^ 59
def prefixEnd_1228527 : Nat := 4983230072969 + 3 ^ 40 * 1228527 * 2
def baseEnd_1228527 : Nat := 630824848026220116162613

theorem tailTrace_1228527 : CollatzResearch.WordTrace tailWord_1228527 prefixEnd_1228527 630824848026220116162613 := by
  unfold tailWord_1228527
  simp only [CollatzResearch.WordTrace]
  refine ⟨44808060820263969552427835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29872040546842646368285223 44808060820263969552427835)
  ·
    refine ⟨67212091230395954328641753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44808060820263969552427835 67212091230395954328641753)
    ·
      refine ⟨50409068422796965746481315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67212091230395954328641753 50409068422796965746481315)
      ·
        refine ⟨75613602634195448619721973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50409068422796965746481315 75613602634195448619721973)
        ·
          refine ⟨7088775246955823308098935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 75613602634195448619721973 7088775246955823308098935)
          ·
            refine ⟨10633162870433734962148403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7088775246955823308098935 10633162870433734962148403)
            ·
              refine ⟨15949744305650602443222605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10633162870433734962148403 15949744305650602443222605)
              ·
                refine ⟨5981154114618975916208477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15949744305650602443222605 5981154114618975916208477)
                ·
                  refine ⟨2242932792982115968578179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5981154114618975916208477 2242932792982115968578179)
                  ·
                    refine ⟨3364399189473173952867269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2242932792982115968578179 3364399189473173952867269)
                    ·
                      refine ⟨630824848026220116162613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3364399189473173952867269 630824848026220116162613)
                      ·
                        rfl

theorem cell23_1228527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 3, 3, 1, 4].length) (baseStart_1228527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1228527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1228527 prefixEnd_1228527 := by exact prefixLift 1228527
  have htrace : WordTrace (prefixWord ++ tailWord_1228527) baseStart_1228527 baseEnd_1228527 := by
    simpa [prefixWord, tailWord_1228527, baseEnd_1228527] using wordTrace_append hprefix tailTrace_1228527
  have hstable : (prefixWord ++ tailWord_1228527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1228527).length < 2 ^ (prefixWord ++ tailWord_1228527).sum := by decide
  have hdescent : baseEnd_1228527 < baseStart_1228527 := by decide
  rcases family_descends (prefixWord ++ tailWord_1228527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1228554 : List Nat := [3, 1, 2, 2, 1, 4, 1, 1, 4, 4]
def baseStart_1228554 : Nat := 118140960795 + 1228554 * 2 ^ 59
def prefixEnd_1228554 : Nat := 4983230072969 + 3 ^ 40 * 1228554 * 2
def baseEnd_1228554 : Nat := 210279570667963836841663

theorem tailTrace_1228554 : CollatzResearch.WordTrace tailWord_1228554 prefixEnd_1228554 210279570667963836841663 := by
  unfold tailWord_1228554
  simp only [CollatzResearch.WordTrace]
  refine ⟨11202261397791538290915179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29872697060777435442440477 11202261397791538290915179)
  ·
    refine ⟨16803392096687307436372769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11202261397791538290915179 16803392096687307436372769)
    ·
      refine ⟨12602544072515480577279577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16803392096687307436372769 12602544072515480577279577)
      ·
        refine ⟨9451908054386610432959683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12602544072515480577279577 9451908054386610432959683)
        ·
          refine ⟨14177862081579915649439525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9451908054386610432959683 14177862081579915649439525)
          ·
            refine ⟨2658349140296234184269911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14177862081579915649439525 2658349140296234184269911)
            ·
              refine ⟨3987523710444351276404867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2658349140296234184269911 3987523710444351276404867)
              ·
                refine ⟨5981285565666526914607301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3987523710444351276404867 5981285565666526914607301)
                ·
                  refine ⟨1121491043562473796488869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5981285565666526914607301 1121491043562473796488869)
                  ·
                    refine ⟨210279570667963836841663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1121491043562473796488869 210279570667963836841663)
                    ·
                      rfl

theorem cell23_1228554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 1, 4, 4].length) (baseStart_1228554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1228554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1228554 prefixEnd_1228554 := by exact prefixLift 1228554
  have htrace : WordTrace (prefixWord ++ tailWord_1228554) baseStart_1228554 baseEnd_1228554 := by
    simpa [prefixWord, tailWord_1228554, baseEnd_1228554] using wordTrace_append hprefix tailTrace_1228554
  have hstable : (prefixWord ++ tailWord_1228554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1228554).length < 2 ^ (prefixWord ++ tailWord_1228554).sum := by decide
  have hdescent : baseEnd_1228554 < baseStart_1228554 := by decide
  rcases family_descends (prefixWord ++ tailWord_1228554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1228581 : List Nat := [1, 3, 1, 2, 3, 3, 2, 2, 1, 2, 3]
def baseStart_1228581 : Nat := 118140960795 + 1228581 * 2 ^ 59
def prefixEnd_1228581 : Nat := 4983230072969 + 3 ^ 40 * 1228581 * 2
def baseEnd_1228581 : Nat := 630852575981562904887365

theorem tailTrace_1228581 : CollatzResearch.WordTrace tailWord_1228581 prefixEnd_1228581 630852575981562904887365 := by
  unfold tailWord_1228581
  simp only [CollatzResearch.WordTrace]
  refine ⟨44810030362068336774893597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29873353574712224516595731 44810030362068336774893597)
  ·
    refine ⟨16803761385775626290585099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44810030362068336774893597 16803761385775626290585099)
    ·
      refine ⟨25205642078663439435877649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16803761385775626290585099 25205642078663439435877649)
      ·
        refine ⟨18904231558997579576908237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25205642078663439435877649 18904231558997579576908237)
        ·
          refine ⟨7089086834624092341340589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18904231558997579576908237 7089086834624092341340589)
          ·
            refine ⟨2658407562984034628002721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7089086834624092341340589 2658407562984034628002721)
            ·
              refine ⟨1993805672238025971002041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2658407562984034628002721 1993805672238025971002041)
              ·
                refine ⟨1495354254178519478251531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1993805672238025971002041 1495354254178519478251531)
                ·
                  refine ⟨2243031381267779217377297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1495354254178519478251531 2243031381267779217377297)
                  ·
                    refine ⟨1682273535950834413032973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2243031381267779217377297 1682273535950834413032973)
                    ·
                      refine ⟨630852575981562904887365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1682273535950834413032973 630852575981562904887365)
                      ·
                        rfl

theorem cell23_1228581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 2, 2, 1, 2, 3].length) (baseStart_1228581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1228581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1228581 prefixEnd_1228581 := by exact prefixLift 1228581
  have htrace : WordTrace (prefixWord ++ tailWord_1228581) baseStart_1228581 baseEnd_1228581 := by
    simpa [prefixWord, tailWord_1228581, baseEnd_1228581] using wordTrace_append hprefix tailTrace_1228581
  have hstable : (prefixWord ++ tailWord_1228581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1228581).length < 2 ^ (prefixWord ++ tailWord_1228581).sum := by decide
  have hdescent : baseEnd_1228581 < baseStart_1228581 := by decide
  rcases family_descends (prefixWord ++ tailWord_1228581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1228584 : List Nat := [2, 1, 5, 1, 1, 2, 4, 7]
def baseStart_1228584 : Nat := 118140960795 + 1228584 * 2 ^ 59
def prefixEnd_1228584 : Nat := 4983230072969 + 3 ^ 40 * 1228584 * 2
def baseEnd_1228584 : Nat := 23364967274945421968513

theorem tailTrace_1228584 : CollatzResearch.WordTrace tailWord_1228584 prefixEnd_1228584 23364967274945421968513 := by
  unfold tailWord_1228584
  simp only [CollatzResearch.WordTrace]
  refine ⟨22405069890528734143626403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29873426520704978858168537 22405069890528734143626403)
  ·
    refine ⟨33607604835793101215439605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22405069890528734143626403 33607604835793101215439605)
    ·
      refine ⟨3150712953355603238947463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 33607604835793101215439605 3150712953355603238947463)
      ·
        refine ⟨4726069430033404858421195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3150712953355603238947463 4726069430033404858421195)
        ·
          refine ⟨7089104145050107287631793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4726069430033404858421195 7089104145050107287631793)
          ·
            refine ⟨5316828108787580465723845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7089104145050107287631793 5316828108787580465723845)
            ·
              refine ⟨996905270397671337323221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5316828108787580465723845 996905270397671337323221)
              ·
                refine ⟨23364967274945421968513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 996905270397671337323221 23364967274945421968513)
                ·
                  rfl

theorem cell23_1228584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 4, 7].length) (baseStart_1228584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1228584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1228584 prefixEnd_1228584 := by exact prefixLift 1228584
  have htrace : WordTrace (prefixWord ++ tailWord_1228584) baseStart_1228584 baseEnd_1228584 := by
    simpa [prefixWord, tailWord_1228584, baseEnd_1228584] using wordTrace_append hprefix tailTrace_1228584
  have hstable : (prefixWord ++ tailWord_1228584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1228584).length < 2 ^ (prefixWord ++ tailWord_1228584).sum := by decide
  have hdescent : baseEnd_1228584 < baseStart_1228584 := by decide
  rcases family_descends (prefixWord ++ tailWord_1228584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1228598 : List Nat := [5, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3]
def baseStart_1228598 : Nat := 118140960795 + 1228598 * 2 ^ 59
def prefixEnd_1228598 : Nat := 4983230072969 + 3 ^ 40 * 1228598 * 2
def baseEnd_1228598 : Nat := 630861305152689338374787

theorem tailTrace_1228598 : CollatzResearch.WordTrace tailWord_1228598 prefixEnd_1228598 630861305152689338374787 := by
  unfold tailWord_1228598
  simp only [CollatzResearch.WordTrace]
  refine ⟨2800665650187921792391403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 29873766935337832452174965 2800665650187921792391403)
  ·
    refine ⟨4200998475281882688587105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2800665650187921792391403 4200998475281882688587105)
    ·
      refine ⟨3150748856461412016440329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4200998475281882688587105 3150748856461412016440329)
      ·
        refine ⟨2363061642346059012330247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3150748856461412016440329 2363061642346059012330247)
        ·
          refine ⟨3544592463519088518495371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2363061642346059012330247 3544592463519088518495371)
          ·
            refine ⟨5316888695278632777743057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3544592463519088518495371 5316888695278632777743057)
            ·
              refine ⟨3987666521458974583307293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5316888695278632777743057 3987666521458974583307293)
              ·
                refine ⟨1495374945547115468740235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3987666521458974583307293 1495374945547115468740235)
                ·
                  refine ⟨2243062418320673203110353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1495374945547115468740235 2243062418320673203110353)
                  ·
                    refine ⟨1682296813740504902332765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2243062418320673203110353 1682296813740504902332765)
                    ·
                      refine ⟨630861305152689338374787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1682296813740504902332765 630861305152689338374787)
                      ·
                        rfl

theorem cell23_1228598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_1228598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1228598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1228598 prefixEnd_1228598 := by exact prefixLift 1228598
  have htrace : WordTrace (prefixWord ++ tailWord_1228598) baseStart_1228598 baseEnd_1228598 := by
    simpa [prefixWord, tailWord_1228598, baseEnd_1228598] using wordTrace_append hprefix tailTrace_1228598
  have hstable : (prefixWord ++ tailWord_1228598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1228598).length < 2 ^ (prefixWord ++ tailWord_1228598).sum := by decide
  have hdescent : baseEnd_1228598 < baseStart_1228598 := by decide
  rcases family_descends (prefixWord ++ tailWord_1228598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1228601 : List Nat := [1, 2, 1, 7, 2, 1, 9]
def baseStart_1228601 : Nat := 118140960795 + 1228601 * 2 ^ 59
def prefixEnd_1228601 : Nat := 4983230072969 + 3 ^ 40 * 1228601 * 2
def baseEnd_1228601 : Nat := 7788430192526578106633

theorem tailTrace_1228601 : CollatzResearch.WordTrace tailWord_1228601 prefixEnd_1228601 7788430192526578106633 := by
  unfold tailWord_1228601
  simp only [CollatzResearch.WordTrace]
  refine ⟨44810759821995880190621657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29873839881330586793747771 44810759821995880190621657)
  ·
    refine ⟨33608069866496910142966243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44810759821995880190621657 33608069866496910142966243)
    ·
      refine ⟨50412104799745365214449365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33608069866496910142966243 50412104799745365214449365)
      ·
        refine ⟨1181533706244031997213657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 50412104799745365214449365 1181533706244031997213657)
        ·
          refine ⟨886150279683023997910243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1181533706244031997213657 886150279683023997910243)
          ·
            refine ⟨1329225419524535996865365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 886150279683023997910243 1329225419524535996865365)
            ·
              refine ⟨7788430192526578106633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1329225419524535996865365 7788430192526578106633)
              ·
                rfl

theorem cell23_1228601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 9].length) (baseStart_1228601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1228601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1228601 prefixEnd_1228601 := by exact prefixLift 1228601
  have htrace : WordTrace (prefixWord ++ tailWord_1228601) baseStart_1228601 baseEnd_1228601 := by
    simpa [prefixWord, tailWord_1228601, baseEnd_1228601] using wordTrace_append hprefix tailTrace_1228601
  have hstable : (prefixWord ++ tailWord_1228601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1228601).length < 2 ^ (prefixWord ++ tailWord_1228601).sum := by decide
  have hdescent : baseEnd_1228601 < baseStart_1228601 := by decide
  rcases family_descends (prefixWord ++ tailWord_1228601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1228617 : List Nat := [1, 2, 1, 1, 2, 4, 2, 1, 2, 3, 4]
def baseStart_1228617 : Nat := 118140960795 + 1228617 * 2 ^ 59
def prefixEnd_1228617 : Nat := 4983230072969 + 3 ^ 40 * 1228617 * 2
def baseEnd_1228617 : Nat := 630871061285124764037199

theorem tailTrace_1228617 : CollatzResearch.WordTrace tailWord_1228617 prefixEnd_1228617 630871061285124764037199 := by
  unfold tailWord_1228617
  simp only [CollatzResearch.WordTrace]
  refine ⟨44811343389937914923204105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29874228926625276615469403 44811343389937914923204105)
  ·
    refine ⟨33608507542453436192403079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44811343389937914923204105 33608507542453436192403079)
    ·
      refine ⟨50412761313680154288604619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33608507542453436192403079 50412761313680154288604619)
      ·
        refine ⟨75619141970520231432906929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50412761313680154288604619 75619141970520231432906929)
        ·
          refine ⟨56714356477890173574680197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75619141970520231432906929 56714356477890173574680197)
          ·
            refine ⟨10633941839604407545252537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56714356477890173574680197 10633941839604407545252537)
            ·
              refine ⟨7975456379703305658939403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10633941839604407545252537 7975456379703305658939403)
              ·
                refine ⟨11963184569554958488409105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7975456379703305658939403 11963184569554958488409105)
                ·
                  refine ⟨8972388427166218866306829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11963184569554958488409105 8972388427166218866306829)
                  ·
                    refine ⟨3364645660187332074865061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8972388427166218866306829 3364645660187332074865061)
                    ·
                      refine ⟨630871061285124764037199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3364645660187332074865061 630871061285124764037199)
                      ·
                        rfl

theorem cell23_1228617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 1, 2, 3, 4].length) (baseStart_1228617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1228617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1228617 prefixEnd_1228617 := by exact prefixLift 1228617
  have htrace : WordTrace (prefixWord ++ tailWord_1228617) baseStart_1228617 baseEnd_1228617 := by
    simpa [prefixWord, tailWord_1228617, baseEnd_1228617] using wordTrace_append hprefix tailTrace_1228617
  have hstable : (prefixWord ++ tailWord_1228617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1228617).length < 2 ^ (prefixWord ++ tailWord_1228617).sum := by decide
  have hdescent : baseEnd_1228617 < baseStart_1228617 := by decide
  rcases family_descends (prefixWord ++ tailWord_1228617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1228628 : List Nat := [2, 4, 1, 1, 3, 2, 1, 3, 2, 1, 3]
def baseStart_1228628 : Nat := 118140960795 + 1228628 * 2 ^ 59
def prefixEnd_1228628 : Nat := 4983230072969 + 3 ^ 40 * 1228628 * 2
def baseEnd_1228628 : Nat := 630876709572324220999649

theorem tailTrace_1228628 : CollatzResearch.WordTrace tailWord_1228628 prefixEnd_1228628 630876709572324220999649 := by
  unfold tailWord_1228628
  simp only [CollatzResearch.WordTrace]
  refine ⟨22405872296449031900927269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29874496395265375867903025 22405872296449031900927269)
  ·
    refine ⟨4201101055584193481423863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22405872296449031900927269 4201101055584193481423863)
    ·
      refine ⟨6301651583376290222135795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4201101055584193481423863 6301651583376290222135795)
      ·
        refine ⟨9452477375064435333203693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6301651583376290222135795 9452477375064435333203693)
        ·
          refine ⟨3544679015649163249951385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9452477375064435333203693 3544679015649163249951385)
          ·
            refine ⟨2658509261736872437463539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3544679015649163249951385 2658509261736872437463539)
            ·
              refine ⟨3987763892605308656195309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2658509261736872437463539 3987763892605308656195309)
              ·
                refine ⟨1495411459726990746073241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3987763892605308656195309 1495411459726990746073241)
                ·
                  refine ⟨1121558594795243059554931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1495411459726990746073241 1121558594795243059554931)
                  ·
                    refine ⟨1682337892192864589332397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1121558594795243059554931 1682337892192864589332397)
                    ·
                      refine ⟨630876709572324220999649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1682337892192864589332397 630876709572324220999649)
                      ·
                        rfl

theorem cell23_1228628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 3, 2, 1, 3].length) (baseStart_1228628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1228628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1228628 prefixEnd_1228628 := by exact prefixLift 1228628
  have htrace : WordTrace (prefixWord ++ tailWord_1228628) baseStart_1228628 baseEnd_1228628 := by
    simpa [prefixWord, tailWord_1228628, baseEnd_1228628] using wordTrace_append hprefix tailTrace_1228628
  have hstable : (prefixWord ++ tailWord_1228628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1228628).length < 2 ^ (prefixWord ++ tailWord_1228628).sum := by decide
  have hdescent : baseEnd_1228628 < baseStart_1228628 := by decide
  rcases family_descends (prefixWord ++ tailWord_1228628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1228697 : List Nat := [1, 2, 1, 2, 1, 3, 2, 2, 1, 1, 7]
def baseStart_1228697 : Nat := 118140960795 + 1228697 * 2 ^ 59
def prefixEnd_1228697 : Nat := 4983230072969 + 3 ^ 40 * 1228697 * 2
def baseEnd_1228697 : Nat := 630912139737484451036831

theorem tailTrace_1228697 : CollatzResearch.WordTrace tailWord_1228697 prefixEnd_1228697 630912139737484451036831 := by
  unfold tailWord_1228697
  simp only [CollatzResearch.WordTrace]
  refine ⟨44814261229648088586116345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29876174153098725724077563 44814261229648088586116345)
  ·
    refine ⟨33610695922236066439587259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44814261229648088586116345 33610695922236066439587259)
    ·
      refine ⟨50416043883354099659380889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33610695922236066439587259 50416043883354099659380889)
      ·
        refine ⟨37812032912515574744535667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50416043883354099659380889 37812032912515574744535667)
        ·
          refine ⟨56718049368773362116803501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37812032912515574744535667 56718049368773362116803501)
          ·
            refine ⟨21269268513290010793801313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56718049368773362116803501 21269268513290010793801313)
            ·
              refine ⟨15951951384967508095350985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21269268513290010793801313 15951951384967508095350985)
              ·
                refine ⟨11963963538725631071513239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15951951384967508095350985 11963963538725631071513239)
                ·
                  refine ⟨17945945308088446607269859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11963963538725631071513239 17945945308088446607269859)
                  ·
                    refine ⟨26918917962132669910904789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17945945308088446607269859 26918917962132669910904789)
                    ·
                      refine ⟨630912139737484451036831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 26918917962132669910904789 630912139737484451036831)
                      ·
                        rfl

theorem cell23_1228697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 2, 1, 1, 7].length) (baseStart_1228697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1228697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1228697 prefixEnd_1228697 := by exact prefixLift 1228697
  have htrace : WordTrace (prefixWord ++ tailWord_1228697) baseStart_1228697 baseEnd_1228697 := by
    simpa [prefixWord, tailWord_1228697, baseEnd_1228697] using wordTrace_append hprefix tailTrace_1228697
  have hstable : (prefixWord ++ tailWord_1228697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1228697).length < 2 ^ (prefixWord ++ tailWord_1228697).sum := by decide
  have hdescent : baseEnd_1228697 < baseStart_1228697 := by decide
  rcases family_descends (prefixWord ++ tailWord_1228697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1228785 : List Nat := [1, 2, 2, 2, 6, 1, 1, 1, 3, 4]
def baseStart_1228785 : Nat := 118140960795 + 1228785 * 2 ^ 59
def prefixEnd_1228785 : Nat := 4983230072969 + 3 ^ 40 * 1228785 * 2
def baseEnd_1228785 : Nat := 210319108678360035578809

theorem tailTrace_1228785 : CollatzResearch.WordTrace tailWord_1228785 prefixEnd_1228785 210319108678360035578809 := by
  unfold tailWord_1228785
  simp only [CollatzResearch.WordTrace]
  refine ⟨44817470853329279615319809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29878313902219519743546539 44817470853329279615319809)
  ·
    refine ⟨33613103139996959711489857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44817470853329279615319809 33613103139996959711489857)
    ·
      refine ⟨25209827354997719783617393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33613103139996959711489857 25209827354997719783617393)
      ·
        refine ⟨18907370516248289837713045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25209827354997719783617393 18907370516248289837713045)
        ·
          refine ⟨886282992949138586142799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 18907370516248289837713045 886282992949138586142799)
          ·
            refine ⟨1329424489423707879214199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 886282992949138586142799 1329424489423707879214199)
            ·
              refine ⟨1994136734135561818821299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1329424489423707879214199 1994136734135561818821299)
              ·
                refine ⟨2991205101203342728231949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1994136734135561818821299 2991205101203342728231949)
                ·
                  refine ⟨1121701912951253523086981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2991205101203342728231949 1121701912951253523086981)
                  ·
                    refine ⟨210319108678360035578809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1121701912951253523086981 210319108678360035578809)
                    ·
                      rfl

theorem cell23_1228785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 1, 1, 3, 4].length) (baseStart_1228785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1228785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1228785 prefixEnd_1228785 := by exact prefixLift 1228785
  have htrace : WordTrace (prefixWord ++ tailWord_1228785) baseStart_1228785 baseEnd_1228785 := by
    simpa [prefixWord, tailWord_1228785, baseEnd_1228785] using wordTrace_append hprefix tailTrace_1228785
  have hstable : (prefixWord ++ tailWord_1228785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1228785).length < 2 ^ (prefixWord ++ tailWord_1228785).sum := by decide
  have hdescent : baseEnd_1228785 < baseStart_1228785 := by decide
  rcases family_descends (prefixWord ++ tailWord_1228785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1228798 : List Nat := [4, 2, 2, 2, 1, 2, 1, 3, 6]
def baseStart_1228798 : Nat := 118140960795 + 1228798 * 2 ^ 59
def prefixEnd_1228798 : Nat := 4983230072969 + 3 ^ 40 * 1228798 * 2
def baseEnd_1228798 : Nat := 70107111253732061763763

theorem tailTrace_1228798 : CollatzResearch.WordTrace tailWord_1228798 prefixEnd_1228798 70107111253732061763763 := by
  unfold tailWord_1228798
  simp only [CollatzResearch.WordTrace]
  refine ⟨5602243125285272854442881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29878630001521455223695365 5602243125285272854442881)
  ·
    refine ⟨4201682343963954640832161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5602243125285272854442881 4201682343963954640832161)
    ·
      refine ⟨3151261757972965980624121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4201682343963954640832161 3151261757972965980624121)
      ·
        refine ⟨2363446318479724485468091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3151261757972965980624121 2363446318479724485468091)
        ·
          refine ⟨3545169477719586728202137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2363446318479724485468091 3545169477719586728202137)
          ·
            refine ⟨2658877108289690046151603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3545169477719586728202137 2658877108289690046151603)
            ·
              refine ⟨3988315662434535069227405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2658877108289690046151603 3988315662434535069227405)
              ·
                refine ⟨1495618373412950650960277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3988315662434535069227405 1495618373412950650960277)
                ·
                  refine ⟨70107111253732061763763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1495618373412950650960277 70107111253732061763763)
                  ·
                    rfl

theorem cell23_1228798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 3, 6].length) (baseStart_1228798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1228798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1228798 prefixEnd_1228798 := by exact prefixLift 1228798
  have htrace : WordTrace (prefixWord ++ tailWord_1228798) baseStart_1228798 baseEnd_1228798 := by
    simpa [prefixWord, tailWord_1228798, baseEnd_1228798] using wordTrace_append hprefix tailTrace_1228798
  have hstable : (prefixWord ++ tailWord_1228798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1228798).length < 2 ^ (prefixWord ++ tailWord_1228798).sum := by decide
  have hdescent : baseEnd_1228798 < baseStart_1228798 := by decide
  rcases family_descends (prefixWord ++ tailWord_1228798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1228842 : List Nat := [3, 1, 4, 1, 2, 2, 1, 4, 1, 1, 3]
def baseStart_1228842 : Nat := 118140960795 + 1228842 * 2 ^ 59
def prefixEnd_1228842 : Nat := 4983230072969 + 3 ^ 40 * 1228842 * 2
def baseEnd_1228842 : Nat := 630986594432386383723665

theorem tailTrace_1228842 : CollatzResearch.WordTrace tailWord_1228842 prefixEnd_1228842 630986594432386383723665 := by
  unfold tailWord_1228842
  simp only [CollatzResearch.WordTrace]
  refine ⟨11204887453530694587536195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29879699876081852233429853 11204887453530694587536195)
  ·
    refine ⟨16807331180296041881304293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11204887453530694587536195 16807331180296041881304293)
    ·
      refine ⟨3151374596305507852744555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16807331180296041881304293 3151374596305507852744555)
      ·
        refine ⟨4727061894458261779116833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3151374596305507852744555 4727061894458261779116833)
        ·
          refine ⟨3545296420843696334337625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4727061894458261779116833 3545296420843696334337625)
          ·
            refine ⟨2658972315632772250753219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3545296420843696334337625 2658972315632772250753219)
            ·
              refine ⟨3988458473449158376129829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2658972315632772250753219 3988458473449158376129829)
              ·
                refine ⟨747835963771717195524343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3988458473449158376129829 747835963771717195524343)
                ·
                  refine ⟨1121753945657575793286515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 747835963771717195524343 1121753945657575793286515)
                  ·
                    refine ⟨1682630918486363689929773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1121753945657575793286515 1682630918486363689929773)
                    ·
                      refine ⟨630986594432386383723665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1682630918486363689929773 630986594432386383723665)
                      ·
                        rfl

theorem cell23_1228842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 4, 1, 1, 3].length) (baseStart_1228842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1228842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1228842 prefixEnd_1228842 := by exact prefixLift 1228842
  have htrace : WordTrace (prefixWord ++ tailWord_1228842) baseStart_1228842 baseEnd_1228842 := by
    simpa [prefixWord, tailWord_1228842, baseEnd_1228842] using wordTrace_append hprefix tailTrace_1228842
  have hstable : (prefixWord ++ tailWord_1228842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1228842).length < 2 ^ (prefixWord ++ tailWord_1228842).sum := by decide
  have hdescent : baseEnd_1228842 < baseStart_1228842 := by decide
  rcases family_descends (prefixWord ++ tailWord_1228842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1228844 : List Nat := [2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 6]
def baseStart_1228844 : Nat := 118140960795 + 1228844 * 2 ^ 59
def prefixEnd_1228844 : Nat := 4983230072969 + 3 ^ 40 * 1228844 * 2
def baseEnd_1228844 : Nat := 630987621393695375898655

theorem tailTrace_1228844 : CollatzResearch.WordTrace tailWord_1228844 prefixEnd_1228844 630987621393695375898655 := by
  unfold tailWord_1228844
  simp only [CollatzResearch.WordTrace]
  refine ⟨22409811380057766345858793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29879748506743688461145057 22409811380057766345858793)
  ·
    refine ⟨16807358535043324759394095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22409811380057766345858793 16807358535043324759394095)
    ·
      refine ⟨25211037802564987139091143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16807358535043324759394095 25211037802564987139091143)
      ·
        refine ⟨37816556703847480708636715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25211037802564987139091143 37816556703847480708636715)
        ·
          refine ⟨56724835055771221062955073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37816556703847480708636715 56724835055771221062955073)
          ·
            refine ⟨42543626291828415797216305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56724835055771221062955073 42543626291828415797216305)
            ·
              refine ⟨31907719718871311847912229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42543626291828415797216305 31907719718871311847912229)
              ·
                refine ⟨5982697447288370971483543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31907719718871311847912229 5982697447288370971483543)
                ·
                  refine ⟨8974046170932556457225315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5982697447288370971483543 8974046170932556457225315)
                  ·
                    refine ⟨13461069256398834685837973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8974046170932556457225315 13461069256398834685837973)
                    ·
                      refine ⟨630987621393695375898655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13461069256398834685837973 630987621393695375898655)
                      ·
                        rfl

theorem cell23_1228844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 6].length) (baseStart_1228844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1228844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1228844 prefixEnd_1228844 := by exact prefixLift 1228844
  have htrace : WordTrace (prefixWord ++ tailWord_1228844) baseStart_1228844 baseEnd_1228844 := by
    simpa [prefixWord, tailWord_1228844, baseEnd_1228844] using wordTrace_append hprefix tailTrace_1228844
  have hstable : (prefixWord ++ tailWord_1228844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1228844).length < 2 ^ (prefixWord ++ tailWord_1228844).sum := by decide
  have hdescent : baseEnd_1228844 < baseStart_1228844 := by decide
  rcases family_descends (prefixWord ++ tailWord_1228844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1228851 : List Nat := [1, 1, 1, 2, 4, 1, 3, 2, 3, 2, 3]
def baseStart_1228851 : Nat := 118140960795 + 1228851 * 2 ^ 59
def prefixEnd_1228851 : Nat := 4983230072969 + 3 ^ 40 * 1228851 * 2
def baseEnd_1228851 : Nat := 630991215758276848511123

theorem tailTrace_1228851 : CollatzResearch.WordTrace tailWord_1228851 prefixEnd_1228851 630991215758276848511123 := by
  unfold tailWord_1228851
  simp only [CollatzResearch.WordTrace]
  refine ⟨44819878071090172887222407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29879918714060115258148271 44819878071090172887222407)
  ·
    refine ⟨67229817106635259330833611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44819878071090172887222407 67229817106635259330833611)
    ·
      refine ⟨100844725659952888996250417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67229817106635259330833611 100844725659952888996250417)
      ·
        refine ⟨75633544244964666747187813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100844725659952888996250417 75633544244964666747187813)
        ·
          refine ⟨14181289545930875015097715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 75633544244964666747187813 14181289545930875015097715)
          ·
            refine ⟨21271934318896312522646573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14181289545930875015097715 21271934318896312522646573)
            ·
              refine ⟨7976975369586117195992465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21271934318896312522646573 7976975369586117195992465)
              ·
                refine ⟨5982731527189587896994349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7976975369586117195992465 5982731527189587896994349)
                ·
                  refine ⟨2243524322696095461372881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5982731527189587896994349 2243524322696095461372881)
                  ·
                    refine ⟨1682643242022071596029661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2243524322696095461372881 1682643242022071596029661)
                    ·
                      refine ⟨630991215758276848511123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1682643242022071596029661 630991215758276848511123)
                      ·
                        rfl

theorem cell23_1228851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 2, 3, 2, 3].length) (baseStart_1228851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1228851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1228851 prefixEnd_1228851 := by exact prefixLift 1228851
  have htrace : WordTrace (prefixWord ++ tailWord_1228851) baseStart_1228851 baseEnd_1228851 := by
    simpa [prefixWord, tailWord_1228851, baseEnd_1228851] using wordTrace_append hprefix tailTrace_1228851
  have hstable : (prefixWord ++ tailWord_1228851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1228851).length < 2 ^ (prefixWord ++ tailWord_1228851).sum := by decide
  have hdescent : baseEnd_1228851 < baseStart_1228851 := by decide
  rcases family_descends (prefixWord ++ tailWord_1228851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1228865 : List Nat := [1, 2, 5, 1, 2, 1, 1, 1, 5, 2, 2]
def baseStart_1228865 : Nat := 118140960795 + 1228865 * 2 ^ 59
def prefixEnd_1228865 : Nat := 4983230072969 + 3 ^ 40 * 1228865 * 2
def baseEnd_1228865 : Nat := 630998404487439793736059

theorem tailTrace_1228865 : CollatzResearch.WordTrace tailWord_1228865 prefixEnd_1228865 630998404487439793736059 := by
  unfold tailWord_1228865
  simp only [CollatzResearch.WordTrace]
  refine ⟨44820388693039453278232049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29880259128692968852154699 44820388693039453278232049)
  ·
    refine ⟨33615291519779589958674037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44820388693039453278232049 33615291519779589958674037)
    ·
      refine ⟨3151433579979336558625691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 33615291519779589958674037 3151433579979336558625691)
      ·
        refine ⟨4727150369969004837938537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3151433579979336558625691 4727150369969004837938537)
        ·
          refine ⟨3545362777476753628453903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4727150369969004837938537 3545362777476753628453903)
          ·
            refine ⟨5318044166215130442680855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3545362777476753628453903 5318044166215130442680855)
            ·
              refine ⟨7977066249322695664021283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5318044166215130442680855 7977066249322695664021283)
              ·
                refine ⟨11965599373984043496031925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7977066249322695664021283 11965599373984043496031925)
                ·
                  refine ⟨1121774941311004077752993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11965599373984043496031925 1121774941311004077752993)
                  ·
                    refine ⟨841331205983253058314745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1121774941311004077752993 841331205983253058314745)
                    ·
                      refine ⟨630998404487439793736059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 841331205983253058314745 630998404487439793736059)
                      ·
                        rfl

theorem cell23_1228865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 1, 5, 2, 2].length) (baseStart_1228865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1228865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1228865 prefixEnd_1228865 := by exact prefixLift 1228865
  have htrace : WordTrace (prefixWord ++ tailWord_1228865) baseStart_1228865 baseEnd_1228865 := by
    simpa [prefixWord, tailWord_1228865, baseEnd_1228865] using wordTrace_append hprefix tailTrace_1228865
  have hstable : (prefixWord ++ tailWord_1228865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1228865).length < 2 ^ (prefixWord ++ tailWord_1228865).sum := by decide
  have hdescent : baseEnd_1228865 < baseStart_1228865 := by decide
  rcases family_descends (prefixWord ++ tailWord_1228865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1228871 : List Nat := [1, 1, 4, 1, 3, 1, 5, 7]
def baseStart_1228871 : Nat := 118140960795 + 1228871 * 2 ^ 59
def prefixEnd_1228871 : Nat := 4983230072969 + 3 ^ 40 * 1228871 * 2
def baseEnd_1228871 : Nat := 23370425384124695194853

theorem tailTrace_1228871 : CollatzResearch.WordTrace tailWord_1228871 prefixEnd_1228871 23370425384124695194853 := by
  unfold tailWord_1228871
  simp only [CollatzResearch.WordTrace]
  refine ⟨44820607531017716302950467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29880405020678477535300311 44820607531017716302950467)
  ·
    refine ⟨67230911296526574454425701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44820607531017716302950467 67230911296526574454425701)
    ·
      refine ⟨12605795868098732710204819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 67230911296526574454425701 12605795868098732710204819)
      ·
        refine ⟨18908693802148099065307229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12605795868098732710204819 18908693802148099065307229)
        ·
          refine ⟨7090760175805537149490211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18908693802148099065307229 7090760175805537149490211)
          ·
            refine ⟨10636140263708305724235317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7090760175805537149490211 10636140263708305724235317)
            ·
              refine ⟨997138149722653661647061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10636140263708305724235317 997138149722653661647061)
              ·
                refine ⟨23370425384124695194853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 997138149722653661647061 23370425384124695194853)
                ·
                  rfl

theorem cell23_1228871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 5, 7].length) (baseStart_1228871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1228871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1228871 prefixEnd_1228871 := by exact prefixLift 1228871
  have htrace : WordTrace (prefixWord ++ tailWord_1228871) baseStart_1228871 baseEnd_1228871 := by
    simpa [prefixWord, tailWord_1228871, baseEnd_1228871] using wordTrace_append hprefix tailTrace_1228871
  have hstable : (prefixWord ++ tailWord_1228871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1228871).length < 2 ^ (prefixWord ++ tailWord_1228871).sum := by decide
  have hdescent : baseEnd_1228871 < baseStart_1228871 := by decide
  rcases family_descends (prefixWord ++ tailWord_1228871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1228882 : List Nat := [3, 2, 2, 1, 4, 2, 2, 1, 1, 1, 4]
def baseStart_1228882 : Nat := 118140960795 + 1228882 * 2 ^ 59
def prefixEnd_1228882 : Nat := 4983230072969 + 3 ^ 40 * 1228882 * 2
def baseEnd_1228882 : Nat := 631007133658566227223481

theorem tailTrace_1228882 : CollatzResearch.WordTrace tailWord_1228882 prefixEnd_1228882 631007133658566227223481 := by
  unfold tailWord_1228882
  simp only [CollatzResearch.WordTrace]
  refine ⟨11205252183494466295400225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29880672489318576787733933 11205252183494466295400225)
  ·
    refine ⟨8403939137620849721550169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11205252183494466295400225 8403939137620849721550169)
    ·
      refine ⟨6302954353215637291162627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8403939137620849721550169 6302954353215637291162627)
      ·
        refine ⟨9454431529823455936743941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6302954353215637291162627 9454431529823455936743941)
        ·
          refine ⟨1772705911841897988139489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9454431529823455936743941 1772705911841897988139489)
          ·
            refine ⟨1329529433881423491104617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1772705911841897988139489 1329529433881423491104617)
            ·
              refine ⟨997147075411067618328463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1329529433881423491104617 997147075411067618328463)
              ·
                refine ⟨1495720613116601427492695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 997147075411067618328463 1495720613116601427492695)
                ·
                  refine ⟨2243580919674902141239043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1495720613116601427492695 2243580919674902141239043)
                  ·
                    refine ⟨3365371379512353211858565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2243580919674902141239043 3365371379512353211858565)
                    ·
                      refine ⟨631007133658566227223481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3365371379512353211858565 631007133658566227223481)
                      ·
                        rfl

theorem cell23_1228882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 2, 1, 1, 1, 4].length) (baseStart_1228882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1228882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1228882 prefixEnd_1228882 := by exact prefixLift 1228882
  have htrace : WordTrace (prefixWord ++ tailWord_1228882) baseStart_1228882 baseEnd_1228882 := by
    simpa [prefixWord, tailWord_1228882, baseEnd_1228882] using wordTrace_append hprefix tailTrace_1228882
  have hstable : (prefixWord ++ tailWord_1228882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1228882).length < 2 ^ (prefixWord ++ tailWord_1228882).sum := by decide
  have hdescent : baseEnd_1228882 < baseStart_1228882 := by decide
  rcases family_descends (prefixWord ++ tailWord_1228882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1228885 : List Nat := [1, 3, 2, 2, 1, 3, 4, 1, 1, 2, 3]
def baseStart_1228885 : Nat := 118140960795 + 1228885 * 2 ^ 59
def prefixEnd_1228885 : Nat := 4983230072969 + 3 ^ 40 * 1228885 * 2
def baseEnd_1228885 : Nat := 631008674100529715485967

theorem tailTrace_1228885 : CollatzResearch.WordTrace tailWord_1228885 prefixEnd_1228885 631008674100529715485967 := by
  unfold tailWord_1228885
  simp only [CollatzResearch.WordTrace]
  refine ⟨44821118152966996693960109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29880745435311331129306739 44821118152966996693960109)
  ·
    refine ⟨16807919307362623760235041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44821118152966996693960109 16807919307362623760235041)
    ·
      refine ⟨12605939480521967820176281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16807919307362623760235041 12605939480521967820176281)
      ·
        refine ⟨9454454610391475865132211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12605939480521967820176281 9454454610391475865132211)
        ·
          refine ⟨14181681915587213797698317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9454454610391475865132211 14181681915587213797698317)
          ·
            refine ⟨5318130718345205174136869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14181681915587213797698317 5318130718345205174136869)
            ·
              refine ⟨997149509689725970150663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5318130718345205174136869 997149509689725970150663)
              ·
                refine ⟨1495724264534588955225995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 997149509689725970150663 1495724264534588955225995)
                ·
                  refine ⟨2243586396801883432838993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1495724264534588955225995 2243586396801883432838993)
                  ·
                    refine ⟨1682689797601412574629245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2243586396801883432838993 1682689797601412574629245)
                    ·
                      refine ⟨631008674100529715485967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1682689797601412574629245 631008674100529715485967)
                      ·
                        rfl

theorem cell23_1228885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 4, 1, 1, 2, 3].length) (baseStart_1228885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1228885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1228885 prefixEnd_1228885 := by exact prefixLift 1228885
  have htrace : WordTrace (prefixWord ++ tailWord_1228885) baseStart_1228885 baseEnd_1228885 := by
    simpa [prefixWord, tailWord_1228885, baseEnd_1228885] using wordTrace_append hprefix tailTrace_1228885
  have hstable : (prefixWord ++ tailWord_1228885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1228885).length < 2 ^ (prefixWord ++ tailWord_1228885).sum := by decide
  have hdescent : baseEnd_1228885 < baseStart_1228885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1228885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1228925 : List Nat := [1, 4, 1, 1, 3, 2, 1, 4, 1, 3, 2]
def baseStart_1228925 : Nat := 118140960795 + 1228925 * 2 ^ 59
def prefixEnd_1228925 : Nat := 4983230072969 + 3 ^ 40 * 1228925 * 2
def baseEnd_1228925 : Nat := 631029213326709558985783

theorem tailTrace_1228925 : CollatzResearch.WordTrace tailWord_1228925 prefixEnd_1228925 631029213326709558985783 := by
  unfold tailWord_1228925
  simp only [CollatzResearch.WordTrace]
  refine ⟨44822577072822083525416229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29881718048548055683610819 44822577072822083525416229)
  ·
    refine ⟨8404233201154140661015543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44822577072822083525416229 8404233201154140661015543)
    ·
      refine ⟨12606349801731210991523315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8404233201154140661015543 12606349801731210991523315)
      ·
        refine ⟨18909524702596816487284973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12606349801731210991523315 18909524702596816487284973)
        ·
          refine ⟨7091071763473806182731865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18909524702596816487284973 7091071763473806182731865)
          ·
            refine ⟨5318303822605354637048899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7091071763473806182731865 5318303822605354637048899)
            ·
              refine ⟨7977455733908031955573349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5318303822605354637048899 7977455733908031955573349)
              ·
                refine ⟨1495772950107755991670003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7977455733908031955573349 1495772950107755991670003)
                ·
                  refine ⟨2243659425161633987505005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1495772950107755991670003 2243659425161633987505005)
                  ·
                    refine ⟨841372284435612745314377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2243659425161633987505005 841372284435612745314377)
                    ·
                      refine ⟨631029213326709558985783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 841372284435612745314377 631029213326709558985783)
                      ·
                        rfl

theorem cell23_1228925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 4, 1, 3, 2].length) (baseStart_1228925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1228925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1228925 prefixEnd_1228925 := by exact prefixLift 1228925
  have htrace : WordTrace (prefixWord ++ tailWord_1228925) baseStart_1228925 baseEnd_1228925 := by
    simpa [prefixWord, tailWord_1228925, baseEnd_1228925] using wordTrace_append hprefix tailTrace_1228925
  have hstable : (prefixWord ++ tailWord_1228925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1228925).length < 2 ^ (prefixWord ++ tailWord_1228925).sum := by decide
  have hdescent : baseEnd_1228925 < baseStart_1228925 := by decide
  rcases family_descends (prefixWord ++ tailWord_1228925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1228950 : List Nat := [5, 3, 2, 1, 1, 2, 1, 1, 3, 2, 2]
def baseStart_1228950 : Nat := 118140960795 + 1228950 * 2 ^ 59
def prefixEnd_1228950 : Nat := 4983230072969 + 3 ^ 40 * 1228950 * 2
def baseEnd_1228950 : Nat := 631042050343071961173169

theorem tailTrace_1228950 : CollatzResearch.WordTrace tailWord_1228950 prefixEnd_1228950 631042050343071961173169 := by
  unfold tailWord_1228950
  simp only [CollatzResearch.WordTrace]
  refine ⟨2801468056108219549692269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 29882325931821008530050869 2801468056108219549692269)
  ·
    refine ⟨1050550521040582331134601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2801468056108219549692269 1050550521040582331134601)
    ·
      refine ⟨787912890780436748350951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1050550521040582331134601 787912890780436748350951)
      ·
        refine ⟨1181869336170655122526427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 787912890780436748350951 1181869336170655122526427)
        ·
          refine ⟨1772804004255982683789641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1181869336170655122526427 1772804004255982683789641)
          ·
            refine ⟨1329603003191987012842231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1772804004255982683789641 1329603003191987012842231)
            ·
              refine ⟨1994404504787980519263347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1329603003191987012842231 1994404504787980519263347)
              ·
                refine ⟨2991606757181970778895021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1994404504787980519263347 2991606757181970778895021)
                ·
                  refine ⟨1121852533943239042085633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2991606757181970778895021 1121852533943239042085633)
                  ·
                    refine ⟨841389400457429281564225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1121852533943239042085633 841389400457429281564225)
                    ·
                      refine ⟨631042050343071961173169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 841389400457429281564225 631042050343071961173169)
                      ·
                        rfl

theorem cell23_1228950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_1228950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1228950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1228950 prefixEnd_1228950 := by exact prefixLift 1228950
  have htrace : WordTrace (prefixWord ++ tailWord_1228950) baseStart_1228950 baseEnd_1228950 := by
    simpa [prefixWord, tailWord_1228950, baseEnd_1228950] using wordTrace_append hprefix tailTrace_1228950
  have hstable : (prefixWord ++ tailWord_1228950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1228950).length < 2 ^ (prefixWord ++ tailWord_1228950).sum := by decide
  have hdescent : baseEnd_1228950 < baseStart_1228950 := by decide
  rcases family_descends (prefixWord ++ tailWord_1228950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1228971 : List Nat := [1, 1, 1, 1, 2, 1, 1, 1, 8, 3, 3]
def baseStart_1228971 : Nat := 118140960795 + 1228971 * 2 ^ 59
def prefixEnd_1228971 : Nat := 4983230072969 + 3 ^ 40 * 1228971 * 2
def baseEnd_1228971 : Nat := 631052833436816379010571

theorem tailTrace_1228971 : CollatzResearch.WordTrace tailWord_1228971 prefixEnd_1228971 631052833436816379010571 := by
  unfold tailWord_1228971
  simp only [CollatzResearch.WordTrace]
  refine ⟨44824254830655433381590767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29882836553770288921060511 44824254830655433381590767)
  ·
    refine ⟨67236382245983150072386151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44824254830655433381590767 67236382245983150072386151)
    ·
      refine ⟨100854573368974725108579227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67236382245983150072386151 100854573368974725108579227)
      ·
        refine ⟨151281860053462087662868841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100854573368974725108579227 151281860053462087662868841)
        ·
          refine ⟨113461395040096565747151631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 151281860053462087662868841 113461395040096565747151631)
          ·
            refine ⟨170192092560144848620727447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113461395040096565747151631 170192092560144848620727447)
            ·
              refine ⟨255288138840217272931091171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 170192092560144848620727447 255288138840217272931091171)
              ·
                refine ⟨382932208260325909396636757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 255288138840217272931091171 382932208260325909396636757)
                ·
                  refine ⟨4487486815550694250741837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 382932208260325909396636757 4487486815550694250741837)
                  ·
                    refine ⟨1682807555831510344028189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4487486815550694250741837 1682807555831510344028189)
                    ·
                      refine ⟨631052833436816379010571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1682807555831510344028189 631052833436816379010571)
                      ·
                        rfl

theorem cell23_1228971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 8, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 8, 3, 3].length) (baseStart_1228971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1228971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1228971 prefixEnd_1228971 := by exact prefixLift 1228971
  have htrace : WordTrace (prefixWord ++ tailWord_1228971) baseStart_1228971 baseEnd_1228971 := by
    simpa [prefixWord, tailWord_1228971, baseEnd_1228971] using wordTrace_append hprefix tailTrace_1228971
  have hstable : (prefixWord ++ tailWord_1228971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1228971).length < 2 ^ (prefixWord ++ tailWord_1228971).sum := by decide
  have hdescent : baseEnd_1228971 < baseStart_1228971 := by decide
  rcases family_descends (prefixWord ++ tailWord_1228971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1229106 : List Nat := [3, 2, 1, 1, 6, 1, 1, 3, 1, 4]
def baseStart_1229106 : Nat := 118140960795 + 1229106 * 2 ^ 59
def prefixEnd_1229106 : Nat := 4983230072969 + 3 ^ 40 * 1229106 * 2
def baseEnd_1229106 : Nat := 210374051108391116940817

theorem tailTrace_1229106 : CollatzResearch.WordTrace tailWord_1229106 prefixEnd_1229106 210374051108391116940817 := by
  unfold tailWord_1229106
  simp only [CollatzResearch.WordTrace]
  refine ⟨11207294671291587859438793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29886119123444234291836781 11207294671291587859438793)
  ·
    refine ⟨8405471003468690894579095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11207294671291587859438793 8405471003468690894579095)
    ·
      refine ⟨12608206505203036341868643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8405471003468690894579095 12608206505203036341868643)
      ·
        refine ⟨18912309757804554512802965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12608206505203036341868643 18912309757804554512802965)
        ·
          refine ⟨886514519897088492787639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 18912309757804554512802965 886514519897088492787639)
          ·
            refine ⟨1329771779845632739181459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 886514519897088492787639 1329771779845632739181459)
            ·
              refine ⟨1994657669768449108772189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1329771779845632739181459 1994657669768449108772189)
              ·
                refine ⟨747996626163168415789571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1994657669768449108772189 747996626163168415789571)
                ·
                  refine ⟨1121994939244752623684357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 747996626163168415789571 1121994939244752623684357)
                  ·
                    refine ⟨210374051108391116940817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1121994939244752623684357 210374051108391116940817)
                    ·
                      rfl

theorem cell23_1229106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 1, 3, 1, 4].length) (baseStart_1229106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1229106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1229106 prefixEnd_1229106 := by exact prefixLift 1229106
  have htrace : WordTrace (prefixWord ++ tailWord_1229106) baseStart_1229106 baseEnd_1229106 := by
    simpa [prefixWord, tailWord_1229106, baseEnd_1229106] using wordTrace_append hprefix tailTrace_1229106
  have hstable : (prefixWord ++ tailWord_1229106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1229106).length < 2 ^ (prefixWord ++ tailWord_1229106).sum := by decide
  have hdescent : baseEnd_1229106 < baseStart_1229106 := by decide
  rcases family_descends (prefixWord ++ tailWord_1229106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1229155 : List Nat := [1, 1, 1, 5, 2, 1, 3, 1, 3, 2, 3]
def baseStart_1229155 : Nat := 118140960795 + 1229155 * 2 ^ 59
def prefixEnd_1229155 : Nat := 4983230072969 + 3 ^ 40 * 1229155 * 2
def baseEnd_1229155 : Nat := 631147313877243659109725

theorem tailTrace_1229155 : CollatzResearch.WordTrace tailWord_1229155 prefixEnd_1229155 631147313877243659109725 := by
  unfold tailWord_1229155
  simp only [CollatzResearch.WordTrace]
  refine ⟨44830965861988832806288919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29887310574659221870859279 44830965861988832806288919)
  ·
    refine ⟨67246448792983249209433379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44830965861988832806288919 67246448792983249209433379)
    ·
      refine ⟨100869673189474873814150069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67246448792983249209433379 100869673189474873814150069)
      ·
        refine ⟨9456531861513269420076569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 100869673189474873814150069 9456531861513269420076569)
        ·
          refine ⟨7092398896134952065057427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9456531861513269420076569 7092398896134952065057427)
          ·
            refine ⟨10638598344202428097586141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7092398896134952065057427 10638598344202428097586141)
            ·
              refine ⟨3989474379075910536594803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10638598344202428097586141 3989474379075910536594803)
              ·
                refine ⟨5984211568613865804892205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3989474379075910536594803 5984211568613865804892205)
                ·
                  refine ⟨2244079338230199676834577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5984211568613865804892205 2244079338230199676834577)
                  ·
                    refine ⟨1683059503672649757625933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2244079338230199676834577 1683059503672649757625933)
                    ·
                      refine ⟨631147313877243659109725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1683059503672649757625933 631147313877243659109725)
                      ·
                        rfl

theorem cell23_1229155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 1, 3, 2, 3].length) (baseStart_1229155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1229155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1229155 prefixEnd_1229155 := by exact prefixLift 1229155
  have htrace : WordTrace (prefixWord ++ tailWord_1229155) baseStart_1229155 baseEnd_1229155 := by
    simpa [prefixWord, tailWord_1229155, baseEnd_1229155] using wordTrace_append hprefix tailTrace_1229155
  have hstable : (prefixWord ++ tailWord_1229155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1229155).length < 2 ^ (prefixWord ++ tailWord_1229155).sum := by decide
  have hdescent : baseEnd_1229155 < baseStart_1229155 := by decide
  rcases family_descends (prefixWord ++ tailWord_1229155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1229165 : List Nat := [1, 5, 1, 1, 1, 2, 3, 2, 1, 2, 4]
def baseStart_1229165 : Nat := 118140960795 + 1229165 * 2 ^ 59
def prefixEnd_1229165 : Nat := 4983230072969 + 3 ^ 40 * 1229165 * 2
def baseEnd_1229165 : Nat := 631152448683788619984679

theorem tailTrace_1229165 : CollatzResearch.WordTrace tailWord_1229165 prefixEnd_1229165 631152448683788619984679 := by
  unfold tailWord_1229165
  simp only [CollatzResearch.WordTrace]
  refine ⟨44831330591952604514152949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29887553727968403009435299 44831330591952604514152949)
  ·
    refine ⟨4202937242995556673201839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 44831330591952604514152949 4202937242995556673201839)
    ·
      refine ⟨6304405864493335009802759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4202937242995556673201839 6304405864493335009802759)
      ·
        refine ⟨9456608796740002514704139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6304405864493335009802759 9456608796740002514704139)
        ·
          refine ⟨14184913195110003772056209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9456608796740002514704139 14184913195110003772056209)
          ·
            refine ⟨10638684896332502829042157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14184913195110003772056209 10638684896332502829042157)
            ·
              refine ⟨3989506836124688560890809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10638684896332502829042157 3989506836124688560890809)
              ·
                refine ⟨2992130127093516420668107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3989506836124688560890809 2992130127093516420668107)
                ·
                  refine ⟨4488195190640274631002161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2992130127093516420668107 4488195190640274631002161)
                  ·
                    refine ⟨3366146392980205973251621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4488195190640274631002161 3366146392980205973251621)
                    ·
                      refine ⟨631152448683788619984679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3366146392980205973251621 631152448683788619984679)
                      ·
                        rfl

theorem cell23_1229165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 2, 1, 2, 4].length) (baseStart_1229165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1229165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1229165 prefixEnd_1229165 := by exact prefixLift 1229165
  have htrace : WordTrace (prefixWord ++ tailWord_1229165) baseStart_1229165 baseEnd_1229165 := by
    simpa [prefixWord, tailWord_1229165, baseEnd_1229165] using wordTrace_append hprefix tailTrace_1229165
  have hstable : (prefixWord ++ tailWord_1229165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1229165).length < 2 ^ (prefixWord ++ tailWord_1229165).sum := by decide
  have hdescent : baseEnd_1229165 < baseStart_1229165 := by decide
  rcases family_descends (prefixWord ++ tailWord_1229165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1229169 : List Nat := [1, 2, 2, 2, 1, 2, 1, 7, 1, 2, 2]
def baseStart_1229169 : Nat := 118140960795 + 1229169 * 2 ^ 59
def prefixEnd_1229169 : Nat := 4983230072969 + 3 ^ 40 * 1229169 * 2
def baseEnd_1229169 : Nat := 631154502606406604334661

theorem tailTrace_1229169 : CollatzResearch.WordTrace tailWord_1229169 prefixEnd_1229169 631154502606406604334661 := by
  unfold tailWord_1229169
  simp only [CollatzResearch.WordTrace]
  refine ⟨44831476483938113197298561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29887650989292075464865707 44831476483938113197298561)
  ·
    refine ⟨33623607362953584897973921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44831476483938113197298561 33623607362953584897973921)
    ·
      refine ⟨25217705522215188673480441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33623607362953584897973921 25217705522215188673480441)
      ·
        refine ⟨18913279141661391505110331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25217705522215188673480441 18913279141661391505110331)
        ·
          refine ⟨28369918712492087257665497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18913279141661391505110331 28369918712492087257665497)
          ·
            refine ⟨21277439034369065443249123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28369918712492087257665497 21277439034369065443249123)
            ·
              refine ⟨31916158551553598164873685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21277439034369065443249123 31916158551553598164873685)
              ·
                refine ⟨748034966052037456989227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 31916158551553598164873685 748034966052037456989227)
                ·
                  refine ⟨1122052449078056185483841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 748034966052037456989227 1122052449078056185483841)
                  ·
                    refine ⟨841539336808542139112881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1122052449078056185483841 841539336808542139112881)
                    ·
                      refine ⟨631154502606406604334661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 841539336808542139112881 631154502606406604334661)
                      ·
                        rfl

theorem cell23_1229169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 7, 1, 2, 2].length) (baseStart_1229169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1229169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1229169 prefixEnd_1229169 := by exact prefixLift 1229169
  have htrace : WordTrace (prefixWord ++ tailWord_1229169) baseStart_1229169 baseEnd_1229169 := by
    simpa [prefixWord, tailWord_1229169, baseEnd_1229169] using wordTrace_append hprefix tailTrace_1229169
  have hstable : (prefixWord ++ tailWord_1229169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1229169).length < 2 ^ (prefixWord ++ tailWord_1229169).sum := by decide
  have hdescent : baseEnd_1229169 < baseStart_1229169 := by decide
  rcases family_descends (prefixWord ++ tailWord_1229169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1229188 : List Nat := [2, 3, 2, 1, 1, 2, 1, 1, 1, 9]
def baseStart_1229188 : Nat := 118140960795 + 1229188 * 2 ^ 59
def prefixEnd_1229188 : Nat := 4983230072969 + 3 ^ 40 * 1229188 * 2
def baseEnd_1229188 : Nat := 210388086246280676665691

theorem tailTrace_1229188 : CollatzResearch.WordTrace tailWord_1229188 prefixEnd_1229188 210388086246280676665691 := by
  unfold tailWord_1229188
  simp only [CollatzResearch.WordTrace]
  refine ⟨22416084735434639721120109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29888112980579519628160145 22416084735434639721120109)
  ·
    refine ⟨8406031775787989895420041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22416084735434639721120109 8406031775787989895420041)
    ·
      refine ⟨6304523831840992421565031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8406031775787989895420041 6304523831840992421565031)
      ·
        refine ⟨9456785747761488632347547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6304523831840992421565031 9456785747761488632347547)
        ·
          refine ⟨14185178621642232948521321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9456785747761488632347547 14185178621642232948521321)
          ·
            refine ⟨10638883966231674711390991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14185178621642232948521321 10638883966231674711390991)
            ·
              refine ⟨15958325949347512067086487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10638883966231674711390991 15958325949347512067086487)
              ·
                refine ⟨23937488924021268100629731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15958325949347512067086487 23937488924021268100629731)
                ·
                  refine ⟨35906233386031902150944597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23937488924021268100629731 35906233386031902150944597)
                  ·
                    refine ⟨210388086246280676665691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 35906233386031902150944597 210388086246280676665691)
                    ·
                      rfl

theorem cell23_1229188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 1, 1, 9].length) (baseStart_1229188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1229188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1229188 prefixEnd_1229188 := by exact prefixLift 1229188
  have htrace : WordTrace (prefixWord ++ tailWord_1229188) baseStart_1229188 baseEnd_1229188 := by
    simpa [prefixWord, tailWord_1229188, baseEnd_1229188] using wordTrace_append hprefix tailTrace_1229188
  have hstable : (prefixWord ++ tailWord_1229188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1229188).length < 2 ^ (prefixWord ++ tailWord_1229188).sum := by decide
  have hdescent : baseEnd_1229188 < baseStart_1229188 := by decide
  rcases family_descends (prefixWord ++ tailWord_1229188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1229228 : List Nat := [2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 5]
def baseStart_1229228 : Nat := 118140960795 + 1229228 * 2 ^ 59
def prefixEnd_1229228 : Nat := 4983230072969 + 3 ^ 40 * 1229228 * 2
def baseEnd_1229228 : Nat := 631184797965021873496889

theorem tailTrace_1229228 : CollatzResearch.WordTrace tailWord_1229228 prefixEnd_1229228 631184797965021873496889 := by
  unfold tailWord_1229228
  simp only [CollatzResearch.WordTrace]
  refine ⟨22416814195362183136848169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29889085593816244182464225 22416814195362183136848169)
  ·
    refine ⟨16812610646521637352636127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22416814195362183136848169 16812610646521637352636127)
    ·
      refine ⟨25218915969782456028954191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16812610646521637352636127 25218915969782456028954191)
      ·
        refine ⟨37828373954673684043431287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25218915969782456028954191 37828373954673684043431287)
        ·
          refine ⟨56742560932010526065146931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37828373954673684043431287 56742560932010526065146931)
          ·
            refine ⟨85113841398015789097720397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56742560932010526065146931 85113841398015789097720397)
            ·
              refine ⟨31917690524255920911645149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85113841398015789097720397 31917690524255920911645149)
              ·
                refine ⟨11969133946595970341866931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31917690524255920911645149 11969133946595970341866931)
                ·
                  refine ⟨17953700919893955512800397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11969133946595970341866931 17953700919893955512800397)
                  ·
                    refine ⟨6732637844960233317300149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17953700919893955512800397 6732637844960233317300149)
                    ·
                      refine ⟨631184797965021873496889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6732637844960233317300149 631184797965021873496889)
                      ·
                        rfl

theorem cell23_1229228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 5].length) (baseStart_1229228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1229228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1229228 prefixEnd_1229228 := by exact prefixLift 1229228
  have htrace : WordTrace (prefixWord ++ tailWord_1229228) baseStart_1229228 baseEnd_1229228 := by
    simpa [prefixWord, tailWord_1229228, baseEnd_1229228] using wordTrace_append hprefix tailTrace_1229228
  have hstable : (prefixWord ++ tailWord_1229228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1229228).length < 2 ^ (prefixWord ++ tailWord_1229228).sum := by decide
  have hdescent : baseEnd_1229228 < baseStart_1229228 := by decide
  rcases family_descends (prefixWord ++ tailWord_1229228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1229255 : List Nat := [1, 1, 4, 1, 1, 4, 2, 1, 2, 2, 4]
def baseStart_1229255 : Nat := 118140960795 + 1229255 * 2 ^ 59
def prefixEnd_1229255 : Nat := 4983230072969 + 3 ^ 40 * 1229255 * 2
def baseEnd_1229255 : Nat := 631198661942693267859265

theorem tailTrace_1229255 : CollatzResearch.WordTrace tailWord_1229255 prefixEnd_1229255 631198661942693267859265 := by
  unfold tailWord_1229255
  simp only [CollatzResearch.WordTrace]
  refine ⟨44834613161626549884929219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29889742107751033256619479 44834613161626549884929219)
  ·
    refine ⟨67251919742439824827393829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44834613161626549884929219 67251919742439824827393829)
    ·
      refine ⟨12609734951707467155136343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 67251919742439824827393829 12609734951707467155136343)
      ·
        refine ⟨18914602427561200732704515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12609734951707467155136343 18914602427561200732704515)
        ·
          refine ⟨28371903641341801099056773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18914602427561200732704515 28371903641341801099056773)
          ·
            refine ⟨5319731932751587706073145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28371903641341801099056773 5319731932751587706073145)
            ·
              refine ⟨3989798949563690779554859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5319731932751587706073145 3989798949563690779554859)
              ·
                refine ⟨5984698424345536169332289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3989798949563690779554859 5984698424345536169332289)
                ·
                  refine ⟨4488523818259152126999217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5984698424345536169332289 4488523818259152126999217)
                  ·
                    refine ⟨3366392863694364095249413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4488523818259152126999217 3366392863694364095249413)
                    ·
                      refine ⟨631198661942693267859265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3366392863694364095249413 631198661942693267859265)
                      ·
                        rfl

theorem cell23_1229255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 1, 2, 2, 4].length) (baseStart_1229255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1229255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1229255 prefixEnd_1229255 := by exact prefixLift 1229255
  have htrace : WordTrace (prefixWord ++ tailWord_1229255) baseStart_1229255 baseEnd_1229255 := by
    simpa [prefixWord, tailWord_1229255, baseEnd_1229255] using wordTrace_append hprefix tailTrace_1229255
  have hstable : (prefixWord ++ tailWord_1229255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1229255).length < 2 ^ (prefixWord ++ tailWord_1229255).sum := by decide
  have hdescent : baseEnd_1229255 < baseStart_1229255 := by decide
  rcases family_descends (prefixWord ++ tailWord_1229255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1229315 : List Nat := [1, 1, 1, 3, 2, 1, 3, 2, 4, 1, 4]
def baseStart_1229315 : Nat := 118140960795 + 1229315 * 2 ^ 59
def prefixEnd_1229315 : Nat := 4983230072969 + 3 ^ 40 * 1229315 * 2
def baseEnd_1229315 : Nat := 631229470781963033108989

theorem tailTrace_1229315 : CollatzResearch.WordTrace tailWord_1229315 prefixEnd_1229315 631229470781963033108989 := by
  unfold tailWord_1229315
  simp only [CollatzResearch.WordTrace]
  refine ⟨44836801541409180132113399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29891201027606120088075599 44836801541409180132113399)
  ·
    refine ⟨67255202312113770198170099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44836801541409180132113399 67255202312113770198170099)
    ·
      refine ⟨100882803468170655297255149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67255202312113770198170099 100882803468170655297255149)
      ·
        refine ⟨37831051300563995736470681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100882803468170655297255149 37831051300563995736470681)
        ·
          refine ⟨28373288475422996802353011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37831051300563995736470681 28373288475422996802353011)
          ·
            refine ⟨42559932713134495203529517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28373288475422996802353011 42559932713134495203529517)
            ·
              refine ⟨15959974767425435701323569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42559932713134495203529517 15959974767425435701323569)
              ·
                refine ⟨11969981075569076775992677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15959974767425435701323569 11969981075569076775992677)
                ·
                  refine ⟨2244371451669201895498627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11969981075569076775992677 2244371451669201895498627)
                  ·
                    refine ⟨3366557177503802843247941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2244371451669201895498627 3366557177503802843247941)
                    ·
                      refine ⟨631229470781963033108989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3366557177503802843247941 631229470781963033108989)
                      ·
                        rfl

theorem cell23_1229315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 2, 4, 1, 4].length) (baseStart_1229315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1229315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1229315 prefixEnd_1229315 := by exact prefixLift 1229315
  have htrace : WordTrace (prefixWord ++ tailWord_1229315) baseStart_1229315 baseEnd_1229315 := by
    simpa [prefixWord, tailWord_1229315, baseEnd_1229315] using wordTrace_append hprefix tailTrace_1229315
  have hstable : (prefixWord ++ tailWord_1229315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1229315).length < 2 ^ (prefixWord ++ tailWord_1229315).sum := by decide
  have hdescent : baseEnd_1229315 < baseStart_1229315 := by decide
  rcases family_descends (prefixWord ++ tailWord_1229315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1229345 : List Nat := [1, 2, 3, 2, 2, 1, 2, 1, 2, 1, 6]
def baseStart_1229345 : Nat := 118140960795 + 1229345 * 2 ^ 59
def prefixEnd_1229345 : Nat := 4983230072969 + 3 ^ 40 * 1229345 * 2
def baseEnd_1229345 : Nat := 631244875201597915733851

theorem tailTrace_1229345 : CollatzResearch.WordTrace tailWord_1229345 prefixEnd_1229345 631244875201597915733851 := by
  unfold tailWord_1229345
  simp only [CollatzResearch.WordTrace]
  refine ⟨44837895731300495255705489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29891930487533663503803659 44837895731300495255705489)
  ·
    refine ⟨33628421798475371441779117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44837895731300495255705489 33628421798475371441779117)
    ·
      refine ⟨12610658174428264290667169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33628421798475371441779117 12610658174428264290667169)
      ·
        refine ⟨9457993630821198218000377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12610658174428264290667169 9457993630821198218000377)
        ·
          refine ⟨7093495223115898663500283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9457993630821198218000377 7093495223115898663500283)
          ·
            refine ⟨10640242834673847995250425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7093495223115898663500283 10640242834673847995250425)
            ·
              refine ⟨7980182126005385996437819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10640242834673847995250425 7980182126005385996437819)
              ·
                refine ⟨11970273189008078994656729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7980182126005385996437819 11970273189008078994656729)
                ·
                  refine ⟨8977704891756059245992547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11970273189008078994656729 8977704891756059245992547)
                  ·
                    refine ⟨13466557337634088868988821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8977704891756059245992547 13466557337634088868988821)
                    ·
                      refine ⟨631244875201597915733851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13466557337634088868988821 631244875201597915733851)
                      ·
                        rfl

theorem cell23_1229345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 1, 2, 1, 6].length) (baseStart_1229345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1229345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1229345 prefixEnd_1229345 := by exact prefixLift 1229345
  have htrace : WordTrace (prefixWord ++ tailWord_1229345) baseStart_1229345 baseEnd_1229345 := by
    simpa [prefixWord, tailWord_1229345, baseEnd_1229345] using wordTrace_append hprefix tailTrace_1229345
  have hstable : (prefixWord ++ tailWord_1229345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1229345).length < 2 ^ (prefixWord ++ tailWord_1229345).sum := by decide
  have hdescent : baseEnd_1229345 < baseStart_1229345 := by decide
  rcases family_descends (prefixWord ++ tailWord_1229345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1229366 : List Nat := [5, 1, 2, 1, 2, 2, 1, 1, 2, 4, 2]
def baseStart_1229366 : Nat := 118140960795 + 1229366 * 2 ^ 59
def prefixEnd_1229366 : Nat := 4983230072969 + 3 ^ 40 * 1229366 * 2
def baseEnd_1229366 : Nat := 631255658295342333571255

theorem tailTrace_1229366 : CollatzResearch.WordTrace tailWord_1229366 prefixEnd_1229366 631255658295342333571255 := by
  unfold tailWord_1229366
  simp only [CollatzResearch.WordTrace]
  refine ⟨2802416354014025990138747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 29892441109482943894813301 2802416354014025990138747)
  ·
    refine ⟨4203624531021038985208121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2802416354014025990138747 4203624531021038985208121)
    ·
      refine ⟨3152718398265779238906091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4203624531021038985208121 3152718398265779238906091)
      ·
        refine ⟨4729077597398668858359137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3152718398265779238906091 4729077597398668858359137)
        ·
          refine ⟨3546808198049001643769353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4729077597398668858359137 3546808198049001643769353)
          ·
            refine ⟨2660106148536751232827015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3546808198049001643769353 2660106148536751232827015)
            ·
              refine ⟨3990159222805126849240523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2660106148536751232827015 3990159222805126849240523)
              ·
                refine ⟨5985238834207690273860785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3990159222805126849240523 5985238834207690273860785)
                ·
                  refine ⟨4488929125655767705395589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5985238834207690273860785 4488929125655767705395589)
                  ·
                    refine ⟨841674211060456444761673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4488929125655767705395589 841674211060456444761673)
                    ·
                      refine ⟨631255658295342333571255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 841674211060456444761673 631255658295342333571255)
                      ·
                        rfl

theorem cell23_1229366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 1, 2, 4, 2].length) (baseStart_1229366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1229366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1229366 prefixEnd_1229366 := by exact prefixLift 1229366
  have htrace : WordTrace (prefixWord ++ tailWord_1229366) baseStart_1229366 baseEnd_1229366 := by
    simpa [prefixWord, tailWord_1229366, baseEnd_1229366] using wordTrace_append hprefix tailTrace_1229366
  have hstable : (prefixWord ++ tailWord_1229366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1229366).length < 2 ^ (prefixWord ++ tailWord_1229366).sum := by decide
  have hdescent : baseEnd_1229366 < baseStart_1229366 := by decide
  rcases family_descends (prefixWord ++ tailWord_1229366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1229372 : List Nat := [2, 2, 2, 2, 3, 1, 2, 3, 6]
def baseStart_1229372 : Nat := 118140960795 + 1229372 * 2 ^ 59
def prefixEnd_1229372 : Nat := 4983230072969 + 3 ^ 40 * 1229372 * 2
def baseEnd_1229372 : Nat := 70139859908807701121803

theorem tailTrace_1229372 : CollatzResearch.WordTrace tailWord_1229372 prefixEnd_1229372 70139859908807701121803 := by
  unfold tailWord_1229372
  simp only [CollatzResearch.WordTrace]
  refine ⟨22419440251101339433469185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29892587001468452577958913 22419440251101339433469185)
  ·
    refine ⟨16814580188326004575101889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22419440251101339433469185 16814580188326004575101889)
    ·
      refine ⟨12610935141244503431326417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16814580188326004575101889 12610935141244503431326417)
      ·
        refine ⟨9458201355933377573494813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12610935141244503431326417 9458201355933377573494813)
        ·
          refine ⟨3546825508475016590060555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9458201355933377573494813 3546825508475016590060555)
          ·
            refine ⟨5320238262712524885090833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3546825508475016590060555 5320238262712524885090833)
            ·
              refine ⟨3990178697034393663818125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5320238262712524885090833 3990178697034393663818125)
              ·
                refine ⟨1496317011387897623931797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3990178697034393663818125 1496317011387897623931797)
                ·
                  refine ⟨70139859908807701121803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1496317011387897623931797 70139859908807701121803)
                  ·
                    rfl

theorem cell23_1229372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 3, 6].length) (baseStart_1229372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1229372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1229372 prefixEnd_1229372 := by exact prefixLift 1229372
  have htrace : WordTrace (prefixWord ++ tailWord_1229372) baseStart_1229372 baseEnd_1229372 := by
    simpa [prefixWord, tailWord_1229372, baseEnd_1229372] using wordTrace_append hprefix tailTrace_1229372
  have hstable : (prefixWord ++ tailWord_1229372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1229372).length < 2 ^ (prefixWord ++ tailWord_1229372).sum := by decide
  have hdescent : baseEnd_1229372 < baseStart_1229372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1229372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1229380 : List Nat := [2, 3, 5, 1, 2, 1, 1, 1, 2, 5]
def baseStart_1229380 : Nat := 118140960795 + 1229380 * 2 ^ 59
def prefixEnd_1229380 : Nat := 4983230072969 + 3 ^ 40 * 1229380 * 2
def baseEnd_1229380 : Nat := 210420949008168426265397

theorem tailTrace_1229380 : CollatzResearch.WordTrace tailWord_1229380 prefixEnd_1229380 210420949008168426265397 := by
  unfold tailWord_1229380
  simp only [CollatzResearch.WordTrace]
  refine ⟨22419586143086848116614797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29892781524115797488819729 22419586143086848116614797)
  ·
    refine ⟨8407344803657568043730549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22419586143086848116614797 8407344803657568043730549)
    ·
      refine ⟨788188575342897004099739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8407344803657568043730549 788188575342897004099739)
      ·
        refine ⟨1182282863014345506149609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 788188575342897004099739 1182282863014345506149609)
        ·
          refine ⟨886712147260759129612207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1182282863014345506149609 886712147260759129612207)
          ·
            refine ⟨1330068220891138694418311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 886712147260759129612207 1330068220891138694418311)
            ·
              refine ⟨1995102331336708041627467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1330068220891138694418311 1995102331336708041627467)
              ·
                refine ⟨2992653497005062062441201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1995102331336708041627467 2992653497005062062441201)
                ·
                  refine ⟨2244490122753796546830901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2992653497005062062441201 2244490122753796546830901)
                  ·
                    refine ⟨210420949008168426265397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2244490122753796546830901 210420949008168426265397)
                    ·
                      rfl

theorem cell23_1229380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_1229380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1229380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1229380 prefixEnd_1229380 := by exact prefixLift 1229380
  have htrace : WordTrace (prefixWord ++ tailWord_1229380) baseStart_1229380 baseEnd_1229380 := by
    simpa [prefixWord, tailWord_1229380, baseEnd_1229380] using wordTrace_append hprefix tailTrace_1229380
  have hstable : (prefixWord ++ tailWord_1229380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1229380).length < 2 ^ (prefixWord ++ tailWord_1229380).sum := by decide
  have hdescent : baseEnd_1229380 < baseStart_1229380 := by decide
  rcases family_descends (prefixWord ++ tailWord_1229380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1229439 : List Nat := [1, 1, 2, 2, 1, 1, 1, 5, 5, 2, 2]
def baseStart_1229439 : Nat := 118140960795 + 1229439 * 2 ^ 59
def prefixEnd_1229439 : Nat := 4983230072969 + 3 ^ 40 * 1229439 * 2
def baseEnd_1229439 : Nat := 631293142383120547958419

theorem tailTrace_1229439 : CollatzResearch.WordTrace tailWord_1229439 prefixEnd_1229439 631293142383120547958419 := by
  unfold tailWord_1229439
  simp only [CollatzResearch.WordTrace]
  refine ⟨44841324192959949309627371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29894216128639966206418247 44841324192959949309627371)
  ·
    refine ⟨67261986289439923964441057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44841324192959949309627371 67261986289439923964441057)
    ·
      refine ⟨50446489717079942973330793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67261986289439923964441057 50446489717079942973330793)
      ·
        refine ⟨37834867287809957229998095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50446489717079942973330793 37834867287809957229998095)
        ·
          refine ⟨56752300931714935844997143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37834867287809957229998095 56752300931714935844997143)
          ·
            refine ⟨85128451397572403767495715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56752300931714935844997143 85128451397572403767495715)
            ·
              refine ⟨127692677096358605651243573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85128451397572403767495715 127692677096358605651243573)
              ·
                refine ⟨11971188477783619279804085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 127692677096358605651243573 11971188477783619279804085)
                ·
                  refine ⟨1122298919792214307481633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11971188477783619279804085 1122298919792214307481633)
                  ·
                    refine ⟨841724189844160730611225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1122298919792214307481633 841724189844160730611225)
                    ·
                      refine ⟨631293142383120547958419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 841724189844160730611225 631293142383120547958419)
                      ·
                        rfl

theorem cell23_1229439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 5, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 5, 5, 2, 2].length) (baseStart_1229439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1229439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1229439 prefixEnd_1229439 := by exact prefixLift 1229439
  have htrace : WordTrace (prefixWord ++ tailWord_1229439) baseStart_1229439 baseEnd_1229439 := by
    simpa [prefixWord, tailWord_1229439, baseEnd_1229439] using wordTrace_append hprefix tailTrace_1229439
  have hstable : (prefixWord ++ tailWord_1229439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1229439).length < 2 ^ (prefixWord ++ tailWord_1229439).sum := by decide
  have hdescent : baseEnd_1229439 < baseStart_1229439 := by decide
  rcases family_descends (prefixWord ++ tailWord_1229439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1229450 : List Nat := [3, 1, 2, 3, 3, 2, 1, 3, 1, 1, 3]
def baseStart_1229450 : Nat := 118140960795 + 1229450 * 2 ^ 59
def prefixEnd_1229450 : Nat := 4983230072969 + 3 ^ 40 * 1229450 * 2
def baseEnd_1229450 : Nat := 631298790670320004920869

theorem tailTrace_1229450 : CollatzResearch.WordTrace tailWord_1229450 prefixEnd_1229450 631298790670320004920869 := by
  unfold tailWord_1229450
  simp only [CollatzResearch.WordTrace]
  refine ⟨11210431348980024547069451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29894483597280065458851869 11210431348980024547069451)
  ·
    refine ⟨16815647023470036820604177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11210431348980024547069451 16815647023470036820604177)
    ·
      refine ⟨12611735267602527615453133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16815647023470036820604177 12611735267602527615453133)
      ·
        refine ⟨4729400725350947855794925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12611735267602527615453133 4729400725350947855794925)
        ·
          refine ⟨1773525272006605445923097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4729400725350947855794925 1773525272006605445923097)
          ·
            refine ⟨1330143954004954084442323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1773525272006605445923097 1330143954004954084442323)
            ·
              refine ⟨1995215931007431126663485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1330143954004954084442323 1995215931007431126663485)
              ·
                refine ⟨748205974127786672498807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1995215931007431126663485 748205974127786672498807)
                ·
                  refine ⟨1122308961191680008748211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 748205974127786672498807 1122308961191680008748211)
                  ·
                    refine ⟨1683463441787520013122317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1122308961191680008748211 1683463441787520013122317)
                    ·
                      refine ⟨631298790670320004920869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1683463441787520013122317 631298790670320004920869)
                      ·
                        rfl

theorem cell23_1229450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 1, 3, 1, 1, 3].length) (baseStart_1229450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1229450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1229450 prefixEnd_1229450 := by exact prefixLift 1229450
  have htrace : WordTrace (prefixWord ++ tailWord_1229450) baseStart_1229450 baseEnd_1229450 := by
    simpa [prefixWord, tailWord_1229450, baseEnd_1229450] using wordTrace_append hprefix tailTrace_1229450
  have hstable : (prefixWord ++ tailWord_1229450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1229450).length < 2 ^ (prefixWord ++ tailWord_1229450).sum := by decide
  have hdescent : baseEnd_1229450 < baseStart_1229450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1229450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1229493 : List Nat := [1, 3, 3, 3, 1, 3, 1, 2, 1, 2, 3]
def baseStart_1229493 : Nat := 118140960795 + 1229493 * 2 ^ 59
def prefixEnd_1229493 : Nat := 4983230072969 + 3 ^ 40 * 1229493 * 2
def baseEnd_1229493 : Nat := 631320870338463336683171

theorem tailTrace_1229493 : CollatzResearch.WordTrace tailWord_1229493 prefixEnd_1229493 631320870338463336683171 := by
  unfold tailWord_1229493
  simp only [CollatzResearch.WordTrace]
  refine ⟨44843293734764316532093133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29895529156509544354728755 44843293734764316532093133)
  ·
    refine ⟨16816235150536618699534925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44843293734764316532093133 16816235150536618699534925)
    ·
      refine ⟨6306088181451232012325597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16816235150536618699534925 6306088181451232012325597)
      ·
        refine ⟨2364783068044212004622099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6306088181451232012325597 2364783068044212004622099)
        ·
          refine ⟨3547174602066318006933149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2364783068044212004622099 3547174602066318006933149)
          ·
            refine ⟨1330190475774869252599931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3547174602066318006933149 1330190475774869252599931)
            ·
              refine ⟨1995285713662303878899897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1330190475774869252599931 1995285713662303878899897)
              ·
                refine ⟨1496464285246727909174923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1995285713662303878899897 1496464285246727909174923)
                ·
                  refine ⟨2244696427870091863762385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1496464285246727909174923 2244696427870091863762385)
                  ·
                    refine ⟨1683522320902568897821789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2244696427870091863762385 1683522320902568897821789)
                    ·
                      refine ⟨631320870338463336683171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1683522320902568897821789 631320870338463336683171)
                      ·
                        rfl

theorem cell23_1229493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_1229493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1229493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1229493 prefixEnd_1229493 := by exact prefixLift 1229493
  have htrace : WordTrace (prefixWord ++ tailWord_1229493) baseStart_1229493 baseEnd_1229493 := by
    simpa [prefixWord, tailWord_1229493, baseEnd_1229493] using wordTrace_append hprefix tailTrace_1229493
  have hstable : (prefixWord ++ tailWord_1229493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1229493).length < 2 ^ (prefixWord ++ tailWord_1229493).sum := by decide
  have hdescent : baseEnd_1229493 < baseStart_1229493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1229493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1229510 : List Nat := [6, 1, 2, 1, 2, 2, 1, 1, 1, 1, 5]
def baseStart_1229510 : Nat := 118140960795 + 1229510 * 2 ^ 59
def prefixEnd_1229510 : Nat := 4983230072969 + 3 ^ 40 * 1229510 * 2
def baseEnd_1229510 : Nat := 631329599509589770170593

theorem tailTrace_1229510 : CollatzResearch.WordTrace tailWord_1229510 prefixEnd_1229510 631329599509589770170593 := by
  unfold tailWord_1229510
  simp only [CollatzResearch.WordTrace]
  refine ⟨1401372305490710263608187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 29895942517135152290307989 1401372305490710263608187)
  ·
    refine ⟨2102058458236065395412281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1401372305490710263608187 2102058458236065395412281)
    ·
      refine ⟨1576543843677049046559211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2102058458236065395412281 1576543843677049046559211)
      ·
        refine ⟨2364815765515573569838817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1576543843677049046559211 2364815765515573569838817)
        ·
          refine ⟨1773611824136680177379113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2364815765515573569838817 1773611824136680177379113)
          ·
            refine ⟨1330208868102510133034335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1773611824136680177379113 1330208868102510133034335)
            ·
              refine ⟨1995313302153765199551503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1330208868102510133034335 1995313302153765199551503)
              ·
                refine ⟨2992969953230647799327255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1995313302153765199551503 2992969953230647799327255)
                ·
                  refine ⟨4489454929845971698990883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2992969953230647799327255 4489454929845971698990883)
                  ·
                    refine ⟨6734182394768957548486325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4489454929845971698990883 6734182394768957548486325)
                    ·
                      refine ⟨631329599509589770170593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6734182394768957548486325 631329599509589770170593)
                      ·
                        rfl

theorem cell23_1229510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_1229510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1229510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1229510 prefixEnd_1229510 := by exact prefixLift 1229510
  have htrace : WordTrace (prefixWord ++ tailWord_1229510) baseStart_1229510 baseEnd_1229510 := by
    simpa [prefixWord, tailWord_1229510, baseEnd_1229510] using wordTrace_append hprefix tailTrace_1229510
  have hstable : (prefixWord ++ tailWord_1229510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1229510).length < 2 ^ (prefixWord ++ tailWord_1229510).sum := by decide
  have hdescent : baseEnd_1229510 < baseStart_1229510 := by decide
  rcases family_descends (prefixWord ++ tailWord_1229510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1229524 : List Nat := [2, 4, 1, 3, 2, 2, 2, 2, 1, 2, 2]
def baseStart_1229524 : Nat := 118140960795 + 1229524 * 2 ^ 59
def prefixEnd_1229524 : Nat := 4983230072969 + 3 ^ 40 * 1229524 * 2
def baseEnd_1229524 : Nat := 631336788238752715395529

theorem tailTrace_1229524 : CollatzResearch.WordTrace tailWord_1229524 prefixEnd_1229524 631336788238752715395529 := by
  unfold tailWord_1229524
  simp only [CollatzResearch.WordTrace]
  refine ⟨22422212198826004413235813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29896282931768005884314417 22422212198826004413235813)
  ·
    refine ⟨4204164787279875827481715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22422212198826004413235813 4204164787279875827481715)
    ·
      refine ⟨6306247180919813741222573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4204164787279875827481715 6306247180919813741222573)
      ·
        refine ⟨2364842692844930152958465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6306247180919813741222573 2364842692844930152958465)
        ·
          refine ⟨1773632019633697614718849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2364842692844930152958465 1773632019633697614718849)
          ·
            refine ⟨1330224014725273211039137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1773632019633697614718849 1330224014725273211039137)
            ·
              refine ⟨997668011043954908279353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1330224014725273211039137 997668011043954908279353)
              ·
                refine ⟨748251008282966181209515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 997668011043954908279353 748251008282966181209515)
                ·
                  refine ⟨1122376512424449271814273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 748251008282966181209515 1122376512424449271814273)
                  ·
                    refine ⟨841782384318336953860705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1122376512424449271814273 841782384318336953860705)
                    ·
                      refine ⟨631336788238752715395529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 841782384318336953860705 631336788238752715395529)
                      ·
                        rfl

theorem cell23_1229524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 2, 2, 1, 2, 2].length) (baseStart_1229524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1229524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1229524 prefixEnd_1229524 := by exact prefixLift 1229524
  have htrace : WordTrace (prefixWord ++ tailWord_1229524) baseStart_1229524 baseEnd_1229524 := by
    simpa [prefixWord, tailWord_1229524, baseEnd_1229524] using wordTrace_append hprefix tailTrace_1229524
  have hstable : (prefixWord ++ tailWord_1229524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1229524).length < 2 ^ (prefixWord ++ tailWord_1229524).sum := by decide
  have hdescent : baseEnd_1229524 < baseStart_1229524 := by decide
  rcases family_descends (prefixWord ++ tailWord_1229524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1229529 : List Nat := [1, 2, 1, 2, 3, 2, 1, 2, 3, 4, 2]
def baseStart_1229529 : Nat := 118140960795 + 1229529 * 2 ^ 59
def prefixEnd_1229529 : Nat := 4983230072969 + 3 ^ 40 * 1229529 * 2
def baseEnd_1229529 : Nat := 631339355642025195833005

theorem tailTrace_1229529 : CollatzResearch.WordTrace tailWord_1229529 prefixEnd_1229529 631339355642025195833005 := by
  unfold tailWord_1229529
  simp only [CollatzResearch.WordTrace]
  refine ⟨44844606762633894680403641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29896404508422596453602427 44844606762633894680403641)
  ·
    refine ⟨33633455071975421010302731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44844606762633894680403641 33633455071975421010302731)
    ·
      refine ⟨50450182607963131515454097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33633455071975421010302731 50450182607963131515454097)
      ·
        refine ⟨37837636955972348636590573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50450182607963131515454097 37837636955972348636590573)
        ·
          refine ⟨14189113858489630738721465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37837636955972348636590573 14189113858489630738721465)
          ·
            refine ⟨10641835393867223054041099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14189113858489630738721465 10641835393867223054041099)
            ·
              refine ⟨15962753090800834581061649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10641835393867223054041099 15962753090800834581061649)
              ·
                refine ⟨11972064818100625935796237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15962753090800834581061649 11972064818100625935796237)
                ·
                  refine ⟨4489524306787734725923589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11972064818100625935796237 4489524306787734725923589)
                  ·
                    refine ⟨841785807522700261110673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4489524306787734725923589 841785807522700261110673)
                    ·
                      refine ⟨631339355642025195833005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 841785807522700261110673 631339355642025195833005)
                      ·
                        rfl

theorem cell23_1229529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 2, 3, 4, 2].length) (baseStart_1229529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1229529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1229529 prefixEnd_1229529 := by exact prefixLift 1229529
  have htrace : WordTrace (prefixWord ++ tailWord_1229529) baseStart_1229529 baseEnd_1229529 := by
    simpa [prefixWord, tailWord_1229529, baseEnd_1229529] using wordTrace_append hprefix tailTrace_1229529
  have hstable : (prefixWord ++ tailWord_1229529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1229529).length < 2 ^ (prefixWord ++ tailWord_1229529).sum := by decide
  have hdescent : baseEnd_1229529 < baseStart_1229529 := by decide
  rcases family_descends (prefixWord ++ tailWord_1229529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1229539 : List Nat := [1, 1, 1, 7, 1, 2, 1, 1, 2, 6]
def baseStart_1229539 : Nat := 118140960795 + 1229539 * 2 ^ 59
def prefixEnd_1229539 : Nat := 4983230072969 + 3 ^ 40 * 1229539 * 2
def baseEnd_1229539 : Nat := 210448163482856718902653

theorem tailTrace_1229539 : CollatzResearch.WordTrace tailWord_1229539 prefixEnd_1229539 210448163482856718902653 := by
  unfold tailWord_1229539
  simp only [CollatzResearch.WordTrace]
  refine ⟨44844971492597666388267671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29896647661731777592178447 44844971492597666388267671)
  ·
    refine ⟨67267457238896499582401507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44844971492597666388267671 67267457238896499582401507)
    ·
      refine ⟨100901185858344749373602261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67267457238896499582401507 100901185858344749373602261)
      ·
        refine ⟨2364871543554955063443803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 100901185858344749373602261 2364871543554955063443803)
        ·
          refine ⟨3547307315332432595165705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2364871543554955063443803 3547307315332432595165705)
          ·
            refine ⟨2660480486499324446374279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3547307315332432595165705 2660480486499324446374279)
            ·
              refine ⟨3990720729748986669561419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2660480486499324446374279 3990720729748986669561419)
              ·
                refine ⟨5986081094623480004342129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3990720729748986669561419 5986081094623480004342129)
                ·
                  refine ⟨4489560820967610003256597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5986081094623480004342129 4489560820967610003256597)
                  ·
                    refine ⟨210448163482856718902653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4489560820967610003256597 210448163482856718902653)
                    ·
                      rfl

theorem cell23_1229539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 1, 2, 6].length) (baseStart_1229539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1229539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1229539 prefixEnd_1229539 := by exact prefixLift 1229539
  have htrace : WordTrace (prefixWord ++ tailWord_1229539) baseStart_1229539 baseEnd_1229539 := by
    simpa [prefixWord, tailWord_1229539, baseEnd_1229539] using wordTrace_append hprefix tailTrace_1229539
  have hstable : (prefixWord ++ tailWord_1229539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1229539).length < 2 ^ (prefixWord ++ tailWord_1229539).sum := by decide
  have hdescent : baseEnd_1229539 < baseStart_1229539 := by decide
  rcases family_descends (prefixWord ++ tailWord_1229539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1229546 : List Nat := [3, 1, 3, 1, 1, 1, 1, 2, 6, 2, 2]
def baseStart_1229546 : Nat := 118140960795 + 1229546 * 2 ^ 59
def prefixEnd_1229546 : Nat := 4983230072969 + 3 ^ 40 * 1229546 * 2
def baseEnd_1229546 : Nat := 631348084813151629320427

theorem tailTrace_1229546 : CollatzResearch.WordTrace tailWord_1229546 prefixEnd_1229546 631348084813151629320427 := by
  unfold tailWord_1229546
  simp only [CollatzResearch.WordTrace]
  refine ⟨11211306700893076645943123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29896817869048204389181661 11211306700893076645943123)
  ·
    refine ⟨16816960051339614968914685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11211306700893076645943123 16816960051339614968914685)
    ·
      refine ⟨6306360019252355613343007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16816960051339614968914685 6306360019252355613343007)
      ·
        refine ⟨9459540028878533420014511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6306360019252355613343007 9459540028878533420014511)
        ·
          refine ⟨14189310043317800130021767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9459540028878533420014511 14189310043317800130021767)
          ·
            refine ⟨21283965064976700195032651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14189310043317800130021767 21283965064976700195032651)
            ·
              refine ⟨31925947597465050292548977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21283965064976700195032651 31925947597465050292548977)
              ·
                refine ⟨23944460698098787719411733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31925947597465050292548977 23944460698098787719411733)
                ·
                  refine ⟨1122396595223380674347425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 23944460698098787719411733 1122396595223380674347425)
                  ·
                    refine ⟨841797446417535505760569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1122396595223380674347425 841797446417535505760569)
                    ·
                      refine ⟨631348084813151629320427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 841797446417535505760569 631348084813151629320427)
                      ·
                        rfl

theorem cell23_1229546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 2, 6, 2, 2].length) (baseStart_1229546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1229546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1229546 prefixEnd_1229546 := by exact prefixLift 1229546
  have htrace : WordTrace (prefixWord ++ tailWord_1229546) baseStart_1229546 baseEnd_1229546 := by
    simpa [prefixWord, tailWord_1229546, baseEnd_1229546] using wordTrace_append hprefix tailTrace_1229546
  have hstable : (prefixWord ++ tailWord_1229546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1229546).length < 2 ^ (prefixWord ++ tailWord_1229546).sum := by decide
  have hdescent : baseEnd_1229546 < baseStart_1229546 := by decide
  rcases family_descends (prefixWord ++ tailWord_1229546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1229549 : List Nat := [1, 5, 1, 2, 1, 1, 1, 2, 2, 4, 3]
def baseStart_1229549 : Nat := 118140960795 + 1229549 * 2 ^ 59
def prefixEnd_1229549 : Nat := 4983230072969 + 3 ^ 40 * 1229549 * 2
def baseEnd_1229549 : Nat := 631349625255115117582913

theorem tailTrace_1229549 : CollatzResearch.WordTrace tailWord_1229549 prefixEnd_1229549 631349625255115117582913 := by
  unfold tailWord_1229549
  simp only [CollatzResearch.WordTrace]
  refine ⟨44845336222561438096131701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29896890815040958730754467 44845336222561438096131701)
  ·
    refine ⟨4204250270865134821512347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 44845336222561438096131701 4204250270865134821512347)
    ·
      refine ⟨6306375406297702232268521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4204250270865134821512347 6306375406297702232268521)
      ·
        refine ⟨4729781554723276674201391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6306375406297702232268521 4729781554723276674201391)
        ·
          refine ⟨7094672332084915011302087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4729781554723276674201391 7094672332084915011302087)
          ·
            refine ⟨10642008498127372516953131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7094672332084915011302087 10642008498127372516953131)
            ·
              refine ⟨15963012747191058775429697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10642008498127372516953131 15963012747191058775429697)
              ·
                refine ⟨11972259560393294081572273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15963012747191058775429697 11972259560393294081572273)
                ·
                  refine ⟨8979194670294970561179205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11972259560393294081572273 8979194670294970561179205)
                  ·
                    refine ⟨1683599000680306980221101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8979194670294970561179205 1683599000680306980221101)
                    ·
                      refine ⟨631349625255115117582913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1683599000680306980221101 631349625255115117582913)
                      ·
                        rfl

theorem cell23_1229549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 2, 2, 4, 3].length) (baseStart_1229549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1229549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1229549 prefixEnd_1229549 := by exact prefixLift 1229549
  have htrace : WordTrace (prefixWord ++ tailWord_1229549) baseStart_1229549 baseEnd_1229549 := by
    simpa [prefixWord, tailWord_1229549, baseEnd_1229549] using wordTrace_append hprefix tailTrace_1229549
  have hstable : (prefixWord ++ tailWord_1229549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1229549).length < 2 ^ (prefixWord ++ tailWord_1229549).sum := by decide
  have hdescent : baseEnd_1229549 < baseStart_1229549 := by decide
  rcases family_descends (prefixWord ++ tailWord_1229549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1229552 : List Nat := [2, 1, 1, 1, 3, 1, 5, 2, 7]
def baseStart_1229552 : Nat := 118140960795 + 1229552 * 2 ^ 59
def prefixEnd_1229552 : Nat := 4983230072969 + 3 ^ 40 * 1229552 * 2
def baseEnd_1229552 : Nat := 70150129521897622871711

theorem tailTrace_1229552 : CollatzResearch.WordTrace tailWord_1229552 prefixEnd_1229552 70150129521897622871711 := by
  unfold tailWord_1229552
  simp only [CollatzResearch.WordTrace]
  refine ⟨22422722820775284804245455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29896963761033713072327273 22422722820775284804245455)
  ·
    refine ⟨33634084231162927206368183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22422722820775284804245455 33634084231162927206368183)
    ·
      refine ⟨50451126346744390809552275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33634084231162927206368183 50451126346744390809552275)
      ·
        refine ⟨75676689520116586214328413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50451126346744390809552275 75676689520116586214328413)
        ·
          refine ⟨28378758570043719830373155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75676689520116586214328413 28378758570043719830373155)
          ·
            refine ⟨42568137855065579745559733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28378758570043719830373155 42568137855065579745559733)
            ·
              refine ⟨3990762923912398101146225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42568137855065579745559733 3990762923912398101146225)
              ·
                refine ⟨2993072192934298575859669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3990762923912398101146225 2993072192934298575859669)
                ·
                  refine ⟨70150129521897622871711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2993072192934298575859669 70150129521897622871711)
                  ·
                    rfl

theorem cell23_1229552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 2, 7].length) (baseStart_1229552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1229552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1229552 prefixEnd_1229552 := by exact prefixLift 1229552
  have htrace : WordTrace (prefixWord ++ tailWord_1229552) baseStart_1229552 baseEnd_1229552 := by
    simpa [prefixWord, tailWord_1229552, baseEnd_1229552] using wordTrace_append hprefix tailTrace_1229552
  have hstable : (prefixWord ++ tailWord_1229552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1229552).length < 2 ^ (prefixWord ++ tailWord_1229552).sum := by decide
  have hdescent : baseEnd_1229552 < baseStart_1229552 := by decide
  rcases family_descends (prefixWord ++ tailWord_1229552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1229592 : List Nat := [2, 1, 2, 3, 1, 1, 1, 3, 1, 1, 7]
def baseStart_1229592 : Nat := 118140960795 + 1229592 * 2 ^ 59
def prefixEnd_1229592 : Nat := 4983230072969 + 3 ^ 40 * 1229592 * 2
def baseEnd_1229592 : Nat := 631371704923258449345215

theorem tailTrace_1229592 : CollatzResearch.WordTrace tailWord_1229592 prefixEnd_1229592 631371704923258449345215 := by
  unfold tailWord_1229592
  simp only [CollatzResearch.WordTrace]
  refine ⟨22423452280702828219973515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29897936374270437626631353 22423452280702828219973515)
  ·
    refine ⟨33635178421054242329960273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22423452280702828219973515 33635178421054242329960273)
    ·
      refine ⟨25226383815790681747470205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33635178421054242329960273 25226383815790681747470205)
      ·
        refine ⟨9459893930921505655301327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25226383815790681747470205 9459893930921505655301327)
        ·
          refine ⟨14189840896382258482951991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9459893930921505655301327 14189840896382258482951991)
          ·
            refine ⟨21284761344573387724427987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14189840896382258482951991 21284761344573387724427987)
            ·
              refine ⟨31927142016860081586641981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21284761344573387724427987 31927142016860081586641981)
              ·
                refine ⟨11972678256322530594990743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31927142016860081586641981 11972678256322530594990743)
                ·
                  refine ⟨17959017384483795892486115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11972678256322530594990743 17959017384483795892486115)
                  ·
                    refine ⟨26938526076725693838729173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17959017384483795892486115 26938526076725693838729173)
                    ·
                      refine ⟨631371704923258449345215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 26938526076725693838729173 631371704923258449345215)
                      ·
                        rfl

theorem cell23_1229592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 3, 1, 1, 7].length) (baseStart_1229592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1229592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1229592 prefixEnd_1229592 := by exact prefixLift 1229592
  have htrace : WordTrace (prefixWord ++ tailWord_1229592) baseStart_1229592 baseEnd_1229592 := by
    simpa [prefixWord, tailWord_1229592, baseEnd_1229592] using wordTrace_append hprefix tailTrace_1229592
  have hstable : (prefixWord ++ tailWord_1229592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1229592).length < 2 ^ (prefixWord ++ tailWord_1229592).sum := by decide
  have hdescent : baseEnd_1229592 < baseStart_1229592 := by decide
  rcases family_descends (prefixWord ++ tailWord_1229592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1229597 : List Nat := [1, 4, 2, 4, 2, 1, 1, 1, 1, 4, 2]
def baseStart_1229597 : Nat := 118140960795 + 1229597 * 2 ^ 59
def prefixEnd_1229597 : Nat := 4983230072969 + 3 ^ 40 * 1229597 * 2
def baseEnd_1229597 : Nat := 631374272326530929782693

theorem tailTrace_1229597 : CollatzResearch.WordTrace tailWord_1229597 prefixEnd_1229597 631374272326530929782693 := by
  unfold tailWord_1229597
  simp only [CollatzResearch.WordTrace]
  refine ⟨44847086926387542293879045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29898057950925028195919363 44847086926387542293879045)
  ·
    refine ⟨8408828798697664180102321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44847086926387542293879045 8408828798697664180102321)
    ·
      refine ⟨6306621599023248135076741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8408828798697664180102321 6306621599023248135076741)
      ·
        refine ⟨1182491549816859025326889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6306621599023248135076741 1182491549816859025326889)
        ·
          refine ⟨886868662362644268995167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1182491549816859025326889 886868662362644268995167)
          ·
            refine ⟨1330302993543966403492751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 886868662362644268995167 1330302993543966403492751)
            ·
              refine ⟨1995454490315949605239127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1330302993543966403492751 1995454490315949605239127)
              ·
                refine ⟨2993181735473924407858691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1995454490315949605239127 2993181735473924407858691)
                ·
                  refine ⟨4489772603210886611788037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2993181735473924407858691 4489772603210886611788037)
                  ·
                    refine ⟨841832363102041239710257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4489772603210886611788037 841832363102041239710257)
                    ·
                      refine ⟨631374272326530929782693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 841832363102041239710257 631374272326530929782693)
                      ·
                        rfl

theorem cell23_1229597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_1229597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1229597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1229597 prefixEnd_1229597 := by exact prefixLift 1229597
  have htrace : WordTrace (prefixWord ++ tailWord_1229597) baseStart_1229597 baseEnd_1229597 := by
    simpa [prefixWord, tailWord_1229597, baseEnd_1229597] using wordTrace_append hprefix tailTrace_1229597
  have hstable : (prefixWord ++ tailWord_1229597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1229597).length < 2 ^ (prefixWord ++ tailWord_1229597).sum := by decide
  have hdescent : baseEnd_1229597 < baseStart_1229597 := by decide
  rcases family_descends (prefixWord ++ tailWord_1229597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1229612 : List Nat := [2, 2, 1, 1, 1, 4, 1, 1, 2, 8]
def baseStart_1229612 : Nat := 118140960795 + 1229612 * 2 ^ 59
def prefixEnd_1229612 : Nat := 4983230072969 + 3 ^ 40 * 1229612 * 2
def baseEnd_1229612 : Nat := 210460658178782790365041

theorem tailTrace_1229612 : CollatzResearch.WordTrace tailWord_1229612 prefixEnd_1229612 210460658178782790365041 := by
  unfold tailWord_1229612
  simp only [CollatzResearch.WordTrace]
  refine ⟨22423817010666599927837545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29898422680888799903783393 22423817010666599927837545)
  ·
    refine ⟨16817862757999949945878159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22423817010666599927837545 16817862757999949945878159)
    ·
      refine ⟨25226794136999924918817239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16817862757999949945878159 25226794136999924918817239)
      ·
        refine ⟨37840191205499887378225859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25226794136999924918817239 37840191205499887378225859)
        ·
          refine ⟨56760286808249831067338789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37840191205499887378225859 56760286808249831067338789)
          ·
            refine ⟨10642553776546843325126023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56760286808249831067338789 10642553776546843325126023)
            ·
              refine ⟨15963830664820264987689035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10642553776546843325126023 15963830664820264987689035)
              ·
                refine ⟨23945745997230397481533553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15963830664820264987689035 23945745997230397481533553)
                ·
                  refine ⟨17959309497922798111150165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23945745997230397481533553 17959309497922798111150165)
                  ·
                    refine ⟨210460658178782790365041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 17959309497922798111150165 210460658178782790365041)
                    ·
                      rfl

theorem cell23_1229612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 8].length) (baseStart_1229612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1229612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1229612 prefixEnd_1229612 := by exact prefixLift 1229612
  have htrace : WordTrace (prefixWord ++ tailWord_1229612) baseStart_1229612 baseEnd_1229612 := by
    simpa [prefixWord, tailWord_1229612, baseEnd_1229612] using wordTrace_append hprefix tailTrace_1229612
  have hstable : (prefixWord ++ tailWord_1229612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1229612).length < 2 ^ (prefixWord ++ tailWord_1229612).sum := by decide
  have hdescent : baseEnd_1229612 < baseStart_1229612 := by decide
  rcases family_descends (prefixWord ++ tailWord_1229612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1229619 : List Nat := [1, 1, 1, 2, 6, 1, 2, 1, 1, 3, 4]
def baseStart_1229619 : Nat := 118140960795 + 1229619 * 2 ^ 59
def prefixEnd_1229619 : Nat := 4983230072969 + 3 ^ 40 * 1229619 * 2
def baseEnd_1229619 : Nat := 631385568900929843707591

theorem tailTrace_1229619 : CollatzResearch.WordTrace tailWord_1229619 prefixEnd_1229619 631385568900929843707591 := by
  unfold tailWord_1229619
  simp only [CollatzResearch.WordTrace]
  refine ⟨44847889332307840051179911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29898592888205226700786607 44847889332307840051179911)
  ·
    refine ⟨67271833998461760076769867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44847889332307840051179911 67271833998461760076769867)
    ·
      refine ⟨100907750997692640115154801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67271833998461760076769867 100907750997692640115154801)
      ·
        refine ⟨75680813248269480086366101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100907750997692640115154801 75680813248269480086366101)
        ·
          refine ⟨3547538121012631879048411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 75680813248269480086366101 3547538121012631879048411)
          ·
            refine ⟨5321307181518947818572617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3547538121012631879048411 5321307181518947818572617)
            ·
              refine ⟨3990980386139210863929463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5321307181518947818572617 3990980386139210863929463)
              ·
                refine ⟨5986470579208816295894195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3990980386139210863929463 5986470579208816295894195)
                ·
                  refine ⟨8979705868813224443841293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5986470579208816295894195 8979705868813224443841293)
                  ·
                    refine ⟨3367389700804959166440485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8979705868813224443841293 3367389700804959166440485)
                    ·
                      refine ⟨631385568900929843707591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3367389700804959166440485 631385568900929843707591)
                      ·
                        rfl

theorem cell23_1229619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 1, 1, 3, 4].length) (baseStart_1229619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1229619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1229619 prefixEnd_1229619 := by exact prefixLift 1229619
  have htrace : WordTrace (prefixWord ++ tailWord_1229619) baseStart_1229619 baseEnd_1229619 := by
    simpa [prefixWord, tailWord_1229619, baseEnd_1229619] using wordTrace_append hprefix tailTrace_1229619
  have hstable : (prefixWord ++ tailWord_1229619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1229619).length < 2 ^ (prefixWord ++ tailWord_1229619).sum := by decide
  have hdescent : baseEnd_1229619 < baseStart_1229619 := by decide
  rcases family_descends (prefixWord ++ tailWord_1229619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1229620 : List Nat := [2, 5, 1, 1, 3, 2, 1, 3, 5]
def baseStart_1229620 : Nat := 118140960795 + 1229620 * 2 ^ 59
def prefixEnd_1229620 : Nat := 4983230072969 + 3 ^ 40 * 1229620 * 2
def baseEnd_1229620 : Nat := 70154009153509371088343

theorem tailTrace_1229620 : CollatzResearch.WordTrace tailWord_1229620 prefixEnd_1229620 70154009153509371088343 := by
  unfold tailWord_1229620
  simp only [CollatzResearch.WordTrace]
  refine ⟨22423962902652108610983157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29898617203536144814644209 22423962902652108610983157)
  ·
    refine ⟨2102246522123635182279671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22423962902652108610983157 2102246522123635182279671)
    ·
      refine ⟨3153369783185452773419507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2102246522123635182279671 3153369783185452773419507)
      ·
        refine ⟨4730054674778179160129261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3153369783185452773419507 4730054674778179160129261)
        ·
          refine ⟨1773770503041817185048473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4730054674778179160129261 1773770503041817185048473)
          ·
            refine ⟨1330327877281362888786355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1773770503041817185048473 1330327877281362888786355)
            ·
              refine ⟨1995491815922044333179533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1330327877281362888786355 1995491815922044333179533)
              ·
                refine ⟨748309430970766624942325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1995491815922044333179533 748309430970766624942325)
                ·
                  refine ⟨70154009153509371088343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 748309430970766624942325 70154009153509371088343)
                  ·
                    rfl

theorem cell23_1229620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 1, 3, 5].length) (baseStart_1229620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1229620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1229620 prefixEnd_1229620 := by exact prefixLift 1229620
  have htrace : WordTrace (prefixWord ++ tailWord_1229620) baseStart_1229620 baseEnd_1229620 := by
    simpa [prefixWord, tailWord_1229620, baseEnd_1229620] using wordTrace_append hprefix tailTrace_1229620
  have hstable : (prefixWord ++ tailWord_1229620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1229620).length < 2 ^ (prefixWord ++ tailWord_1229620).sum := by decide
  have hdescent : baseEnd_1229620 < baseStart_1229620 := by decide
  rcases family_descends (prefixWord ++ tailWord_1229620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1229632 : List Nat := [2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 6]
def baseStart_1229632 : Nat := 118140960795 + 1229632 * 2 ^ 59
def prefixEnd_1229632 : Nat := 4983230072969 + 3 ^ 40 * 1229632 * 2
def baseEnd_1229632 : Nat := 631392244149438292845031

theorem tailTrace_1229632 : CollatzResearch.WordTrace tailWord_1229632 prefixEnd_1229632 631392244149438292845031 := by
  unfold tailWord_1229632
  simp only [CollatzResearch.WordTrace]
  refine ⟨22424181740630371635701575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29898908987507162180935433 22424181740630371635701575)
  ·
    refine ⟨33636272610945557453552363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22424181740630371635701575 33636272610945557453552363)
    ·
      refine ⟨50454408916418336180328545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33636272610945557453552363 50454408916418336180328545)
      ·
        refine ⟨37840806687313752135246409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50454408916418336180328545 37840806687313752135246409)
        ·
          refine ⟨28380605015485314101434807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37840806687313752135246409 28380605015485314101434807)
          ·
            refine ⟨42570907523227971152152211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28380605015485314101434807 42570907523227971152152211)
            ·
              refine ⟨63856361284841956728228317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42570907523227971152152211 63856361284841956728228317)
              ·
                refine ⟨23946135481815733773085619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63856361284841956728228317 23946135481815733773085619)
                ·
                  refine ⟨35919203222723600659628429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23946135481815733773085619 35919203222723600659628429)
                  ·
                    refine ⟨13469701208521350247360661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35919203222723600659628429 13469701208521350247360661)
                    ·
                      refine ⟨631392244149438292845031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13469701208521350247360661 631392244149438292845031)
                      ·
                        rfl

theorem cell23_1229632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 6].length) (baseStart_1229632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1229632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1229632 prefixEnd_1229632 := by exact prefixLift 1229632
  have htrace : WordTrace (prefixWord ++ tailWord_1229632) baseStart_1229632 baseEnd_1229632 := by
    simpa [prefixWord, tailWord_1229632, baseEnd_1229632] using wordTrace_append hprefix tailTrace_1229632
  have hstable : (prefixWord ++ tailWord_1229632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1229632).length < 2 ^ (prefixWord ++ tailWord_1229632).sum := by decide
  have hdescent : baseEnd_1229632 < baseStart_1229632 := by decide
  rcases family_descends (prefixWord ++ tailWord_1229632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1229633 : List Nat := [1, 2, 5, 3, 1, 1, 1, 2, 2, 5]
def baseStart_1229633 : Nat := 118140960795 + 1229633 * 2 ^ 59
def prefixEnd_1229633 : Nat := 4983230072969 + 3 ^ 40 * 1229633 * 2
def baseEnd_1229633 : Nat := 210464252543364262977509

theorem tailTrace_1229633 : CollatzResearch.WordTrace tailWord_1229633 prefixEnd_1229633 210464252543364262977509 := by
  unfold tailWord_1229633
  simp only [CollatzResearch.WordTrace]
  refine ⟨44848399954257120442189553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29898933302838080294793035 44848399954257120442189553)
  ·
    refine ⟨33636299965692840331642165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44848399954257120442189553 33636299965692840331642165)
    ·
      refine ⟨3153403121783703781091453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 33636299965692840331642165 3153403121783703781091453)
      ·
        refine ⟨1182526170668888917909295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3153403121783703781091453 1182526170668888917909295)
        ·
          refine ⟨1773789256003333376863943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1182526170668888917909295 1773789256003333376863943)
          ·
            refine ⟨2660683884005000065295915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1773789256003333376863943 2660683884005000065295915)
            ·
              refine ⟨3991025826007500097943873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2660683884005000065295915 3991025826007500097943873)
              ·
                refine ⟨2993269369505625073457905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3991025826007500097943873 2993269369505625073457905)
                ·
                  refine ⟨2244952027129218805093429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2993269369505625073457905 2244952027129218805093429)
                  ·
                    refine ⟨210464252543364262977509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2244952027129218805093429 210464252543364262977509)
                    ·
                      rfl

theorem cell23_1229633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 2, 2, 5].length) (baseStart_1229633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1229633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1229633 prefixEnd_1229633 := by exact prefixLift 1229633
  have htrace : WordTrace (prefixWord ++ tailWord_1229633) baseStart_1229633 baseEnd_1229633 := by
    simpa [prefixWord, tailWord_1229633, baseEnd_1229633] using wordTrace_append hprefix tailTrace_1229633
  have hstable : (prefixWord ++ tailWord_1229633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1229633).length < 2 ^ (prefixWord ++ tailWord_1229633).sum := by decide
  have hdescent : baseEnd_1229633 < baseStart_1229633 := by decide
  rcases family_descends (prefixWord ++ tailWord_1229633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1229669 : List Nat := [1, 3, 1, 3, 1, 1, 2, 1, 2, 5, 3]
def baseStart_1229669 : Nat := 118140960795 + 1229669 * 2 ^ 59
def prefixEnd_1229669 : Nat := 4983230072969 + 3 ^ 40 * 1229669 * 2
def baseEnd_1229669 : Nat := 631411242933654648082361

theorem tailTrace_1229669 : CollatzResearch.WordTrace tailWord_1229669 prefixEnd_1229669 631411242933654648082361 := by
  unfold tailWord_1229669
  simp only [CollatzResearch.WordTrace]
  refine ⟨44849712982126698590500061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29899808654751132393666707 44849712982126698590500061)
  ·
    refine ⟨16818642368297511971437523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44849712982126698590500061 16818642368297511971437523)
    ·
      refine ⟨25227963552446267957156285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16818642368297511971437523 25227963552446267957156285)
      ·
        refine ⟨9460486332167350483933607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25227963552446267957156285 9460486332167350483933607)
        ·
          refine ⟨14190729498251025725900411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9460486332167350483933607 14190729498251025725900411)
          ·
            refine ⟨21286094247376538588850617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14190729498251025725900411 21286094247376538588850617)
            ·
              refine ⟨15964570685532403941637963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21286094247376538588850617 15964570685532403941637963)
              ·
                refine ⟨23946856028298605912456945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15964570685532403941637963 23946856028298605912456945)
                ·
                  refine ⟨17960142021223954434342709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23946856028298605912456945 17960142021223954434342709)
                  ·
                    refine ⟨1683763314489745728219629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17960142021223954434342709 1683763314489745728219629)
                    ·
                      refine ⟨631411242933654648082361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1683763314489745728219629 631411242933654648082361)
                      ·
                        rfl

theorem cell23_1229669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 1, 2, 5, 3].length) (baseStart_1229669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1229669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1229669 prefixEnd_1229669 := by exact prefixLift 1229669
  have htrace : WordTrace (prefixWord ++ tailWord_1229669) baseStart_1229669 baseEnd_1229669 := by
    simpa [prefixWord, tailWord_1229669, baseEnd_1229669] using wordTrace_append hprefix tailTrace_1229669
  have hstable : (prefixWord ++ tailWord_1229669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1229669).length < 2 ^ (prefixWord ++ tailWord_1229669).sum := by decide
  have hdescent : baseEnd_1229669 < baseStart_1229669 := by decide
  rcases family_descends (prefixWord ++ tailWord_1229669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1229696 : List Nat := [2, 1, 1, 2, 1, 2, 2, 3, 4, 3, 2]
def baseStart_1229696 : Nat := 118140960795 + 1229696 * 2 ^ 59
def prefixEnd_1229696 : Nat := 4983230072969 + 3 ^ 40 * 1229696 * 2
def baseEnd_1229696 : Nat := 631425106911326042444737

theorem tailTrace_1229696 : CollatzResearch.WordTrace tailWord_1229696 prefixEnd_1229696 631425106911326042444737 := by
  unfold tailWord_1229696
  simp only [CollatzResearch.WordTrace]
  refine ⟨22425348876514441100866471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29900465168685921467821961 22425348876514441100866471)
  ·
    refine ⟨33638023314771661651299707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22425348876514441100866471 33638023314771661651299707)
    ·
      refine ⟨50457034972157492476949561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33638023314771661651299707 50457034972157492476949561)
      ·
        refine ⟨37842776229118119357712171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50457034972157492476949561 37842776229118119357712171)
        ·
          refine ⟨56764164343677179036568257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37842776229118119357712171 56764164343677179036568257)
          ·
            refine ⟨42573123257757884277426193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56764164343677179036568257 42573123257757884277426193)
            ·
              refine ⟨31929842443318413208069645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42573123257757884277426193 31929842443318413208069645)
              ·
                refine ⟨11973690916244404953026117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31929842443318413208069645 11973690916244404953026117)
                ·
                  refine ⟨2245067046795825928692397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11973690916244404953026117 2245067046795825928692397)
                  ·
                    refine ⟨841900142548434723259649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2245067046795825928692397 841900142548434723259649)
                    ·
                      refine ⟨631425106911326042444737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 841900142548434723259649 631425106911326042444737)
                      ·
                        rfl

theorem cell23_1229696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 3, 4, 3, 2].length) (baseStart_1229696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1229696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1229696 prefixEnd_1229696 := by exact prefixLift 1229696
  have htrace : WordTrace (prefixWord ++ tailWord_1229696) baseStart_1229696 baseEnd_1229696 := by
    simpa [prefixWord, tailWord_1229696, baseEnd_1229696] using wordTrace_append hprefix tailTrace_1229696
  have hstable : (prefixWord ++ tailWord_1229696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1229696).length < 2 ^ (prefixWord ++ tailWord_1229696).sum := by decide
  have hdescent : baseEnd_1229696 < baseStart_1229696 := by decide
  rcases family_descends (prefixWord ++ tailWord_1229696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1229706 : List Nat := [3, 1, 2, 4, 1, 1, 1, 2, 3, 5]
def baseStart_1229706 : Nat := 118140960795 + 1229706 * 2 ^ 59
def prefixEnd_1229706 : Nat := 4983230072969 + 3 ^ 40 * 1229706 * 2
def baseEnd_1229706 : Nat := 210476747239290334439897

theorem tailTrace_1229706 : CollatzResearch.WordTrace tailWord_1229706 prefixEnd_1229706 210476747239290334439897 := by
  unfold tailWord_1229706
  simp only [CollatzResearch.WordTrace]
  refine ⟨11212765620748163477399243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29900708321995102606397981 11212765620748163477399243)
  ·
    refine ⟨16819148431122245216098865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11212765620748163477399243 16819148431122245216098865)
    ·
      refine ⟨12614361323341683912074149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16819148431122245216098865 12614361323341683912074149)
      ·
        refine ⟨2365192748126565733513903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12614361323341683912074149 2365192748126565733513903)
        ·
          refine ⟨3547789122189848600270855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2365192748126565733513903 3547789122189848600270855)
          ·
            refine ⟨5321683683284772900406283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3547789122189848600270855 5321683683284772900406283)
            ·
              refine ⟨7982525524927159350609425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5321683683284772900406283 7982525524927159350609425)
              ·
                refine ⟨5986894143695369512957069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7982525524927159350609425 5986894143695369512957069)
                ·
                  refine ⟨2245085303885763567358901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5986894143695369512957069 2245085303885763567358901)
                  ·
                    refine ⟨210476747239290334439897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2245085303885763567358901 210476747239290334439897)
                    ·
                      rfl

theorem cell23_1229706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 2, 3, 5].length) (baseStart_1229706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1229706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1229706 prefixEnd_1229706 := by exact prefixLift 1229706
  have htrace : WordTrace (prefixWord ++ tailWord_1229706) baseStart_1229706 baseEnd_1229706 := by
    simpa [prefixWord, tailWord_1229706, baseEnd_1229706] using wordTrace_append hprefix tailTrace_1229706
  have hstable : (prefixWord ++ tailWord_1229706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1229706).length < 2 ^ (prefixWord ++ tailWord_1229706).sum := by decide
  have hdescent : baseEnd_1229706 < baseStart_1229706 := by decide
  rcases family_descends (prefixWord ++ tailWord_1229706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1229730 : List Nat := [3, 3, 1, 2, 2, 1, 3, 1, 2, 3, 2]
def baseStart_1229730 : Nat := 118140960795 + 1229730 * 2 ^ 59
def prefixEnd_1229730 : Nat := 4983230072969 + 3 ^ 40 * 1229730 * 2
def baseEnd_1229730 : Nat := 631442565253578909419581

theorem tailTrace_1229730 : CollatzResearch.WordTrace tailWord_1229730 prefixEnd_1229730 631442565253578909419581 := by
  unfold tailWord_1229730
  simp only [CollatzResearch.WordTrace]
  refine ⟨11212984458726426502117661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29901291889937137338980429 11212984458726426502117661)
  ·
    refine ⟨4204869172022409938294123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11212984458726426502117661 4204869172022409938294123)
    ·
      refine ⟨6307303758033614907441185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4204869172022409938294123 6307303758033614907441185)
      ·
        refine ⟨4730477818525211180580889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6307303758033614907441185 4730477818525211180580889)
        ·
          refine ⟨3547858363893908385435667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4730477818525211180580889 3547858363893908385435667)
          ·
            refine ⟨5321787545840862578153501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3547858363893908385435667 5321787545840862578153501)
            ·
              refine ⟨1995670329690323466807563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5321787545840862578153501 1995670329690323466807563)
              ·
                refine ⟨2993505494535485200211345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1995670329690323466807563 2993505494535485200211345)
                ·
                  refine ⟨2245129120901613900158509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2993505494535485200211345 2245129120901613900158509)
                  ·
                    refine ⟨841923420338105212559441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2245129120901613900158509 841923420338105212559441)
                    ·
                      refine ⟨631442565253578909419581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 841923420338105212559441 631442565253578909419581)
                      ·
                        rfl

theorem cell23_1229730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 3, 1, 2, 3, 2].length) (baseStart_1229730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1229730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1229730 prefixEnd_1229730 := by exact prefixLift 1229730
  have htrace : WordTrace (prefixWord ++ tailWord_1229730) baseStart_1229730 baseEnd_1229730 := by
    simpa [prefixWord, tailWord_1229730, baseEnd_1229730] using wordTrace_append hprefix tailTrace_1229730
  have hstable : (prefixWord ++ tailWord_1229730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1229730).length < 2 ^ (prefixWord ++ tailWord_1229730).sum := by decide
  have hdescent : baseEnd_1229730 < baseStart_1229730 := by decide
  rcases family_descends (prefixWord ++ tailWord_1229730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1229749 : List Nat := [1, 3, 3, 2, 1, 1, 12]
def baseStart_1229749 : Nat := 118140960795 + 1229749 * 2 ^ 59
def prefixEnd_1229749 : Nat := 4983230072969 + 3 ^ 40 * 1229749 * 2
def baseEnd_1229749 : Nat := 7795707671432275741753

theorem tailTrace_1229749 : CollatzResearch.WordTrace tailWord_1229749 prefixEnd_1229749 7795707671432275741753 := by
  unfold tailWord_1229749
  simp only [CollatzResearch.WordTrace]
  refine ⟨44852630821836872253412301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29901753881224581502274867 44852630821836872253412301)
  ·
    refine ⟨16819736558188827095029613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44852630821836872253412301 16819736558188827095029613)
    ·
      refine ⟨6307401209320810160636105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16819736558188827095029613 6307401209320810160636105)
      ·
        refine ⟨4730550906990607620477079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6307401209320810160636105 4730550906990607620477079)
        ·
          refine ⟨7095826360485911430715619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4730550906990607620477079 7095826360485911430715619)
          ·
            refine ⟨10643739540728867146073429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7095826360485911430715619 10643739540728867146073429)
            ·
              refine ⟨7795707671432275741753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 10643739540728867146073429 7795707671432275741753)
              ·
                rfl

theorem cell23_1229749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 12].length) (baseStart_1229749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1229749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1229749 prefixEnd_1229749 := by exact prefixLift 1229749
  have htrace : WordTrace (prefixWord ++ tailWord_1229749) baseStart_1229749 baseEnd_1229749 := by
    simpa [prefixWord, tailWord_1229749, baseEnd_1229749] using wordTrace_append hprefix tailTrace_1229749
  have hstable : (prefixWord ++ tailWord_1229749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1229749).length < 2 ^ (prefixWord ++ tailWord_1229749).sum := by decide
  have hdescent : baseEnd_1229749 < baseStart_1229749 := by decide
  rcases family_descends (prefixWord ++ tailWord_1229749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1229753 : List Nat := [1, 2, 1, 4, 2, 2, 3, 2, 2, 4]
def baseStart_1229753 : Nat := 118140960795 + 1229753 * 2 ^ 59
def prefixEnd_1229753 : Nat := 4983230072969 + 3 ^ 40 * 1229753 * 2
def baseEnd_1229753 : Nat := 210484791769544106477325

theorem tailTrace_1229753 : CollatzResearch.WordTrace tailWord_1229753 prefixEnd_1229753 210484791769544106477325 := by
  unfold tailWord_1229753
  simp only [CollatzResearch.WordTrace]
  refine ⟨44852776713822380936557913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29901851142548253957705275 44852776713822380936557913)
  ·
    refine ⟨33639582535366785702418435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44852776713822380936557913 33639582535366785702418435)
    ·
      refine ⟨50459373803050178553627653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33639582535366785702418435 50459373803050178553627653)
      ·
        refine ⟨9461132588071908478805185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50459373803050178553627653 9461132588071908478805185)
        ·
          refine ⟨7095849441053931359103889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9461132588071908478805185 7095849441053931359103889)
          ·
            refine ⟨5321887080790448519327917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7095849441053931359103889 5321887080790448519327917)
            ·
              refine ⟨1995707655296418194747969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5321887080790448519327917 1995707655296418194747969)
              ·
                refine ⟨1496780741472313646060977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1995707655296418194747969 1496780741472313646060977)
                ·
                  refine ⟨1122585556104235234545733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1496780741472313646060977 1122585556104235234545733)
                  ·
                    refine ⟨210484791769544106477325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1122585556104235234545733 210484791769544106477325)
                    ·
                      rfl

theorem cell23_1229753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 3, 2, 2, 4].length) (baseStart_1229753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1229753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1229753 prefixEnd_1229753 := by exact prefixLift 1229753
  have htrace : WordTrace (prefixWord ++ tailWord_1229753) baseStart_1229753 baseEnd_1229753 := by
    simpa [prefixWord, tailWord_1229753, baseEnd_1229753] using wordTrace_append hprefix tailTrace_1229753
  have hstable : (prefixWord ++ tailWord_1229753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1229753).length < 2 ^ (prefixWord ++ tailWord_1229753).sum := by decide
  have hdescent : baseEnd_1229753 < baseStart_1229753 := by decide
  rcases family_descends (prefixWord ++ tailWord_1229753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1229760 : List Nat := [2, 1, 1, 2, 3, 4, 2, 1, 3, 2, 2]
def baseStart_1229760 : Nat := 118140960795 + 1229760 * 2 ^ 59
def prefixEnd_1229760 : Nat := 4983230072969 + 3 ^ 40 * 1229760 * 2
def baseEnd_1229760 : Nat := 631457969673213792044443

theorem tailTrace_1229760 : CollatzResearch.WordTrace tailWord_1229760 prefixEnd_1229760 631457969673213792044443 := by
  unfold tailWord_1229760
  simp only [CollatzResearch.WordTrace]
  refine ⟨22426516012398510566031367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29902021349864680754708489 22426516012398510566031367)
  ·
    refine ⟨33639774018597765849047051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22426516012398510566031367 33639774018597765849047051)
    ·
      refine ⟨50459661027896648773570577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33639774018597765849047051 50459661027896648773570577)
      ·
        refine ⟨37844745770922486580177933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50459661027896648773570577 37844745770922486580177933)
        ·
          refine ⟨14191779664095932467566725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37844745770922486580177933 14191779664095932467566725)
          ·
            refine ⟨2660958687017987337668761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14191779664095932467566725 2660958687017987337668761)
            ·
              refine ⟨1995719015263490503251571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2660958687017987337668761 1995719015263490503251571)
              ·
                refine ⟨2993578522895235754877357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1995719015263490503251571 2993578522895235754877357)
                ·
                  refine ⟨1122591946085713408079009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2993578522895235754877357 1122591946085713408079009)
                  ·
                    refine ⟨841943959564285056059257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1122591946085713408079009 841943959564285056059257)
                    ·
                      refine ⟨631457969673213792044443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 841943959564285056059257 631457969673213792044443)
                      ·
                        rfl

theorem cell23_1229760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 2, 1, 3, 2, 2].length) (baseStart_1229760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1229760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1229760 prefixEnd_1229760 := by exact prefixLift 1229760
  have htrace : WordTrace (prefixWord ++ tailWord_1229760) baseStart_1229760 baseEnd_1229760 := by
    simpa [prefixWord, tailWord_1229760, baseEnd_1229760] using wordTrace_append hprefix tailTrace_1229760
  have hstable : (prefixWord ++ tailWord_1229760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1229760).length < 2 ^ (prefixWord ++ tailWord_1229760).sum := by decide
  have hdescent : baseEnd_1229760 < baseStart_1229760 := by decide
  rcases family_descends (prefixWord ++ tailWord_1229760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1229780 : List Nat := [2, 4, 1, 2, 1, 3, 2, 2, 1, 2, 3]
def baseStart_1229780 : Nat := 118140960795 + 1229780 * 2 ^ 59
def prefixEnd_1229780 : Nat := 4983230072969 + 3 ^ 40 * 1229780 * 2
def baseEnd_1229780 : Nat := 631468239286303713794351

theorem tailTrace_1229780 : CollatzResearch.WordTrace tailWord_1229780 prefixEnd_1229780 631468239286303713794351 := by
  unfold tailWord_1229780
  simp only [CollatzResearch.WordTrace]
  refine ⟨22426880742362282273895397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29902507656483043031860529 22426880742362282273895397)
  ·
    refine ⟨4205040139192927926355387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22426880742362282273895397 4205040139192927926355387)
    ·
      refine ⟨6307560208789391889533081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4205040139192927926355387 6307560208789391889533081)
      ·
        refine ⟨4730670156592043917149811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6307560208789391889533081 4730670156592043917149811)
        ·
          refine ⟨7096005234888065875724717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4730670156592043917149811 7096005234888065875724717)
          ·
            refine ⟨2661001963083024703396769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7096005234888065875724717 2661001963083024703396769)
            ·
              refine ⟨1995751472312268527547577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2661001963083024703396769 1995751472312268527547577)
              ·
                refine ⟨1496813604234201395660683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1995751472312268527547577 1496813604234201395660683)
                ·
                  refine ⟨2245220406351302093491025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1496813604234201395660683 2245220406351302093491025)
                  ·
                    refine ⟨1683915304763476570118269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2245220406351302093491025 1683915304763476570118269)
                    ·
                      refine ⟨631468239286303713794351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1683915304763476570118269 631468239286303713794351)
                      ·
                        rfl

theorem cell23_1229780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 2, 2, 1, 2, 3].length) (baseStart_1229780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1229780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1229780 prefixEnd_1229780 := by exact prefixLift 1229780
  have htrace : WordTrace (prefixWord ++ tailWord_1229780) baseStart_1229780 baseEnd_1229780 := by
    simpa [prefixWord, tailWord_1229780, baseEnd_1229780] using wordTrace_append hprefix tailTrace_1229780
  have hstable : (prefixWord ++ tailWord_1229780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1229780).length < 2 ^ (prefixWord ++ tailWord_1229780).sum := by decide
  have hdescent : baseEnd_1229780 < baseStart_1229780 := by decide
  rcases family_descends (prefixWord ++ tailWord_1229780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1229819 : List Nat := [1, 1, 1, 1, 1, 3, 3, 1, 3, 3, 5]
def baseStart_1229819 : Nat := 118140960795 + 1229819 * 2 ^ 59
def prefixEnd_1229819 : Nat := 4983230072969 + 3 ^ 40 * 1229819 * 2
def baseEnd_1229819 : Nat := 631488265031829061206671

theorem tailTrace_1229819 : CollatzResearch.WordTrace tailWord_1229819 prefixEnd_1229819 631488265031829061206671 := by
  unfold tailWord_1229819
  simp only [CollatzResearch.WordTrace]
  refine ⟨44855183931583274208460511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29903455954388849472307007 44855183931583274208460511)
  ·
    refine ⟨67282775897374911312690767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44855183931583274208460511 67282775897374911312690767)
    ·
      refine ⟨100924163846062366969036151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67282775897374911312690767 100924163846062366969036151)
      ·
        refine ⟨151386245769093550453554227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100924163846062366969036151 151386245769093550453554227)
        ·
          refine ⟨227079368653640325680331341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151386245769093550453554227 227079368653640325680331341)
          ·
            refine ⟨85154763245115122130124253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 227079368653640325680331341 85154763245115122130124253)
            ·
              refine ⟨31933036216918170798796595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85154763245115122130124253 31933036216918170798796595)
              ·
                refine ⟨47899554325377256198194893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31933036216918170798796595 47899554325377256198194893)
                ·
                  refine ⟨17962332872016471074323085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47899554325377256198194893 17962332872016471074323085)
                  ·
                    refine ⟨6735874827006176652871157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17962332872016471074323085 6735874827006176652871157)
                    ·
                      refine ⟨631488265031829061206671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6735874827006176652871157 631488265031829061206671)
                      ·
                        rfl

theorem cell23_1229819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 3, 3, 5].length) (baseStart_1229819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1229819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1229819 prefixEnd_1229819 := by exact prefixLift 1229819
  have htrace : WordTrace (prefixWord ++ tailWord_1229819) baseStart_1229819 baseEnd_1229819 := by
    simpa [prefixWord, tailWord_1229819, baseEnd_1229819] using wordTrace_append hprefix tailTrace_1229819
  have hstable : (prefixWord ++ tailWord_1229819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1229819).length < 2 ^ (prefixWord ++ tailWord_1229819).sum := by decide
  have hdescent : baseEnd_1229819 < baseStart_1229819 := by decide
  rcases family_descends (prefixWord ++ tailWord_1229819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1229836 : List Nat := [2, 2, 1, 2, 3, 2, 1, 2, 2, 1, 5]
def baseStart_1229836 : Nat := 118140960795 + 1229836 * 2 ^ 59
def prefixEnd_1229836 : Nat := 4983230072969 + 3 ^ 40 * 1229836 * 2
def baseEnd_1229836 : Nat := 631496994202955494694093

theorem tailTrace_1229836 : CollatzResearch.WordTrace tailWord_1229836 prefixEnd_1229836 631496994202955494694093 := by
  unfold tailWord_1229836
  simp only [CollatzResearch.WordTrace]
  refine ⟨22427901986260843055914681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29903869315014457407886241 22427901986260843055914681)
  ·
    refine ⟨16820926489695632291936011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22427901986260843055914681 16820926489695632291936011)
    ·
      refine ⟨25231389734543448437904017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16820926489695632291936011 25231389734543448437904017)
      ·
        refine ⟨18923542300907586328428013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25231389734543448437904017 18923542300907586328428013)
        ·
          refine ⟨7096328362840344873160505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18923542300907586328428013 7096328362840344873160505)
          ·
            refine ⟨5322246272130258654870379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7096328362840344873160505 5322246272130258654870379)
            ·
              refine ⟨7983369408195387982305569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5322246272130258654870379 7983369408195387982305569)
              ·
                refine ⟨5987527056146540986729177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7983369408195387982305569 5987527056146540986729177)
                ·
                  refine ⟨4490645292109905740046883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5987527056146540986729177 4490645292109905740046883)
                  ·
                    refine ⟨6735967938164858610070325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4490645292109905740046883 6735967938164858610070325)
                    ·
                      refine ⟨631496994202955494694093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6735967938164858610070325 631496994202955494694093)
                      ·
                        rfl

theorem cell23_1229836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 2, 2, 1, 5].length) (baseStart_1229836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1229836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1229836 prefixEnd_1229836 := by exact prefixLift 1229836
  have htrace : WordTrace (prefixWord ++ tailWord_1229836) baseStart_1229836 baseEnd_1229836 := by
    simpa [prefixWord, tailWord_1229836, baseEnd_1229836] using wordTrace_append hprefix tailTrace_1229836
  have hstable : (prefixWord ++ tailWord_1229836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1229836).length < 2 ^ (prefixWord ++ tailWord_1229836).sum := by decide
  have hdescent : baseEnd_1229836 < baseStart_1229836 := by decide
  rcases family_descends (prefixWord ++ tailWord_1229836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1229873 : List Nat := [1, 2, 2, 3, 1, 2, 3, 4, 5]
def baseStart_1229873 : Nat := 118140960795 + 1229873 * 2 ^ 59
def prefixEnd_1229873 : Nat := 4983230072969 + 3 ^ 40 * 1229873 * 2
def baseEnd_1229873 : Nat := 70168443665241316659047

theorem tailTrace_1229873 : CollatzResearch.WordTrace tailWord_1229873 prefixEnd_1229873 70168443665241316659047 := by
  unfold tailWord_1229873
  simp only [CollatzResearch.WordTrace]
  refine ⟨44857153473387641430926273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29904768982258427620617515 44857153473387641430926273)
  ·
    refine ⟨33642865105040731073194705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44857153473387641430926273 33642865105040731073194705)
    ·
      refine ⟨25232148828780548304896029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33642865105040731073194705 25232148828780548304896029)
      ·
        refine ⟨9462055810792705614336011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25232148828780548304896029 9462055810792705614336011)
        ·
          refine ⟨14193083716189058421504017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9462055810792705614336011 14193083716189058421504017)
          ·
            refine ⟨10644812787141793816128013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14193083716189058421504017 10644812787141793816128013)
            ·
              refine ⟨3991804795178172681048005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10644812787141793816128013 3991804795178172681048005)
              ·
                refine ⟨748463399095907377696501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3991804795178172681048005 748463399095907377696501)
                ·
                  refine ⟨70168443665241316659047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 748463399095907377696501 70168443665241316659047)
                  ·
                    rfl

theorem cell23_1229873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 4, 5].length) (baseStart_1229873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1229873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1229873 prefixEnd_1229873 := by exact prefixLift 1229873
  have htrace : WordTrace (prefixWord ++ tailWord_1229873) baseStart_1229873 baseEnd_1229873 := by
    simpa [prefixWord, tailWord_1229873, baseEnd_1229873] using wordTrace_append hprefix tailTrace_1229873
  have hstable : (prefixWord ++ tailWord_1229873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1229873).length < 2 ^ (prefixWord ++ tailWord_1229873).sum := by decide
  have hdescent : baseEnd_1229873 < baseStart_1229873 := by decide
  rcases family_descends (prefixWord ++ tailWord_1229873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1229918 : List Nat := [4, 4, 1, 1, 1, 3, 1, 2, 2, 2, 2]
def baseStart_1229918 : Nat := 118140960795 + 1229918 * 2 ^ 59
def prefixEnd_1229918 : Nat := 4983230072969 + 3 ^ 40 * 1229918 * 2
def baseEnd_1229918 : Nat := 631539099616624173868717

theorem tailTrace_1229918 : CollatzResearch.WordTrace tailWord_1229918 prefixEnd_1229918 631539099616624173868717 := by
  unfold tailWord_1229918
  simp only [CollatzResearch.WordTrace]
  refine ⟨5607349344778076764539301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29905863172149742744209605 5607349344778076764539301)
  ·
    refine ⟨1051378002145889393351119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5607349344778076764539301 1051378002145889393351119)
    ·
      refine ⟨1577067003218834090026679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1051378002145889393351119 1577067003218834090026679)
      ·
        refine ⟨2365600504828251135040019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1577067003218834090026679 2365600504828251135040019)
        ·
          refine ⟨3548400757242376702560029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2365600504828251135040019 3548400757242376702560029)
          ·
            refine ⟨1330650283965891263460011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3548400757242376702560029 1330650283965891263460011)
            ·
              refine ⟨1995975425948836895190017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1330650283965891263460011 1995975425948836895190017)
              ·
                refine ⟨1496981569461627671392513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1995975425948836895190017 1496981569461627671392513)
                ·
                  refine ⟨1122736177096220753544385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1496981569461627671392513 1122736177096220753544385)
                  ·
                    refine ⟨842052132822165565158289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1122736177096220753544385 842052132822165565158289)
                    ·
                      refine ⟨631539099616624173868717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 842052132822165565158289 631539099616624173868717)
                      ·
                        rfl

theorem cell23_1229918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 1, 2, 2, 2, 2].length) (baseStart_1229918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1229918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1229918 prefixEnd_1229918 := by exact prefixLift 1229918
  have htrace : WordTrace (prefixWord ++ tailWord_1229918) baseStart_1229918 baseEnd_1229918 := by
    simpa [prefixWord, tailWord_1229918, baseEnd_1229918] using wordTrace_append hprefix tailTrace_1229918
  have hstable : (prefixWord ++ tailWord_1229918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1229918).length < 2 ^ (prefixWord ++ tailWord_1229918).sum := by decide
  have hdescent : baseEnd_1229918 < baseStart_1229918 := by decide
  rcases family_descends (prefixWord ++ tailWord_1229918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1229936 : List Nat := [2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 6]
def baseStart_1229936 : Nat := 118140960795 + 1229936 * 2 ^ 59
def prefixEnd_1229936 : Nat := 4983230072969 + 3 ^ 40 * 1229936 * 2
def baseEnd_1229936 : Nat := 631548342268405103443633

theorem tailTrace_1229936 : CollatzResearch.WordTrace tailWord_1229936 prefixEnd_1229936 631548342268405103443633 := by
  unfold tailWord_1229936
  simp only [CollatzResearch.WordTrace]
  refine ⟨22429725636079701595234831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29906300848106268793646441 22429725636079701595234831)
  ·
    refine ⟨33644588454119552392852247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22429725636079701595234831 33644588454119552392852247)
    ·
      refine ⟨50466882681179328589278371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33644588454119552392852247 50466882681179328589278371)
      ·
        refine ⟨75700324021768992883917557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50466882681179328589278371 75700324021768992883917557)
        ·
          refine ⟨7096905377040843082867271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 75700324021768992883917557 7096905377040843082867271)
          ·
            refine ⟨10645358065561264624300907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7096905377040843082867271 10645358065561264624300907)
            ·
              refine ⟨15968037098341896936451361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10645358065561264624300907 15968037098341896936451361)
              ·
                refine ⟨11976027823756422702338521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15968037098341896936451361 11976027823756422702338521)
                ·
                  refine ⟨8982020867817317026753891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11976027823756422702338521 8982020867817317026753891)
                  ·
                    refine ⟨13473031301725975540130837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8982020867817317026753891 13473031301725975540130837)
                    ·
                      refine ⟨631548342268405103443633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13473031301725975540130837 631548342268405103443633)
                      ·
                        rfl

theorem cell23_1229936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 6].length) (baseStart_1229936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1229936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1229936 prefixEnd_1229936 := by exact prefixLift 1229936
  have htrace : WordTrace (prefixWord ++ tailWord_1229936) baseStart_1229936 baseEnd_1229936 := by
    simpa [prefixWord, tailWord_1229936, baseEnd_1229936] using wordTrace_append hprefix tailTrace_1229936
  have hstable : (prefixWord ++ tailWord_1229936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1229936).length < 2 ^ (prefixWord ++ tailWord_1229936).sum := by decide
  have hdescent : baseEnd_1229936 < baseStart_1229936 := by decide
  rcases family_descends (prefixWord ++ tailWord_1229936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
