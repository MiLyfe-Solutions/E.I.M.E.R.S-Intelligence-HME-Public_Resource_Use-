import V185TrunkScan21Chunk078

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_956241 : List Nat := [1, 2, 2, 1, 5, 2, 1, 4, 3]
def baseStart_956241 : Nat := 118140960795 + 956241 * 2 ^ 59
def prefixEnd_956241 : Nat := 4983230072969 + 3 ^ 40 * 956241 * 2
def baseEnd_956241 : Nat := 218227224238265971728815

theorem tailTrace_956241 : CollatzResearch.WordTrace tailWord_956241 prefixEnd_956241 218227224238265971728815 := by
  unfold tailWord_956241
  simp only [CollatzResearch.WordTrace]
  refine ⟨34876974528709644805900577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23251316352473096537267051 34876974528709644805900577)
  ·
    refine ⟨26157730896532233604425433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34876974528709644805900577 26157730896532233604425433)
    ·
      refine ⟨19618298172399175203319075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26157730896532233604425433 19618298172399175203319075)
      ·
        refine ⟨29427447258598762804978613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19618298172399175203319075 29427447258598762804978613)
        ·
          refine ⟨2758823180493634012966745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29427447258598762804978613 2758823180493634012966745)
          ·
            refine ⟨2069117385370225509725059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2758823180493634012966745 2069117385370225509725059)
            ·
              refine ⟨3103676078055338264587589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2069117385370225509725059 3103676078055338264587589)
              ·
                refine ⟨581939264635375924610173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3103676078055338264587589 581939264635375924610173)
                ·
                  refine ⟨218227224238265971728815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 581939264635375924610173 218227224238265971728815)
                  ·
                    rfl

theorem cell21_956241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 4, 3].length) (baseStart_956241 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_956241 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_956241 prefixEnd_956241 := by exact prefixLift 956241
  have htrace : WordTrace (prefixWord ++ tailWord_956241) baseStart_956241 baseEnd_956241 := by
    simpa [prefixWord, tailWord_956241, baseEnd_956241] using wordTrace_append hprefix tailTrace_956241
  have hstable : (prefixWord ++ tailWord_956241).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956241).length < 2 ^ (prefixWord ++ tailWord_956241).sum := by decide
  have hdescent : baseEnd_956241 < baseStart_956241 := by decide
  rcases family_descends (prefixWord ++ tailWord_956241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956286 : List Nat := [4, 2, 3, 1, 1, 2, 8]
def baseStart_956286 : Nat := 118140960795 + 956286 * 2 ^ 59
def prefixEnd_956286 : Nat := 4983230072969 + 3 ^ 40 * 956286 * 2
def baseEnd_956286 : Nat := 24248610427928432608747

theorem tailTrace_956286 : CollatzResearch.WordTrace tailWord_956286 prefixEnd_956286 24248610427928432608747 := by
  unfold tailWord_956286
  simp only [CollatzResearch.WordTrace]
  refine ⟨4359826976693327186411089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23252410542364411660859141 4359826976693327186411089)
  ·
    refine ⟨3269870232519995389808317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4359826976693327186411089 3269870232519995389808317)
    ·
      refine ⟨1226201337194998271178119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3269870232519995389808317 1226201337194998271178119)
      ·
        refine ⟨1839302005792497406767179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1226201337194998271178119 1839302005792497406767179)
        ·
          refine ⟨2758953008688746110150769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1839302005792497406767179 2758953008688746110150769)
          ·
            refine ⟨2069214756516559582613077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2758953008688746110150769 2069214756516559582613077)
            ·
              refine ⟨24248610427928432608747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2069214756516559582613077 24248610427928432608747)
              ·
                rfl

theorem cell21_956286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 8].length) (baseStart_956286 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_956286 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_956286 prefixEnd_956286 := by exact prefixLift 956286
  have htrace : WordTrace (prefixWord ++ tailWord_956286) baseStart_956286 baseEnd_956286 := by
    simpa [prefixWord, tailWord_956286, baseEnd_956286] using wordTrace_append hprefix tailTrace_956286
  have hstable : (prefixWord ++ tailWord_956286).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956286).length < 2 ^ (prefixWord ++ tailWord_956286).sum := by decide
  have hdescent : baseEnd_956286 < baseStart_956286 := by decide
  rcases family_descends (prefixWord ++ tailWord_956286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956289 : List Nat := [1, 2, 4, 4, 1, 2, 1, 2, 4]
def baseStart_956289 : Nat := 118140960795 + 956289 * 2 ^ 59
def prefixEnd_956289 : Nat := 4983230072969 + 3 ^ 40 * 956289 * 2
def baseEnd_956289 : Nat := 218238178492228554928717

theorem tailTrace_956289 : CollatzResearch.WordTrace tailWord_956289 prefixEnd_956289 218238178492228554928717 := by
  unfold tailWord_956289
  simp only [CollatzResearch.WordTrace]
  refine ⟨34878725232535749003647921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23252483488357166002431947 34878725232535749003647921)
  ·
    refine ⟨26159043924401811752735941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34878725232535749003647921 26159043924401811752735941)
    ·
      refine ⟨4904820735825339703637989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26159043924401811752735941 4904820735825339703637989)
      ·
        refine ⟨919653887967251194432123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4904820735825339703637989 919653887967251194432123)
        ·
          refine ⟨1379480831950876791648185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 919653887967251194432123 1379480831950876791648185)
          ·
            refine ⟨1034610623963157593736139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1379480831950876791648185 1034610623963157593736139)
            ·
              refine ⟨1551915935944736390604209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1034610623963157593736139 1551915935944736390604209)
              ·
                refine ⟨1163936951958552292953157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1551915935944736390604209 1163936951958552292953157)
                ·
                  refine ⟨218238178492228554928717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1163936951958552292953157 218238178492228554928717)
                  ·
                    rfl

theorem cell21_956289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 1, 2, 4].length) (baseStart_956289 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_956289 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_956289 prefixEnd_956289 := by exact prefixLift 956289
  have htrace : WordTrace (prefixWord ++ tailWord_956289) baseStart_956289 baseEnd_956289 := by
    simpa [prefixWord, tailWord_956289, baseEnd_956289] using wordTrace_append hprefix tailTrace_956289
  have hstable : (prefixWord ++ tailWord_956289).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956289).length < 2 ^ (prefixWord ++ tailWord_956289).sum := by decide
  have hdescent : baseEnd_956289 < baseStart_956289 := by decide
  rcases family_descends (prefixWord ++ tailWord_956289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956421 : List Nat := [1, 3, 1, 1, 2, 6, 1, 6]
def baseStart_956421 : Nat := 118140960795 + 956421 * 2 ^ 59
def prefixEnd_956421 : Nat := 4983230072969 + 3 ^ 40 * 956421 * 2
def baseEnd_956421 : Nat := 72756100896875219576149

theorem tailTrace_956421 : CollatzResearch.WordTrace tailWord_956421 prefixEnd_956421 72756100896875219576149 := by
  unfold tailWord_956421
  simp only [CollatzResearch.WordTrace]
  refine ⟨34883539668057535547453117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23255693112038357031635411 34883539668057535547453117)
  ·
    refine ⟨13081327375521575830294919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34883539668057535547453117 13081327375521575830294919)
    ·
      refine ⟨19621991063282363745442379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13081327375521575830294919 19621991063282363745442379)
      ·
        refine ⟨29432986594923545618163569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19621991063282363745442379 29432986594923545618163569)
        ·
          refine ⟨22074739946192659213622677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29432986594923545618163569 22074739946192659213622677)
          ·
            refine ⟨1034753434977780900638563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 22074739946192659213622677 1034753434977780900638563)
            ·
              refine ⟨1552130152466671350957845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1034753434977780900638563 1552130152466671350957845)
              ·
                refine ⟨72756100896875219576149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1552130152466671350957845 72756100896875219576149)
                ·
                  rfl

theorem cell21_956421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 1, 6].length) (baseStart_956421 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_956421 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_956421 prefixEnd_956421 := by exact prefixLift 956421
  have htrace : WordTrace (prefixWord ++ tailWord_956421) baseStart_956421 baseEnd_956421 := by
    simpa [prefixWord, tailWord_956421, baseEnd_956421] using wordTrace_append hprefix tailTrace_956421
  have hstable : (prefixWord ++ tailWord_956421).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956421).length < 2 ^ (prefixWord ++ tailWord_956421).sum := by decide
  have hdescent : baseEnd_956421 < baseStart_956421 := by decide
  rcases family_descends (prefixWord ++ tailWord_956421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956466 : List Nat := [3, 2, 1, 1, 2, 4, 1, 1, 6]
def baseStart_956466 : Nat := 118140960795 + 956466 * 2 ^ 59
def prefixEnd_956466 : Nat := 4983230072969 + 3 ^ 40 * 956466 * 2
def baseEnd_956466 : Nat := 218278572303715580478355

theorem tailTrace_956466 : CollatzResearch.WordTrace tailWord_956466 prefixEnd_956466 218278572303715580478355 := by
  unfold tailWord_956466
  simp only [CollatzResearch.WordTrace]
  refine ⟨8721295238223627058210313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23256787301929672155227501 8721295238223627058210313)
  ·
    refine ⟨6540971428667720293657735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8721295238223627058210313 6540971428667720293657735)
    ·
      refine ⟨9811457143001580440486603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6540971428667720293657735 9811457143001580440486603)
      ·
        refine ⟨14717185714502370660729905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9811457143001580440486603 14717185714502370660729905)
        ·
          refine ⟨11037889285876777995547429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14717185714502370660729905 11037889285876777995547429)
          ·
            refine ⟨2069604241101895874165143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11037889285876777995547429 2069604241101895874165143)
            ·
              refine ⟨3104406361652843811247715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2069604241101895874165143 3104406361652843811247715)
              ·
                refine ⟨4656609542479265716871573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3104406361652843811247715 4656609542479265716871573)
                ·
                  refine ⟨218278572303715580478355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4656609542479265716871573 218278572303715580478355)
                  ·
                    rfl

theorem cell21_956466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 1, 6].length) (baseStart_956466 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_956466 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_956466 prefixEnd_956466 := by exact prefixLift 956466
  have htrace : WordTrace (prefixWord ++ tailWord_956466) baseStart_956466 baseEnd_956466 := by
    simpa [prefixWord, tailWord_956466, baseEnd_956466] using wordTrace_append hprefix tailTrace_956466
  have hstable : (prefixWord ++ tailWord_956466).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956466).length < 2 ^ (prefixWord ++ tailWord_956466).sum := by decide
  have hdescent : baseEnd_956466 < baseStart_956466 := by decide
  rcases family_descends (prefixWord ++ tailWord_956466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956514 : List Nat := [3, 3, 2, 2, 2, 2, 7]
def baseStart_956514 : Nat := 118140960795 + 956514 * 2 ^ 59
def prefixEnd_956514 : Nat := 4983230072969 + 3 ^ 40 * 956514 * 2
def baseEnd_956514 : Nat := 24254391839742018186473

theorem tailTrace_956514 : CollatzResearch.WordTrace tailWord_956514 prefixEnd_956514 24254391839742018186473 := by
  unfold tailWord_956514
  simp only [CollatzResearch.WordTrace]
  refine ⟨8721732914180153107647149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23257954437813741620392397 8721732914180153107647149)
  ·
    refine ⟨3270649842817557415367681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8721732914180153107647149 3270649842817557415367681)
    ·
      refine ⟨2452987382113168061525761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3270649842817557415367681 2452987382113168061525761)
      ·
        refine ⟨1839740536584876046144321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2452987382113168061525761 1839740536584876046144321)
        ·
          refine ⟨1379805402438657034608241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1839740536584876046144321 1379805402438657034608241)
          ·
            refine ⟨1034854051828992775956181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1379805402438657034608241 1034854051828992775956181)
            ·
              refine ⟨24254391839742018186473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1034854051828992775956181 24254391839742018186473)
              ·
                rfl

theorem cell21_956514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 7].length) (baseStart_956514 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_956514 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_956514 prefixEnd_956514 := by exact prefixLift 956514
  have htrace : WordTrace (prefixWord ++ tailWord_956514) baseStart_956514 baseEnd_956514 := by
    simpa [prefixWord, tailWord_956514, baseEnd_956514] using wordTrace_append hprefix tailTrace_956514
  have hstable : (prefixWord ++ tailWord_956514).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956514).length < 2 ^ (prefixWord ++ tailWord_956514).sum := by decide
  have hdescent : baseEnd_956514 < baseStart_956514 := by decide
  rcases family_descends (prefixWord ++ tailWord_956514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956528 : List Nat := [2, 1, 1, 1, 5, 4, 1, 1, 5]
def baseStart_956528 : Nat := 118140960795 + 956528 * 2 ^ 59
def prefixEnd_956528 : Nat := 4983230072969 + 3 ^ 40 * 956528 * 2
def baseEnd_956528 : Nat := 218292721548417250444895

theorem tailTrace_956528 : CollatzResearch.WordTrace tailWord_956528 prefixEnd_956528 218292721548417250444895 := by
  unfold tailWord_956528
  simp only [CollatzResearch.WordTrace]
  refine ⟨17443721139334946410799119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23258294852446595214398825 17443721139334946410799119)
  ·
    refine ⟨26165581709002419616198679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17443721139334946410799119 26165581709002419616198679)
    ·
      refine ⟨39248372563503629424298019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26165581709002419616198679 39248372563503629424298019)
      ·
        refine ⟨58872558845255444136447029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39248372563503629424298019 58872558845255444136447029)
        ·
          refine ⟨5519302391742697887791909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58872558845255444136447029 5519302391742697887791909)
          ·
            refine ⟨1034869198451755853960983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5519302391742697887791909 1034869198451755853960983)
            ·
              refine ⟨1552303797677633780941475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1034869198451755853960983 1552303797677633780941475)
              ·
                refine ⟨2328455696516450671412213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1552303797677633780941475 2328455696516450671412213)
                ·
                  refine ⟨218292721548417250444895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2328455696516450671412213 218292721548417250444895)
                  ·
                    rfl

theorem cell21_956528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 1, 1, 5].length) (baseStart_956528 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_956528 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_956528 prefixEnd_956528 := by exact prefixLift 956528
  have htrace : WordTrace (prefixWord ++ tailWord_956528) baseStart_956528 baseEnd_956528 := by
    simpa [prefixWord, tailWord_956528, baseEnd_956528] using wordTrace_append hprefix tailTrace_956528
  have hstable : (prefixWord ++ tailWord_956528).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956528).length < 2 ^ (prefixWord ++ tailWord_956528).sum := by decide
  have hdescent : baseEnd_956528 < baseStart_956528 := by decide
  rcases family_descends (prefixWord ++ tailWord_956528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956604 : List Nat := [2, 2, 2, 3, 3, 1, 1, 2, 5]
def baseStart_956604 : Nat := 118140960795 + 956604 * 2 ^ 59
def prefixEnd_956604 : Nat := 4983230072969 + 3 ^ 40 * 956604 * 2
def baseEnd_956604 : Nat := 218310065783858007178073

theorem tailTrace_956604 : CollatzResearch.WordTrace tailWord_956604 prefixEnd_956604 218310065783858007178073 := by
  unfold tailWord_956604
  simp only [CollatzResearch.WordTrace]
  refine ⟨17445107113197278900682433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23260142817596371867576577 17445107113197278900682433)
  ·
    refine ⟨13083830334897959175511825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17445107113197278900682433 13083830334897959175511825)
    ·
      refine ⟨9812872751173469381633869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13083830334897959175511825 9812872751173469381633869)
      ·
        refine ⟨3679827281690051018112701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9812872751173469381633869 3679827281690051018112701)
        ·
          refine ⟨1379935230633769131792263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3679827281690051018112701 1379935230633769131792263)
          ·
            refine ⟨2069902845950653697688395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1379935230633769131792263 2069902845950653697688395)
            ·
              refine ⟨3104854268925980546532593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2069902845950653697688395 3104854268925980546532593)
              ·
                refine ⟨2328640701694485409899445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3104854268925980546532593 2328640701694485409899445)
                ·
                  refine ⟨218310065783858007178073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2328640701694485409899445 218310065783858007178073)
                  ·
                    rfl

theorem cell21_956604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 2, 5].length) (baseStart_956604 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_956604 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_956604 prefixEnd_956604 := by exact prefixLift 956604
  have htrace : WordTrace (prefixWord ++ tailWord_956604) baseStart_956604 baseEnd_956604 := by
    simpa [prefixWord, tailWord_956604, baseEnd_956604] using wordTrace_append hprefix tailTrace_956604
  have hstable : (prefixWord ++ tailWord_956604).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956604).length < 2 ^ (prefixWord ++ tailWord_956604).sum := by decide
  have hdescent : baseEnd_956604 < baseStart_956604 := by decide
  rcases family_descends (prefixWord ++ tailWord_956604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956632 : List Nat := [2, 1, 2, 2, 4, 2, 8]
def baseStart_956632 : Nat := 118140960795 + 956632 * 2 ^ 59
def prefixEnd_956632 : Nat := 4983230072969 + 3 ^ 40 * 956632 * 2
def baseEnd_956632 : Nat := 24257383973926242301261

theorem tailTrace_956632 : CollatzResearch.WordTrace tailWord_956632 prefixEnd_956632 24257383973926242301261 := by
  unfold tailWord_956632
  simp only [CollatzResearch.WordTrace]
  refine ⟨17445617735146559291692075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23260823646862079055589433 17445617735146559291692075)
  ·
    refine ⟨26168426602719838937538113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17445617735146559291692075 26168426602719838937538113)
    ·
      refine ⟨19626319952039879203153585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26168426602719838937538113 19626319952039879203153585)
      ·
        refine ⟨14719739964029909402365189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19626319952039879203153585 14719739964029909402365189)
        ·
          refine ⟨2759951243255608012943473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14719739964029909402365189 2759951243255608012943473)
          ·
            refine ⟨2069963432441706009707605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2759951243255608012943473 2069963432441706009707605)
            ·
              refine ⟨24257383973926242301261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2069963432441706009707605 24257383973926242301261)
              ·
                rfl

theorem cell21_956632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 8].length) (baseStart_956632 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_956632 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_956632 prefixEnd_956632 := by exact prefixLift 956632
  have htrace : WordTrace (prefixWord ++ tailWord_956632) baseStart_956632 baseEnd_956632 := by
    simpa [prefixWord, tailWord_956632, baseEnd_956632] using wordTrace_append hprefix tailTrace_956632
  have hstable : (prefixWord ++ tailWord_956632).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956632).length < 2 ^ (prefixWord ++ tailWord_956632).sum := by decide
  have hdescent : baseEnd_956632 < baseStart_956632 := by decide
  rcases family_descends (prefixWord ++ tailWord_956632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956708 : List Nat := [2, 3, 1, 3, 1, 2, 1, 8]
def baseStart_956708 : Nat := 118140960795 + 956708 * 2 ^ 59
def prefixEnd_956708 : Nat := 4983230072969 + 3 ^ 40 * 956708 * 2
def baseEnd_956708 : Nat := 72777933333592312481509

theorem tailTrace_956708 : CollatzResearch.WordTrace tailWord_956708 prefixEnd_956708 72777933333592312481509 := by
  unfold tailWord_956708
  simp only [CollatzResearch.WordTrace]
  refine ⟨17447003709008891781575389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23262671612011855708767185 17447003709008891781575389)
  ·
    refine ⟨6542626390878334418090771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17447003709008891781575389 6542626390878334418090771)
    ·
      refine ⟨9813939586317501627136157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6542626390878334418090771 9813939586317501627136157)
      ·
        refine ⟨3680227344869063110176059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9813939586317501627136157 3680227344869063110176059)
        ·
          refine ⟨5520341017303594665264089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3680227344869063110176059 5520341017303594665264089)
          ·
            refine ⟨4140255762977695998948067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5520341017303594665264089 4140255762977695998948067)
            ·
              refine ⟨6210383644466543998422101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4140255762977695998948067 6210383644466543998422101)
              ·
                refine ⟨72777933333592312481509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6210383644466543998422101 72777933333592312481509)
                ·
                  rfl

theorem cell21_956708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 8].length) (baseStart_956708 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_956708 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_956708 prefixEnd_956708 := by exact prefixLift 956708
  have htrace : WordTrace (prefixWord ++ tailWord_956708) baseStart_956708 baseEnd_956708 := by
    simpa [prefixWord, tailWord_956708, baseEnd_956708] using wordTrace_append hprefix tailTrace_956708
  have hstable : (prefixWord ++ tailWord_956708).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956708).length < 2 ^ (prefixWord ++ tailWord_956708).sum := by decide
  have hdescent : baseEnd_956708 < baseStart_956708 := by decide
  rcases family_descends (prefixWord ++ tailWord_956708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956849 : List Nat := [1, 2, 2, 4, 1, 4, 1, 3, 3]
def baseStart_956849 : Nat := 118140960795 + 956849 * 2 ^ 59
def prefixEnd_956849 : Nat := 4983230072969 + 3 ^ 40 * 956849 * 2
def baseEnd_956849 : Nat := 218365978121792025594239

theorem tailTrace_956849 : CollatzResearch.WordTrace tailWord_956849 prefixEnd_956849 218365978121792025594239 := by
  unfold tailWord_956849
  simp only [CollatzResearch.WordTrace]
  refine ⟨34899150110506964644033601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23266100073671309762689067 34899150110506964644033601)
  ·
    refine ⟨26174362582880223483025201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34899150110506964644033601 26174362582880223483025201)
    ·
      refine ⟨19630771937160167612268901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26174362582880223483025201 19630771937160167612268901)
      ·
        refine ⟨3680769738217531427300419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19630771937160167612268901 3680769738217531427300419)
        ·
          refine ⟨5521154607326297140950629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3680769738217531427300419 5521154607326297140950629)
          ·
            refine ⟨1035216488873680713928243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5521154607326297140950629 1035216488873680713928243)
            ·
              refine ⟨1552824733310521070892365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1035216488873680713928243 1552824733310521070892365)
              ·
                refine ⟨582309274991445401584637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1552824733310521070892365 582309274991445401584637)
                ·
                  refine ⟨218365978121792025594239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 582309274991445401584637 218365978121792025594239)
                  ·
                    rfl

theorem cell21_956849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 1, 3, 3].length) (baseStart_956849 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_956849 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_956849 prefixEnd_956849 := by exact prefixLift 956849
  have htrace : WordTrace (prefixWord ++ tailWord_956849) baseStart_956849 baseEnd_956849 := by
    simpa [prefixWord, tailWord_956849, baseEnd_956849] using wordTrace_append hprefix tailTrace_956849
  have hstable : (prefixWord ++ tailWord_956849).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956849).length < 2 ^ (prefixWord ++ tailWord_956849).sum := by decide
  have hdescent : baseEnd_956849 < baseStart_956849 := by decide
  rcases family_descends (prefixWord ++ tailWord_956849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956860 : List Nat := [2, 2, 2, 4, 1, 1, 9]
def baseStart_956860 : Nat := 118140960795 + 956860 * 2 ^ 59
def prefixEnd_956860 : Nat := 4983230072969 + 3 ^ 40 * 956860 * 2
def baseEnd_956860 : Nat := 24263165385739827878987

theorem tailTrace_956860 : CollatzResearch.WordTrace tailWord_956860 prefixEnd_956860 24263165385739827878987 := by
  unfold tailWord_956860
  simp only [CollatzResearch.WordTrace]
  refine ⟨17449775656733556761342017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23266367542311409015122689 17449775656733556761342017)
  ·
    refine ⟨13087331742550167571006513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17449775656733556761342017 13087331742550167571006513)
    ·
      refine ⟨9815498806912625678254885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13087331742550167571006513 9815498806912625678254885)
      ·
        refine ⟨1840406026296117314672791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9815498806912625678254885 1840406026296117314672791)
        ·
          refine ⟨2760609039444175972009187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1840406026296117314672791 2760609039444175972009187)
          ·
            refine ⟨4140913559166263958013781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2760609039444175972009187 4140913559166263958013781)
            ·
              refine ⟨24263165385739827878987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4140913559166263958013781 24263165385739827878987)
              ·
                rfl

theorem cell21_956860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 9].length) (baseStart_956860 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_956860 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_956860 prefixEnd_956860 := by exact prefixLift 956860
  have htrace : WordTrace (prefixWord ++ tailWord_956860) baseStart_956860 baseEnd_956860 := by
    simpa [prefixWord, tailWord_956860, baseEnd_956860] using wordTrace_append hprefix tailTrace_956860
  have hstable : (prefixWord ++ tailWord_956860).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956860).length < 2 ^ (prefixWord ++ tailWord_956860).sum := by decide
  have hdescent : baseEnd_956860 < baseStart_956860 := by decide
  rcases family_descends (prefixWord ++ tailWord_956860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956981 : List Nat := [1, 3, 3, 1, 1, 2, 3, 1, 6]
def baseStart_956981 : Nat := 118140960795 + 956981 * 2 ^ 59
def prefixEnd_956981 : Nat := 4983230072969 + 3 ^ 40 * 956981 * 2
def baseEnd_956981 : Nat := 218396102320189129393969

theorem tailTrace_956981 : CollatzResearch.WordTrace tailWord_956981 prefixEnd_956981 218396102320189129393969 := by
  unfold tailWord_956981
  simp only [CollatzResearch.WordTrace]
  refine ⟨34903964546028751187838797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23269309697352500791892531 34903964546028751187838797)
  ·
    refine ⟨13088986704760781695439549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34903964546028751187838797 13088986704760781695439549)
    ·
      refine ⟨4908370014285293135789831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13088986704760781695439549 4908370014285293135789831)
      ·
        refine ⟨7362555021427939703684747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4908370014285293135789831 7362555021427939703684747)
        ·
          refine ⟨11043832532141909555527121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7362555021427939703684747 11043832532141909555527121)
          ·
            refine ⟨8282874399106432166645341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11043832532141909555527121 8282874399106432166645341)
            ·
              refine ⟨3106077899664912062492003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8282874399106432166645341 3106077899664912062492003)
              ·
                refine ⟨4659116849497368093738005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3106077899664912062492003 4659116849497368093738005)
                ·
                  refine ⟨218396102320189129393969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4659116849497368093738005 218396102320189129393969)
                  ·
                    rfl

theorem cell21_956981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 1, 6].length) (baseStart_956981 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_956981 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_956981 prefixEnd_956981 := by exact prefixLift 956981
  have htrace : WordTrace (prefixWord ++ tailWord_956981) baseStart_956981 baseEnd_956981 := by
    simpa [prefixWord, tailWord_956981, baseEnd_956981] using wordTrace_append hprefix tailTrace_956981
  have hstable : (prefixWord ++ tailWord_956981).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956981).length < 2 ^ (prefixWord ++ tailWord_956981).sum := by decide
  have hdescent : baseEnd_956981 < baseStart_956981 := by decide
  rcases family_descends (prefixWord ++ tailWord_956981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957012 : List Nat := [2, 4, 1, 1, 1, 4, 1, 7]
def baseStart_957012 : Nat := 118140960795 + 957012 * 2 ^ 59
def prefixEnd_957012 : Nat := 4983230072969 + 3 ^ 40 * 957012 * 2
def baseEnd_957012 : Nat := 72801058980846654792413

theorem tailTrace_957012 : CollatzResearch.WordTrace tailWord_957012 prefixEnd_957012 72801058980846654792413 := by
  unfold tailWord_957012
  simp only [CollatzResearch.WordTrace]
  refine ⟨17452547604458221741108645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23270063472610962321478193 17452547604458221741108645)
  ·
    refine ⟨3272352675835916576457871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17452547604458221741108645 3272352675835916576457871)
    ·
      refine ⟨4908529013753874864686807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3272352675835916576457871 4908529013753874864686807)
      ·
        refine ⟨7362793520630812297030211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4908529013753874864686807 7362793520630812297030211)
        ·
          refine ⟨11044190280946218445545317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7362793520630812297030211 11044190280946218445545317)
          ·
            refine ⟨2070785677677415958539747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11044190280946218445545317 2070785677677415958539747)
            ·
              refine ⟨3106178516516123937809621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2070785677677415958539747 3106178516516123937809621)
              ·
                refine ⟨72801058980846654792413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3106178516516123937809621 72801058980846654792413)
                ·
                  rfl

theorem cell21_957012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 7].length) (baseStart_957012 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_957012 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_957012 prefixEnd_957012 := by exact prefixLift 957012
  have htrace : WordTrace (prefixWord ++ tailWord_957012) baseStart_957012 baseEnd_957012 := by
    simpa [prefixWord, tailWord_957012, baseEnd_957012] using wordTrace_append hprefix tailTrace_957012
  have hstable : (prefixWord ++ tailWord_957012).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957012).length < 2 ^ (prefixWord ++ tailWord_957012).sum := by decide
  have hdescent : baseEnd_957012 < baseStart_957012 := by decide
  rcases family_descends (prefixWord ++ tailWord_957012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957029 : List Nat := [1, 3, 1, 3, 5, 1, 7]
def baseStart_957029 : Nat := 118140960795 + 957029 * 2 ^ 59
def prefixEnd_957029 : Nat := 4983230072969 + 3 ^ 40 * 957029 * 2
def baseEnd_957029 : Nat := 24267450730461301399319

theorem tailTrace_957029 : CollatzResearch.WordTrace tailWord_957029 prefixEnd_957029 24267450730461301399319 := by
  unfold tailWord_957029
  simp only [CollatzResearch.WordTrace]
  refine ⟨34905715249854855385586141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23270476833236570257057427 34905715249854855385586141)
  ·
    refine ⟨13089643218695570769594803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34905715249854855385586141 13089643218695570769594803)
    ·
      refine ⟨19634464828043356154392205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13089643218695570769594803 19634464828043356154392205)
      ·
        refine ⟨7362924310516258557897077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19634464828043356154392205 7362924310516258557897077)
        ·
          refine ⟨690274154110899239802851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7362924310516258557897077 690274154110899239802851)
          ·
            refine ⟨1035411231166348859704277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 690274154110899239802851 1035411231166348859704277)
            ·
              refine ⟨24267450730461301399319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1035411231166348859704277 24267450730461301399319)
              ·
                rfl

theorem cell21_957029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 7].length) (baseStart_957029 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_957029 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_957029 prefixEnd_957029 := by exact prefixLift 957029
  have htrace : WordTrace (prefixWord ++ tailWord_957029) baseStart_957029 baseEnd_957029 := by
    simpa [prefixWord, tailWord_957029, baseEnd_957029] using wordTrace_append hprefix tailTrace_957029
  have hstable : (prefixWord ++ tailWord_957029).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957029).length < 2 ^ (prefixWord ++ tailWord_957029).sum := by decide
  have hdescent : baseEnd_957029 < baseStart_957029 := by decide
  rcases family_descends (prefixWord ++ tailWord_957029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957088 : List Nat := [2, 1, 1, 4, 5, 8]
def baseStart_957088 : Nat := 118140960795 + 957088 * 2 ^ 59
def prefixEnd_957088 : Nat := 4983230072969 + 3 ^ 40 * 957088 * 2
def baseEnd_957088 : Nat := 8089648932517804485571

theorem tailTrace_957088 : CollatzResearch.WordTrace tailWord_957088 prefixEnd_957088 8089648932517804485571 := by
  unfold tailWord_957088
  simp only [CollatzResearch.WordTrace]
  refine ⟨17453933578320554230991959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23271911437760738974655945 17453933578320554230991959)
  ·
    refine ⟨26180900367480831346487939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17453933578320554230991959 26180900367480831346487939)
    ·
      refine ⟨39271350551221247019731909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26180900367480831346487939 39271350551221247019731909)
      ·
        refine ⟨7363378228353983816199733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39271350551221247019731909 7363378228353983816199733)
        ·
          refine ⟨690316708908185982768725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7363378228353983816199733 690316708908185982768725)
          ·
            refine ⟨8089648932517804485571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 690316708908185982768725 8089648932517804485571)
            ·
              rfl

theorem cell21_957088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 8].length) (baseStart_957088 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_957088 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_957088 prefixEnd_957088 := by exact prefixLift 957088
  have htrace : WordTrace (prefixWord ++ tailWord_957088) baseStart_957088 baseEnd_957088 := by
    simpa [prefixWord, tailWord_957088, baseEnd_957088] using wordTrace_append hprefix tailTrace_957088
  have hstable : (prefixWord ++ tailWord_957088).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957088).length < 2 ^ (prefixWord ++ tailWord_957088).sum := by decide
  have hdescent : baseEnd_957088 < baseStart_957088 := by decide
  rcases family_descends (prefixWord ++ tailWord_957088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957178 : List Nat := [3, 1, 1, 1, 1, 3, 4, 2, 5]
def baseStart_957178 : Nat := 118140960795 + 957178 * 2 ^ 59
def prefixEnd_957178 : Nat := 4983230072969 + 3 ^ 40 * 957178 * 2
def baseEnd_957178 : Nat := 218441060404160564610233

theorem tailTrace_957178 : CollatzResearch.WordTrace tailWord_957178 prefixEnd_957178 218441060404160564610233 := by
  unfold tailWord_957178
  simp only [CollatzResearch.WordTrace]
  refine ⟨8727787431578763458190047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23274099817543369221840125 8727787431578763458190047)
  ·
    refine ⟨13091681147368145187285071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8727787431578763458190047 13091681147368145187285071)
    ·
      refine ⟨19637521721052217780927607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13091681147368145187285071 19637521721052217780927607)
      ·
        refine ⟨29456282581578326671391411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19637521721052217780927607 29456282581578326671391411)
        ·
          refine ⟨44184423872367490007087117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29456282581578326671391411 44184423872367490007087117)
          ·
            refine ⟨16569158952137808752657669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44184423872367490007087117 16569158952137808752657669)
            ·
              refine ⟨3106717303525839141123313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16569158952137808752657669 3106717303525839141123313)
              ·
                refine ⟨2330037977644379355842485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3106717303525839141123313 2330037977644379355842485)
                ·
                  refine ⟨218441060404160564610233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2330037977644379355842485 218441060404160564610233)
                  ·
                    rfl

theorem cell21_957178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 2, 5].length) (baseStart_957178 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_957178 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_957178 prefixEnd_957178 := by exact prefixLift 957178
  have htrace : WordTrace (prefixWord ++ tailWord_957178) baseStart_957178 baseEnd_957178 := by
    simpa [prefixWord, tailWord_957178, baseEnd_957178] using wordTrace_append hprefix tailTrace_957178
  have hstable : (prefixWord ++ tailWord_957178).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957178).length < 2 ^ (prefixWord ++ tailWord_957178).sum := by decide
  have hdescent : baseEnd_957178 < baseStart_957178 := by decide
  rcases family_descends (prefixWord ++ tailWord_957178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957285 : List Nat := [1, 3, 1, 3, 1, 1, 4, 3, 4]
def baseStart_957285 : Nat := 118140960795 + 957285 * 2 ^ 59
def prefixEnd_957285 : Nat := 4983230072969 + 3 ^ 40 * 957285 * 2
def baseEnd_957285 : Nat := 218465479261952156326681

theorem tailTrace_957285 : CollatzResearch.WordTrace tailWord_957285 prefixEnd_957285 218465479261952156326681 := by
  unfold tailWord_957285
  simp only [CollatzResearch.WordTrace]
  refine ⟨34915052336927411106905309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23276701557951607404603539 34915052336927411106905309)
  ·
    refine ⟨13093144626347779165089491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34915052336927411106905309 13093144626347779165089491)
    ·
      refine ⟨19639716939521668747634237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13093144626347779165089491 19639716939521668747634237)
      ·
        refine ⟨7364893852320625780362839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19639716939521668747634237 7364893852320625780362839)
        ·
          refine ⟨11047340778480938670544259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7364893852320625780362839 11047340778480938670544259)
          ·
            refine ⟨16571011167721408005816389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11047340778480938670544259 16571011167721408005816389)
            ·
              refine ⟨3107064593947764001090573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16571011167721408005816389 3107064593947764001090573)
              ·
                refine ⟨1165149222730411500408965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3107064593947764001090573 1165149222730411500408965)
                ·
                  refine ⟨218465479261952156326681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1165149222730411500408965 218465479261952156326681)
                  ·
                    rfl

theorem cell21_957285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 3, 4].length) (baseStart_957285 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_957285 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_957285 prefixEnd_957285 := by exact prefixLift 957285
  have htrace : WordTrace (prefixWord ++ tailWord_957285) baseStart_957285 baseEnd_957285 := by
    simpa [prefixWord, tailWord_957285, baseEnd_957285] using wordTrace_append hprefix tailTrace_957285
  have hstable : (prefixWord ++ tailWord_957285).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957285).length < 2 ^ (prefixWord ++ tailWord_957285).sum := by decide
  have hdescent : baseEnd_957285 < baseStart_957285 := by decide
  rcases family_descends (prefixWord ++ tailWord_957285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957451 : List Nat := [1, 1, 1, 1, 6, 2, 3, 6]
def baseStart_957451 : Nat := 118140960795 + 957451 * 2 ^ 59
def prefixEnd_957451 : Nat := 4983230072969 + 3 ^ 40 * 957451 * 2
def baseEnd_957451 : Nat := 72834454241190918853225

theorem tailTrace_957451 : CollatzResearch.WordTrace tailWord_957451 prefixEnd_957451 72834454241190918853225 := by
  unfold tailWord_957451
  simp only [CollatzResearch.WordTrace]
  refine ⟨34921106854326021457448207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23280737902884014304965471 34921106854326021457448207)
  ·
    refine ⟨52381660281489032186172311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34921106854326021457448207 52381660281489032186172311)
    ·
      refine ⟨78572490422233548279258467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52381660281489032186172311 78572490422233548279258467)
      ·
        refine ⟨117858735633350322418887701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78572490422233548279258467 117858735633350322418887701)
        ·
          refine ⟨5524628232813296363385361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 117858735633350322418887701 5524628232813296363385361)
          ·
            refine ⟨4143471174609972272539021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5524628232813296363385361 4143471174609972272539021)
            ·
              refine ⟨1553801690478739602202133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4143471174609972272539021 1553801690478739602202133)
              ·
                refine ⟨72834454241190918853225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1553801690478739602202133 72834454241190918853225)
                ·
                  rfl

theorem cell21_957451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 3, 6].length) (baseStart_957451 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_957451 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_957451 prefixEnd_957451 := by exact prefixLift 957451
  have htrace : WordTrace (prefixWord ++ tailWord_957451) baseStart_957451 baseEnd_957451 := by
    simpa [prefixWord, tailWord_957451, baseEnd_957451] using wordTrace_append hprefix tailTrace_957451
  have hstable : (prefixWord ++ tailWord_957451).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957451).length < 2 ^ (prefixWord ++ tailWord_957451).sum := by decide
  have hdescent : baseEnd_957451 < baseStart_957451 := by decide
  rcases family_descends (prefixWord ++ tailWord_957451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957465 : List Nat := [1, 2, 1, 2, 1, 1, 5, 1, 7]
def baseStart_957465 : Nat := 118140960795 + 957465 * 2 ^ 59
def prefixEnd_957465 : Nat := 4983230072969 + 3 ^ 40 * 957465 * 2
def baseEnd_957465 : Nat := 218506557714311843326313

theorem tailTrace_957465 : CollatzResearch.WordTrace tailWord_957465 prefixEnd_957465 218506557714311843326313 := by
  unfold tailWord_957465
  simp only [CollatzResearch.WordTrace]
  refine ⟨34921617476275301848457849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23281078317516867898971899 34921617476275301848457849)
  ·
    refine ⟨26191213107206476386343387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34921617476275301848457849 26191213107206476386343387)
    ·
      refine ⟨39286819660809714579515081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26191213107206476386343387 39286819660809714579515081)
      ·
        refine ⟨29465114745607285934636311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39286819660809714579515081 29465114745607285934636311)
        ·
          refine ⟨44197672118410928901954467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29465114745607285934636311 44197672118410928901954467)
          ·
            refine ⟨66296508177616393352931701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44197672118410928901954467 66296508177616393352931701)
            ·
              refine ⟨6215297641651536876837347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66296508177616393352931701 6215297641651536876837347)
              ·
                refine ⟨9322946462477305315256021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6215297641651536876837347 9322946462477305315256021)
                ·
                  refine ⟨218506557714311843326313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9322946462477305315256021 218506557714311843326313)
                  ·
                    rfl

theorem cell21_957465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 1, 7].length) (baseStart_957465 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_957465 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_957465 prefixEnd_957465 := by exact prefixLift 957465
  have htrace : WordTrace (prefixWord ++ tailWord_957465) baseStart_957465 baseEnd_957465 := by
    simpa [prefixWord, tailWord_957465, baseEnd_957465] using wordTrace_append hprefix tailTrace_957465
  have hstable : (prefixWord ++ tailWord_957465).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957465).length < 2 ^ (prefixWord ++ tailWord_957465).sum := by decide
  have hdescent : baseEnd_957465 < baseStart_957465 := by decide
  rcases family_descends (prefixWord ++ tailWord_957465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957665 : List Nat := [1, 2, 3, 1, 3, 2, 3, 2, 4]
def baseStart_957665 : Nat := 118140960795 + 957665 * 2 ^ 59
def prefixEnd_957665 : Nat := 4983230072969 + 3 ^ 40 * 957665 * 2
def baseEnd_957665 : Nat := 218552200439155939992571

theorem tailTrace_957665 : CollatzResearch.WordTrace tailWord_957665 prefixEnd_957665 218552200439155939992571 := by
  unfold tailWord_957665
  simp only [CollatzResearch.WordTrace]
  refine ⟨34928912075550736005738449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23285941383700490670492299 34928912075550736005738449)
  ·
    refine ⟨26196684056663052004303837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34928912075550736005738449 26196684056663052004303837)
    ·
      refine ⟨9823756521248644501613939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26196684056663052004303837 9823756521248644501613939)
      ·
        refine ⟨14735634781872966752420909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9823756521248644501613939 14735634781872966752420909)
        ·
          refine ⟨5525863043202362532157841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14735634781872966752420909 5525863043202362532157841)
          ·
            refine ⟨4144397282401771899118381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5525863043202362532157841 4144397282401771899118381)
            ·
              refine ⟨1554148980900664462169393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4144397282401771899118381 1554148980900664462169393)
              ·
                refine ⟨1165611735675498346627045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1554148980900664462169393 1165611735675498346627045)
                ·
                  refine ⟨218552200439155939992571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1165611735675498346627045 218552200439155939992571)
                  ·
                    rfl

theorem cell21_957665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 3, 2, 4].length) (baseStart_957665 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_957665 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_957665 prefixEnd_957665 := by exact prefixLift 957665
  have htrace : WordTrace (prefixWord ++ tailWord_957665) baseStart_957665 baseEnd_957665 := by
    simpa [prefixWord, tailWord_957665, baseEnd_957665] using wordTrace_append hprefix tailTrace_957665
  have hstable : (prefixWord ++ tailWord_957665).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957665).length < 2 ^ (prefixWord ++ tailWord_957665).sum := by decide
  have hdescent : baseEnd_957665 < baseStart_957665 := by decide
  rcases family_descends (prefixWord ++ tailWord_957665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957724 : List Nat := [2, 2, 3, 1, 1, 1, 4, 1, 6]
def baseStart_957724 : Nat := 118140960795 + 957724 * 2 ^ 59
def prefixEnd_957724 : Nat := 4983230072969 + 3 ^ 40 * 957724 * 2
def baseEnd_957724 : Nat := 218565665042984948509117

theorem tailTrace_957724 : CollatzResearch.WordTrace tailWord_957724 prefixEnd_957724 218565665042984948509117 := by
  unfold tailWord_957724
  simp only [CollatzResearch.WordTrace]
  refine ⟨17465531991168494541068113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23287375988224659388090817 17465531991168494541068113)
  ·
    refine ⟨13099148993376370905801085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17465531991168494541068113 13099148993376370905801085)
    ·
      refine ⟨4912180872516139089675407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13099148993376370905801085 4912180872516139089675407)
      ·
        refine ⟨7368271308774208634513111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4912180872516139089675407 7368271308774208634513111)
        ·
          refine ⟨11052406963161312951769667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7368271308774208634513111 11052406963161312951769667)
          ·
            refine ⟨16578610444741969427654501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11052406963161312951769667 16578610444741969427654501)
            ·
              refine ⟨3108489458389119267685219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16578610444741969427654501 3108489458389119267685219)
              ·
                refine ⟨4662734187583678901527829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3108489458389119267685219 4662734187583678901527829)
                ·
                  refine ⟨218565665042984948509117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4662734187583678901527829 218565665042984948509117)
                  ·
                    rfl

theorem cell21_957724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 1, 6].length) (baseStart_957724 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_957724 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_957724 prefixEnd_957724 := by exact prefixLift 957724
  have htrace : WordTrace (prefixWord ++ tailWord_957724) baseStart_957724 baseEnd_957724 := by
    simpa [prefixWord, tailWord_957724, baseEnd_957724] using wordTrace_append hprefix tailTrace_957724
  have hstable : (prefixWord ++ tailWord_957724).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957724).length < 2 ^ (prefixWord ++ tailWord_957724).sum := by decide
  have hdescent : baseEnd_957724 < baseStart_957724 := by decide
  rcases family_descends (prefixWord ++ tailWord_957724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957727 : List Nat := [1, 1, 2, 4, 4, 2, 1, 1, 5]
def baseStart_957727 : Nat := 118140960795 + 957727 * 2 ^ 59
def prefixEnd_957727 : Nat := 4983230072969 + 3 ^ 40 * 957727 * 2
def baseEnd_957727 : Nat := 218566349683857609959111

theorem tailTrace_957727 : CollatzResearch.WordTrace tailWord_957727 prefixEnd_957727 218566349683857609959111 := by
  unfold tailWord_957727
  simp only [CollatzResearch.WordTrace]
  refine ⟨34931173401326120594495435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23287448934217413729663623 34931173401326120594495435)
  ·
    refine ⟨52396760101989180891743153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34931173401326120594495435 52396760101989180891743153)
    ·
      refine ⟨39297570076491885668807365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52396760101989180891743153 39297570076491885668807365)
      ·
        refine ⟨7368294389342228562901381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39297570076491885668807365 7368294389342228562901381)
        ·
          refine ⟨1381555198001667855544009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7368294389342228562901381 1381555198001667855544009)
          ·
            refine ⟨1036166398501250891658007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1381555198001667855544009 1036166398501250891658007)
            ·
              refine ⟨1554249597751876337487011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1036166398501250891658007 1554249597751876337487011)
              ·
                refine ⟨2331374396627814506230517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1554249597751876337487011 2331374396627814506230517)
                ·
                  refine ⟨218566349683857609959111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2331374396627814506230517 218566349683857609959111)
                  ·
                    rfl

theorem cell21_957727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 1, 1, 5].length) (baseStart_957727 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_957727 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_957727 prefixEnd_957727 := by exact prefixLift 957727
  have htrace : WordTrace (prefixWord ++ tailWord_957727) baseStart_957727 baseEnd_957727 := by
    simpa [prefixWord, tailWord_957727, baseEnd_957727] using wordTrace_append hprefix tailTrace_957727
  have hstable : (prefixWord ++ tailWord_957727).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957727).length < 2 ^ (prefixWord ++ tailWord_957727).sum := by decide
  have hdescent : baseEnd_957727 < baseStart_957727 := by decide
  rcases family_descends (prefixWord ++ tailWord_957727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957845 : List Nat := [1, 3, 2, 1, 1, 2, 3, 3, 5]
def baseStart_957845 : Nat := 118140960795 + 957845 * 2 ^ 59
def prefixEnd_957845 : Nat := 4983230072969 + 3 ^ 40 * 957845 * 2
def baseEnd_957845 : Nat := 218593278891515626992203

theorem tailTrace_957845 : CollatzResearch.WordTrace tailWord_957845 prefixEnd_957845 218593278891515626992203 := by
  unfold tailWord_957845
  simp only [CollatzResearch.WordTrace]
  refine ⟨34935477214898626747290989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23290318143265751164860659 34935477214898626747290989)
  ·
    refine ⟨13100803955586985030234121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34935477214898626747290989 13100803955586985030234121)
    ·
      refine ⟨9825602966690238772675591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13100803955586985030234121 9825602966690238772675591)
      ·
        refine ⟨14738404450035358159013387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9825602966690238772675591 14738404450035358159013387)
        ·
          refine ⟨22107606675053037238520081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14738404450035358159013387 22107606675053037238520081)
          ·
            refine ⟨16580705006289777928890061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22107606675053037238520081 16580705006289777928890061)
            ·
              refine ⟨6217764377358666723333773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16580705006289777928890061 6217764377358666723333773)
              ·
                refine ⟨2331661641509500021250165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6217764377358666723333773 2331661641509500021250165)
                ·
                  refine ⟨218593278891515626992203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2331661641509500021250165 218593278891515626992203)
                  ·
                    rfl

theorem cell21_957845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 3, 5].length) (baseStart_957845 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_957845 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_957845 prefixEnd_957845 := by exact prefixLift 957845
  have htrace : WordTrace (prefixWord ++ tailWord_957845) baseStart_957845 baseEnd_957845 := by
    simpa [prefixWord, tailWord_957845, baseEnd_957845] using wordTrace_append hprefix tailTrace_957845
  have hstable : (prefixWord ++ tailWord_957845).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957845).length < 2 ^ (prefixWord ++ tailWord_957845).sum := by decide
  have hdescent : baseEnd_957845 < baseStart_957845 := by decide
  rcases family_descends (prefixWord ++ tailWord_957845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957910 : List Nat := [5, 2, 1, 1, 1, 3, 1, 3, 4]
def baseStart_957910 : Nat := 118140960795 + 957910 * 2 ^ 59
def prefixEnd_957910 : Nat := 4983230072969 + 3 ^ 40 * 957910 * 2
def baseEnd_957910 : Nat := 218608112777089958408737

theorem tailTrace_957910 : CollatzResearch.WordTrace tailWord_957910 prefixEnd_957910 218608112777089958408737 := by
  unfold tailWord_957910
  simp only [CollatzResearch.WordTrace]
  refine ⟨2183615497478946428025449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23291898639775428565604789 2183615497478946428025449)
  ·
    refine ⟨1637711623109209821019087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2183615497478946428025449 1637711623109209821019087)
    ·
      refine ⟨2456567434663814731528631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1637711623109209821019087 2456567434663814731528631)
      ·
        refine ⟨3684851151995722097292947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2456567434663814731528631 3684851151995722097292947)
        ·
          refine ⟨5527276727993583145939421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3684851151995722097292947 5527276727993583145939421)
          ·
            refine ⟨2072728772997593679727283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5527276727993583145939421 2072728772997593679727283)
            ·
              refine ⟨3109093159496390519590925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2072728772997593679727283 3109093159496390519590925)
              ·
                refine ⟨1165909934811146444846597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3109093159496390519590925 1165909934811146444846597)
                ·
                  refine ⟨218608112777089958408737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1165909934811146444846597 218608112777089958408737)
                  ·
                    rfl

theorem cell21_957910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_957910 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_957910 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_957910 prefixEnd_957910 := by exact prefixLift 957910
  have htrace : WordTrace (prefixWord ++ tailWord_957910) baseStart_957910 baseEnd_957910 := by
    simpa [prefixWord, tailWord_957910, baseEnd_957910] using wordTrace_append hprefix tailTrace_957910
  have hstable : (prefixWord ++ tailWord_957910).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957910).length < 2 ^ (prefixWord ++ tailWord_957910).sum := by decide
  have hdescent : baseEnd_957910 < baseStart_957910 := by decide
  rcases family_descends (prefixWord ++ tailWord_957910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957935 : List Nat := [1, 1, 2, 1, 4, 1, 2, 1, 8]
def baseStart_957935 : Nat := 118140960795 + 957935 * 2 ^ 59
def prefixEnd_957935 : Nat := 4983230072969 + 3 ^ 40 * 957935 * 2
def baseEnd_957935 : Nat := 218613818117695470492019

theorem tailTrace_957935 : CollatzResearch.WordTrace tailWord_957935 prefixEnd_957935 218613818117695470492019 := by
  unfold tailWord_957935
  simp only [CollatzResearch.WordTrace]
  refine ⟨34938759784572572118067259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23292506523048381412044839 34938759784572572118067259)
  ·
    refine ⟨52408139676858858177100889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34938759784572572118067259 52408139676858858177100889)
    ·
      refine ⟨39306104757644143632825667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52408139676858858177100889 39306104757644143632825667)
      ·
        refine ⟨58959157136466215449238501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39306104757644143632825667 58959157136466215449238501)
        ·
          refine ⟨11054841963087415396732219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58959157136466215449238501 11054841963087415396732219)
          ·
            refine ⟨16582262944631123095098329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11054841963087415396732219 16582262944631123095098329)
            ·
              refine ⟨12436697208473342321323747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16582262944631123095098329 12436697208473342321323747)
              ·
                refine ⟨18655045812710013481985621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12436697208473342321323747 18655045812710013481985621)
                ·
                  refine ⟨218613818117695470492019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18655045812710013481985621 218613818117695470492019)
                  ·
                    rfl

theorem cell21_957935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 1, 8].length) (baseStart_957935 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_957935 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_957935 prefixEnd_957935 := by exact prefixLift 957935
  have htrace : WordTrace (prefixWord ++ tailWord_957935) baseStart_957935 baseEnd_957935 := by
    simpa [prefixWord, tailWord_957935, baseEnd_957935] using wordTrace_append hprefix tailTrace_957935
  have hstable : (prefixWord ++ tailWord_957935).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957935).length < 2 ^ (prefixWord ++ tailWord_957935).sum := by decide
  have hdescent : baseEnd_957935 < baseStart_957935 := by decide
  rcases family_descends (prefixWord ++ tailWord_957935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958135 : List Nat := [1, 1, 3, 1, 5, 3, 1, 6]
def baseStart_958135 : Nat := 118140960795 + 958135 * 2 ^ 59
def prefixEnd_958135 : Nat := 4983230072969 + 3 ^ 40 * 958135 * 2
def baseEnd_958135 : Nat := 72886486947513189052759

theorem tailTrace_958135 : CollatzResearch.WordTrace tailWord_958135 prefixEnd_958135 72886486947513189052759 := by
  unfold tailWord_958135
  simp only [CollatzResearch.WordTrace]
  refine ⟨34946054383848006275347859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23297369589232004183565239 34946054383848006275347859)
  ·
    refine ⟨52419081575772009413021789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34946054383848006275347859 52419081575772009413021789)
    ·
      refine ⟨19657155590914503529883171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52419081575772009413021789 19657155590914503529883171)
      ·
        refine ⟨29485733386371755294824757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19657155590914503529883171 29485733386371755294824757)
        ·
          refine ⟨2764287504972352058889821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29485733386371755294824757 2764287504972352058889821)
          ·
            refine ⟨1036607814364632022083683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2764287504972352058889821 1036607814364632022083683)
            ·
              refine ⟨1554911721546948033125525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1036607814364632022083683 1554911721546948033125525)
              ·
                refine ⟨72886486947513189052759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1554911721546948033125525 72886486947513189052759)
                ·
                  rfl

theorem cell21_958135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 1, 6].length) (baseStart_958135 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_958135 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_958135 prefixEnd_958135 := by exact prefixLift 958135
  have htrace : WordTrace (prefixWord ++ tailWord_958135) baseStart_958135 baseEnd_958135 := by
    simpa [prefixWord, tailWord_958135, baseEnd_958135] using wordTrace_append hprefix tailTrace_958135
  have hstable : (prefixWord ++ tailWord_958135).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958135).length < 2 ^ (prefixWord ++ tailWord_958135).sum := by decide
  have hdescent : baseEnd_958135 < baseStart_958135 := by decide
  rcases family_descends (prefixWord ++ tailWord_958135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958183 : List Nat := [1, 1, 5, 4, 1, 1, 2, 1, 5]
def baseStart_958183 : Nat := 118140960795 + 958183 * 2 ^ 59
def prefixEnd_958183 : Nat := 4983230072969 + 3 ^ 40 * 958183 * 2
def baseEnd_958183 : Nat := 218670415096502150358179

theorem tailTrace_958183 : CollatzResearch.WordTrace tailWord_958183 prefixEnd_958183 218670415096502150358179 := by
  unfold tailWord_958183
  simp only [CollatzResearch.WordTrace]
  refine ⟨34947805087674110473095203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23298536725116073648730135 34947805087674110473095203)
  ·
    refine ⟨52421707631511165709642805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34947805087674110473095203 52421707631511165709642805)
    ·
      refine ⟨4914535090454171785279013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 52421707631511165709642805 4914535090454171785279013)
      ·
        refine ⟨921475329460157209739815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4914535090454171785279013 921475329460157209739815)
        ·
          refine ⟨1382212994190235814609723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 921475329460157209739815 1382212994190235814609723)
          ·
            refine ⟨2073319491285353721914585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1382212994190235814609723 2073319491285353721914585)
            ·
              refine ⟨1554989618464015291435939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2073319491285353721914585 1554989618464015291435939)
              ·
                refine ⟨2332484427696022937153909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1554989618464015291435939 2332484427696022937153909)
                ·
                  refine ⟨218670415096502150358179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2332484427696022937153909 218670415096502150358179)
                  ·
                    rfl

theorem cell21_958183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 2, 1, 5].length) (baseStart_958183 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_958183 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_958183 prefixEnd_958183 := by exact prefixLift 958183
  have htrace : WordTrace (prefixWord ++ tailWord_958183) baseStart_958183 baseEnd_958183 := by
    simpa [prefixWord, tailWord_958183, baseEnd_958183] using wordTrace_append hprefix tailTrace_958183
  have hstable : (prefixWord ++ tailWord_958183).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958183).length < 2 ^ (prefixWord ++ tailWord_958183).sum := by decide
  have hdescent : baseEnd_958183 < baseStart_958183 := by decide
  rcases family_descends (prefixWord ++ tailWord_958183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958194 : List Nat := [3, 2, 1, 3, 1, 1, 2, 8]
def baseStart_958194 : Nat := 118140960795 + 958194 * 2 ^ 59
def prefixEnd_958194 : Nat := 4983230072969 + 3 ^ 40 * 958194 * 2
def baseEnd_958194 : Nat := 72890975148789525224941

theorem tailTrace_958194 : CollatzResearch.WordTrace tailWord_958194 prefixEnd_958194 72890975148789525224941 := by
  unfold tailWord_958194
  simp only [CollatzResearch.WordTrace]
  refine ⟨8737051572658564837936409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23298804193756172901163757 8737051572658564837936409)
  ·
    refine ⟨6552788679493923628452307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8737051572658564837936409 6552788679493923628452307)
    ·
      refine ⟨9829183019240885442678461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6552788679493923628452307 9829183019240885442678461)
      ·
        refine ⟨3685943632215332041004423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9829183019240885442678461 3685943632215332041004423)
        ·
          refine ⟨5528915448322998061506635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3685943632215332041004423 5528915448322998061506635)
          ·
            refine ⟨8293373172484497092259953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5528915448322998061506635 8293373172484497092259953)
            ·
              refine ⟨6220029879363372819194965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8293373172484497092259953 6220029879363372819194965)
              ·
                refine ⟨72890975148789525224941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6220029879363372819194965 72890975148789525224941)
                ·
                  rfl

theorem cell21_958194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 8].length) (baseStart_958194 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_958194 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_958194 prefixEnd_958194 := by exact prefixLift 958194
  have htrace : WordTrace (prefixWord ++ tailWord_958194) baseStart_958194 baseEnd_958194 := by
    simpa [prefixWord, tailWord_958194, baseEnd_958194] using wordTrace_append hprefix tailTrace_958194
  have hstable : (prefixWord ++ tailWord_958194).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958194).length < 2 ^ (prefixWord ++ tailWord_958194).sum := by decide
  have hdescent : baseEnd_958194 < baseStart_958194 := by decide
  rcases family_descends (prefixWord ++ tailWord_958194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958239 : List Nat := [1, 1, 2, 4, 2, 1, 1, 3, 6]
def baseStart_958239 : Nat := 118140960795 + 958239 * 2 ^ 59
def prefixEnd_958239 : Nat := 4983230072969 + 3 ^ 40 * 958239 * 2
def baseEnd_958239 : Nat := 218683195059458497424731

theorem tailTrace_958239 : CollatzResearch.WordTrace tailWord_958239 prefixEnd_958239 218683195059458497424731 := by
  unfold tailWord_958239
  simp only [CollatzResearch.WordTrace]
  refine ⟨34949847575471232037133771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23299898383647488024755847 34949847575471232037133771)
  ·
    refine ⟨52424771363206848055700657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34949847575471232037133771 52424771363206848055700657)
    ·
      refine ⟨39318578522405136041775493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52424771363206848055700657 39318578522405136041775493)
      ·
        refine ⟨7372233472950963007832905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39318578522405136041775493 7372233472950963007832905)
        ·
          refine ⟨5529175104713222255874679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7372233472950963007832905 5529175104713222255874679)
          ·
            refine ⟨8293762657069833383812019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5529175104713222255874679 8293762657069833383812019)
            ·
              refine ⟨12440643985604750075718029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8293762657069833383812019 12440643985604750075718029)
              ·
                refine ⟨4665241494601781278394261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12440643985604750075718029 4665241494601781278394261)
                ·
                  refine ⟨218683195059458497424731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4665241494601781278394261 218683195059458497424731)
                  ·
                    rfl

theorem cell21_958239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 3, 6].length) (baseStart_958239 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_958239 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_958239 prefixEnd_958239 := by exact prefixLift 958239
  have htrace : WordTrace (prefixWord ++ tailWord_958239) baseStart_958239 baseEnd_958239 := by
    simpa [prefixWord, tailWord_958239, baseEnd_958239] using wordTrace_append hprefix tailTrace_958239
  have hstable : (prefixWord ++ tailWord_958239).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958239).length < 2 ^ (prefixWord ++ tailWord_958239).sum := by decide
  have hdescent : baseEnd_958239 < baseStart_958239 := by decide
  rcases family_descends (prefixWord ++ tailWord_958239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958318 : List Nat := [4, 1, 2, 3, 1, 2, 1, 2, 5]
def baseStart_958318 : Nat := 118140960795 + 958318 * 2 ^ 59
def prefixEnd_958318 : Nat := 4983230072969 + 3 ^ 40 * 958318 * 2
def baseEnd_958318 : Nat := 218701223935771915607903

theorem tailTrace_958318 : CollatzResearch.WordTrace tailWord_958318 prefixEnd_958318 218701223935771915607903 := by
  unfold tailWord_958318
  simp only [CollatzResearch.WordTrace]
  refine ⟨4369091117773128566157451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23301819294790019019506405 4369091117773128566157451)
  ·
    refine ⟨6553636676659692849236177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4369091117773128566157451 6553636676659692849236177)
    ·
      refine ⟨4915227507494769636927133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6553636676659692849236177 4915227507494769636927133)
      ·
        refine ⟨1843210315310538613847675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4915227507494769636927133 1843210315310538613847675)
        ·
          refine ⟨2764815472965807920771513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1843210315310538613847675 2764815472965807920771513)
          ·
            refine ⟨2073611604724355940578635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2764815472965807920771513 2073611604724355940578635)
            ·
              refine ⟨3110417407086533910867953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2073611604724355940578635 3110417407086533910867953)
              ·
                refine ⟨2332813055314900433150965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3110417407086533910867953 2332813055314900433150965)
                ·
                  refine ⟨218701223935771915607903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2332813055314900433150965 218701223935771915607903)
                  ·
                    rfl

theorem cell21_958318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 2, 5].length) (baseStart_958318 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_958318 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_958318 prefixEnd_958318 := by exact prefixLift 958318
  have htrace : WordTrace (prefixWord ++ tailWord_958318) baseStart_958318 baseEnd_958318 := by
    simpa [prefixWord, tailWord_958318, baseEnd_958318] using wordTrace_append hprefix tailTrace_958318
  have hstable : (prefixWord ++ tailWord_958318).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958318).length < 2 ^ (prefixWord ++ tailWord_958318).sum := by decide
  have hdescent : baseEnd_958318 < baseStart_958318 := by decide
  rcases family_descends (prefixWord ++ tailWord_958318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958436 : List Nat := [2, 3, 1, 1, 1, 1, 4, 1, 7]
def baseStart_958436 : Nat := 118140960795 + 958436 * 2 ^ 59
def prefixEnd_958436 : Nat := 4983230072969 + 3 ^ 40 * 958436 * 2
def baseEnd_958436 : Nat := 218728153143429932640995

theorem tailTrace_958436 : CollatzResearch.WordTrace tailWord_958436 prefixEnd_958436 218728153143429932640995 := by
  unfold tailWord_958436
  simp only [CollatzResearch.WordTrace]
  refine ⟨17478516377878767341027581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23304688503838356454703441 17478516377878767341027581)
  ·
    refine ⟨6554443641704537752885343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17478516377878767341027581 6554443641704537752885343)
    ·
      refine ⟨9831665462556806629328015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6554443641704537752885343 9831665462556806629328015)
      ·
        refine ⟨14747498193835209943992023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9831665462556806629328015 14747498193835209943992023)
        ·
          refine ⟨22121247290752814915988035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14747498193835209943992023 22121247290752814915988035)
          ·
            refine ⟨33181870936129222373982053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22121247290752814915988035 33181870936129222373982053)
            ·
              refine ⟨6221600800524229195121635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33181870936129222373982053 6221600800524229195121635)
              ·
                refine ⟨9332401200786343792682453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6221600800524229195121635 9332401200786343792682453)
                ·
                  refine ⟨218728153143429932640995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9332401200786343792682453 218728153143429932640995)
                  ·
                    rfl

theorem cell21_958436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 1, 7].length) (baseStart_958436 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_958436 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_958436 prefixEnd_958436 := by exact prefixLift 958436
  have htrace : WordTrace (prefixWord ++ tailWord_958436) baseStart_958436 baseEnd_958436 := by
    simpa [prefixWord, tailWord_958436, baseEnd_958436] using wordTrace_append hprefix tailTrace_958436
  have hstable : (prefixWord ++ tailWord_958436).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958436).length < 2 ^ (prefixWord ++ tailWord_958436).sum := by decide
  have hdescent : baseEnd_958436 < baseStart_958436 := by decide
  rcases family_descends (prefixWord ++ tailWord_958436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958504 : List Nat := [2, 1, 5, 3, 1, 1, 2, 3, 3]
def baseStart_958504 : Nat := 118140960795 + 958504 * 2 ^ 59
def prefixEnd_958504 : Nat := 4983230072969 + 3 ^ 40 * 958504 * 2
def baseEnd_958504 : Nat := 218743671669876925507523

theorem tailTrace_958504 : CollatzResearch.WordTrace tailWord_958504 prefixEnd_958504 218743671669876925507523 := by
  unfold tailWord_958504
  simp only [CollatzResearch.WordTrace]
  refine ⟨17479756459755591147765283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23306341946340788197020377 17479756459755591147765283)
  ·
    refine ⟨26219634689633386721647925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17479756459755591147765283 26219634689633386721647925)
    ·
      refine ⟨2458090752153130005154493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26219634689633386721647925 2458090752153130005154493)
      ·
        refine ⟨921784032057423751932935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2458090752153130005154493 921784032057423751932935)
        ·
          refine ⟨1382676048086135627899403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 921784032057423751932935 1382676048086135627899403)
          ·
            refine ⟨2074014072129203441849105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1382676048086135627899403 2074014072129203441849105)
            ·
              refine ⟨1555510554096902581386829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2074014072129203441849105 1555510554096902581386829)
              ·
                refine ⟨583316457786338468020061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1555510554096902581386829 583316457786338468020061)
                ·
                  refine ⟨218743671669876925507523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 583316457786338468020061 218743671669876925507523)
                  ·
                    rfl

theorem cell21_958504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 2, 3, 3].length) (baseStart_958504 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_958504 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_958504 prefixEnd_958504 := by exact prefixLift 958504
  have htrace : WordTrace (prefixWord ++ tailWord_958504) baseStart_958504 baseEnd_958504 := by
    simpa [prefixWord, tailWord_958504, baseEnd_958504] using wordTrace_append hprefix tailTrace_958504
  have hstable : (prefixWord ++ tailWord_958504).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958504).length < 2 ^ (prefixWord ++ tailWord_958504).sum := by decide
  have hdescent : baseEnd_958504 < baseStart_958504 := by decide
  rcases family_descends (prefixWord ++ tailWord_958504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958529 : List Nat := [1, 2, 5, 1, 2, 1, 1, 3, 5]
def baseStart_958529 : Nat := 118140960795 + 958529 * 2 ^ 59
def prefixEnd_958529 : Nat := 4983230072969 + 3 ^ 40 * 958529 * 2
def baseEnd_958529 : Nat := 218749377010482437590805

theorem tailTrace_958529 : CollatzResearch.WordTrace tailWord_958529 prefixEnd_958529 218749377010482437590805 := by
  unfold tailWord_958529
  simp only [CollatzResearch.WordTrace]
  refine ⟨34960424744420611565190641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23306949829613741043460427 34960424744420611565190641)
  ·
    refine ⟨26220318558315458673892981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34960424744420611565190641 26220318558315458673892981)
    ·
      refine ⟨2458154864842074250677467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26220318558315458673892981 2458154864842074250677467)
      ·
        refine ⟨3687232297263111376016201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2458154864842074250677467 3687232297263111376016201)
        ·
          refine ⟨2765424222947333532012151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3687232297263111376016201 2765424222947333532012151)
          ·
            refine ⟨4148136334421000298018227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2765424222947333532012151 4148136334421000298018227)
            ·
              refine ⟨6222204501631500447027341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4148136334421000298018227 6222204501631500447027341)
              ·
                refine ⟨2333326688111812667635253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6222204501631500447027341 2333326688111812667635253)
                ·
                  refine ⟨218749377010482437590805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2333326688111812667635253 218749377010482437590805)
                  ·
                    rfl

theorem cell21_958529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 3, 5].length) (baseStart_958529 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_958529 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_958529 prefixEnd_958529 := by exact prefixLift 958529
  have htrace : WordTrace (prefixWord ++ tailWord_958529) baseStart_958529 baseEnd_958529 := by
    simpa [prefixWord, tailWord_958529, baseEnd_958529] using wordTrace_append hprefix tailTrace_958529
  have hstable : (prefixWord ++ tailWord_958529).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958529).length < 2 ^ (prefixWord ++ tailWord_958529).sum := by decide
  have hdescent : baseEnd_958529 < baseStart_958529 := by decide
  rcases family_descends (prefixWord ++ tailWord_958529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958681 : List Nat := [1, 2, 1, 2, 3, 1, 3, 5, 3]
def baseStart_958681 : Nat := 118140960795 + 958681 * 2 ^ 59
def prefixEnd_958681 : Nat := 4983230072969 + 3 ^ 40 * 958681 * 2
def baseEnd_958681 : Nat := 218784065481363951057161

theorem tailTrace_958681 : CollatzResearch.WordTrace tailWord_958681 prefixEnd_958681 218784065481363951057161 := by
  unfold tailWord_958681
  simp only [CollatzResearch.WordTrace]
  refine ⟨34965968639869941524723897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23310645759913294349815931 34965968639869941524723897)
  ·
    refine ⟨26224476479902456143542923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34965968639869941524723897 26224476479902456143542923)
    ·
      refine ⟨39336714719853684215314385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26224476479902456143542923 39336714719853684215314385)
      ·
        refine ⟨29502536039890263161485789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39336714719853684215314385 29502536039890263161485789)
        ·
          refine ⟨11063451014958848685557171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29502536039890263161485789 11063451014958848685557171)
          ·
            refine ⟨16595176522438273028335757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11063451014958848685557171 16595176522438273028335757)
            ·
              refine ⟨6223191195914352385625909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16595176522438273028335757 6223191195914352385625909)
              ·
                refine ⟨583424174616970536152429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6223191195914352385625909 583424174616970536152429)
                ·
                  refine ⟨218784065481363951057161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 583424174616970536152429 218784065481363951057161)
                  ·
                    rfl

theorem cell21_958681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 5, 3].length) (baseStart_958681 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_958681 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_958681 prefixEnd_958681 := by exact prefixLift 958681
  have htrace : WordTrace (prefixWord ++ tailWord_958681) baseStart_958681 baseEnd_958681 := by
    simpa [prefixWord, tailWord_958681, baseEnd_958681] using wordTrace_append hprefix tailTrace_958681
  have hstable : (prefixWord ++ tailWord_958681).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958681).length < 2 ^ (prefixWord ++ tailWord_958681).sum := by decide
  have hdescent : baseEnd_958681 < baseStart_958681 := by decide
  rcases family_descends (prefixWord ++ tailWord_958681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958771 : List Nat := [1, 1, 1, 2, 5, 1, 3, 3, 4]
def baseStart_958771 : Nat := 118140960795 + 958771 * 2 ^ 59
def prefixEnd_958771 : Nat := 4983230072969 + 3 ^ 40 * 958771 * 2
def baseEnd_958771 : Nat := 218804604707543794556977

theorem tailTrace_958771 : CollatzResearch.WordTrace tailWord_958771 prefixEnd_958771 218804604707543794556977 := by
  unfold tailWord_958771
  simp only [CollatzResearch.WordTrace]
  refine ⟨34969251209543886895500167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23312834139695924597000111 34969251209543886895500167)
  ·
    refine ⟨52453876814315830343250251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34969251209543886895500167 52453876814315830343250251)
    ·
      refine ⟨78680815221473745514875377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52453876814315830343250251 78680815221473745514875377)
      ·
        refine ⟨59010611416105309136156533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78680815221473745514875377 59010611416105309136156533)
        ·
          refine ⟨5532244820259872731514675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 59010611416105309136156533 5532244820259872731514675)
          ·
            refine ⟨8298367230389809097272013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5532244820259872731514675 8298367230389809097272013)
            ·
              refine ⟨3111887711396178411477005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8298367230389809097272013 3111887711396178411477005)
              ·
                refine ⟨1166957891773566904303877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3111887711396178411477005 1166957891773566904303877)
                ·
                  refine ⟨218804604707543794556977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1166957891773566904303877 218804604707543794556977)
                  ·
                    rfl

theorem cell21_958771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 3, 4].length) (baseStart_958771 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_958771 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_958771 prefixEnd_958771 := by exact prefixLift 958771
  have htrace : WordTrace (prefixWord ++ tailWord_958771) baseStart_958771 baseEnd_958771 := by
    simpa [prefixWord, tailWord_958771, baseEnd_958771] using wordTrace_append hprefix tailTrace_958771
  have hstable : (prefixWord ++ tailWord_958771).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958771).length < 2 ^ (prefixWord ++ tailWord_958771).sum := by decide
  have hdescent : baseEnd_958771 < baseStart_958771 := by decide
  rcases family_descends (prefixWord ++ tailWord_958771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958799 : List Nat := [1, 1, 2, 1, 1, 2, 1, 3, 9]
def baseStart_958799 : Nat := 118140960795 + 958799 * 2 ^ 59
def prefixEnd_958799 : Nat := 4983230072969 + 3 ^ 40 * 958799 * 2
def baseEnd_958799 : Nat := 218810994689021968090253

theorem tailTrace_958799 : CollatzResearch.WordTrace tailWord_958799 prefixEnd_958799 218810994689021968090253 := by
  unfold tailWord_958799
  simp only [CollatzResearch.WordTrace]
  refine ⟨34970272453442447677519451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23313514968961631785012967 34970272453442447677519451)
  ·
    refine ⟨52455408680163671516279177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34970272453442447677519451 52455408680163671516279177)
    ·
      refine ⟨39341556510122753637209383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52455408680163671516279177 39341556510122753637209383)
      ·
        refine ⟨59012334765184130455814075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39341556510122753637209383 59012334765184130455814075)
        ·
          refine ⟨88518502147776195683721113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59012334765184130455814075 88518502147776195683721113)
          ·
            refine ⟨66388876610832146762790835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88518502147776195683721113 66388876610832146762790835)
            ·
              refine ⟨99583314916248220144186253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66388876610832146762790835 99583314916248220144186253)
              ·
                refine ⟨37343743093593082554069845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99583314916248220144186253 37343743093593082554069845)
                ·
                  refine ⟨218810994689021968090253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 37343743093593082554069845 218810994689021968090253)
                  ·
                    rfl

theorem cell21_958799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 9].length) (baseStart_958799 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_958799 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_958799 prefixEnd_958799 := by exact prefixLift 958799
  have htrace : WordTrace (prefixWord ++ tailWord_958799) baseStart_958799 baseEnd_958799 := by
    simpa [prefixWord, tailWord_958799, baseEnd_958799] using wordTrace_append hprefix tailTrace_958799
  have hstable : (prefixWord ++ tailWord_958799).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958799).length < 2 ^ (prefixWord ++ tailWord_958799).sum := by decide
  have hdescent : baseEnd_958799 < baseStart_958799 := by decide
  rcases family_descends (prefixWord ++ tailWord_958799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958937 : List Nat := [1, 2, 1, 2, 4, 1, 4, 6]
def baseStart_958937 : Nat := 118140960795 + 958937 * 2 ^ 59
def prefixEnd_958937 : Nat := 4983230072969 + 3 ^ 40 * 958937 * 2
def baseEnd_958937 : Nat := 72947496056388131596657

theorem tailTrace_958937 : CollatzResearch.WordTrace tailWord_958937 prefixEnd_958937 72947496056388131596657 := by
  unfold tailWord_958937
  simp only [CollatzResearch.WordTrace]
  refine ⟨34975305726942497246043065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23316870484628331497362043 34975305726942497246043065)
  ·
    refine ⟨26231479295206872934532299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34975305726942497246043065 26231479295206872934532299)
    ·
      refine ⟨39347218942810309401798449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26231479295206872934532299 39347218942810309401798449)
      ·
        refine ⟨29510414207107732051348837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39347218942810309401798449 29510414207107732051348837)
        ·
          refine ⟨5533202663832699759627907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29510414207107732051348837 5533202663832699759627907)
          ·
            refine ⟨8299803995749049639441861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5533202663832699759627907 8299803995749049639441861)
            ·
              refine ⟨1556213249202946807395349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8299803995749049639441861 1556213249202946807395349)
              ·
                refine ⟨72947496056388131596657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1556213249202946807395349 72947496056388131596657)
                ·
                  rfl

theorem cell21_958937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 4, 6].length) (baseStart_958937 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_958937 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_958937 prefixEnd_958937 := by exact prefixLift 958937
  have htrace : WordTrace (prefixWord ++ tailWord_958937) baseStart_958937 baseEnd_958937 := by
    simpa [prefixWord, tailWord_958937, baseEnd_958937] using wordTrace_append hprefix tailTrace_958937
  have hstable : (prefixWord ++ tailWord_958937).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958937).length < 2 ^ (prefixWord ++ tailWord_958937).sum := by decide
  have hdescent : baseEnd_958937 < baseStart_958937 := by decide
  rcases family_descends (prefixWord ++ tailWord_958937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959027 : List Nat := [1, 1, 1, 2, 4, 2, 1, 2, 7]
def baseStart_959027 : Nat := 118140960795 + 959027 * 2 ^ 59
def prefixEnd_959027 : Nat := 4983230072969 + 3 ^ 40 * 959027 * 2
def baseEnd_959027 : Nat := 218863027395344238289787

theorem tailTrace_959027 : CollatzResearch.WordTrace tailWord_959027 prefixEnd_959027 218863027395344238289787 := by
  unfold tailWord_959027
  simp only [CollatzResearch.WordTrace]
  refine ⟨34978588296616442616819335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23319058864410961744546223 34978588296616442616819335)
  ·
    refine ⟨52467882444924663925229003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34978588296616442616819335 52467882444924663925229003)
    ·
      refine ⟨78701823667386995887843505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52467882444924663925229003 78701823667386995887843505)
      ·
        refine ⟨59026367750540246915882629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78701823667386995887843505 59026367750540246915882629)
        ·
          refine ⟨11067443953226296296727993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59026367750540246915882629 11067443953226296296727993)
          ·
            refine ⟨8300582964919722222545995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11067443953226296296727993 8300582964919722222545995)
            ·
              refine ⟨12450874447379583333818993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8300582964919722222545995 12450874447379583333818993)
              ·
                refine ⟨9338155835534687500364245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12450874447379583333818993 9338155835534687500364245)
                ·
                  refine ⟨218863027395344238289787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9338155835534687500364245 218863027395344238289787)
                  ·
                    rfl

theorem cell21_959027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 2, 7].length) (baseStart_959027 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_959027 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_959027 prefixEnd_959027 := by exact prefixLift 959027
  have htrace : WordTrace (prefixWord ++ tailWord_959027) baseStart_959027 baseEnd_959027 := by
    simpa [prefixWord, tailWord_959027, baseEnd_959027] using wordTrace_append hprefix tailTrace_959027
  have hstable : (prefixWord ++ tailWord_959027).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959027).length < 2 ^ (prefixWord ++ tailWord_959027).sum := by decide
  have hdescent : baseEnd_959027 < baseStart_959027 := by decide
  rcases family_descends (prefixWord ++ tailWord_959027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959030 : List Nat := [5, 1, 2, 1, 2, 2, 8]
def baseStart_959030 : Nat := 118140960795 + 959030 * 2 ^ 59
def prefixEnd_959030 : Nat := 4983230072969 + 3 ^ 40 * 959030 * 2
def baseEnd_959030 : Nat := 24318190226246322193309

theorem tailTrace_959030 : CollatzResearch.WordTrace tailWord_959030 prefixEnd_959030 24318190226246322193309 := by
  unfold tailWord_959030
  simp only [CollatzResearch.WordTrace]
  refine ⟨2186168607225348383073659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23319131810403716086119029 2186168607225348383073659)
  ·
    refine ⟨3279252910838022574610489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2186168607225348383073659 3279252910838022574610489)
    ·
      refine ⟨2459439683128516930957867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3279252910838022574610489 2459439683128516930957867)
      ·
        refine ⟨3689159524692775396436801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2459439683128516930957867 3689159524692775396436801)
        ·
          refine ⟨2766869643519581547327601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3689159524692775396436801 2766869643519581547327601)
          ·
            refine ⟨2075152232639686160495701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2766869643519581547327601 2075152232639686160495701)
            ·
              refine ⟨24318190226246322193309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2075152232639686160495701 24318190226246322193309)
              ·
                rfl

theorem cell21_959030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 8].length) (baseStart_959030 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_959030 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_959030 prefixEnd_959030 := by exact prefixLift 959030
  have htrace : WordTrace (prefixWord ++ tailWord_959030) baseStart_959030 baseEnd_959030 := by
    simpa [prefixWord, tailWord_959030, baseEnd_959030] using wordTrace_append hprefix tailTrace_959030
  have hstable : (prefixWord ++ tailWord_959030).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959030).length < 2 ^ (prefixWord ++ tailWord_959030).sum := by decide
  have hdescent : baseEnd_959030 < baseStart_959030 := by decide
  rcases family_descends (prefixWord ++ tailWord_959030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959070 : List Nat := [4, 4, 1, 2, 2, 1, 1, 3, 3]
def baseStart_959070 : Nat := 118140960795 + 959070 * 2 ^ 59
def prefixEnd_959070 : Nat := 4983230072969 + 3 ^ 40 * 959070 * 2
def baseEnd_959070 : Nat := 218872840581185719073033

theorem tailTrace_959070 : CollatzResearch.WordTrace tailWord_959070 prefixEnd_959070 218872840581185719073033 := by
  unfold tailWord_959070
  simp only [CollatzResearch.WordTrace]
  refine ⟨4372519579432582620079333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23320104423640440640423109 4372519579432582620079333)
  ·
    refine ⟨819847421143609241264875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4372519579432582620079333 819847421143609241264875)
    ·
      refine ⟨1229771131715413861897313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 819847421143609241264875 1229771131715413861897313)
      ·
        refine ⟨922328348786560396422985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1229771131715413861897313 922328348786560396422985)
        ·
          refine ⟨691746261589920297317239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 922328348786560396422985 691746261589920297317239)
          ·
            refine ⟨1037619392384880445975859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 691746261589920297317239 1037619392384880445975859)
            ·
              refine ⟨1556429088577320668963789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1037619392384880445975859 1556429088577320668963789)
              ·
                refine ⟨583660908216495250861421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1556429088577320668963789 583660908216495250861421)
                ·
                  refine ⟨218872840581185719073033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 583660908216495250861421 218872840581185719073033)
                  ·
                    rfl

theorem cell21_959070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_959070 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_959070 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_959070 prefixEnd_959070 := by exact prefixLift 959070
  have htrace : WordTrace (prefixWord ++ tailWord_959070) baseStart_959070 baseEnd_959070 := by
    simpa [prefixWord, tailWord_959070, baseEnd_959070] using wordTrace_append hprefix tailTrace_959070
  have hstable : (prefixWord ++ tailWord_959070).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959070).length < 2 ^ (prefixWord ++ tailWord_959070).sum := by decide
  have hdescent : baseEnd_959070 < baseStart_959070 := by decide
  rcases family_descends (prefixWord ++ tailWord_959070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959103 : List Nat := [1, 1, 2, 2, 1, 1, 1, 7, 5]
def baseStart_959103 : Nat := 118140960795 + 959103 * 2 ^ 59
def prefixEnd_959103 : Nat := 4983230072969 + 3 ^ 40 * 959103 * 2
def baseEnd_959103 : Nat := 218880371630784995022965

theorem tailTrace_959103 : CollatzResearch.WordTrace tailWord_959103 prefixEnd_959103 218880371630784995022965 := by
  unfold tailWord_959103
  simp only [CollatzResearch.WordTrace]
  refine ⟨34981360244341107596585963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23320906829560738397723975 34981360244341107596585963)
  ·
    refine ⟨52472040366511661394878945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34981360244341107596585963 52472040366511661394878945)
    ·
      refine ⟨39354030274883746046159209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52472040366511661394878945 39354030274883746046159209)
      ·
        refine ⟨29515522706162809534619407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39354030274883746046159209 29515522706162809534619407)
        ·
          refine ⟨44273284059244214301929111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29515522706162809534619407 44273284059244214301929111)
          ·
            refine ⟨66409926088866321452893667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44273284059244214301929111 66409926088866321452893667)
            ·
              refine ⟨99614889133299482179340501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66409926088866321452893667 99614889133299482179340501)
              ·
                refine ⟨2334723964061706613578293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 99614889133299482179340501 2334723964061706613578293)
                ·
                  refine ⟨218880371630784995022965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2334723964061706613578293 218880371630784995022965)
                  ·
                    rfl

theorem cell21_959103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 7, 5].length) (baseStart_959103 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_959103 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_959103 prefixEnd_959103 := by exact prefixLift 959103
  have htrace : WordTrace (prefixWord ++ tailWord_959103) baseStart_959103 baseEnd_959103 := by
    simpa [prefixWord, tailWord_959103, baseEnd_959103] using wordTrace_append hprefix tailTrace_959103
  have hstable : (prefixWord ++ tailWord_959103).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959103).length < 2 ^ (prefixWord ++ tailWord_959103).sum := by decide
  have hdescent : baseEnd_959103 < baseStart_959103 := by decide
  rcases family_descends (prefixWord ++ tailWord_959103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959151 : List Nat := [1, 1, 2, 1, 2, 6, 2, 2, 4]
def baseStart_959151 : Nat := 118140960795 + 959151 * 2 ^ 59
def prefixEnd_959151 : Nat := 4983230072969 + 3 ^ 40 * 959151 * 2
def baseEnd_959151 : Nat := 218891325884747578222867

theorem tailTrace_959151 : CollatzResearch.WordTrace tailWord_959151 prefixEnd_959151 218891325884747578222867 := by
  unfold tailWord_959151
  simp only [CollatzResearch.WordTrace]
  refine ⟨34983110948167211794333307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23322073965444807862888871 34983110948167211794333307)
  ·
    refine ⟨52474666422250817691499961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34983110948167211794333307 52474666422250817691499961)
    ·
      refine ⟨39355999816688113268624971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52474666422250817691499961 39355999816688113268624971)
      ·
        refine ⟨59033999725032169902937457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39355999816688113268624971 59033999725032169902937457)
        ·
          refine ⟨44275499793774127427203093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59033999725032169902937457 44275499793774127427203093)
          ·
            refine ⟨2075414052833162223150145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 44275499793774127427203093 2075414052833162223150145)
            ·
              refine ⟨1556560539624871667362609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2075414052833162223150145 1556560539624871667362609)
              ·
                refine ⟨1167420404718653750521957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1556560539624871667362609 1167420404718653750521957)
                ·
                  refine ⟨218891325884747578222867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1167420404718653750521957 218891325884747578222867)
                  ·
                    rfl

theorem cell21_959151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 2, 2, 4].length) (baseStart_959151 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_959151 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_959151 prefixEnd_959151 := by exact prefixLift 959151
  have htrace : WordTrace (prefixWord ++ tailWord_959151) baseStart_959151 baseEnd_959151 := by
    simpa [prefixWord, tailWord_959151, baseEnd_959151] using wordTrace_append hprefix tailTrace_959151
  have hstable : (prefixWord ++ tailWord_959151).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959151).length < 2 ^ (prefixWord ++ tailWord_959151).sum := by decide
  have hdescent : baseEnd_959151 < baseStart_959151 := by decide
  rcases family_descends (prefixWord ++ tailWord_959151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959165 : List Nat := [1, 4, 1, 2, 1, 3, 3, 6]
def baseStart_959165 : Nat := 118140960795 + 959165 * 2 ^ 59
def prefixEnd_959165 : Nat := 4983230072969 + 3 ^ 40 * 959165 * 2
def baseEnd_959165 : Nat := 72964840291828888329835

theorem tailTrace_959165 : CollatzResearch.WordTrace tailWord_959165 prefixEnd_959165 72964840291828888329835 := by
  unfold tailWord_959165
  simp only [CollatzResearch.WordTrace]
  refine ⟨34983621570116492185342949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23322414380077661456895299 34983621570116492185342949)
  ·
    refine ⟨6559429044396842284751803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34983621570116492185342949 6559429044396842284751803)
    ·
      refine ⟨9839143566595263427127705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6559429044396842284751803 9839143566595263427127705)
      ·
        refine ⟨7379357674946447570345779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9839143566595263427127705 7379357674946447570345779)
        ·
          refine ⟨11069036512419671355518669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7379357674946447570345779 11069036512419671355518669)
          ·
            refine ⟨4150888692157376758319501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11069036512419671355518669 4150888692157376758319501)
            ·
              refine ⟨1556583259559016284369813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4150888692157376758319501 1556583259559016284369813)
              ·
                refine ⟨72964840291828888329835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1556583259559016284369813 72964840291828888329835)
                ·
                  rfl

theorem cell21_959165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 3, 6].length) (baseStart_959165 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_959165 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_959165 prefixEnd_959165 := by exact prefixLift 959165
  have htrace : WordTrace (prefixWord ++ tailWord_959165) baseStart_959165 baseEnd_959165 := by
    simpa [prefixWord, tailWord_959165, baseEnd_959165] using wordTrace_append hprefix tailTrace_959165
  have hstable : (prefixWord ++ tailWord_959165).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959165).length < 2 ^ (prefixWord ++ tailWord_959165).sum := by decide
  have hdescent : baseEnd_959165 < baseStart_959165 := by decide
  rcases family_descends (prefixWord ++ tailWord_959165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959182 : List Nat := [4, 1, 1, 1, 3, 3, 3, 5]
def baseStart_959182 : Nat := 118140960795 + 959182 * 2 ^ 59
def prefixEnd_959182 : Nat := 4983230072969 + 3 ^ 40 * 959182 * 2
def baseEnd_959182 : Nat := 72966133502366137735379

theorem tailTrace_959182 : CollatzResearch.WordTrace tailWord_959182 prefixEnd_959182 72966133502366137735379 := by
  unfold tailWord_959182
  simp only [CollatzResearch.WordTrace]
  refine ⟨4373030201381863011088975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23322827740703269392474533 4373030201381863011088975)
  ·
    refine ⟨6559545302072794516633463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4373030201381863011088975 6559545302072794516633463)
    ·
      refine ⟨9839317953109191774950195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6559545302072794516633463 9839317953109191774950195)
      ·
        refine ⟨14758976929663787662425293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9839317953109191774950195 14758976929663787662425293)
        ·
          refine ⟨5534616348623920373409485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14758976929663787662425293 5534616348623920373409485)
          ·
            refine ⟨2075481130733970140028557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5534616348623920373409485 2075481130733970140028557)
            ·
              refine ⟨778305424025238802510709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2075481130733970140028557 778305424025238802510709)
              ·
                refine ⟨72966133502366137735379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 778305424025238802510709 72966133502366137735379)
                ·
                  rfl

theorem cell21_959182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 3, 5].length) (baseStart_959182 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_959182 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_959182 prefixEnd_959182 := by exact prefixLift 959182
  have htrace : WordTrace (prefixWord ++ tailWord_959182) baseStart_959182 baseEnd_959182 := by
    simpa [prefixWord, tailWord_959182, baseEnd_959182] using wordTrace_append hprefix tailTrace_959182
  have hstable : (prefixWord ++ tailWord_959182).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959182).length < 2 ^ (prefixWord ++ tailWord_959182).sum := by decide
  have hdescent : baseEnd_959182 < baseStart_959182 := by decide
  rcases family_descends (prefixWord ++ tailWord_959182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959213 : List Nat := [1, 5, 1, 2, 1, 1, 1, 6, 3]
def baseStart_959213 : Nat := 118140960795 + 959213 * 2 ^ 59
def prefixEnd_959213 : Nat := 4983230072969 + 3 ^ 40 * 959213 * 2
def baseEnd_959213 : Nat := 218905475129449248189407

theorem tailTrace_959213 : CollatzResearch.WordTrace tailWord_959213 prefixEnd_959213 218905475129449248189407 := by
  unfold tailWord_959213
  simp only [CollatzResearch.WordTrace]
  refine ⟨34985372273942596383090293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23323581515961730922060195 34985372273942596383090293)
  ·
    refine ⟨3279878650682118410914715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34985372273942596383090293 3279878650682118410914715)
    ·
      refine ⟨4919817976023177616372073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3279878650682118410914715 4919817976023177616372073)
      ·
        refine ⟨3689863482017383212279055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4919817976023177616372073 3689863482017383212279055)
        ·
          refine ⟨5534795223026074818418583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3689863482017383212279055 5534795223026074818418583)
          ·
            refine ⟨8302192834539112227627875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5534795223026074818418583 8302192834539112227627875)
            ·
              refine ⟨12453289251808668341441813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8302192834539112227627875 12453289251808668341441813)
              ·
                refine ⟨583747933678531328505085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12453289251808668341441813 583747933678531328505085)
                ·
                  refine ⟨218905475129449248189407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 583747933678531328505085 218905475129449248189407)
                  ·
                    rfl

theorem cell21_959213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 6, 3].length) (baseStart_959213 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_959213 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_959213 prefixEnd_959213 := by exact prefixLift 959213
  have htrace : WordTrace (prefixWord ++ tailWord_959213) baseStart_959213 baseEnd_959213 := by
    simpa [prefixWord, tailWord_959213, baseEnd_959213] using wordTrace_append hprefix tailTrace_959213
  have hstable : (prefixWord ++ tailWord_959213).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959213).length < 2 ^ (prefixWord ++ tailWord_959213).sum := by decide
  have hdescent : baseEnd_959213 < baseStart_959213 := by decide
  rcases family_descends (prefixWord ++ tailWord_959213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959224 : List Nat := [2, 1, 2, 1, 1, 2, 4, 8]
def baseStart_959224 : Nat := 118140960795 + 959224 * 2 ^ 59
def prefixEnd_959224 : Nat := 4983230072969 + 3 ^ 40 * 959224 * 2
def baseEnd_959224 : Nat := 72969328493105224502017

theorem tailTrace_959224 : CollatzResearch.WordTrace tailWord_959224 prefixEnd_959224 72969328493105224502017 := by
  unfold tailWord_959224
  simp only [CollatzResearch.WordTrace]
  refine ⟨17492886738451372630870363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23323848984601830174493817 17492886738451372630870363)
  ·
    refine ⟨26239330107677058946305545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17492886738451372630870363 26239330107677058946305545)
    ·
      refine ⟨19679497580757794209729159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26239330107677058946305545 19679497580757794209729159)
      ·
        refine ⟨29519246371136691314593739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19679497580757794209729159 29519246371136691314593739)
        ·
          refine ⟨44278869556705036971890609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29519246371136691314593739 44278869556705036971890609)
          ·
            refine ⟨33209152167528777728917957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44278869556705036971890609 33209152167528777728917957)
            ·
              refine ⟨6226716031411645824172117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33209152167528777728917957 6226716031411645824172117)
              ·
                refine ⟨72969328493105224502017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6226716031411645824172117 72969328493105224502017)
                ·
                  rfl

theorem cell21_959224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 8].length) (baseStart_959224 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_959224 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_959224 prefixEnd_959224 := by exact prefixLift 959224
  have htrace : WordTrace (prefixWord ++ tailWord_959224) baseStart_959224 baseEnd_959224 := by
    simpa [prefixWord, tailWord_959224, baseEnd_959224] using wordTrace_append hprefix tailTrace_959224
  have hstable : (prefixWord ++ tailWord_959224).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959224).length < 2 ^ (prefixWord ++ tailWord_959224).sum := by decide
  have hdescent : baseEnd_959224 < baseStart_959224 := by decide
  rcases family_descends (prefixWord ++ tailWord_959224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959241 : List Nat := [1, 2, 1, 1, 3, 2, 6, 5]
def baseStart_959241 : Nat := 118140960795 + 959241 * 2 ^ 59
def prefixEnd_959241 : Nat := 4983230072969 + 3 ^ 40 * 959241 * 2
def baseEnd_959241 : Nat := 72970621703642473907561

theorem tailTrace_959241 : CollatzResearch.WordTrace tailWord_959241 prefixEnd_959241 72970621703642473907561 := by
  unfold tailWord_959241
  simp only [CollatzResearch.WordTrace]
  refine ⟨34986393517841157165109577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23324262345227438110073051 34986393517841157165109577)
  ·
    refine ⟨26239795138380867873832183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34986393517841157165109577 26239795138380867873832183)
    ·
      refine ⟨39359692707571301810748275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26239795138380867873832183 39359692707571301810748275)
      ·
        refine ⟨59039539061356952716122413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39359692707571301810748275 59039539061356952716122413)
        ·
          refine ⟨22139827148008857268545905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59039539061356952716122413 22139827148008857268545905)
          ·
            refine ⟨16604870361006642951409429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22139827148008857268545905 16604870361006642951409429)
            ·
              refine ⟨778353298172186388347317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 16604870361006642951409429 778353298172186388347317)
              ·
                refine ⟨72970621703642473907561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 778353298172186388347317 72970621703642473907561)
                ·
                  rfl

theorem cell21_959241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 6, 5].length) (baseStart_959241 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_959241 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_959241 prefixEnd_959241 := by exact prefixLift 959241
  have htrace : WordTrace (prefixWord ++ tailWord_959241) baseStart_959241 baseEnd_959241 := by
    simpa [prefixWord, tailWord_959241, baseEnd_959241] using wordTrace_append hprefix tailTrace_959241
  have hstable : (prefixWord ++ tailWord_959241).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959241).length < 2 ^ (prefixWord ++ tailWord_959241).sum := by decide
  have hdescent : baseEnd_959241 < baseStart_959241 := by decide
  rcases family_descends (prefixWord ++ tailWord_959241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959365 : List Nat := [1, 3, 1, 1, 3, 4, 2, 3, 3]
def baseStart_959365 : Nat := 118140960795 + 959365 * 2 ^ 59
def prefixEnd_959365 : Nat := 4983230072969 + 3 ^ 40 * 959365 * 2
def baseEnd_959365 : Nat := 218940163600330761655763

theorem tailTrace_959365 : CollatzResearch.WordTrace tailWord_959365 prefixEnd_959365 218940163600330761655763 := by
  unfold tailWord_959365
  simp only [CollatzResearch.WordTrace]
  refine ⟨34990916169391926342623549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23327277446261284228415699 34990916169391926342623549)
  ·
    refine ⟨13121593563521972378483831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34990916169391926342623549 13121593563521972378483831)
    ·
      refine ⟨19682390345282958567725747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13121593563521972378483831 19682390345282958567725747)
      ·
        refine ⟨29523585517924437851588621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19682390345282958567725747 29523585517924437851588621)
        ·
          refine ⟨11071344569221664194345733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29523585517924437851588621 11071344569221664194345733)
          ·
            refine ⟨2075877106729062036439825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11071344569221664194345733 2075877106729062036439825)
            ·
              refine ⟨1556907830046796527329869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2075877106729062036439825 1556907830046796527329869)
              ·
                refine ⟨583840436267548697748701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1556907830046796527329869 583840436267548697748701)
                ·
                  refine ⟨218940163600330761655763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 583840436267548697748701 218940163600330761655763)
                  ·
                    rfl

theorem cell21_959365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 2, 3, 3].length) (baseStart_959365 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_959365 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_959365 prefixEnd_959365 := by exact prefixLift 959365
  have htrace : WordTrace (prefixWord ++ tailWord_959365) baseStart_959365 baseEnd_959365 := by
    simpa [prefixWord, tailWord_959365, baseEnd_959365] using wordTrace_append hprefix tailTrace_959365
  have hstable : (prefixWord ++ tailWord_959365).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959365).length < 2 ^ (prefixWord ++ tailWord_959365).sum := by decide
  have hdescent : baseEnd_959365 < baseStart_959365 := by decide
  rcases family_descends (prefixWord ++ tailWord_959365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959382 : List Nat := [5, 3, 1, 1, 1, 1, 1, 3, 5]
def baseStart_959382 : Nat := 118140960795 + 959382 * 2 ^ 59
def prefixEnd_959382 : Nat := 4983230072969 + 3 ^ 40 * 959382 * 2
def baseEnd_959382 : Nat := 218944043231942509872395

theorem tailTrace_959382 : CollatzResearch.WordTrace tailWord_959382 prefixEnd_959382 218944043231942509872395 := by
  unfold tailWord_959382
  simp only [CollatzResearch.WordTrace]
  refine ⟨2186971013145646140374525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23327690806886892163994933 2186971013145646140374525)
  ·
    refine ⟨820114129929617302640447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2186971013145646140374525 820114129929617302640447)
    ·
      refine ⟨1230171194894425953960671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 820114129929617302640447 1230171194894425953960671)
      ·
        refine ⟨1845256792341638930941007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1230171194894425953960671 1845256792341638930941007)
        ·
          refine ⟨2767885188512458396411511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1845256792341638930941007 2767885188512458396411511)
          ·
            refine ⟨4151827782768687594617267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2767885188512458396411511 4151827782768687594617267)
            ·
              refine ⟨6227741674153031391925901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4151827782768687594617267 6227741674153031391925901)
              ·
                refine ⟨2335403127807386771972213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6227741674153031391925901 2335403127807386771972213)
                ·
                  refine ⟨218944043231942509872395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2335403127807386771972213 218944043231942509872395)
                  ·
                    rfl

theorem cell21_959382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_959382 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_959382 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_959382 prefixEnd_959382 := by exact prefixLift 959382
  have htrace : WordTrace (prefixWord ++ tailWord_959382) baseStart_959382 baseEnd_959382 := by
    simpa [prefixWord, tailWord_959382, baseEnd_959382] using wordTrace_append hprefix tailTrace_959382
  have hstable : (prefixWord ++ tailWord_959382).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959382).length < 2 ^ (prefixWord ++ tailWord_959382).sum := by decide
  have hdescent : baseEnd_959382 < baseStart_959382 := by decide
  rcases family_descends (prefixWord ++ tailWord_959382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959438 : List Nat := [4, 1, 1, 1, 2, 3, 2, 1, 6]
def baseStart_959438 : Nat := 118140960795 + 959438 * 2 ^ 59
def prefixEnd_959438 : Nat := 4983230072969 + 3 ^ 40 * 959438 * 2
def baseEnd_959438 : Nat := 218956823194898856938947

theorem tailTrace_959438 : CollatzResearch.WordTrace tailWord_959438 prefixEnd_959438 218956823194898856938947 := by
  unfold tailWord_959438
  simp only [CollatzResearch.WordTrace]
  refine ⟨4374197337265932476253871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23329052465418306540020645 4374197337265932476253871)
  ·
    refine ⟨6561296005898898714380807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4374197337265932476253871 6561296005898898714380807)
    ·
      refine ⟨9841944008848348071571211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6561296005898898714380807 9841944008848348071571211)
      ·
        refine ⟨14762916013272522107356817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9841944008848348071571211 14762916013272522107356817)
        ·
          refine ⟨11072187009954391580517613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14762916013272522107356817 11072187009954391580517613)
          ·
            refine ⟨4152070128732896842694105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11072187009954391580517613 4152070128732896842694105)
            ·
              refine ⟨3114052596549672632020579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4152070128732896842694105 3114052596549672632020579)
              ·
                refine ⟨4671078894824508948030869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3114052596549672632020579 4671078894824508948030869)
                ·
                  refine ⟨218956823194898856938947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4671078894824508948030869 218956823194898856938947)
                  ·
                    rfl

theorem cell21_959438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 1, 6].length) (baseStart_959438 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_959438 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_959438 prefixEnd_959438 := by exact prefixLift 959438
  have htrace : WordTrace (prefixWord ++ tailWord_959438) baseStart_959438 baseEnd_959438 := by
    simpa [prefixWord, tailWord_959438, baseEnd_959438] using wordTrace_append hprefix tailTrace_959438
  have hstable : (prefixWord ++ tailWord_959438).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959438).length < 2 ^ (prefixWord ++ tailWord_959438).sum := by decide
  have hdescent : baseEnd_959438 < baseStart_959438 := by decide
  rcases family_descends (prefixWord ++ tailWord_959438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959441 : List Nat := [1, 2, 2, 1, 2, 1, 7, 2, 3]
def baseStart_959441 : Nat := 118140960795 + 959441 * 2 ^ 59
def prefixEnd_959441 : Nat := 4983230072969 + 3 ^ 40 * 959441 * 2
def baseEnd_959441 : Nat := 218957507835771518388941

theorem tailTrace_959441 : CollatzResearch.WordTrace tailWord_959441 prefixEnd_959441 218957507835771518388941 := by
  unfold tailWord_959441
  simp only [CollatzResearch.WordTrace]
  refine ⟨34993688117116591322390177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23329125411411060881593451 34993688117116591322390177)
  ·
    refine ⟨26245266087837443491792633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34993688117116591322390177 26245266087837443491792633)
    ·
      refine ⟨19683949565878082618844475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26245266087837443491792633 19683949565878082618844475)
      ·
        refine ⟨29525924348817123928266713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19683949565878082618844475 29525924348817123928266713)
        ·
          refine ⟨22144443261612842946200035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29525924348817123928266713 22144443261612842946200035)
          ·
            refine ⟨33216664892419264419300053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22144443261612842946200035 33216664892419264419300053)
            ·
              refine ⟨778515583416076509827345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 33216664892419264419300053 778515583416076509827345)
              ·
                refine ⟨583886687562057382370509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 778515583416076509827345 583886687562057382370509)
                ·
                  refine ⟨218957507835771518388941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 583886687562057382370509 218957507835771518388941)
                  ·
                    rfl

theorem cell21_959441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 7, 2, 3].length) (baseStart_959441 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_959441 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_959441 prefixEnd_959441 := by exact prefixLift 959441
  have htrace : WordTrace (prefixWord ++ tailWord_959441) baseStart_959441 baseEnd_959441 := by
    simpa [prefixWord, tailWord_959441, baseEnd_959441] using wordTrace_append hprefix tailTrace_959441
  have hstable : (prefixWord ++ tailWord_959441).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959441).length < 2 ^ (prefixWord ++ tailWord_959441).sum := by decide
  have hdescent : baseEnd_959441 < baseStart_959441 := by decide
  rcases family_descends (prefixWord ++ tailWord_959441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959455 : List Nat := [1, 1, 2, 3, 5, 1, 1, 3, 4]
def baseStart_959455 : Nat := 118140960795 + 959455 * 2 ^ 59
def prefixEnd_959455 : Nat := 4983230072969 + 3 ^ 40 * 959455 * 2
def baseEnd_959455 : Nat := 218960702826510605155579

theorem tailTrace_959455 : CollatzResearch.WordTrace tailWord_959455 prefixEnd_959455 218960702826510605155579 := by
  unfold tailWord_959455
  simp only [CollatzResearch.WordTrace]
  refine ⟨34994198739065871713399819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23329465826043914475599879 34994198739065871713399819)
  ·
    refine ⟨52491298108598807570099729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34994198739065871713399819 52491298108598807570099729)
    ·
      refine ⟨39368473581449105677574797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52491298108598807570099729 39368473581449105677574797)
      ·
        refine ⟨14763177593043414629090549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39368473581449105677574797 14763177593043414629090549)
        ·
          refine ⟨1384047899347820121477239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14763177593043414629090549 1384047899347820121477239)
          ·
            refine ⟨2076071849021730182215859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1384047899347820121477239 2076071849021730182215859)
            ·
              refine ⟨3114107773532595273323789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2076071849021730182215859 3114107773532595273323789)
              ·
                refine ⟨1167790415074723227496421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3114107773532595273323789 1167790415074723227496421)
                ·
                  refine ⟨218960702826510605155579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1167790415074723227496421 218960702826510605155579)
                  ·
                    rfl

theorem cell21_959455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 3, 4].length) (baseStart_959455 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_959455 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_959455 prefixEnd_959455 := by exact prefixLift 959455
  have htrace : WordTrace (prefixWord ++ tailWord_959455) baseStart_959455 baseEnd_959455 := by
    simpa [prefixWord, tailWord_959455, baseEnd_959455] using wordTrace_append hprefix tailTrace_959455
  have hstable : (prefixWord ++ tailWord_959455).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959455).length < 2 ^ (prefixWord ++ tailWord_959455).sum := by decide
  have hdescent : baseEnd_959455 < baseStart_959455 := by decide
  rcases family_descends (prefixWord ++ tailWord_959455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959486 : List Nat := [4, 2, 2, 2, 3, 8]
def baseStart_959486 : Nat := 118140960795 + 959486 * 2 ^ 59
def prefixEnd_959486 : Nat := 4983230072969 + 3 ^ 40 * 959486 * 2
def baseEnd_959486 : Nat := 8109917683291164449587

theorem tailTrace_959486 : CollatzResearch.WordTrace tailWord_959486 prefixEnd_959486 8109917683291164449587 := by
  unfold tailWord_959486
  simp only [CollatzResearch.WordTrace]
  refine ⟨4374416175244195500972289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23330219601302376005185541 4374416175244195500972289)
  ·
    refine ⟨3280812131433146625729217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4374416175244195500972289 3280812131433146625729217)
    ·
      refine ⟨2460609098574859969296913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3280812131433146625729217 2460609098574859969296913)
      ·
        refine ⟨1845456823931144976972685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2460609098574859969296913 1845456823931144976972685)
        ·
          refine ⟨692046308974179366364757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1845456823931144976972685 692046308974179366364757)
          ·
            refine ⟨8109917683291164449587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 692046308974179366364757 8109917683291164449587)
            ·
              rfl

theorem cell21_959486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 8].length) (baseStart_959486 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_959486 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_959486 prefixEnd_959486 := by exact prefixLift 959486
  have htrace : WordTrace (prefixWord ++ tailWord_959486) baseStart_959486 baseEnd_959486 := by
    simpa [prefixWord, tailWord_959486, baseEnd_959486] using wordTrace_append hprefix tailTrace_959486
  have hstable : (prefixWord ++ tailWord_959486).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959486).length < 2 ^ (prefixWord ++ tailWord_959486).sum := by decide
  have hdescent : baseEnd_959486 < baseStart_959486 := by decide
  rcases family_descends (prefixWord ++ tailWord_959486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959497 : List Nat := [1, 2, 1, 1, 3, 1, 1, 5, 6]
def baseStart_959497 : Nat := 118140960795 + 959497 * 2 ^ 59
def prefixEnd_959497 : Nat := 4983230072969 + 3 ^ 40 * 959497 * 2
def baseEnd_959497 : Nat := 218970287798727865455493

theorem tailTrace_959497 : CollatzResearch.WordTrace tailWord_959497 prefixEnd_959497 218970287798727865455493 := by
  unfold tailWord_959497
  simp only [CollatzResearch.WordTrace]
  refine ⟨34995730604913712886428745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23330487069942475257619163 34995730604913712886428745)
  ·
    refine ⟨26246797953685284664821559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34995730604913712886428745 26246797953685284664821559)
    ·
      refine ⟨39370196930527926997232339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26246797953685284664821559 39370196930527926997232339)
      ·
        refine ⟨59055295395791890495848509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39370196930527926997232339 59055295395791890495848509)
        ·
          refine ⟨22145735773421958935943191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59055295395791890495848509 22145735773421958935943191)
          ·
            refine ⟨33218603660132938403914787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22145735773421958935943191 33218603660132938403914787)
            ·
              refine ⟨49827905490199407605872181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33218603660132938403914787 49827905490199407605872181)
              ·
                refine ⟨4671366139706194463050517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49827905490199407605872181 4671366139706194463050517)
                ·
                  refine ⟨218970287798727865455493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4671366139706194463050517 218970287798727865455493)
                  ·
                    rfl

theorem cell21_959497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 5, 6].length) (baseStart_959497 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_959497 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_959497 prefixEnd_959497 := by exact prefixLift 959497
  have htrace : WordTrace (prefixWord ++ tailWord_959497) baseStart_959497 baseEnd_959497 := by
    simpa [prefixWord, tailWord_959497, baseEnd_959497] using wordTrace_append hprefix tailTrace_959497
  have hstable : (prefixWord ++ tailWord_959497).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959497).length < 2 ^ (prefixWord ++ tailWord_959497).sum := by decide
  have hdescent : baseEnd_959497 < baseStart_959497 := by decide
  rcases family_descends (prefixWord ++ tailWord_959497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959514 : List Nat := [3, 1, 1, 3, 1, 2, 1, 5, 4]
def baseStart_959514 : Nat := 118140960795 + 959514 * 2 ^ 59
def prefixEnd_959514 : Nat := 4983230072969 + 3 ^ 40 * 959514 * 2
def baseEnd_959514 : Nat := 218974167430339613672125

theorem tailTrace_959514 : CollatzResearch.WordTrace tailWord_959514 prefixEnd_959514 218974167430339613672125 := by
  unfold tailWord_959514
  simp only [CollatzResearch.WordTrace]
  refine ⟨8749087661463031197449399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23330900430568083193198397 8749087661463031197449399)
  ·
    refine ⟨13123631492194546796174099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8749087661463031197449399 13123631492194546796174099)
    ·
      refine ⟨19685447238291820194261149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13123631492194546796174099 19685447238291820194261149)
      ·
        refine ⟨7382042714359432572847931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19685447238291820194261149 7382042714359432572847931)
        ·
          refine ⟨11073064071539148859271897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7382042714359432572847931 11073064071539148859271897)
          ·
            refine ⟨8304798053654361644453923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11073064071539148859271897 8304798053654361644453923)
            ·
              refine ⟨12457197080481542466680885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8304798053654361644453923 12457197080481542466680885)
              ·
                refine ⟨1167862226295144606251333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12457197080481542466680885 1167862226295144606251333)
                ·
                  refine ⟨218974167430339613672125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1167862226295144606251333 218974167430339613672125)
                  ·
                    rfl

theorem cell21_959514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 5, 4].length) (baseStart_959514 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_959514 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_959514 prefixEnd_959514 := by exact prefixLift 959514
  have htrace : WordTrace (prefixWord ++ tailWord_959514) baseStart_959514 baseEnd_959514 := by
    simpa [prefixWord, tailWord_959514, baseEnd_959514] using wordTrace_append hprefix tailTrace_959514
  have hstable : (prefixWord ++ tailWord_959514).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959514).length < 2 ^ (prefixWord ++ tailWord_959514).sum := by decide
  have hdescent : baseEnd_959514 < baseStart_959514 := by decide
  rcases family_descends (prefixWord ++ tailWord_959514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959559 : List Nat := [1, 1, 4, 1, 3, 2, 1, 3, 5]
def baseStart_959559 : Nat := 118140960795 + 959559 * 2 ^ 59
def prefixEnd_959559 : Nat := 4983230072969 + 3 ^ 40 * 959559 * 2
def baseEnd_959559 : Nat := 218984437043429535422033

theorem tailTrace_959559 : CollatzResearch.WordTrace tailWord_959559 prefixEnd_959559 218984437043429535422033 := by
  unfold tailWord_959559
  simp only [CollatzResearch.WordTrace]
  refine ⟨34997991930689097475185731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23331994620459398316790487 34997991930689097475185731)
  ·
    refine ⟨52496987896033646212778597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34997991930689097475185731 52496987896033646212778597)
    ·
      refine ⟨9843185230506308664895987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52496987896033646212778597 9843185230506308664895987)
      ·
        refine ⟨14764777845759462997343981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9843185230506308664895987 14764777845759462997343981)
        ·
          refine ⟨5536791692159798624003993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14764777845759462997343981 5536791692159798624003993)
          ·
            refine ⟨4152593769119848968002995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5536791692159798624003993 4152593769119848968002995)
            ·
              refine ⟨6228890653679773452004493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4152593769119848968002995 6228890653679773452004493)
              ·
                refine ⟨2335833995129915044501685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6228890653679773452004493 2335833995129915044501685)
                ·
                  refine ⟨218984437043429535422033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2335833995129915044501685 218984437043429535422033)
                  ·
                    rfl

theorem cell21_959559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 3, 5].length) (baseStart_959559 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_959559 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_959559 prefixEnd_959559 := by exact prefixLift 959559
  have htrace : WordTrace (prefixWord ++ tailWord_959559) baseStart_959559 baseEnd_959559 := by
    simpa [prefixWord, tailWord_959559, baseEnd_959559] using wordTrace_append hprefix tailTrace_959559
  have hstable : (prefixWord ++ tailWord_959559).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959559).length < 2 ^ (prefixWord ++ tailWord_959559).sum := by decide
  have hdescent : baseEnd_959559 < baseStart_959559 := by decide
  rcases family_descends (prefixWord ++ tailWord_959559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959593 : List Nat := [1, 2, 1, 1, 1, 8, 1, 3, 3]
def baseStart_959593 : Nat := 118140960795 + 959593 * 2 ^ 59
def prefixEnd_959593 : Nat := 4983230072969 + 3 ^ 40 * 959593 * 2
def baseEnd_959593 : Nat := 218992196306653031855297

theorem tailTrace_959593 : CollatzResearch.WordTrace tailWord_959593 prefixEnd_959593 218992196306653031855297 := by
  unfold tailWord_959593
  simp only [CollatzResearch.WordTrace]
  refine ⟨34999232012565921281923433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23332821341710614187948955 34999232012565921281923433)
  ·
    refine ⟨26249424009424440961442575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34999232012565921281923433 26249424009424440961442575)
    ·
      refine ⟨39374136014136661442163863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26249424009424440961442575 39374136014136661442163863)
      ·
        refine ⟨59061204021204992163245795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39374136014136661442163863 59061204021204992163245795)
        ·
          refine ⟨88591806031807488244868693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59061204021204992163245795 88591806031807488244868693)
          ·
            refine ⟨1038185226935244002869555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 88591806031807488244868693 1038185226935244002869555)
            ·
              refine ⟨1557277840402866004304333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1038185226935244002869555 1557277840402866004304333)
              ·
                refine ⟨583979190151074751614125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1557277840402866004304333 583979190151074751614125)
                ·
                  refine ⟨218992196306653031855297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 583979190151074751614125 218992196306653031855297)
                  ·
                    rfl

theorem cell21_959593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 1, 3, 3].length) (baseStart_959593 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_959593 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_959593 prefixEnd_959593 := by exact prefixLift 959593
  have htrace : WordTrace (prefixWord ++ tailWord_959593) baseStart_959593 baseEnd_959593 := by
    simpa [prefixWord, tailWord_959593, baseEnd_959593] using wordTrace_append hprefix tailTrace_959593
  have hstable : (prefixWord ++ tailWord_959593).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959593).length < 2 ^ (prefixWord ++ tailWord_959593).sum := by decide
  have hdescent : baseEnd_959593 < baseStart_959593 := by decide
  rcases family_descends (prefixWord ++ tailWord_959593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959621 : List Nat := [1, 3, 1, 1, 6, 1, 2, 6]
def baseStart_959621 : Nat := 118140960795 + 959621 * 2 ^ 59
def prefixEnd_959621 : Nat := 4983230072969 + 3 ^ 40 * 959621 * 2
def baseEnd_959621 : Nat := 72999528762710401796191

theorem tailTrace_959621 : CollatzResearch.WordTrace tailWord_959621 prefixEnd_959621 72999528762710401796191 := by
  unfold tailWord_959621
  simp only [CollatzResearch.WordTrace]
  refine ⟨35000253256464482063942717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23333502170976321375961811 35000253256464482063942717)
  ·
    refine ⟨13125094971174180773978519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35000253256464482063942717 13125094971174180773978519)
    ·
      refine ⟨19687642456761271160967779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13125094971174180773978519 19687642456761271160967779)
      ·
        refine ⟨29531463685141906741451669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19687642456761271160967779 29531463685141906741451669)
        ·
          refine ⟨1384287360241026878505547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 29531463685141906741451669 1384287360241026878505547)
          ·
            refine ⟨2076431040361540317758321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1384287360241026878505547 2076431040361540317758321)
            ·
              refine ⟨1557323280271155238318741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2076431040361540317758321 1557323280271155238318741)
              ·
                refine ⟨72999528762710401796191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1557323280271155238318741 72999528762710401796191)
                ·
                  rfl

theorem cell21_959621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 2, 6].length) (baseStart_959621 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_959621 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_959621 prefixEnd_959621 := by exact prefixLift 959621
  have htrace : WordTrace (prefixWord ++ tailWord_959621) baseStart_959621 baseEnd_959621 := by
    simpa [prefixWord, tailWord_959621, baseEnd_959621] using wordTrace_append hprefix tailTrace_959621
  have hstable : (prefixWord ++ tailWord_959621).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959621).length < 2 ^ (prefixWord ++ tailWord_959621).sum := by decide
  have hdescent : baseEnd_959621 < baseStart_959621 := by decide
  rcases family_descends (prefixWord ++ tailWord_959621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959666 : List Nat := [3, 2, 1, 1, 1, 4, 1, 4, 4]
def baseStart_959666 : Nat := 118140960795 + 959666 * 2 ^ 59
def prefixEnd_959666 : Nat := 4983230072969 + 3 ^ 40 * 959666 * 2
def baseEnd_959666 : Nat := 219008855901221127138481

theorem tailTrace_959666 : CollatzResearch.WordTrace tailWord_959666 prefixEnd_959666 219008855901221127138481 := by
  unfold tailWord_959666
  simp only [CollatzResearch.WordTrace]
  refine ⟨8750473635325363687332713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23334596360867636499553901 8750473635325363687332713)
  ·
    refine ⟨6562855226494022765499535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8750473635325363687332713 6562855226494022765499535)
    ·
      refine ⟨9844282839741034148249303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6562855226494022765499535 9844282839741034148249303)
      ·
        refine ⟨14766424259611551222373955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9844282839741034148249303 14766424259611551222373955)
        ·
          refine ⟨22149636389417326833560933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14766424259611551222373955 22149636389417326833560933)
          ·
            refine ⟨4153056823015748781292675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22149636389417326833560933 4153056823015748781292675)
            ·
              refine ⟨6229585234523623171939013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4153056823015748781292675 6229585234523623171939013)
              ·
                refine ⟨1168047231473179344738565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6229585234523623171939013 1168047231473179344738565)
                ·
                  refine ⟨219008855901221127138481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1168047231473179344738565 219008855901221127138481)
                  ·
                    rfl

theorem cell21_959666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 4, 4].length) (baseStart_959666 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_959666 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_959666 prefixEnd_959666 := by exact prefixLift 959666
  have htrace : WordTrace (prefixWord ++ tailWord_959666) baseStart_959666 baseEnd_959666 := by
    simpa [prefixWord, tailWord_959666, baseEnd_959666] using wordTrace_append hprefix tailTrace_959666
  have hstable : (prefixWord ++ tailWord_959666).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959666).length < 2 ^ (prefixWord ++ tailWord_959666).sum := by decide
  have hdescent : baseEnd_959666 < baseStart_959666 := by decide
  rcases family_descends (prefixWord ++ tailWord_959666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959756 : List Nat := [2, 2, 1, 2, 2, 4, 1, 7]
def baseStart_959756 : Nat := 118140960795 + 959756 * 2 ^ 59
def prefixEnd_959756 : Nat := 4983230072969 + 3 ^ 40 * 959756 * 2
def baseEnd_959756 : Nat := 73009798375800323546099

theorem tailTrace_959756 : CollatzResearch.WordTrace tailWord_959756 prefixEnd_959756 73009798375800323546099 := by
  unfold tailWord_959756
  simp only [CollatzResearch.WordTrace]
  refine ⟨17502588555487700060053561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23336784740650266746738081 17502588555487700060053561)
  ·
    refine ⟨13126941416615775045040171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17502588555487700060053561 13126941416615775045040171)
    ·
      refine ⟨19690412124923662567560257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13126941416615775045040171 19690412124923662567560257)
      ·
        refine ⟨14767809093692746925670193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19690412124923662567560257 14767809093692746925670193)
        ·
          refine ⟨11075856820269560194252645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14767809093692746925670193 11075856820269560194252645)
          ·
            refine ⟨2076723153800542536422371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11075856820269560194252645 2076723153800542536422371)
            ·
              refine ⟨3115084730700813804633557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2076723153800542536422371 3115084730700813804633557)
              ·
                refine ⟨73009798375800323546099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3115084730700813804633557 73009798375800323546099)
                ·
                  rfl

theorem cell21_959756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 7].length) (baseStart_959756 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_959756 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_959756 prefixEnd_959756 := by exact prefixLift 959756
  have htrace : WordTrace (prefixWord ++ tailWord_959756) baseStart_959756 baseEnd_959756 := by
    simpa [prefixWord, tailWord_959756, baseEnd_959756] using wordTrace_append hprefix tailTrace_959756
  have hstable : (prefixWord ++ tailWord_959756).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959756).length < 2 ^ (prefixWord ++ tailWord_959756).sum := by decide
  have hdescent : baseEnd_959756 < baseStart_959756 := by decide
  rcases family_descends (prefixWord ++ tailWord_959756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959773 : List Nat := [1, 4, 2, 3, 1, 3, 7]
def baseStart_959773 : Nat := 118140960795 + 959773 * 2 ^ 59
def prefixEnd_959773 : Nat := 4983230072969 + 3 ^ 40 * 959773 * 2
def baseEnd_959773 : Nat := 24337030528779190983881

theorem tailTrace_959773 : CollatzResearch.WordTrace tailWord_959773 prefixEnd_959773 24337030528779190983881 := by
  unfold tailWord_959773
  simp only [CollatzResearch.WordTrace]
  refine ⟨35005797151913812023475973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23337198101275874682317315 35005797151913812023475973)
  ·
    refine ⟨6563586965983839754401745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35005797151913812023475973 6563586965983839754401745)
    ·
      refine ⟨4922690224487879815801309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6563586965983839754401745 4922690224487879815801309)
      ·
        refine ⟨1846008834182954930925491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4922690224487879815801309 1846008834182954930925491)
        ·
          refine ⟨2769013251274432396388237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1846008834182954930925491 2769013251274432396388237)
          ·
            refine ⟨1038379969227912148645589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2769013251274432396388237 1038379969227912148645589)
            ·
              refine ⟨24337030528779190983881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1038379969227912148645589 24337030528779190983881)
              ·
                rfl

theorem cell21_959773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 7].length) (baseStart_959773 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_959773 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_959773 prefixEnd_959773 := by exact prefixLift 959773
  have htrace : WordTrace (prefixWord ++ tailWord_959773) baseStart_959773 baseEnd_959773 := by
    simpa [prefixWord, tailWord_959773, baseEnd_959773] using wordTrace_append hprefix tailTrace_959773
  have hstable : (prefixWord ++ tailWord_959773).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959773).length < 2 ^ (prefixWord ++ tailWord_959773).sum := by decide
  have hdescent : baseEnd_959773 < baseStart_959773 := by decide
  rcases family_descends (prefixWord ++ tailWord_959773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959830 : List Nat := [5, 2, 3, 1, 2, 1, 2, 2, 3]
def baseStart_959830 : Nat := 118140960795 + 959830 * 2 ^ 59
def prefixEnd_959830 : Nat := 4983230072969 + 3 ^ 40 * 959830 * 2
def baseEnd_959830 : Nat := 219046282935593286404813

theorem tailTrace_959830 : CollatzResearch.WordTrace tailWord_959830 prefixEnd_959830 219046282935593286404813 := by
  unfold tailWord_959830
  simp only [CollatzResearch.WordTrace]
  refine ⟨2187992257044206922393809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23338584075138207172200629 2187992257044206922393809)
  ·
    refine ⟨1640994192783155191795357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2187992257044206922393809 1640994192783155191795357)
    ·
      refine ⟨615372822293683196923259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1640994192783155191795357 615372822293683196923259)
      ·
        refine ⟨923059233440524795384889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 615372822293683196923259 923059233440524795384889)
        ·
          refine ⟨692294425080393596538667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 923059233440524795384889 692294425080393596538667)
          ·
            refine ⟨1038441637620590394808001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 692294425080393596538667 1038441637620590394808001)
            ·
              refine ⟨778831228215442796106001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1038441637620590394808001 778831228215442796106001)
              ·
                refine ⟨584123421161582097079501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 778831228215442796106001 584123421161582097079501)
                ·
                  refine ⟨219046282935593286404813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 584123421161582097079501 219046282935593286404813)
                  ·
                    rfl

theorem cell21_959830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 2, 2, 3].length) (baseStart_959830 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_959830 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_959830 prefixEnd_959830 := by exact prefixLift 959830
  have htrace : WordTrace (prefixWord ++ tailWord_959830) baseStart_959830 baseEnd_959830 := by
    simpa [prefixWord, tailWord_959830, baseEnd_959830] using wordTrace_append hprefix tailTrace_959830
  have hstable : (prefixWord ++ tailWord_959830).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959830).length < 2 ^ (prefixWord ++ tailWord_959830).sum := by decide
  have hdescent : baseEnd_959830 < baseStart_959830 := by decide
  rcases family_descends (prefixWord ++ tailWord_959830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959880 : List Nat := [2, 1, 3, 3, 1, 2, 1, 5, 3]
def baseStart_959880 : Nat := 118140960795 + 959880 * 2 ^ 59
def prefixEnd_959880 : Nat := 4983230072969 + 3 ^ 40 * 959880 * 2
def baseEnd_959880 : Nat := 219057693616804310571377

theorem tailTrace_959880 : CollatzResearch.WordTrace tailWord_959880 prefixEnd_959880 219057693616804310571377 := by
  unfold tailWord_959880
  simp only [CollatzResearch.WordTrace]
  refine ⟨17504849881263084648810547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23339799841684112865080729 17504849881263084648810547)
  ·
    refine ⟨26257274821894626973215821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17504849881263084648810547 26257274821894626973215821)
    ·
      refine ⟨9846478058210485114955933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26257274821894626973215821 9846478058210485114955933)
      ·
        refine ⟨3692429271828931918108475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9846478058210485114955933 3692429271828931918108475)
        ·
          refine ⟨5538643907743397877162713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3692429271828931918108475 5538643907743397877162713)
          ·
            refine ⟨4153982930807548407872035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5538643907743397877162713 4153982930807548407872035)
            ·
              refine ⟨6230974396211322611808053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4153982930807548407872035 6230974396211322611808053)
              ·
                refine ⟨584153849644811494857005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6230974396211322611808053 584153849644811494857005)
                ·
                  refine ⟨219057693616804310571377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 584153849644811494857005 219057693616804310571377)
                  ·
                    rfl

theorem cell21_959880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 5, 3].length) (baseStart_959880 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_959880 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_959880 prefixEnd_959880 := by exact prefixLift 959880
  have htrace : WordTrace (prefixWord ++ tailWord_959880) baseStart_959880 baseEnd_959880 := by
    simpa [prefixWord, tailWord_959880, baseEnd_959880] using wordTrace_append hprefix tailTrace_959880
  have hstable : (prefixWord ++ tailWord_959880).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959880).length < 2 ^ (prefixWord ++ tailWord_959880).sum := by decide
  have hdescent : baseEnd_959880 < baseStart_959880 := by decide
  rcases family_descends (prefixWord ++ tailWord_959880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959911 : List Nat := [1, 1, 6, 1, 1, 1, 5, 1, 4]
def baseStart_959911 : Nat := 118140960795 + 959911 * 2 ^ 59
def prefixEnd_959911 : Nat := 4983230072969 + 3 ^ 40 * 959911 * 2
def baseEnd_959911 : Nat := 219064768239155145554647

theorem tailTrace_959911 : CollatzResearch.WordTrace tailWord_959911 prefixEnd_959911 219064768239155145554647 := by
  unfold tailWord_959911
  simp only [CollatzResearch.WordTrace]
  refine ⟨35010830425413861591999587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23340553616942574394666391 35010830425413861591999587)
  ·
    refine ⟨52516245638120792387999381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35010830425413861591999587 52516245638120792387999381)
    ·
      refine ⟨2461699014286912143187471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 52516245638120792387999381 2461699014286912143187471)
      ·
        refine ⟨3692548521430368214781207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2461699014286912143187471 3692548521430368214781207)
        ·
          refine ⟨5538822782145552322171811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3692548521430368214781207 5538822782145552322171811)
          ·
            refine ⟨8308234173218328483257717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5538822782145552322171811 8308234173218328483257717)
            ·
              refine ⟨778896953739218295305411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8308234173218328483257717 778896953739218295305411)
              ·
                refine ⟨1168345430608827442958117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 778896953739218295305411 1168345430608827442958117)
                ·
                  refine ⟨219064768239155145554647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1168345430608827442958117 219064768239155145554647)
                  ·
                    rfl

theorem cell21_959911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 5, 1, 4].length) (baseStart_959911 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_959911 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_959911 prefixEnd_959911 := by exact prefixLift 959911
  have htrace : WordTrace (prefixWord ++ tailWord_959911) baseStart_959911 baseEnd_959911 := by
    simpa [prefixWord, tailWord_959911, baseEnd_959911] using wordTrace_append hprefix tailTrace_959911
  have hstable : (prefixWord ++ tailWord_959911).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959911).length < 2 ^ (prefixWord ++ tailWord_959911).sum := by decide
  have hdescent : baseEnd_959911 < baseStart_959911 := by decide
  rcases family_descends (prefixWord ++ tailWord_959911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959922 : List Nat := [3, 2, 1, 1, 1, 1, 2, 3, 7]
def baseStart_959922 : Nat := 118140960795 + 959922 * 2 ^ 59
def prefixEnd_959922 : Nat := 4983230072969 + 3 ^ 40 * 959922 * 2
def baseEnd_959922 : Nat := 219067278589021570871291

theorem tailTrace_959922 : CollatzResearch.WordTrace tailWord_959922 prefixEnd_959922 219067278589021570871291 := by
  unfold tailWord_959922
  simp only [CollatzResearch.WordTrace]
  refine ⟨8752807907093502617662505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23340821085582673647100013 8752807907093502617662505)
  ·
    refine ⟨6564605930320126963246879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8752807907093502617662505 6564605930320126963246879)
    ·
      refine ⟨9846908895480190444870319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6564605930320126963246879 9846908895480190444870319)
      ·
        refine ⟨14770363343220285667305479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9846908895480190444870319 14770363343220285667305479)
        ·
          refine ⟨22155545014830428500958219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14770363343220285667305479 22155545014830428500958219)
          ·
            refine ⟨33233317522245642751437329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22155545014830428500958219 33233317522245642751437329)
            ·
              refine ⟨24924988141684232063577997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33233317522245642751437329 24924988141684232063577997)
              ·
                refine ⟨9346870553131587023841749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24924988141684232063577997 9346870553131587023841749)
                ·
                  refine ⟨219067278589021570871291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9346870553131587023841749 219067278589021570871291)
                  ·
                    rfl

theorem cell21_959922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 3, 7].length) (baseStart_959922 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_959922 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_959922 prefixEnd_959922 := by exact prefixLift 959922
  have htrace : WordTrace (prefixWord ++ tailWord_959922) baseStart_959922 baseEnd_959922 := by
    simpa [prefixWord, tailWord_959922, baseEnd_959922] using wordTrace_append hprefix tailTrace_959922
  have hstable : (prefixWord ++ tailWord_959922).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959922).length < 2 ^ (prefixWord ++ tailWord_959922).sum := by decide
  have hdescent : baseEnd_959922 < baseStart_959922 := by decide
  rcases family_descends (prefixWord ++ tailWord_959922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959925 : List Nat := [1, 3, 3, 2, 2, 1, 4, 5]
def baseStart_959925 : Nat := 118140960795 + 959925 * 2 ^ 59
def prefixEnd_959925 : Nat := 4983230072969 + 3 ^ 40 * 959925 * 2
def baseEnd_959925 : Nat := 73022654409964744107095

theorem tailTrace_959925 : CollatzResearch.WordTrace tailWord_959925 prefixEnd_959925 73022654409964744107095 := by
  unfold tailWord_959925
  simp only [CollatzResearch.WordTrace]
  refine ⟨35011341047363141983009229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23340894031575427988672819 35011341047363141983009229)
  ·
    refine ⟨13129252892761178243628461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35011341047363141983009229 13129252892761178243628461)
    ·
      refine ⟨4923469834785441841360673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13129252892761178243628461 4923469834785441841360673)
      ·
        refine ⟨3692602376089081381020505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4923469834785441841360673 3692602376089081381020505)
        ·
          refine ⟨2769451782066811035765379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3692602376089081381020505 2769451782066811035765379)
          ·
            refine ⟨4154177673100216553648069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2769451782066811035765379 4154177673100216553648069)
            ·
              refine ⟨778908313706290603809013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4154177673100216553648069 778908313706290603809013)
              ·
                refine ⟨73022654409964744107095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 778908313706290603809013 73022654409964744107095)
                ·
                  rfl

theorem cell21_959925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 4, 5].length) (baseStart_959925 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_959925 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_959925 prefixEnd_959925 := by exact prefixLift 959925
  have htrace : WordTrace (prefixWord ++ tailWord_959925) baseStart_959925 baseEnd_959925 := by
    simpa [prefixWord, tailWord_959925, baseEnd_959925] using wordTrace_append hprefix tailTrace_959925
  have hstable : (prefixWord ++ tailWord_959925).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959925).length < 2 ^ (prefixWord ++ tailWord_959925).sum := by decide
  have hdescent : baseEnd_959925 < baseStart_959925 := by decide
  rcases family_descends (prefixWord ++ tailWord_959925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960060 : List Nat := [2, 2, 2, 2, 4, 1, 8]
def baseStart_960060 : Nat := 118140960795 + 960060 * 2 ^ 59
def prefixEnd_960060 : Nat := 4983230072969 + 3 ^ 40 * 960060 * 2
def baseEnd_960060 : Nat := 24344308007684888619001

theorem tailTrace_960060 : CollatzResearch.WordTrace tailWord_960060 prefixEnd_960060 24344308007684888619001 := by
  unfold tailWord_960060
  simp only [CollatzResearch.WordTrace]
  refine ⟨17508132450937030019586817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23344176601249373359449089 17508132450937030019586817)
  ·
    refine ⟨13131099338202772514690113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17508132450937030019586817 13131099338202772514690113)
    ·
      refine ⟨9848324503652079386017585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13131099338202772514690113 9848324503652079386017585)
      ·
        refine ⟨7386243377739059539513189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9848324503652079386017585 7386243377739059539513189)
        ·
          refine ⟨1384920633326073663658723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7386243377739059539513189 1384920633326073663658723)
          ·
            refine ⟨2077380949989110495488085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1384920633326073663658723 2077380949989110495488085)
            ·
              refine ⟨24344308007684888619001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2077380949989110495488085 24344308007684888619001)
              ·
                rfl

theorem cell21_960060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 8].length) (baseStart_960060 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_960060 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_960060 prefixEnd_960060 := by exact prefixLift 960060
  have htrace : WordTrace (prefixWord ++ tailWord_960060) baseStart_960060 baseEnd_960060 := by
    simpa [prefixWord, tailWord_960060, baseEnd_960060] using wordTrace_append hprefix tailTrace_960060
  have hstable : (prefixWord ++ tailWord_960060).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960060).length < 2 ^ (prefixWord ++ tailWord_960060).sum := by decide
  have hdescent : baseEnd_960060 < baseStart_960060 := by decide
  rcases family_descends (prefixWord ++ tailWord_960060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960125 : List Nat := [1, 4, 1, 1, 4, 2, 3, 2, 3]
def baseStart_960125 : Nat := 118140960795 + 960125 * 2 ^ 59
def prefixEnd_960125 : Nat := 4983230072969 + 3 ^ 40 * 960125 * 2
def baseEnd_960125 : Nat := 219113605954738328987543

theorem tailTrace_960125 : CollatzResearch.WordTrace tailWord_960125 prefixEnd_960125 219113605954738328987543 := by
  unfold tailWord_960125
  simp only [CollatzResearch.WordTrace]
  refine ⟨35018635646638576140289829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23345757097759050760193219 35018635646638576140289829)
  ·
    refine ⟨6565994183744733026304343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35018635646638576140289829 6565994183744733026304343)
    ·
      refine ⟨9848991275617099539456515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6565994183744733026304343 9848991275617099539456515)
      ·
        refine ⟨14773486913425649309184773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9848991275617099539456515 14773486913425649309184773)
        ·
          refine ⟨2770028796267309245472145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14773486913425649309184773 2770028796267309245472145)
          ·
            refine ⟨2077521597200481934104109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2770028796267309245472145 2077521597200481934104109)
            ·
              refine ⟨779070598950180725289041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2077521597200481934104109 779070598950180725289041)
              ·
                refine ⟨584302949212635543966781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 779070598950180725289041 584302949212635543966781)
                ·
                  refine ⟨219113605954738328987543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 584302949212635543966781 219113605954738328987543)
                  ·
                    rfl

theorem cell21_960125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 3, 2, 3].length) (baseStart_960125 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_960125 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_960125 prefixEnd_960125 := by exact prefixLift 960125
  have htrace : WordTrace (prefixWord ++ tailWord_960125) baseStart_960125 baseEnd_960125 := by
    simpa [prefixWord, tailWord_960125, baseEnd_960125] using wordTrace_append hprefix tailTrace_960125
  have hstable : (prefixWord ++ tailWord_960125).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960125).length < 2 ^ (prefixWord ++ tailWord_960125).sum := by decide
  have hdescent : baseEnd_960125 < baseStart_960125 := by decide
  rcases family_descends (prefixWord ++ tailWord_960125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960243 : List Nat := [1, 1, 1, 2, 2, 3, 4, 4, 3]
def baseStart_960243 : Nat := 118140960795 + 960243 * 2 ^ 59
def prefixEnd_960243 : Nat := 4983230072969 + 3 ^ 40 * 960243 * 2
def baseEnd_960243 : Nat := 219140535162396346020635

theorem tailTrace_960243 : CollatzResearch.WordTrace tailWord_960243 prefixEnd_960243 219140535162396346020635 := by
  unfold tailWord_960243
  simp only [CollatzResearch.WordTrace]
  refine ⟨35022939460211082293085383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23348626306807388195390255 35022939460211082293085383)
  ·
    refine ⟨52534409190316623439628075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35022939460211082293085383 52534409190316623439628075)
    ·
      refine ⟨78801613785474935159442113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52534409190316623439628075 78801613785474935159442113)
      ·
        refine ⟨59101210339106201369581585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78801613785474935159442113 59101210339106201369581585)
        ·
          refine ⟨44325907754329651027186189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59101210339106201369581585 44325907754329651027186189)
          ·
            refine ⟨16622215407873619135194821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44325907754329651027186189 16622215407873619135194821)
            ·
              refine ⟨3116665388976303587849029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16622215407873619135194821 3116665388976303587849029)
              ·
                refine ⟨584374760433056922721693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3116665388976303587849029 584374760433056922721693)
                ·
                  refine ⟨219140535162396346020635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 584374760433056922721693 219140535162396346020635)
                  ·
                    rfl

theorem cell21_960243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 4, 3].length) (baseStart_960243 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_960243 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_960243 prefixEnd_960243 := by exact prefixLift 960243
  have htrace : WordTrace (prefixWord ++ tailWord_960243) baseStart_960243 baseEnd_960243 := by
    simpa [prefixWord, tailWord_960243, baseEnd_960243] using wordTrace_append hprefix tailTrace_960243
  have hstable : (prefixWord ++ tailWord_960243).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960243).length < 2 ^ (prefixWord ++ tailWord_960243).sum := by decide
  have hdescent : baseEnd_960243 < baseStart_960243 := by decide
  rcases family_descends (prefixWord ++ tailWord_960243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960257 : List Nat := [1, 2, 4, 1, 1, 1, 2, 5, 4]
def baseStart_960257 : Nat := 118140960795 + 960257 * 2 ^ 59
def prefixEnd_960257 : Nat := 4983230072969 + 3 ^ 40 * 960257 * 2
def baseEnd_960257 : Nat := 219143730153135432787273

theorem tailTrace_960257 : CollatzResearch.WordTrace tailWord_960257 prefixEnd_960257 219143730153135432787273 := by
  unfold tailWord_960257
  simp only [CollatzResearch.WordTrace]
  refine ⟨35023450082160362684095025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23348966721440241789396683 35023450082160362684095025)
  ·
    refine ⟨26267587561620272013071269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35023450082160362684095025 26267587561620272013071269)
    ·
      refine ⟨4925172667803801002450863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26267587561620272013071269 4925172667803801002450863)
      ·
        refine ⟨7387759001705701503676295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4925172667803801002450863 7387759001705701503676295)
        ·
          refine ⟨11081638502558552255514443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7387759001705701503676295 11081638502558552255514443)
          ·
            refine ⟨16622457753837828383271665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11081638502558552255514443 16622457753837828383271665)
            ·
              refine ⟨12466843315378371287453749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16622457753837828383271665 12466843315378371287453749)
              ·
                refine ⟨1168766560816722308198789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12466843315378371287453749 1168766560816722308198789)
                ·
                  refine ⟨219143730153135432787273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1168766560816722308198789 219143730153135432787273)
                  ·
                    rfl

theorem cell21_960257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 5, 4].length) (baseStart_960257 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_960257 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_960257 prefixEnd_960257 := by exact prefixLift 960257
  have htrace : WordTrace (prefixWord ++ tailWord_960257) baseStart_960257 baseEnd_960257 := by
    simpa [prefixWord, tailWord_960257, baseEnd_960257] using wordTrace_append hprefix tailTrace_960257
  have hstable : (prefixWord ++ tailWord_960257).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960257).length < 2 ^ (prefixWord ++ tailWord_960257).sum := by decide
  have hdescent : baseEnd_960257 < baseStart_960257 := by decide
  rcases family_descends (prefixWord ++ tailWord_960257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960269 : List Nat := [1, 7, 2, 1, 2, 1, 1, 3, 3]
def baseStart_960269 : Nat := 118140960795 + 960269 * 2 ^ 59
def prefixEnd_960269 : Nat := 4983230072969 + 3 ^ 40 * 960269 * 2
def baseEnd_960269 : Nat := 219146468716626078587249

theorem tailTrace_960269 : CollatzResearch.WordTrace tailWord_960269 prefixEnd_960269 219146468716626078587249 := by
  unfold tailWord_960269
  simp only [CollatzResearch.WordTrace]
  refine ⟨35023887758116888733531861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23349258505411259155687907 35023887758116888733531861)
  ·
    refine ⟨820872369330864579692153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 35023887758116888733531861 820872369330864579692153)
    ·
      refine ⟨615654276998148434769115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 820872369330864579692153 615654276998148434769115)
      ·
        refine ⟨923481415497222652153673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 615654276998148434769115 923481415497222652153673)
        ·
          refine ⟨692611061622916989115255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 923481415497222652153673 692611061622916989115255)
          ·
            refine ⟨1038916592434375483672883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 692611061622916989115255 1038916592434375483672883)
            ·
              refine ⟨1558374888651563225509325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1038916592434375483672883 1558374888651563225509325)
              ·
                refine ⟨584390583244336209565997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1558374888651563225509325 584390583244336209565997)
                ·
                  refine ⟨219146468716626078587249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 584390583244336209565997 219146468716626078587249)
                  ·
                    rfl

theorem cell21_960269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_960269 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_960269 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_960269 prefixEnd_960269 := by exact prefixLift 960269
  have htrace : WordTrace (prefixWord ++ tailWord_960269) baseStart_960269 baseEnd_960269 := by
    simpa [prefixWord, tailWord_960269, baseEnd_960269] using wordTrace_append hprefix tailTrace_960269
  have hstable : (prefixWord ++ tailWord_960269).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960269).length < 2 ^ (prefixWord ++ tailWord_960269).sum := by decide
  have hdescent : baseEnd_960269 < baseStart_960269 := by decide
  rcases family_descends (prefixWord ++ tailWord_960269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960274 : List Nat := [3, 2, 4, 1, 1, 1, 1, 2, 6]
def baseStart_960274 : Nat := 118140960795 + 960274 * 2 ^ 59
def prefixEnd_960274 : Nat := 4983230072969 + 3 ^ 40 * 960274 * 2
def baseEnd_960274 : Nat := 219147609784747181003905

theorem tailTrace_960274 : CollatzResearch.WordTrace tailWord_960274 prefixEnd_960274 219147609784747181003905 := by
  unfold tailWord_960274
  simp only [CollatzResearch.WordTrace]
  refine ⟨8756017530774693646865969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23349380082065849724975917 8756017530774693646865969)
  ·
    refine ⟨6567013148081020235149477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8756017530774693646865969 6567013148081020235149477)
    ·
      refine ⟨1231314965265191294090527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6567013148081020235149477 1231314965265191294090527)
      ·
        refine ⟨1846972447897786941135791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1231314965265191294090527 1846972447897786941135791)
        ·
          refine ⟨2770458671846680411703687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1846972447897786941135791 2770458671846680411703687)
          ·
            refine ⟨4155688007770020617555531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2770458671846680411703687 4155688007770020617555531)
            ·
              refine ⟨6233532011655030926333297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4155688007770020617555531 6233532011655030926333297)
              ·
                refine ⟨4675149008741273194749973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6233532011655030926333297 4675149008741273194749973)
                ·
                  refine ⟨219147609784747181003905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4675149008741273194749973 219147609784747181003905)
                  ·
                    rfl

theorem cell21_960274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 2, 6].length) (baseStart_960274 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_960274 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_960274 prefixEnd_960274 := by exact prefixLift 960274
  have htrace : WordTrace (prefixWord ++ tailWord_960274) baseStart_960274 baseEnd_960274 := by
    simpa [prefixWord, tailWord_960274, baseEnd_960274] using wordTrace_append hprefix tailTrace_960274
  have hstable : (prefixWord ++ tailWord_960274).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960274).length < 2 ^ (prefixWord ++ tailWord_960274).sum := by decide
  have hdescent : baseEnd_960274 < baseStart_960274 := by decide
  rcases family_descends (prefixWord ++ tailWord_960274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960308 : List Nat := [2, 5, 1, 1, 2, 3, 2, 1, 4]
def baseStart_960308 : Nat := 118140960795 + 960308 * 2 ^ 59
def prefixEnd_960308 : Nat := 4983230072969 + 3 ^ 40 * 960308 * 2
def baseEnd_960308 : Nat := 219155369047970677437169

theorem tailTrace_960308 : CollatzResearch.WordTrace tailWord_960308 prefixEnd_960308 219155369047970677437169 := by
  unfold tailWord_960308
  simp only [CollatzResearch.WordTrace]
  refine ⟨17512655102487799197100789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23350206803317065596134385 17512655102487799197100789)
  ·
    refine ⟨1641811415858231174728199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17512655102487799197100789 1641811415858231174728199)
    ·
      refine ⟨2462717123787346762092299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1641811415858231174728199 2462717123787346762092299)
      ·
        refine ⟨3694075685681020143138449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2462717123787346762092299 3694075685681020143138449)
        ·
          refine ⟨2770556764260765107353837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3694075685681020143138449 2770556764260765107353837)
          ·
            refine ⟨1038958786597786915257689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2770556764260765107353837 1038958786597786915257689)
            ·
              refine ⟨779219089948340186443267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1038958786597786915257689 779219089948340186443267)
              ·
                refine ⟨1168828634922510279664901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 779219089948340186443267 1168828634922510279664901)
                ·
                  refine ⟨219155369047970677437169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1168828634922510279664901 219155369047970677437169)
                  ·
                    rfl

theorem cell21_960308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_960308 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_960308 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_960308 prefixEnd_960308 := by exact prefixLift 960308
  have htrace : WordTrace (prefixWord ++ tailWord_960308) baseStart_960308 baseEnd_960308 := by
    simpa [prefixWord, tailWord_960308, baseEnd_960308] using wordTrace_append hprefix tailTrace_960308
  have hstable : (prefixWord ++ tailWord_960308).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960308).length < 2 ^ (prefixWord ++ tailWord_960308).sum := by decide
  have hdescent : baseEnd_960308 < baseStart_960308 := by decide
  rcases family_descends (prefixWord ++ tailWord_960308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960361 : List Nat := [1, 2, 1, 1, 1, 3, 1, 2, 9]
def baseStart_960361 : Nat := 118140960795 + 960361 * 2 ^ 59
def prefixEnd_960361 : Nat := 4983230072969 + 3 ^ 40 * 960361 * 2
def baseEnd_960361 : Nat := 219167464370054363053727

theorem tailTrace_960361 : CollatzResearch.WordTrace tailWord_960361 prefixEnd_960361 219167464370054363053727 := by
  unfold tailWord_960361
  simp only [CollatzResearch.WordTrace]
  refine ⟨35027243273783588445880937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23351495515855725630587291 35027243273783588445880937)
  ·
    refine ⟨26270432455337691334410703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35027243273783588445880937 26270432455337691334410703)
    ·
      refine ⟨39405648683006537001616055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26270432455337691334410703 39405648683006537001616055)
      ·
        refine ⟨59108473024509805502424083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39405648683006537001616055 59108473024509805502424083)
        ·
          refine ⟨88662709536764708253636125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59108473024509805502424083 88662709536764708253636125)
          ·
            refine ⟨33248516076286765595113547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88662709536764708253636125 33248516076286765595113547)
            ·
              refine ⟨49872774114430148392670321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33248516076286765595113547 49872774114430148392670321)
              ·
                refine ⟨37404580585822611294502741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49872774114430148392670321 37404580585822611294502741)
                ·
                  refine ⟨219167464370054363053727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 37404580585822611294502741 219167464370054363053727)
                  ·
                    rfl

theorem cell21_960361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 9].length) (baseStart_960361 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_960361 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_960361 prefixEnd_960361 := by exact prefixLift 960361
  have htrace : WordTrace (prefixWord ++ tailWord_960361) baseStart_960361 baseEnd_960361 := by
    simpa [prefixWord, tailWord_960361, baseEnd_960361] using wordTrace_append hprefix tailTrace_960361
  have hstable : (prefixWord ++ tailWord_960361).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960361).length < 2 ^ (prefixWord ++ tailWord_960361).sum := by decide
  have hdescent : baseEnd_960361 < baseStart_960361 := by decide
  rcases family_descends (prefixWord ++ tailWord_960361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960364 : List Nat := [2, 2, 1, 1, 4, 4, 1, 6]
def baseStart_960364 : Nat := 118140960795 + 960364 * 2 ^ 59
def prefixEnd_960364 : Nat := 4983230072969 + 3 ^ 40 * 960364 * 2
def baseEnd_960364 : Nat := 73056049670309008167907

theorem tailTrace_960364 : CollatzResearch.WordTrace tailWord_960364 prefixEnd_960364 73056049670309008167907 := by
  unfold tailWord_960364
  simp only [CollatzResearch.WordTrace]
  refine ⟨17513676346386359979120073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23351568461848479972160097 17513676346386359979120073)
  ·
    refine ⟨13135257259789769984340055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17513676346386359979120073 13135257259789769984340055)
    ·
      refine ⟨19702885889684654976510083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13135257259789769984340055 19702885889684654976510083)
      ·
        refine ⟨29554328834526982464765125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19702885889684654976510083 29554328834526982464765125)
        ·
          refine ⟨5541436656473809212143461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29554328834526982464765125 5541436656473809212143461)
          ·
            refine ⟨1039019373088839227276899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5541436656473809212143461 1039019373088839227276899)
            ·
              refine ⟨1558529059633258840915349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1039019373088839227276899 1558529059633258840915349)
              ·
                refine ⟨73056049670309008167907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1558529059633258840915349 73056049670309008167907)
                ·
                  rfl

theorem cell21_960364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 1, 6].length) (baseStart_960364 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_960364 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_960364 prefixEnd_960364 := by exact prefixLift 960364
  have htrace : WordTrace (prefixWord ++ tailWord_960364) baseStart_960364 baseEnd_960364 := by
    simpa [prefixWord, tailWord_960364, baseEnd_960364] using wordTrace_append hprefix tailTrace_960364
  have hstable : (prefixWord ++ tailWord_960364).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960364).length < 2 ^ (prefixWord ++ tailWord_960364).sum := by decide
  have hdescent : baseEnd_960364 < baseStart_960364 := by decide
  rcases family_descends (prefixWord ++ tailWord_960364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960409 : List Nat := [1, 2, 1, 2, 1, 3, 5, 2, 4]
def baseStart_960409 : Nat := 118140960795 + 960409 * 2 ^ 59
def prefixEnd_960409 : Nat := 4983230072969 + 3 ^ 40 * 960409 * 2
def baseEnd_960409 : Nat := 219178418624016946253629

theorem tailTrace_960409 : CollatzResearch.WordTrace tailWord_960409 prefixEnd_960409 219178418624016946253629 := by
  unfold tailWord_960409
  simp only [CollatzResearch.WordTrace]
  refine ⟨35028993977609692643628281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23352662651739795095752187 35028993977609692643628281)
  ·
    refine ⟨26271745483207269482721211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35028993977609692643628281 26271745483207269482721211)
    ·
      refine ⟨39407618224810904224081817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26271745483207269482721211 39407618224810904224081817)
      ·
        refine ⟨29555713668608178168061363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39407618224810904224081817 29555713668608178168061363)
        ·
          refine ⟨44333570502912267252092045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29555713668608178168061363 44333570502912267252092045)
          ·
            refine ⟨16625088938592100219534517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44333570502912267252092045 16625088938592100219534517)
            ·
              refine ⟨1558602087993009395581361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16625088938592100219534517 1558602087993009395581361)
              ·
                refine ⟨1168951565994757046686021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1558602087993009395581361 1168951565994757046686021)
                ·
                  refine ⟨219178418624016946253629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1168951565994757046686021 219178418624016946253629)
                  ·
                    rfl

theorem cell21_960409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 5, 2, 4].length) (baseStart_960409 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_960409 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_960409 prefixEnd_960409 := by exact prefixLift 960409
  have htrace : WordTrace (prefixWord ++ tailWord_960409) baseStart_960409 baseEnd_960409 := by
    simpa [prefixWord, tailWord_960409, baseEnd_960409] using wordTrace_append hprefix tailTrace_960409
  have hstable : (prefixWord ++ tailWord_960409).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960409).length < 2 ^ (prefixWord ++ tailWord_960409).sum := by decide
  have hdescent : baseEnd_960409 < baseStart_960409 := by decide
  rcases family_descends (prefixWord ++ tailWord_960409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960412 : List Nat := [2, 2, 3, 3, 1, 1, 2, 4, 3]
def baseStart_960412 : Nat := 118140960795 + 960412 * 2 ^ 59
def prefixEnd_960412 : Nat := 4983230072969 + 3 ^ 40 * 960412 * 2
def baseEnd_960412 : Nat := 219179103264889607703623

theorem tailTrace_960412 : CollatzResearch.WordTrace tailWord_960412 prefixEnd_960412 219179103264889607703623 := by
  unfold tailWord_960412
  simp only [CollatzResearch.WordTrace]
  refine ⟨17514551698299412077993745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23352735597732549437324993 17514551698299412077993745)
  ·
    refine ⟨13135913773724559058495309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17514551698299412077993745 13135913773724559058495309)
    ·
      refine ⟨4925967665146709646935741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13135913773724559058495309 4925967665146709646935741)
      ·
        refine ⟨1847237874430016117600903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4925967665146709646935741 1847237874430016117600903)
        ·
          refine ⟨2770856811645024176401355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1847237874430016117600903 2770856811645024176401355)
          ·
            refine ⟨4156285217467536264602033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2770856811645024176401355 4156285217467536264602033)
            ·
              refine ⟨3117213913100652198451525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4156285217467536264602033 3117213913100652198451525)
              ·
                refine ⟨584477608706372287209661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3117213913100652198451525 584477608706372287209661)
                ·
                  refine ⟨219179103264889607703623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 584477608706372287209661 219179103264889607703623)
                  ·
                    rfl

theorem cell21_960412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 4, 3].length) (baseStart_960412 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_960412 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_960412 prefixEnd_960412 := by exact prefixLift 960412
  have htrace : WordTrace (prefixWord ++ tailWord_960412) baseStart_960412 baseEnd_960412 := by
    simpa [prefixWord, tailWord_960412, baseEnd_960412] using wordTrace_append hprefix tailTrace_960412
  have hstable : (prefixWord ++ tailWord_960412).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960412).length < 2 ^ (prefixWord ++ tailWord_960412).sum := by decide
  have hdescent : baseEnd_960412 < baseStart_960412 := by decide
  rcases family_descends (prefixWord ++ tailWord_960412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960516 : List Nat := [2, 3, 2, 4, 1, 9]
def baseStart_960516 : Nat := 118140960795 + 960516 * 2 ^ 59
def prefixEnd_960516 : Nat := 4983230072969 + 3 ^ 40 * 960516 * 2
def baseEnd_960516 : Nat := 8118623610437353258151

theorem tailTrace_960516 : CollatzResearch.WordTrace tailWord_960516 prefixEnd_960516 8118623610437353258151 := by
  unfold tailWord_960516
  simp only [CollatzResearch.WordTrace]
  refine ⟨17516448294111024958886701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23355264392148033278515601 17516448294111024958886701)
  ·
    refine ⟨6568668110291634359582513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17516448294111024958886701 6568668110291634359582513)
    ·
      refine ⟨4926501082718725769686885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6568668110291634359582513 4926501082718725769686885)
      ·
        refine ⟨923718953009761081816291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4926501082718725769686885 923718953009761081816291)
        ·
          refine ⟨1385578429514641622724437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 923718953009761081816291 1385578429514641622724437)
          ·
            refine ⟨8118623610437353258151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1385578429514641622724437 8118623610437353258151)
            ·
              rfl

theorem cell21_960516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 9].length) (baseStart_960516 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_960516 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_960516 prefixEnd_960516 := by exact prefixLift 960516
  have htrace : WordTrace (prefixWord ++ tailWord_960516) baseStart_960516 baseEnd_960516 := by
    simpa [prefixWord, tailWord_960516, baseEnd_960516] using wordTrace_append hprefix tailTrace_960516
  have hstable : (prefixWord ++ tailWord_960516).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960516).length < 2 ^ (prefixWord ++ tailWord_960516).sum := by decide
  have hdescent : baseEnd_960516 < baseStart_960516 := by decide
  rcases family_descends (prefixWord ++ tailWord_960516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960522 : List Nat := [3, 1, 2, 2, 5, 1, 2, 2, 3]
def baseStart_960522 : Nat := 118140960795 + 960522 * 2 ^ 59
def prefixEnd_960522 : Nat := 4983230072969 + 3 ^ 40 * 960522 * 2
def baseEnd_960522 : Nat := 219204206763553860870065

theorem tailTrace_960522 : CollatzResearch.WordTrace tailWord_960522 prefixEnd_960522 219204206763553860870065 := by
  unfold tailWord_960522
  simp only [CollatzResearch.WordTrace]
  refine ⟨8758278856550078235622955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23355410284133541961661213 8758278856550078235622955)
  ·
    refine ⟨13137418284825117353434433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8758278856550078235622955 13137418284825117353434433)
    ·
      refine ⟨9853063713618838015075825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13137418284825117353434433 9853063713618838015075825)
      ·
        refine ⟨7389797785214128511306869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9853063713618838015075825 7389797785214128511306869)
        ·
          refine ⟨692793542363824547935019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7389797785214128511306869 692793542363824547935019)
          ·
            refine ⟨1039190313545736821902529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 692793542363824547935019 1039190313545736821902529)
            ·
              refine ⟨779392735159302616426897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1039190313545736821902529 779392735159302616426897)
              ·
                refine ⟨584544551369476962320173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 779392735159302616426897 584544551369476962320173)
                ·
                  refine ⟨219204206763553860870065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 584544551369476962320173 219204206763553860870065)
                  ·
                    rfl

theorem cell21_960522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 2, 2, 3].length) (baseStart_960522 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_960522 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_960522 prefixEnd_960522 := by exact prefixLift 960522
  have htrace : WordTrace (prefixWord ++ tailWord_960522) baseStart_960522 baseEnd_960522 := by
    simpa [prefixWord, tailWord_960522, baseEnd_960522] using wordTrace_append hprefix tailTrace_960522
  have hstable : (prefixWord ++ tailWord_960522).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960522).length < 2 ^ (prefixWord ++ tailWord_960522).sum := by decide
  have hdescent : baseEnd_960522 < baseStart_960522 := by decide
  rcases family_descends (prefixWord ++ tailWord_960522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960533 : List Nat := [1, 3, 2, 1, 6, 1, 1, 6]
def baseStart_960533 : Nat := 118140960795 + 960533 * 2 ^ 59
def prefixEnd_960533 : Nat := 4983230072969 + 3 ^ 40 * 960533 * 2
def baseEnd_960533 : Nat := 73068905704473428728903

theorem tailTrace_960533 : CollatzResearch.WordTrace tailWord_960533 prefixEnd_960533 73068905704473428728903 := by
  unfold tailWord_960533
  simp only [CollatzResearch.WordTrace]
  refine ⟨35033516629160461821142253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23355677752773641214094835 35033516629160461821142253)
  ·
    refine ⟨13137568735935173182928345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35033516629160461821142253 13137568735935173182928345)
    ·
      refine ⟨9853176551951379887196259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13137568735935173182928345 9853176551951379887196259)
      ·
        refine ⟨14779764827927069830794389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9853176551951379887196259 14779764827927069830794389)
        ·
          refine ⟨692801476309081398318487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 14779764827927069830794389 692801476309081398318487)
          ·
            refine ⟨1039202214463622097477731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 692801476309081398318487 1039202214463622097477731)
            ·
              refine ⟨1558803321695433146216597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1039202214463622097477731 1558803321695433146216597)
              ·
                refine ⟨73068905704473428728903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1558803321695433146216597 73068905704473428728903)
                ·
                  rfl

theorem cell21_960533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 1, 6].length) (baseStart_960533 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_960533 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_960533 prefixEnd_960533 := by exact prefixLift 960533
  have htrace : WordTrace (prefixWord ++ tailWord_960533) baseStart_960533 baseEnd_960533 := by
    simpa [prefixWord, tailWord_960533, baseEnd_960533] using wordTrace_append hprefix tailTrace_960533
  have hstable : (prefixWord ++ tailWord_960533).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960533).length < 2 ^ (prefixWord ++ tailWord_960533).sum := by decide
  have hdescent : baseEnd_960533 < baseStart_960533 := by decide
  rcases family_descends (prefixWord ++ tailWord_960533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960620 : List Nat := [2, 2, 1, 1, 3, 3, 1, 2, 6]
def baseStart_960620 : Nat := 118140960795 + 960620 * 2 ^ 59
def prefixEnd_960620 : Nat := 4983230072969 + 3 ^ 40 * 960620 * 2
def baseEnd_960620 : Nat := 219226571698727468236531

theorem tailTrace_960620 : CollatzResearch.WordTrace tailWord_960620 prefixEnd_960620 219226571698727468236531 := by
  unfold tailWord_960620
  simp only [CollatzResearch.WordTrace]
  refine ⟨17518344889922637839779657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23357793186563517119706209 17518344889922637839779657)
  ·
    refine ⟨13138758667441978379834743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17518344889922637839779657 13138758667441978379834743)
    ·
      refine ⟨19708138001162967569752115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13138758667441978379834743 19708138001162967569752115)
      ·
        refine ⟨29562207001744451354628173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19708138001162967569752115 29562207001744451354628173)
        ·
          refine ⟨11085827625654169257985565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29562207001744451354628173 11085827625654169257985565)
          ·
            refine ⟨4157185359620313471744587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11085827625654169257985565 4157185359620313471744587)
            ·
              refine ⟨6235778039430470207616881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4157185359620313471744587 6235778039430470207616881)
              ·
                refine ⟨4676833529572852655712661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6235778039430470207616881 4676833529572852655712661)
                ·
                  refine ⟨219226571698727468236531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4676833529572852655712661 219226571698727468236531)
                  ·
                    rfl

theorem cell21_960620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 6].length) (baseStart_960620 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_960620 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_960620 prefixEnd_960620 := by exact prefixLift 960620
  have htrace : WordTrace (prefixWord ++ tailWord_960620) baseStart_960620 baseEnd_960620 := by
    simpa [prefixWord, tailWord_960620, baseEnd_960620] using wordTrace_append hprefix tailTrace_960620
  have hstable : (prefixWord ++ tailWord_960620).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960620).length < 2 ^ (prefixWord ++ tailWord_960620).sum := by decide
  have hdescent : baseEnd_960620 < baseStart_960620 := by decide
  rcases family_descends (prefixWord ++ tailWord_960620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960623 : List Nat := [1, 1, 2, 1, 3, 4, 3, 3, 3]
def baseStart_960623 : Nat := 118140960795 + 960623 * 2 ^ 59
def prefixEnd_960623 : Nat := 4983230072969 + 3 ^ 40 * 960623 * 2
def baseEnd_960623 : Nat := 219227256339600129686525

theorem tailTrace_960623 : CollatzResearch.WordTrace tailWord_960623 prefixEnd_960623 219227256339600129686525 := by
  unfold tailWord_960623
  simp only [CollatzResearch.WordTrace]
  refine ⟨35036799198834407191918523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23357866132556271461279015 35036799198834407191918523)
  ·
    refine ⟨52555198798251610787877785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35036799198834407191918523 52555198798251610787877785)
    ·
      refine ⟨39416399098688708090908339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52555198798251610787877785 39416399098688708090908339)
      ·
        refine ⟨59124598648033062136362509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39416399098688708090908339 59124598648033062136362509)
        ·
          refine ⟨22171724493012398301135941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59124598648033062136362509 22171724493012398301135941)
          ·
            refine ⟨4157198342439824681462989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22171724493012398301135941 4157198342439824681462989)
            ·
              refine ⟨1558949378414934255548621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4157198342439824681462989 1558949378414934255548621)
              ·
                refine ⟨584606016905600345830733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1558949378414934255548621 584606016905600345830733)
                ·
                  refine ⟨219227256339600129686525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 584606016905600345830733 219227256339600129686525)
                  ·
                    rfl

theorem cell21_960623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 3, 3, 3].length) (baseStart_960623 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_960623 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_960623 prefixEnd_960623 := by exact prefixLift 960623
  have htrace : WordTrace (prefixWord ++ tailWord_960623) baseStart_960623 baseEnd_960623 := by
    simpa [prefixWord, tailWord_960623, baseEnd_960623] using wordTrace_append hprefix tailTrace_960623
  have hstable : (prefixWord ++ tailWord_960623).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960623).length < 2 ^ (prefixWord ++ tailWord_960623).sum := by decide
  have hdescent : baseEnd_960623 < baseStart_960623 := by decide
  rcases family_descends (prefixWord ++ tailWord_960623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960654 : List Nat := [4, 1, 1, 3, 3, 1, 1, 3, 4]
def baseStart_960654 : Nat := 118140960795 + 960654 * 2 ^ 59
def prefixEnd_960654 : Nat := 4983230072969 + 3 ^ 40 * 960654 * 2
def baseEnd_960654 : Nat := 219234330961950964669795

theorem tailTrace_960654 : CollatzResearch.WordTrace tailWord_960654 prefixEnd_960654 219234330961950964669795 := by
  unfold tailWord_960654
  simp only [CollatzResearch.WordTrace]
  refine ⟨4379741232715262435787127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23358619907814732990864677 4379741232715262435787127)
  ·
    refine ⟨6569611849072893653680691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4379741232715262435787127 6569611849072893653680691)
    ·
      refine ⟨9854417773609340480521037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6569611849072893653680691 9854417773609340480521037)
      ·
        refine ⟨3695406665103502680195389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9854417773609340480521037 3695406665103502680195389)
        ·
          refine ⟨1385777499413813505073271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3695406665103502680195389 1385777499413813505073271)
          ·
            refine ⟨2078666249120720257609907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1385777499413813505073271 2078666249120720257609907)
            ·
              refine ⟨3117999373681080386414861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2078666249120720257609907 3117999373681080386414861)
              ·
                refine ⟨1169249765130405144905573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3117999373681080386414861 1169249765130405144905573)
                ·
                  refine ⟨219234330961950964669795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1169249765130405144905573 219234330961950964669795)
                  ·
                    rfl

theorem cell21_960654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 3, 4].length) (baseStart_960654 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_960654 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_960654 prefixEnd_960654 := by exact prefixLift 960654
  have htrace : WordTrace (prefixWord ++ tailWord_960654) baseStart_960654 baseEnd_960654 := by
    simpa [prefixWord, tailWord_960654, baseEnd_960654] using wordTrace_append hprefix tailTrace_960654
  have hstable : (prefixWord ++ tailWord_960654).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960654).length < 2 ^ (prefixWord ++ tailWord_960654).sum := by decide
  have hdescent : baseEnd_960654 < baseStart_960654 := by decide
  rcases family_descends (prefixWord ++ tailWord_960654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960665 : List Nat := [1, 2, 1, 2, 1, 2, 1, 6, 5]
def baseStart_960665 : Nat := 118140960795 + 960665 * 2 ^ 59
def prefixEnd_960665 : Nat := 4983230072969 + 3 ^ 40 * 960665 * 2
def baseEnd_960665 : Nat := 219236841311817389986439

theorem tailTrace_960665 : CollatzResearch.WordTrace tailWord_960665 prefixEnd_960665 219236841311817389986439 := by
  unfold tailWord_960665
  simp only [CollatzResearch.WordTrace]
  refine ⟨35038331064682248364947449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23358887376454832243298299 35038331064682248364947449)
  ·
    refine ⟨26278748298511686273710587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35038331064682248364947449 26278748298511686273710587)
    ·
      refine ⟨39418122447767529410565881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26278748298511686273710587 39418122447767529410565881)
      ·
        refine ⟨29563591835825647057924411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39418122447767529410565881 29563591835825647057924411)
        ·
          refine ⟨44345387753738470586886617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29563591835825647057924411 44345387753738470586886617)
          ·
            refine ⟨33259040815303852940164963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44345387753738470586886617 33259040815303852940164963)
            ·
              refine ⟨49888561222955779410247445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33259040815303852940164963 49888561222955779410247445)
              ·
                refine ⟨2338526307326052159855349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 49888561222955779410247445 2338526307326052159855349)
                ·
                  refine ⟨219236841311817389986439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2338526307326052159855349 219236841311817389986439)
                  ·
                    rfl

theorem cell21_960665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 6, 5].length) (baseStart_960665 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_960665 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_960665 prefixEnd_960665 := by exact prefixLift 960665
  have htrace : WordTrace (prefixWord ++ tailWord_960665) baseStart_960665 baseEnd_960665 := by
    simpa [prefixWord, tailWord_960665, baseEnd_960665] using wordTrace_append hprefix tailTrace_960665
  have hstable : (prefixWord ++ tailWord_960665).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960665).length < 2 ^ (prefixWord ++ tailWord_960665).sum := by decide
  have hdescent : baseEnd_960665 < baseStart_960665 := by decide
  rcases family_descends (prefixWord ++ tailWord_960665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960758 : List Nat := [5, 1, 1, 1, 1, 1, 3, 3, 5]
def baseStart_960758 : Nat := 118140960795 + 960758 * 2 ^ 59
def prefixEnd_960758 : Nat := 4983230072969 + 3 ^ 40 * 960758 * 2
def baseEnd_960758 : Nat := 219258065178869894936249

theorem tailTrace_960758 : CollatzResearch.WordTrace tailWord_960758 prefixEnd_960758 219258065178869894936249 := by
  unfold tailWord_960758
  simp only [CollatzResearch.WordTrace]
  refine ⟨2190107690834082828005183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23361148702230216832055285 2190107690834082828005183)
  ·
    refine ⟨3285161536251124242007775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2190107690834082828005183 3285161536251124242007775)
    ·
      refine ⟨4927742304376686363011663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3285161536251124242007775 4927742304376686363011663)
      ·
        refine ⟨7391613456565029544517495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4927742304376686363011663 7391613456565029544517495)
        ·
          refine ⟨11087420184847544316776243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7391613456565029544517495 11087420184847544316776243)
          ·
            refine ⟨16631130277271316475164365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11087420184847544316776243 16631130277271316475164365)
            ·
              refine ⟨6236673853976743678186637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16631130277271316475164365 6236673853976743678186637)
              ·
                refine ⟨2338752695241278879319989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6236673853976743678186637 2338752695241278879319989)
                ·
                  refine ⟨219258065178869894936249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2338752695241278879319989 219258065178869894936249)
                  ·
                    rfl

theorem cell21_960758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 3, 5].length) (baseStart_960758 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_960758 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_960758 prefixEnd_960758 := by exact prefixLift 960758
  have htrace : WordTrace (prefixWord ++ tailWord_960758) baseStart_960758 baseEnd_960758 := by
    simpa [prefixWord, tailWord_960758, baseEnd_960758] using wordTrace_append hprefix tailTrace_960758
  have hstable : (prefixWord ++ tailWord_960758).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960758).length < 2 ^ (prefixWord ++ tailWord_960758).sum := by decide
  have hdescent : baseEnd_960758 < baseStart_960758 := by decide
  rcases family_descends (prefixWord ++ tailWord_960758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960820 : List Nat := [2, 5, 1, 1, 1, 3, 2, 6]
def baseStart_960820 : Nat := 118140960795 + 960820 * 2 ^ 59
def prefixEnd_960820 : Nat := 4983230072969 + 3 ^ 40 * 960820 * 2
def baseEnd_960820 : Nat := 73090738141190521634263

theorem tailTrace_960820 : CollatzResearch.WordTrace tailWord_960820 prefixEnd_960820 73090738141190521634263 := by
  unfold tailWord_960820
  simp only [CollatzResearch.WordTrace]
  refine ⟨17521992189560354918419957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23362656252747139891226609 17521992189560354918419957)
  ·
    refine ⟨1642686767771283273601871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17521992189560354918419957 1642686767771283273601871)
    ·
      refine ⟨2464030151656924910402807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1642686767771283273601871 2464030151656924910402807)
      ·
        refine ⟨3696045227485387365604211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2464030151656924910402807 3696045227485387365604211)
        ·
          refine ⟨5544067841228081048406317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3696045227485387365604211 5544067841228081048406317)
          ·
            refine ⟨2079025440460530393152369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5544067841228081048406317 2079025440460530393152369)
            ·
              refine ⟨1559269080345397794864277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2079025440460530393152369 1559269080345397794864277)
              ·
                refine ⟨73090738141190521634263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1559269080345397794864277 73090738141190521634263)
                ·
                  rfl

theorem cell21_960820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 2, 6].length) (baseStart_960820 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_960820 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_960820 prefixEnd_960820 := by exact prefixLift 960820
  have htrace : WordTrace (prefixWord ++ tailWord_960820) baseStart_960820 baseEnd_960820 := by
    simpa [prefixWord, tailWord_960820, baseEnd_960820] using wordTrace_append hprefix tailTrace_960820
  have hstable : (prefixWord ++ tailWord_960820).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960820).length < 2 ^ (prefixWord ++ tailWord_960820).sum := by decide
  have hdescent : baseEnd_960820 < baseStart_960820 := by decide
  rcases family_descends (prefixWord ++ tailWord_960820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960893 : List Nat := [1, 4, 1, 1, 2, 3, 1, 1, 7]
def baseStart_960893 : Nat := 118140960795 + 960893 * 2 ^ 59
def prefixEnd_960893 : Nat := 4983230072969 + 3 ^ 40 * 960893 * 2
def baseEnd_960893 : Nat := 219288874018139660185973

theorem tailTrace_960893 : CollatzResearch.WordTrace tailWord_960893 prefixEnd_960893 219288874018139660185973 := by
  unfold tailWord_960893
  simp only [CollatzResearch.WordTrace]
  refine ⟨35046646907856243304247333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23364431271904162202831555 35046646907856243304247333)
  ·
    refine ⟨6571246295223045619546375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35046646907856243304247333 6571246295223045619546375)
    ·
      refine ⟨9856869442834568429319563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6571246295223045619546375 9856869442834568429319563)
      ·
        refine ⟨14785304164251852643979345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9856869442834568429319563 14785304164251852643979345)
        ·
          refine ⟨11088978123188889482984509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14785304164251852643979345 11088978123188889482984509)
          ·
            refine ⟨4158366796195833556119191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11088978123188889482984509 4158366796195833556119191)
            ·
              refine ⟨6237550194293750334178787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4158366796195833556119191 6237550194293750334178787)
              ·
                refine ⟨9356325291440625501268181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6237550194293750334178787 9356325291440625501268181)
                ·
                  refine ⟨219288874018139660185973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9356325291440625501268181 219288874018139660185973)
                  ·
                    rfl

theorem cell21_960893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 1, 7].length) (baseStart_960893 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_960893 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_960893 prefixEnd_960893 := by exact prefixLift 960893
  have htrace : WordTrace (prefixWord ++ tailWord_960893) baseStart_960893 baseEnd_960893 := by
    simpa [prefixWord, tailWord_960893, baseEnd_960893] using wordTrace_append hprefix tailTrace_960893
  have hstable : (prefixWord ++ tailWord_960893).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960893).length < 2 ^ (prefixWord ++ tailWord_960893).sum := by decide
  have hdescent : baseEnd_960893 < baseStart_960893 := by decide
  rcases family_descends (prefixWord ++ tailWord_960893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960972 : List Nat := [2, 2, 1, 4, 4, 1, 7]
def baseStart_960972 : Nat := 118140960795 + 960972 * 2 ^ 59
def prefixEnd_960972 : Nat := 4983230072969 + 3 ^ 40 * 960972 * 2
def baseEnd_960972 : Nat := 24367433654939230929905

theorem tailTrace_960972 : CollatzResearch.WordTrace tailWord_960972 prefixEnd_960972 24367433654939230929905 := by
  unfold tailWord_960972
  simp only [CollatzResearch.WordTrace]
  refine ⟨17524764137285019898186585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23366352183046693197582113 17524764137285019898186585)
  ·
    refine ⟨13143573102963764923639939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17524764137285019898186585 13143573102963764923639939)
    ·
      refine ⟨19715359654445647385459909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13143573102963764923639939 19715359654445647385459909)
      ·
        refine ⟨3696629935208558884773733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19715359654445647385459909 3696629935208558884773733)
        ·
          refine ⟨693118112851604790895075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3696629935208558884773733 693118112851604790895075)
          ·
            refine ⟨1039677169277407186342613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 693118112851604790895075 1039677169277407186342613)
            ·
              refine ⟨24367433654939230929905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1039677169277407186342613 24367433654939230929905)
              ·
                rfl

theorem cell21_960972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 7].length) (baseStart_960972 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_960972 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_960972 prefixEnd_960972 := by exact prefixLift 960972
  have htrace : WordTrace (prefixWord ++ tailWord_960972) baseStart_960972 baseEnd_960972 := by
    simpa [prefixWord, tailWord_960972, baseEnd_960972] using wordTrace_append hprefix tailTrace_960972
  have hstable : (prefixWord ++ tailWord_960972).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960972).length < 2 ^ (prefixWord ++ tailWord_960972).sum := by decide
  have hdescent : baseEnd_960972 < baseStart_960972 := by decide
  rcases family_descends (prefixWord ++ tailWord_960972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961031 : List Nat := [1, 1, 4, 3, 4, 8]
def baseStart_961031 : Nat := 118140960795 + 961031 * 2 ^ 59
def prefixEnd_961031 : Nat := 4983230072969 + 3 ^ 40 * 961031 * 2
def baseEnd_961031 : Nat := 8122976574010447662433

theorem tailTrace_961031 : CollatzResearch.WordTrace tailWord_961031 prefixEnd_961031 8122976574010447662433 := by
  unfold tailWord_961031
  simp only [CollatzResearch.WordTrace]
  refine ⟨35051680181356292872770947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23367786787570861915180631 35051680181356292872770947)
  ·
    refine ⟨52577520272034439309156421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35051680181356292872770947 52577520272034439309156421)
    ·
      refine ⟨9858285051006457370466829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52577520272034439309156421 9858285051006457370466829)
      ·
        refine ⟨3696856894127421513925061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9858285051006457370466829 3696856894127421513925061)
        ·
          refine ⟨693160667648891533860949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3696856894127421513925061 693160667648891533860949)
          ·
            refine ⟨8122976574010447662433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 693160667648891533860949 8122976574010447662433)
            ·
              rfl

theorem cell21_961031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 8].length) (baseStart_961031 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_961031 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_961031 prefixEnd_961031 := by exact prefixLift 961031
  have htrace : WordTrace (prefixWord ++ tailWord_961031) baseStart_961031 baseEnd_961031 := by
    simpa [prefixWord, tailWord_961031, baseEnd_961031] using wordTrace_append hprefix tailTrace_961031
  have hstable : (prefixWord ++ tailWord_961031).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961031).length < 2 ^ (prefixWord ++ tailWord_961031).sum := by decide
  have hdescent : baseEnd_961031 < baseStart_961031 := by decide
  rcases family_descends (prefixWord ++ tailWord_961031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961037 : List Nat := [1, 7, 1, 1, 1, 2, 1, 4, 3]
def baseStart_961037 : Nat := 118140960795 + 961037 * 2 ^ 59
def prefixEnd_961037 : Nat := 4983230072969 + 3 ^ 40 * 961037 * 2
def baseEnd_961037 : Nat := 219321736780027409785679

theorem tailTrace_961037 : CollatzResearch.WordTrace tailWord_961037 prefixEnd_961037 219321736780027409785679 := by
  unfold tailWord_961037
  simp only [CollatzResearch.WordTrace]
  refine ⟨35051899019334555897489365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23367932679556370598326243 35051899019334555897489365)
  ·
    refine ⟨821528883265653653847407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 35051899019334555897489365 821528883265653653847407)
    ·
      refine ⟨1232293324898480480771111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 821528883265653653847407 1232293324898480480771111)
      ·
        refine ⟨1848439987347720721156667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1232293324898480480771111 1848439987347720721156667)
        ·
          refine ⟨2772659981021581081735001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1848439987347720721156667 2772659981021581081735001)
          ·
            refine ⟨2079494985766185811301251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2772659981021581081735001 2079494985766185811301251)
            ·
              refine ⟨3119242478649278716951877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2079494985766185811301251 3119242478649278716951877)
              ·
                refine ⟨584857964746739759428477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3119242478649278716951877 584857964746739759428477)
                ·
                  refine ⟨219321736780027409785679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 584857964746739759428477 219321736780027409785679)
                  ·
                    rfl

theorem cell21_961037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_961037 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_961037 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_961037 prefixEnd_961037 := by exact prefixLift 961037
  have htrace : WordTrace (prefixWord ++ tailWord_961037) baseStart_961037 baseEnd_961037 := by
    simpa [prefixWord, tailWord_961037, baseEnd_961037] using wordTrace_append hprefix tailTrace_961037
  have hstable : (prefixWord ++ tailWord_961037).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961037).length < 2 ^ (prefixWord ++ tailWord_961037).sum := by decide
  have hdescent : baseEnd_961037 < baseStart_961037 := by decide
  rcases family_descends (prefixWord ++ tailWord_961037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961045 : List Nat := [1, 3, 2, 1, 3, 1, 2, 3, 5]
def baseStart_961045 : Nat := 118140960795 + 961045 * 2 ^ 59
def prefixEnd_961045 : Nat := 4983230072969 + 3 ^ 40 * 961045 * 2
def baseEnd_961045 : Nat := 219323562489021173652329

theorem tailTrace_961045 : CollatzResearch.WordTrace tailWord_961045 prefixEnd_961045 219323562489021173652329 := by
  unfold tailWord_961045
  simp only [CollatzResearch.WordTrace]
  refine ⟨35052190803305573263780589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23368127202203715509187059 35052190803305573263780589)
  ·
    refine ⟨13144571551239589973917721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35052190803305573263780589 13144571551239589973917721)
    ·
      refine ⟨9858428663429692480438291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13144571551239589973917721 9858428663429692480438291)
      ·
        refine ⟨14787642995144538720657437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9858428663429692480438291 14787642995144538720657437)
        ·
          refine ⟨5545366123179202020246539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14787642995144538720657437 5545366123179202020246539)
          ·
            refine ⟨8318049184768803030369809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5545366123179202020246539 8318049184768803030369809)
            ·
              refine ⟨6238536888576602272777357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8318049184768803030369809 6238536888576602272777357)
              ·
                refine ⟨2339451333216225852291509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6238536888576602272777357 2339451333216225852291509)
                ·
                  refine ⟨219323562489021173652329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2339451333216225852291509 219323562489021173652329)
                  ·
                    rfl

theorem cell21_961045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 3, 5].length) (baseStart_961045 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_961045 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_961045 prefixEnd_961045 := by exact prefixLift 961045
  have htrace : WordTrace (prefixWord ++ tailWord_961045) baseStart_961045 baseEnd_961045 := by
    simpa [prefixWord, tailWord_961045, baseEnd_961045] using wordTrace_append hprefix tailTrace_961045
  have hstable : (prefixWord ++ tailWord_961045).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961045).length < 2 ^ (prefixWord ++ tailWord_961045).sum := by decide
  have hdescent : baseEnd_961045 < baseStart_961045 := by decide
  rcases family_descends (prefixWord ++ tailWord_961045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961093 : List Nat := [1, 3, 1, 1, 1, 7, 1, 2, 4]
def baseStart_961093 : Nat := 118140960795 + 961093 * 2 ^ 59
def prefixEnd_961093 : Nat := 4983230072969 + 3 ^ 40 * 961093 * 2
def baseEnd_961093 : Nat := 219334516742983756852231

theorem tailTrace_961093 : CollatzResearch.WordTrace tailWord_961093 prefixEnd_961093 219334516742983756852231 := by
  unfold tailWord_961093
  simp only [CollatzResearch.WordTrace]
  refine ⟨35053941507131677461527933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23369294338087784974351955 35053941507131677461527933)
  ·
    refine ⟨13145228065174379048072975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35053941507131677461527933 13145228065174379048072975)
    ·
      refine ⟨19717842097761568572109463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13145228065174379048072975 19717842097761568572109463)
      ·
        refine ⟨29576763146642352858164195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19717842097761568572109463 29576763146642352858164195)
        ·
          refine ⟨44365144719963529287246293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29576763146642352858164195 44365144719963529287246293)
          ·
            refine ⟨1039808079374145217669835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 44365144719963529287246293 1039808079374145217669835)
            ·
              refine ⟨1559712119061217826504753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1039808079374145217669835 1559712119061217826504753)
              ·
                refine ⟨1169784089295913369878565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1559712119061217826504753 1169784089295913369878565)
                ·
                  refine ⟨219334516742983756852231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1169784089295913369878565 219334516742983756852231)
                  ·
                    rfl

theorem cell21_961093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 1, 2, 4].length) (baseStart_961093 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_961093 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_961093 prefixEnd_961093 := by exact prefixLift 961093
  have htrace : WordTrace (prefixWord ++ tailWord_961093) baseStart_961093 baseEnd_961093 := by
    simpa [prefixWord, tailWord_961093, baseEnd_961093] using wordTrace_append hprefix tailTrace_961093
  have hstable : (prefixWord ++ tailWord_961093).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961093).length < 2 ^ (prefixWord ++ tailWord_961093).sum := by decide
  have hdescent : baseEnd_961093 < baseStart_961093 := by decide
  rcases family_descends (prefixWord ++ tailWord_961093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961121 : List Nat := [1, 2, 3, 1, 1, 4, 2, 2, 5]
def baseStart_961121 : Nat := 118140960795 + 961121 * 2 ^ 59
def prefixEnd_961121 : Nat := 4983230072969 + 3 ^ 40 * 961121 * 2
def baseEnd_961121 : Nat := 219340906724461930385507

theorem tailTrace_961121 : CollatzResearch.WordTrace tailWord_961121 prefixEnd_961121 219340906724461930385507 := by
  unfold tailWord_961121
  simp only [CollatzResearch.WordTrace]
  refine ⟨35054962751030238243547217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23369975167353492162364811 35054962751030238243547217)
  ·
    refine ⟨26291222063272678682660413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35054962751030238243547217 26291222063272678682660413)
    ·
      refine ⟨9859208273727254505997655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26291222063272678682660413 9859208273727254505997655)
      ·
        refine ⟨14788812410590881758996483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9859208273727254505997655 14788812410590881758996483)
        ·
          refine ⟨22183218615886322638494725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14788812410590881758996483 22183218615886322638494725)
          ·
            refine ⟨4159353490478685494717761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22183218615886322638494725 4159353490478685494717761)
            ·
              refine ⟨3119515117859014121038321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4159353490478685494717761 3119515117859014121038321)
              ·
                refine ⟨2339636338394260590778741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3119515117859014121038321 2339636338394260590778741)
                ·
                  refine ⟨219340906724461930385507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2339636338394260590778741 219340906724461930385507)
                  ·
                    rfl

theorem cell21_961121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 2, 5].length) (baseStart_961121 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_961121 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_961121 prefixEnd_961121 := by exact prefixLift 961121
  have htrace : WordTrace (prefixWord ++ tailWord_961121) baseStart_961121 baseEnd_961121 := by
    simpa [prefixWord, tailWord_961121, baseEnd_961121] using wordTrace_append hprefix tailTrace_961121
  have hstable : (prefixWord ++ tailWord_961121).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961121).length < 2 ^ (prefixWord ++ tailWord_961121).sum := by decide
  have hdescent : baseEnd_961121 < baseStart_961121 := by decide
  rcases family_descends (prefixWord ++ tailWord_961121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961135 : List Nat := [1, 1, 2, 1, 3, 2, 3, 2, 6]
def baseStart_961135 : Nat := 118140960795 + 961135 * 2 ^ 59
def prefixEnd_961135 : Nat := 4983230072969 + 3 ^ 40 * 961135 * 2
def baseEnd_961135 : Nat := 219344101715201017152145

theorem tailTrace_961135 : CollatzResearch.WordTrace tailWord_961135 prefixEnd_961135 219344101715201017152145 := by
  unfold tailWord_961135
  simp only [CollatzResearch.WordTrace]
  refine ⟨35055473372979518634556859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23370315581986345756371239 35055473372979518634556859)
  ·
    refine ⟨52583210059469277951835289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35055473372979518634556859 52583210059469277951835289)
    ·
      refine ⟨39437407544601958463876467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52583210059469277951835289 39437407544601958463876467)
      ·
        refine ⟨59156111316902937695814701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39437407544601958463876467 59156111316902937695814701)
        ·
          refine ⟨22183541743838601635930513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59156111316902937695814701 22183541743838601635930513)
          ·
            refine ⟨16637656307878951226947885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22183541743838601635930513 16637656307878951226947885)
            ·
              refine ⟨6239121115454606710105457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16637656307878951226947885 6239121115454606710105457)
              ·
                refine ⟨4679340836590955032579093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6239121115454606710105457 4679340836590955032579093)
                ·
                  refine ⟨219344101715201017152145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4679340836590955032579093 219344101715201017152145)
                  ·
                    rfl

theorem cell21_961135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 2, 6].length) (baseStart_961135 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_961135 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_961135 prefixEnd_961135 := by exact prefixLift 961135
  have htrace : WordTrace (prefixWord ++ tailWord_961135) baseStart_961135 baseEnd_961135 := by
    simpa [prefixWord, tailWord_961135, baseEnd_961135] using wordTrace_append hprefix tailTrace_961135
  have hstable : (prefixWord ++ tailWord_961135).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961135).length < 2 ^ (prefixWord ++ tailWord_961135).sum := by decide
  have hdescent : baseEnd_961135 < baseStart_961135 := by decide
  rcases family_descends (prefixWord ++ tailWord_961135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961206 : List Nat := [5, 1, 3, 1, 2, 2, 2, 2, 3]
def baseStart_961206 : Nat := 118140960795 + 961206 * 2 ^ 59
def prefixEnd_961206 : Nat := 4983230072969 + 3 ^ 40 * 961206 * 2
def baseEnd_961206 : Nat := 219360304882520671468667

theorem tailTrace_961206 : CollatzResearch.WordTrace tailWord_961206 prefixEnd_961206 219360304882520671468667 := by
  unfold tailWord_961206
  simp only [CollatzResearch.WordTrace]
  refine ⟨2191128934732643610024467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23372041970481531840260981 2191128934732643610024467)
  ·
    refine ⟨3286693402098965415036701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2191128934732643610024467 3286693402098965415036701)
    ·
      refine ⟨1232510025787112030638763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3286693402098965415036701 1232510025787112030638763)
      ·
        refine ⟨1848765038680668045958145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1232510025787112030638763 1848765038680668045958145)
        ·
          refine ⟨1386573779010501034468609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1848765038680668045958145 1386573779010501034468609)
          ·
            refine ⟨1039930334257875775851457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1386573779010501034468609 1039930334257875775851457)
            ·
              refine ⟨779947750693406831888593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1039930334257875775851457 779947750693406831888593)
              ·
                refine ⟨584960813020055123916445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 779947750693406831888593 584960813020055123916445)
                ·
                  refine ⟨219360304882520671468667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 584960813020055123916445 219360304882520671468667)
                  ·
                    rfl

theorem cell21_961206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 2, 2, 3].length) (baseStart_961206 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_961206 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_961206 prefixEnd_961206 := by exact prefixLift 961206
  have htrace : WordTrace (prefixWord ++ tailWord_961206) baseStart_961206 baseEnd_961206 := by
    simpa [prefixWord, tailWord_961206, baseEnd_961206] using wordTrace_append hprefix tailTrace_961206
  have hstable : (prefixWord ++ tailWord_961206).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961206).length < 2 ^ (prefixWord ++ tailWord_961206).sum := by decide
  have hdescent : baseEnd_961206 < baseStart_961206 := by decide
  rcases family_descends (prefixWord ++ tailWord_961206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961217 : List Nat := [1, 2, 6, 2, 1, 2, 1, 6]
def baseStart_961217 : Nat := 118140960795 + 961217 * 2 ^ 59
def prefixEnd_961217 : Nat := 4983230072969 + 3 ^ 40 * 961217 * 2
def baseEnd_961217 : Nat := 73120938410795698928437

theorem tailTrace_961217 : CollatzResearch.WordTrace tailWord_961217 prefixEnd_961217 73120938410795698928437 := by
  unfold tailWord_961217
  simp only [CollatzResearch.WordTrace]
  refine ⟨35058464158682446639041905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23372309439121631092694603 35058464158682446639041905)
  ·
    refine ⟨26293848119011834979281429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35058464158682446639041905 26293848119011834979281429)
    ·
      refine ⟨1232524130578679764653817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 26293848119011834979281429 1232524130578679764653817)
      ·
        refine ⟨924393097934009823490363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1232524130578679764653817 924393097934009823490363)
        ·
          refine ⟨1386589646901014735235545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 924393097934009823490363 1386589646901014735235545)
          ·
            refine ⟨1039942235175761051426659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1386589646901014735235545 1039942235175761051426659)
            ·
              refine ⟨1559913352763641577139989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1039942235175761051426659 1559913352763641577139989)
              ·
                refine ⟨73120938410795698928437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1559913352763641577139989 73120938410795698928437)
                ·
                  rfl

theorem cell21_961217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 1, 6].length) (baseStart_961217 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_961217 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_961217 prefixEnd_961217 := by exact prefixLift 961217
  have htrace : WordTrace (prefixWord ++ tailWord_961217) baseStart_961217 baseEnd_961217 := by
    simpa [prefixWord, tailWord_961217, baseEnd_961217] using wordTrace_append hprefix tailTrace_961217
  have hstable : (prefixWord ++ tailWord_961217).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961217).length < 2 ^ (prefixWord ++ tailWord_961217).sum := by decide
  have hdescent : baseEnd_961217 < baseStart_961217 := by decide
  rcases family_descends (prefixWord ++ tailWord_961217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961338 : List Nat := [3, 1, 1, 1, 6, 2, 2, 1, 4]
def baseStart_961338 : Nat := 118140960795 + 961338 * 2 ^ 59
def prefixEnd_961338 : Nat := 4983230072969 + 3 ^ 40 * 961338 * 2
def baseEnd_961338 : Nat := 219390429080917775268397

theorem tailTrace_961338 : CollatzResearch.WordTrace tailWord_961338 prefixEnd_961338 219390429080917775268397 := by
  unfold tailWord_961338
  simp only [CollatzResearch.WordTrace]
  refine ⟨8765719347811021076049167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23375251594162722869464445 8765719347811021076049167)
  ·
    refine ⟨13148579021716531614073751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8765719347811021076049167 13148579021716531614073751)
    ·
      refine ⟨19722868532574797421110627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13148579021716531614073751 19722868532574797421110627)
      ·
        refine ⟨29584302798862196131665941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19722868532574797421110627 29584302798862196131665941)
        ·
          refine ⟨1386764193696665443671841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 29584302798862196131665941 1386764193696665443671841)
          ·
            refine ⟨1040073145272499082753881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1386764193696665443671841 1040073145272499082753881)
            ·
              refine ⟨780054858954374312065411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1040073145272499082753881 780054858954374312065411)
              ·
                refine ⟨1170082288431561468098117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 780054858954374312065411 1170082288431561468098117)
                ·
                  refine ⟨219390429080917775268397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1170082288431561468098117 219390429080917775268397)
                  ·
                    rfl

theorem cell21_961338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 2, 1, 4].length) (baseStart_961338 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_961338 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_961338 prefixEnd_961338 := by exact prefixLift 961338
  have htrace : WordTrace (prefixWord ++ tailWord_961338) baseStart_961338 baseEnd_961338 := by
    simpa [prefixWord, tailWord_961338, baseEnd_961338] using wordTrace_append hprefix tailTrace_961338
  have hstable : (prefixWord ++ tailWord_961338).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961338).length < 2 ^ (prefixWord ++ tailWord_961338).sum := by decide
  have hdescent : baseEnd_961338 < baseStart_961338 := by decide
  rcases family_descends (prefixWord ++ tailWord_961338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961380 : List Nat := [2, 3, 1, 1, 4, 1, 1, 4, 4]
def baseStart_961380 : Nat := 118140960795 + 961380 * 2 ^ 59
def prefixEnd_961380 : Nat := 4983230072969 + 3 ^ 40 * 961380 * 2
def baseEnd_961380 : Nat := 219400014053135035568311

theorem tailTrace_961380 : CollatzResearch.WordTrace tailWord_961380 prefixEnd_961380 219400014053135035568311 := by
  unfold tailWord_961380
  simp only [CollatzResearch.WordTrace]
  refine ⟨17532204628545962738612797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23376272838061283651483729 17532204628545962738612797)
  ·
    refine ⟨6574576735704736026979799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17532204628545962738612797 6574576735704736026979799)
    ·
      refine ⟨9861865103557104040469699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6574576735704736026979799 9861865103557104040469699)
      ·
        refine ⟨14792797655335656060704549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9861865103557104040469699 14792797655335656060704549)
        ·
          refine ⟨2773649560375435511382103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14792797655335656060704549 2773649560375435511382103)
          ·
            refine ⟨4160474340563153267073155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2773649560375435511382103 4160474340563153267073155)
            ·
              refine ⟨6240711510844729900609733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4160474340563153267073155 6240711510844729900609733)
              ·
                refine ⟨1170133408283386856364325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6240711510844729900609733 1170133408283386856364325)
                ·
                  refine ⟨219400014053135035568311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1170133408283386856364325 219400014053135035568311)
                  ·
                    rfl

theorem cell21_961380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 4, 4].length) (baseStart_961380 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_961380 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_961380 prefixEnd_961380 := by exact prefixLift 961380
  have htrace : WordTrace (prefixWord ++ tailWord_961380) baseStart_961380 baseEnd_961380 := by
    simpa [prefixWord, tailWord_961380, baseEnd_961380] using wordTrace_append hprefix tailTrace_961380
  have hstable : (prefixWord ++ tailWord_961380).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961380).length < 2 ^ (prefixWord ++ tailWord_961380).sum := by decide
  have hdescent : baseEnd_961380 < baseStart_961380 := by decide
  rcases family_descends (prefixWord ++ tailWord_961380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961383 : List Nat := [1, 1, 5, 1, 2, 2, 4, 2, 3]
def baseStart_961383 : Nat := 118140960795 + 961383 * 2 ^ 59
def prefixEnd_961383 : Nat := 4983230072969 + 3 ^ 40 * 961383 * 2
def baseEnd_961383 : Nat := 219400698694007697018305

theorem tailTrace_961383 : CollatzResearch.WordTrace tailWord_961383 prefixEnd_961383 219400698694007697018305 := by
  unfold tailWord_961383
  simp only [CollatzResearch.WordTrace]
  refine ⟨35064518676081056989584803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23376345784054037993056535 35064518676081056989584803)
  ·
    refine ⟨52596778014121585484377205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35064518676081056989584803 52596778014121585484377205)
    ·
      refine ⟨4930947938823898639160363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 52596778014121585484377205 4930947938823898639160363)
      ·
        refine ⟨7396421908235847958740545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4930947938823898639160363 7396421908235847958740545)
        ·
          refine ⟨5547316431176885969055409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7396421908235847958740545 5547316431176885969055409)
          ·
            refine ⟨4160487323382664476791557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5547316431176885969055409 4160487323382664476791557)
            ·
              refine ⟨780091373134249589398417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4160487323382664476791557 780091373134249589398417)
              ·
                refine ⟨585068529850687192048813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 780091373134249589398417 585068529850687192048813)
                ·
                  refine ⟨219400698694007697018305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 585068529850687192048813 219400698694007697018305)
                  ·
                    rfl

theorem cell21_961383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 4, 2, 3].length) (baseStart_961383 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_961383 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_961383 prefixEnd_961383 := by exact prefixLift 961383
  have htrace : WordTrace (prefixWord ++ tailWord_961383) baseStart_961383 baseEnd_961383 := by
    simpa [prefixWord, tailWord_961383, baseEnd_961383] using wordTrace_append hprefix tailTrace_961383
  have hstable : (prefixWord ++ tailWord_961383).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961383).length < 2 ^ (prefixWord ++ tailWord_961383).sum := by decide
  have hdescent : baseEnd_961383 < baseStart_961383 := by decide
  rcases family_descends (prefixWord ++ tailWord_961383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961394 : List Nat := [3, 2, 1, 2, 1, 1, 5, 6]
def baseStart_961394 : Nat := 118140960795 + 961394 * 2 ^ 59
def prefixEnd_961394 : Nat := 4983230072969 + 3 ^ 40 * 961394 * 2
def baseEnd_961394 : Nat := 73134403014624707444983

theorem tailTrace_961394 : CollatzResearch.WordTrace tailWord_961394 prefixEnd_961394 73134403014624707444983 := by
  unfold tailWord_961394
  simp only [CollatzResearch.WordTrace]
  refine ⟨8766229969760301467058809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23376613252694137245490157 8766229969760301467058809)
  ·
    refine ⟨6574672477320226100294107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8766229969760301467058809 6574672477320226100294107)
    ·
      refine ⟨9862008715980339150441161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6574672477320226100294107 9862008715980339150441161)
      ·
        refine ⟨7396506536985254362830871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9862008715980339150441161 7396506536985254362830871)
        ·
          refine ⟨11094759805477881544246307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7396506536985254362830871 11094759805477881544246307)
          ·
            refine ⟨16642139708216822316369461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11094759805477881544246307 16642139708216822316369461)
            ·
              refine ⟨1560200597645327092159637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16642139708216822316369461 1560200597645327092159637)
              ·
                refine ⟨73134403014624707444983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1560200597645327092159637 73134403014624707444983)
                ·
                  rfl

theorem cell21_961394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 5, 6].length) (baseStart_961394 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_961394 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_961394 prefixEnd_961394 := by exact prefixLift 961394
  have htrace : WordTrace (prefixWord ++ tailWord_961394) baseStart_961394 baseEnd_961394 := by
    simpa [prefixWord, tailWord_961394, baseEnd_961394] using wordTrace_append hprefix tailTrace_961394
  have hstable : (prefixWord ++ tailWord_961394).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961394).length < 2 ^ (prefixWord ++ tailWord_961394).sum := by decide
  have hdescent : baseEnd_961394 < baseStart_961394 := by decide
  rcases family_descends (prefixWord ++ tailWord_961394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961442 : List Nat := [3, 3, 1, 2, 2, 2, 2, 1, 5]
def baseStart_961442 : Nat := 118140960795 + 961442 * 2 ^ 59
def prefixEnd_961442 : Nat := 4983230072969 + 3 ^ 40 * 961442 * 2
def baseEnd_961442 : Nat := 219414163297836705534851

theorem tailTrace_961442 : CollatzResearch.WordTrace tailWord_961442 prefixEnd_961442 219414163297836705534851 := by
  unfold tailWord_961442
  simp only [CollatzResearch.WordTrace]
  refine ⟨8766667645716827516495645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23377780388578206710655053 8766667645716827516495645)
  ·
    refine ⟨3287500367143810318685867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8766667645716827516495645 3287500367143810318685867)
    ·
      refine ⟨4931250550715715478028801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3287500367143810318685867 4931250550715715478028801)
      ·
        refine ⟨3698437913036786608521601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4931250550715715478028801 3698437913036786608521601)
        ·
          refine ⟨2773828434777589956391201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3698437913036786608521601 2773828434777589956391201)
          ·
            refine ⟨2080371326083192467293401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2773828434777589956391201 2080371326083192467293401)
            ·
              refine ⟨1560278494562394350470051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2080371326083192467293401 1560278494562394350470051)
              ·
                refine ⟨2340417741843591525705077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1560278494562394350470051 2340417741843591525705077)
                ·
                  refine ⟨219414163297836705534851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2340417741843591525705077 219414163297836705534851)
                  ·
                    rfl

theorem cell21_961442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 2, 1, 5].length) (baseStart_961442 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_961442 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_961442 prefixEnd_961442 := by exact prefixLift 961442
  have htrace : WordTrace (prefixWord ++ tailWord_961442) baseStart_961442 baseEnd_961442 := by
    simpa [prefixWord, tailWord_961442, baseEnd_961442] using wordTrace_append hprefix tailTrace_961442
  have hstable : (prefixWord ++ tailWord_961442).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961442).length < 2 ^ (prefixWord ++ tailWord_961442).sum := by decide
  have hdescent : baseEnd_961442 < baseStart_961442 := by decide
  rcases family_descends (prefixWord ++ tailWord_961442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961470 : List Nat := [4, 2, 1, 1, 1, 2, 3, 7]
def baseStart_961470 : Nat := 118140960795 + 961470 * 2 ^ 59
def prefixEnd_961470 : Nat := 4983230072969 + 3 ^ 40 * 961470 * 2
def baseEnd_961470 : Nat := 73140184426438293022709

theorem tailTrace_961470 : CollatzResearch.WordTrace tailWord_961470 prefixEnd_961470 73140184426438293022709 := by
  unfold tailWord_961470
  simp only [CollatzResearch.WordTrace]
  refine ⟨4383461478345733856000233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23378461217843913898667909 4383461478345733856000233)
  ·
    refine ⟨3287596108759300392000175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4383461478345733856000233 3287596108759300392000175)
    ·
      refine ⟨4931394163138950588000263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3287596108759300392000175 4931394163138950588000263)
      ·
        refine ⟨7397091244708425882000395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4931394163138950588000263 7397091244708425882000395)
        ·
          refine ⟨11095636867062638823000593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7397091244708425882000395 11095636867062638823000593)
          ·
            refine ⟨8321727650296979117250445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11095636867062638823000593 8321727650296979117250445)
            ·
              refine ⟨3120647868861367168968917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8321727650296979117250445 3120647868861367168968917)
              ·
                refine ⟨73140184426438293022709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3120647868861367168968917 73140184426438293022709)
                ·
                  rfl

theorem cell21_961470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 7].length) (baseStart_961470 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_961470 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_961470 prefixEnd_961470 := by exact prefixLift 961470
  have htrace : WordTrace (prefixWord ++ tailWord_961470) baseStart_961470 baseEnd_961470 := by
    simpa [prefixWord, tailWord_961470, baseEnd_961470] using wordTrace_append hprefix tailTrace_961470
  have hstable : (prefixWord ++ tailWord_961470).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961470).length < 2 ^ (prefixWord ++ tailWord_961470).sum := by decide
  have hdescent : baseEnd_961470 < baseStart_961470 := by decide
  rcases family_descends (prefixWord ++ tailWord_961470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961529 : List Nat := [1, 2, 1, 3, 1, 3, 1, 9]
def baseStart_961529 : Nat := 118140960795 + 961529 * 2 ^ 59
def prefixEnd_961529 : Nat := 4983230072969 + 3 ^ 40 * 961529 * 2
def baseEnd_961529 : Nat := 73144672627714629194891

theorem tailTrace_961529 : CollatzResearch.WordTrace tailWord_961529 prefixEnd_961529 73144672627714629194891 := by
  unfold tailWord_961529
  simp only [CollatzResearch.WordTrace]
  refine ⟨35069843733552123924399641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23379895822368082616266427 35069843733552123924399641)
  ·
    refine ⟨26302382800164092943299731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35069843733552123924399641 26302382800164092943299731)
    ·
      refine ⟨39453574200246139414949597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26302382800164092943299731 39453574200246139414949597)
      ·
        refine ⟨14795090325092302280606099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39453574200246139414949597 14795090325092302280606099)
        ·
          refine ⟨22192635487638453420909149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14795090325092302280606099 22192635487638453420909149)
          ·
            refine ⟨8322238307864420032840931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22192635487638453420909149 8322238307864420032840931)
            ·
              refine ⟨12483357461796630049261397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8322238307864420032840931 12483357461796630049261397)
              ·
                refine ⟨73144672627714629194891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12483357461796630049261397 73144672627714629194891)
                ·
                  rfl

theorem cell21_961529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 9].length) (baseStart_961529 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_961529 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_961529 prefixEnd_961529 := by exact prefixLift 961529
  have htrace : WordTrace (prefixWord ++ tailWord_961529) baseStart_961529 baseEnd_961529 := by
    simpa [prefixWord, tailWord_961529, baseEnd_961529] using wordTrace_append hprefix tailTrace_961529
  have hstable : (prefixWord ++ tailWord_961529).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961529).length < 2 ^ (prefixWord ++ tailWord_961529).sum := by decide
  have hdescent : baseEnd_961529 < baseStart_961529 := by decide
  rcases family_descends (prefixWord ++ tailWord_961529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961639 : List Nat := [1, 1, 5, 1, 1, 5, 2, 5]
def baseStart_961639 : Nat := 118140960795 + 961639 * 2 ^ 59
def prefixEnd_961639 : Nat := 4983230072969 + 3 ^ 40 * 961639 * 2
def baseEnd_961639 : Nat := 73153040460602713583705

theorem tailTrace_961639 : CollatzResearch.WordTrace tailWord_961639 prefixEnd_961639 73153040460602713583705 := by
  unfold tailWord_961639
  simp only [CollatzResearch.WordTrace]
  refine ⟨35073855763153612710903971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23382570508769075140602647 35073855763153612710903971)
  ·
    refine ⟨52610783644730419066355957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35073855763153612710903971 52610783644730419066355957)
    ·
      refine ⟨4932260966693476787470871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 52610783644730419066355957 4932260966693476787470871)
      ·
        refine ⟨7398391450040215181206307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4932260966693476787470871 7398391450040215181206307)
        ·
          refine ⟨11097587175060322771809461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7398391450040215181206307 11097587175060322771809461)
          ·
            refine ⟨1040398797661905259857137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11097587175060322771809461 1040398797661905259857137)
            ·
              refine ⟨780299098246428944892853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1040398797661905259857137 780299098246428944892853)
              ·
                refine ⟨73153040460602713583705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 780299098246428944892853 73153040460602713583705)
                ·
                  rfl

theorem cell21_961639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 2, 5].length) (baseStart_961639 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_961639 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_961639 prefixEnd_961639 := by exact prefixLift 961639
  have htrace : WordTrace (prefixWord ++ tailWord_961639) baseStart_961639 baseEnd_961639 := by
    simpa [prefixWord, tailWord_961639, baseEnd_961639] using wordTrace_append hprefix tailTrace_961639
  have hstable : (prefixWord ++ tailWord_961639).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961639).length < 2 ^ (prefixWord ++ tailWord_961639).sum := by decide
  have hdescent : baseEnd_961639 < baseStart_961639 := by decide
  rcases family_descends (prefixWord ++ tailWord_961639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961662 : List Nat := [4, 2, 4, 1, 1, 1, 3, 2, 3]
def baseStart_961662 : Nat := 118140960795 + 961662 * 2 ^ 59
def prefixEnd_961662 : Nat := 4983230072969 + 3 ^ 40 * 961662 * 2
def baseEnd_961662 : Nat := 219464370295165211867735

theorem tailTrace_961662 : CollatzResearch.WordTrace tailWord_961662 prefixEnd_961662 219464370295165211867735 := by
  unfold tailWord_961662
  simp only [CollatzResearch.WordTrace]
  refine ⟨4384336830258785954873905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23383129761380191759327493 4384336830258785954873905)
  ·
    refine ⟨3288252622694089466155429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4384336830258785954873905 3288252622694089466155429)
    ·
      refine ⟨616547366755141774904143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3288252622694089466155429 616547366755141774904143)
      ·
        refine ⟨924821050132712662356215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 616547366755141774904143 924821050132712662356215)
        ·
          refine ⟨1387231575199068993534323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 924821050132712662356215 1387231575199068993534323)
          ·
            refine ⟨2080847362798603490301485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1387231575199068993534323 2080847362798603490301485)
            ·
              refine ⟨780317761049476308863057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2080847362798603490301485 780317761049476308863057)
              ·
                refine ⟨585238320787107231647293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 780317761049476308863057 585238320787107231647293)
                ·
                  refine ⟨219464370295165211867735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 585238320787107231647293 219464370295165211867735)
                  ·
                    rfl

theorem cell21_961662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 3, 2, 3].length) (baseStart_961662 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_961662 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_961662 prefixEnd_961662 := by exact prefixLift 961662
  have htrace : WordTrace (prefixWord ++ tailWord_961662) baseStart_961662 baseEnd_961662 := by
    simpa [prefixWord, tailWord_961662, baseEnd_961662] using wordTrace_append hprefix tailTrace_961662
  have hstable : (prefixWord ++ tailWord_961662).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961662).length < 2 ^ (prefixWord ++ tailWord_961662).sum := by decide
  have hdescent : baseEnd_961662 < baseStart_961662 := by decide
  rcases family_descends (prefixWord ++ tailWord_961662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961667 : List Nat := [1, 1, 1, 3, 3, 2, 2, 4, 4]
def baseStart_961667 : Nat := 118140960795 + 961667 * 2 ^ 59
def prefixEnd_961667 : Nat := 4983230072969 + 3 ^ 40 * 961667 * 2
def baseEnd_961667 : Nat := 219465511363286314284391

theorem tailTrace_961667 : CollatzResearch.WordTrace tailWord_961667 prefixEnd_961667 219465511363286314284391 := by
  unfold tailWord_961667
  simp only [CollatzResearch.WordTrace]
  refine ⟨35074877007052173492923255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23383251338034782328615503 35074877007052173492923255)
  ·
    refine ⟨52612315510578260239384883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35074877007052173492923255 52612315510578260239384883)
    ·
      refine ⟨78918473265867390359077325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52612315510578260239384883 78918473265867390359077325)
      ·
        refine ⟨29594427474700271384653997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78918473265867390359077325 29594427474700271384653997)
        ·
          refine ⟨11097910303012601769245249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29594427474700271384653997 11097910303012601769245249)
          ·
            refine ⟨8323432727259451326933937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11097910303012601769245249 8323432727259451326933937)
            ·
              refine ⟨6242574545444588495200453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8323432727259451326933937 6242574545444588495200453)
              ·
                refine ⟨1170482727270860342850085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6242574545444588495200453 1170482727270860342850085)
                ·
                  refine ⟨219465511363286314284391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1170482727270860342850085 219465511363286314284391)
                  ·
                    rfl

theorem cell21_961667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 4, 4].length) (baseStart_961667 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_961667 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_961667 prefixEnd_961667 := by exact prefixLift 961667
  have htrace : WordTrace (prefixWord ++ tailWord_961667) baseStart_961667 baseEnd_961667 := by
    simpa [prefixWord, tailWord_961667, baseEnd_961667] using wordTrace_append hprefix tailTrace_961667
  have hstable : (prefixWord ++ tailWord_961667).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961667).length < 2 ^ (prefixWord ++ tailWord_961667).sum := by decide
  have hdescent : baseEnd_961667 < baseStart_961667 := by decide
  rcases family_descends (prefixWord ++ tailWord_961667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961732 : List Nat := [2, 3, 3, 1, 4, 1, 1, 6]
def baseStart_961732 : Nat := 118140960795 + 961732 * 2 ^ 59
def prefixEnd_961732 : Nat := 4983230072969 + 3 ^ 40 * 961732 * 2
def baseEnd_961732 : Nat := 73160115082953548566975

theorem tailTrace_961732 : CollatzResearch.WordTrace tailWord_961732 prefixEnd_961732 73160115082953548566975 := by
  unfold tailWord_961732
  simp only [CollatzResearch.WordTrace]
  refine ⟨17538623875908344797019725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23384831834544459729359633 17538623875908344797019725)
  ·
    refine ⟨6576983953465629298882397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17538623875908344797019725 6576983953465629298882397)
    ·
      refine ⟨2466368982549610987080899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6576983953465629298882397 2466368982549610987080899)
      ·
        refine ⟨3699553473824416480621349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2466368982549610987080899 3699553473824416480621349)
        ·
          refine ⟨693666276342078090116503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3699553473824416480621349 693666276342078090116503)
          ·
            refine ⟨1040499414513117135174755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 693666276342078090116503 1040499414513117135174755)
            ·
              refine ⟨1560749121769675702762133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1040499414513117135174755 1560749121769675702762133)
              ·
                refine ⟨73160115082953548566975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1560749121769675702762133 73160115082953548566975)
                ·
                  rfl

theorem cell21_961732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 1, 6].length) (baseStart_961732 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_961732 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_961732 prefixEnd_961732 := by exact prefixLift 961732
  have htrace : WordTrace (prefixWord ++ tailWord_961732) baseStart_961732 baseEnd_961732 := by
    simpa [prefixWord, tailWord_961732, baseEnd_961732] using wordTrace_append hprefix tailTrace_961732
  have hstable : (prefixWord ++ tailWord_961732).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961732).length < 2 ^ (prefixWord ++ tailWord_961732).sum := by decide
  have hdescent : baseEnd_961732 < baseStart_961732 := by decide
  rcases family_descends (prefixWord ++ tailWord_961732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961780 : List Nat := [2, 6, 1, 2, 1, 1, 2, 1, 5]
def baseStart_961780 : Nat := 118140960795 + 961780 * 2 ^ 59
def prefixEnd_961780 : Nat := 4983230072969 + 3 ^ 40 * 961780 * 2
def baseEnd_961780 : Nat := 219491299502823228900827

theorem tailTrace_961780 : CollatzResearch.WordTrace tailWord_961780 prefixEnd_961780 219491299502823228900827 := by
  unfold tailWord_961780
  simp only [CollatzResearch.WordTrace]
  refine ⟨17539499227821396895893397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23385998970428529194524529 17539499227821396895893397)
  ·
    refine ⟨822164026304127979495003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 17539499227821396895893397 822164026304127979495003)
    ·
      refine ⟨1233246039456191969242505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 822164026304127979495003 1233246039456191969242505)
      ·
        refine ⟨924934529592143976931879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1233246039456191969242505 924934529592143976931879)
        ·
          refine ⟨1387401794388215965397819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 924934529592143976931879 1387401794388215965397819)
          ·
            refine ⟨2081102691582323948096729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1387401794388215965397819 2081102691582323948096729)
            ·
              refine ⟨1560827018686742961072547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2081102691582323948096729 1560827018686742961072547)
              ·
                refine ⟨2341240528030114441608821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1560827018686742961072547 2341240528030114441608821)
                ·
                  refine ⟨219491299502823228900827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2341240528030114441608821 219491299502823228900827)
                  ·
                    rfl

theorem cell21_961780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_961780 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_961780 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_961780 prefixEnd_961780 := by exact prefixLift 961780
  have htrace : WordTrace (prefixWord ++ tailWord_961780) baseStart_961780 baseEnd_961780 := by
    simpa [prefixWord, tailWord_961780, baseEnd_961780] using wordTrace_append hprefix tailTrace_961780
  have hstable : (prefixWord ++ tailWord_961780).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961780).length < 2 ^ (prefixWord ++ tailWord_961780).sum := by decide
  have hdescent : baseEnd_961780 < baseStart_961780 := by decide
  rcases family_descends (prefixWord ++ tailWord_961780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961794 : List Nat := [3, 4, 1, 1, 3, 1, 3, 1, 4]
def baseStart_961794 : Nat := 118140960795 + 961794 * 2 ^ 59
def prefixEnd_961794 : Nat := 4983230072969 + 3 ^ 40 * 961794 * 2
def baseEnd_961794 : Nat := 219494494493562315667465

theorem tailTrace_961794 : CollatzResearch.WordTrace tailWord_961794 prefixEnd_961794 219494494493562315667465 := by
  unfold tailWord_961794
  simp only [CollatzResearch.WordTrace]
  refine ⟨8769877269398018545699109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23386339385061382788530957 8769877269398018545699109)
  ·
    refine ⟨1644351988012128477318583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8769877269398018545699109 1644351988012128477318583)
    ·
      refine ⟨2466527982018192715977875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1644351988012128477318583 2466527982018192715977875)
      ·
        refine ⟨3699791973027289073966813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2466527982018192715977875 3699791973027289073966813)
        ·
          refine ⟨1387421989885233402737555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3699791973027289073966813 1387421989885233402737555)
          ·
            refine ⟨2081132984827850104106333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1387421989885233402737555 2081132984827850104106333)
            ·
              refine ⟨780424869310443789039875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2081132984827850104106333 780424869310443789039875)
              ·
                refine ⟨1170637303965665683559813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 780424869310443789039875 1170637303965665683559813)
                ·
                  refine ⟨219494494493562315667465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1170637303965665683559813 219494494493562315667465)
                  ·
                    rfl

theorem cell21_961794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_961794 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_961794 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_961794 prefixEnd_961794 := by exact prefixLift 961794
  have htrace : WordTrace (prefixWord ++ tailWord_961794) baseStart_961794 baseEnd_961794 := by
    simpa [prefixWord, tailWord_961794, baseEnd_961794] using wordTrace_append hprefix tailTrace_961794
  have hstable : (prefixWord ++ tailWord_961794).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961794).length < 2 ^ (prefixWord ++ tailWord_961794).sum := by decide
  have hdescent : baseEnd_961794 < baseStart_961794 := by decide
  rcases family_descends (prefixWord ++ tailWord_961794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961853 : List Nat := [1, 4, 1, 5, 1, 1, 1, 3, 4]
def baseStart_961853 : Nat := 118140960795 + 961853 * 2 ^ 59
def prefixEnd_961853 : Nat := 4983230072969 + 3 ^ 40 * 961853 * 2
def baseEnd_961853 : Nat := 219507959097391324184011

theorem tailTrace_961853 : CollatzResearch.WordTrace tailWord_961853 prefixEnd_961853 219507959097391324184011 := by
  unfold tailWord_961853
  simp only [CollatzResearch.WordTrace]
  refine ⟨35081660984378327259194213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23387773989585551506129475 35081660984378327259194213)
  ·
    refine ⟨6577811434570936361098915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35081660984378327259194213 6577811434570936361098915)
    ·
      refine ⟨9866717151856404541648373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6577811434570936361098915 9866717151856404541648373)
      ·
        refine ⟨925004732986537925779535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9866717151856404541648373 925004732986537925779535)
        ·
          refine ⟨1387507099479806888669303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 925004732986537925779535 1387507099479806888669303)
          ·
            refine ⟨2081260649219710333003955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1387507099479806888669303 2081260649219710333003955)
            ·
              refine ⟨3121890973829565499505933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2081260649219710333003955 3121890973829565499505933)
              ·
                refine ⟨1170709115186087062314725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3121890973829565499505933 1170709115186087062314725)
                ·
                  refine ⟨219507959097391324184011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1170709115186087062314725 219507959097391324184011)
                  ·
                    rfl

theorem cell21_961853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 3, 4].length) (baseStart_961853 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_961853 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_961853 prefixEnd_961853 := by exact prefixLift 961853
  have htrace : WordTrace (prefixWord ++ tailWord_961853) baseStart_961853 baseEnd_961853 := by
    simpa [prefixWord, tailWord_961853, baseEnd_961853] using wordTrace_append hprefix tailTrace_961853
  have hstable : (prefixWord ++ tailWord_961853).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961853).length < 2 ^ (prefixWord ++ tailWord_961853).sum := by decide
  have hdescent : baseEnd_961853 < baseStart_961853 := by decide
  rcases family_descends (prefixWord ++ tailWord_961853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961999 : List Nat := [1, 1, 2, 1, 1, 4, 2, 2, 7]
def baseStart_961999 : Nat := 118140960795 + 961999 * 2 ^ 59
def prefixEnd_961999 : Nat := 4983230072969 + 3 ^ 40 * 961999 * 2
def baseEnd_961999 : Nat := 219541278286527514750379

theorem tailTrace_961999 : CollatzResearch.WordTrace tailWord_961999 prefixEnd_961999 219541278286527514750379 := by
  unfold tailWord_961999
  simp only [CollatzResearch.WordTrace]
  refine ⟨35086986041849394194009051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23391324027899596129339367 35086986041849394194009051)
  ·
    refine ⟨52630479062774091291013577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35086986041849394194009051 52630479062774091291013577)
    ·
      refine ⟨39472859297080568468260183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52630479062774091291013577 39472859297080568468260183)
      ·
        refine ⟨59209288945620852702390275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39472859297080568468260183 59209288945620852702390275)
        ·
          refine ⟨88813933418431279053585413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59209288945620852702390275 88813933418431279053585413)
          ·
            refine ⟨16652612515955864822547265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88813933418431279053585413 16652612515955864822547265)
            ·
              refine ⟨12489459386966898616910449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16652612515955864822547265 12489459386966898616910449)
              ·
                refine ⟨9367094540225173962682837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12489459386966898616910449 9367094540225173962682837)
                ·
                  refine ⟨219541278286527514750379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9367094540225173962682837 219541278286527514750379)
                  ·
                    rfl

theorem cell21_961999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 2, 7].length) (baseStart_961999 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_961999 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_961999 prefixEnd_961999 := by exact prefixLift 961999
  have htrace : WordTrace (prefixWord ++ tailWord_961999) baseStart_961999 baseEnd_961999 := by
    simpa [prefixWord, tailWord_961999, baseEnd_961999] using wordTrace_append hprefix tailTrace_961999
  have hstable : (prefixWord ++ tailWord_961999).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961999).length < 2 ^ (prefixWord ++ tailWord_961999).sum := by decide
  have hdescent : baseEnd_961999 < baseStart_961999 := by decide
  rcases family_descends (prefixWord ++ tailWord_961999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962106 : List Nat := [3, 1, 1, 1, 3, 2, 2, 2, 6]
def baseStart_962106 : Nat := 118140960795 + 962106 * 2 ^ 59
def prefixEnd_962106 : Nat := 4983230072969 + 3 ^ 40 * 962106 * 2
def baseEnd_962106 : Nat := 219565697144319106466827

theorem tailTrace_962106 : CollatzResearch.WordTrace tailWord_962106 prefixEnd_962106 219565697144319106466827 := by
  unfold tailWord_962106
  simp only [CollatzResearch.WordTrace]
  refine ⟨8772722163115437867038543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23393925768307834312102781 8772722163115437867038543)
  ·
    refine ⟨13159083244673156800557815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8772722163115437867038543 13159083244673156800557815)
    ·
      refine ⟨19738624867009735200836723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13159083244673156800557815 19738624867009735200836723)
      ·
        refine ⟨29607937300514602801255085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19738624867009735200836723 29607937300514602801255085)
        ·
          refine ⟨11102976487692976050470657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29607937300514602801255085 11102976487692976050470657)
          ·
            refine ⟨8327232365769732037852993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11102976487692976050470657 8327232365769732037852993)
            ·
              refine ⟨6245424274327299028389745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8327232365769732037852993 6245424274327299028389745)
              ·
                refine ⟨4684068205745474271292309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6245424274327299028389745 4684068205745474271292309)
                ·
                  refine ⟨219565697144319106466827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4684068205745474271292309 219565697144319106466827)
                  ·
                    rfl

theorem cell21_962106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 2, 6].length) (baseStart_962106 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_962106 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_962106 prefixEnd_962106 := by exact prefixLift 962106
  have htrace : WordTrace (prefixWord ++ tailWord_962106) baseStart_962106 baseEnd_962106 := by
    simpa [prefixWord, tailWord_962106, baseEnd_962106] using wordTrace_append hprefix tailTrace_962106
  have hstable : (prefixWord ++ tailWord_962106).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962106).length < 2 ^ (prefixWord ++ tailWord_962106).sum := by decide
  have hdescent : baseEnd_962106 < baseStart_962106 := by decide
  rcases family_descends (prefixWord ++ tailWord_962106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962154 : List Nat := [3, 1, 3, 2, 1, 2, 4, 5]
def baseStart_962154 : Nat := 118140960795 + 962154 * 2 ^ 59
def prefixEnd_962154 : Nat := 4983230072969 + 3 ^ 40 * 962154 * 2
def baseEnd_962154 : Nat := 73192217132760563222243

theorem tailTrace_962154 : CollatzResearch.WordTrace tailWord_962154 prefixEnd_962154 73192217132760563222243 := by
  unfold tailWord_962154
  simp only [CollatzResearch.WordTrace]
  refine ⟨8773159839071963916475379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23395092904191903777267677 8773159839071963916475379)
  ·
    refine ⟨13159739758607945874713069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8773159839071963916475379 13159739758607945874713069)
    ·
      refine ⟨4934902409477979703017401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13159739758607945874713069 4934902409477979703017401)
      ·
        refine ⟨3701176807108484777263051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4934902409477979703017401 3701176807108484777263051)
        ·
          refine ⟨5551765210662727165894577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3701176807108484777263051 5551765210662727165894577)
          ·
            refine ⟨4163823907997045374420933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5551765210662727165894577 4163823907997045374420933)
            ·
              refine ⟨780716982749446007703925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4163823907997045374420933 780716982749446007703925)
              ·
                refine ⟨73192217132760563222243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 780716982749446007703925 73192217132760563222243)
                ·
                  rfl

theorem cell21_962154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 4, 5].length) (baseStart_962154 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_962154 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_962154 prefixEnd_962154 := by exact prefixLift 962154
  have htrace : WordTrace (prefixWord ++ tailWord_962154) baseStart_962154 baseEnd_962154 := by
    simpa [prefixWord, tailWord_962154, baseEnd_962154] using wordTrace_append hprefix tailTrace_962154
  have hstable : (prefixWord ++ tailWord_962154).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962154).length < 2 ^ (prefixWord ++ tailWord_962154).sum := by decide
  have hdescent : baseEnd_962154 < baseStart_962154 := by decide
  rcases family_descends (prefixWord ++ tailWord_962154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962199 : List Nat := [1, 1, 3, 3, 2, 3, 1, 3, 4]
def baseStart_962199 : Nat := 118140960795 + 962199 * 2 ^ 59
def prefixEnd_962199 : Nat := 4983230072969 + 3 ^ 40 * 962199 * 2
def baseEnd_962199 : Nat := 219586921011371611416637

theorem tailTrace_962199 : CollatzResearch.WordTrace tailWord_962199 prefixEnd_962199 219586921011371611416637 := by
  unfold tailWord_962199
  simp only [CollatzResearch.WordTrace]
  refine ⟨35094280641124828351289651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23396187094083218900859767 35094280641124828351289651)
  ·
    refine ⟨52641420961687242526934477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35094280641124828351289651 52641420961687242526934477)
    ·
      refine ⟨19740532860632715947600429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52641420961687242526934477 19740532860632715947600429)
      ·
        refine ⟨7402699822737268480350161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19740532860632715947600429 7402699822737268480350161)
        ·
          refine ⟨5552024867052951360262621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7402699822737268480350161 5552024867052951360262621)
          ·
            refine ⟨2082009325144856760098483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5552024867052951360262621 2082009325144856760098483)
            ·
              refine ⟨3123013987717285140147725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2082009325144856760098483 3123013987717285140147725)
              ·
                refine ⟨1171130245393981927555397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3123013987717285140147725 1171130245393981927555397)
                ·
                  refine ⟨219586921011371611416637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1171130245393981927555397 219586921011371611416637)
                  ·
                    rfl

theorem cell21_962199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 3, 4].length) (baseStart_962199 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_962199 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_962199 prefixEnd_962199 := by exact prefixLift 962199
  have htrace : WordTrace (prefixWord ++ tailWord_962199) baseStart_962199 baseEnd_962199 := by
    simpa [prefixWord, tailWord_962199, baseEnd_962199] using wordTrace_append hprefix tailTrace_962199
  have hstable : (prefixWord ++ tailWord_962199).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962199).length < 2 ^ (prefixWord ++ tailWord_962199).sum := by decide
  have hdescent : baseEnd_962199 < baseStart_962199 := by decide
  rcases family_descends (prefixWord ++ tailWord_962199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962230 : List Nat := [5, 1, 3, 1, 1, 10]
def baseStart_962230 : Nat := 118140960795 + 962230 * 2 ^ 59
def prefixEnd_962230 : Nat := 4983230072969 + 3 ^ 40 * 962230 * 2
def baseEnd_962230 : Nat := 8133110949397127644441

theorem tailTrace_962230 : CollatzResearch.WordTrace tailWord_962230 prefixEnd_962230 8133110949397127644441 := by
  unfold tailWord_962230
  simp only [CollatzResearch.WordTrace]
  refine ⟨2193463206500782540354259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23396940869341680430445429 2193463206500782540354259)
  ·
    refine ⟨3290194809751173810531389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2193463206500782540354259 3290194809751173810531389)
    ·
      refine ⟨1233823053656690178949271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3290194809751173810531389 1233823053656690178949271)
      ·
        refine ⟨1850734580485035268423907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1233823053656690178949271 1850734580485035268423907)
        ·
          refine ⟨2776101870727552902635861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1850734580485035268423907 2776101870727552902635861)
          ·
            refine ⟨8133110949397127644441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2776101870727552902635861 8133110949397127644441)
            ·
              rfl

theorem cell21_962230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 10].length) (baseStart_962230 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_962230 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_962230 prefixEnd_962230 := by exact prefixLift 962230
  have htrace : WordTrace (prefixWord ++ tailWord_962230) baseStart_962230 baseEnd_962230 := by
    simpa [prefixWord, tailWord_962230, baseEnd_962230] using wordTrace_append hprefix tailTrace_962230
  have hstable : (prefixWord ++ tailWord_962230).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962230).length < 2 ^ (prefixWord ++ tailWord_962230).sum := by decide
  have hdescent : baseEnd_962230 < baseStart_962230 := by decide
  rcases family_descends (prefixWord ++ tailWord_962230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962244 : List Nat := [2, 3, 3, 1, 1, 1, 2, 3, 5]
def baseStart_962244 : Nat := 118140960795 + 962244 * 2 ^ 59
def prefixEnd_962244 : Nat := 4983230072969 + 3 ^ 40 * 962244 * 2
def baseEnd_962244 : Nat := 219597190624461533166545

theorem tailTrace_962244 : CollatzResearch.WordTrace tailWord_962244 prefixEnd_962244 219597190624461533166545 := by
  unfold tailWord_962244
  simp only [CollatzResearch.WordTrace]
  refine ⟨17547960962980900518338893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23397281283974534024451857 17547960962980900518338893)
  ·
    refine ⟨6580485361117837694377085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17547960962980900518338893 6580485361117837694377085)
    ·
      refine ⟨2467682010419189135391407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6580485361117837694377085 2467682010419189135391407)
      ·
        refine ⟨3701523015628783703087111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2467682010419189135391407 3701523015628783703087111)
        ·
          refine ⟨5552284523443175554630667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3701523015628783703087111 5552284523443175554630667)
          ·
            refine ⟨8328426785164763331946001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5552284523443175554630667 8328426785164763331946001)
            ·
              refine ⟨6246320088873572498959501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8328426785164763331946001 6246320088873572498959501)
              ·
                refine ⟨2342370033327589687109813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6246320088873572498959501 2342370033327589687109813)
                ·
                  refine ⟨219597190624461533166545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2342370033327589687109813 219597190624461533166545)
                  ·
                    rfl

theorem cell21_962244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 3, 5].length) (baseStart_962244 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_962244 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_962244 prefixEnd_962244 := by exact prefixLift 962244
  have htrace : WordTrace (prefixWord ++ tailWord_962244) baseStart_962244 baseEnd_962244 := by
    simpa [prefixWord, tailWord_962244, baseEnd_962244] using wordTrace_append hprefix tailTrace_962244
  have hstable : (prefixWord ++ tailWord_962244).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962244).length < 2 ^ (prefixWord ++ tailWord_962244).sum := by decide
  have hdescent : baseEnd_962244 < baseStart_962244 := by decide
  rcases family_descends (prefixWord ++ tailWord_962244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962272 : List Nat := [2, 1, 1, 3, 1, 2, 2, 9]
def baseStart_962272 : Nat := 118140960795 + 962272 * 2 ^ 59
def prefixEnd_962272 : Nat := 4983230072969 + 3 ^ 40 * 962272 * 2
def baseEnd_962272 : Nat := 73201193535313235566607

theorem tailTrace_962272 : CollatzResearch.WordTrace tailWord_962272 prefixEnd_962272 73201193535313235566607 := by
  unfold tailWord_962272
  simp only [CollatzResearch.WordTrace]
  refine ⟨17548471584930180909348535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23397962113240241212464713 17548471584930180909348535)
  ·
    refine ⟨26322707377395271364022803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17548471584930180909348535 26322707377395271364022803)
    ·
      refine ⟨39484061066092907046034205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26322707377395271364022803 39484061066092907046034205)
      ·
        refine ⟨14806522899784840142262827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39484061066092907046034205 14806522899784840142262827)
        ·
          refine ⟨22209784349677260213394241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14806522899784840142262827 22209784349677260213394241)
          ·
            refine ⟨16657338262257945160045681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22209784349677260213394241 16657338262257945160045681)
            ·
              refine ⟨12493003696693458870034261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16657338262257945160045681 12493003696693458870034261)
              ·
                refine ⟨73201193535313235566607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12493003696693458870034261 73201193535313235566607)
                ·
                  rfl

theorem cell21_962272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 9].length) (baseStart_962272 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_962272 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_962272 prefixEnd_962272 := by exact prefixLift 962272
  have htrace : WordTrace (prefixWord ++ tailWord_962272) baseStart_962272 baseEnd_962272 := by
    simpa [prefixWord, tailWord_962272, baseEnd_962272] using wordTrace_append hprefix tailTrace_962272
  have hstable : (prefixWord ++ tailWord_962272).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962272).length < 2 ^ (prefixWord ++ tailWord_962272).sum := by decide
  have hdescent : baseEnd_962272 < baseStart_962272 := by decide
  rcases family_descends (prefixWord ++ tailWord_962272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962303 : List Nat := [1, 1, 2, 2, 1, 3, 3, 3, 5]
def baseStart_962303 : Nat := 118140960795 + 962303 * 2 ^ 59
def prefixEnd_962303 : Nat := 4983230072969 + 3 ^ 40 * 962303 * 2
def baseEnd_962303 : Nat := 219610655228290541683091

theorem tailTrace_962303 : CollatzResearch.WordTrace tailWord_962303 prefixEnd_962303 219610655228290541683091 := by
  unfold tailWord_962303
  simp only [CollatzResearch.WordTrace]
  refine ⟨35098073832748054113075563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23398715888498702742050375 35098073832748054113075563)
  ·
    refine ⟨52647110749122081169613345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35098073832748054113075563 52647110749122081169613345)
    ·
      refine ⟨39485333061841560877210009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52647110749122081169613345 39485333061841560877210009)
      ·
        refine ⟨29613999796381170657907507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39485333061841560877210009 29613999796381170657907507)
        ·
          refine ⟨44420999694571755986861261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29613999796381170657907507 44420999694571755986861261)
          ·
            refine ⟨16657874885464408495072973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44420999694571755986861261 16657874885464408495072973)
            ·
              refine ⟨6246703082049153185652365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16657874885464408495072973 6246703082049153185652365)
              ·
                refine ⟨2342513655768432444619637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6246703082049153185652365 2342513655768432444619637)
                ·
                  refine ⟨219610655228290541683091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2342513655768432444619637 219610655228290541683091)
                  ·
                    rfl

theorem cell21_962303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 3, 5].length) (baseStart_962303 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_962303 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_962303 prefixEnd_962303 := by exact prefixLift 962303
  have htrace : WordTrace (prefixWord ++ tailWord_962303) baseStart_962303 baseEnd_962303 := by
    simpa [prefixWord, tailWord_962303, baseEnd_962303] using wordTrace_append hprefix tailTrace_962303
  have hstable : (prefixWord ++ tailWord_962303).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962303).length < 2 ^ (prefixWord ++ tailWord_962303).sum := by decide
  have hdescent : baseEnd_962303 < baseStart_962303 := by decide
  rcases family_descends (prefixWord ++ tailWord_962303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962337 : List Nat := [1, 2, 3, 2, 1, 3, 3, 3, 3]
def baseStart_962337 : Nat := 118140960795 + 962337 * 2 ^ 59
def prefixEnd_962337 : Nat := 4983230072969 + 3 ^ 40 * 962337 * 2
def baseEnd_962337 : Nat := 219618414491514038116355

theorem tailTrace_962337 : CollatzResearch.WordTrace tailWord_962337 prefixEnd_962337 219618414491514038116355 := by
  unfold tailWord_962337
  simp only [CollatzResearch.WordTrace]
  refine ⟨35099313914624877919813265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23399542609749918613208843 35099313914624877919813265)
  ·
    refine ⟨26324485435968658439859949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35099313914624877919813265 26324485435968658439859949)
    ·
      refine ⟨9871682038488246914947481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26324485435968658439859949 9871682038488246914947481)
      ·
        refine ⟨7403761528866185186210611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9871682038488246914947481 7403761528866185186210611)
        ·
          refine ⟨11105642293299277779315917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7403761528866185186210611 11105642293299277779315917)
          ·
            refine ⟨4164615859987229167243469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11105642293299277779315917 4164615859987229167243469)
            ·
              refine ⟨1561730947495210937716301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4164615859987229167243469 1561730947495210937716301)
              ·
                refine ⟨585649105310704101643613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1561730947495210937716301 585649105310704101643613)
                ·
                  refine ⟨219618414491514038116355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 585649105310704101643613 219618414491514038116355)
                  ·
                    rfl

theorem cell21_962337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 3, 3, 3].length) (baseStart_962337 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_962337 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_962337 prefixEnd_962337 := by exact prefixLift 962337
  have htrace : WordTrace (prefixWord ++ tailWord_962337) baseStart_962337 baseEnd_962337 := by
    simpa [prefixWord, tailWord_962337, baseEnd_962337] using wordTrace_append hprefix tailTrace_962337
  have hstable : (prefixWord ++ tailWord_962337).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962337).length < 2 ^ (prefixWord ++ tailWord_962337).sum := by decide
  have hdescent : baseEnd_962337 < baseStart_962337 := by decide
  rcases family_descends (prefixWord ++ tailWord_962337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962348 : List Nat := [2, 2, 1, 1, 1, 5, 9]
def baseStart_962348 : Nat := 118140960795 + 962348 * 2 ^ 59
def prefixEnd_962348 : Nat := 4983230072969 + 3 ^ 40 * 962348 * 2
def baseEnd_962348 : Nat := 24402324982375607048111

theorem tailTrace_962348 : CollatzResearch.WordTrace tailWord_962348 prefixEnd_962348 24402324982375607048111 := by
  unfold tailWord_962348
  simp only [CollatzResearch.WordTrace]
  refine ⟨17549857558792513399231849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23399810078390017865642465 17549857558792513399231849)
  ·
    refine ⟨13162393169094385049423887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17549857558792513399231849 13162393169094385049423887)
    ·
      refine ⟨19743589753641577574135831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13162393169094385049423887 19743589753641577574135831)
      ·
        refine ⟨29615384630462366361203747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19743589753641577574135831 29615384630462366361203747)
        ·
          refine ⟨44423076945693549541805621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29615384630462366361203747 44423076945693549541805621)
          ·
            refine ⟨4164663463658770269544277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 44423076945693549541805621 4164663463658770269544277)
            ·
              refine ⟨24402324982375607048111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4164663463658770269544277 24402324982375607048111)
              ·
                rfl

theorem cell21_962348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 9].length) (baseStart_962348 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_962348 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_962348 prefixEnd_962348 := by exact prefixLift 962348
  have htrace : WordTrace (prefixWord ++ tailWord_962348) baseStart_962348 baseEnd_962348 := by
    simpa [prefixWord, tailWord_962348, baseEnd_962348] using wordTrace_append hprefix tailTrace_962348
  have hstable : (prefixWord ++ tailWord_962348).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962348).length < 2 ^ (prefixWord ++ tailWord_962348).sum := by decide
  have hdescent : baseEnd_962348 < baseStart_962348 := by decide
  rcases family_descends (prefixWord ++ tailWord_962348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962354 : List Nat := [3, 2, 1, 1, 3, 3, 3, 2, 3]
def baseStart_962354 : Nat := 118140960795 + 962354 * 2 ^ 59
def prefixEnd_962354 : Nat := 4983230072969 + 3 ^ 40 * 962354 * 2
def baseEnd_962354 : Nat := 219622294123125786332987

theorem tailTrace_962354 : CollatzResearch.WordTrace tailWord_962354 prefixEnd_962354 219622294123125786332987 := by
  unfold tailWord_962354
  simp only [CollatzResearch.WordTrace]
  refine ⟨8774983488890822455795529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23399955970375526548788077 8774983488890822455795529)
  ·
    refine ⟨6581237616668116841846647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8774983488890822455795529 6581237616668116841846647)
    ·
      refine ⟨9871856425002175262769971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6581237616668116841846647 9871856425002175262769971)
      ·
        refine ⟨14807784637503262894154957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9871856425002175262769971 14807784637503262894154957)
        ·
          refine ⟨5552919239063723585308109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14807784637503262894154957 5552919239063723585308109)
          ·
            refine ⟨2082344714648896344490541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5552919239063723585308109 2082344714648896344490541)
            ·
              refine ⟨780879267993336129183953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2082344714648896344490541 780879267993336129183953)
              ·
                refine ⟨585659450995002096887965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 780879267993336129183953 585659450995002096887965)
                ·
                  refine ⟨219622294123125786332987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 585659450995002096887965 219622294123125786332987)
                  ·
                    rfl

theorem cell21_962354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 3, 2, 3].length) (baseStart_962354 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_962354 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_962354 prefixEnd_962354 := by exact prefixLift 962354
  have htrace : WordTrace (prefixWord ++ tailWord_962354) baseStart_962354 baseEnd_962354 := by
    simpa [prefixWord, tailWord_962354, baseEnd_962354] using wordTrace_append hprefix tailTrace_962354
  have hstable : (prefixWord ++ tailWord_962354).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962354).length < 2 ^ (prefixWord ++ tailWord_962354).sum := by decide
  have hdescent : baseEnd_962354 < baseStart_962354 := by decide
  rcases family_descends (prefixWord ++ tailWord_962354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962365 : List Nat := [1, 4, 1, 4, 1, 1, 1, 8]
def baseStart_962365 : Nat := 118140960795 + 962365 * 2 ^ 59
def prefixEnd_962365 : Nat := 4983230072969 + 3 ^ 40 * 962365 * 2
def baseEnd_962365 : Nat := 73208268157664070549877

theorem tailTrace_962365 : CollatzResearch.WordTrace tailWord_962365 prefixEnd_962365 73208268157664070549877 := by
  unfold tailWord_962365
  simp only [CollatzResearch.WordTrace]
  refine ⟨35100335158523438701832549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23400223439015625801221699 35100335158523438701832549)
  ·
    refine ⟨6581312842223144756593603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35100335158523438701832549 6581312842223144756593603)
    ·
      refine ⟨9871969263334717134890405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6581312842223144756593603 9871969263334717134890405)
      ·
        refine ⟨1850994236875259462791951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9871969263334717134890405 1850994236875259462791951)
        ·
          refine ⟨2776491355312889194187927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1850994236875259462791951 2776491355312889194187927)
          ·
            refine ⟨4164737032969333791281891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2776491355312889194187927 4164737032969333791281891)
            ·
              refine ⟨6247105549454000686922837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4164737032969333791281891 6247105549454000686922837)
              ·
                refine ⟨73208268157664070549877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6247105549454000686922837 73208268157664070549877)
                ·
                  rfl

theorem cell21_962365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 8].length) (baseStart_962365 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_962365 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_962365 prefixEnd_962365 := by exact prefixLift 962365
  have htrace : WordTrace (prefixWord ++ tailWord_962365) baseStart_962365 baseEnd_962365 := by
    simpa [prefixWord, tailWord_962365, baseEnd_962365] using wordTrace_append hprefix tailTrace_962365
  have hstable : (prefixWord ++ tailWord_962365).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962365).length < 2 ^ (prefixWord ++ tailWord_962365).sum := by decide
  have hdescent : baseEnd_962365 < baseStart_962365 := by decide
  rcases family_descends (prefixWord ++ tailWord_962365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962441 : List Nat := [1, 2, 1, 1, 5, 1, 5, 5]
def baseStart_962441 : Nat := 118140960795 + 962441 * 2 ^ 59
def prefixEnd_962441 : Nat := 4983230072969 + 3 ^ 40 * 962441 * 2
def baseEnd_962441 : Nat := 73214049569477656127603

theorem tailTrace_962441 : CollatzResearch.WordTrace tailWord_962441 prefixEnd_962441 73214049569477656127603 := by
  unfold tailWord_962441
  simp only [CollatzResearch.WordTrace]
  refine ⟨35103107106248103681599177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23402071404165402454399451 35103107106248103681599177)
  ·
    refine ⟨26327330329686077761199383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35103107106248103681599177 26327330329686077761199383)
    ·
      refine ⟨39490995494529116641799075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26327330329686077761199383 39490995494529116641799075)
      ·
        refine ⟨59236493241793674962698613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39490995494529116641799075 59236493241793674962698613)
        ·
          refine ⟨5553421241418157027752995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 59236493241793674962698613 5553421241418157027752995)
          ·
            refine ⟨8330131862127235541629493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5553421241418157027752995 8330131862127235541629493)
            ·
              refine ⟨780949862074428332027765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8330131862127235541629493 780949862074428332027765)
              ·
                refine ⟨73214049569477656127603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 780949862074428332027765 73214049569477656127603)
                ·
                  rfl

theorem cell21_962441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 5, 5].length) (baseStart_962441 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_962441 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_962441 prefixEnd_962441 := by exact prefixLift 962441
  have htrace : WordTrace (prefixWord ++ tailWord_962441) baseStart_962441 baseEnd_962441 := by
    simpa [prefixWord, tailWord_962441, baseEnd_962441] using wordTrace_append hprefix tailTrace_962441
  have hstable : (prefixWord ++ tailWord_962441).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962441).length < 2 ^ (prefixWord ++ tailWord_962441).sum := by decide
  have hdescent : baseEnd_962441 < baseStart_962441 := by decide
  rcases family_descends (prefixWord ++ tailWord_962441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962492 : List Nat := [2, 2, 2, 5, 2, 1, 2, 5]
def baseStart_962492 : Nat := 118140960795 + 962492 * 2 ^ 59
def prefixEnd_962492 : Nat := 4983230072969 + 3 ^ 40 * 962492 * 2
def baseEnd_962492 : Nat := 73217929201089404344235

theorem tailTrace_962492 : CollatzResearch.WordTrace tailWord_962492 prefixEnd_962492 73217929201089404344235 := by
  unfold tailWord_962492
  simp only [CollatzResearch.WordTrace]
  refine ⟨17552483614531669695852865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23403311486042226261137153 17552483614531669695852865)
  ·
    refine ⟨13164362710898752271889649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17552483614531669695852865 13164362710898752271889649)
    ·
      refine ⟨9873272033174064203917237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13164362710898752271889649 9873272033174064203917237)
      ·
        refine ⟨925619253110068519117241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9873272033174064203917237 925619253110068519117241)
        ·
          refine ⟨694214439832551389337931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 925619253110068519117241 694214439832551389337931)
          ·
            refine ⟨1041321659748827084006897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 694214439832551389337931 1041321659748827084006897)
            ·
              refine ⟨780991244811620313005173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1041321659748827084006897 780991244811620313005173)
              ·
                refine ⟨73217929201089404344235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 780991244811620313005173 73217929201089404344235)
                ·
                  rfl

theorem cell21_962492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 2, 5].length) (baseStart_962492 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_962492 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_962492 prefixEnd_962492 := by exact prefixLift 962492
  have htrace : WordTrace (prefixWord ++ tailWord_962492) baseStart_962492 baseEnd_962492 := by
    simpa [prefixWord, tailWord_962492, baseEnd_962492] using wordTrace_append hprefix tailTrace_962492
  have hstable : (prefixWord ++ tailWord_962492).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962492).length < 2 ^ (prefixWord ++ tailWord_962492).sum := by decide
  have hdescent : baseEnd_962492 < baseStart_962492 := by decide
  rcases family_descends (prefixWord ++ tailWord_962492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962517 : List Nat := [1, 3, 2, 3, 2, 3, 7]
def baseStart_962517 : Nat := 118140960795 + 962517 * 2 ^ 59
def prefixEnd_962517 : Nat := 4983230072969 + 3 ^ 40 * 962517 * 2
def baseEnd_962517 : Nat := 24406610327097080568443

theorem tailTrace_962517 : CollatzResearch.WordTrace tailWord_962517 prefixEnd_962517 24406610327097080568443 := by
  unfold tailWord_962517
  simp only [CollatzResearch.WordTrace]
  refine ⟨35105879053972768661365805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23403919369315179107577203 35105879053972768661365805)
  ·
    refine ⟨13164704645239788248012177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35105879053972768661365805 13164704645239788248012177)
    ·
      refine ⟨9873528483929841186009133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13164704645239788248012177 9873528483929841186009133)
      ·
        refine ⟨3702573181473690444753425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9873528483929841186009133 3702573181473690444753425)
        ·
          refine ⟨2776929886105267833565069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3702573181473690444753425 2776929886105267833565069)
          ·
            refine ⟨1041348707289475437586901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2776929886105267833565069 1041348707289475437586901)
            ·
              refine ⟨24406610327097080568443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1041348707289475437586901 24406610327097080568443)
              ·
                rfl

theorem cell21_962517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 7].length) (baseStart_962517 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_962517 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_962517 prefixEnd_962517 := by exact prefixLift 962517
  have htrace : WordTrace (prefixWord ++ tailWord_962517) baseStart_962517 baseEnd_962517 := by
    simpa [prefixWord, tailWord_962517, baseEnd_962517] using wordTrace_append hprefix tailTrace_962517
  have hstable : (prefixWord ++ tailWord_962517).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962517).length < 2 ^ (prefixWord ++ tailWord_962517).sum := by decide
  have hdescent : baseEnd_962517 < baseStart_962517 := by decide
  rcases family_descends (prefixWord ++ tailWord_962517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962624 : List Nat := [2, 1, 1, 2, 2, 4, 1, 5, 3]
def baseStart_962624 : Nat := 118140960795 + 962624 * 2 ^ 59
def prefixEnd_962624 : Nat := 4983230072969 + 3 ^ 40 * 962624 * 2
def baseEnd_962624 : Nat := 219683911801665316832435

theorem tailTrace_962624 : CollatzResearch.WordTrace tailWord_962624 prefixEnd_962624 219683911801665316832435 := by
  unfold tailWord_962624
  simp only [CollatzResearch.WordTrace]
  refine ⟨17554890832292562967755463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23406521109723417290340617 17554890832292562967755463)
  ·
    refine ⟨26332336248438844451633195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17554890832292562967755463 26332336248438844451633195)
    ·
      refine ⟨39498504372658266677449793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26332336248438844451633195 39498504372658266677449793)
      ·
        refine ⟨29623878279493700008087345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39498504372658266677449793 29623878279493700008087345)
        ·
          refine ⟨22217908709620275006065509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29623878279493700008087345 22217908709620275006065509)
          ·
            refine ⟨4165857883053801563637283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22217908709620275006065509 4165857883053801563637283)
            ·
              refine ⟨6248786824580702345455925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4165857883053801563637283 6248786824580702345455925)
              ·
                refine ⟨585823764804440844886493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6248786824580702345455925 585823764804440844886493)
                ·
                  refine ⟨219683911801665316832435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 585823764804440844886493 219683911801665316832435)
                  ·
                    rfl

theorem cell21_962624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 5, 3].length) (baseStart_962624 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_962624 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_962624 prefixEnd_962624 := by exact prefixLift 962624
  have htrace : WordTrace (prefixWord ++ tailWord_962624) baseStart_962624 baseEnd_962624 := by
    simpa [prefixWord, tailWord_962624, baseEnd_962624] using wordTrace_append hprefix tailTrace_962624
  have hstable : (prefixWord ++ tailWord_962624).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962624).length < 2 ^ (prefixWord ++ tailWord_962624).sum := by decide
  have hdescent : baseEnd_962624 < baseStart_962624 := by decide
  rcases family_descends (prefixWord ++ tailWord_962624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962638 : List Nat := [4, 1, 1, 1, 1, 5, 1, 1, 6]
def baseStart_962638 : Nat := 118140960795 + 962638 * 2 ^ 59
def prefixEnd_962638 : Nat := 4983230072969 + 3 ^ 40 * 962638 * 2
def baseEnd_962638 : Nat := 219687106792404403599073

theorem tailTrace_962638 : CollatzResearch.WordTrace tailWord_962638 prefixEnd_962638 219687106792404403599073 := by
  unfold tailWord_962638
  simp only [CollatzResearch.WordTrace]
  refine ⟨4388786535816800790815071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23406861524356270884347045 4388786535816800790815071)
  ·
    refine ⟨6583179803725201186222607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4388786535816800790815071 6583179803725201186222607)
    ·
      refine ⟨9874769705587801779333911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6583179803725201186222607 9874769705587801779333911)
      ·
        refine ⟨14812154558381702669000867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9874769705587801779333911 14812154558381702669000867)
        ·
          refine ⟨22218231837572554003501301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14812154558381702669000867 22218231837572554003501301)
          ·
            refine ⟨2082959234772426937828247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22218231837572554003501301 2082959234772426937828247)
            ·
              refine ⟨3124438852158640406742371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2082959234772426937828247 3124438852158640406742371)
              ·
                refine ⟨4686658278237960610113557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3124438852158640406742371 4686658278237960610113557)
                ·
                  refine ⟨219687106792404403599073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4686658278237960610113557 219687106792404403599073)
                  ·
                    rfl

theorem cell21_962638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 1, 6].length) (baseStart_962638 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_962638 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_962638 prefixEnd_962638 := by exact prefixLift 962638
  have htrace : WordTrace (prefixWord ++ tailWord_962638) baseStart_962638 baseEnd_962638 := by
    simpa [prefixWord, tailWord_962638, baseEnd_962638] using wordTrace_append hprefix tailTrace_962638
  have hstable : (prefixWord ++ tailWord_962638).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962638).length < 2 ^ (prefixWord ++ tailWord_962638).sum := by decide
  have hdescent : baseEnd_962638 < baseStart_962638 := by decide
  rcases family_descends (prefixWord ++ tailWord_962638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962697 : List Nat := [1, 2, 1, 1, 4, 2, 1, 3, 6]
def baseStart_962697 : Nat := 118140960795 + 962697 * 2 ^ 59
def prefixEnd_962697 : Nat := 4983230072969 + 3 ^ 40 * 962697 * 2
def baseEnd_962697 : Nat := 219700571396233412115619

theorem tailTrace_962697 : CollatzResearch.WordTrace tailWord_962697 prefixEnd_962697 219700571396233412115619 := by
  unfold tailWord_962697
  simp only [CollatzResearch.WordTrace]
  refine ⟨35112444193320659402918345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23408296128880439601945563 35112444193320659402918345)
  ·
    refine ⟨26334333144990494552188759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35112444193320659402918345 26334333144990494552188759)
    ·
      refine ⟨39501499717485741828283139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26334333144990494552188759 39501499717485741828283139)
      ·
        refine ⟨59252249576228612742424709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39501499717485741828283139 59252249576228612742424709)
        ·
          refine ⟨11109796795542864889204633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59252249576228612742424709 11109796795542864889204633)
          ·
            refine ⟨8332347596657148666903475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11109796795542864889204633 8332347596657148666903475)
            ·
              refine ⟨12498521394985723000355213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8332347596657148666903475 12498521394985723000355213)
              ·
                refine ⟨4686945523119646125133205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12498521394985723000355213 4686945523119646125133205)
                ·
                  refine ⟨219700571396233412115619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4686945523119646125133205 219700571396233412115619)
                  ·
                    rfl

theorem cell21_962697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 3, 6].length) (baseStart_962697 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_962697 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_962697 prefixEnd_962697 := by exact prefixLift 962697
  have htrace : WordTrace (prefixWord ++ tailWord_962697) baseStart_962697 baseEnd_962697 := by
    simpa [prefixWord, tailWord_962697, baseEnd_962697] using wordTrace_append hprefix tailTrace_962697
  have hstable : (prefixWord ++ tailWord_962697).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962697).length < 2 ^ (prefixWord ++ tailWord_962697).sum := by decide
  have hdescent : baseEnd_962697 < baseStart_962697 := by decide
  rcases family_descends (prefixWord ++ tailWord_962697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962849 : List Nat := [1, 2, 3, 2, 1, 1, 3, 2, 6]
def baseStart_962849 : Nat := 118140960795 + 962849 * 2 ^ 59
def prefixEnd_962849 : Nat := 4983230072969 + 3 ^ 40 * 962849 * 2
def baseEnd_962849 : Nat := 219735259867114925581975

theorem tailTrace_962849 : CollatzResearch.WordTrace tailWord_962849 prefixEnd_962849 219735259867114925581975 := by
  unfold tailWord_962849
  simp only [CollatzResearch.WordTrace]
  refine ⟨35117988088769989362451601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23411992059179992908301067 35117988088769989362451601)
  ·
    refine ⟨26338491066577492021838701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35117988088769989362451601 26338491066577492021838701)
    ·
      refine ⟨9876934149966559508189513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26338491066577492021838701 9876934149966559508189513)
      ·
        refine ⟨7407700612474919631142135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9876934149966559508189513 7407700612474919631142135)
        ·
          refine ⟨11111550918712379446713203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7407700612474919631142135 11111550918712379446713203)
          ·
            refine ⟨16667326378068569170069805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11111550918712379446713203 16667326378068569170069805)
            ·
              refine ⟨6250247391775713438776177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16667326378068569170069805 6250247391775713438776177)
              ·
                refine ⟨4687685543831785079082133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6250247391775713438776177 4687685543831785079082133)
                ·
                  refine ⟨219735259867114925581975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4687685543831785079082133 219735259867114925581975)
                  ·
                    rfl

theorem cell21_962849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 2, 6].length) (baseStart_962849 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_962849 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_962849 prefixEnd_962849 := by exact prefixLift 962849
  have htrace : WordTrace (prefixWord ++ tailWord_962849) baseStart_962849 baseEnd_962849 := by
    simpa [prefixWord, tailWord_962849, baseEnd_962849] using wordTrace_append hprefix tailTrace_962849
  have hstable : (prefixWord ++ tailWord_962849).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962849).length < 2 ^ (prefixWord ++ tailWord_962849).sum := by decide
  have hdescent : baseEnd_962849 < baseStart_962849 := by decide
  rcases family_descends (prefixWord ++ tailWord_962849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962855 : List Nat := [1, 1, 8, 1, 1, 2, 7]
def baseStart_962855 : Nat := 118140960795 + 962855 * 2 ^ 59
def prefixEnd_962855 : Nat := 4983230072969 + 3 ^ 40 * 962855 * 2
def baseEnd_962855 : Nat := 24415181016540027609107

theorem tailTrace_962855 : CollatzResearch.WordTrace tailWord_962855 prefixEnd_962855 24415181016540027609107 := by
  unfold tailWord_962855
  simp only [CollatzResearch.WordTrace]
  refine ⟨35118206926748252387170019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23412137951165501591446679 35118206926748252387170019)
  ·
    refine ⟨52677310390122378580755029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35118206926748252387170019 52677310390122378580755029)
    ·
      refine ⟨617312231134246623993223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 52677310390122378580755029 617312231134246623993223)
      ·
        refine ⟨925968346701369935989835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 617312231134246623993223 925968346701369935989835)
        ·
          refine ⟨1388952520052054903984753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 925968346701369935989835 1388952520052054903984753)
          ·
            refine ⟨1041714390039041177988565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1388952520052054903984753 1041714390039041177988565)
            ·
              refine ⟨24415181016540027609107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1041714390039041177988565 24415181016540027609107)
              ·
                rfl

theorem cell21_962855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 7].length) (baseStart_962855 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_962855 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_962855 prefixEnd_962855 := by exact prefixLift 962855
  have htrace : WordTrace (prefixWord ++ tailWord_962855) baseStart_962855 baseEnd_962855 := by
    simpa [prefixWord, tailWord_962855, baseEnd_962855] using wordTrace_append hprefix tailTrace_962855
  have hstable : (prefixWord ++ tailWord_962855).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962855).length < 2 ^ (prefixWord ++ tailWord_962855).sum := by decide
  have hdescent : baseEnd_962855 < baseStart_962855 := by decide
  rcases family_descends (prefixWord ++ tailWord_962855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962863 : List Nat := [1, 1, 2, 1, 2, 1, 13]
def baseStart_962863 : Nat := 118140960795 + 962863 * 2 ^ 59
def prefixEnd_962863 : Nat := 4983230072969 + 3 ^ 40 * 962863 * 2
def baseEnd_962863 : Nat := 24415383873094890260957

theorem tailTrace_962863 : CollatzResearch.WordTrace tailWord_962863 prefixEnd_962863 24415383873094890260957 := by
  unfold tailWord_962863
  simp only [CollatzResearch.WordTrace]
  refine ⟨35118498710719269753461243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23412332473812846502307495 35118498710719269753461243)
  ·
    refine ⟨52677748066078904630191865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35118498710719269753461243 52677748066078904630191865)
    ·
      refine ⟨39508311049559178472643899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52677748066078904630191865 39508311049559178472643899)
      ·
        refine ⟨59262466574338767708965849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39508311049559178472643899 59262466574338767708965849)
        ·
          refine ⟨44446849930754075781724387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59262466574338767708965849 44446849930754075781724387)
          ·
            refine ⟨66670274896131113672586581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44446849930754075781724387 66670274896131113672586581)
            ·
              refine ⟨24415383873094890260957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 66670274896131113672586581 24415383873094890260957)
              ·
                rfl

theorem cell21_962863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 13].length) (baseStart_962863 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_962863 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_962863 prefixEnd_962863 := by exact prefixLift 962863
  have htrace : WordTrace (prefixWord ++ tailWord_962863) baseStart_962863 baseEnd_962863 := by
    simpa [prefixWord, tailWord_962863, baseEnd_962863] using wordTrace_append hprefix tailTrace_962863
  have hstable : (prefixWord ++ tailWord_962863).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962863).length < 2 ^ (prefixWord ++ tailWord_962863).sum := by decide
  have hdescent : baseEnd_962863 < baseStart_962863 := by decide
  rcases family_descends (prefixWord ++ tailWord_962863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962869 : List Nat := [1, 3, 3, 1, 2, 1, 5, 2, 3]
def baseStart_962869 : Nat := 118140960795 + 962869 * 2 ^ 59
def prefixEnd_962869 : Nat := 4983230072969 + 3 ^ 40 * 962869 * 2
def baseEnd_962869 : Nat := 219739824139599335248601

theorem tailTrace_962869 : CollatzResearch.WordTrace tailWord_962869 prefixEnd_962869 219739824139599335248601 := by
  unfold tailWord_962869
  simp only [CollatzResearch.WordTrace]
  refine ⟨35118717548697532778179661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23412478365798355185453107 35118717548697532778179661)
  ·
    refine ⟨13169519080761574791817373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35118717548697532778179661 13169519080761574791817373)
    ·
      refine ⟨4938569655285590546931515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13169519080761574791817373 4938569655285590546931515)
      ·
        refine ⟨7407854482928385820397273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4938569655285590546931515 7407854482928385820397273)
        ·
          refine ⟨5555890862196289365297955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7407854482928385820397273 5555890862196289365297955)
          ·
            refine ⟨8333836293294434047946933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5555890862196289365297955 8333836293294434047946933)
            ·
              refine ⟨781297152496353191995025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8333836293294434047946933 781297152496353191995025)
              ·
                refine ⟨585972864372264893996269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 781297152496353191995025 585972864372264893996269)
                ·
                  refine ⟨219739824139599335248601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 585972864372264893996269 219739824139599335248601)
                  ·
                    rfl

theorem cell21_962869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 5, 2, 3].length) (baseStart_962869 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_962869 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_962869 prefixEnd_962869 := by exact prefixLift 962869
  have htrace : WordTrace (prefixWord ++ tailWord_962869) baseStart_962869 baseEnd_962869 := by
    simpa [prefixWord, tailWord_962869, baseEnd_962869] using wordTrace_append hprefix tailTrace_962869
  have hstable : (prefixWord ++ tailWord_962869).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962869).length < 2 ^ (prefixWord ++ tailWord_962869).sum := by decide
  have hdescent : baseEnd_962869 < baseStart_962869 := by decide
  rcases family_descends (prefixWord ++ tailWord_962869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962928 : List Nat := [2, 1, 1, 1, 4, 4, 1, 4, 3]
def baseStart_962928 : Nat := 118140960795 + 962928 * 2 ^ 59
def prefixEnd_962928 : Nat := 4983230072969 + 3 ^ 40 * 962928 * 2
def baseEnd_962928 : Nat := 219753288743428343765147

theorem tailTrace_962928 : CollatzResearch.WordTrace tailWord_962928 prefixEnd_962928 219753288743428343765147 := by
  unfold tailWord_962928
  simp only [CollatzResearch.WordTrace]
  refine ⟨17560434727741892927288719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23413912970322523903051625 17560434727741892927288719)
  ·
    refine ⟨26340652091612839390933079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17560434727741892927288719 26340652091612839390933079)
    ·
      refine ⟨39510978137419259086399619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26340652091612839390933079 39510978137419259086399619)
      ·
        refine ⟨59266467206128888629599429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39510978137419259086399619 59266467206128888629599429)
        ·
          refine ⟨11112462601149166618049893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59266467206128888629599429 11112462601149166618049893)
          ·
            refine ⟨2083586737715468740884355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11112462601149166618049893 2083586737715468740884355)
            ·
              refine ⟨3125380106573203111326533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2083586737715468740884355 3125380106573203111326533)
              ·
                refine ⟨586008769982475583373725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3125380106573203111326533 586008769982475583373725)
                ·
                  refine ⟨219753288743428343765147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 586008769982475583373725 219753288743428343765147)
                  ·
                    rfl

theorem cell21_962928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 4, 3].length) (baseStart_962928 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_962928 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_962928 prefixEnd_962928 := by exact prefixLift 962928
  have htrace : WordTrace (prefixWord ++ tailWord_962928) baseStart_962928 baseEnd_962928 := by
    simpa [prefixWord, tailWord_962928, baseEnd_962928] using wordTrace_append hprefix tailTrace_962928
  have hstable : (prefixWord ++ tailWord_962928).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962928).length < 2 ^ (prefixWord ++ tailWord_962928).sum := by decide
  have hdescent : baseEnd_962928 < baseStart_962928 := by decide
  rcases family_descends (prefixWord ++ tailWord_962928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963122 : List Nat := [3, 2, 1, 1, 2, 1, 3, 1, 7]
def baseStart_963122 : Nat := 118140960795 + 963122 * 2 ^ 59
def prefixEnd_963122 : Nat := 4983230072969 + 3 ^ 40 * 963122 * 2
def baseEnd_963122 : Nat := 219797562186527117531417

theorem tailTrace_963122 : CollatzResearch.WordTrace tailWord_963122 prefixEnd_963122 219797562186527117531417 := by
  unfold tailWord_963122
  simp only [CollatzResearch.WordTrace]
  refine ⟨8781986304195239246784905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23418630144520637991426413 8781986304195239246784905)
  ·
    refine ⟨6586489728146429435088679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8781986304195239246784905 6586489728146429435088679)
    ·
      refine ⟨9879734592219644152633019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6586489728146429435088679 9879734592219644152633019)
      ·
        refine ⟨14819601888329466228949529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9879734592219644152633019 14819601888329466228949529)
        ·
          refine ⟨11114701416247099671712147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14819601888329466228949529 11114701416247099671712147)
          ·
            refine ⟨16672052124370649507568221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11114701416247099671712147 16672052124370649507568221)
            ·
              refine ⟨6252019546638993565338083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16672052124370649507568221 6252019546638993565338083)
              ·
                refine ⟨9378029319958490348007125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6252019546638993565338083 9378029319958490348007125)
                ·
                  refine ⟨219797562186527117531417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9378029319958490348007125 219797562186527117531417)
                  ·
                    rfl

theorem cell21_963122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 1, 7].length) (baseStart_963122 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_963122 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_963122 prefixEnd_963122 := by exact prefixLift 963122
  have htrace : WordTrace (prefixWord ++ tailWord_963122) baseStart_963122 baseEnd_963122 := by
    simpa [prefixWord, tailWord_963122, baseEnd_963122] using wordTrace_append hprefix tailTrace_963122
  have hstable : (prefixWord ++ tailWord_963122).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963122).length < 2 ^ (prefixWord ++ tailWord_963122).sum := by decide
  have hdescent : baseEnd_963122 < baseStart_963122 := by decide
  rcases family_descends (prefixWord ++ tailWord_963122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963153 : List Nat := [1, 2, 2, 1, 3, 4, 1, 1, 6]
def baseStart_963153 : Nat := 118140960795 + 963153 * 2 ^ 59
def prefixEnd_963153 : Nat := 4983230072969 + 3 ^ 40 * 963153 * 2
def baseEnd_963153 : Nat := 219804636808877952514687

theorem tailTrace_963153 : CollatzResearch.WordTrace tailWord_963153 prefixEnd_963153 219804636808877952514687 := by
  unfold tailWord_963153
  simp only [CollatzResearch.WordTrace]
  refine ⟨35129075879668649281518113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23419383919779099521012075 35129075879668649281518113)
  ·
    refine ⟨26346806909751486961138585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35129075879668649281518113 26346806909751486961138585)
    ·
      refine ⟨19760105182313615220853939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26346806909751486961138585 19760105182313615220853939)
      ·
        refine ⟨29640157773470422831280909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19760105182313615220853939 29640157773470422831280909)
        ·
          refine ⟨11115059165051408561730341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29640157773470422831280909 11115059165051408561730341)
          ·
            refine ⟨2084073593447139105324439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11115059165051408561730341 2084073593447139105324439)
            ·
              refine ⟨3126110390170708657986659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2084073593447139105324439 3126110390170708657986659)
              ·
                refine ⟨4689165585256062986979989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3126110390170708657986659 4689165585256062986979989)
                ·
                  refine ⟨219804636808877952514687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4689165585256062986979989 219804636808877952514687)
                  ·
                    rfl

theorem cell21_963153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 1, 6].length) (baseStart_963153 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_963153 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_963153 prefixEnd_963153 := by exact prefixLift 963153
  have htrace : WordTrace (prefixWord ++ tailWord_963153) baseStart_963153 baseEnd_963153 := by
    simpa [prefixWord, tailWord_963153, baseEnd_963153] using wordTrace_append hprefix tailTrace_963153
  have hstable : (prefixWord ++ tailWord_963153).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963153).length < 2 ^ (prefixWord ++ tailWord_963153).sum := by decide
  have hdescent : baseEnd_963153 < baseStart_963153 := by decide
  rcases family_descends (prefixWord ++ tailWord_963153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963156 : List Nat := [2, 4, 1, 1, 1, 3, 2, 4, 3]
def baseStart_963156 : Nat := 118140960795 + 963156 * 2 ^ 59
def prefixEnd_963156 : Nat := 4983230072969 + 3 ^ 40 * 963156 * 2
def baseEnd_963156 : Nat := 219805321449750613964681

theorem tailTrace_963156 : CollatzResearch.WordTrace tailWord_963156 prefixEnd_963156 219805321449750613964681 := by
  unfold tailWord_963156
  simp only [CollatzResearch.WordTrace]
  refine ⟨17564592649328890396938661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23419456865771853862584881 17564592649328890396938661)
  ·
    refine ⟨3293361121749166949425999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17564592649328890396938661 3293361121749166949425999)
    ·
      refine ⟨4940041682623750424138999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3293361121749166949425999 4940041682623750424138999)
      ·
        refine ⟨7410062523935625636208499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4940041682623750424138999 7410062523935625636208499)
        ·
          refine ⟨11115093785903438454312749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7410062523935625636208499 11115093785903438454312749)
          ·
            refine ⟨4168160169713789420367281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11115093785903438454312749 4168160169713789420367281)
            ·
              refine ⟨3126120127285342065275461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4168160169713789420367281 3126120127285342065275461)
              ·
                refine ⟨586147523866001637239149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3126120127285342065275461 586147523866001637239149)
                ·
                  refine ⟨219805321449750613964681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 586147523866001637239149 219805321449750613964681)
                  ·
                    rfl

theorem cell21_963156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 4, 3].length) (baseStart_963156 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_963156 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_963156 prefixEnd_963156 := by exact prefixLift 963156
  have htrace : WordTrace (prefixWord ++ tailWord_963156) baseStart_963156 baseEnd_963156 := by
    simpa [prefixWord, tailWord_963156, baseEnd_963156] using wordTrace_append hprefix tailTrace_963156
  have hstable : (prefixWord ++ tailWord_963156).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963156).length < 2 ^ (prefixWord ++ tailWord_963156).sum := by decide
  have hdescent : baseEnd_963156 < baseStart_963156 := by decide
  rcases family_descends (prefixWord ++ tailWord_963156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963184 : List Nat := [2, 1, 1, 1, 7, 1, 1, 7]
def baseStart_963184 : Nat := 118140960795 + 963184 * 2 ^ 59
def prefixEnd_963184 : Nat := 4983230072969 + 3 ^ 40 * 963184 * 2
def baseEnd_963184 : Nat := 73270570477076262499319

theorem tailTrace_963184 : CollatzResearch.WordTrace tailWord_963184 prefixEnd_963184 73270570477076262499319 := by
  unfold tailWord_963184
  simp only [CollatzResearch.WordTrace]
  refine ⟨17565103271278170787948303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23420137695037561050597737 17565103271278170787948303)
  ·
    refine ⟨26347654906917256181922455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17565103271278170787948303 26347654906917256181922455)
    ·
      refine ⟨39521482360375884272883683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26347654906917256181922455 39521482360375884272883683)
      ·
        refine ⟨59282223540563826409325525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39521482360375884272883683 59282223540563826409325525)
        ·
          refine ⟨1389427114231964681468567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 59282223540563826409325525 1389427114231964681468567)
          ·
            refine ⟨2084140671347947022202851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1389427114231964681468567 2084140671347947022202851)
            ·
              refine ⟨3126211007021920533304277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2084140671347947022202851 3126211007021920533304277)
              ·
                refine ⟨73270570477076262499319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3126211007021920533304277 73270570477076262499319)
                ·
                  rfl

theorem cell21_963184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 7].length) (baseStart_963184 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_963184 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_963184 prefixEnd_963184 := by exact prefixLift 963184
  have htrace : WordTrace (prefixWord ++ tailWord_963184) baseStart_963184 baseEnd_963184 := by
    simpa [prefixWord, tailWord_963184, baseEnd_963184] using wordTrace_append hprefix tailTrace_963184
  have hstable : (prefixWord ++ tailWord_963184).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963184).length < 2 ^ (prefixWord ++ tailWord_963184).sum := by decide
  have hdescent : baseEnd_963184 < baseStart_963184 := by decide
  rcases family_descends (prefixWord ++ tailWord_963184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963190 : List Nat := [5, 1, 1, 2, 3, 2, 1, 3, 3]
def baseStart_963190 : Nat := 118140960795 + 963190 * 2 ^ 59
def prefixEnd_963190 : Nat := 4983230072969 + 3 ^ 40 * 963190 * 2
def baseEnd_963190 : Nat := 219813080712974110397945

theorem tailTrace_963190 : CollatzResearch.WordTrace tailWord_963190 prefixEnd_963190 219813080712974110397945 := by
  unfold tailWord_963190
  simp only [CollatzResearch.WordTrace]
  refine ⟨2195651586283412787538439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23420283587023069733743349 2195651586283412787538439)
  ·
    refine ⟨3293477379425119181307659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2195651586283412787538439 3293477379425119181307659)
    ·
      refine ⟨4940216069137678771961489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3293477379425119181307659 4940216069137678771961489)
      ·
        refine ⟨3705162051853259078971117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4940216069137678771961489 3705162051853259078971117)
        ·
          refine ⟨1389435769444972154614169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3705162051853259078971117 1389435769444972154614169)
          ·
            refine ⟨1042076827083729115960627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1389435769444972154614169 1042076827083729115960627)
            ·
              refine ⟨1563115240625593673940941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1042076827083729115960627 1563115240625593673940941)
              ·
                refine ⟨586168215234597627727853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1563115240625593673940941 586168215234597627727853)
                ·
                  refine ⟨219813080712974110397945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 586168215234597627727853 219813080712974110397945)
                  ·
                    rfl

theorem cell21_963190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 1, 3, 3].length) (baseStart_963190 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_963190 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_963190 prefixEnd_963190 := by exact prefixLift 963190
  have htrace : WordTrace (prefixWord ++ tailWord_963190) baseStart_963190 baseEnd_963190 := by
    simpa [prefixWord, tailWord_963190, baseEnd_963190] using wordTrace_append hprefix tailTrace_963190
  have hstable : (prefixWord ++ tailWord_963190).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963190).length < 2 ^ (prefixWord ++ tailWord_963190).sum := by decide
  have hdescent : baseEnd_963190 < baseStart_963190 := by decide
  rcases family_descends (prefixWord ++ tailWord_963190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963370 : List Nat := [3, 1, 4, 3, 2, 1, 7]
def baseStart_963370 : Nat := 118140960795 + 963370 * 2 ^ 59
def prefixEnd_963370 : Nat := 4983230072969 + 3 ^ 40 * 963370 * 2
def baseEnd_963370 : Nat := 24428239907259310821953

theorem tailTrace_963370 : CollatzResearch.WordTrace tailWord_963370 prefixEnd_963370 24428239907259310821953 := by
  unfold tailWord_963370
  simp only [CollatzResearch.WordTrace]
  refine ⟨8784247629970623835541891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23424660346588330228111709 8784247629970623835541891)
  ·
    refine ⟨13176371444955935753312837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8784247629970623835541891 13176371444955935753312837)
    ·
      refine ⟨2470569645929237953746157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13176371444955935753312837 2470569645929237953746157)
      ·
        refine ⟨926463617223464232654809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2470569645929237953746157 926463617223464232654809)
        ·
          refine ⟨694847712917598174491107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 926463617223464232654809 694847712917598174491107)
          ·
            refine ⟨1042271569376397261736661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 694847712917598174491107 1042271569376397261736661)
            ·
              refine ⟨24428239907259310821953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1042271569376397261736661 24428239907259310821953)
              ·
                rfl

theorem cell21_963370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 7].length) (baseStart_963370 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_963370 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_963370 prefixEnd_963370 := by exact prefixLift 963370
  have htrace : WordTrace (prefixWord ++ tailWord_963370) baseStart_963370 baseEnd_963370 := by
    simpa [prefixWord, tailWord_963370, baseEnd_963370] using wordTrace_append hprefix tailTrace_963370
  have hstable : (prefixWord ++ tailWord_963370).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963370).length < 2 ^ (prefixWord ++ tailWord_963370).sum := by decide
  have hdescent : baseEnd_963370 < baseStart_963370 := by decide
  rcases family_descends (prefixWord ++ tailWord_963370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963381 : List Nat := [1, 3, 3, 1, 3, 1, 2, 1, 6]
def baseStart_963381 : Nat := 118140960795 + 963381 * 2 ^ 59
def prefixEnd_963381 : Nat := 4983230072969 + 3 ^ 40 * 963381 * 2
def baseEnd_963381 : Nat := 219856669515200222714221

theorem tailTrace_963381 : CollatzResearch.WordTrace tailWord_963381 prefixEnd_963381 219856669515200222714221 := by
  unfold tailWord_963381
  simp only [CollatzResearch.WordTrace]
  refine ⟨35137391722842644220817997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23424927815228429480545331 35137391722842644220817997)
  ·
    refine ⟨13176521896065991582806749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35137391722842644220817997 13176521896065991582806749)
    ·
      refine ⟨4941195711024746843552531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13176521896065991582806749 4941195711024746843552531)
      ·
        refine ⟨7411793566537120265328797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4941195711024746843552531 7411793566537120265328797)
        ·
          refine ⟨2779422587451420099498299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7411793566537120265328797 2779422587451420099498299)
          ·
            refine ⟨4169133881177130149247449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2779422587451420099498299 4169133881177130149247449)
            ·
              refine ⟨3126850410882847611935587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4169133881177130149247449 3126850410882847611935587)
              ·
                refine ⟨4690275616324271417903381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3126850410882847611935587 4690275616324271417903381)
                ·
                  refine ⟨219856669515200222714221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4690275616324271417903381 219856669515200222714221)
                  ·
                    rfl

theorem cell21_963381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 1, 6].length) (baseStart_963381 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_963381 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_963381 prefixEnd_963381 := by exact prefixLift 963381
  have htrace : WordTrace (prefixWord ++ tailWord_963381) baseStart_963381 baseEnd_963381 := by
    simpa [prefixWord, tailWord_963381, baseEnd_963381] using wordTrace_append hprefix tailTrace_963381
  have hstable : (prefixWord ++ tailWord_963381).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963381).length < 2 ^ (prefixWord ++ tailWord_963381).sum := by decide
  have hdescent : baseEnd_963381 < baseStart_963381 := by decide
  rcases family_descends (prefixWord ++ tailWord_963381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963384 : List Nat := [2, 1, 2, 1, 3, 2, 5, 2, 3]
def baseStart_963384 : Nat := 118140960795 + 963384 * 2 ^ 59
def prefixEnd_963384 : Nat := 4983230072969 + 3 ^ 40 * 963384 * 2
def baseEnd_963384 : Nat := 219857354156072884164215

theorem tailTrace_963384 : CollatzResearch.WordTrace tailWord_963384 prefixEnd_963384 219857354156072884164215 := by
  unfold tailWord_963384
  simp only [CollatzResearch.WordTrace]
  refine ⟨17568750570915887866588603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23425000761221183822118137 17568750570915887866588603)
  ·
    refine ⟨26353125856373831799882905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17568750570915887866588603 26353125856373831799882905)
    ·
      refine ⟨19764844392280373849912179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26353125856373831799882905 19764844392280373849912179)
      ·
        refine ⟨29647266588420560774868269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19764844392280373849912179 29647266588420560774868269)
        ·
          refine ⟨11117724970657710290575601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29647266588420560774868269 11117724970657710290575601)
          ·
            refine ⟨8338293727993282717931701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11117724970657710290575601 8338293727993282717931701)
            ·
              refine ⟨781715036999370254806097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8338293727993282717931701 781715036999370254806097)
              ·
                refine ⟨586286277749527691104573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 781715036999370254806097 586286277749527691104573)
                ·
                  refine ⟨219857354156072884164215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 586286277749527691104573 219857354156072884164215)
                  ·
                    rfl

theorem cell21_963384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 5, 2, 3].length) (baseStart_963384 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_963384 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_963384 prefixEnd_963384 := by exact prefixLift 963384
  have htrace : WordTrace (prefixWord ++ tailWord_963384) baseStart_963384 baseEnd_963384 := by
    simpa [prefixWord, tailWord_963384, baseEnd_963384] using wordTrace_append hprefix tailTrace_963384
  have hstable : (prefixWord ++ tailWord_963384).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963384).length < 2 ^ (prefixWord ++ tailWord_963384).sum := by decide
  have hdescent : baseEnd_963384 < baseStart_963384 := by decide
  rcases family_descends (prefixWord ++ tailWord_963384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963395 : List Nat := [1, 1, 1, 3, 1, 4, 4, 6]
def baseStart_963395 : Nat := 118140960795 + 963395 * 2 ^ 59
def prefixEnd_963395 : Nat := 4983230072969 + 3 ^ 40 * 963395 * 2
def baseEnd_963395 : Nat := 73286621501979769826953

theorem tailTrace_963395 : CollatzResearch.WordTrace tailWord_963395 prefixEnd_963395 73286621501979769826953 := by
  unfold tailWord_963395
  simp only [CollatzResearch.WordTrace]
  refine ⟨35137902344791924611827639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23425268229861283074551759 35137902344791924611827639)
  ·
    refine ⟨52706853517187886917741459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35137902344791924611827639 52706853517187886917741459)
    ·
      refine ⟨79060280275781830376612189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52706853517187886917741459 79060280275781830376612189)
      ·
        refine ⟨29647605103418186391229571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79060280275781830376612189 29647605103418186391229571)
        ·
          refine ⟨44471407655127279586844357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29647605103418186391229571 44471407655127279586844357)
          ·
            refine ⟨8338388935336364922533317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44471407655127279586844357 8338388935336364922533317)
            ·
              refine ⟨1563447925375568422974997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8338388935336364922533317 1563447925375568422974997)
              ·
                refine ⟨73286621501979769826953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1563447925375568422974997 73286621501979769826953)
                ·
                  rfl

theorem cell21_963395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 4, 6].length) (baseStart_963395 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_963395 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_963395 prefixEnd_963395 := by exact prefixLift 963395
  have htrace : WordTrace (prefixWord ++ tailWord_963395) baseStart_963395 baseEnd_963395 := by
    simpa [prefixWord, tailWord_963395, baseEnd_963395] using wordTrace_append hprefix tailTrace_963395
  have hstable : (prefixWord ++ tailWord_963395).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963395).length < 2 ^ (prefixWord ++ tailWord_963395).sum := by decide
  have hdescent : baseEnd_963395 < baseStart_963395 := by decide
  rcases family_descends (prefixWord ++ tailWord_963395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963440 : List Nat := [2, 1, 1, 1, 4, 1, 2, 3, 6]
def baseStart_963440 : Nat := 118140960795 + 963440 * 2 ^ 59
def prefixEnd_963440 : Nat := 4983230072969 + 3 ^ 40 * 963440 * 2
def baseEnd_963440 : Nat := 219870134119029231230767

theorem tailTrace_963440 : CollatzResearch.WordTrace tailWord_963440 prefixEnd_963440 219870134119029231230767 := by
  unfold tailWord_963440
  simp only [CollatzResearch.WordTrace]
  refine ⟨17569771814814448648607887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23426362419752598198143849 17569771814814448648607887)
  ·
    refine ⟨26354657722221672972911831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17569771814814448648607887 26354657722221672972911831)
    ·
      refine ⟨39531986583332509459367747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26354657722221672972911831 39531986583332509459367747)
      ·
        refine ⟨59297979874998764189051621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39531986583332509459367747 59297979874998764189051621)
        ·
          refine ⟨11118371226562268285447179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59297979874998764189051621 11118371226562268285447179)
          ·
            refine ⟨16677556839843402428170769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11118371226562268285447179 16677556839843402428170769)
            ·
              refine ⟨12508167629882551821128077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16677556839843402428170769 12508167629882551821128077)
              ·
                refine ⟨4690562861205956932923029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12508167629882551821128077 4690562861205956932923029)
                ·
                  refine ⟨219870134119029231230767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4690562861205956932923029 219870134119029231230767)
                  ·
                    rfl

theorem cell21_963440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 3, 6].length) (baseStart_963440 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_963440 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_963440 prefixEnd_963440 := by exact prefixLift 963440
  have htrace : WordTrace (prefixWord ++ tailWord_963440) baseStart_963440 baseEnd_963440 := by
    simpa [prefixWord, tailWord_963440, baseEnd_963440] using wordTrace_append hprefix tailTrace_963440
  have hstable : (prefixWord ++ tailWord_963440).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963440).length < 2 ^ (prefixWord ++ tailWord_963440).sum := by decide
  have hdescent : baseEnd_963440 < baseStart_963440 := by decide
  rcases family_descends (prefixWord ++ tailWord_963440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963508 : List Nat := [2, 5, 2, 1, 1, 2, 3, 1, 4]
def baseStart_963508 : Nat := 118140960795 + 963508 * 2 ^ 59
def prefixEnd_963508 : Nat := 4983230072969 + 3 ^ 40 * 963508 * 2
def baseEnd_963508 : Nat := 219885652645476224097295

theorem tailTrace_963508 : CollatzResearch.WordTrace tailWord_963508 prefixEnd_963508 219885652645476224097295 := by
  unfold tailWord_963508
  simp only [CollatzResearch.WordTrace]
  refine ⟨17571011896691272455345589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23428015862255029940460785 17571011896691272455345589)
  ·
    refine ⟨1647282365314806792688649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17571011896691272455345589 1647282365314806792688649)
    ·
      refine ⟨1235461773986105094516487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1647282365314806792688649 1235461773986105094516487)
      ·
        refine ⟨1853192660979157641774731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1235461773986105094516487 1853192660979157641774731)
        ·
          refine ⟨2779788991468736462662097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1853192660979157641774731 2779788991468736462662097)
          ·
            refine ⟨2084841743601552346996573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2779788991468736462662097 2084841743601552346996573)
            ·
              refine ⟨781815653850582130123715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2084841743601552346996573 781815653850582130123715)
              ·
                refine ⟨1172723480775873195185573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 781815653850582130123715 1172723480775873195185573)
                ·
                  refine ⟨219885652645476224097295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1172723480775873195185573 219885652645476224097295)
                  ·
                    rfl

theorem cell21_963508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_963508 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_963508 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_963508 prefixEnd_963508 := by exact prefixLift 963508
  have htrace : WordTrace (prefixWord ++ tailWord_963508) baseStart_963508 baseEnd_963508 := by
    simpa [prefixWord, tailWord_963508, baseEnd_963508] using wordTrace_append hprefix tailTrace_963508
  have hstable : (prefixWord ++ tailWord_963508).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963508).length < 2 ^ (prefixWord ++ tailWord_963508).sum := by decide
  have hdescent : baseEnd_963508 < baseStart_963508 := by decide
  rcases family_descends (prefixWord ++ tailWord_963508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963612 : List Nat := [2, 2, 3, 1, 4, 1, 1, 4, 3]
def baseStart_963612 : Nat := 118140960795 + 963612 * 2 ^ 59
def prefixEnd_963612 : Nat := 4983230072969 + 3 ^ 40 * 963612 * 2
def baseEnd_963612 : Nat := 219909386862395154363749

theorem tailTrace_963612 : CollatzResearch.WordTrace tailWord_963612 prefixEnd_963612 219909386862395154363749 := by
  unfold tailWord_963612
  simp only [CollatzResearch.WordTrace]
  refine ⟨17572908492502885336238545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23430544656670513781651393 17572908492502885336238545)
  ·
    refine ⟨13179681369377164002178909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17572908492502885336238545 13179681369377164002178909)
    ·
      refine ⟨4942380513516436500817091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13179681369377164002178909 4942380513516436500817091)
      ·
        refine ⟨7413570770274654751225637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4942380513516436500817091 7413570770274654751225637)
        ·
          refine ⟨1390044519426497765854807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7413570770274654751225637 1390044519426497765854807)
          ·
            refine ⟨2085066779139746648782211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1390044519426497765854807 2085066779139746648782211)
            ·
              refine ⟨3127600168709619973173317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2085066779139746648782211 3127600168709619973173317)
              ·
                refine ⟨586425031633053744969997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3127600168709619973173317 586425031633053744969997)
                ·
                  refine ⟨219909386862395154363749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 586425031633053744969997 219909386862395154363749)
                  ·
                    rfl

theorem cell21_963612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 4, 3].length) (baseStart_963612 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_963612 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_963612 prefixEnd_963612 := by exact prefixLift 963612
  have htrace : WordTrace (prefixWord ++ tailWord_963612) baseStart_963612 baseEnd_963612 := by
    simpa [prefixWord, tailWord_963612, baseEnd_963612] using wordTrace_append hprefix tailTrace_963612
  have hstable : (prefixWord ++ tailWord_963612).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963612).length < 2 ^ (prefixWord ++ tailWord_963612).sum := by decide
  have hdescent : baseEnd_963612 < baseStart_963612 := by decide
  rcases family_descends (prefixWord ++ tailWord_963612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963640 : List Nat := [2, 1, 2, 1, 5, 2, 3, 5]
def baseStart_963640 : Nat := 118140960795 + 963640 * 2 ^ 59
def prefixEnd_963640 : Nat := 4983230072969 + 3 ^ 40 * 963640 * 2
def baseEnd_963640 : Nat := 73305258947957775965675

theorem tailTrace_963640 : CollatzResearch.WordTrace tailWord_963640 prefixEnd_963640 73305258947957775965675 := by
  unfold tailWord_963640
  simp only [CollatzResearch.WordTrace]
  refine ⟨17573419114452165727248187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23431225485936220969664249 17573419114452165727248187)
  ·
    refine ⟨26360128671678248590872281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17573419114452165727248187 26360128671678248590872281)
    ·
      refine ⟨19770096503758686443154211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26360128671678248590872281 19770096503758686443154211)
      ·
        refine ⟨29655144755638029664731317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19770096503758686443154211 29655144755638029664731317)
        ·
          refine ⟨2780169820841065281068561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29655144755638029664731317 2780169820841065281068561)
          ·
            refine ⟨2085127365630798960801421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2780169820841065281068561 2085127365630798960801421)
            ·
              refine ⟨781922762111549610300533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2085127365630798960801421 781922762111549610300533)
              ·
                refine ⟨73305258947957775965675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 781922762111549610300533 73305258947957775965675)
                ·
                  rfl

theorem cell21_963640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 3, 5].length) (baseStart_963640 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_963640 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_963640 prefixEnd_963640 := by exact prefixLift 963640
  have htrace : WordTrace (prefixWord ++ tailWord_963640) baseStart_963640 baseEnd_963640 := by
    simpa [prefixWord, tailWord_963640, baseEnd_963640] using wordTrace_append hprefix tailTrace_963640
  have hstable : (prefixWord ++ tailWord_963640).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963640).length < 2 ^ (prefixWord ++ tailWord_963640).sum := by decide
  have hdescent : baseEnd_963640 < baseStart_963640 := by decide
  rcases family_descends (prefixWord ++ tailWord_963640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963705 : List Nat := [1, 2, 1, 3, 6, 1, 1, 3, 3]
def baseStart_963705 : Nat := 118140960795 + 963705 * 2 ^ 59
def prefixEnd_963705 : Nat := 4983230072969 + 3 ^ 40 * 963705 * 2
def baseEnd_963705 : Nat := 219930610729447659313559

theorem tailTrace_963705 : CollatzResearch.WordTrace tailWord_963705 prefixEnd_963705 219930610729447659313559 := by
  unfold tailWord_963705
  simp only [CollatzResearch.WordTrace]
  refine ⟨35149208973668847555612569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23432805982445898370408379 35149208973668847555612569)
  ·
    refine ⟨26361906730251635666709427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35149208973668847555612569 26361906730251635666709427)
    ·
      refine ⟨39542860095377453500064141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26361906730251635666709427 39542860095377453500064141)
      ·
        refine ⟨14828572535766545062524053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39542860095377453500064141 14828572535766545062524053)
        ·
          refine ⟨695089337614056799805815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 14828572535766545062524053 695089337614056799805815)
          ·
            refine ⟨1042634006421085199708723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 695089337614056799805815 1042634006421085199708723)
            ·
              refine ⟨1563951009631627799563085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1042634006421085199708723 1563951009631627799563085)
              ·
                refine ⟨586481628611860424836157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1563951009631627799563085 586481628611860424836157)
                ·
                  refine ⟨219930610729447659313559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 586481628611860424836157 219930610729447659313559)
                  ·
                    rfl

theorem cell21_963705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 1, 3, 3].length) (baseStart_963705 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_963705 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_963705 prefixEnd_963705 := by exact prefixLift 963705
  have htrace : WordTrace (prefixWord ++ tailWord_963705) baseStart_963705 baseEnd_963705 := by
    simpa [prefixWord, tailWord_963705, baseEnd_963705] using wordTrace_append hprefix tailTrace_963705
  have hstable : (prefixWord ++ tailWord_963705).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963705).length < 2 ^ (prefixWord ++ tailWord_963705).sum := by decide
  have hdescent : baseEnd_963705 < baseStart_963705 := by decide
  rcases family_descends (prefixWord ++ tailWord_963705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963834 : List Nat := [3, 1, 1, 1, 1, 4, 10]
def baseStart_963834 : Nat := 118140960795 + 963834 * 2 ^ 59
def prefixEnd_963834 : Nat := 4983230072969 + 3 ^ 40 * 963834 * 2
def baseEnd_963834 : Nat := 24440005587441344629255

theorem tailTrace_963834 : CollatzResearch.WordTrace tailWord_963834 prefixEnd_963834 24440005587441344629255 := by
  unfold tailWord_963834
  simp only [CollatzResearch.WordTrace]
  refine ⟨8788478497550375646764639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23435942660134335058039037 8788478497550375646764639)
  ·
    refine ⟨13182717746325563470146959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8788478497550375646764639 13182717746325563470146959)
    ·
      refine ⟨19774076619488345205220439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13182717746325563470146959 19774076619488345205220439)
      ·
        refine ⟨29661114929232517807830659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19774076619488345205220439 29661114929232517807830659)
        ·
          refine ⟨44491672393848776711745989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29661114929232517807830659 44491672393848776711745989)
          ·
            refine ⟨8342188573846645633452373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44491672393848776711745989 8342188573846645633452373)
            ·
              refine ⟨24440005587441344629255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 8342188573846645633452373 24440005587441344629255)
              ·
                rfl

theorem cell21_963834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 10].length) (baseStart_963834 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_963834 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_963834 prefixEnd_963834 := by exact prefixLift 963834
  have htrace : WordTrace (prefixWord ++ tailWord_963834) baseStart_963834 baseEnd_963834 := by
    simpa [prefixWord, tailWord_963834, baseEnd_963834] using wordTrace_append hprefix tailTrace_963834
  have hstable : (prefixWord ++ tailWord_963834).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963834).length < 2 ^ (prefixWord ++ tailWord_963834).sum := by decide
  have hdescent : baseEnd_963834 < baseStart_963834 := by decide
  rcases family_descends (prefixWord ++ tailWord_963834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963854 : List Nat := [4, 1, 1, 2, 1, 4, 3, 1, 4]
def baseStart_963854 : Nat := 118140960795 + 963854 * 2 ^ 59
def prefixEnd_963854 : Nat := 4983230072969 + 3 ^ 40 * 963854 * 2
def baseEnd_963854 : Nat := 219964614559456511329921

theorem tailTrace_963854 : CollatzResearch.WordTrace tailWord_963854 prefixEnd_963854 219964614559456511329921 := by
  unfold tailWord_963854
  simp only [CollatzResearch.WordTrace]
  refine ⟨4394330431266130750348327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23436428966752697335191077 4394330431266130750348327)
  ·
    refine ⟨6591495646899196125522491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4394330431266130750348327 6591495646899196125522491)
    ·
      refine ⟨9887243470348794188283737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6591495646899196125522491 9887243470348794188283737)
      ·
        refine ⟨7415432602761595641212803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9887243470348794188283737 7415432602761595641212803)
        ·
          refine ⟨11123148904142393461819205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7415432602761595641212803 11123148904142393461819205)
          ·
            refine ⟨2085590419526698774091101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11123148904142393461819205 2085590419526698774091101)
            ·
              refine ⟨782096407322512040284163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2085590419526698774091101 782096407322512040284163)
              ·
                refine ⟨1173144610983768060426245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 782096407322512040284163 1173144610983768060426245)
                ·
                  refine ⟨219964614559456511329921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1173144610983768060426245 219964614559456511329921)
                  ·
                    rfl

theorem cell21_963854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 3, 1, 4].length) (baseStart_963854 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_963854 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_963854 prefixEnd_963854 := by exact prefixLift 963854
  have htrace : WordTrace (prefixWord ++ tailWord_963854) baseStart_963854 baseEnd_963854 := by
    simpa [prefixWord, tailWord_963854, baseEnd_963854] using wordTrace_append hprefix tailTrace_963854
  have hstable : (prefixWord ++ tailWord_963854).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963854).length < 2 ^ (prefixWord ++ tailWord_963854).sum := by decide
  have hdescent : baseEnd_963854 < baseStart_963854 := by decide
  rcases family_descends (prefixWord ++ tailWord_963854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963896 : List Nat := [2, 1, 2, 1, 3, 1, 1, 6, 4]
def baseStart_963896 : Nat := 118140960795 + 963896 * 2 ^ 59
def prefixEnd_963896 : Nat := 4983230072969 + 3 ^ 40 * 963896 * 2
def baseEnd_963896 : Nat := 219974199531673771629835

theorem tailTrace_963896 : CollatzResearch.WordTrace tailWord_963896 prefixEnd_963896 219974199531673771629835 := by
  unfold tailWord_963896
  simp only [CollatzResearch.WordTrace]
  refine ⟨17578087657988443587907771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23437450210651258117210361 17578087657988443587907771)
  ·
    refine ⟨26367131486982665381861657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17578087657988443587907771 26367131486982665381861657)
    ·
      refine ⟨19775348615236999036396243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26367131486982665381861657 19775348615236999036396243)
      ·
        refine ⟨29663022922855498554594365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19775348615236999036396243 29663022922855498554594365)
        ·
          refine ⟨11123633596070811957972887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29663022922855498554594365 11123633596070811957972887)
          ·
            refine ⟨16685450394106217936959331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11123633596070811957972887 16685450394106217936959331)
            ·
              refine ⟨25028175591159326905438997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16685450394106217936959331 25028175591159326905438997)
              ·
                refine ⟨1173195730835593448692453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 25028175591159326905438997 1173195730835593448692453)
                ·
                  refine ⟨219974199531673771629835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1173195730835593448692453 219974199531673771629835)
                  ·
                    rfl

theorem cell21_963896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 6, 4].length) (baseStart_963896 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_963896 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_963896 prefixEnd_963896 := by exact prefixLift 963896
  have htrace : WordTrace (prefixWord ++ tailWord_963896) baseStart_963896 baseEnd_963896 := by
    simpa [prefixWord, tailWord_963896, baseEnd_963896] using wordTrace_append hprefix tailTrace_963896
  have hstable : (prefixWord ++ tailWord_963896).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963896).length < 2 ^ (prefixWord ++ tailWord_963896).sum := by decide
  have hdescent : baseEnd_963896 < baseStart_963896 := by decide
  rcases family_descends (prefixWord ++ tailWord_963896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963913 : List Nat := [1, 2, 1, 1, 2, 3, 6, 1, 4]
def baseStart_963913 : Nat := 118140960795 + 963913 * 2 ^ 59
def prefixEnd_963913 : Nat := 4983230072969 + 3 ^ 40 * 963913 * 2
def baseEnd_963913 : Nat := 219978079163285519846467

theorem tailTrace_963913 : CollatzResearch.WordTrace tailWord_963913 prefixEnd_963913 219978079163285519846467 := by
  unfold tailWord_963913
  simp only [CollatzResearch.WordTrace]
  refine ⟨35156795356915299079184393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23437863571276866052789595 35156795356915299079184393)
  ·
    refine ⟨26367596517686474309388295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35156795356915299079184393 26367596517686474309388295)
    ·
      refine ⟨39551394776529711464082443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26367596517686474309388295 39551394776529711464082443)
      ·
        refine ⟨59327092164794567196123665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39551394776529711464082443 59327092164794567196123665)
        ·
          refine ⟨44495319123595925397092749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59327092164794567196123665 44495319123595925397092749)
          ·
            refine ⟨16685744671348472023909781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44495319123595925397092749 16685744671348472023909781)
            ·
              refine ⟨782144281469459626120771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 16685744671348472023909781 782144281469459626120771)
              ·
                refine ⟨1173216422204189439181157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 782144281469459626120771 1173216422204189439181157)
                ·
                  refine ⟨219978079163285519846467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1173216422204189439181157 219978079163285519846467)
                  ·
                    rfl

theorem cell21_963913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 6, 1, 4].length) (baseStart_963913 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_963913 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_963913 prefixEnd_963913 := by exact prefixLift 963913
  have htrace : WordTrace (prefixWord ++ tailWord_963913) baseStart_963913 baseEnd_963913 := by
    simpa [prefixWord, tailWord_963913, baseEnd_963913] using wordTrace_append hprefix tailTrace_963913
  have hstable : (prefixWord ++ tailWord_963913).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963913).length < 2 ^ (prefixWord ++ tailWord_963913).sum := by decide
  have hdescent : baseEnd_963913 < baseStart_963913 := by decide
  rcases family_descends (prefixWord ++ tailWord_963913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963950 : List Nat := [4, 1, 2, 4, 1, 2, 2, 2, 3]
def baseStart_963950 : Nat := 118140960795 + 963950 * 2 ^ 59
def prefixEnd_963950 : Nat := 4983230072969 + 3 ^ 40 * 963950 * 2
def baseEnd_963950 : Nat := 219986523067381677729725

theorem tailTrace_963950 : CollatzResearch.WordTrace tailWord_963950 prefixEnd_963950 219986523067381677729725 := by
  unfold tailWord_963950
  simp only [CollatzResearch.WordTrace]
  refine ⟨4394768107222656799785163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23438763238520836265520869 4394768107222656799785163)
  ·
    refine ⟨6592152160833985199677745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4394768107222656799785163 6592152160833985199677745)
    ·
      refine ⟨4944114120625488899758309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6592152160833985199677745 4944114120625488899758309)
      ·
        refine ⟨927021397617279168704683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4944114120625488899758309 927021397617279168704683)
        ·
          refine ⟨1390532096425918753057025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 927021397617279168704683 1390532096425918753057025)
          ·
            refine ⟨1042899072319439064792769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1390532096425918753057025 1042899072319439064792769)
            ·
              refine ⟨782174304239579298594577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1042899072319439064792769 782174304239579298594577)
              ·
                refine ⟨586630728179684473945933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 782174304239579298594577 586630728179684473945933)
                ·
                  refine ⟨219986523067381677729725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 586630728179684473945933 219986523067381677729725)
                  ·
                    rfl

theorem cell21_963950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 2, 2, 3].length) (baseStart_963950 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_963950 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_963950 prefixEnd_963950 := by exact prefixLift 963950
  have htrace : WordTrace (prefixWord ++ tailWord_963950) baseStart_963950 baseEnd_963950 := by
    simpa [prefixWord, tailWord_963950, baseEnd_963950] using wordTrace_append hprefix tailTrace_963950
  have hstable : (prefixWord ++ tailWord_963950).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963950).length < 2 ^ (prefixWord ++ tailWord_963950).sum := by decide
  have hdescent : baseEnd_963950 < baseStart_963950 := by decide
  rcases family_descends (prefixWord ++ tailWord_963950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963992 : List Nat := [2, 1, 2, 5, 2, 1, 2, 3, 3]
def baseStart_963992 : Nat := 118140960795 + 963992 * 2 ^ 59
def prefixEnd_963992 : Nat := 4983230072969 + 3 ^ 40 * 963992 * 2
def baseEnd_963992 : Nat := 219996108039598938029639

theorem tailTrace_963992 : CollatzResearch.WordTrace tailWord_963992 prefixEnd_963992 219996108039598938029639 := by
  unfold tailWord_963992
  simp only [CollatzResearch.WordTrace]
  refine ⟨17579838361814547785655115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23439784482419397047540153 17579838361814547785655115)
  ·
    refine ⟨26369757542721821678482673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17579838361814547785655115 26369757542721821678482673)
    ·
      refine ⟨19777318157041366258862005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26369757542721821678482673 19777318157041366258862005)
      ·
        refine ⟨1854123577222628086768313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19777318157041366258862005 1854123577222628086768313)
        ·
          refine ⟨1390592682916971065076235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1854123577222628086768313 1390592682916971065076235)
          ·
            refine ⟨2085889024375456597614353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1390592682916971065076235 2085889024375456597614353)
            ·
              refine ⟨1564416768281592448210765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2085889024375456597614353 1564416768281592448210765)
              ·
                refine ⟨586656288105597168079037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1564416768281592448210765 586656288105597168079037)
                ·
                  refine ⟨219996108039598938029639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 586656288105597168079037 219996108039598938029639)
                  ·
                    rfl

theorem cell21_963992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 2, 3, 3].length) (baseStart_963992 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_963992 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_963992 prefixEnd_963992 := by exact prefixLift 963992
  have htrace : WordTrace (prefixWord ++ tailWord_963992) baseStart_963992 baseEnd_963992 := by
    simpa [prefixWord, tailWord_963992, baseEnd_963992] using wordTrace_append hprefix tailTrace_963992
  have hstable : (prefixWord ++ tailWord_963992).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963992).length < 2 ^ (prefixWord ++ tailWord_963992).sum := by decide
  have hdescent : baseEnd_963992 < baseStart_963992 := by decide
  rcases family_descends (prefixWord ++ tailWord_963992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964082 : List Nat := [3, 2, 1, 4, 1, 1, 4, 1, 4]
def baseStart_964082 : Nat := 118140960795 + 964082 * 2 ^ 59
def prefixEnd_964082 : Nat := 4983230072969 + 3 ^ 40 * 964082 * 2
def baseEnd_964082 : Nat := 220016647265778781529455

theorem tailTrace_964082 : CollatzResearch.WordTrace tailWord_964082 prefixEnd_964082 220016647265778781529455 := by
  unfold tailWord_964082
  simp only [CollatzResearch.WordTrace]
  refine ⟨8790739823325760235521625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23441972862202027294724333 8790739823325760235521625)
  ·
    refine ⟨6593054867494320176641219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8790739823325760235521625 6593054867494320176641219)
    ·
      refine ⟨9889582301241480264961829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6593054867494320176641219 9889582301241480264961829)
      ·
        refine ⟨1854296681482777549680343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9889582301241480264961829 1854296681482777549680343)
        ·
          refine ⟨2781445022224166324520515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1854296681482777549680343 2781445022224166324520515)
          ·
            refine ⟨4172167533336249486780773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2781445022224166324520515 4172167533336249486780773)
            ·
              refine ⟨782281412500546778771395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4172167533336249486780773 782281412500546778771395)
              ·
                refine ⟨1173422118750820168157093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 782281412500546778771395 1173422118750820168157093)
                ·
                  refine ⟨220016647265778781529455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1173422118750820168157093 220016647265778781529455)
                  ·
                    rfl

theorem cell21_964082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 4, 1, 4].length) (baseStart_964082 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_964082 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_964082 prefixEnd_964082 := by exact prefixLift 964082
  have htrace : WordTrace (prefixWord ++ tailWord_964082) baseStart_964082 baseEnd_964082 := by
    simpa [prefixWord, tailWord_964082, baseEnd_964082] using wordTrace_append hprefix tailTrace_964082
  have hstable : (prefixWord ++ tailWord_964082).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964082).length < 2 ^ (prefixWord ++ tailWord_964082).sum := by decide
  have hdescent : baseEnd_964082 < baseStart_964082 := by decide
  rcases family_descends (prefixWord ++ tailWord_964082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964127 : List Nat := [1, 1, 2, 4, 1, 1, 6, 2, 3]
def baseStart_964127 : Nat := 118140960795 + 964127 * 2 ^ 59
def prefixEnd_964127 : Nat := 4983230072969 + 3 ^ 40 * 964127 * 2
def baseEnd_964127 : Nat := 220026916878868703279363

theorem tailTrace_964127 : CollatzResearch.WordTrace tailWord_964127 prefixEnd_964127 220026916878868703279363 := by
  unfold tailWord_964127
  simp only [CollatzResearch.WordTrace]
  refine ⟨35164600578140013627474635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23443067052093342418316423 35164600578140013627474635)
  ·
    refine ⟨52746900867210020441211953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35164600578140013627474635 52746900867210020441211953)
    ·
      refine ⟨39560175650407515330908965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52746900867210020441211953 39560175650407515330908965)
      ·
        refine ⟨7417532934451409124545431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39560175650407515330908965 7417532934451409124545431)
        ·
          refine ⟨11126299401677113686818147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7417532934451409124545431 11126299401677113686818147)
          ·
            refine ⟨16689449102515670530227221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11126299401677113686818147 16689449102515670530227221)
            ·
              refine ⟨782317926680422056104401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 16689449102515670530227221 782317926680422056104401)
              ·
                refine ⟨586738445010316542078301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 782317926680422056104401 586738445010316542078301)
                ·
                  refine ⟨220026916878868703279363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 586738445010316542078301 220026916878868703279363)
                  ·
                    rfl

theorem cell21_964127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 6, 2, 3].length) (baseStart_964127 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_964127 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_964127 prefixEnd_964127 := by exact prefixLift 964127
  have htrace : WordTrace (prefixWord ++ tailWord_964127) baseStart_964127 baseEnd_964127 := by
    simpa [prefixWord, tailWord_964127, baseEnd_964127] using wordTrace_append hprefix tailTrace_964127
  have hstable : (prefixWord ++ tailWord_964127).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964127).length < 2 ^ (prefixWord ++ tailWord_964127).sum := by decide
  have hdescent : baseEnd_964127 < baseStart_964127 := by decide
  rcases family_descends (prefixWord ++ tailWord_964127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964335 : List Nat := [1, 1, 2, 1, 5, 1, 2, 2, 6]
def baseStart_964335 : Nat := 118140960795 + 964335 * 2 ^ 59
def prefixEnd_964335 : Nat := 4983230072969 + 3 ^ 40 * 964335 * 2
def baseEnd_964335 : Nat := 220074385312706563812271

theorem tailTrace_964335 : CollatzResearch.WordTrace tailWord_964335 prefixEnd_964335 220074385312706563812271 := by
  unfold tailWord_964335
  simp only [CollatzResearch.WordTrace]
  refine ⟨35172186961386465151046459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23448124640924310100697639 35172186961386465151046459)
  ·
    refine ⟨52758280442079697726569689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35172186961386465151046459 52758280442079697726569689)
    ·
      refine ⟨39568710331559773294927267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52758280442079697726569689 39568710331559773294927267)
      ·
        refine ⟨59353065497339659942390901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39568710331559773294927267 59353065497339659942390901)
        ·
          refine ⟨5564349890375593119599147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 59353065497339659942390901 5564349890375593119599147)
          ·
            refine ⟨8346524835563389679398721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5564349890375593119599147 8346524835563389679398721)
            ·
              refine ⟨6259893626672542259549041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8346524835563389679398721 6259893626672542259549041)
              ·
                refine ⟨4694920220004406694661781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6259893626672542259549041 4694920220004406694661781)
                ·
                  refine ⟨220074385312706563812271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4694920220004406694661781 220074385312706563812271)
                  ·
                    rfl

theorem cell21_964335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 2, 6].length) (baseStart_964335 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_964335 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_964335 prefixEnd_964335 := by exact prefixLift 964335
  have htrace : WordTrace (prefixWord ++ tailWord_964335) baseStart_964335 baseEnd_964335 := by
    simpa [prefixWord, tailWord_964335, baseEnd_964335] using wordTrace_append hprefix tailTrace_964335
  have hstable : (prefixWord ++ tailWord_964335).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964335).length < 2 ^ (prefixWord ++ tailWord_964335).sum := by decide
  have hdescent : baseEnd_964335 < baseStart_964335 := by decide
  rcases family_descends (prefixWord ++ tailWord_964335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964414 : List Nat := [4, 2, 1, 2, 2, 1, 3, 1, 5]
def baseStart_964414 : Nat := 118140960795 + 964414 * 2 ^ 59
def prefixEnd_964414 : Nat := 4983230072969 + 3 ^ 40 * 964414 * 2
def baseEnd_964414 : Nat := 220092414189019981995443

theorem tailTrace_964414 : CollatzResearch.WordTrace tailWord_964414 prefixEnd_964414 220092414189019981995443 := by
  unfold tailWord_964414
  simp only [CollatzResearch.WordTrace]
  refine ⟨4396883541012532705396537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23450045552066841095448197 4396883541012532705396537)
  ·
    refine ⟨3297662655759399529047403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4396883541012532705396537 3297662655759399529047403)
    ·
      refine ⟨4946493983639099293571105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3297662655759399529047403 4946493983639099293571105)
      ·
        refine ⟨3709870487729324470178329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4946493983639099293571105 3709870487729324470178329)
        ·
          refine ⟨2782402865796993352633747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3709870487729324470178329 2782402865796993352633747)
          ·
            refine ⟨4173604298695490028950621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2782402865796993352633747 4173604298695490028950621)
            ·
              refine ⟨1565101612010808760856483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4173604298695490028950621 1565101612010808760856483)
              ·
                refine ⟨2347652418016213141284725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1565101612010808760856483 2347652418016213141284725)
                ·
                  refine ⟨220092414189019981995443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2347652418016213141284725 220092414189019981995443)
                  ·
                    rfl

theorem cell21_964414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 3, 1, 5].length) (baseStart_964414 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_964414 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_964414 prefixEnd_964414 := by exact prefixLift 964414
  have htrace : WordTrace (prefixWord ++ tailWord_964414) baseStart_964414 baseEnd_964414 := by
    simpa [prefixWord, tailWord_964414, baseEnd_964414] using wordTrace_append hprefix tailTrace_964414
  have hstable : (prefixWord ++ tailWord_964414).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964414).length < 2 ^ (prefixWord ++ tailWord_964414).sum := by decide
  have hdescent : baseEnd_964414 < baseStart_964414 := by decide
  rcases family_descends (prefixWord ++ tailWord_964414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964490 : List Nat := [3, 1, 2, 4, 2, 1, 1, 2, 5]
def baseStart_964490 : Nat := 118140960795 + 964490 * 2 ^ 59
def prefixEnd_964490 : Nat := 4983230072969 + 3 ^ 40 * 964490 * 2
def baseEnd_964490 : Nat := 220109758424460738728621

theorem tailTrace_964490 : CollatzResearch.WordTrace tailWord_964490 prefixEnd_964490 220109758424460738728621 := by
  unfold tailWord_964490
  simp only [CollatzResearch.WordTrace]
  refine ⟨8794460068956231655734731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23451893517216617748625949 8794460068956231655734731)
  ·
    refine ⟨13191690103434347483602097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8794460068956231655734731 13191690103434347483602097)
    ·
      refine ⟨9893767577575760612701573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13191690103434347483602097 9893767577575760612701573)
      ·
        refine ⟨1855081420795455114881545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9893767577575760612701573 1855081420795455114881545)
        ·
          refine ⟨1391311065596591336161159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1855081420795455114881545 1391311065596591336161159)
          ·
            refine ⟨2086966598394887004241739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1391311065596591336161159 2086966598394887004241739)
            ·
              refine ⟨3130449897592330506362609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2086966598394887004241739 3130449897592330506362609)
              ·
                refine ⟨2347837423194247879771957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3130449897592330506362609 2347837423194247879771957)
                ·
                  refine ⟨220109758424460738728621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2347837423194247879771957 220109758424460738728621)
                  ·
                    rfl

theorem cell21_964490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 2, 5].length) (baseStart_964490 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_964490 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_964490 prefixEnd_964490 := by exact prefixLift 964490
  have htrace : WordTrace (prefixWord ++ tailWord_964490) baseStart_964490 baseEnd_964490 := by
    simpa [prefixWord, tailWord_964490, baseEnd_964490] using wordTrace_append hprefix tailTrace_964490
  have hstable : (prefixWord ++ tailWord_964490).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964490).length < 2 ^ (prefixWord ++ tailWord_964490).sum := by decide
  have hdescent : baseEnd_964490 < baseStart_964490 := by decide
  rcases family_descends (prefixWord ++ tailWord_964490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964577 : List Nat := [1, 2, 3, 1, 2, 1, 11]
def baseStart_964577 : Nat := 118140960795 + 964577 * 2 ^ 59
def prefixEnd_964577 : Nat := 4983230072969 + 3 ^ 40 * 964577 * 2
def baseEnd_964577 : Nat := 24458845889974213419827

theorem tailTrace_964577 : CollatzResearch.WordTrace tailWord_964577 prefixEnd_964577 24458845889974213419827 := by
  unfold tailWord_964577
  simp only [CollatzResearch.WordTrace]
  refine ⟨35181013426509740481355985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23454008951006493654237323 35181013426509740481355985)
  ·
    refine ⟨26385760069882305361016989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35181013426509740481355985 26385760069882305361016989)
    ·
      refine ⟨9894660026205864510381371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26385760069882305361016989 9894660026205864510381371)
      ·
        refine ⟨14841990039308796765572057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9894660026205864510381371 14841990039308796765572057)
        ·
          refine ⟨11131492529481597574179043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14841990039308796765572057 11131492529481597574179043)
          ·
            refine ⟨16697238794222396361268565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11131492529481597574179043 16697238794222396361268565)
            ·
              refine ⟨24458845889974213419827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 16697238794222396361268565 24458845889974213419827)
              ·
                rfl

theorem cell21_964577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 11].length) (baseStart_964577 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_964577 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_964577 prefixEnd_964577 := by exact prefixLift 964577
  have htrace : WordTrace (prefixWord ++ tailWord_964577) baseStart_964577 baseEnd_964577 := by
    simpa [prefixWord, tailWord_964577, baseEnd_964577] using wordTrace_append hprefix tailTrace_964577
  have hstable : (prefixWord ++ tailWord_964577).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964577).length < 2 ^ (prefixWord ++ tailWord_964577).sum := by decide
  have hdescent : baseEnd_964577 < baseStart_964577 := by decide
  rcases family_descends (prefixWord ++ tailWord_964577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964583 : List Nat := [1, 1, 5, 2, 4, 1, 1, 1, 5]
def baseStart_964583 : Nat := 118140960795 + 964583 * 2 ^ 59
def prefixEnd_964583 : Nat := 4983230072969 + 3 ^ 40 * 964583 * 2
def baseEnd_964583 : Nat := 220130982291513243678431

theorem tailTrace_964583 : CollatzResearch.WordTrace tailWord_964583 prefixEnd_964583 220130982291513243678431 := by
  unfold tailWord_964583
  simp only [CollatzResearch.WordTrace]
  refine ⟨35181232264488003506074403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23454154842992002337382935 35181232264488003506074403)
  ·
    refine ⟨52771848396732005259111605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35181232264488003506074403 52771848396732005259111605)
    ·
      refine ⟨4947360787193625493041713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 52771848396732005259111605 4947360787193625493041713)
      ·
        refine ⟨3710520590395219119781285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4947360787193625493041713 3710520590395219119781285)
        ·
          refine ⟨695722610699103584958991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3710520590395219119781285 695722610699103584958991)
          ·
            refine ⟨1043583916048655377438487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 695722610699103584958991 1043583916048655377438487)
            ·
              refine ⟨1565375874072983066157731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1043583916048655377438487 1565375874072983066157731)
              ·
                refine ⟨2348063811109474599236597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1565375874072983066157731 2348063811109474599236597)
                ·
                  refine ⟨220130982291513243678431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2348063811109474599236597 220130982291513243678431)
                  ·
                    rfl

theorem cell21_964583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 1, 1, 5].length) (baseStart_964583 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_964583 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_964583 prefixEnd_964583 := by exact prefixLift 964583
  have htrace : WordTrace (prefixWord ++ tailWord_964583) baseStart_964583 baseEnd_964583 := by
    simpa [prefixWord, tailWord_964583, baseEnd_964583] using wordTrace_append hprefix tailTrace_964583
  have hstable : (prefixWord ++ tailWord_964583).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964583).length < 2 ^ (prefixWord ++ tailWord_964583).sum := by decide
  have hdescent : baseEnd_964583 < baseStart_964583 := by decide
  rcases family_descends (prefixWord ++ tailWord_964583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964628 : List Nat := [2, 4, 3, 2, 2, 8]
def baseStart_964628 : Nat := 118140960795 + 964628 * 2 ^ 59
def prefixEnd_964628 : Nat := 4983230072969 + 3 ^ 40 * 964628 * 2
def baseEnd_964628 : Nat := 8153379700170487608457

theorem tailTrace_964628 : CollatzResearch.WordTrace tailWord_964628 prefixEnd_964628 8153379700170487608457 := by
  unfold tailWord_964628
  simp only [CollatzResearch.WordTrace]
  refine ⟨17591436774662488095731269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23455249032883317460975025 17591436774662488095731269)
  ·
    refine ⟨3298394395249216517949613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17591436774662488095731269 3298394395249216517949613)
    ·
      refine ⟨1236897898218456194231105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3298394395249216517949613 1236897898218456194231105)
      ·
        refine ⟨927673423663842145673329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1236897898218456194231105 927673423663842145673329)
        ·
          refine ⟨695755067747881609254997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 927673423663842145673329 695755067747881609254997)
          ·
            refine ⟨8153379700170487608457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 695755067747881609254997 8153379700170487608457)
            ·
              rfl

theorem cell21_964628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 8].length) (baseStart_964628 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_964628 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_964628 prefixEnd_964628 := by exact prefixLift 964628
  have htrace : WordTrace (prefixWord ++ tailWord_964628) baseStart_964628 baseEnd_964628 := by
    simpa [prefixWord, tailWord_964628, baseEnd_964628] using wordTrace_append hprefix tailTrace_964628
  have hstable : (prefixWord ++ tailWord_964628).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964628).length < 2 ^ (prefixWord ++ tailWord_964628).sum := by decide
  have hdescent : baseEnd_964628 < baseStart_964628 := by decide
  rcases family_descends (prefixWord ++ tailWord_964628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964642 : List Nat := [3, 3, 1, 1, 1, 2, 3, 4, 3]
def baseStart_964642 : Nat := 118140960795 + 964642 * 2 ^ 59
def prefixEnd_964642 : Nat := 4983230072969 + 3 ^ 40 * 964642 * 2
def baseEnd_964642 : Nat := 220144446895342252194977

theorem tailTrace_964642 : CollatzResearch.WordTrace tailWord_964642 prefixEnd_964642 220144446895342252194977 := by
  unfold tailWord_964642
  simp only [CollatzResearch.WordTrace]
  refine ⟨8795846042818564145618045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23455589447516171054981453 8795846042818564145618045)
  ·
    refine ⟨3298442266056961554606767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8795846042818564145618045 3298442266056961554606767)
    ·
      refine ⟨4947663399085442331910151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3298442266056961554606767 4947663399085442331910151)
      ·
        refine ⟨7421495098628163497865227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4947663399085442331910151 7421495098628163497865227)
        ·
          refine ⟨11132242647942245246797841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7421495098628163497865227 11132242647942245246797841)
          ·
            refine ⟨8349181985956683935098381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11132242647942245246797841 8349181985956683935098381)
            ·
              refine ⟨3130943244733756475661893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8349181985956683935098381 3130943244733756475661893)
              ·
                refine ⟨587051858387579339186605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3130943244733756475661893 587051858387579339186605)
                ·
                  refine ⟨220144446895342252194977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 587051858387579339186605 220144446895342252194977)
                  ·
                    rfl

theorem cell21_964642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 4, 3].length) (baseStart_964642 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_964642 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_964642 prefixEnd_964642 := by exact prefixLift 964642
  have htrace : WordTrace (prefixWord ++ tailWord_964642) baseStart_964642 baseEnd_964642 := by
    simpa [prefixWord, tailWord_964642, baseEnd_964642] using wordTrace_append hprefix tailTrace_964642
  have hstable : (prefixWord ++ tailWord_964642).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964642).length < 2 ^ (prefixWord ++ tailWord_964642).sum := by decide
  have hdescent : baseEnd_964642 < baseStart_964642 := by decide
  rcases family_descends (prefixWord ++ tailWord_964642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964690 : List Nat := [3, 2, 2, 1, 5, 1, 1, 2, 4]
def baseStart_964690 : Nat := 118140960795 + 964690 * 2 ^ 59
def prefixEnd_964690 : Nat := 4983230072969 + 3 ^ 40 * 964690 * 2
def baseEnd_964690 : Nat := 220155401149304835394879

theorem tailTrace_964690 : CollatzResearch.WordTrace tailWord_964690 prefixEnd_964690 220155401149304835394879 := by
  unfold tailWord_964690
  simp only [CollatzResearch.WordTrace]
  refine ⟨8796283718775090195054881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23456756583400240520146349 8796283718775090195054881)
  ·
    refine ⟨6597212789081317646291161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8796283718775090195054881 6597212789081317646291161)
    ·
      refine ⟨4947909591810988234718371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6597212789081317646291161 4947909591810988234718371)
      ·
        refine ⟨7421864387716482352077557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4947909591810988234718371 7421864387716482352077557)
        ·
          refine ⟨695799786348420220507271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7421864387716482352077557 695799786348420220507271)
          ·
            refine ⟨1043699679522630330760907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 695799786348420220507271 1043699679522630330760907)
            ·
              refine ⟨1565549519283945496141361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1043699679522630330760907 1565549519283945496141361)
              ·
                refine ⟨1174162139462959122106021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1565549519283945496141361 1174162139462959122106021)
                ·
                  refine ⟨220155401149304835394879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1174162139462959122106021 220155401149304835394879)
                  ·
                    rfl

theorem cell21_964690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 1, 2, 4].length) (baseStart_964690 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_964690 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_964690 prefixEnd_964690 := by exact prefixLift 964690
  have htrace : WordTrace (prefixWord ++ tailWord_964690) baseStart_964690 baseEnd_964690 := by
    simpa [prefixWord, tailWord_964690, baseEnd_964690] using wordTrace_append hprefix tailTrace_964690
  have hstable : (prefixWord ++ tailWord_964690).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964690).length < 2 ^ (prefixWord ++ tailWord_964690).sum := by decide
  have hdescent : baseEnd_964690 < baseStart_964690 := by decide
  rcases family_descends (prefixWord ++ tailWord_964690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964746 : List Nat := [3, 1, 2, 3, 1, 4, 7]
def baseStart_964746 : Nat := 118140960795 + 964746 * 2 ^ 59
def prefixEnd_964746 : Nat := 4983230072969 + 3 ^ 40 * 964746 * 2
def baseEnd_964746 : Nat := 24463131234695686940159

theorem tailTrace_964746 : CollatzResearch.WordTrace tailWord_964746 prefixEnd_964746 24463131234695686940159 := by
  unfold tailWord_964746
  simp only [CollatzResearch.WordTrace]
  refine ⟨8796794340724370586064523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23458118241931654896172061 8796794340724370586064523)
  ·
    refine ⟨13195191511086555879096785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8796794340724370586064523 13195191511086555879096785)
    ·
      refine ⟨9896393633314916909322589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13195191511086555879096785 9896393633314916909322589)
      ·
        refine ⟨3711147612493093840995971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9896393633314916909322589 3711147612493093840995971)
        ·
          refine ⟨5566721418739640761493957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3711147612493093840995971 5566721418739640761493957)
          ·
            refine ⟨1043760266013682642780117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5566721418739640761493957 1043760266013682642780117)
            ·
              refine ⟨24463131234695686940159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1043760266013682642780117 24463131234695686940159)
              ·
                rfl

theorem cell21_964746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 7].length) (baseStart_964746 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_964746 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_964746 prefixEnd_964746 := by exact prefixLift 964746
  have htrace : WordTrace (prefixWord ++ tailWord_964746) baseStart_964746 baseEnd_964746 := by
    simpa [prefixWord, tailWord_964746, baseEnd_964746] using wordTrace_append hprefix tailTrace_964746
  have hstable : (prefixWord ++ tailWord_964746).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964746).length < 2 ^ (prefixWord ++ tailWord_964746).sum := by decide
  have hdescent : baseEnd_964746 < baseStart_964746 := by decide
  rcases family_descends (prefixWord ++ tailWord_964746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964758 : List Nat := [5, 3, 2, 1, 2, 1, 2, 1, 4]
def baseStart_964758 : Nat := 118140960795 + 964758 * 2 ^ 59
def prefixEnd_964758 : Nat := 4983230072969 + 3 ^ 40 * 964758 * 2
def baseEnd_964758 : Nat := 220170919675751828261407

theorem tailTrace_964758 : CollatzResearch.WordTrace tailWord_964758 prefixEnd_964758 220170919675751828261407 := by
  unfold tailWord_964758
  simp only [CollatzResearch.WordTrace]
  refine ⟨2199225939928375524605933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23458410025902672262463285 2199225939928375524605933)
  ·
    refine ⟨824709727473140821727225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2199225939928375524605933 824709727473140821727225)
    ·
      refine ⟨618532295604855616295419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 824709727473140821727225 618532295604855616295419)
      ·
        refine ⟨927798443407283424443129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 618532295604855616295419 927798443407283424443129)
        ·
          refine ⟨695848832555462568332347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 927798443407283424443129 695848832555462568332347)
          ·
            refine ⟨1043773248833193852498521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 695848832555462568332347 1043773248833193852498521)
            ·
              refine ⟨782829936624895389373891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1043773248833193852498521 782829936624895389373891)
              ·
                refine ⟨1174244904937343084060837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 782829936624895389373891 1174244904937343084060837)
                ·
                  refine ⟨220170919675751828261407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1174244904937343084060837 220170919675751828261407)
                  ·
                    rfl

theorem cell21_964758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_964758 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_964758 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_964758 prefixEnd_964758 := by exact prefixLift 964758
  have htrace : WordTrace (prefixWord ++ tailWord_964758) baseStart_964758 baseEnd_964758 := by
    simpa [prefixWord, tailWord_964758, baseEnd_964758] using wordTrace_append hprefix tailTrace_964758
  have hstable : (prefixWord ++ tailWord_964758).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964758).length < 2 ^ (prefixWord ++ tailWord_964758).sum := by decide
  have hdescent : baseEnd_964758 < baseStart_964758 := by decide
  rcases family_descends (prefixWord ++ tailWord_964758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964839 : List Nat := [1, 1, 5, 3, 1, 2, 3, 5]
def baseStart_964839 : Nat := 118140960795 + 964839 * 2 ^ 59
def prefixEnd_964839 : Nat := 4983230072969 + 3 ^ 40 * 964839 * 2
def baseEnd_964839 : Nat := 73396468326437895803747

theorem tailTrace_964839 : CollatzResearch.WordTrace tailWord_964839 prefixEnd_964839 73396468326437895803747 := by
  unfold tailWord_964839
  simp only [CollatzResearch.WordTrace]
  refine ⟨35190569351560559227393571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23460379567707039484929047 35190569351560559227393571)
  ·
    refine ⟨52785854027340838841090357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35190569351560559227393571 52785854027340838841090357)
    ·
      refine ⟨4948673815063203641352221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 52785854027340838841090357 4948673815063203641352221)
      ·
        refine ⟨1855752680648701365507083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4948673815063203641352221 1855752680648701365507083)
        ·
          refine ⟨2783629020973052048260625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1855752680648701365507083 2783629020973052048260625)
          ·
            refine ⟨2087721765729789036195469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2783629020973052048260625 2087721765729789036195469)
            ·
              refine ⟨782895662148670888573301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2087721765729789036195469 782895662148670888573301)
              ·
                refine ⟨73396468326437895803747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 782895662148670888573301 73396468326437895803747)
                ·
                  rfl

theorem cell21_964839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 3, 5].length) (baseStart_964839 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_964839 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_964839 prefixEnd_964839 := by exact prefixLift 964839
  have htrace : WordTrace (prefixWord ++ tailWord_964839) baseStart_964839 baseEnd_964839 := by
    simpa [prefixWord, tailWord_964839, baseEnd_964839] using wordTrace_append hprefix tailTrace_964839
  have hstable : (prefixWord ++ tailWord_964839).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964839).length < 2 ^ (prefixWord ++ tailWord_964839).sum := by decide
  have hdescent : baseEnd_964839 < baseStart_964839 := by decide
  rcases family_descends (prefixWord ++ tailWord_964839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964898 : List Nat := [3, 3, 1, 1, 3, 2, 1, 7]
def baseStart_964898 : Nat := 118140960795 + 964898 * 2 ^ 59
def prefixEnd_964898 : Nat := 4983230072969 + 3 ^ 40 * 964898 * 2
def baseEnd_964898 : Nat := 73400956527714231975929

theorem tailTrace_964898 : CollatzResearch.WordTrace tailWord_964898 prefixEnd_964898 73400956527714231975929 := by
  unfold tailWord_964898
  simp only [CollatzResearch.WordTrace]
  refine ⟨8798180314586703075947837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23461814172231208202527565 8798180314586703075947837)
  ·
    refine ⟨3299317617970013653480439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8798180314586703075947837 3299317617970013653480439)
    ·
      refine ⟨4948976426955020480220659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3299317617970013653480439 4948976426955020480220659)
      ·
        refine ⟨7423464640432530720330989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4948976426955020480220659 7423464640432530720330989)
        ·
          refine ⟨2783799240162199020124121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7423464640432530720330989 2783799240162199020124121)
          ·
            refine ⟨2087849430121649265093091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2783799240162199020124121 2087849430121649265093091)
            ·
              refine ⟨3131774145182473897639637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2087849430121649265093091 3131774145182473897639637)
              ·
                refine ⟨73400956527714231975929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3131774145182473897639637 73400956527714231975929)
                ·
                  rfl

theorem cell21_964898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 7].length) (baseStart_964898 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_964898 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_964898 prefixEnd_964898 := by exact prefixLift 964898
  have htrace : WordTrace (prefixWord ++ tailWord_964898) baseStart_964898 baseEnd_964898 := by
    simpa [prefixWord, tailWord_964898, baseEnd_964898] using wordTrace_append hprefix tailTrace_964898
  have hstable : (prefixWord ++ tailWord_964898).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964898).length < 2 ^ (prefixWord ++ tailWord_964898).sum := by decide
  have hdescent : baseEnd_964898 < baseStart_964898 := by decide
  rcases family_descends (prefixWord ++ tailWord_964898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964904 : List Nat := [2, 1, 5, 1, 4, 1, 1, 3, 3]
def baseStart_964904 : Nat := 118140960795 + 964904 * 2 ^ 59
def prefixEnd_964904 : Nat := 4983230072969 + 3 ^ 40 * 964904 * 2
def baseEnd_964904 : Nat := 220204238864888018827775

theorem tailTrace_964904 : CollatzResearch.WordTrace tailWord_964904 prefixEnd_964904 220204238864888018827775 := by
  unfold tailWord_964904
  simp only [CollatzResearch.WordTrace]
  refine ⟨17596470048162537664254883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23461960064216716885673177 17596470048162537664254883)
  ·
    refine ⟨26394705072243806496382325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17596470048162537664254883 26394705072243806496382325)
    ·
      refine ⟨2474503600522856859035843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26394705072243806496382325 2474503600522856859035843)
      ·
        refine ⟨3711755400784285288553765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2474503600522856859035843 3711755400784285288553765)
        ·
          refine ⟨695954137647053491603831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3711755400784285288553765 695954137647053491603831)
          ·
            refine ⟨1043931206470580237405747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 695954137647053491603831 1043931206470580237405747)
            ·
              refine ⟨1565896809705870356108621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1043931206470580237405747 1565896809705870356108621)
              ·
                refine ⟨587211303639701383540733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1565896809705870356108621 587211303639701383540733)
                ·
                  refine ⟨220204238864888018827775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 587211303639701383540733 220204238864888018827775)
                  ·
                    rfl

theorem cell21_964904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 1, 3, 3].length) (baseStart_964904 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_964904 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_964904 prefixEnd_964904 := by exact prefixLift 964904
  have htrace : WordTrace (prefixWord ++ tailWord_964904) baseStart_964904 baseEnd_964904 := by
    simpa [prefixWord, tailWord_964904, baseEnd_964904] using wordTrace_append hprefix tailTrace_964904
  have hstable : (prefixWord ++ tailWord_964904).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964904).length < 2 ^ (prefixWord ++ tailWord_964904).sum := by decide
  have hdescent : baseEnd_964904 < baseStart_964904 := by decide
  rcases family_descends (prefixWord ++ tailWord_964904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964971 : List Nat := [1, 1, 1, 1, 2, 2, 2, 4, 7]
def baseStart_964971 : Nat := 118140960795 + 964971 * 2 ^ 59
def prefixEnd_964971 : Nat := 4983230072969 + 3 ^ 40 * 964971 * 2
def baseEnd_964971 : Nat := 220219529177710791210971

theorem tailTrace_964971 : CollatzResearch.WordTrace tailWord_964971 prefixEnd_964971 220219529177710791210971 := by
  unfold tailWord_964971
  simp only [CollatzResearch.WordTrace]
  refine ⟨35195383787082345771198767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23463589191388230514132511 35195383787082345771198767)
  ·
    refine ⟨52793075680623518656798151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35195383787082345771198767 52793075680623518656798151)
    ·
      refine ⟨79189613520935277985197227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52793075680623518656798151 79189613520935277985197227)
      ·
        refine ⟨118784420281402916977795841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79189613520935277985197227 118784420281402916977795841)
        ·
          refine ⟨89088315211052187733346881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118784420281402916977795841 89088315211052187733346881)
          ·
            refine ⟨66816236408289140800010161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89088315211052187733346881 66816236408289140800010161)
            ·
              refine ⟨50112177306216855600007621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66816236408289140800010161 50112177306216855600007621)
              ·
                refine ⟨9396033244915660425001429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50112177306216855600007621 9396033244915660425001429)
                ·
                  refine ⟨220219529177710791210971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9396033244915660425001429 220219529177710791210971)
                  ·
                    rfl

theorem cell21_964971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4, 7].length) (baseStart_964971 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_964971 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_964971 prefixEnd_964971 := by exact prefixLift 964971
  have htrace : WordTrace (prefixWord ++ tailWord_964971) baseStart_964971 baseEnd_964971 := by
    simpa [prefixWord, tailWord_964971, baseEnd_964971] using wordTrace_append hprefix tailTrace_964971
  have hstable : (prefixWord ++ tailWord_964971).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964971).length < 2 ^ (prefixWord ++ tailWord_964971).sum := by decide
  have hdescent : baseEnd_964971 < baseStart_964971 := by decide
  rcases family_descends (prefixWord ++ tailWord_964971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965064 : List Nat := [2, 1, 3, 1, 3, 2, 2, 2, 5]
def baseStart_965064 : Nat := 118140960795 + 965064 * 2 ^ 59
def prefixEnd_965064 : Nat := 4983230072969 + 3 ^ 40 * 965064 * 2
def baseEnd_965064 : Nat := 220240753044763296160781

theorem tailTrace_965064 : CollatzResearch.WordTrace tailWord_965064 prefixEnd_965064 220240753044763296160781 := by
  unfold tailWord_965064
  simp only [CollatzResearch.WordTrace]
  refine ⟨17599387887872711327167123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23465850517163615102889497 17599387887872711327167123)
  ·
    refine ⟨26399081831809066990750685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17599387887872711327167123 26399081831809066990750685)
    ·
      refine ⟨9899655686928400121531507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26399081831809066990750685 9899655686928400121531507)
      ·
        refine ⟨14849483530392600182297261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9899655686928400121531507 14849483530392600182297261)
        ·
          refine ⟨5568556323897225068361473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14849483530392600182297261 5568556323897225068361473)
          ·
            refine ⟨4176417242922918801271105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5568556323897225068361473 4176417242922918801271105)
            ·
              refine ⟨3132312932192189100953329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4176417242922918801271105 3132312932192189100953329)
              ·
                refine ⟨2349234699144141825714997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3132312932192189100953329 2349234699144141825714997)
                ·
                  refine ⟨220240753044763296160781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2349234699144141825714997 220240753044763296160781)
                  ·
                    rfl

theorem cell21_965064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 2, 5].length) (baseStart_965064 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_965064 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_965064 prefixEnd_965064 := by exact prefixLift 965064
  have htrace : WordTrace (prefixWord ++ tailWord_965064) baseStart_965064 baseEnd_965064 := by
    simpa [prefixWord, tailWord_965064, baseEnd_965064] using wordTrace_append hprefix tailTrace_965064
  have hstable : (prefixWord ++ tailWord_965064).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965064).length < 2 ^ (prefixWord ++ tailWord_965064).sum := by decide
  have hdescent : baseEnd_965064 < baseStart_965064 := by decide
  rcases family_descends (prefixWord ++ tailWord_965064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965095 : List Nat := [1, 1, 5, 2, 1, 1, 2, 4, 4]
def baseStart_965095 : Nat := 118140960795 + 965095 * 2 ^ 59
def prefixEnd_965095 : Nat := 4983230072969 + 3 ^ 40 * 965095 * 2
def baseEnd_965095 : Nat := 220247827667114131144051

theorem tailTrace_965095 : CollatzResearch.WordTrace tailWord_965095 prefixEnd_965095 220247827667114131144051 := by
  unfold tailWord_965095
  simp only [CollatzResearch.WordTrace]
  refine ⟨35199906438633114948712739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23466604292422076632475159 35199906438633114948712739)
  ·
    refine ⟨52799859657949672423069109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35199906438633114948712739 52799859657949672423069109)
    ·
      refine ⟨4949986842932781789662729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 52799859657949672423069109 4949986842932781789662729)
      ·
        refine ⟨3712490132199586342247047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4949986842932781789662729 3712490132199586342247047)
        ·
          refine ⟨5568735198299379513370571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3712490132199586342247047 5568735198299379513370571)
          ·
            refine ⟨8353102797449069270055857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5568735198299379513370571 8353102797449069270055857)
            ·
              refine ⟨6264827098086801952541893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8353102797449069270055857 6264827098086801952541893)
              ·
                refine ⟨1174655080891275366101605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6264827098086801952541893 1174655080891275366101605)
                ·
                  refine ⟨220247827667114131144051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1174655080891275366101605 220247827667114131144051)
                  ·
                    rfl

theorem cell21_965095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 4, 4].length) (baseStart_965095 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_965095 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_965095 prefixEnd_965095 := by exact prefixLift 965095
  have htrace : WordTrace (prefixWord ++ tailWord_965095) baseStart_965095 baseEnd_965095 := by
    simpa [prefixWord, tailWord_965095, baseEnd_965095] using wordTrace_append hprefix tailTrace_965095
  have hstable : (prefixWord ++ tailWord_965095).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965095).length < 2 ^ (prefixWord ++ tailWord_965095).sum := by decide
  have hdescent : baseEnd_965095 < baseStart_965095 := by decide
  rcases family_descends (prefixWord ++ tailWord_965095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965123 : List Nat := [1, 1, 1, 3, 2, 1, 4, 1, 7]
def baseStart_965123 : Nat := 118140960795 + 965123 * 2 ^ 59
def prefixEnd_965123 : Nat := 4983230072969 + 3 ^ 40 * 965123 * 2
def baseEnd_965123 : Nat := 220254217648592304677327

theorem tailTrace_965123 : CollatzResearch.WordTrace tailWord_965123 prefixEnd_965123 220254217648592304677327 := by
  unfold tailWord_965123
  simp only [CollatzResearch.WordTrace]
  refine ⟨35200927682531675730732023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23467285121687783820488015 35200927682531675730732023)
  ·
    refine ⟨52801391523797513596098035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35200927682531675730732023 52801391523797513596098035)
    ·
      refine ⟨79202087285696270394147053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52801391523797513596098035 79202087285696270394147053)
      ·
        refine ⟨29700782732136101397805145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79202087285696270394147053 29700782732136101397805145)
        ·
          refine ⟨22275587049102076048353859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29700782732136101397805145 22275587049102076048353859)
          ·
            refine ⟨33413380573653114072530789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22275587049102076048353859 33413380573653114072530789)
            ·
              refine ⟨6265008857559958888599523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33413380573653114072530789 6265008857559958888599523)
              ·
                refine ⟨9397513286339938332899285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6265008857559958888599523 9397513286339938332899285)
                ·
                  refine ⟨220254217648592304677327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9397513286339938332899285 220254217648592304677327)
                  ·
                    rfl

theorem cell21_965123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 1, 7].length) (baseStart_965123 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_965123 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_965123 prefixEnd_965123 := by exact prefixLift 965123
  have htrace : WordTrace (prefixWord ++ tailWord_965123) baseStart_965123 baseEnd_965123 := by
    simpa [prefixWord, tailWord_965123, baseEnd_965123] using wordTrace_append hprefix tailTrace_965123
  have hstable : (prefixWord ++ tailWord_965123).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965123).length < 2 ^ (prefixWord ++ tailWord_965123).sum := by decide
  have hdescent : baseEnd_965123 < baseStart_965123 := by decide
  rcases family_descends (prefixWord ++ tailWord_965123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965278 : List Nat := [4, 3, 1, 1, 1, 1, 4, 6]
def baseStart_965278 : Nat := 118140960795 + 965278 * 2 ^ 59
def prefixEnd_965278 : Nat := 4983230072969 + 3 ^ 40 * 965278 * 2
def baseEnd_965278 : Nat := 73429863586782159864559

theorem tailTrace_965278 : CollatzResearch.WordTrace tailWord_965278 prefixEnd_965278 73429863586782159864559 := by
  unfold tailWord_965278
  simp only [CollatzResearch.WordTrace]
  refine ⟨4400822624621267150328061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23471053997980091468416325 4400822624621267150328061)
  ·
    refine ⟨1650308484232975181373023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4400822624621267150328061 1650308484232975181373023)
    ·
      refine ⟨2475462726349462772059535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1650308484232975181373023 2475462726349462772059535)
      ·
        refine ⟨3713194089524194158089303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2475462726349462772059535 3713194089524194158089303)
        ·
          refine ⟨5569791134286291237133955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3713194089524194158089303 5569791134286291237133955)
          ·
            refine ⟨8354686701429436855700933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5569791134286291237133955 8354686701429436855700933)
            ·
              refine ⟨1566503756518019410443925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8354686701429436855700933 1566503756518019410443925)
              ·
                refine ⟨73429863586782159864559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1566503756518019410443925 73429863586782159864559)
                ·
                  rfl

theorem cell21_965278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 4, 6].length) (baseStart_965278 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_965278 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_965278 prefixEnd_965278 := by exact prefixLift 965278
  have htrace : WordTrace (prefixWord ++ tailWord_965278) baseStart_965278 baseEnd_965278 := by
    simpa [prefixWord, tailWord_965278, baseEnd_965278] using wordTrace_append hprefix tailTrace_965278
  have hstable : (prefixWord ++ tailWord_965278).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965278).length < 2 ^ (prefixWord ++ tailWord_965278).sum := by decide
  have hdescent : baseEnd_965278 < baseStart_965278 := by decide
  rcases family_descends (prefixWord ++ tailWord_965278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965281 : List Nat := [1, 2, 3, 3, 3, 2, 2, 1, 4]
def baseStart_965281 : Nat := 118140960795 + 965281 * 2 ^ 59
def prefixEnd_965281 : Nat := 4983230072969 + 3 ^ 40 * 965281 * 2
def baseEnd_965281 : Nat := 220290275401219141043671

theorem tailTrace_965281 : CollatzResearch.WordTrace tailWord_965281 prefixEnd_965281 220290275401219141043671 := by
  unfold tailWord_965281
  simp only [CollatzResearch.WordTrace]
  refine ⟨35206690415959268714983697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23471126943972845809989131 35206690415959268714983697)
  ·
    refine ⟨26405017811969451536237773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35206690415959268714983697 26405017811969451536237773)
    ·
      refine ⟨9901881679488544326089165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26405017811969451536237773 9901881679488544326089165)
      ·
        refine ⟨3713205629808204122283437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9901881679488544326089165 3713205629808204122283437)
        ·
          refine ⟨1392452111178076545856289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3713205629808204122283437 1392452111178076545856289)
          ·
            refine ⟨1044339083383557409392217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1392452111178076545856289 1044339083383557409392217)
            ·
              refine ⟨783254312537668057044163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1044339083383557409392217 783254312537668057044163)
              ·
                refine ⟨1174881468806502085566245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 783254312537668057044163 1174881468806502085566245)
                ·
                  refine ⟨220290275401219141043671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1174881468806502085566245 220290275401219141043671)
                  ·
                    rfl

theorem cell21_965281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 2, 1, 4].length) (baseStart_965281 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_965281 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_965281 prefixEnd_965281 := by exact prefixLift 965281
  have htrace : WordTrace (prefixWord ++ tailWord_965281) baseStart_965281 baseEnd_965281 := by
    simpa [prefixWord, tailWord_965281, baseEnd_965281] using wordTrace_append hprefix tailTrace_965281
  have hstable : (prefixWord ++ tailWord_965281).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965281).length < 2 ^ (prefixWord ++ tailWord_965281).sum := by decide
  have hdescent : baseEnd_965281 < baseStart_965281 := by decide
  rcases family_descends (prefixWord ++ tailWord_965281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965318 : List Nat := [6, 1, 2, 1, 3, 1, 2, 2, 3]
def baseStart_965318 : Nat := 118140960795 + 965318 * 2 ^ 59
def prefixEnd_965318 : Nat := 4983230072969 + 3 ^ 40 * 965318 * 2
def baseEnd_965318 : Nat := 220298719305315298926929

theorem tailTrace_965318 : CollatzResearch.WordTrace tailWord_965318 prefixEnd_965318 220298719305315298926929 := by
  unfold tailWord_965318
  simp only [CollatzResearch.WordTrace]
  refine ⟨1100251247400788251065019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 23472026611216816022720405 1100251247400788251065019)
  ·
    refine ⟨1650376871101182376597529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1100251247400788251065019 1650376871101182376597529)
    ·
      refine ⟨1237782653325886782448147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1650376871101182376597529 1237782653325886782448147)
      ·
        refine ⟨1856673979988830173672221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1237782653325886782448147 1856673979988830173672221)
        ·
          refine ⟨696252742495811315127083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1856673979988830173672221 696252742495811315127083)
          ·
            refine ⟨1044379113743716972690625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 696252742495811315127083 1044379113743716972690625)
            ·
              refine ⟨783284335307787729517969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1044379113743716972690625 783284335307787729517969)
              ·
                refine ⟨587463251480840797138477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 783284335307787729517969 587463251480840797138477)
                ·
                  refine ⟨220298719305315298926929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 587463251480840797138477 220298719305315298926929)
                  ·
                    rfl

theorem cell21_965318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 2, 2, 3].length) (baseStart_965318 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_965318 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_965318 prefixEnd_965318 := by exact prefixLift 965318
  have htrace : WordTrace (prefixWord ++ tailWord_965318) baseStart_965318 baseEnd_965318 := by
    simpa [prefixWord, tailWord_965318, baseEnd_965318] using wordTrace_append hprefix tailTrace_965318
  have hstable : (prefixWord ++ tailWord_965318).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965318).length < 2 ^ (prefixWord ++ tailWord_965318).sum := by decide
  have hdescent : baseEnd_965318 < baseStart_965318 := by decide
  rcases family_descends (prefixWord ++ tailWord_965318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965320 : List Nat := [2, 1, 3, 1, 2, 12]
def baseStart_965320 : Nat := 118140960795 + 965320 * 2 ^ 59
def prefixEnd_965320 : Nat := 4983230072969 + 3 ^ 40 * 965320 * 2
def baseEnd_965320 : Nat := 8159228730835694070133

theorem tailTrace_965320 : CollatzResearch.WordTrace tailWord_965320 prefixEnd_965320 8159228730835694070133 := by
  unfold tailWord_965320
  simp only [CollatzResearch.WordTrace]
  refine ⟨17604056431408989187826707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23472075241878652250435609 17604056431408989187826707)
  ·
    refine ⟨26406084647113483781740061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17604056431408989187826707 26406084647113483781740061)
    ·
      refine ⟨9902281742667556418152523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26406084647113483781740061 9902281742667556418152523)
      ·
        refine ⟨14853422614001334627228785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9902281742667556418152523 14853422614001334627228785)
        ·
          refine ⟨11140066960501000970421589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14853422614001334627228785 11140066960501000970421589)
          ·
            refine ⟨8159228730835694070133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 11140066960501000970421589 8159228730835694070133)
            ·
              rfl

theorem cell21_965320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 12].length) (baseStart_965320 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_965320 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_965320 prefixEnd_965320 := by exact prefixLift 965320
  have htrace : WordTrace (prefixWord ++ tailWord_965320) baseStart_965320 baseEnd_965320 := by
    simpa [prefixWord, tailWord_965320, baseEnd_965320] using wordTrace_append hprefix tailTrace_965320
  have hstable : (prefixWord ++ tailWord_965320).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965320).length < 2 ^ (prefixWord ++ tailWord_965320).sum := by decide
  have hdescent : baseEnd_965320 < baseStart_965320 := by decide
  rcases family_descends (prefixWord ++ tailWord_965320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965326 : List Nat := [4, 1, 1, 1, 3, 2, 4, 2, 3]
def baseStart_965326 : Nat := 118140960795 + 965326 * 2 ^ 59
def prefixEnd_965326 : Nat := 4983230072969 + 3 ^ 40 * 965326 * 2
def baseEnd_965326 : Nat := 220300545014309062793579

theorem tailTrace_965326 : CollatzResearch.WordTrace tailWord_965326 prefixEnd_965326 220300545014309062793579 := by
  unfold tailWord_965326
  simp only [CollatzResearch.WordTrace]
  refine ⟨4401041462599530175046479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23472221133864160933581221 4401041462599530175046479)
  ·
    refine ⟨6601562193899295262569719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4401041462599530175046479 6601562193899295262569719)
    ·
      refine ⟨9902343290848942893854579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6601562193899295262569719 9902343290848942893854579)
      ·
        refine ⟨14853514936273414340781869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9902343290848942893854579 14853514936273414340781869)
        ·
          refine ⟨5570068101102530377793201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14853514936273414340781869 5570068101102530377793201)
          ·
            refine ⟨4177551075826897783344901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5570068101102530377793201 4177551075826897783344901)
            ·
              refine ⟨783290826717543334377169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4177551075826897783344901 783290826717543334377169)
              ·
                refine ⟨587468120038157500782877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 783290826717543334377169 587468120038157500782877)
                ·
                  refine ⟨220300545014309062793579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 587468120038157500782877 220300545014309062793579)
                  ·
                    rfl

theorem cell21_965326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 4, 2, 3].length) (baseStart_965326 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_965326 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_965326 prefixEnd_965326 := by exact prefixLift 965326
  have htrace : WordTrace (prefixWord ++ tailWord_965326) baseStart_965326 baseEnd_965326 := by
    simpa [prefixWord, tailWord_965326, baseEnd_965326] using wordTrace_append hprefix tailTrace_965326
  have hstable : (prefixWord ++ tailWord_965326).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965326).length < 2 ^ (prefixWord ++ tailWord_965326).sum := by decide
  have hdescent : baseEnd_965326 < baseStart_965326 := by decide
  rcases family_descends (prefixWord ++ tailWord_965326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965340 : List Nat := [2, 2, 5, 1, 1, 1, 2, 3, 4]
def baseStart_965340 : Nat := 118140960795 + 965340 * 2 ^ 59
def prefixEnd_965340 : Nat := 4983230072969 + 3 ^ 40 * 965340 * 2
def baseEnd_965340 : Nat := 220303740005048149560217

theorem tailTrace_965340 : CollatzResearch.WordTrace tailWord_965340 prefixEnd_965340 220303740005048149560217 := by
  unfold tailWord_965340
  simp only [CollatzResearch.WordTrace]
  refine ⟨17604421161372760895690737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23472561548497014527587649 17604421161372760895690737)
  ·
    refine ⟨13203315871029570671768053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17604421161372760895690737 13203315871029570671768053)
    ·
      refine ⟨1237810862909022250478255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13203315871029570671768053 1237810862909022250478255)
      ·
        refine ⟨1856716294363533375717383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1237810862909022250478255 1856716294363533375717383)
        ·
          refine ⟨2785074441545300063576075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1856716294363533375717383 2785074441545300063576075)
          ·
            refine ⟨4177611662317950095364113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2785074441545300063576075 4177611662317950095364113)
            ·
              refine ⟨3133208746738462571523085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4177611662317950095364113 3133208746738462571523085)
              ·
                refine ⟨1174953280026923464321157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3133208746738462571523085 1174953280026923464321157)
                ·
                  refine ⟨220303740005048149560217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1174953280026923464321157 220303740005048149560217)
                  ·
                    rfl

theorem cell21_965340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 3, 4].length) (baseStart_965340 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_965340 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_965340 prefixEnd_965340 := by exact prefixLift 965340
  have htrace : WordTrace (prefixWord ++ tailWord_965340) baseStart_965340 baseEnd_965340 := by
    simpa [prefixWord, tailWord_965340, baseEnd_965340] using wordTrace_append hprefix tailTrace_965340
  have hstable : (prefixWord ++ tailWord_965340).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965340).length < 2 ^ (prefixWord ++ tailWord_965340).sum := by decide
  have hdescent : baseEnd_965340 < baseStart_965340 := by decide
  rcases family_descends (prefixWord ++ tailWord_965340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965472 : List Nat := [2, 1, 1, 3, 3, 1, 1, 9]
def baseStart_965472 : Nat := 118140960795 + 965472 * 2 ^ 59
def prefixEnd_965472 : Nat := 4983230072969 + 3 ^ 40 * 965472 * 2
def baseEnd_965472 : Nat := 73444621401148417786649

theorem tailTrace_965472 : CollatzResearch.WordTrace tailWord_965472 prefixEnd_965472 73444621401148417786649 := by
  unfold tailWord_965472
  simp only [CollatzResearch.WordTrace]
  refine ⟨17606828379133654167593335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23475771172178205556791113 17606828379133654167593335)
  ·
    refine ⟨26410242568700481251390003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17606828379133654167593335 26410242568700481251390003)
    ·
      refine ⟨39615363853050721877085005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26410242568700481251390003 39615363853050721877085005)
      ·
        refine ⟨14855761444894020703906877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39615363853050721877085005 14855761444894020703906877)
        ·
          refine ⟨5570910541835257763965079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14855761444894020703906877 5570910541835257763965079)
          ·
            refine ⟨8356365812752886645947619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5570910541835257763965079 8356365812752886645947619)
            ·
              refine ⟨12534548719129329968921429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8356365812752886645947619 12534548719129329968921429)
              ·
                refine ⟨73444621401148417786649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12534548719129329968921429 73444621401148417786649)
                ·
                  rfl

theorem cell21_965472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 9].length) (baseStart_965472 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_965472 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_965472 prefixEnd_965472 := by exact prefixLift 965472
  have htrace : WordTrace (prefixWord ++ tailWord_965472) baseStart_965472 baseEnd_965472 := by
    simpa [prefixWord, tailWord_965472, baseEnd_965472] using wordTrace_append hprefix tailTrace_965472
  have hstable : (prefixWord ++ tailWord_965472).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965472).length < 2 ^ (prefixWord ++ tailWord_965472).sum := by decide
  have hdescent : baseEnd_965472 < baseStart_965472 := by decide
  rcases family_descends (prefixWord ++ tailWord_965472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965537 : List Nat := [1, 2, 3, 4, 1, 1, 1, 5, 3]
def baseStart_965537 : Nat := 118140960795 + 965537 * 2 ^ 59
def prefixEnd_965537 : Nat := 4983230072969 + 3 ^ 40 * 965537 * 2
def baseEnd_965537 : Nat := 220348698089019584776481

theorem tailTrace_965537 : CollatzResearch.WordTrace tailWord_965537 prefixEnd_965537 220348698089019584776481 := by
  unfold tailWord_965537
  simp only [CollatzResearch.WordTrace]
  refine ⟨35216027503031824436302865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23477351668687882957535243 35216027503031824436302865)
  ·
    refine ⟨26412020627273868327227149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35216027503031824436302865 26412020627273868327227149)
    ·
      refine ⟨9904507735227700622710181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26412020627273868327227149 9904507735227700622710181)
      ·
        refine ⟨1857095200355193866758159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9904507735227700622710181 1857095200355193866758159)
        ·
          refine ⟨2785642800532790800137239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1857095200355193866758159 2785642800532790800137239)
          ·
            refine ⟨4178464200799186200205859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2785642800532790800137239 4178464200799186200205859)
            ·
              refine ⟨6267696301198779300308789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4178464200799186200205859 6267696301198779300308789)
              ·
                refine ⟨587596528237385559403949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6267696301198779300308789 587596528237385559403949)
                ·
                  refine ⟨220348698089019584776481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 587596528237385559403949 220348698089019584776481)
                  ·
                    rfl

theorem cell21_965537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 5, 3].length) (baseStart_965537 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_965537 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_965537 prefixEnd_965537 := by exact prefixLift 965537
  have htrace : WordTrace (prefixWord ++ tailWord_965537) baseStart_965537 baseEnd_965537 := by
    simpa [prefixWord, tailWord_965537, baseEnd_965537] using wordTrace_append hprefix tailTrace_965537
  have hstable : (prefixWord ++ tailWord_965537).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965537).length < 2 ^ (prefixWord ++ tailWord_965537).sum := by decide
  have hdescent : baseEnd_965537 < baseStart_965537 := by decide
  rcases family_descends (prefixWord ++ tailWord_965537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965574 : List Nat := [6, 1, 3, 1, 1, 2, 2, 5]
def baseStart_965574 : Nat := 118140960795 + 965574 * 2 ^ 59
def prefixEnd_965574 : Nat := 4983230072969 + 3 ^ 40 * 965574 * 2
def baseEnd_965574 : Nat := 73452380664371914219913

theorem tailTrace_965574 : CollatzResearch.WordTrace tailWord_965574 prefixEnd_965574 73452380664371914219913 := by
  unfold tailWord_965574
  simp only [CollatzResearch.WordTrace]
  refine ⟨1100543031371805617356243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 23478251335931853170266517 1100543031371805617356243)
  ·
    refine ⟨1650814547057708426034365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1100543031371805617356243 1650814547057708426034365)
    ·
      refine ⟨619055455146640659762887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1650814547057708426034365 619055455146640659762887)
      ·
        refine ⟨928583182719960989644331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 619055455146640659762887 928583182719960989644331)
        ·
          refine ⟨1392874774079941484466497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 928583182719960989644331 1392874774079941484466497)
          ·
            refine ⟨1044656080559956113349873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1392874774079941484466497 1044656080559956113349873)
            ·
              refine ⟨783492060419967085012405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1044656080559956113349873 783492060419967085012405)
              ·
                refine ⟨73452380664371914219913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 783492060419967085012405 73452380664371914219913)
                ·
                  rfl

theorem cell21_965574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 2, 5].length) (baseStart_965574 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_965574 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_965574 prefixEnd_965574 := by exact prefixLift 965574
  have htrace : WordTrace (prefixWord ++ tailWord_965574) baseStart_965574 baseEnd_965574 := by
    simpa [prefixWord, tailWord_965574, baseEnd_965574] using wordTrace_append hprefix tailTrace_965574
  have hstable : (prefixWord ++ tailWord_965574).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965574).length < 2 ^ (prefixWord ++ tailWord_965574).sum := by decide
  have hdescent : baseEnd_965574 < baseStart_965574 := by decide
  rcases family_descends (prefixWord ++ tailWord_965574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965579 : List Nat := [1, 1, 1, 1, 3, 5, 2, 2, 5]
def baseStart_965579 : Nat := 118140960795 + 965579 * 2 ^ 59
def prefixEnd_965579 : Nat := 4983230072969 + 3 ^ 40 * 965579 * 2
def baseEnd_965579 : Nat := 220358283061236845076395

theorem tailTrace_965579 : CollatzResearch.WordTrace tailWord_965579 prefixEnd_965579 220358283061236845076395 := by
  unfold tailWord_965579
  simp only [CollatzResearch.WordTrace]
  refine ⟨35217559368879665609331791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23478372912586443739554527 35217559368879665609331791)
  ·
    refine ⟨52826339053319498413997687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35217559368879665609331791 52826339053319498413997687)
    ·
      refine ⟨79239508579979247620996531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52826339053319498413997687 79239508579979247620996531)
      ·
        refine ⟨118859262869968871431494797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79239508579979247620996531 118859262869968871431494797)
        ·
          refine ⟨44572223576238326786810549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118859262869968871431494797 44572223576238326786810549)
          ·
            refine ⟨4178645960272343136263489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 44572223576238326786810549 4178645960272343136263489)
            ·
              refine ⟨3133984470204257352197617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4178645960272343136263489 3133984470204257352197617)
              ·
                refine ⟨2350488352653193014148213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3133984470204257352197617 2350488352653193014148213)
                ·
                  refine ⟨220358283061236845076395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2350488352653193014148213 220358283061236845076395)
                  ·
                    rfl

theorem cell21_965579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 2, 5].length) (baseStart_965579 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_965579 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_965579 prefixEnd_965579 := by exact prefixLift 965579
  have htrace : WordTrace (prefixWord ++ tailWord_965579) baseStart_965579 baseEnd_965579 := by
    simpa [prefixWord, tailWord_965579, baseEnd_965579] using wordTrace_append hprefix tailTrace_965579
  have hstable : (prefixWord ++ tailWord_965579).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965579).length < 2 ^ (prefixWord ++ tailWord_965579).sum := by decide
  have hdescent : baseEnd_965579 < baseStart_965579 := by decide
  rcases family_descends (prefixWord ++ tailWord_965579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965582 : List Nat := [4, 1, 1, 1, 2, 5, 2, 5]
def baseStart_965582 : Nat := 118140960795 + 965582 * 2 ^ 59
def prefixEnd_965582 : Nat := 4983230072969 + 3 ^ 40 * 965582 * 2
def baseEnd_965582 : Nat := 73452989234036502175463

theorem tailTrace_965582 : CollatzResearch.WordTrace tailWord_965582 prefixEnd_965582 73452989234036502175463 := by
  unfold tailWord_965582
  simp only [CollatzResearch.WordTrace]
  refine ⟨4402208598483599640211375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23478445858579198081127333 4402208598483599640211375)
  ·
    refine ⟨6603312897725399460317063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4402208598483599640211375 6603312897725399460317063)
    ·
      refine ⟨9904969346588099190475595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6603312897725399460317063 9904969346588099190475595)
      ·
        refine ⟨14857454019882148785713393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9904969346588099190475595 14857454019882148785713393)
        ·
          refine ⟨11143090514911611589285045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14857454019882148785713393 11143090514911611589285045)
          ·
            refine ⟨1044664735772963586495473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11143090514911611589285045 1044664735772963586495473)
            ·
              refine ⟨783498551829722689871605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1044664735772963586495473 783498551829722689871605)
              ·
                refine ⟨73452989234036502175463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 783498551829722689871605 73452989234036502175463)
                ·
                  rfl

theorem cell21_965582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 2, 5].length) (baseStart_965582 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_965582 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_965582 prefixEnd_965582 := by exact prefixLift 965582
  have htrace : WordTrace (prefixWord ++ tailWord_965582) baseStart_965582 baseEnd_965582 := by
    simpa [prefixWord, tailWord_965582, baseEnd_965582] using wordTrace_append hprefix tailTrace_965582
  have hstable : (prefixWord ++ tailWord_965582).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965582).length < 2 ^ (prefixWord ++ tailWord_965582).sum := by decide
  have hdescent : baseEnd_965582 < baseStart_965582 := by decide
  rcases family_descends (prefixWord ++ tailWord_965582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965610 : List Nat := [3, 1, 3, 1, 2, 2, 2, 1, 6]
def baseStart_965610 : Nat := 118140960795 + 965610 * 2 ^ 59
def prefixEnd_965610 : Nat := 4983230072969 + 3 ^ 40 * 965610 * 2
def baseEnd_965610 : Nat := 220365357683587680059665

theorem tailTrace_965610 : CollatzResearch.WordTrace tailWord_965610 prefixEnd_965610 220365357683587680059665 := by
  unfold tailWord_965610
  simp only [CollatzResearch.WordTrace]
  refine ⟨8804672507941839475927571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23479126687844905269140189 8804672507941839475927571)
  ·
    refine ⟨13207008761912759213891357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8804672507941839475927571 13207008761912759213891357)
    ·
      refine ⟨4952628285717284705209259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13207008761912759213891357 4952628285717284705209259)
      ·
        refine ⟨7428942428575927057813889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4952628285717284705209259 7428942428575927057813889)
        ·
          refine ⟨5571706821431945293360417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7428942428575927057813889 5571706821431945293360417)
          ·
            refine ⟨4178780116073958970020313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5571706821431945293360417 4178780116073958970020313)
            ·
              refine ⟨3134085087055469227515235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4178780116073958970020313 3134085087055469227515235)
              ·
                refine ⟨4701127630583203841272853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3134085087055469227515235 4701127630583203841272853)
                ·
                  refine ⟨220365357683587680059665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4701127630583203841272853 220365357683587680059665)
                  ·
                    rfl

theorem cell21_965610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 1, 6].length) (baseStart_965610 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_965610 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_965610 prefixEnd_965610 := by exact prefixLift 965610
  have htrace : WordTrace (prefixWord ++ tailWord_965610) baseStart_965610 baseEnd_965610 := by
    simpa [prefixWord, tailWord_965610, baseEnd_965610] using wordTrace_append hprefix tailTrace_965610
  have hstable : (prefixWord ++ tailWord_965610).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965610).length < 2 ^ (prefixWord ++ tailWord_965610).sum := by decide
  have hdescent : baseEnd_965610 < baseStart_965610 := by decide
  rcases family_descends (prefixWord ++ tailWord_965610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965664 : List Nat := [2, 1, 1, 7, 2, 1, 2, 2, 3]
def baseStart_965664 : Nat := 118140960795 + 965664 * 2 ^ 59
def prefixEnd_965664 : Nat := 4983230072969 + 3 ^ 40 * 965664 * 2
def baseEnd_965664 : Nat := 220377681219295586159555

theorem tailTrace_965664 : CollatzResearch.WordTrace tailWord_965664 prefixEnd_965664 220377681219295586159555 := by
  unfold tailWord_965664
  simp only [CollatzResearch.WordTrace]
  refine ⟨17610329786785862563088023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23480439715714483417450697 17610329786785862563088023)
  ·
    refine ⟨26415494680178793844632035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17610329786785862563088023 26415494680178793844632035)
    ·
      refine ⟨39623242020268190766948053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26415494680178793844632035 39623242020268190766948053)
      ·
        refine ⟨928669734850035721100345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 39623242020268190766948053 928669734850035721100345)
        ·
          refine ⟨696502301137526790825259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 928669734850035721100345 696502301137526790825259)
          ·
            refine ⟨1044753451706290186237889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 696502301137526790825259 1044753451706290186237889)
            ·
              refine ⟨783565088779717639678417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1044753451706290186237889 783565088779717639678417)
              ·
                refine ⟨587673816584788229758813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 783565088779717639678417 587673816584788229758813)
                ·
                  refine ⟨220377681219295586159555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 587673816584788229758813 220377681219295586159555)
                  ·
                    rfl

theorem cell21_965664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 2, 2, 3].length) (baseStart_965664 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_965664 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_965664 prefixEnd_965664 := by exact prefixLift 965664
  have htrace : WordTrace (prefixWord ++ tailWord_965664) baseStart_965664 baseEnd_965664 := by
    simpa [prefixWord, tailWord_965664, baseEnd_965664] using wordTrace_append hprefix tailTrace_965664
  have hstable : (prefixWord ++ tailWord_965664).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965664).length < 2 ^ (prefixWord ++ tailWord_965664).sum := by decide
  have hdescent : baseEnd_965664 < baseStart_965664 := by decide
  rcases family_descends (prefixWord ++ tailWord_965664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965796 : List Nat := [2, 3, 1, 2, 3, 3, 2, 1, 4]
def baseStart_965796 : Nat := 118140960795 + 965796 * 2 ^ 59
def prefixEnd_965796 : Nat := 4983230072969 + 3 ^ 40 * 965796 * 2
def baseEnd_965796 : Nat := 220407805417692689959285

theorem tailTrace_965796 : CollatzResearch.WordTrace tailWord_965796 prefixEnd_965796 220407805417692689959285 := by
  unfold tailWord_965796
  simp only [CollatzResearch.WordTrace]
  refine ⟨17612737004546755834990621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23483649339395674446654161 17612737004546755834990621)
  ·
    refine ⟨6604776376705033438121483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17612737004546755834990621 6604776376705033438121483)
    ·
      refine ⟨9907164565057550157182225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6604776376705033438121483 9907164565057550157182225)
      ·
        refine ⟨7430373423793162617886669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9907164565057550157182225 7430373423793162617886669)
        ·
          refine ⟨2786390033922435981707501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7430373423793162617886669 2786390033922435981707501)
          ·
            refine ⟨1044896262720913493140313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2786390033922435981707501 1044896262720913493140313)
            ·
              refine ⟨783672197040685119855235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1044896262720913493140313 783672197040685119855235)
              ·
                refine ⟨1175508295561027679782853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 783672197040685119855235 1175508295561027679782853)
                ·
                  refine ⟨220407805417692689959285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1175508295561027679782853 220407805417692689959285)
                  ·
                    rfl

theorem cell21_965796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 2, 1, 4].length) (baseStart_965796 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_965796 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_965796 prefixEnd_965796 := by exact prefixLift 965796
  have htrace : WordTrace (prefixWord ++ tailWord_965796) baseStart_965796 baseEnd_965796 := by
    simpa [prefixWord, tailWord_965796, baseEnd_965796] using wordTrace_append hprefix tailTrace_965796
  have hstable : (prefixWord ++ tailWord_965796).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965796).length < 2 ^ (prefixWord ++ tailWord_965796).sum := by decide
  have hdescent : baseEnd_965796 < baseStart_965796 := by decide
  rcases family_descends (prefixWord ++ tailWord_965796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965821 : List Nat := [1, 4, 1, 2, 1, 1, 2, 1, 8]
def baseStart_965821 : Nat := 118140960795 + 965821 * 2 ^ 59
def prefixEnd_965821 : Nat := 4983230072969 + 3 ^ 40 * 965821 * 2
def baseEnd_965821 : Nat := 220413510758298202042567

theorem tailTrace_965821 : CollatzResearch.WordTrace tailWord_965821 prefixEnd_965821 220413510758298202042567 := by
  unfold tailWord_965821
  simp only [CollatzResearch.WordTrace]
  refine ⟨35226385834002940939641317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23484257222668627293094211 35226385834002940939641317)
  ·
    refine ⟨6604947343875551426182747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35226385834002940939641317 6604947343875551426182747)
    ·
      refine ⟨9907421015813327139274121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6604947343875551426182747 9907421015813327139274121)
      ·
        refine ⟨7430565761859995354455591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9907421015813327139274121 7430565761859995354455591)
        ·
          refine ⟨11145848642789993031683387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7430565761859995354455591 11145848642789993031683387)
          ·
            refine ⟨16718772964184989547525081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11145848642789993031683387 16718772964184989547525081)
            ·
              refine ⟨12539079723138742160643811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16718772964184989547525081 12539079723138742160643811)
              ·
                refine ⟨18808619584708113240965717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12539079723138742160643811 18808619584708113240965717)
                ·
                  refine ⟨220413510758298202042567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18808619584708113240965717 220413510758298202042567)
                  ·
                    rfl

theorem cell21_965821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 1, 8].length) (baseStart_965821 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_965821 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_965821 prefixEnd_965821 := by exact prefixLift 965821
  have htrace : WordTrace (prefixWord ++ tailWord_965821) baseStart_965821 baseEnd_965821 := by
    simpa [prefixWord, tailWord_965821, baseEnd_965821] using wordTrace_append hprefix tailTrace_965821
  have hstable : (prefixWord ++ tailWord_965821).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965821).length < 2 ^ (prefixWord ++ tailWord_965821).sum := by decide
  have hdescent : baseEnd_965821 < baseStart_965821 := by decide
  rcases family_descends (prefixWord ++ tailWord_965821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965830 : List Nat := [6, 1, 2, 2, 1, 1, 2, 2, 4]
def baseStart_965830 : Nat := 118140960795 + 965830 * 2 ^ 59
def prefixEnd_965830 : Nat := 4983230072969 + 3 ^ 40 * 965830 * 2
def baseEnd_965830 : Nat := 220415564680916186392549

theorem tailTrace_965830 : CollatzResearch.WordTrace tailWord_965830 prefixEnd_965830 220415564680916186392549 := by
  unfold tailWord_965830
  simp only [CollatzResearch.WordTrace]
  refine ⟨1100834815342822983647467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 23484476060646890317812629 1100834815342822983647467)
  ·
    refine ⟨1651252223014234475471201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1100834815342822983647467 1651252223014234475471201)
    ·
      refine ⟨1238439167260675856603401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1651252223014234475471201 1238439167260675856603401)
      ·
        refine ⟨928829375445506892452551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1238439167260675856603401 928829375445506892452551)
        ·
          refine ⟨1393244063168260338678827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 928829375445506892452551 1393244063168260338678827)
          ·
            refine ⟨2089866094752390508018241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1393244063168260338678827 2089866094752390508018241)
            ·
              refine ⟨1567399571064292881013681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2089866094752390508018241 1567399571064292881013681)
              ·
                refine ⟨1175549678298219660760261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1567399571064292881013681 1175549678298219660760261)
                ·
                  refine ⟨220415564680916186392549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1175549678298219660760261 220415564680916186392549)
                  ·
                    rfl

theorem cell21_965830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_965830 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_965830 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_965830 prefixEnd_965830 := by exact prefixLift 965830
  have htrace : WordTrace (prefixWord ++ tailWord_965830) baseStart_965830 baseEnd_965830 := by
    simpa [prefixWord, tailWord_965830, baseEnd_965830] using wordTrace_append hprefix tailTrace_965830
  have hstable : (prefixWord ++ tailWord_965830).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965830).length < 2 ^ (prefixWord ++ tailWord_965830).sum := by decide
  have hdescent : baseEnd_965830 < baseStart_965830 := by decide
  rcases family_descends (prefixWord ++ tailWord_965830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965897 : List Nat := [1, 2, 1, 1, 3, 3, 3, 1, 6]
def baseStart_965897 : Nat := 118140960795 + 965897 * 2 ^ 59
def prefixEnd_965897 : Nat := 4983230072969 + 3 ^ 40 * 965897 * 2
def baseEnd_965897 : Nat := 220430854993738958775745

theorem tailTrace_965897 : CollatzResearch.WordTrace tailWord_965897 prefixEnd_965897 220430854993738958775745 := by
  unfold tailWord_965897
  simp only [CollatzResearch.WordTrace]
  refine ⟨35229157781727605919407945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23486105187818403946271963 35229157781727605919407945)
  ·
    refine ⟨26421868336295704439555959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35229157781727605919407945 26421868336295704439555959)
    ·
      refine ⟨39632802504443556659333939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26421868336295704439555959 39632802504443556659333939)
      ·
        refine ⟨59449203756665334989000909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39632802504443556659333939 59449203756665334989000909)
        ·
          refine ⟨22293451408749500620875341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59449203756665334989000909 22293451408749500620875341)
          ·
            refine ⟨8360044278281062732828253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22293451408749500620875341 8360044278281062732828253)
            ·
              refine ⟨3135016604355398524810595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8360044278281062732828253 3135016604355398524810595)
              ·
                refine ⟨4702524906533097787215893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3135016604355398524810595 4702524906533097787215893)
                ·
                  refine ⟨220430854993738958775745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4702524906533097787215893 220430854993738958775745)
                  ·
                    rfl

theorem cell21_965897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 1, 6].length) (baseStart_965897 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_965897 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_965897 prefixEnd_965897 := by exact prefixLift 965897
  have htrace : WordTrace (prefixWord ++ tailWord_965897) baseStart_965897 baseEnd_965897 := by
    simpa [prefixWord, tailWord_965897, baseEnd_965897] using wordTrace_append hprefix tailTrace_965897
  have hstable : (prefixWord ++ tailWord_965897).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965897).length < 2 ^ (prefixWord ++ tailWord_965897).sum := by decide
  have hdescent : baseEnd_965897 < baseStart_965897 := by decide
  rcases family_descends (prefixWord ++ tailWord_965897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965900 : List Nat := [2, 2, 1, 2, 2, 3, 2, 4, 3]
def baseStart_965900 : Nat := 118140960795 + 965900 * 2 ^ 59
def prefixEnd_965900 : Nat := 4983230072969 + 3 ^ 40 * 965900 * 2
def baseEnd_965900 : Nat := 220431539634611620225739

theorem tailTrace_965900 : CollatzResearch.WordTrace tailWord_965900 prefixEnd_965900 220431539634611620225739 := by
  unfold tailWord_965900
  simp only [CollatzResearch.WordTrace]
  refine ⟨17614633600358368715883577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23486178133811158287844769 17614633600358368715883577)
  ·
    refine ⟨13210975200268776536912683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17614633600358368715883577 13210975200268776536912683)
    ·
      refine ⟨19816462800403164805369025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13210975200268776536912683 19816462800403164805369025)
      ·
        refine ⟨14862347100302373604026769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19816462800403164805369025 14862347100302373604026769)
        ·
          refine ⟨11146760325226780203020077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14862347100302373604026769 11146760325226780203020077)
          ·
            refine ⟨4180035121960042576132529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11146760325226780203020077 4180035121960042576132529)
            ·
              refine ⟨3135026341470031932099397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4180035121960042576132529 3135026341470031932099397)
              ·
                refine ⟨587817439025630987268637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3135026341470031932099397 587817439025630987268637)
                ·
                  refine ⟨220431539634611620225739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 587817439025630987268637 220431539634611620225739)
                  ·
                    rfl

theorem cell21_965900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 4, 3].length) (baseStart_965900 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_965900 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_965900 prefixEnd_965900 := by exact prefixLift 965900
  have htrace : WordTrace (prefixWord ++ tailWord_965900) baseStart_965900 baseEnd_965900 := by
    simpa [prefixWord, tailWord_965900, baseEnd_965900] using wordTrace_append hprefix tailTrace_965900
  have hstable : (prefixWord ++ tailWord_965900).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965900).length < 2 ^ (prefixWord ++ tailWord_965900).sum := by decide
  have hdescent : baseEnd_965900 < baseStart_965900 := by decide
  rcases family_descends (prefixWord ++ tailWord_965900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965945 : List Nat := [1, 2, 1, 6, 2, 2, 7]
def baseStart_965945 : Nat := 118140960795 + 965945 * 2 ^ 59
def prefixEnd_965945 : Nat := 4983230072969 + 3 ^ 40 * 965945 * 2
def baseEnd_965945 : Nat := 24493534360855726886183

theorem tailTrace_965945 : CollatzResearch.WordTrace tailWord_965945 prefixEnd_965945 24493534360855726886183 := by
  unfold tailWord_965945
  simp only [CollatzResearch.WordTrace]
  refine ⟨35230908485553710117155289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23487272323702473411436859 35230908485553710117155289)
  ·
    refine ⟨26423181364165282587866467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35230908485553710117155289 26423181364165282587866467)
    ·
      refine ⟨39634772046247923881799701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26423181364165282587866467 39634772046247923881799701)
      ·
        refine ⟨1857879939667871431959361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 39634772046247923881799701 1857879939667871431959361)
        ·
          refine ⟨1393409954750903573969521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1857879939667871431959361 1393409954750903573969521)
          ·
            refine ⟨1045057466063177680477141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1393409954750903573969521 1045057466063177680477141)
            ·
              refine ⟨24493534360855726886183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1045057466063177680477141 24493534360855726886183)
              ·
                rfl

theorem cell21_965945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 7].length) (baseStart_965945 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_965945 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_965945 prefixEnd_965945 := by exact prefixLift 965945
  have htrace : WordTrace (prefixWord ++ tailWord_965945) baseStart_965945 baseEnd_965945 := by
    simpa [prefixWord, tailWord_965945, baseEnd_965945] using wordTrace_append hprefix tailTrace_965945
  have hstable : (prefixWord ++ tailWord_965945).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965945).length < 2 ^ (prefixWord ++ tailWord_965945).sum := by decide
  have hdescent : baseEnd_965945 < baseStart_965945 := by decide
  rcases family_descends (prefixWord ++ tailWord_965945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965959 : List Nat := [1, 1, 4, 1, 2, 3, 3, 1, 5]
def baseStart_965959 : Nat := 118140960795 + 965959 * 2 ^ 59
def prefixEnd_965959 : Nat := 4983230072969 + 3 ^ 40 * 965959 * 2
def baseEnd_965959 : Nat := 220445004238440628742285

theorem tailTrace_965959 : CollatzResearch.WordTrace tailWord_965959 prefixEnd_965959 220445004238440628742285 := by
  unfold tailWord_965959
  simp only [CollatzResearch.WordTrace]
  refine ⟨35231419107502990508164931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23487612738335327005443287 35231419107502990508164931)
  ·
    refine ⟨52847128661254485762247397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35231419107502990508164931 52847128661254485762247397)
    ·
      refine ⟨9908836623985216080421387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52847128661254485762247397 9908836623985216080421387)
      ·
        refine ⟨14863254935977824120632081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9908836623985216080421387 14863254935977824120632081)
        ·
          refine ⟨11147441201983368090474061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14863254935977824120632081 11147441201983368090474061)
          ·
            refine ⟨4180290450743763033927773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11147441201983368090474061 4180290450743763033927773)
            ·
              refine ⟨1567608919028911137722915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4180290450743763033927773 1567608919028911137722915)
              ·
                refine ⟨2351413378543366706584373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1567608919028911137722915 2351413378543366706584373)
                ·
                  refine ⟨220445004238440628742285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2351413378543366706584373 220445004238440628742285)
                  ·
                    rfl

theorem cell21_965959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 3, 1, 5].length) (baseStart_965959 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_965959 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_965959 prefixEnd_965959 := by exact prefixLift 965959
  have htrace : WordTrace (prefixWord ++ tailWord_965959) baseStart_965959 baseEnd_965959 := by
    simpa [prefixWord, tailWord_965959, baseEnd_965959] using wordTrace_append hprefix tailTrace_965959
  have hstable : (prefixWord ++ tailWord_965959).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965959).length < 2 ^ (prefixWord ++ tailWord_965959).sum := by decide
  have hdescent : baseEnd_965959 < baseStart_965959 := by decide
  rcases family_descends (prefixWord ++ tailWord_965959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966308 : List Nat := [2, 3, 1, 2, 2, 3, 2, 6]
def baseStart_966308 : Nat := 118140960795 + 966308 * 2 ^ 59
def prefixEnd_966308 : Nat := 4983230072969 + 3 ^ 40 * 966308 * 2
def baseEnd_966308 : Nat := 73508216931097859141635

theorem tailTrace_966308 : CollatzResearch.WordTrace tailWord_966308 prefixEnd_966308 73508216931097859141635 := by
  unfold tailWord_966308
  simp only [CollatzResearch.WordTrace]
  refine ⟨17622074091619311556309789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23496098788825748741746385 17622074091619311556309789)
  ·
    refine ⟨6608277784357241833616171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17622074091619311556309789 6608277784357241833616171)
    ·
      refine ⟨9912416676535862750424257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6608277784357241833616171 9912416676535862750424257)
      ·
        refine ⟨7434312507401897062818193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9912416676535862750424257 7434312507401897062818193)
        ·
          refine ⟨5575734380551422797113645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7434312507401897062818193 5575734380551422797113645)
          ·
            refine ⟨2090900392706783548917617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5575734380551422797113645 2090900392706783548917617)
            ·
              refine ⟨1568175294530087661688213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2090900392706783548917617 1568175294530087661688213)
              ·
                refine ⟨73508216931097859141635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1568175294530087661688213 73508216931097859141635)
                ·
                  rfl

theorem cell21_966308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 2, 6].length) (baseStart_966308 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_966308 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_966308 prefixEnd_966308 := by exact prefixLift 966308
  have htrace : WordTrace (prefixWord ++ tailWord_966308) baseStart_966308 baseEnd_966308 := by
    simpa [prefixWord, tailWord_966308, baseEnd_966308] using wordTrace_append hprefix tailTrace_966308
  have hstable : (prefixWord ++ tailWord_966308).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966308).length < 2 ^ (prefixWord ++ tailWord_966308).sum := by decide
  have hdescent : baseEnd_966308 < baseStart_966308 := by decide
  rcases family_descends (prefixWord ++ tailWord_966308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966322 : List Nat := [3, 2, 1, 1, 1, 2, 2, 4, 5]
def baseStart_966322 : Nat := 118140960795 + 966322 * 2 ^ 59
def prefixEnd_966322 : Nat := 4983230072969 + 3 ^ 40 * 966322 * 2
def baseEnd_966322 : Nat := 220527845784032664191543

theorem tailTrace_966322 : CollatzResearch.WordTrace tailWord_966322 prefixEnd_966322 220527845784032664191543 := by
  unfold tailWord_966322
  simp only [CollatzResearch.WordTrace]
  refine ⟨8811164701296975875907305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23496439203458602335752813 8811164701296975875907305)
  ·
    refine ⟨6608373525972731906930479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8811164701296975875907305 6608373525972731906930479)
    ·
      refine ⟨9912560288959097860395719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6608373525972731906930479 9912560288959097860395719)
      ·
        refine ⟨14868840433438646790593579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9912560288959097860395719 14868840433438646790593579)
        ·
          refine ⟨22303260650157970185890369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14868840433438646790593579 22303260650157970185890369)
          ·
            refine ⟨16727445487618477639417777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22303260650157970185890369 16727445487618477639417777)
            ·
              refine ⟨12545584115713858229563333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16727445487618477639417777 12545584115713858229563333)
              ·
                refine ⟨2352297021696348418043125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12545584115713858229563333 2352297021696348418043125)
                ·
                  refine ⟨220527845784032664191543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2352297021696348418043125 220527845784032664191543)
                  ·
                    rfl

theorem cell21_966322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 4, 5].length) (baseStart_966322 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_966322 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_966322 prefixEnd_966322 := by exact prefixLift 966322
  have htrace : WordTrace (prefixWord ++ tailWord_966322) baseStart_966322 baseEnd_966322 := by
    simpa [prefixWord, tailWord_966322, baseEnd_966322] using wordTrace_append hprefix tailTrace_966322
  have hstable : (prefixWord ++ tailWord_966322).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966322).length < 2 ^ (prefixWord ++ tailWord_966322).sum := by decide
  have hdescent : baseEnd_966322 < baseStart_966322 := by decide
  rcases family_descends (prefixWord ++ tailWord_966322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966353 : List Nat := [1, 2, 2, 1, 2, 4, 1, 4, 4]
def baseStart_966353 : Nat := 118140960795 + 966353 * 2 ^ 59
def prefixEnd_966353 : Nat := 4983230072969 + 3 ^ 40 * 966353 * 2
def baseEnd_966353 : Nat := 220534920406383499174813

theorem tailTrace_966353 : CollatzResearch.WordTrace tailWord_966353 prefixEnd_966353 220534920406383499174813 := by
  unfold tailWord_966353
  simp only [CollatzResearch.WordTrace]
  refine ⟨35245789468075595798007713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23497192978717063865338475 35245789468075595798007713)
  ·
    refine ⟨26434342101056696848505785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35245789468075595798007713 26434342101056696848505785)
    ·
      refine ⟨19825756575792522636379339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26434342101056696848505785 19825756575792522636379339)
      ·
        refine ⟨29738634863688783954569009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19825756575792522636379339 29738634863688783954569009)
        ·
          refine ⟨22303976147766587965926757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29738634863688783954569009 22303976147766587965926757)
          ·
            refine ⟨4181995527706235243611267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22303976147766587965926757 4181995527706235243611267)
            ·
              refine ⟨6272993291559352865416901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4181995527706235243611267 6272993291559352865416901)
              ·
                refine ⟨1176186242167378662265669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6272993291559352865416901 1176186242167378662265669)
                ·
                  refine ⟨220534920406383499174813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1176186242167378662265669 220534920406383499174813)
                  ·
                    rfl

theorem cell21_966353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 4, 4].length) (baseStart_966353 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_966353 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_966353 prefixEnd_966353 := by exact prefixLift 966353
  have htrace : WordTrace (prefixWord ++ tailWord_966353) baseStart_966353 baseEnd_966353 := by
    simpa [prefixWord, tailWord_966353, baseEnd_966353] using wordTrace_append hprefix tailTrace_966353
  have hstable : (prefixWord ++ tailWord_966353).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966353).length < 2 ^ (prefixWord ++ tailWord_966353).sum := by decide
  have hdescent : baseEnd_966353 < baseStart_966353 := by decide
  rcases family_descends (prefixWord ++ tailWord_966353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966477 : List Nat := [1, 6, 1, 2, 1, 2, 2, 6]
def baseStart_966477 : Nat := 118140960795 + 966477 * 2 ^ 59
def prefixEnd_966477 : Nat := 4983230072969 + 3 ^ 40 * 966477 * 2
def baseEnd_966477 : Nat := 73521072965262279702631

theorem tailTrace_966477 : CollatzResearch.WordTrace tailWord_966477 prefixEnd_966477 73521072965262279702631 := by
  unfold tailWord_966477
  simp only [CollatzResearch.WordTrace]
  refine ⟨35250312119626364975521685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23500208079750909983681123 35250312119626364975521685)
  ·
    refine ⟨1652358380607485858227579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 35250312119626364975521685 1652358380607485858227579)
    ·
      refine ⟨2478537570911228787341369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1652358380607485858227579 2478537570911228787341369)
      ·
        refine ⟨1858903178183421590506027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2478537570911228787341369 1858903178183421590506027)
        ·
          refine ⟨2788354767275132385759041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1858903178183421590506027 2788354767275132385759041)
          ·
            refine ⟨2091266075456349289319281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2788354767275132385759041 2091266075456349289319281)
            ·
              refine ⟨1568449556592261966989461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2091266075456349289319281 1568449556592261966989461)
              ·
                refine ⟨73521072965262279702631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1568449556592261966989461 73521072965262279702631)
                ·
                  rfl

theorem cell21_966477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 2, 6].length) (baseStart_966477 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_966477 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_966477 prefixEnd_966477 := by exact prefixLift 966477
  have htrace : WordTrace (prefixWord ++ tailWord_966477) baseStart_966477 baseEnd_966477 := by
    simpa [prefixWord, tailWord_966477, baseEnd_966477] using wordTrace_append hprefix tailTrace_966477
  have hstable : (prefixWord ++ tailWord_966477).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966477).length < 2 ^ (prefixWord ++ tailWord_966477).sum := by decide
  have hdescent : baseEnd_966477 < baseStart_966477 := by decide
  rcases family_descends (prefixWord ++ tailWord_966477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966581 : List Nat := [1, 3, 3, 2, 1, 3, 1, 1, 6]
def baseStart_966581 : Nat := 118140960795 + 966581 * 2 ^ 59
def prefixEnd_966581 : Nat := 4983230072969 + 3 ^ 40 * 966581 * 2
def baseEnd_966581 : Nat := 220586953112705769374347

theorem tailTrace_966581 : CollatzResearch.WordTrace tailWord_966581 prefixEnd_966581 220586953112705769374347 := by
  unfold tailWord_966581
  simp only [CollatzResearch.WordTrace]
  refine ⟨35254105311249590737307597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23502736874166393824871731 35254105311249590737307597)
  ·
    refine ⟨13220289491718596526490349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35254105311249590737307597 13220289491718596526490349)
    ·
      refine ⟨4957608559394473697433881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13220289491718596526490349 4957608559394473697433881)
      ·
        refine ⟨3718206419545855273075411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4957608559394473697433881 3718206419545855273075411)
        ·
          refine ⟨5577309629318782909613117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3718206419545855273075411 5577309629318782909613117)
          ·
            refine ⟨2091491110994543591104919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5577309629318782909613117 2091491110994543591104919)
            ·
              refine ⟨3137236666491815386657379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2091491110994543591104919 3137236666491815386657379)
              ·
                refine ⟨4705854999737723079986069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3137236666491815386657379 4705854999737723079986069)
                ·
                  refine ⟨220586953112705769374347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4705854999737723079986069 220586953112705769374347)
                  ·
                    rfl

theorem cell21_966581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 1, 6].length) (baseStart_966581 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_966581 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_966581 prefixEnd_966581 := by exact prefixLift 966581
  have htrace : WordTrace (prefixWord ++ tailWord_966581) baseStart_966581 baseEnd_966581 := by
    simpa [prefixWord, tailWord_966581, baseEnd_966581] using wordTrace_append hprefix tailTrace_966581
  have hstable : (prefixWord ++ tailWord_966581).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966581).length < 2 ^ (prefixWord ++ tailWord_966581).sum := by decide
  have hdescent : baseEnd_966581 < baseStart_966581 := by decide
  rcases family_descends (prefixWord ++ tailWord_966581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966609 : List Nat := [1, 2, 2, 1, 2, 1, 2, 3, 7]
def baseStart_966609 : Nat := 118140960795 + 966609 * 2 ^ 59
def prefixEnd_966609 : Nat := 4983230072969 + 3 ^ 40 * 966609 * 2
def baseEnd_966609 : Nat := 220593343094183942907623

theorem tailTrace_966609 : CollatzResearch.WordTrace tailWord_966609 prefixEnd_966609 220593343094183942907623 := by
  unfold tailWord_966609
  simp only [CollatzResearch.WordTrace]
  refine ⟨35255126555148151519326881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23503417703432101012884587 35255126555148151519326881)
  ·
    refine ⟨26441344916361113639495161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35255126555148151519326881 26441344916361113639495161)
    ·
      refine ⟨19831008687270835229621371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26441344916361113639495161 19831008687270835229621371)
      ·
        refine ⟨29746513030906252844432057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19831008687270835229621371 29746513030906252844432057)
        ·
          refine ⟨22309884773179689633324043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29746513030906252844432057 22309884773179689633324043)
          ·
            refine ⟨33464827159769534449986065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22309884773179689633324043 33464827159769534449986065)
            ·
              refine ⟨25098620369827150837489549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33464827159769534449986065 25098620369827150837489549)
              ·
                refine ⟨9411982638685181564058581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25098620369827150837489549 9411982638685181564058581)
                ·
                  refine ⟨220593343094183942907623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9411982638685181564058581 220593343094183942907623)
                  ·
                    rfl

theorem cell21_966609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 3, 7].length) (baseStart_966609 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_966609 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_966609 prefixEnd_966609 := by exact prefixLift 966609
  have htrace : WordTrace (prefixWord ++ tailWord_966609) baseStart_966609 baseEnd_966609 := by
    simpa [prefixWord, tailWord_966609, baseEnd_966609] using wordTrace_append hprefix tailTrace_966609
  have hstable : (prefixWord ++ tailWord_966609).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966609).length < 2 ^ (prefixWord ++ tailWord_966609).sum := by decide
  have hdescent : baseEnd_966609 < baseStart_966609 := by decide
  rcases family_descends (prefixWord ++ tailWord_966609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966640 : List Nat := [2, 1, 1, 1, 3, 2, 4, 1, 6]
def baseStart_966640 : Nat := 118140960795 + 966640 * 2 ^ 59
def prefixEnd_966640 : Nat := 4983230072969 + 3 ^ 40 * 966640 * 2
def baseEnd_966640 : Nat := 220600417716534777890893

theorem tailTrace_966640 : CollatzResearch.WordTrace tailWord_966640 prefixEnd_966640 220600417716534777890893 := by
  unfold tailWord_966640
  simp only [CollatzResearch.WordTrace]
  refine ⟨17628128609017921906852687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23504171478690562542470249 17628128609017921906852687)
  ·
    refine ⟨26442192913526882860279031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17628128609017921906852687 26442192913526882860279031)
    ·
      refine ⟨39663289370290324290418547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26442192913526882860279031 39663289370290324290418547)
      ·
        refine ⟨59494934055435486435627821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39663289370290324290418547 59494934055435486435627821)
        ·
          refine ⟨22310600270788307413360433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59494934055435486435627821 22310600270788307413360433)
          ·
            refine ⟨16732950203091230560020325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22310600270788307413360433 16732950203091230560020325)
            ·
              refine ⟨3137428163079605730003811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16732950203091230560020325 3137428163079605730003811)
              ·
                refine ⟨4706142244619408595005717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3137428163079605730003811 4706142244619408595005717)
                ·
                  refine ⟨220600417716534777890893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4706142244619408595005717 220600417716534777890893)
                  ·
                    rfl

theorem cell21_966640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 1, 6].length) (baseStart_966640 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_966640 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_966640 prefixEnd_966640 := by exact prefixLift 966640
  have htrace : WordTrace (prefixWord ++ tailWord_966640) baseStart_966640 baseEnd_966640 := by
    simpa [prefixWord, tailWord_966640, baseEnd_966640] using wordTrace_append hprefix tailTrace_966640
  have hstable : (prefixWord ++ tailWord_966640).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966640).length < 2 ^ (prefixWord ++ tailWord_966640).sum := by decide
  have hdescent : baseEnd_966640 < baseStart_966640 := by decide
  rcases family_descends (prefixWord ++ tailWord_966640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966657 : List Nat := [1, 2, 4, 1, 2, 1, 3, 3, 4]
def baseStart_966657 : Nat := 118140960795 + 966657 * 2 ^ 59
def prefixEnd_966657 : Nat := 4983230072969 + 3 ^ 40 * 966657 * 2
def baseEnd_966657 : Nat := 220604297348146526107525

theorem tailTrace_966657 : CollatzResearch.WordTrace tailWord_966657 prefixEnd_966657 220604297348146526107525 := by
  unfold tailWord_966657
  simp only [CollatzResearch.WordTrace]
  refine ⟨35256877258974255717074225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23504584839316170478049483 35256877258974255717074225)
  ·
    refine ⟨26442657944230691787805669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35256877258974255717074225 26442657944230691787805669)
    ·
      refine ⟨4957998364543254710213563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26442657944230691787805669 4957998364543254710213563)
      ·
        refine ⟨7436997546814882065320345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4957998364543254710213563 7436997546814882065320345)
        ·
          refine ⟨5577748160111161548990259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7436997546814882065320345 5577748160111161548990259)
          ·
            refine ⟨8366622240166742323485389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5577748160111161548990259 8366622240166742323485389)
            ·
              refine ⟨3137483340062528371307021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8366622240166742323485389 3137483340062528371307021)
              ·
                refine ⟨1176556252523448139240133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3137483340062528371307021 1176556252523448139240133)
                ·
                  refine ⟨220604297348146526107525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1176556252523448139240133 220604297348146526107525)
                  ·
                    rfl

theorem cell21_966657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 3, 4].length) (baseStart_966657 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_966657 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_966657 prefixEnd_966657 := by exact prefixLift 966657
  have htrace : WordTrace (prefixWord ++ tailWord_966657) baseStart_966657 baseEnd_966657 := by
    simpa [prefixWord, tailWord_966657, baseEnd_966657] using wordTrace_append hprefix tailTrace_966657
  have hstable : (prefixWord ++ tailWord_966657).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966657).length < 2 ^ (prefixWord ++ tailWord_966657).sum := by decide
  have hdescent : baseEnd_966657 < baseStart_966657 := by decide
  rcases family_descends (prefixWord ++ tailWord_966657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966733 : List Nat := [1, 6, 1, 1, 1, 1, 2, 2, 6]
def baseStart_966733 : Nat := 118140960795 + 966733 * 2 ^ 59
def prefixEnd_966733 : Nat := 4983230072969 + 3 ^ 40 * 966733 * 2
def baseEnd_966733 : Nat := 220621641583587282840703

theorem tailTrace_966733 : CollatzResearch.WordTrace tailWord_966733 prefixEnd_966733 220621641583587282840703 := by
  unfold tailWord_966733
  simp only [CollatzResearch.WordTrace]
  refine ⟨35259649206698920696840853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23506432804465947131227235 35259649206698920696840853)
  ·
    refine ⟨1652796056564011907664415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 35259649206698920696840853 1652796056564011907664415)
    ·
      refine ⟨2479194084846017861496623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1652796056564011907664415 2479194084846017861496623)
      ·
        refine ⟨3718791127269026792244935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2479194084846017861496623 3718791127269026792244935)
        ·
          refine ⟨5578186690903540188367403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3718791127269026792244935 5578186690903540188367403)
          ·
            refine ⟨8367280036355310282551105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5578186690903540188367403 8367280036355310282551105)
            ·
              refine ⟨6275460027266482711913329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8367280036355310282551105 6275460027266482711913329)
              ·
                refine ⟨4706595020449862033934997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6275460027266482711913329 4706595020449862033934997)
                ·
                  refine ⟨220621641583587282840703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4706595020449862033934997 220621641583587282840703)
                  ·
                    rfl

theorem cell21_966733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_966733 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_966733 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_966733 prefixEnd_966733 := by exact prefixLift 966733
  have htrace : WordTrace (prefixWord ++ tailWord_966733) baseStart_966733 baseEnd_966733 := by
    simpa [prefixWord, tailWord_966733, baseEnd_966733] using wordTrace_append hprefix tailTrace_966733
  have hstable : (prefixWord ++ tailWord_966733).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966733).length < 2 ^ (prefixWord ++ tailWord_966733).sum := by decide
  have hdescent : baseEnd_966733 < baseStart_966733 := by decide
  rcases family_descends (prefixWord ++ tailWord_966733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966812 : List Nat := [2, 2, 3, 2, 1, 1, 5, 2, 3]
def baseStart_966812 : Nat := 118140960795 + 966812 * 2 ^ 59
def prefixEnd_966812 : Nat := 4983230072969 + 3 ^ 40 * 966812 * 2
def baseEnd_966812 : Nat := 220639670459900701023875

theorem tailTrace_966812 : CollatzResearch.WordTrace tailWord_966812 prefixEnd_966812 220639670459900701023875 := by
  unfold tailWord_966812
  simp only [CollatzResearch.WordTrace]
  refine ⟨17631265286706358594483345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23508353715608478125977793 17631265286706358594483345)
  ·
    refine ⟨13223448965029768945862509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17631265286706358594483345 13223448965029768945862509)
    ·
      refine ⟨4958793361886163354698441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13223448965029768945862509 4958793361886163354698441)
      ·
        refine ⟨3719095021414622516023831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4958793361886163354698441 3719095021414622516023831)
        ·
          refine ⟨5578642532121933774035747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3719095021414622516023831 5578642532121933774035747)
          ·
            refine ⟨8367963798182900661053621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5578642532121933774035747 8367963798182900661053621)
            ·
              refine ⟨784496606079646936973777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8367963798182900661053621 784496606079646936973777)
              ·
                refine ⟨588372454559735202730333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 784496606079646936973777 588372454559735202730333)
                ·
                  refine ⟨220639670459900701023875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 588372454559735202730333 220639670459900701023875)
                  ·
                    rfl

theorem cell21_966812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 5, 2, 3].length) (baseStart_966812 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_966812 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_966812 prefixEnd_966812 := by exact prefixLift 966812
  have htrace : WordTrace (prefixWord ++ tailWord_966812) baseStart_966812 baseEnd_966812 := by
    simpa [prefixWord, tailWord_966812, baseEnd_966812] using wordTrace_append hprefix tailTrace_966812
  have hstable : (prefixWord ++ tailWord_966812).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966812).length < 2 ^ (prefixWord ++ tailWord_966812).sum := by decide
  have hdescent : baseEnd_966812 < baseStart_966812 := by decide
  rcases family_descends (prefixWord ++ tailWord_966812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966885 : List Nat := [1, 3, 1, 4, 2, 1, 2, 3, 4]
def baseStart_966885 : Nat := 118140960795 + 966885 * 2 ^ 59
def prefixEnd_966885 : Nat := 4983230072969 + 3 ^ 40 * 966885 * 2
def baseEnd_966885 : Nat := 220656330054468796307059

theorem tailTrace_966885 : CollatzResearch.WordTrace tailWord_966885 prefixEnd_966885 220656330054468796307059 := by
  unfold tailWord_966885
  simp only [CollatzResearch.WordTrace]
  refine ⟨35265193102148250656374109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23510128734765500437582739 35265193102148250656374109)
  ·
    refine ⟨13224447413305593996140291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35265193102148250656374109 13224447413305593996140291)
    ·
      refine ⟨19836671119958390994210437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13224447413305593996140291 19836671119958390994210437)
      ·
        refine ⟨3719375834992198311414457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19836671119958390994210437 3719375834992198311414457)
        ·
          refine ⟨2789531876244148733560843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3719375834992198311414457 2789531876244148733560843)
          ·
            refine ⟨4184297814366223100341265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2789531876244148733560843 4184297814366223100341265)
            ·
              refine ⟨3138223360774667325255949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4184297814366223100341265 3138223360774667325255949)
              ·
                refine ⟨1176833760290500246970981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3138223360774667325255949 1176833760290500246970981)
                ·
                  refine ⟨220656330054468796307059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1176833760290500246970981 220656330054468796307059)
                  ·
                    rfl

theorem cell21_966885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 3, 4].length) (baseStart_966885 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_966885 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_966885 prefixEnd_966885 := by exact prefixLift 966885
  have htrace : WordTrace (prefixWord ++ tailWord_966885) baseStart_966885 baseEnd_966885 := by
    simpa [prefixWord, tailWord_966885, baseEnd_966885] using wordTrace_append hprefix tailTrace_966885
  have hstable : (prefixWord ++ tailWord_966885).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966885).length < 2 ^ (prefixWord ++ tailWord_966885).sum := by decide
  have hdescent : baseEnd_966885 < baseStart_966885 := by decide
  rcases family_descends (prefixWord ++ tailWord_966885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966899 : List Nat := [1, 1, 1, 2, 2, 4, 5, 5]
def baseStart_966899 : Nat := 118140960795 + 966899 * 2 ^ 59
def prefixEnd_966899 : Nat := 4983230072969 + 3 ^ 40 * 966899 * 2
def baseEnd_966899 : Nat := 73553175015069294357899

theorem tailTrace_966899 : CollatzResearch.WordTrace tailWord_966899 prefixEnd_966899 73553175015069294357899 := by
  unfold tailWord_966899
  simp only [CollatzResearch.WordTrace]
  refine ⟨35265703724097531047383751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23510469149398354031589167 35265703724097531047383751)
  ·
    refine ⟨52898555586146296571075627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35265703724097531047383751 52898555586146296571075627)
    ·
      refine ⟨79347833379219444856613441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52898555586146296571075627 79347833379219444856613441)
      ·
        refine ⟨59510875034414583642460081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79347833379219444856613441 59510875034414583642460081)
        ·
          refine ⟨44633156275810937731845061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59510875034414583642460081 44633156275810937731845061)
          ·
            refine ⟨8368716801714550824720949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44633156275810937731845061 8368716801714550824720949)
            ·
              refine ⟨784567200160739139817589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8368716801714550824720949 784567200160739139817589)
              ·
                refine ⟨73553175015069294357899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 784567200160739139817589 73553175015069294357899)
                ·
                  rfl

theorem cell21_966899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 5, 5].length) (baseStart_966899 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_966899 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_966899 prefixEnd_966899 := by exact prefixLift 966899
  have htrace : WordTrace (prefixWord ++ tailWord_966899) baseStart_966899 baseEnd_966899 := by
    simpa [prefixWord, tailWord_966899, baseEnd_966899] using wordTrace_append hprefix tailTrace_966899
  have hstable : (prefixWord ++ tailWord_966899).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966899).length < 2 ^ (prefixWord ++ tailWord_966899).sum := by decide
  have hdescent : baseEnd_966899 < baseStart_966899 := by decide
  rcases family_descends (prefixWord ++ tailWord_966899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966913 : List Nat := [1, 2, 4, 1, 1, 2, 1, 2, 7]
def baseStart_966913 : Nat := 118140960795 + 966913 * 2 ^ 59
def prefixEnd_966913 : Nat := 4983230072969 + 3 ^ 40 * 966913 * 2
def baseEnd_966913 : Nat := 220662720035946969840335

theorem tailTrace_966913 : CollatzResearch.WordTrace tailWord_966913 prefixEnd_966913 220662720035946969840335 := by
  unfold tailWord_966913
  simp only [CollatzResearch.WordTrace]
  refine ⟨35266214346046811438393393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23510809564031207625595595 35266214346046811438393393)
  ·
    refine ⟨26449660759535108578795045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35266214346046811438393393 26449660759535108578795045)
    ·
      refine ⟨4959311392412832858524071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26449660759535108578795045 4959311392412832858524071)
      ·
        refine ⟨7438967088619249287786107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4959311392412832858524071 7438967088619249287786107)
        ·
          refine ⟨11158450632928873931679161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7438967088619249287786107 11158450632928873931679161)
          ·
            refine ⟨8368837974696655448759371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11158450632928873931679161 8368837974696655448759371)
            ·
              refine ⟨12553256962044983173139057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8368837974696655448759371 12553256962044983173139057)
              ·
                refine ⟨9414942721533737379854293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12553256962044983173139057 9414942721533737379854293)
                ·
                  refine ⟨220662720035946969840335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9414942721533737379854293 220662720035946969840335)
                  ·
                    rfl

theorem cell21_966913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 2, 7].length) (baseStart_966913 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_966913 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_966913 prefixEnd_966913 := by exact prefixLift 966913
  have htrace : WordTrace (prefixWord ++ tailWord_966913) baseStart_966913 baseEnd_966913 := by
    simpa [prefixWord, tailWord_966913, baseEnd_966913] using wordTrace_append hprefix tailTrace_966913
  have hstable : (prefixWord ++ tailWord_966913).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966913).length < 2 ^ (prefixWord ++ tailWord_966913).sum := by decide
  have hdescent : baseEnd_966913 < baseStart_966913 := by decide
  rcases family_descends (prefixWord ++ tailWord_966913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966919 : List Nat := [1, 1, 4, 5, 1, 2, 1, 2, 4]
def baseStart_966919 : Nat := 118140960795 + 966919 * 2 ^ 59
def prefixEnd_966919 : Nat := 4983230072969 + 3 ^ 40 * 966919 * 2
def baseEnd_966919 : Nat := 220664089317692292740323

theorem tailTrace_966919 : CollatzResearch.WordTrace tailWord_966919 prefixEnd_966919 220664089317692292740323 := by
  unfold tailWord_966919
  simp only [CollatzResearch.WordTrace]
  refine ⟨35266433184025074463111811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23510955456016716308741207 35266433184025074463111811)
  ·
    refine ⟨52899649776037611694667717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35266433184025074463111811 52899649776037611694667717)
    ·
      refine ⟨9918684333007052192750197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52899649776037611694667717 9918684333007052192750197)
      ·
        refine ⟨929876656219411143070331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9918684333007052192750197 929876656219411143070331)
        ·
          refine ⟨1394814984329116714605497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 929876656219411143070331 1394814984329116714605497)
          ·
            refine ⟨1046111238246837535954123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1394814984329116714605497 1046111238246837535954123)
            ·
              refine ⟨1569166857370256303931185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1046111238246837535954123 1569166857370256303931185)
              ·
                refine ⟨1176875143027692227948389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1569166857370256303931185 1176875143027692227948389)
                ·
                  refine ⟨220664089317692292740323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1176875143027692227948389 220664089317692292740323)
                  ·
                    rfl

theorem cell21_966919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 1, 2, 4].length) (baseStart_966919 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_966919 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_966919 prefixEnd_966919 := by exact prefixLift 966919
  have htrace : WordTrace (prefixWord ++ tailWord_966919) baseStart_966919 baseEnd_966919 := by
    simpa [prefixWord, tailWord_966919, baseEnd_966919] using wordTrace_append hprefix tailTrace_966919
  have hstable : (prefixWord ++ tailWord_966919).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966919).length < 2 ^ (prefixWord ++ tailWord_966919).sum := by decide
  have hdescent : baseEnd_966919 < baseStart_966919 := by decide
  rcases family_descends (prefixWord ++ tailWord_966919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966964 : List Nat := [2, 5, 1, 1, 1, 2, 3, 3, 3]
def baseStart_966964 : Nat := 118140960795 + 966964 * 2 ^ 59
def prefixEnd_966964 : Nat := 4983230072969 + 3 ^ 40 * 966964 * 2
def baseEnd_966964 : Nat := 220674358930782214490231

theorem tailTrace_966964 : CollatzResearch.WordTrace tailWord_966964 prefixEnd_966964 220674358930782214490231 := by
  unfold tailWord_966964
  simp only [CollatzResearch.WordTrace]
  refine ⟨17634037234431023574249973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23512049645908031432333297 17634037234431023574249973)
  ·
    refine ⟨1653190990727908460085935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17634037234431023574249973 1653190990727908460085935)
    ·
      refine ⟨2479786486091862690128903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1653190990727908460085935 2479786486091862690128903)
      ·
        refine ⟨3719679729137794035193355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2479786486091862690128903 3719679729137794035193355)
        ·
          refine ⟨5579519593706691052790033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3719679729137794035193355 5579519593706691052790033)
          ·
            refine ⟨4184639695280018289592525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5579519593706691052790033 4184639695280018289592525)
            ·
              refine ⟨1569239885730006858597197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4184639695280018289592525 1569239885730006858597197)
              ·
                refine ⟨588464957148752571973949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1569239885730006858597197 588464957148752571973949)
                ·
                  refine ⟨220674358930782214490231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 588464957148752571973949 220674358930782214490231)
                  ·
                    rfl

theorem cell21_966964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 3, 3, 3].length) (baseStart_966964 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_966964 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_966964 prefixEnd_966964 := by exact prefixLift 966964
  have htrace : WordTrace (prefixWord ++ tailWord_966964) baseStart_966964 baseEnd_966964 := by
    simpa [prefixWord, tailWord_966964, baseEnd_966964] using wordTrace_append hprefix tailTrace_966964
  have hstable : (prefixWord ++ tailWord_966964).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966964).length < 2 ^ (prefixWord ++ tailWord_966964).sum := by decide
  have hdescent : baseEnd_966964 < baseStart_966964 := by decide
  rcases family_descends (prefixWord ++ tailWord_966964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967037 : List Nat := [1, 4, 1, 1, 2, 4, 2, 2, 4]
def baseStart_967037 : Nat := 118140960795 + 967037 * 2 ^ 59
def prefixEnd_967037 : Nat := 4983230072969 + 3 ^ 40 * 967037 * 2
def baseEnd_967037 : Nat := 220691018525350309773415

theorem tailTrace_967037 : CollatzResearch.WordTrace tailWord_967037 prefixEnd_967037 220691018525350309773415 := by
  unfold tailWord_967037
  simp only [CollatzResearch.WordTrace]
  refine ⟨35270736997597580615907365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23513824665065053743938243 35270736997597580615907365)
  ·
    refine ⟨6613263187049546365482631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35270736997597580615907365 6613263187049546365482631)
    ·
      refine ⟨9919894780574319548223947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6613263187049546365482631 9919894780574319548223947)
      ·
        refine ⟨14879842170861479322335921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9919894780574319548223947 14879842170861479322335921)
        ·
          refine ⟨11159881628146109491751941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14879842170861479322335921 11159881628146109491751941)
          ·
            refine ⟨2092477805277395529703489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11159881628146109491751941 2092477805277395529703489)
            ·
              refine ⟨1569358353958046647277617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2092477805277395529703489 1569358353958046647277617)
              ·
                refine ⟨1177018765468534985458213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1569358353958046647277617 1177018765468534985458213)
                ·
                  refine ⟨220691018525350309773415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1177018765468534985458213 220691018525350309773415)
                  ·
                    rfl

theorem cell21_967037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 2, 2, 4].length) (baseStart_967037 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_967037 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_967037 prefixEnd_967037 := by exact prefixLift 967037
  have htrace : WordTrace (prefixWord ++ tailWord_967037) baseStart_967037 baseEnd_967037 := by
    simpa [prefixWord, tailWord_967037, baseEnd_967037] using wordTrace_append hprefix tailTrace_967037
  have hstable : (prefixWord ++ tailWord_967037).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967037).length < 2 ^ (prefixWord ++ tailWord_967037).sum := by decide
  have hdescent : baseEnd_967037 < baseStart_967037 := by decide
  rcases family_descends (prefixWord ++ tailWord_967037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967051 : List Nat := [1, 1, 1, 1, 4, 6, 1, 6]
def baseStart_967051 : Nat := 118140960795 + 967051 * 2 ^ 59
def prefixEnd_967051 : Nat := 4983230072969 + 3 ^ 40 * 967051 * 2
def baseEnd_967051 : Nat := 73564737838696465513351

theorem tailTrace_967051 : CollatzResearch.WordTrace tailWord_967051 prefixEnd_967051 73564737838696465513351 := by
  unfold tailWord_967051
  simp only [CollatzResearch.WordTrace]
  refine ⟨35271247619546861006917007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23514165079697907337944671 35271247619546861006917007)
  ·
    refine ⟨52906871429320291510375511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35271247619546861006917007 52906871429320291510375511)
    ·
      refine ⟨79360307143980437265563267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52906871429320291510375511 79360307143980437265563267)
      ·
        refine ⟨119040460715970655898344901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79360307143980437265563267 119040460715970655898344901)
        ·
          refine ⟨22320086384244497980939669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 119040460715970655898344901 22320086384244497980939669)
          ·
            refine ⟨1046254049261460842856547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 22320086384244497980939669 1046254049261460842856547)
            ·
              refine ⟨1569381073892191264284821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1046254049261460842856547 1569381073892191264284821)
              ·
                refine ⟨73564737838696465513351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1569381073892191264284821 73564737838696465513351)
                ·
                  rfl

theorem cell21_967051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 1, 6].length) (baseStart_967051 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_967051 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_967051 prefixEnd_967051 := by exact prefixLift 967051
  have htrace : WordTrace (prefixWord ++ tailWord_967051) baseStart_967051 baseEnd_967051 := by
    simpa [prefixWord, tailWord_967051, baseEnd_967051] using wordTrace_append hprefix tailTrace_967051
  have hstable : (prefixWord ++ tailWord_967051).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967051).length < 2 ^ (prefixWord ++ tailWord_967051).sum := by decide
  have hdescent : baseEnd_967051 < baseStart_967051 := by decide
  rcases family_descends (prefixWord ++ tailWord_967051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967065 : List Nat := [1, 2, 1, 2, 1, 4, 3, 2, 5]
def baseStart_967065 : Nat := 118140960795 + 967065 * 2 ^ 59
def prefixEnd_967065 : Nat := 4983230072969 + 3 ^ 40 * 967065 * 2
def baseEnd_967065 : Nat := 220697408506828483306691

theorem tailTrace_967065 : CollatzResearch.WordTrace tailWord_967065 prefixEnd_967065 220697408506828483306691 := by
  unfold tailWord_967065
  simp only [CollatzResearch.WordTrace]
  refine ⟨35271758241496141397926649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23514505494330760931951099 35271758241496141397926649)
  ·
    refine ⟨26453818681122106048444987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35271758241496141397926649 26453818681122106048444987)
    ·
      refine ⟨39680728021683159072667481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26453818681122106048444987 39680728021683159072667481)
      ·
        refine ⟨29760546016262369304500611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39680728021683159072667481 29760546016262369304500611)
        ·
          refine ⟨44640819024393553956750917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29760546016262369304500611 44640819024393553956750917)
          ·
            refine ⟨8370153567073791366890797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44640819024393553956750917 8370153567073791366890797)
            ·
              refine ⟨3138807587652671762584049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8370153567073791366890797 3138807587652671762584049)
              ·
                refine ⟨2354105690739503821938037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3138807587652671762584049 2354105690739503821938037)
                ·
                  refine ⟨220697408506828483306691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2354105690739503821938037 220697408506828483306691)
                  ·
                    rfl

theorem cell21_967065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 2, 5].length) (baseStart_967065 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_967065 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_967065 prefixEnd_967065 := by exact prefixLift 967065
  have htrace : WordTrace (prefixWord ++ tailWord_967065) baseStart_967065 baseEnd_967065 := by
    simpa [prefixWord, tailWord_967065, baseEnd_967065] using wordTrace_append hprefix tailTrace_967065
  have hstable : (prefixWord ++ tailWord_967065).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967065).length < 2 ^ (prefixWord ++ tailWord_967065).sum := by decide
  have hdescent : baseEnd_967065 < baseStart_967065 := by decide
  rcases family_descends (prefixWord ++ tailWord_967065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967155 : List Nat := [1, 1, 1, 2, 2, 2, 3, 3, 6]
def baseStart_967155 : Nat := 118140960795 + 967155 * 2 ^ 59
def prefixEnd_967155 : Nat := 4983230072969 + 3 ^ 40 * 967155 * 2
def baseEnd_967155 : Nat := 220717947733008326806507

theorem tailTrace_967155 : CollatzResearch.WordTrace tailWord_967155 prefixEnd_967155 220717947733008326806507 := by
  unfold tailWord_967155
  simp only [CollatzResearch.WordTrace]
  refine ⟨35275040811170086768702919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23516693874113391179135279 35275040811170086768702919)
  ·
    refine ⟨52912561216755130153054379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35275040811170086768702919 52912561216755130153054379)
    ·
      refine ⟨79368841825132695229581569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52912561216755130153054379 79368841825132695229581569)
      ·
        refine ⟨59526631368849521422186177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79368841825132695229581569 59526631368849521422186177)
        ·
          refine ⟨44644973526637141066639633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59526631368849521422186177 44644973526637141066639633)
          ·
            refine ⟨33483730144977855799979725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44644973526637141066639633 33483730144977855799979725)
            ·
              refine ⟨12556398804366695924992397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33483730144977855799979725 12556398804366695924992397)
              ·
                refine ⟨4708649551637510971872149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12556398804366695924992397 4708649551637510971872149)
                ·
                  refine ⟨220717947733008326806507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4708649551637510971872149 220717947733008326806507)
                  ·
                    rfl

theorem cell21_967155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 6].length) (baseStart_967155 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_967155 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_967155 prefixEnd_967155 := by exact prefixLift 967155
  have htrace : WordTrace (prefixWord ++ tailWord_967155) baseStart_967155 baseEnd_967155 := by
    simpa [prefixWord, tailWord_967155, baseEnd_967155] using wordTrace_append hprefix tailTrace_967155
  have hstable : (prefixWord ++ tailWord_967155).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967155).length < 2 ^ (prefixWord ++ tailWord_967155).sum := by decide
  have hdescent : baseEnd_967155 < baseStart_967155 := by decide
  rcases family_descends (prefixWord ++ tailWord_967155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967265 : List Nat := [1, 2, 3, 1, 1, 6, 1, 2, 4]
def baseStart_967265 : Nat := 118140960795 + 967265 * 2 ^ 59
def prefixEnd_967265 : Nat := 4983230072969 + 3 ^ 40 * 967265 * 2
def baseEnd_967265 : Nat := 220743051231672579972949

theorem tailTrace_967265 : CollatzResearch.WordTrace tailWord_967265 prefixEnd_967265 220743051231672579972949 := by
  unfold tailWord_967265
  simp only [CollatzResearch.WordTrace]
  refine ⟨35279052840771575555207249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23519368560514383703471499 35279052840771575555207249)
  ·
    refine ⟨26459289630578681666405437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35279052840771575555207249 26459289630578681666405437)
    ·
      refine ⟨9922233611467005624902039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26459289630578681666405437 9922233611467005624902039)
      ·
        refine ⟨14883350417200508437353059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9922233611467005624902039 14883350417200508437353059)
        ·
          refine ⟨22325025625800762656029589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14883350417200508437353059 22325025625800762656029589)
          ·
            refine ⟨1046485576209410749501387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 22325025625800762656029589 1046485576209410749501387)
            ·
              refine ⟨1569728364314116124252081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1046485576209410749501387 1569728364314116124252081)
              ·
                refine ⟨1177296273235587093189061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1569728364314116124252081 1177296273235587093189061)
                ·
                  refine ⟨220743051231672579972949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1177296273235587093189061 220743051231672579972949)
                  ·
                    rfl

theorem cell21_967265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 1, 2, 4].length) (baseStart_967265 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_967265 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_967265 prefixEnd_967265 := by exact prefixLift 967265
  have htrace : WordTrace (prefixWord ++ tailWord_967265) baseStart_967265 baseEnd_967265 := by
    simpa [prefixWord, tailWord_967265, baseEnd_967265] using wordTrace_append hprefix tailTrace_967265
  have hstable : (prefixWord ++ tailWord_967265).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967265).length < 2 ^ (prefixWord ++ tailWord_967265).sum := by decide
  have hdescent : baseEnd_967265 < baseStart_967265 := by decide
  rcases family_descends (prefixWord ++ tailWord_967265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967282 : List Nat := [3, 2, 1, 2, 4, 1, 3, 1, 4]
def baseStart_967282 : Nat := 118140960795 + 967282 * 2 ^ 59
def prefixEnd_967282 : Nat := 4983230072969 + 3 ^ 40 * 967282 * 2
def baseEnd_967282 : Nat := 220746930863284328189581

theorem tailTrace_967282 : CollatzResearch.WordTrace tailWord_967282 prefixEnd_967282 220746930863284328189581 := by
  unfold tailWord_967282
  simp only [CollatzResearch.WordTrace]
  refine ⟨8819918220427496864644025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23519781921139991639050733 8819918220427496864644025)
  ·
    refine ⟨6614938665320622648483019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8819918220427496864644025 6614938665320622648483019)
    ·
      refine ⟨9922407997980933972724529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6614938665320622648483019 9922407997980933972724529)
      ·
        refine ⟨7441805998485700479543397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9922407997980933972724529 7441805998485700479543397)
        ·
          refine ⟨1395338624716068839914387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7441805998485700479543397 1395338624716068839914387)
          ·
            refine ⟨2093007937074103259871581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1395338624716068839914387 2093007937074103259871581)
            ·
              refine ⟨784877976402788722451843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2093007937074103259871581 784877976402788722451843)
              ·
                refine ⟨1177316964604183083677765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 784877976402788722451843 1177316964604183083677765)
                ·
                  refine ⟨220746930863284328189581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1177316964604183083677765 220746930863284328189581)
                  ·
                    rfl

theorem cell21_967282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 3, 1, 4].length) (baseStart_967282 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_967282 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_967282 prefixEnd_967282 := by exact prefixLift 967282
  have htrace : WordTrace (prefixWord ++ tailWord_967282) baseStart_967282 baseEnd_967282 := by
    simpa [prefixWord, tailWord_967282, baseEnd_967282] using wordTrace_append hprefix tailTrace_967282
  have hstable : (prefixWord ++ tailWord_967282).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967282).length < 2 ^ (prefixWord ++ tailWord_967282).sum := by decide
  have hdescent : baseEnd_967282 < baseStart_967282 := by decide
  rcases family_descends (prefixWord ++ tailWord_967282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967324 : List Nat := [2, 2, 3, 2, 2, 1, 2, 1, 6]
def baseStart_967324 : Nat := 118140960795 + 967324 * 2 ^ 59
def prefixEnd_967324 : Nat := 4983230072969 + 3 ^ 40 * 967324 * 2
def baseEnd_967324 : Nat := 220756515835501588489495

theorem tailTrace_967324 : CollatzResearch.WordTrace tailWord_967324 prefixEnd_967324 220756515835501588489495 := by
  unfold tailWord_967324
  simp only [CollatzResearch.WordTrace]
  refine ⟨17640602373778914315802513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23520803165038552421070017 17640602373778914315802513)
  ·
    refine ⟨13230451780334185736851885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17640602373778914315802513 13230451780334185736851885)
    ·
      refine ⟨4961419417625319651319457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13230451780334185736851885 4961419417625319651319457)
      ·
        refine ⟨3721064563218989738489593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4961419417625319651319457 3721064563218989738489593)
        ·
          refine ⟨2790798422414242303867195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3721064563218989738489593 2790798422414242303867195)
          ·
            refine ⟨4186197633621363455800793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2790798422414242303867195 4186197633621363455800793)
            ·
              refine ⟨3139648225216022591850595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4186197633621363455800793 3139648225216022591850595)
              ·
                refine ⟨4709472337824033887775893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3139648225216022591850595 4709472337824033887775893)
                ·
                  refine ⟨220756515835501588489495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4709472337824033887775893 220756515835501588489495)
                  ·
                    rfl

theorem cell21_967324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 1, 6].length) (baseStart_967324 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_967324 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_967324 prefixEnd_967324 := by exact prefixLift 967324
  have htrace : WordTrace (prefixWord ++ tailWord_967324) baseStart_967324 baseEnd_967324 := by
    simpa [prefixWord, tailWord_967324, baseEnd_967324] using wordTrace_append hprefix tailTrace_967324
  have hstable : (prefixWord ++ tailWord_967324).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967324).length < 2 ^ (prefixWord ++ tailWord_967324).sum := by decide
  have hdescent : baseEnd_967324 < baseStart_967324 := by decide
  rcases family_descends (prefixWord ++ tailWord_967324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967341 : List Nat := [1, 5, 2, 1, 1, 3, 1, 3, 4]
def baseStart_967341 : Nat := 118140960795 + 967341 * 2 ^ 59
def prefixEnd_967341 : Nat := 4983230072969 + 3 ^ 40 * 967341 * 2
def baseEnd_967341 : Nat := 220760395467113336706127

theorem tailTrace_967341 : CollatzResearch.WordTrace tailWord_967341 prefixEnd_967341 220760395467113336706127 := by
  unfold tailWord_967341
  simp only [CollatzResearch.WordTrace]
  refine ⟨35281824788496240534973877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23521216525664160356649251 35281824788496240534973877)
  ·
    refine ⟨3307671073921522550153801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35281824788496240534973877 3307671073921522550153801)
    ·
      refine ⟨2480753305441141912615351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3307671073921522550153801 2480753305441141912615351)
      ·
        refine ⟨3721129958161712868923027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2480753305441141912615351 3721129958161712868923027)
        ·
          refine ⟨5581694937242569303384541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3721129958161712868923027 5581694937242569303384541)
          ·
            refine ⟨2093135601465963488769203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5581694937242569303384541 2093135601465963488769203)
            ·
              refine ⟨3139703402198945233153805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2093135601465963488769203 3139703402198945233153805)
              ·
                refine ⟨1177388775824604462432677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3139703402198945233153805 1177388775824604462432677)
                ·
                  refine ⟨220760395467113336706127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1177388775824604462432677 220760395467113336706127)
                  ·
                    rfl

theorem cell21_967341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 3, 4].length) (baseStart_967341 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_967341 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_967341 prefixEnd_967341 := by exact prefixLift 967341
  have htrace : WordTrace (prefixWord ++ tailWord_967341) baseStart_967341 baseEnd_967341 := by
    simpa [prefixWord, tailWord_967341, baseEnd_967341] using wordTrace_append hprefix tailTrace_967341
  have hstable : (prefixWord ++ tailWord_967341).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967341).length < 2 ^ (prefixWord ++ tailWord_967341).sum := by decide
  have hdescent : baseEnd_967341 < baseStart_967341 := by decide
  rcases family_descends (prefixWord ++ tailWord_967341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967386 : List Nat := [3, 1, 1, 2, 2, 2, 3, 4, 3]
def baseStart_967386 : Nat := 118140960795 + 967386 * 2 ^ 59
def prefixEnd_967386 : Nat := 4983230072969 + 3 ^ 40 * 967386 * 2
def baseEnd_967386 : Nat := 220770665080203258456035

theorem tailTrace_967386 : CollatzResearch.WordTrace tailWord_967386 prefixEnd_967386 220770665080203258456035 := by
  unfold tailWord_967386
  simp only [CollatzResearch.WordTrace]
  refine ⟨8820866518333303305090503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23522310715555475480241341 8820866518333303305090503)
  ·
    refine ⟨13231299777499954957635755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8820866518333303305090503 13231299777499954957635755)
    ·
      refine ⟨19846949666249932436453633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13231299777499954957635755 19846949666249932436453633)
      ·
        refine ⟨14885212249687449327340225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19846949666249932436453633 14885212249687449327340225)
        ·
          refine ⟨11163909187265586995505169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14885212249687449327340225 11163909187265586995505169)
          ·
            refine ⟨8372931890449190246628877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11163909187265586995505169 8372931890449190246628877)
            ·
              refine ⟨3139849458918446342485829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8372931890449190246628877 3139849458918446342485829)
              ·
                refine ⟨588721773547208689216093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3139849458918446342485829 588721773547208689216093)
                ·
                  refine ⟨220770665080203258456035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 588721773547208689216093 220770665080203258456035)
                  ·
                    rfl

theorem cell21_967386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 4, 3].length) (baseStart_967386 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_967386 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_967386 prefixEnd_967386 := by exact prefixLift 967386
  have htrace : WordTrace (prefixWord ++ tailWord_967386) baseStart_967386 baseEnd_967386 := by
    simpa [prefixWord, tailWord_967386, baseEnd_967386] using wordTrace_append hprefix tailTrace_967386
  have hstable : (prefixWord ++ tailWord_967386).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967386).length < 2 ^ (prefixWord ++ tailWord_967386).sum := by decide
  have hdescent : baseEnd_967386 < baseStart_967386 := by decide
  rcases family_descends (prefixWord ++ tailWord_967386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967445 : List Nat := [1, 3, 2, 1, 2, 2, 4, 1, 5]
def baseStart_967445 : Nat := 118140960795 + 967445 * 2 ^ 59
def prefixEnd_967445 : Nat := 4983230072969 + 3 ^ 40 * 967445 * 2
def baseEnd_967445 : Nat := 220784129684032266972581

theorem tailTrace_967445 : CollatzResearch.WordTrace tailWord_967445 prefixEnd_967445 220784129684032266972581 := by
  unfold tailWord_967445
  simp only [CollatzResearch.WordTrace]
  refine ⟨35285617980119466296759789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23523745320079644197839859 35285617980119466296759789)
  ·
    refine ⟨13232106742544799861284921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35285617980119466296759789 13232106742544799861284921)
    ·
      refine ⟨9924080056908599895963691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13232106742544799861284921 9924080056908599895963691)
      ·
        refine ⟨14886120085362899843945537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9924080056908599895963691 14886120085362899843945537)
        ·
          refine ⟨11164590064022174882959153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14886120085362899843945537 11164590064022174882959153)
          ·
            refine ⟨8373442548016631162219365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11164590064022174882959153 8373442548016631162219365)
            ·
              refine ⟨1570020477753118342916131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8373442548016631162219365 1570020477753118342916131)
              ·
                refine ⟨2355030716629677514374197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1570020477753118342916131 2355030716629677514374197)
                ·
                  refine ⟨220784129684032266972581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2355030716629677514374197 220784129684032266972581)
                  ·
                    rfl

theorem cell21_967445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 4, 1, 5].length) (baseStart_967445 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_967445 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_967445 prefixEnd_967445 := by exact prefixLift 967445
  have htrace : WordTrace (prefixWord ++ tailWord_967445) baseStart_967445 baseEnd_967445 := by
    simpa [prefixWord, tailWord_967445, baseEnd_967445] using wordTrace_append hprefix tailTrace_967445
  have hstable : (prefixWord ++ tailWord_967445).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967445).length < 2 ^ (prefixWord ++ tailWord_967445).sum := by decide
  have hdescent : baseEnd_967445 < baseStart_967445 := by decide
  rcases family_descends (prefixWord ++ tailWord_967445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967583 : List Nat := [1, 1, 2, 5, 2, 2, 3, 5]
def baseStart_967583 : Nat := 118140960795 + 967583 * 2 ^ 59
def prefixEnd_967583 : Nat := 4983230072969 + 3 ^ 40 * 967583 * 2
def baseEnd_967583 : Nat := 73605207721391564557433

theorem tailTrace_967583 : CollatzResearch.WordTrace tailWord_967583 prefixEnd_967583 73605207721391564557433 := by
  unfold tailWord_967583
  simp only [CollatzResearch.WordTrace]
  refine ⟨35290651253619515865283403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23527100835746343910188935 35290651253619515865283403)
  ·
    refine ⟨52935976880429273797925105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35290651253619515865283403 52935976880429273797925105)
    ·
      refine ⟨39701982660321955348443829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52935976880429273797925105 39701982660321955348443829)
      ·
        refine ⟨3722060874405183313916609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39701982660321955348443829 3722060874405183313916609)
        ·
          refine ⟨2791545655803887485437457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3722060874405183313916609 2791545655803887485437457)
          ·
            refine ⟨2093659241852915614078093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2791545655803887485437457 2093659241852915614078093)
            ·
              refine ⟨785122215694843355279285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2093659241852915614078093 785122215694843355279285)
              ·
                refine ⟨73605207721391564557433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 785122215694843355279285 73605207721391564557433)
                ·
                  rfl

theorem cell21_967583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 3, 5].length) (baseStart_967583 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_967583 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_967583 prefixEnd_967583 := by exact prefixLift 967583
  have htrace : WordTrace (prefixWord ++ tailWord_967583) baseStart_967583 baseEnd_967583 := by
    simpa [prefixWord, tailWord_967583, baseEnd_967583] using wordTrace_append hprefix tailTrace_967583
  have hstable : (prefixWord ++ tailWord_967583).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967583).length < 2 ^ (prefixWord ++ tailWord_967583).sum := by decide
  have hdescent : baseEnd_967583 < baseStart_967583 := by decide
  rcases family_descends (prefixWord ++ tailWord_967583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967614 : List Nat := [4, 2, 1, 1, 1, 2, 1, 6, 3]
def baseStart_967614 : Nat := 118140960795 + 967614 * 2 ^ 59
def prefixEnd_967614 : Nat := 4983230072969 + 3 ^ 40 * 967614 * 2
def baseEnd_967614 : Nat := 220822697786525528655569

theorem tailTrace_967614 : CollatzResearch.WordTrace tailWord_967614 prefixEnd_967614 220822697786525528655569 := by
  unfold tailWord_967614
  simp only [CollatzResearch.WordTrace]
  refine ⟨4411472739563401019957737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23527854611004805439774597 4411472739563401019957737)
  ·
    refine ⟨3308604554672550764968303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4411472739563401019957737 3308604554672550764968303)
    ·
      refine ⟨4962906832008826147452455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3308604554672550764968303 4962906832008826147452455)
      ·
        refine ⟨7444360248013239221178683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4962906832008826147452455 7444360248013239221178683)
        ·
          refine ⟨11166540372019858831768025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7444360248013239221178683 11166540372019858831768025)
          ·
            refine ⟨8374905279014894123826019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11166540372019858831768025 8374905279014894123826019)
            ·
              refine ⟨12562357918522341185739029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8374905279014894123826019 12562357918522341185739029)
              ·
                refine ⟨588860527430734743081517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12562357918522341185739029 588860527430734743081517)
                ·
                  refine ⟨220822697786525528655569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 588860527430734743081517 220822697786525528655569)
                  ·
                    rfl

theorem cell21_967614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 6, 3].length) (baseStart_967614 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_967614 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_967614 prefixEnd_967614 := by exact prefixLift 967614
  have htrace : WordTrace (prefixWord ++ tailWord_967614) baseStart_967614 baseEnd_967614 := by
    simpa [prefixWord, tailWord_967614, baseEnd_967614] using wordTrace_append hprefix tailTrace_967614
  have hstable : (prefixWord ++ tailWord_967614).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967614).length < 2 ^ (prefixWord ++ tailWord_967614).sum := by decide
  have hdescent : baseEnd_967614 < baseStart_967614 := by decide
  rcases family_descends (prefixWord ++ tailWord_967614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967642 : List Nat := [3, 1, 1, 2, 4, 2, 1, 7]
def baseStart_967642 : Nat := 118140960795 + 967642 * 2 ^ 59
def prefixEnd_967642 : Nat := 4983230072969 + 3 ^ 40 * 967642 * 2
def baseEnd_967642 : Nat := 73609695922667900729615

theorem tailTrace_967642 : CollatzResearch.WordTrace tailWord_967642 prefixEnd_967642 73609695922667900729615 := by
  unfold tailWord_967642
  simp only [CollatzResearch.WordTrace]
  refine ⟨8823200790101442235420295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23528535440270512627787453 8823200790101442235420295)
  ·
    refine ⟨13234801185152163353130443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8823200790101442235420295 13234801185152163353130443)
    ·
      refine ⟨19852201777728245029695665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13234801185152163353130443 19852201777728245029695665)
      ·
        refine ⟨14889151333296183772271749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19852201777728245029695665 14889151333296183772271749)
        ·
          refine ⟨2791715874993034457300953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14889151333296183772271749 2791715874993034457300953)
          ·
            refine ⟨2093786906244775842975715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2791715874993034457300953 2093786906244775842975715)
            ·
              refine ⟨3140680359367163764463573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2093786906244775842975715 3140680359367163764463573)
              ·
                refine ⟨73609695922667900729615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3140680359367163764463573 73609695922667900729615)
                ·
                  rfl

theorem cell21_967642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 7].length) (baseStart_967642 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_967642 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_967642 prefixEnd_967642 := by exact prefixLift 967642
  have htrace : WordTrace (prefixWord ++ tailWord_967642) baseStart_967642 baseEnd_967642 := by
    simpa [prefixWord, tailWord_967642, baseEnd_967642] using wordTrace_append hprefix tailTrace_967642
  have hstable : (prefixWord ++ tailWord_967642).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967642).length < 2 ^ (prefixWord ++ tailWord_967642).sum := by decide
  have hdescent : baseEnd_967642 < baseStart_967642 := by decide
  rcases family_descends (prefixWord ++ tailWord_967642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967656 : List Nat := [2, 1, 4, 1, 1, 1, 2, 2, 7]
def baseStart_967656 : Nat := 118140960795 + 967656 * 2 ^ 59
def prefixEnd_967656 : Nat := 4983230072969 + 3 ^ 40 * 967656 * 2
def baseEnd_967656 : Nat := 220832282758742788955483

theorem tailTrace_967656 : CollatzResearch.WordTrace tailWord_967656 prefixEnd_967656 220832282758742788955483 := by
  unfold tailWord_967656
  simp only [CollatzResearch.WordTrace]
  refine ⟨17646656891177524666345411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23528875854903366221793881 17646656891177524666345411)
  ·
    refine ⟨26469985336766286999518117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17646656891177524666345411 26469985336766286999518117)
    ·
      refine ⟨4963122250643678812409647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26469985336766286999518117 4963122250643678812409647)
      ·
        refine ⟨7444683375965518218614471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4963122250643678812409647 7444683375965518218614471)
        ·
          refine ⟨11167025063948277327921707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7444683375965518218614471 11167025063948277327921707)
          ·
            refine ⟨16750537595922415991882561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11167025063948277327921707 16750537595922415991882561)
            ·
              refine ⟨12562903196941811993911921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16750537595922415991882561 12562903196941811993911921)
              ·
                refine ⟨9422177397706358995433941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12562903196941811993911921 9422177397706358995433941)
                ·
                  refine ⟨220832282758742788955483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9422177397706358995433941 220832282758742788955483)
                  ·
                    rfl

theorem cell21_967656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 2, 7].length) (baseStart_967656 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_967656 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_967656 prefixEnd_967656 := by exact prefixLift 967656
  have htrace : WordTrace (prefixWord ++ tailWord_967656) baseStart_967656 baseEnd_967656 := by
    simpa [prefixWord, tailWord_967656, baseEnd_967656] using wordTrace_append hprefix tailTrace_967656
  have hstable : (prefixWord ++ tailWord_967656).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967656).length < 2 ^ (prefixWord ++ tailWord_967656).sum := by decide
  have hdescent : baseEnd_967656 < baseStart_967656 := by decide
  rcases family_descends (prefixWord ++ tailWord_967656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967808 : List Nat := [2, 1, 1, 2, 1, 3, 4, 2, 5]
def baseStart_967808 : Nat := 118140960795 + 967808 * 2 ^ 59
def prefixEnd_967808 : Nat := 4983230072969 + 3 ^ 40 * 967808 * 2
def baseEnd_967808 : Nat := 220866971229624302421839

theorem tailTrace_967808 : CollatzResearch.WordTrace tailWord_967808 prefixEnd_967808 220866971229624302421839 := by
  unfold tailWord_967808
  simp only [CollatzResearch.WordTrace]
  refine ⟨17649428838902189646112039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23532571785202919528149385 17649428838902189646112039)
  ·
    refine ⟨26474143258353284469168059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17649428838902189646112039 26474143258353284469168059)
    ·
      refine ⟨39711214887529926703752089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26474143258353284469168059 39711214887529926703752089)
      ·
        refine ⟨29783411165647445027814067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39711214887529926703752089 29783411165647445027814067)
        ·
          refine ⟨44675116748471167541721101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29783411165647445027814067 44675116748471167541721101)
          ·
            refine ⟨16753168780676687828145413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44675116748471167541721101 16753168780676687828145413)
            ·
              refine ⟨3141219146376878967777265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16753168780676687828145413 3141219146376878967777265)
              ·
                refine ⟨2355914359782659225832949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3141219146376878967777265 2355914359782659225832949)
                ·
                  refine ⟨220866971229624302421839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2355914359782659225832949 220866971229624302421839)
                  ·
                    rfl

theorem cell21_967808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 2, 5].length) (baseStart_967808 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_967808 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_967808 prefixEnd_967808 := by exact prefixLift 967808
  have htrace : WordTrace (prefixWord ++ tailWord_967808) baseStart_967808 baseEnd_967808 := by
    simpa [prefixWord, tailWord_967808, baseEnd_967808] using wordTrace_append hprefix tailTrace_967808
  have hstable : (prefixWord ++ tailWord_967808).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967808).length < 2 ^ (prefixWord ++ tailWord_967808).sum := by decide
  have hdescent : baseEnd_967808 < baseStart_967808 := by decide
  rcases family_descends (prefixWord ++ tailWord_967808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967870 : List Nat := [4, 2, 1, 1, 3, 1, 2, 7]
def baseStart_967870 : Nat := 118140960795 + 967870 * 2 ^ 59
def prefixEnd_967870 : Nat := 4983230072969 + 3 ^ 40 * 967870 * 2
def baseEnd_967870 : Nat := 73627040158108657462793

theorem tailTrace_967870 : CollatzResearch.WordTrace tailWord_967870 prefixEnd_967870 73627040158108657462793 := by
  unfold tailWord_967870
  simp only [CollatzResearch.WordTrace]
  refine ⟨4412639875447470485122633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23534079335719842587320709 4412639875447470485122633)
  ·
    refine ⟨3309479906585602863841975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4412639875447470485122633 3309479906585602863841975)
    ·
      refine ⟨4964219859878404295762963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3309479906585602863841975 4964219859878404295762963)
      ·
        refine ⟨7446329789817606443644445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4964219859878404295762963 7446329789817606443644445)
        ·
          refine ⟨2792373671181602416366667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7446329789817606443644445 2792373671181602416366667)
          ·
            refine ⟨4188560506772403624550001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2792373671181602416366667 4188560506772403624550001)
            ·
              refine ⟨3141420380079302718412501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4188560506772403624550001 3141420380079302718412501)
              ·
                refine ⟨73627040158108657462793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3141420380079302718412501 73627040158108657462793)
                ·
                  rfl

theorem cell21_967870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 7].length) (baseStart_967870 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_967870 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_967870 prefixEnd_967870 := by exact prefixLift 967870
  have htrace : WordTrace (prefixWord ++ tailWord_967870) baseStart_967870 baseEnd_967870 := by
    simpa [prefixWord, tailWord_967870, baseEnd_967870] using wordTrace_append hprefix tailTrace_967870
  have hstable : (prefixWord ++ tailWord_967870).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967870).length < 2 ^ (prefixWord ++ tailWord_967870).sum := by decide
  have hdescent : baseEnd_967870 < baseStart_967870 := by decide
  rcases family_descends (prefixWord ++ tailWord_967870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967915 : List Nat := [1, 1, 1, 1, 2, 6, 2, 3, 4]
def baseStart_967915 : Nat := 118140960795 + 967915 * 2 ^ 59
def prefixEnd_967915 : Nat := 4983230072969 + 3 ^ 40 * 967915 * 2
def baseEnd_967915 : Nat := 220891390087415894138287

theorem tailTrace_967915 : CollatzResearch.WordTrace tailWord_967915 prefixEnd_967915 220891390087415894138287 := by
  unfold tailWord_967915
  simp only [CollatzResearch.WordTrace]
  refine ⟨35302760288416736566369199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23535173525611157710912799 35302760288416736566369199)
  ·
    refine ⟨52954140432625104849553799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35302760288416736566369199 52954140432625104849553799)
    ·
      refine ⟨79431210648937657274330699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52954140432625104849553799 79431210648937657274330699)
      ·
        refine ⟨119146815973406485911496049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79431210648937657274330699 119146815973406485911496049)
        ·
          refine ⟨89360111980054864433622037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119146815973406485911496049 89360111980054864433622037)
          ·
            refine ⟨4188755249065071770326033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 89360111980054864433622037 4188755249065071770326033)
            ·
              refine ⟨3141566436798803827744525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4188755249065071770326033 3141566436798803827744525)
              ·
                refine ⟨1178087413799551435404197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3141566436798803827744525 1178087413799551435404197)
                ·
                  refine ⟨220891390087415894138287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1178087413799551435404197 220891390087415894138287)
                  ·
                    rfl

theorem cell21_967915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 3, 4].length) (baseStart_967915 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_967915 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_967915 prefixEnd_967915 := by exact prefixLift 967915
  have htrace : WordTrace (prefixWord ++ tailWord_967915) baseStart_967915 baseEnd_967915 := by
    simpa [prefixWord, tailWord_967915, baseEnd_967915] using wordTrace_append hprefix tailTrace_967915
  have hstable : (prefixWord ++ tailWord_967915).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967915).length < 2 ^ (prefixWord ++ tailWord_967915).sum := by decide
  have hdescent : baseEnd_967915 < baseStart_967915 := by decide
  rcases family_descends (prefixWord ++ tailWord_967915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967960 : List Nat := [2, 1, 2, 3, 1, 3, 1, 3, 5]
def baseStart_967960 : Nat := 118140960795 + 967960 * 2 ^ 59
def prefixEnd_967960 : Nat := 4983230072969 + 3 ^ 40 * 967960 * 2
def baseEnd_967960 : Nat := 220901659700505815888195

theorem tailTrace_967960 : CollatzResearch.WordTrace tailWord_967960 prefixEnd_967960 220901659700505815888195 := by
  unfold tailWord_967960
  simp only [CollatzResearch.WordTrace]
  refine ⟨17652200786626854625878667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23536267715502472834504889 17652200786626854625878667)
  ·
    refine ⟨26478301179940281938818001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17652200786626854625878667 26478301179940281938818001)
    ·
      refine ⟨19858725884955211454113501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26478301179940281938818001 19858725884955211454113501)
      ·
        refine ⟨7447022206858204295292563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19858725884955211454113501 7447022206858204295292563)
        ·
          refine ⟨11170533310287306442938845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7447022206858204295292563 11170533310287306442938845)
          ·
            refine ⟨4188949991357739916102067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11170533310287306442938845 4188949991357739916102067)
            ·
              refine ⟨6283424987036609874153101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4188949991357739916102067 6283424987036609874153101)
              ·
                refine ⟨2356284370138728702807413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6283424987036609874153101 2356284370138728702807413)
                ·
                  refine ⟨220901659700505815888195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2356284370138728702807413 220901659700505815888195)
                  ·
                    rfl

theorem cell21_967960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 3, 5].length) (baseStart_967960 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_967960 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_967960 prefixEnd_967960 := by exact prefixLift 967960
  have htrace : WordTrace (prefixWord ++ tailWord_967960) baseStart_967960 baseEnd_967960 := by
    simpa [prefixWord, tailWord_967960, baseEnd_967960] using wordTrace_append hprefix tailTrace_967960
  have hstable : (prefixWord ++ tailWord_967960).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967960).length < 2 ^ (prefixWord ++ tailWord_967960).sum := by decide
  have hdescent : baseEnd_967960 < baseStart_967960 := by decide
  rcases family_descends (prefixWord ++ tailWord_967960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968062 : List Nat := [4, 2, 3, 2, 2, 1, 2, 2, 3]
def baseStart_968062 : Nat := 118140960795 + 968062 * 2 ^ 59
def prefixEnd_968062 : Nat := 4983230072969 + 3 ^ 40 * 968062 * 2
def baseEnd_968062 : Nat := 220924937490176305187987

theorem tailTrace_968062 : CollatzResearch.WordTrace tailWord_968062 prefixEnd_968062 220924937490176305187987 := by
  unfold tailWord_968062
  simp only [CollatzResearch.WordTrace]
  refine ⟨4413515227360522583996305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23538747879256120447980293 4413515227360522583996305)
  ·
    refine ⟨3310136420520391937997229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4413515227360522583996305 3310136420520391937997229)
    ·
      refine ⟨1241301157695146976748961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3310136420520391937997229 1241301157695146976748961)
      ·
        refine ⟨930975868271360232561721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1241301157695146976748961 930975868271360232561721)
        ·
          refine ⟨698231901203520174421291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 930975868271360232561721 698231901203520174421291)
          ·
            refine ⟨1047347851805280261631937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 698231901203520174421291 1047347851805280261631937)
            ·
              refine ⟨785510888853960196223953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1047347851805280261631937 785510888853960196223953)
              ·
                refine ⟨589133166640470147167965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 785510888853960196223953 589133166640470147167965)
                ·
                  refine ⟨220924937490176305187987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 589133166640470147167965 220924937490176305187987)
                  ·
                    rfl

theorem cell21_968062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 2, 2, 3].length) (baseStart_968062 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_968062 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_968062 prefixEnd_968062 := by exact prefixLift 968062
  have htrace : WordTrace (prefixWord ++ tailWord_968062) baseStart_968062 baseEnd_968062 := by
    simpa [prefixWord, tailWord_968062, baseEnd_968062] using wordTrace_append hprefix tailTrace_968062
  have hstable : (prefixWord ++ tailWord_968062).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968062).length < 2 ^ (prefixWord ++ tailWord_968062).sum := by decide
  have hdescent : baseEnd_968062 < baseStart_968062 := by decide
  rcases family_descends (prefixWord ++ tailWord_968062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968067 : List Nat := [1, 1, 1, 3, 5, 1, 1, 4, 4]
def baseStart_968067 : Nat := 118140960795 + 968067 * 2 ^ 59
def prefixEnd_968067 : Nat := 4983230072969 + 3 ^ 40 * 968067 * 2
def baseEnd_968067 : Nat := 220926078558297407604643

theorem tailTrace_968067 : CollatzResearch.WordTrace tailWord_968067 prefixEnd_968067 220926078558297407604643 := by
  unfold tailWord_968067
  simp only [CollatzResearch.WordTrace]
  refine ⟨35308304183866066525902455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23538869455910711017268303 35308304183866066525902455)
  ·
    refine ⟨52962456275799099788853683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35308304183866066525902455 52962456275799099788853683)
    ·
      refine ⟨79443684413698649683280525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52962456275799099788853683 79443684413698649683280525)
      ·
        refine ⟨29791381655136993631230197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79443684413698649683280525 29791381655136993631230197)
        ·
          refine ⟨2792942030169093152927831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29791381655136993631230197 2792942030169093152927831)
          ·
            refine ⟨4189413045253639729391747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2792942030169093152927831 4189413045253639729391747)
            ·
              refine ⟨6284119567880459594087621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4189413045253639729391747 6284119567880459594087621)
              ·
                refine ⟨1178272418977586173891429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6284119567880459594087621 1178272418977586173891429)
                ·
                  refine ⟨220926078558297407604643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1178272418977586173891429 220926078558297407604643)
                  ·
                    rfl

theorem cell21_968067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 4, 4].length) (baseStart_968067 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_968067 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_968067 prefixEnd_968067 := by exact prefixLift 968067
  have htrace : WordTrace (prefixWord ++ tailWord_968067) baseStart_968067 baseEnd_968067 := by
    simpa [prefixWord, tailWord_968067, baseEnd_968067] using wordTrace_append hprefix tailTrace_968067
  have hstable : (prefixWord ++ tailWord_968067).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968067).length < 2 ^ (prefixWord ++ tailWord_968067).sum := by decide
  have hdescent : baseEnd_968067 < baseStart_968067 := by decide
  rcases family_descends (prefixWord ++ tailWord_968067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968084 : List Nat := [2, 4, 2, 1, 2, 1, 2, 3, 4]
def baseStart_968084 : Nat := 118140960795 + 968084 * 2 ^ 59
def prefixEnd_968084 : Nat := 4983230072969 + 3 ^ 40 * 968084 * 2
def baseEnd_968084 : Nat := 220929958189909155821275

theorem tailTrace_968084 : CollatzResearch.WordTrace tailWord_968084 prefixEnd_968084 220929958189909155821275 := by
  unfold tailWord_968084
  simp only [CollatzResearch.WordTrace]
  refine ⟨17654462112402239214635653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23539282816536318952847537 17654462112402239214635653)
  ·
    refine ⟨3310211646075419852744185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17654462112402239214635653 3310211646075419852744185)
    ·
      refine ⟨2482658734556564889558139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3310211646075419852744185 2482658734556564889558139)
      ·
        refine ⟨3723988101834847334337209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2482658734556564889558139 3723988101834847334337209)
        ·
          refine ⟨2792991076376135500752907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3723988101834847334337209 2792991076376135500752907)
          ·
            refine ⟨4189486614564203251129361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2792991076376135500752907 4189486614564203251129361)
            ·
              refine ⟨3142114960923152438347021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4189486614564203251129361 3142114960923152438347021)
              ·
                refine ⟨1178293110346182164380133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3142114960923152438347021 1178293110346182164380133)
                ·
                  refine ⟨220929958189909155821275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1178293110346182164380133 220929958189909155821275)
                  ·
                    rfl

theorem cell21_968084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 3, 4].length) (baseStart_968084 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_968084 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_968084 prefixEnd_968084 := by exact prefixLift 968084
  have htrace : WordTrace (prefixWord ++ tailWord_968084) baseStart_968084 baseEnd_968084 := by
    simpa [prefixWord, tailWord_968084, baseEnd_968084] using wordTrace_append hprefix tailTrace_968084
  have hstable : (prefixWord ++ tailWord_968084).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968084).length < 2 ^ (prefixWord ++ tailWord_968084).sum := by decide
  have hdescent : baseEnd_968084 < baseStart_968084 := by decide
  rcases family_descends (prefixWord ++ tailWord_968084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968188 : List Nat := [2, 2, 2, 1, 2, 1, 5, 1, 5]
def baseStart_968188 : Nat := 118140960795 + 968188 * 2 ^ 59
def prefixEnd_968188 : Nat := 4983230072969 + 3 ^ 40 * 968188 * 2
def baseEnd_968188 : Nat := 220953692406828086087729

theorem tailTrace_968188 : CollatzResearch.WordTrace tailWord_968188 prefixEnd_968188 220953692406828086087729 := by
  unfold tailWord_968188
  simp only [CollatzResearch.WordTrace]
  refine ⟨17656358708213852095528609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23541811610951802794038145 17656358708213852095528609)
  ·
    refine ⟨13242269031160389071646457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17656358708213852095528609 13242269031160389071646457)
    ·
      refine ⟨9931701773370291803734843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13242269031160389071646457 9931701773370291803734843)
      ·
        refine ⟨14897552660055437705602265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9931701773370291803734843 14897552660055437705602265)
        ·
          refine ⟨11173164495041578279201699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14897552660055437705602265 11173164495041578279201699)
          ·
            refine ⟨16759746742562367418802549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11173164495041578279201699 16759746742562367418802549)
            ·
              refine ⟨1571226257115221945512739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16759746742562367418802549 1571226257115221945512739)
              ·
                refine ⟨2356839385672832918269109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1571226257115221945512739 2356839385672832918269109)
                ·
                  refine ⟨220953692406828086087729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2356839385672832918269109 220953692406828086087729)
                  ·
                    rfl

theorem cell21_968188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 5, 1, 5].length) (baseStart_968188 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_968188 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_968188 prefixEnd_968188 := by exact prefixLift 968188
  have htrace : WordTrace (prefixWord ++ tailWord_968188) baseStart_968188 baseEnd_968188 := by
    simpa [prefixWord, tailWord_968188, baseEnd_968188] using wordTrace_append hprefix tailTrace_968188
  have hstable : (prefixWord ++ tailWord_968188).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968188).length < 2 ^ (prefixWord ++ tailWord_968188).sum := by decide
  have hdescent : baseEnd_968188 < baseStart_968188 := by decide
  rcases family_descends (prefixWord ++ tailWord_968188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968194 : List Nat := [3, 4, 1, 2, 1, 3, 2, 1, 4]
def baseStart_968194 : Nat := 118140960795 + 968194 * 2 ^ 59
def prefixEnd_968194 : Nat := 4983230072969 + 3 ^ 40 * 968194 * 2
def baseEnd_968194 : Nat := 220955061688573408987717

theorem tailTrace_968194 : CollatzResearch.WordTrace tailWord_968194 prefixEnd_968194 220955061688573408987717 := by
  unfold tailWord_968194
  simp only [CollatzResearch.WordTrace]
  refine ⟨8828234063601491803943909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23541957502937311477183757 8828234063601491803943909)
  ·
    refine ⟨1655293886925279713239483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8828234063601491803943909 1655293886925279713239483)
    ·
      refine ⟨2482940830387919569859225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1655293886925279713239483 2482940830387919569859225)
      ·
        refine ⟨1862205622790939677394419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2482940830387919569859225 1862205622790939677394419)
        ·
          refine ⟨2793308434186409516091629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1862205622790939677394419 2793308434186409516091629)
          ·
            refine ⟨1047490662819903568534361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2793308434186409516091629 1047490662819903568534361)
            ·
              refine ⟨785617997114927676400771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1047490662819903568534361 785617997114927676400771)
              ·
                refine ⟨1178426995672391514601157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 785617997114927676400771 1178426995672391514601157)
                ·
                  refine ⟨220955061688573408987717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1178426995672391514601157 220955061688573408987717)
                  ·
                    rfl

theorem cell21_968194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_968194 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_968194 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_968194 prefixEnd_968194 := by exact prefixLift 968194
  have htrace : WordTrace (prefixWord ++ tailWord_968194) baseStart_968194 baseEnd_968194 := by
    simpa [prefixWord, tailWord_968194, baseEnd_968194] using wordTrace_append hprefix tailTrace_968194
  have hstable : (prefixWord ++ tailWord_968194).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968194).length < 2 ^ (prefixWord ++ tailWord_968194).sum := by decide
  have hdescent : baseEnd_968194 < baseStart_968194 := by decide
  rcases family_descends (prefixWord ++ tailWord_968194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968295 : List Nat := [1, 1, 5, 1, 1, 1, 5, 2, 4]
def baseStart_968295 : Nat := 118140960795 + 968295 * 2 ^ 59
def prefixEnd_968295 : Nat := 4983230072969 + 3 ^ 40 * 968295 * 2
def baseEnd_968295 : Nat := 220978111264619677804177

theorem tailTrace_968295 : CollatzResearch.WordTrace tailWord_968295 prefixEnd_968295 220978111264619677804177 := by
  unfold tailWord_968295
  simp only [CollatzResearch.WordTrace]
  refine ⟨35316620027040061465202339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23544413351360040976801559 35316620027040061465202339)
  ·
    refine ⟨52974930040560092197803509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35316620027040061465202339 52974930040560092197803509)
    ·
      refine ⟨4966399691302508643544079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 52974930040560092197803509 4966399691302508643544079)
      ·
        refine ⟨7449599536953762965316119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4966399691302508643544079 7449599536953762965316119)
        ·
          refine ⟨11174399305430644447974179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7449599536953762965316119 11174399305430644447974179)
          ·
            refine ⟨16761598958145966671961269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11174399305430644447974179 16761598958145966671961269)
            ·
              refine ⟨1571399902326184375496369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16761598958145966671961269 1571399902326184375496369)
              ·
                refine ⟨1178549926744638281622277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1571399902326184375496369 1178549926744638281622277)
                ·
                  refine ⟨220978111264619677804177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1178549926744638281622277 220978111264619677804177)
                  ·
                    rfl

theorem cell21_968295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 5, 2, 4].length) (baseStart_968295 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_968295 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_968295 prefixEnd_968295 := by exact prefixLift 968295
  have htrace : WordTrace (prefixWord ++ tailWord_968295) baseStart_968295 baseEnd_968295 := by
    simpa [prefixWord, tailWord_968295, baseEnd_968295] using wordTrace_append hprefix tailTrace_968295
  have hstable : (prefixWord ++ tailWord_968295).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968295).length < 2 ^ (prefixWord ++ tailWord_968295).sum := by decide
  have hdescent : baseEnd_968295 < baseStart_968295 := by decide
  rcases family_descends (prefixWord ++ tailWord_968295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968360 : List Nat := [2, 1, 7, 1, 1, 1, 2, 6]
def baseStart_968360 : Nat := 118140960795 + 968360 * 2 ^ 59
def prefixEnd_968360 : Nat := 4983230072969 + 3 ^ 40 * 968360 * 2
def baseEnd_968360 : Nat := 73664315050064669740237

theorem tailTrace_968360 : CollatzResearch.WordTrace tailWord_968360 prefixEnd_968360 73664315050064669740237 := by
  unfold tailWord_968360
  simp only [CollatzResearch.WordTrace]
  refine ⟨17659495385902288783159267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23545993847869718377545689 17659495385902288783159267)
  ·
    refine ⟨26489243078853433174738901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17659495385902288783159267 26489243078853433174738901)
    ·
      refine ⟨620841634660627340032943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 26489243078853433174738901 620841634660627340032943)
      ·
        refine ⟨931262451990941010049415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 620841634660627340032943 931262451990941010049415)
        ·
          refine ⟨1396893677986411515074123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 931262451990941010049415 1396893677986411515074123)
          ·
            refine ⟨2095340516979617272611185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1396893677986411515074123 2095340516979617272611185)
            ·
              refine ⟨1571505387734712954458389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2095340516979617272611185 1571505387734712954458389)
              ·
                refine ⟨73664315050064669740237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1571505387734712954458389 73664315050064669740237)
                ·
                  rfl

theorem cell21_968360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 2, 6].length) (baseStart_968360 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_968360 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_968360 prefixEnd_968360 := by exact prefixLift 968360
  have htrace : WordTrace (prefixWord ++ tailWord_968360) baseStart_968360 baseEnd_968360 := by
    simpa [prefixWord, tailWord_968360, baseEnd_968360] using wordTrace_append hprefix tailTrace_968360
  have hstable : (prefixWord ++ tailWord_968360).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968360).length < 2 ^ (prefixWord ++ tailWord_968360).sum := by decide
  have hdescent : baseEnd_968360 < baseStart_968360 := by decide
  rcases family_descends (prefixWord ++ tailWord_968360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968368 : List Nat := [2, 1, 1, 1, 2, 1, 5, 8]
def baseStart_968368 : Nat := 118140960795 + 968368 * 2 ^ 59
def prefixEnd_968368 : Nat := 4983230072969 + 3 ^ 40 * 968368 * 2
def baseEnd_968368 : Nat := 73664923619729257695787

theorem tailTrace_968368 : CollatzResearch.WordTrace tailWord_968368 prefixEnd_968368 73664923619729257695787 := by
  unfold tailWord_968368
  simp only [CollatzResearch.WordTrace]
  refine ⟨17659641277887797466304879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23546188370517063288406505 17659641277887797466304879)
  ·
    refine ⟨26489461916831696199457319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17659641277887797466304879 26489461916831696199457319)
    ·
      refine ⟨39734192875247544299185979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26489461916831696199457319 39734192875247544299185979)
      ·
        refine ⟨59601289312871316448778969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39734192875247544299185979 59601289312871316448778969)
        ·
          refine ⟨44700966984653487336584227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59601289312871316448778969 44700966984653487336584227)
          ·
            refine ⟨67051450476980231004876341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44700966984653487336584227 67051450476980231004876341)
            ·
              refine ⟨6286073482216896656707157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67051450476980231004876341 6286073482216896656707157)
              ·
                refine ⟨73664923619729257695787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6286073482216896656707157 73664923619729257695787)
                ·
                  rfl

theorem cell21_968368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 8].length) (baseStart_968368 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_968368 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_968368 prefixEnd_968368 := by exact prefixLift 968368
  have htrace : WordTrace (prefixWord ++ tailWord_968368) baseStart_968368 baseEnd_968368 := by
    simpa [prefixWord, tailWord_968368, baseEnd_968368] using wordTrace_append hprefix tailTrace_968368
  have hstable : (prefixWord ++ tailWord_968368).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968368).length < 2 ^ (prefixWord ++ tailWord_968368).sum := by decide
  have hdescent : baseEnd_968368 < baseStart_968368 := by decide
  rcases family_descends (prefixWord ++ tailWord_968368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968419 : List Nat := [1, 1, 1, 7, 3, 1, 1, 6]
def baseStart_968419 : Nat := 118140960795 + 968419 * 2 ^ 59
def prefixEnd_968419 : Nat := 4983230072969 + 3 ^ 40 * 968419 * 2
def baseEnd_968419 : Nat := 73668803251341005912419

theorem tailTrace_968419 : CollatzResearch.WordTrace tailWord_968419 prefixEnd_968419 73668803251341005912419 := by
  unfold tailWord_968419
  simp only [CollatzResearch.WordTrace]
  refine ⟨35321142678590830642716311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23547428452393887095144207 35321142678590830642716311)
  ·
    refine ⟨52981714017886245964074467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35321142678590830642716311 52981714017886245964074467)
    ·
      refine ⟨79472571026829368946111701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52981714017886245964074467 79472571026829368946111701)
      ·
        refine ⟨1862638383441313334674493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 79472571026829368946111701 1862638383441313334674493)
        ·
          refine ⟨698489393790492500502935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1862638383441313334674493 698489393790492500502935)
          ·
            refine ⟨1047734090685738750754403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 698489393790492500502935 1047734090685738750754403)
            ·
              refine ⟨1571601136028608126131605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1047734090685738750754403 1571601136028608126131605)
              ·
                refine ⟨73668803251341005912419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1571601136028608126131605 73668803251341005912419)
                ·
                  rfl

theorem cell21_968419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 1, 6].length) (baseStart_968419 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_968419 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_968419 prefixEnd_968419 := by exact prefixLift 968419
  have htrace : WordTrace (prefixWord ++ tailWord_968419) baseStart_968419 baseEnd_968419 := by
    simpa [prefixWord, tailWord_968419, baseEnd_968419] using wordTrace_append hprefix tailTrace_968419
  have hstable : (prefixWord ++ tailWord_968419).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968419).length < 2 ^ (prefixWord ++ tailWord_968419).sum := by decide
  have hdescent : baseEnd_968419 < baseStart_968419 := by decide
  rcases family_descends (prefixWord ++ tailWord_968419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968436 : List Nat := [2, 6, 1, 1, 1, 2, 3, 5]
def baseStart_968436 : Nat := 118140960795 + 968436 * 2 ^ 59
def prefixEnd_968436 : Nat := 4983230072969 + 3 ^ 40 * 968436 * 2
def baseEnd_968436 : Nat := 73670096461878255317963

theorem tailTrace_968436 : CollatzResearch.WordTrace tailWord_968436 prefixEnd_968436 73670096461878255317963 := by
  unfold tailWord_968436
  simp only [CollatzResearch.WordTrace]
  refine ⟨17660881359764621273042581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23547841813019495030723441 17660881359764621273042581)
  ·
    refine ⟨827853813738966622173871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 17660881359764621273042581 827853813738966622173871)
    ·
      refine ⟨1241780720608449933260807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 827853813738966622173871 1241780720608449933260807)
      ·
        refine ⟨1862671080912674899891211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1241780720608449933260807 1862671080912674899891211)
        ·
          refine ⟨2794006621369012349836817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1862671080912674899891211 2794006621369012349836817)
          ·
            refine ⟨2095504966026759262377613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2794006621369012349836817 2095504966026759262377613)
            ·
              refine ⟨785814362260034723391605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2095504966026759262377613 785814362260034723391605)
              ·
                refine ⟨73670096461878255317963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 785814362260034723391605 73670096461878255317963)
                ·
                  rfl

theorem cell21_968436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 3, 5].length) (baseStart_968436 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_968436 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_968436 prefixEnd_968436 := by exact prefixLift 968436
  have htrace : WordTrace (prefixWord ++ tailWord_968436) baseStart_968436 baseEnd_968436 := by
    simpa [prefixWord, tailWord_968436, baseEnd_968436] using wordTrace_append hprefix tailTrace_968436
  have hstable : (prefixWord ++ tailWord_968436).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968436).length < 2 ^ (prefixWord ++ tailWord_968436).sum := by decide
  have hdescent : baseEnd_968436 < baseStart_968436 := by decide
  rcases family_descends (prefixWord ++ tailWord_968436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968450 : List Nat := [3, 4, 1, 1, 1, 1, 4, 3, 3]
def baseStart_968450 : Nat := 118140960795 + 968450 * 2 ^ 59
def prefixEnd_968450 : Nat := 4983230072969 + 3 ^ 40 * 968450 * 2
def baseEnd_968450 : Nat := 221013484376373852720527

theorem tailTrace_968450 : CollatzResearch.WordTrace tailWord_968450 prefixEnd_968450 221013484376373852720527 := by
  unfold tailWord_968450
  simp only [CollatzResearch.WordTrace]
  refine ⟨8830568335369630734273701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23548182227652348624729869 8830568335369630734273701)
  ·
    refine ⟨1655731562881805762676319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8830568335369630734273701 1655731562881805762676319)
    ·
      refine ⟨2483597344322708644014479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1655731562881805762676319 2483597344322708644014479)
      ·
        refine ⟨3725396016484062966021719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2483597344322708644014479 3725396016484062966021719)
        ·
          refine ⟨5588094024726094449032579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3725396016484062966021719 5588094024726094449032579)
          ·
            refine ⟨8382141037089141673548869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5588094024726094449032579 8382141037089141673548869)
            ·
              refine ⟨1571651444454214063790413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8382141037089141673548869 1571651444454214063790413)
              ·
                refine ⟨589369291670330273921405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1571651444454214063790413 589369291670330273921405)
                ·
                  refine ⟨221013484376373852720527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 589369291670330273921405 221013484376373852720527)
                  ·
                    rfl

theorem cell21_968450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 4, 3, 3].length) (baseStart_968450 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_968450 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_968450 prefixEnd_968450 := by exact prefixLift 968450
  have htrace : WordTrace (prefixWord ++ tailWord_968450) baseStart_968450 baseEnd_968450 := by
    simpa [prefixWord, tailWord_968450, baseEnd_968450] using wordTrace_append hprefix tailTrace_968450
  have hstable : (prefixWord ++ tailWord_968450).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968450).length < 2 ^ (prefixWord ++ tailWord_968450).sum := by decide
  have hdescent : baseEnd_968450 < baseStart_968450 := by decide
  rcases family_descends (prefixWord ++ tailWord_968450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968489 : List Nat := [1, 2, 1, 1, 1, 1, 1, 3, 10]
def baseStart_968489 : Nat := 118140960795 + 968489 * 2 ^ 59
def prefixEnd_968489 : Nat := 4983230072969 + 3 ^ 40 * 968489 * 2
def baseEnd_968489 : Nat := 221022384707718451570447

theorem tailTrace_968489 : CollatzResearch.WordTrace tailWord_968489 prefixEnd_968489 221022384707718451570447 := by
  unfold tailWord_968489
  simp only [CollatzResearch.WordTrace]
  refine ⟨35323695788337232597764521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23549130525558155065176347 35323695788337232597764521)
  ·
    refine ⟨26492771841252924448323391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35323695788337232597764521 26492771841252924448323391)
    ·
      refine ⟨39739157761879386672485087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26492771841252924448323391 39739157761879386672485087)
      ·
        refine ⟨59608736642819080008727631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39739157761879386672485087 59608736642819080008727631)
        ·
          refine ⟨89413104964228620013091447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59608736642819080008727631 89413104964228620013091447)
          ·
            refine ⟨134119657446342930019637171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89413104964228620013091447 134119657446342930019637171)
            ·
              refine ⟨201179486169514395029455757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134119657446342930019637171 201179486169514395029455757)
              ·
                refine ⟨75442307313567898136045909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 201179486169514395029455757 75442307313567898136045909)
                ·
                  refine ⟨221022384707718451570447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 75442307313567898136045909 221022384707718451570447)
                  ·
                    rfl

theorem cell21_968489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 10].length) (baseStart_968489 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_968489 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_968489 prefixEnd_968489 := by exact prefixLift 968489
  have htrace : WordTrace (prefixWord ++ tailWord_968489) baseStart_968489 baseEnd_968489 := by
    simpa [prefixWord, tailWord_968489, baseEnd_968489] using wordTrace_append hprefix tailTrace_968489
  have hstable : (prefixWord ++ tailWord_968489).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968489).length < 2 ^ (prefixWord ++ tailWord_968489).sum := by decide
  have hdescent : baseEnd_968489 < baseStart_968489 := by decide
  rcases family_descends (prefixWord ++ tailWord_968489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968506 : List Nat := [3, 1, 1, 1, 5, 1, 1, 2, 6]
def baseStart_968506 : Nat := 118140960795 + 968506 * 2 ^ 59
def prefixEnd_968506 : Nat := 4983230072969 + 3 ^ 40 * 968506 * 2
def baseEnd_968506 : Nat := 221026264339330199787079

theorem tailTrace_968506 : CollatzResearch.WordTrace tailWord_968506 prefixEnd_968506 221026264339330199787079 := by
  unfold tailWord_968506
  simp only [CollatzResearch.WordTrace]
  refine ⟨8831078957318911125283343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23549543886183763000755581 8831078957318911125283343)
  ·
    refine ⟨13246618435978366687925015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8831078957318911125283343 13246618435978366687925015)
    ·
      refine ⟨19869927653967550031887523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13246618435978366687925015 19869927653967550031887523)
      ·
        refine ⟨29804891480951325047831285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19869927653967550031887523 29804891480951325047831285)
        ·
          refine ⟨2794208576339186723234183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29804891480951325047831285 2794208576339186723234183)
          ·
            refine ⟨4191312864508780084851275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2794208576339186723234183 4191312864508780084851275)
            ·
              refine ⟨6286969296763170127276913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4191312864508780084851275 6286969296763170127276913)
              ·
                refine ⟨4715226972572377595457685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6286969296763170127276913 4715226972572377595457685)
                ·
                  refine ⟨221026264339330199787079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4715226972572377595457685 221026264339330199787079)
                  ·
                    rfl

theorem cell21_968506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 2, 6].length) (baseStart_968506 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_968506 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_968506 prefixEnd_968506 := by exact prefixLift 968506
  have htrace : WordTrace (prefixWord ++ tailWord_968506) baseStart_968506 baseEnd_968506 := by
    simpa [prefixWord, tailWord_968506, baseEnd_968506] using wordTrace_append hprefix tailTrace_968506
  have hstable : (prefixWord ++ tailWord_968506).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968506).length < 2 ^ (prefixWord ++ tailWord_968506).sum := by decide
  have hdescent : baseEnd_968506 < baseStart_968506 := by decide
  rcases family_descends (prefixWord ++ tailWord_968506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968520 : List Nat := [2, 1, 3, 1, 1, 4, 9]
def baseStart_968520 : Nat := 118140960795 + 968520 * 2 ^ 59
def prefixEnd_968520 : Nat := 4983230072969 + 3 ^ 40 * 968520 * 2
def baseEnd_968520 : Nat := 24558828814452142950413

theorem tailTrace_968520 : CollatzResearch.WordTrace tailWord_968520 prefixEnd_968520 24558828814452142950413 := by
  unfold tailWord_968520
  simp only [CollatzResearch.WordTrace]
  refine ⟨17662413225612462446071507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23549884300816616594762009 17662413225612462446071507)
  ·
    refine ⟨26493619838418693669107261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17662413225612462446071507 26493619838418693669107261)
    ·
      refine ⟨9935107439407010125915223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26493619838418693669107261 9935107439407010125915223)
      ·
        refine ⟨14902661159110515188872835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9935107439407010125915223 14902661159110515188872835)
        ·
          refine ⟨22353991738665772783309253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14902661159110515188872835 22353991738665772783309253)
          ·
            refine ⟨4191373450999832396870485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22353991738665772783309253 4191373450999832396870485)
            ·
              refine ⟨24558828814452142950413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4191373450999832396870485 24558828814452142950413)
              ·
                rfl

theorem cell21_968520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 9].length) (baseStart_968520 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_968520 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_968520 prefixEnd_968520 := by exact prefixLift 968520
  have htrace : WordTrace (prefixWord ++ tailWord_968520) baseStart_968520 baseEnd_968520 := by
    simpa [prefixWord, tailWord_968520, baseEnd_968520] using wordTrace_append hprefix tailTrace_968520
  have hstable : (prefixWord ++ tailWord_968520).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968520).length < 2 ^ (prefixWord ++ tailWord_968520).sum := by decide
  have hdescent : baseEnd_968520 < baseStart_968520 := by decide
  rcases family_descends (prefixWord ++ tailWord_968520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968540 : List Nat := [2, 2, 4, 2, 2, 1, 1, 3, 4]
def baseStart_968540 : Nat := 118140960795 + 968540 * 2 ^ 59
def prefixEnd_968540 : Nat := 4983230072969 + 3 ^ 40 * 968540 * 2
def baseEnd_968540 : Nat := 221034023602553696220343

theorem tailTrace_968540 : CollatzResearch.WordTrace tailWord_968540 prefixEnd_968540 221034023602553696220343 := by
  unfold tailWord_968540
  simp only [CollatzResearch.WordTrace]
  refine ⟨17662777955576234153935537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23550370607434978871914049 17662777955576234153935537)
  ·
    refine ⟨13247083466682175615451653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17662777955576234153935537 13247083466682175615451653)
    ·
      refine ⟨2483828150002907927897185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13247083466682175615451653 2483828150002907927897185)
      ·
        refine ⟨1862871112502180945922889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2483828150002907927897185 1862871112502180945922889)
        ·
          refine ⟨1397153334376635709442167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1862871112502180945922889 1397153334376635709442167)
          ·
            refine ⟨2095730001564953564163251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1397153334376635709442167 2095730001564953564163251)
            ·
              refine ⟨3143595002347430346244877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2095730001564953564163251 3143595002347430346244877)
              ·
                refine ⟨1178848125880286379841829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3143595002347430346244877 1178848125880286379841829)
                ·
                  refine ⟨221034023602553696220343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1178848125880286379841829 221034023602553696220343)
                  ·
                    rfl

theorem cell21_968540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 3, 4].length) (baseStart_968540 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_968540 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_968540 prefixEnd_968540 := by exact prefixLift 968540
  have htrace : WordTrace (prefixWord ++ tailWord_968540) baseStart_968540 baseEnd_968540 := by
    simpa [prefixWord, tailWord_968540, baseEnd_968540] using wordTrace_append hprefix tailTrace_968540
  have hstable : (prefixWord ++ tailWord_968540).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968540).length < 2 ^ (prefixWord ++ tailWord_968540).sum := by decide
  have hdescent : baseEnd_968540 < baseStart_968540 := by decide
  rcases family_descends (prefixWord ++ tailWord_968540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968551 : List Nat := [1, 1, 5, 1, 2, 1, 2, 1, 7]
def baseStart_968551 : Nat := 118140960795 + 968551 * 2 ^ 59
def prefixEnd_968551 : Nat := 4983230072969 + 3 ^ 40 * 968551 * 2
def baseEnd_968551 : Nat := 221036533952420121536987

theorem tailTrace_968551 : CollatzResearch.WordTrace tailWord_968551 prefixEnd_968551 221036533952420121536987 := by
  unfold tailWord_968551
  simp only [CollatzResearch.WordTrace]
  refine ⟨35325957114112617186521507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23550638076075078124347671 35325957114112617186521507)
  ·
    refine ⟨52988935671168925779782261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35325957114112617186521507 52988935671168925779782261)
    ·
      refine ⟨4967712719172086791854587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 52988935671168925779782261 4967712719172086791854587)
      ·
        refine ⟨7451569078758130187781881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4967712719172086791854587 7451569078758130187781881)
        ·
          refine ⟨5588676809068597640836411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7451569078758130187781881 5588676809068597640836411)
          ·
            refine ⟨8383015213602896461254617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5588676809068597640836411 8383015213602896461254617)
            ·
              refine ⟨6287261410202172345940963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8383015213602896461254617 6287261410202172345940963)
              ·
                refine ⟨9430892115303258518911445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6287261410202172345940963 9430892115303258518911445)
                ·
                  refine ⟨221036533952420121536987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9430892115303258518911445 221036533952420121536987)
                  ·
                    rfl

theorem cell21_968551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 1, 7].length) (baseStart_968551 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_968551 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_968551 prefixEnd_968551 := by exact prefixLift 968551
  have htrace : WordTrace (prefixWord ++ tailWord_968551) baseStart_968551 baseEnd_968551 := by
    simpa [prefixWord, tailWord_968551, baseEnd_968551] using wordTrace_append hprefix tailTrace_968551
  have hstable : (prefixWord ++ tailWord_968551).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968551).length < 2 ^ (prefixWord ++ tailWord_968551).sum := by decide
  have hdescent : baseEnd_968551 < baseStart_968551 := by decide
  rcases family_descends (prefixWord ++ tailWord_968551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968689 : List Nat := [1, 2, 2, 2, 5, 2, 7]
def baseStart_968689 : Nat := 118140960795 + 968689 * 2 ^ 59
def prefixEnd_968689 : Nat := 4983230072969 + 3 ^ 40 * 968689 * 2
def baseEnd_968689 : Nat := 24563114159173616470745

theorem tailTrace_968689 : CollatzResearch.WordTrace tailWord_968689 prefixEnd_968689 24563114159173616470745 := by
  unfold tailWord_968689
  simp only [CollatzResearch.WordTrace]
  refine ⟨35330990387612666755045121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23553993591741777836696747 35330990387612666755045121)
  ·
    refine ⟨26498242790709500066283841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35330990387612666755045121 26498242790709500066283841)
    ·
      refine ⟨19873682093032125049712881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26498242790709500066283841 19873682093032125049712881)
      ·
        refine ⟨14905261569774093787284661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19873682093032125049712881 14905261569774093787284661)
        ·
          refine ⟨1397368272166321292557937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14905261569774093787284661 1397368272166321292557937)
          ·
            refine ⟨1048026204124740969418453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1397368272166321292557937 1048026204124740969418453)
            ·
              refine ⟨24563114159173616470745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1048026204124740969418453 24563114159173616470745)
              ·
                rfl

theorem cell21_968689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 7].length) (baseStart_968689 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_968689 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_968689 prefixEnd_968689 := by exact prefixLift 968689
  have htrace : WordTrace (prefixWord ++ tailWord_968689) baseStart_968689 baseEnd_968689 := by
    simpa [prefixWord, tailWord_968689, baseEnd_968689] using wordTrace_append hprefix tailTrace_968689
  have hstable : (prefixWord ++ tailWord_968689).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968689).length < 2 ^ (prefixWord ++ tailWord_968689).sum := by decide
  have hdescent : baseEnd_968689 < baseStart_968689 := by decide
  rcases family_descends (prefixWord ++ tailWord_968689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968754 : List Nat := [3, 2, 1, 1, 2, 5, 2, 2, 3]
def baseStart_968754 : Nat := 118140960795 + 968754 * 2 ^ 59
def prefixEnd_968754 : Nat := 4983230072969 + 3 ^ 40 * 968754 * 2
def baseEnd_968754 : Nat := 221082861318136879653239

theorem tailTrace_968754 : CollatzResearch.WordTrace tailWord_968754 prefixEnd_968754 221082861318136879653239 := by
  unfold tailWord_968754
  simp only [CollatzResearch.WordTrace]
  refine ⟨8833340283094295714040329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23555574088251455237440877 8833340283094295714040329)
  ·
    refine ⟨6625005212320721785530247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8833340283094295714040329 6625005212320721785530247)
    ·
      refine ⟨9937507818481082678295371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6625005212320721785530247 9937507818481082678295371)
      ·
        refine ⟨14906261727721624017443057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9937507818481082678295371 14906261727721624017443057)
        ·
          refine ⟨11179696295791218013082293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14906261727721624017443057 11179696295791218013082293)
          ·
            refine ⟨1048096527730426688726465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11179696295791218013082293 1048096527730426688726465)
            ·
              refine ⟨786072395797820016544849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1048096527730426688726465 786072395797820016544849)
              ·
                refine ⟨589554296848365012408637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 786072395797820016544849 589554296848365012408637)
                ·
                  refine ⟨221082861318136879653239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 589554296848365012408637 221082861318136879653239)
                  ·
                    rfl

theorem cell21_968754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 2, 2, 3].length) (baseStart_968754 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_968754 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_968754 prefixEnd_968754 := by exact prefixLift 968754
  have htrace : WordTrace (prefixWord ++ tailWord_968754) baseStart_968754 baseEnd_968754 := by
    simpa [prefixWord, tailWord_968754, baseEnd_968754] using wordTrace_append hprefix tailTrace_968754
  have hstable : (prefixWord ++ tailWord_968754).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968754).length < 2 ^ (prefixWord ++ tailWord_968754).sum := by decide
  have hdescent : baseEnd_968754 < baseStart_968754 := by decide
  rcases family_descends (prefixWord ++ tailWord_968754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968793 : List Nat := [1, 2, 1, 2, 2, 1, 4, 2, 6]
def baseStart_968793 : Nat := 118140960795 + 968793 * 2 ^ 59
def prefixEnd_968793 : Nat := 4983230072969 + 3 ^ 40 * 968793 * 2
def baseEnd_968793 : Nat := 221091761649481478503159

theorem tailTrace_968793 : CollatzResearch.WordTrace tailWord_968793 prefixEnd_968793 221091761649481478503159 := by
  unfold tailWord_968793
  simp only [CollatzResearch.WordTrace]
  refine ⟨35334783579235892516831033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23556522386157261677887355 35334783579235892516831033)
  ·
    refine ⟨26501087684426919387623275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35334783579235892516831033 26501087684426919387623275)
    ·
      refine ⟨39751631526640379081434913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26501087684426919387623275 39751631526640379081434913)
      ·
        refine ⟨29813723644980284311076185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39751631526640379081434913 29813723644980284311076185)
        ·
          refine ⟨22360292733735213233307139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29813723644980284311076185 22360292733735213233307139)
          ·
            refine ⟨33540439100602819849960709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22360292733735213233307139 33540439100602819849960709)
            ·
              refine ⟨6288832331363028721867633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33540439100602819849960709 6288832331363028721867633)
              ·
                refine ⟨4716624248522271541400725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6288832331363028721867633 4716624248522271541400725)
                ·
                  refine ⟨221091761649481478503159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4716624248522271541400725 221091761649481478503159)
                  ·
                    rfl

theorem cell21_968793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 2, 6].length) (baseStart_968793 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_968793 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_968793 prefixEnd_968793 := by exact prefixLift 968793
  have htrace : WordTrace (prefixWord ++ tailWord_968793) baseStart_968793 baseEnd_968793 := by
    simpa [prefixWord, tailWord_968793, baseEnd_968793] using wordTrace_append hprefix tailTrace_968793
  have hstable : (prefixWord ++ tailWord_968793).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968793).length < 2 ^ (prefixWord ++ tailWord_968793).sum := by decide
  have hdescent : baseEnd_968793 < baseStart_968793 := by decide
  rcases family_descends (prefixWord ++ tailWord_968793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968858 : List Nat := [3, 1, 1, 5, 3, 1, 7]
def baseStart_968858 : Nat := 118140960795 + 968858 * 2 ^ 59
def prefixEnd_968858 : Nat := 4983230072969 + 3 ^ 40 * 968858 * 2
def baseEnd_968858 : Nat := 24567399503895089991077

theorem tailTrace_968858 : CollatzResearch.WordTrace tailWord_968858 prefixEnd_968858 24567399503895089991077 := by
  unfold tailWord_968858
  simp only [CollatzResearch.WordTrace]
  refine ⟨8834288581000102154486807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23558102882666939078631485 8834288581000102154486807)
  ·
    refine ⟨13251432871500153231730211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8834288581000102154486807 13251432871500153231730211)
    ·
      refine ⟨19877149307250229847595317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13251432871500153231730211 19877149307250229847595317)
      ·
        refine ⟨1863482747554709048212061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19877149307250229847595317 1863482747554709048212061)
        ·
          refine ⟨698806030333015893079523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1863482747554709048212061 698806030333015893079523)
          ·
            refine ⟨1048209045499523839619285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 698806030333015893079523 1048209045499523839619285)
            ·
              refine ⟨24567399503895089991077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1048209045499523839619285 24567399503895089991077)
              ·
                rfl

theorem cell21_968858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 7].length) (baseStart_968858 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_968858 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_968858 prefixEnd_968858 := by exact prefixLift 968858
  have htrace : WordTrace (prefixWord ++ tailWord_968858) baseStart_968858 baseEnd_968858 := by
    simpa [prefixWord, tailWord_968858, baseEnd_968858] using wordTrace_append hprefix tailTrace_968858
  have hstable : (prefixWord ++ tailWord_968858).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968858).length < 2 ^ (prefixWord ++ tailWord_968858).sum := by decide
  have hdescent : baseEnd_968858 < baseStart_968858 := by decide
  rcases family_descends (prefixWord ++ tailWord_968858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968869 : List Nat := [1, 3, 1, 2, 1, 3, 1, 3, 6]
def baseStart_968869 : Nat := 118140960795 + 968869 * 2 ^ 59
def prefixEnd_968869 : Nat := 4983230072969 + 3 ^ 40 * 968869 * 2
def baseEnd_968869 : Nat := 221109105884922235236337

theorem tailTrace_968869 : CollatzResearch.WordTrace tailWord_968869 prefixEnd_968869 221109105884922235236337 := by
  unfold tailWord_968869
  simp only [CollatzResearch.WordTrace]
  refine ⟨35337555526960557496597661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23558370351307038331065107 35337555526960557496597661)
  ·
    refine ⟨13251583322610209061224123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35337555526960557496597661 13251583322610209061224123)
    ·
      refine ⟨19877374983915313591836185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13251583322610209061224123 19877374983915313591836185)
      ·
        refine ⟨14908031237936485193877139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19877374983915313591836185 14908031237936485193877139)
        ·
          refine ⟨22362046856904727790815709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14908031237936485193877139 22362046856904727790815709)
          ·
            refine ⟨8385767571339272921555891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22362046856904727790815709 8385767571339272921555891)
            ·
              refine ⟨12578651357008909382333837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8385767571339272921555891 12578651357008909382333837)
              ·
                refine ⟨4716994258878341018375189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12578651357008909382333837 4716994258878341018375189)
                ·
                  refine ⟨221109105884922235236337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4716994258878341018375189 221109105884922235236337)
                  ·
                    rfl

theorem cell21_968869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 3, 6].length) (baseStart_968869 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_968869 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_968869 prefixEnd_968869 := by exact prefixLift 968869
  have htrace : WordTrace (prefixWord ++ tailWord_968869) baseStart_968869 baseEnd_968869 := by
    simpa [prefixWord, tailWord_968869, baseEnd_968869] using wordTrace_append hprefix tailTrace_968869
  have hstable : (prefixWord ++ tailWord_968869).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968869).length < 2 ^ (prefixWord ++ tailWord_968869).sum := by decide
  have hdescent : baseEnd_968869 < baseStart_968869 := by decide
  rcases family_descends (prefixWord ++ tailWord_968869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968878 : List Nat := [4, 1, 4, 2, 1, 2, 2, 1, 4]
def baseStart_968878 : Nat := 118140960795 + 968878 * 2 ^ 59
def prefixEnd_968878 : Nat := 4983230072969 + 3 ^ 40 * 968878 * 2
def baseEnd_968878 : Nat := 221111159807540219586319

theorem tailTrace_968878 : CollatzResearch.WordTrace tailWord_968878 prefixEnd_968878 221111159807540219586319 := by
  unfold tailWord_968878
  simp only [CollatzResearch.WordTrace]
  refine ⟨4417235472990994004209411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23558589189285301355783525 4417235472990994004209411)
  ·
    refine ⟨6625853209486491006314117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4417235472990994004209411 6625853209486491006314117)
    ·
      refine ⟨1242347476778717063683897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6625853209486491006314117 1242347476778717063683897)
      ·
        refine ⟨931760607584037797762923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1242347476778717063683897 931760607584037797762923)
        ·
          refine ⟨1397640911376056696644385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 931760607584037797762923 1397640911376056696644385)
          ·
            refine ⟨1048230683532042522483289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1397640911376056696644385 1048230683532042522483289)
            ·
              refine ⟨786173012649031891862467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1048230683532042522483289 786173012649031891862467)
              ·
                refine ⟨1179259518973547837793701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 786173012649031891862467 1179259518973547837793701)
                ·
                  refine ⟨221111159807540219586319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1179259518973547837793701 221111159807540219586319)
                  ·
                    rfl

theorem cell21_968878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 2, 1, 4].length) (baseStart_968878 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_968878 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_968878 prefixEnd_968878 := by exact prefixLift 968878
  have htrace : WordTrace (prefixWord ++ tailWord_968878) baseStart_968878 baseEnd_968878 := by
    simpa [prefixWord, tailWord_968878, baseEnd_968878] using wordTrace_append hprefix tailTrace_968878
  have hstable : (prefixWord ++ tailWord_968878).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968878).length < 2 ^ (prefixWord ++ tailWord_968878).sum := by decide
  have hdescent : baseEnd_968878 < baseStart_968878 := by decide
  rcases family_descends (prefixWord ++ tailWord_968878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968917 : List Nat := [1, 3, 2, 4, 3, 8]
def baseStart_968917 : Nat := 118140960795 + 968917 * 2 ^ 59
def prefixEnd_968917 : Nat := 4983230072969 + 3 ^ 40 * 968917 * 2
def baseEnd_968917 : Nat := 8189631856995734016157

theorem tailTrace_968917 : CollatzResearch.WordTrace tailWord_968917 prefixEnd_968917 8189631856995734016157 := by
  unfold tailWord_968917
  simp only [CollatzResearch.WordTrace]
  refine ⟨35339306230786661694345005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23559537487191107796230003 35339306230786661694345005)
  ·
    refine ⟨13252239836544998135379377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35339306230786661694345005 13252239836544998135379377)
    ·
      refine ⟨9939179877408748601534533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13252239836544998135379377 9939179877408748601534533)
      ·
        refine ⟨1863596227014140362787725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9939179877408748601534533 1863596227014140362787725)
        ·
          refine ⟨698848585130302636045397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1863596227014140362787725 698848585130302636045397)
          ·
            refine ⟨8189631856995734016157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 698848585130302636045397 8189631856995734016157)
            ·
              rfl

theorem cell21_968917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 8].length) (baseStart_968917 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_968917 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_968917 prefixEnd_968917 := by exact prefixLift 968917
  have htrace : WordTrace (prefixWord ++ tailWord_968917) baseStart_968917 baseEnd_968917 := by
    simpa [prefixWord, tailWord_968917, baseEnd_968917] using wordTrace_append hprefix tailTrace_968917
  have hstable : (prefixWord ++ tailWord_968917).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968917).length < 2 ^ (prefixWord ++ tailWord_968917).sum := by decide
  have hdescent : baseEnd_968917 < baseStart_968917 := by decide
  rcases family_descends (prefixWord ++ tailWord_968917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969010 : List Nat := [3, 2, 1, 1, 5, 2, 2, 5]
def baseStart_969010 : Nat := 118140960795 + 969010 * 2 ^ 59
def prefixEnd_969010 : Nat := 4983230072969 + 3 ^ 40 * 969010 * 2
def baseEnd_969010 : Nat := 73713761335312441128683

theorem tailTrace_969010 : CollatzResearch.WordTrace tailWord_969010 prefixEnd_969010 73713761335312441128683 := by
  unfold tailWord_969010
  simp only [CollatzResearch.WordTrace]
  refine ⟨8835674554862434644370121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23561798812966492384986989 8835674554862434644370121)
  ·
    refine ⟨6626755916146825983277591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8835674554862434644370121 6626755916146825983277591)
    ·
      refine ⟨9940133874220238974916387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6626755916146825983277591 9940133874220238974916387)
      ·
        refine ⟨14910200811330358462374581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9940133874220238974916387 14910200811330358462374581)
        ·
          refine ⟨1397831326062221105847617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14910200811330358462374581 1397831326062221105847617)
          ·
            refine ⟨1048373494546665829385713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1397831326062221105847617 1048373494546665829385713)
            ·
              refine ⟨786280120909999372039285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1048373494546665829385713 786280120909999372039285)
              ·
                refine ⟨73713761335312441128683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 786280120909999372039285 73713761335312441128683)
                ·
                  rfl

theorem cell21_969010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 2, 5].length) (baseStart_969010 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_969010 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_969010 prefixEnd_969010 := by exact prefixLift 969010
  have htrace : WordTrace (prefixWord ++ tailWord_969010) baseStart_969010 baseEnd_969010 := by
    simpa [prefixWord, tailWord_969010, baseEnd_969010] using wordTrace_append hprefix tailTrace_969010
  have hstable : (prefixWord ++ tailWord_969010).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969010).length < 2 ^ (prefixWord ++ tailWord_969010).sum := by decide
  have hdescent : baseEnd_969010 < baseStart_969010 := by decide
  rcases family_descends (prefixWord ++ tailWord_969010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969041 : List Nat := [1, 2, 2, 1, 4, 3, 3, 2, 3]
def baseStart_969041 : Nat := 118140960795 + 969041 * 2 ^ 59
def prefixEnd_969041 : Nat := 4983230072969 + 3 ^ 40 * 969041 * 2
def baseEnd_969041 : Nat := 221148358628288158369319

theorem tailTrace_969041 : CollatzResearch.WordTrace tailWord_969041 prefixEnd_969041 221148358628288158369319 := by
  unfold tailWord_969041
  simp only [CollatzResearch.WordTrace]
  refine ⟨35343828882337430871858977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23562552588224953914572651 35343828882337430871858977)
  ·
    refine ⟨26507871661753073153894233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35343828882337430871858977 26507871661753073153894233)
    ·
      refine ⟨19880903746314804865420675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26507871661753073153894233 19880903746314804865420675)
      ·
        refine ⟨29821355619472207298131013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19880903746314804865420675 29821355619472207298131013)
        ·
          refine ⟨5591504178651038868399565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29821355619472207298131013 5591504178651038868399565)
          ·
            refine ⟨2096814066994139575649837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5591504178651038868399565 2096814066994139575649837)
            ·
              refine ⟨786305275122802340868689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2096814066994139575649837 786305275122802340868689)
              ·
                refine ⟨589728956342101755651517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 786305275122802340868689 589728956342101755651517)
                ·
                  refine ⟨221148358628288158369319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 589728956342101755651517 221148358628288158369319)
                  ·
                    rfl

theorem cell21_969041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 3, 2, 3].length) (baseStart_969041 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_969041 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_969041 prefixEnd_969041 := by exact prefixLift 969041
  have htrace : WordTrace (prefixWord ++ tailWord_969041) baseStart_969041 baseEnd_969041 := by
    simpa [prefixWord, tailWord_969041, baseEnd_969041] using wordTrace_append hprefix tailTrace_969041
  have hstable : (prefixWord ++ tailWord_969041).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969041).length < 2 ^ (prefixWord ++ tailWord_969041).sum := by decide
  have hdescent : baseEnd_969041 < baseStart_969041 := by decide
  rcases family_descends (prefixWord ++ tailWord_969041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969100 : List Nat := [2, 2, 1, 2, 1, 5, 1, 4, 3]
def baseStart_969100 : Nat := 118140960795 + 969100 * 2 ^ 59
def prefixEnd_969100 : Nat := 4983230072969 + 3 ^ 40 * 969100 * 2
def baseEnd_969100 : Nat := 221161823232117166885865

theorem tailTrace_969100 : CollatzResearch.WordTrace tailWord_969100 prefixEnd_969100 221161823232117166885865 := by
  unfold tailWord_969100
  simp only [CollatzResearch.WordTrace]
  refine ⟨17672990394561841974128377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23563987192749122632171169 17672990394561841974128377)
  ·
    refine ⟨13254742795921381480596283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17672990394561841974128377 13254742795921381480596283)
    ·
      refine ⟨19882114193882072220894425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13254742795921381480596283 19882114193882072220894425)
      ·
        refine ⟨14911585645411554165670819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19882114193882072220894425 14911585645411554165670819)
        ·
          refine ⟨22367378468117331248506229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14911585645411554165670819 22367378468117331248506229)
          ·
            refine ⟨2096941731385999804547459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22367378468117331248506229 2096941731385999804547459)
            ·
              refine ⟨3145412597078999706821189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2096941731385999804547459 3145412597078999706821189)
              ·
                refine ⟨589764861952312445028973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3145412597078999706821189 589764861952312445028973)
                ·
                  refine ⟨221161823232117166885865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 589764861952312445028973 221161823232117166885865)
                  ·
                    rfl

theorem cell21_969100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 4, 3].length) (baseStart_969100 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_969100 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_969100 prefixEnd_969100 := by exact prefixLift 969100
  have htrace : WordTrace (prefixWord ++ tailWord_969100) baseStart_969100 baseEnd_969100 := by
    simpa [prefixWord, tailWord_969100, baseEnd_969100] using wordTrace_append hprefix tailTrace_969100
  have hstable : (prefixWord ++ tailWord_969100).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969100).length < 2 ^ (prefixWord ++ tailWord_969100).sum := by decide
  have hdescent : baseEnd_969100 < baseStart_969100 := by decide
  rcases family_descends (prefixWord ++ tailWord_969100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969114 : List Nat := [3, 1, 1, 4, 1, 2, 2, 3, 4]
def baseStart_969114 : Nat := 118140960795 + 969114 * 2 ^ 59
def prefixEnd_969114 : Nat := 4983230072969 + 3 ^ 40 * 969114 * 2
def baseEnd_969114 : Nat := 221165018222856253652503

theorem tailTrace_969114 : CollatzResearch.WordTrace tailWord_969114 prefixEnd_969114 221165018222856253652503 := by
  unfold tailWord_969114
  simp only [CollatzResearch.WordTrace]
  refine ⟨8836622852768241084816599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23564327607381976226177597 8836622852768241084816599)
  ·
    refine ⟨13254934279152361627224899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8836622852768241084816599 13254934279152361627224899)
    ·
      refine ⟨19882401418728542440837349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13254934279152361627224899 19882401418728542440837349)
      ·
        refine ⟨3727950266011601707657003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19882401418728542440837349 3727950266011601707657003)
        ·
          refine ⟨5591925399017402561485505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3727950266011601707657003 5591925399017402561485505)
          ·
            refine ⟨4193944049263051921114129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5591925399017402561485505 4193944049263051921114129)
            ·
              refine ⟨3145458036947288940835597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4193944049263051921114129 3145458036947288940835597)
              ·
                refine ⟨1179546763855233352813349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3145458036947288940835597 1179546763855233352813349)
                ·
                  refine ⟨221165018222856253652503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1179546763855233352813349 221165018222856253652503)
                  ·
                    rfl

theorem cell21_969114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 3, 4].length) (baseStart_969114 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_969114 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_969114 prefixEnd_969114 := by exact prefixLift 969114
  have htrace : WordTrace (prefixWord ++ tailWord_969114) baseStart_969114 baseEnd_969114 := by
    simpa [prefixWord, tailWord_969114, baseEnd_969114] using wordTrace_append hprefix tailTrace_969114
  have hstable : (prefixWord ++ tailWord_969114).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969114).length < 2 ^ (prefixWord ++ tailWord_969114).sum := by decide
  have hdescent : baseEnd_969114 < baseStart_969114 := by decide
  rcases family_descends (prefixWord ++ tailWord_969114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969159 : List Nat := [1, 1, 4, 1, 1, 5, 2, 1, 5]
def baseStart_969159 : Nat := 118140960795 + 969159 * 2 ^ 59
def prefixEnd_969159 : Nat := 4983230072969 + 3 ^ 40 * 969159 * 2
def baseEnd_969159 : Nat := 221175287835946175402411

theorem tailTrace_969159 : CollatzResearch.WordTrace tailWord_969159 prefixEnd_969159 221175287835946175402411 := by
  unfold tailWord_969159
  simp only [CollatzResearch.WordTrace]
  refine ⟨35348132695909937024654531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23565421797273291349769687 35348132695909937024654531)
  ·
    refine ⟨53022199043864905536981797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35348132695909937024654531 53022199043864905536981797)
    ·
      refine ⟨9941662320724669788184087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53022199043864905536981797 9941662320724669788184087)
      ·
        refine ⟨14912493481087004682276131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9941662320724669788184087 14912493481087004682276131)
        ·
          refine ⟨22368740221630507023414197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14912493481087004682276131 22368740221630507023414197)
          ·
            refine ⟨2097069395777860033445081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22368740221630507023414197 2097069395777860033445081)
            ·
              refine ⟨1572802046833395025083811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2097069395777860033445081 1572802046833395025083811)
              ·
                refine ⟨2359203070250092537625717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1572802046833395025083811 2359203070250092537625717)
                ·
                  refine ⟨221175287835946175402411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2359203070250092537625717 221175287835946175402411)
                  ·
                    rfl

theorem cell21_969159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 2, 1, 5].length) (baseStart_969159 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_969159 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_969159 prefixEnd_969159 := by exact prefixLift 969159
  have htrace : WordTrace (prefixWord ++ tailWord_969159) baseStart_969159 baseEnd_969159 := by
    simpa [prefixWord, tailWord_969159, baseEnd_969159] using wordTrace_append hprefix tailTrace_969159
  have hstable : (prefixWord ++ tailWord_969159).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969159).length < 2 ^ (prefixWord ++ tailWord_969159).sum := by decide
  have hdescent : baseEnd_969159 < baseStart_969159 := by decide
  rcases family_descends (prefixWord ++ tailWord_969159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969261 : List Nat := [1, 5, 4, 1, 2, 1, 2, 2, 3]
def baseStart_969261 : Nat := 118140960795 + 969261 * 2 ^ 59
def prefixEnd_969261 : Nat := 4983230072969 + 3 ^ 40 * 969261 * 2
def baseEnd_969261 : Nat := 221198565625616664702203

theorem tailTrace_969261 : CollatzResearch.WordTrace tailWord_969261 prefixEnd_969261 221198565625616664702203 := by
  unfold tailWord_969261
  simp only [CollatzResearch.WordTrace]
  refine ⟨35351852941540408444867637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23567901961026938963245091 35351852941540408444867637)
  ·
    refine ⟨3314236213269413291706341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35351852941540408444867637 3314236213269413291706341)
    ·
      refine ⟨621419289988014992194939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3314236213269413291706341 621419289988014992194939)
      ·
        refine ⟨932128934982022488292409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 621419289988014992194939 932128934982022488292409)
        ·
          refine ⟨699096701236516866219307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 932128934982022488292409 699096701236516866219307)
          ·
            refine ⟨1048645051854775299328961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 699096701236516866219307 1048645051854775299328961)
            ·
              refine ⟨786483788891081474496721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1048645051854775299328961 786483788891081474496721)
              ·
                refine ⟨589862841668311105872541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 786483788891081474496721 589862841668311105872541)
                ·
                  refine ⟨221198565625616664702203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 589862841668311105872541 221198565625616664702203)
                  ·
                    rfl

theorem cell21_969261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 2, 2, 3].length) (baseStart_969261 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_969261 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_969261 prefixEnd_969261 := by exact prefixLift 969261
  have htrace : WordTrace (prefixWord ++ tailWord_969261) baseStart_969261 baseEnd_969261 := by
    simpa [prefixWord, tailWord_969261, baseEnd_969261] using wordTrace_append hprefix tailTrace_969261
  have hstable : (prefixWord ++ tailWord_969261).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969261).length < 2 ^ (prefixWord ++ tailWord_969261).sum := by decide
  have hdescent : baseEnd_969261 < baseStart_969261 := by decide
  rcases family_descends (prefixWord ++ tailWord_969261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969294 : List Nat := [4, 1, 1, 1, 1, 2, 3, 1, 7]
def baseStart_969294 : Nat := 118140960795 + 969294 * 2 ^ 59
def prefixEnd_969294 : Nat := 4983230072969 + 3 ^ 40 * 969294 * 2
def baseEnd_969294 : Nat := 221206096675215940652135

theorem tailTrace_969294 : CollatzResearch.WordTrace tailWord_969294 prefixEnd_969294 221206096675215940652135 := by
  unfold tailWord_969294
  simp only [CollatzResearch.WordTrace]
  refine ⟨4419132068802606885102367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23568704366947236720545957 4419132068802606885102367)
  ·
    refine ⟨6628698103203910327653551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4419132068802606885102367 6628698103203910327653551)
    ·
      refine ⟨9943047154805865491480327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6628698103203910327653551 9943047154805865491480327)
      ·
        refine ⟨14914570732208798237220491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9943047154805865491480327 14914570732208798237220491)
        ·
          refine ⟨22371856098313197355830737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14914570732208798237220491 22371856098313197355830737)
          ·
            refine ⟨16778892073734898016873053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22371856098313197355830737 16778892073734898016873053)
            ·
              refine ⟨6292084527650586756327395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16778892073734898016873053 6292084527650586756327395)
              ·
                refine ⟨9438126791475880134491093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6292084527650586756327395 9438126791475880134491093)
                ·
                  refine ⟨221206096675215940652135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9438126791475880134491093 221206096675215940652135)
                  ·
                    rfl

theorem cell21_969294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 1, 7].length) (baseStart_969294 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_969294 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_969294 prefixEnd_969294 := by exact prefixLift 969294
  have htrace : WordTrace (prefixWord ++ tailWord_969294) baseStart_969294 baseEnd_969294 := by
    simpa [prefixWord, tailWord_969294, baseEnd_969294] using wordTrace_append hprefix tailTrace_969294
  have hstable : (prefixWord ++ tailWord_969294).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969294).length < 2 ^ (prefixWord ++ tailWord_969294).sum := by decide
  have hdescent : baseEnd_969294 < baseStart_969294 := by decide
  rcases family_descends (prefixWord ++ tailWord_969294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
