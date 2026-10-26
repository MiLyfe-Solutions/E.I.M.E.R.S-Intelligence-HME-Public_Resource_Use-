import V185TrunkScan23Chunk0981

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5813266 : List Nat := [3, 2, 5, 1, 1, 1, 2, 2, 1, 2, 3]
def baseStart_5813266 : Nat := 118140960795 + 5813266 * 2 ^ 59
def prefixEnd_5813266 : Nat := 4983230072969 + 3 ^ 40 * 5813266 * 2
def baseEnd_5813266 : Nat := 2984999630439957803740283

theorem tailTrace_5813266 : CollatzResearch.WordTrace tailWord_5813266 prefixEnd_5813266 2984999630439957803740283 := by
  unfold tailWord_5813266
  simp only [CollatzResearch.WordTrace]
  refine ⟨53006807439384395908732913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141351486505025055756621101 53006807439384395908732913)
  ·
    refine ⟨39755105579538296931549685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53006807439384395908732913 39755105579538296931549685)
    ·
      refine ⟨3727041148081715337332783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 39755105579538296931549685 3727041148081715337332783)
      ·
        refine ⟨5590561722122573005999175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3727041148081715337332783 5590561722122573005999175)
        ·
          refine ⟨8385842583183859508998763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5590561722122573005999175 8385842583183859508998763)
          ·
            refine ⟨12578763874775789263498145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8385842583183859508998763 12578763874775789263498145)
            ·
              refine ⟨9434072906081841947623609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12578763874775789263498145 9434072906081841947623609)
              ·
                refine ⟨7075554679561381460717707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9434072906081841947623609 7075554679561381460717707)
                ·
                  refine ⟨10613332019342072191076561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7075554679561381460717707 10613332019342072191076561)
                  ·
                    refine ⟨7959999014506554143307421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10613332019342072191076561 7959999014506554143307421)
                    ·
                      refine ⟨2984999630439957803740283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7959999014506554143307421 2984999630439957803740283)
                      ·
                        rfl

theorem cell23_5813266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_5813266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5813266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5813266 prefixEnd_5813266 := by exact prefixLift 5813266
  have htrace : WordTrace (prefixWord ++ tailWord_5813266) baseStart_5813266 baseEnd_5813266 := by
    simpa [prefixWord, tailWord_5813266, baseEnd_5813266] using wordTrace_append hprefix tailTrace_5813266
  have hstable : (prefixWord ++ tailWord_5813266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5813266).length < 2 ^ (prefixWord ++ tailWord_5813266).sum := by decide
  have hdescent : baseEnd_5813266 < baseStart_5813266 := by decide
  rcases family_descends (prefixWord ++ tailWord_5813266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5813272 : List Nat := [2, 1, 2, 3, 2, 3, 2, 2, 1, 3, 2]
def baseStart_5813272 : Nat := 118140960795 + 5813272 * 2 ^ 59
def prefixEnd_5813272 : Nat := 4983230072969 + 3 ^ 40 * 5813272 * 2
def baseEnd_5813272 : Nat := 2985002711323884780265255

theorem tailTrace_5813272 : CollatzResearch.WordTrace tailWord_5813272 prefixEnd_5813272 2985002711323884780265255 := by
  unfold tailWord_5813272
  simp only [CollatzResearch.WordTrace]
  refine ⟨106013724297757923329825035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141351632397010564439766713 106013724297757923329825035)
  ·
    refine ⟨159020586446636884994737553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106013724297757923329825035 159020586446636884994737553)
    ·
      refine ⟨119265439834977663746053165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159020586446636884994737553 119265439834977663746053165)
      ·
        refine ⟨44724539938116623904769937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119265439834977663746053165 44724539938116623904769937)
        ·
          refine ⟨33543404953587467928577453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44724539938116623904769937 33543404953587467928577453)
          ·
            refine ⟨12578776857595300473216545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33543404953587467928577453 12578776857595300473216545)
            ·
              refine ⟨9434082643196475354912409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12578776857595300473216545 9434082643196475354912409)
              ·
                refine ⟨7075561982397356516184307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9434082643196475354912409 7075561982397356516184307)
                ·
                  refine ⟨10613342973596034774276461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7075561982397356516184307 10613342973596034774276461)
                  ·
                    refine ⟨3980003615098513040353673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10613342973596034774276461 3980003615098513040353673)
                    ·
                      refine ⟨2985002711323884780265255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3980003615098513040353673 2985002711323884780265255)
                      ·
                        rfl

theorem cell23_5813272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 2, 2, 1, 3, 2].length) (baseStart_5813272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5813272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5813272 prefixEnd_5813272 := by exact prefixLift 5813272
  have htrace : WordTrace (prefixWord ++ tailWord_5813272) baseStart_5813272 baseEnd_5813272 := by
    simpa [prefixWord, tailWord_5813272, baseEnd_5813272] using wordTrace_append hprefix tailTrace_5813272
  have hstable : (prefixWord ++ tailWord_5813272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5813272).length < 2 ^ (prefixWord ++ tailWord_5813272).sum := by decide
  have hdescent : baseEnd_5813272 < baseStart_5813272 := by decide
  rcases family_descends (prefixWord ++ tailWord_5813272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5813285 : List Nat := [1, 3, 1, 2, 2, 2, 1, 1, 6, 2, 2]
def baseStart_5813285 : Nat := 118140960795 + 5813285 * 2 ^ 59
def prefixEnd_5813285 : Nat := 4983230072969 + 3 ^ 40 * 5813285 * 2
def baseEnd_5813285 : Nat := 2985009386572393229402695

theorem tailTrace_5813285 : CollatzResearch.WordTrace tailWord_5813285 prefixEnd_5813285 2985009386572393229402695 := by
  unfold tailWord_5813285
  simp only [CollatzResearch.WordTrace]
  refine ⟨212027922744468749879873309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141351948496312499919915539 212027922744468749879873309)
  ·
    refine ⟨79510471029175781204952491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 212027922744468749879873309 79510471029175781204952491)
    ·
      refine ⟨119265706543763671807428737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79510471029175781204952491 119265706543763671807428737)
      ·
        refine ⟨89449279907822753855571553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119265706543763671807428737 89449279907822753855571553)
        ·
          refine ⟨67086959930867065391678665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89449279907822753855571553 67086959930867065391678665)
          ·
            refine ⟨50315219948150299043758999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67086959930867065391678665 50315219948150299043758999)
            ·
              refine ⟨75472829922225448565638499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50315219948150299043758999 75472829922225448565638499)
              ·
                refine ⟨113209244883338172848457749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75472829922225448565638499 113209244883338172848457749)
                ·
                  refine ⟨5306683353906476852271457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 113209244883338172848457749 5306683353906476852271457)
                  ·
                    refine ⟨3980012515429857639203593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5306683353906476852271457 3980012515429857639203593)
                    ·
                      refine ⟨2985009386572393229402695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3980012515429857639203593 2985009386572393229402695)
                      ·
                        rfl

theorem cell23_5813285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 1, 6, 2, 2].length) (baseStart_5813285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5813285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5813285 prefixEnd_5813285 := by exact prefixLift 5813285
  have htrace : WordTrace (prefixWord ++ tailWord_5813285) baseStart_5813285 baseEnd_5813285 := by
    simpa [prefixWord, tailWord_5813285, baseEnd_5813285] using wordTrace_append hprefix tailTrace_5813285
  have hstable : (prefixWord ++ tailWord_5813285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5813285).length < 2 ^ (prefixWord ++ tailWord_5813285).sum := by decide
  have hdescent : baseEnd_5813285 < baseStart_5813285 := by decide
  rcases family_descends (prefixWord ++ tailWord_5813285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5813301 : List Nat := [1, 3, 3, 1, 1, 1, 1, 1, 1, 1, 9]
def baseStart_5813301 : Nat := 118140960795 + 5813301 * 2 ^ 59
def prefixEnd_5813301 : Nat := 4983230072969 + 3 ^ 40 * 5813301 * 2
def baseEnd_5813301 : Nat := 2985017602262865166802621

theorem tailTrace_5813301 : CollatzResearch.WordTrace tailWord_5813301 prefixEnd_5813301 2985017602262865166802621 := by
  unfold tailWord_5813301
  simp only [CollatzResearch.WordTrace]
  refine ⟨212028506312410784612455757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141352337541607189741637171 212028506312410784612455757)
  ·
    refine ⟨79510689867154044229670909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 212028506312410784612455757 79510689867154044229670909)
    ·
      refine ⟨29816508700182766586126591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79510689867154044229670909 29816508700182766586126591)
      ·
        refine ⟨44724763050274149879189887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29816508700182766586126591 44724763050274149879189887)
        ·
          refine ⟨67087144575411224818784831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44724763050274149879189887 67087144575411224818784831)
          ·
            refine ⟨100630716863116837228177247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67087144575411224818784831 100630716863116837228177247)
            ·
              refine ⟨150946075294675255842265871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100630716863116837228177247 150946075294675255842265871)
              ·
                refine ⟨226419112942012883763398807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 150946075294675255842265871 226419112942012883763398807)
                ·
                  refine ⟨339628669413019325645098211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 226419112942012883763398807 339628669413019325645098211)
                  ·
                    refine ⟨509443004119528988467647317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 339628669413019325645098211 509443004119528988467647317)
                    ·
                      refine ⟨2985017602262865166802621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 509443004119528988467647317 2985017602262865166802621)
                      ·
                        rfl

theorem cell23_5813301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 1, 9].length) (baseStart_5813301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5813301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5813301 prefixEnd_5813301 := by exact prefixLift 5813301
  have htrace : WordTrace (prefixWord ++ tailWord_5813301) baseStart_5813301 baseEnd_5813301 := by
    simpa [prefixWord, tailWord_5813301, baseEnd_5813301] using wordTrace_append hprefix tailTrace_5813301
  have hstable : (prefixWord ++ tailWord_5813301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5813301).length < 2 ^ (prefixWord ++ tailWord_5813301).sum := by decide
  have hdescent : baseEnd_5813301 < baseStart_5813301 := by decide
  rcases family_descends (prefixWord ++ tailWord_5813301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5813308 : List Nat := [2, 2, 2, 2, 2, 2, 3, 1, 7]
def baseStart_5813308 : Nat := 118140960795 + 5813308 * 2 ^ 59
def prefixEnd_5813308 : Nat := 4983230072969 + 3 ^ 40 * 5813308 * 2
def baseEnd_5813308 : Nat := 331669021847494071046121

theorem tailTrace_5813308 : CollatzResearch.WordTrace tailWord_5813308 prefixEnd_5813308 331669021847494071046121 := by
  unfold tailWord_5813308
  simp only [CollatzResearch.WordTrace]
  refine ⟨106014380811692712403980289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141352507748923616538640385 106014380811692712403980289)
  ·
    refine ⟨79510785608769534302985217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106014380811692712403980289 79510785608769534302985217)
    ·
      refine ⟨59633089206577150727238913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79510785608769534302985217 59633089206577150727238913)
      ·
        refine ⟨44724816904932863045429185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59633089206577150727238913 44724816904932863045429185)
        ·
          refine ⟨33543612678699647284071889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44724816904932863045429185 33543612678699647284071889)
          ·
            refine ⟨25157709509024735463053917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33543612678699647284071889 25157709509024735463053917)
            ·
              refine ⟨9434141065884275798645219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25157709509024735463053917 9434141065884275798645219)
              ·
                refine ⟨14151211598826413697967829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9434141065884275798645219 14151211598826413697967829)
                ·
                  refine ⟨331669021847494071046121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14151211598826413697967829 331669021847494071046121)
                  ·
                    rfl

theorem cell23_5813308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 3, 1, 7].length) (baseStart_5813308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5813308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5813308 prefixEnd_5813308 := by exact prefixLift 5813308
  have htrace : WordTrace (prefixWord ++ tailWord_5813308) baseStart_5813308 baseEnd_5813308 := by
    simpa [prefixWord, tailWord_5813308, baseEnd_5813308] using wordTrace_append hprefix tailTrace_5813308
  have hstable : (prefixWord ++ tailWord_5813308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5813308).length < 2 ^ (prefixWord ++ tailWord_5813308).sum := by decide
  have hdescent : baseEnd_5813308 < baseStart_5813308 := by decide
  rcases family_descends (prefixWord ++ tailWord_5813308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5813319 : List Nat := [1, 1, 4, 1, 3, 2, 4, 1, 2, 2, 2]
def baseStart_5813319 : Nat := 118140960795 + 5813319 * 2 ^ 59
def prefixEnd_5813319 : Nat := 4983230072969 + 3 ^ 40 * 5813319 * 2
def baseEnd_5813319 : Nat := 2985026844914646096377539

theorem tailTrace_5813319 : CollatzResearch.WordTrace tailWord_5813319 prefixEnd_5813319 2985026844914646096377539 := by
  unfold tailWord_5813319
  simp only [CollatzResearch.WordTrace]
  refine ⟨212029162826345573686611011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141352775217563715791074007 212029162826345573686611011)
  ·
    refine ⟨318043744239518360529916517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212029162826345573686611011 318043744239518360529916517)
    ·
      refine ⟨59633202044909692599359347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 318043744239518360529916517 59633202044909692599359347)
      ·
        refine ⟨89449803067364538899039021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59633202044909692599359347 89449803067364538899039021)
        ·
          refine ⟨33543676150261702087139633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89449803067364538899039021 33543676150261702087139633)
          ·
            refine ⟨25157757112696276565354725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33543676150261702087139633 25157757112696276565354725)
            ·
              refine ⟨4717079458630551856004011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25157757112696276565354725 4717079458630551856004011)
              ·
                refine ⟨7075619187945827784006017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4717079458630551856004011 7075619187945827784006017)
                ·
                  refine ⟨5306714390959370838004513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7075619187945827784006017 5306714390959370838004513)
                  ·
                    refine ⟨3980035793219528128503385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5306714390959370838004513 3980035793219528128503385)
                    ·
                      refine ⟨2985026844914646096377539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3980035793219528128503385 2985026844914646096377539)
                      ·
                        rfl

theorem cell23_5813319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 4, 1, 2, 2, 2].length) (baseStart_5813319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5813319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5813319 prefixEnd_5813319 := by exact prefixLift 5813319
  have htrace : WordTrace (prefixWord ++ tailWord_5813319) baseStart_5813319 baseEnd_5813319 := by
    simpa [prefixWord, tailWord_5813319, baseEnd_5813319] using wordTrace_append hprefix tailTrace_5813319
  have hstable : (prefixWord ++ tailWord_5813319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5813319).length < 2 ^ (prefixWord ++ tailWord_5813319).sum := by decide
  have hdescent : baseEnd_5813319 < baseStart_5813319 := by decide
  rcases family_descends (prefixWord ++ tailWord_5813319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5813321 : List Nat := [1, 2, 1, 1, 2, 2, 2, 4, 1, 7]
def baseStart_5813321 : Nat := 118140960795 + 5813321 * 2 ^ 59
def prefixEnd_5813321 : Nat := 4983230072969 + 3 ^ 40 * 5813321 * 2
def baseEnd_5813321 : Nat := 995009290625318362850843

theorem tailTrace_5813321 : CollatzResearch.WordTrace tailWord_5813321 prefixEnd_5813321 995009290625318362850843 := by
  unfold tailWord_5813321
  simp only [CollatzResearch.WordTrace]
  refine ⟨212029235772338328028183817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141352823848225552018789211 212029235772338328028183817)
  ·
    refine ⟨159021926829253746021137863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212029235772338328028183817 159021926829253746021137863)
    ·
      refine ⟨238532890243880619031706795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159021926829253746021137863 238532890243880619031706795)
      ·
        refine ⟨357799335365820928547560193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238532890243880619031706795 357799335365820928547560193)
        ·
          refine ⟨268349501524365696410670145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 357799335365820928547560193 268349501524365696410670145)
          ·
            refine ⟨201262126143274272308002609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 268349501524365696410670145 201262126143274272308002609)
            ·
              refine ⟨150946594607455704231001957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 201262126143274272308002609 150946594607455704231001957)
              ·
                refine ⟨28302486488897944543312867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 150946594607455704231001957 28302486488897944543312867)
                ·
                  refine ⟨42453729733346916814969301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28302486488897944543312867 42453729733346916814969301)
                  ·
                    refine ⟨995009290625318362850843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42453729733346916814969301 995009290625318362850843)
                    ·
                      rfl

theorem cell23_5813321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 4, 1, 7].length) (baseStart_5813321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5813321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5813321 prefixEnd_5813321 := by exact prefixLift 5813321
  have htrace : WordTrace (prefixWord ++ tailWord_5813321) baseStart_5813321 baseEnd_5813321 := by
    simpa [prefixWord, tailWord_5813321, baseEnd_5813321] using wordTrace_append hprefix tailTrace_5813321
  have hstable : (prefixWord ++ tailWord_5813321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5813321).length < 2 ^ (prefixWord ++ tailWord_5813321).sum := by decide
  have hdescent : baseEnd_5813321 < baseStart_5813321 := by decide
  rcases family_descends (prefixWord ++ tailWord_5813321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5813331 : List Nat := [1, 1, 1, 2, 1, 1, 2, 4, 3, 2, 5]
def baseStart_5813331 : Nat := 118140960795 + 5813331 * 2 ^ 59
def prefixEnd_5813331 : Nat := 4983230072969 + 3 ^ 40 * 5813331 * 2
def baseEnd_5813331 : Nat := 2985033006682500049427483

theorem tailTrace_5813331 : CollatzResearch.WordTrace tailWord_5813331 prefixEnd_5813331 2985033006682500049427483 := by
  unfold tailWord_5813331
  simp only [CollatzResearch.WordTrace]
  refine ⟨212029600502302099736047847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141353067001534733157365231 212029600502302099736047847)
  ·
    refine ⟨318044400753453149604071771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212029600502302099736047847 318044400753453149604071771)
    ·
      refine ⟨477066601130179724406107657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 318044400753453149604071771 477066601130179724406107657)
      ·
        refine ⟨357799950847634793304580743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 477066601130179724406107657 357799950847634793304580743)
        ·
          refine ⟨536699926271452189956871115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 357799950847634793304580743 536699926271452189956871115)
          ·
            refine ⟨805049889407178284935306673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 536699926271452189956871115 805049889407178284935306673)
            ·
              refine ⟨603787417055383713701480005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 805049889407178284935306673 603787417055383713701480005)
              ·
                refine ⟨113210140697884446319027501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 603787417055383713701480005 113210140697884446319027501)
                ·
                  refine ⟨42453802761706667369635313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 113210140697884446319027501 42453802761706667369635313)
                  ·
                    refine ⟨31840352071280000527226485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42453802761706667369635313 31840352071280000527226485)
                    ·
                      refine ⟨2985033006682500049427483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31840352071280000527226485 2985033006682500049427483)
                      ·
                        rfl

theorem cell23_5813331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 4, 3, 2, 5].length) (baseStart_5813331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5813331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5813331 prefixEnd_5813331 := by exact prefixLift 5813331
  have htrace : WordTrace (prefixWord ++ tailWord_5813331) baseStart_5813331 baseEnd_5813331 := by
    simpa [prefixWord, tailWord_5813331, baseEnd_5813331] using wordTrace_append hprefix tailTrace_5813331
  have hstable : (prefixWord ++ tailWord_5813331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5813331).length < 2 ^ (prefixWord ++ tailWord_5813331).sum := by decide
  have hdescent : baseEnd_5813331 < baseStart_5813331 := by decide
  rcases family_descends (prefixWord ++ tailWord_5813331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5813385 : List Nat := [1, 2, 1, 1, 4, 4, 1, 2, 3, 4]
def baseStart_5813385 : Nat := 118140960795 + 5813385 * 2 ^ 59
def prefixEnd_5813385 : Nat := 4983230072969 + 3 ^ 40 * 5813385 * 2
def baseEnd_5813385 : Nat := 995020244879280946050745

theorem tailTrace_5813385 : CollatzResearch.WordTrace tailWord_5813385 prefixEnd_5813385 995020244879280946050745 := by
  unfold tailWord_5813385
  simp only [CollatzResearch.WordTrace]
  refine ⟨212031570044106466958513609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141354380029404311305675739 212031570044106466958513609)
  ·
    refine ⟨159023677533079850218885207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212031570044106466958513609 159023677533079850218885207)
    ·
      refine ⟨238535516299619775328327811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159023677533079850218885207 238535516299619775328327811)
      ·
        refine ⟨357803274449429662992491717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238535516299619775328327811 357803274449429662992491717)
        ·
          refine ⟨67088113959268061811092197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 357803274449429662992491717 67088113959268061811092197)
          ·
            refine ⟨12579021367362761589579787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67088113959268061811092197 12579021367362761589579787)
            ·
              refine ⟨18868532051044142384369681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12579021367362761589579787 18868532051044142384369681)
              ·
                refine ⟨14151399038283106788277261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18868532051044142384369681 14151399038283106788277261)
                ·
                  refine ⟨5306774639356165045603973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14151399038283106788277261 5306774639356165045603973)
                  ·
                    refine ⟨995020244879280946050745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5306774639356165045603973 995020244879280946050745)
                    ·
                      rfl

theorem cell23_5813385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 2, 3, 4].length) (baseStart_5813385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5813385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5813385 prefixEnd_5813385 := by exact prefixLift 5813385
  have htrace : WordTrace (prefixWord ++ tailWord_5813385) baseStart_5813385 baseEnd_5813385 := by
    simpa [prefixWord, tailWord_5813385, baseEnd_5813385] using wordTrace_append hprefix tailTrace_5813385
  have hstable : (prefixWord ++ tailWord_5813385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5813385).length < 2 ^ (prefixWord ++ tailWord_5813385).sum := by decide
  have hdescent : baseEnd_5813385 < baseStart_5813385 := by decide
  rcases family_descends (prefixWord ++ tailWord_5813385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5813395 : List Nat := [1, 1, 1, 2, 1, 2, 7, 1, 2, 2, 3]
def baseStart_5813395 : Nat := 118140960795 + 5813395 * 2 ^ 59
def prefixEnd_5813395 : Nat := 4983230072969 + 3 ^ 40 * 5813395 * 2
def baseEnd_5813395 : Nat := 2985065869444387799027189

theorem tailTrace_5813395 : CollatzResearch.WordTrace tailWord_5813395 prefixEnd_5813395 2985065869444387799027189 := by
  unfold tailWord_5813395
  simp only [CollatzResearch.WordTrace]
  refine ⟨212031934774070238666377639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141354623182713492444251759 212031934774070238666377639)
  ·
    refine ⟨318047902161105357999566459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212031934774070238666377639 318047902161105357999566459)
    ·
      refine ⟨477071853241658036999349689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 318047902161105357999566459 477071853241658036999349689)
      ·
        refine ⟨357803889931243527749512267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 477071853241658036999349689 357803889931243527749512267)
        ·
          refine ⟨536705834896865291624268401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 357803889931243527749512267 536705834896865291624268401)
          ·
            refine ⟨402529376172648968718201301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 536705834896865291624268401 402529376172648968718201301)
            ·
              refine ⟨9434282254046460204332843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 402529376172648968718201301 9434282254046460204332843)
              ·
                refine ⟨14151423381069690306499265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9434282254046460204332843 14151423381069690306499265)
                ·
                  refine ⟨10613567535802267729874449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14151423381069690306499265 10613567535802267729874449)
                  ·
                    refine ⟨7960175651851700797405837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10613567535802267729874449 7960175651851700797405837)
                    ·
                      refine ⟨2985065869444387799027189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7960175651851700797405837 2985065869444387799027189)
                      ·
                        rfl

theorem cell23_5813395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 7, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 7, 1, 2, 2, 3].length) (baseStart_5813395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5813395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5813395 prefixEnd_5813395 := by exact prefixLift 5813395
  have htrace : WordTrace (prefixWord ++ tailWord_5813395) baseStart_5813395 baseEnd_5813395 := by
    simpa [prefixWord, tailWord_5813395, baseEnd_5813395] using wordTrace_append hprefix tailTrace_5813395
  have hstable : (prefixWord ++ tailWord_5813395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5813395).length < 2 ^ (prefixWord ++ tailWord_5813395).sum := by decide
  have hdescent : baseEnd_5813395 < baseStart_5813395 := by decide
  rcases family_descends (prefixWord ++ tailWord_5813395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5813415 : List Nat := [1, 1, 6, 2, 1, 2, 1, 1, 8]
def baseStart_5813415 : Nat := 118140960795 + 5813415 * 2 ^ 59
def prefixEnd_5813415 : Nat := 4983230072969 + 3 ^ 40 * 5813415 * 2
def baseEnd_5813415 : Nat := 331675126561941968975233

theorem tailTrace_5813415 : CollatzResearch.WordTrace tailWord_5813415 prefixEnd_5813415 331675126561941968975233 := by
  unfold tailWord_5813415
  simp only [CollatzResearch.WordTrace]
  refine ⟨212032664233997782082105699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141355109489331854721403799 212032664233997782082105699)
  ·
    refine ⟨318048996350996673123158549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212032664233997782082105699 318048996350996673123158549)
    ·
      refine ⟨14908546703952969052648057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 318048996350996673123158549 14908546703952969052648057)
      ·
        refine ⟨11181410027964726789486043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14908546703952969052648057 11181410027964726789486043)
        ·
          refine ⟨16772115041947090184229065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11181410027964726789486043 16772115041947090184229065)
          ·
            refine ⟨12579086281460317638171799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16772115041947090184229065 12579086281460317638171799)
            ·
              refine ⟨18868629422190476457257699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12579086281460317638171799 18868629422190476457257699)
              ·
                refine ⟨28302944133285714685886549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18868629422190476457257699 28302944133285714685886549)
                ·
                  refine ⟨331675126561941968975233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28302944133285714685886549 331675126561941968975233)
                  ·
                    rfl

theorem cell23_5813415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 1, 8].length) (baseStart_5813415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5813415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5813415 prefixEnd_5813415 := by exact prefixLift 5813415
  have htrace : WordTrace (prefixWord ++ tailWord_5813415) baseStart_5813415 baseEnd_5813415 := by
    simpa [prefixWord, tailWord_5813415, baseEnd_5813415] using wordTrace_append hprefix tailTrace_5813415
  have hstable : (prefixWord ++ tailWord_5813415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5813415).length < 2 ^ (prefixWord ++ tailWord_5813415).sum := by decide
  have hdescent : baseEnd_5813415 < baseStart_5813415 := by decide
  rcases family_descends (prefixWord ++ tailWord_5813415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5813435 : List Nat := [1, 1, 1, 1, 1, 2, 4, 1, 6, 3, 2]
def baseStart_5813435 : Nat := 118140960795 + 5813435 * 2 ^ 59
def prefixEnd_5813435 : Nat := 4983230072969 + 3 ^ 40 * 5813435 * 2
def baseEnd_5813435 : Nat := 2985086408670567642527005

theorem tailTrace_5813435 : CollatzResearch.WordTrace tailWord_5813435 prefixEnd_5813435 2985086408670567642527005 := by
  unfold tailWord_5813435
  simp only [CollatzResearch.WordTrace]
  refine ⟨212033393693925325497833759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141355595795950216998555839 212033393693925325497833759)
  ·
    refine ⟨318050090540887988246750639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212033393693925325497833759 318050090540887988246750639)
    ·
      refine ⟨477075135811331982370125959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 318050090540887988246750639 477075135811331982370125959)
      ·
        refine ⟨715612703716997973555188939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 477075135811331982370125959 715612703716997973555188939)
        ·
          refine ⟨1073419055575496960332783409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 715612703716997973555188939 1073419055575496960332783409)
          ·
            refine ⟨805064291681622720249587557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1073419055575496960332783409 805064291681622720249587557)
            ·
              refine ⟨150949554690304260046797667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 805064291681622720249587557 150949554690304260046797667)
              ·
                refine ⟨226424332035456390070196501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 150949554690304260046797667 226424332035456390070196501)
                ·
                  refine ⟨10613640564162018284540461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 226424332035456390070196501 10613640564162018284540461)
                  ·
                    refine ⟨3980115211560756856702673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10613640564162018284540461 3980115211560756856702673)
                    ·
                      refine ⟨2985086408670567642527005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3980115211560756856702673 2985086408670567642527005)
                      ·
                        rfl

theorem cell23_5813435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 6, 3, 2].length) (baseStart_5813435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5813435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5813435 prefixEnd_5813435 := by exact prefixLift 5813435
  have htrace : WordTrace (prefixWord ++ tailWord_5813435) baseStart_5813435 baseEnd_5813435 := by
    simpa [prefixWord, tailWord_5813435, baseEnd_5813435] using wordTrace_append hprefix tailTrace_5813435
  have hstable : (prefixWord ++ tailWord_5813435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5813435).length < 2 ^ (prefixWord ++ tailWord_5813435).sum := by decide
  have hdescent : baseEnd_5813435 < baseStart_5813435 := by decide
  rcases family_descends (prefixWord ++ tailWord_5813435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5813512 : List Nat := [2, 1, 3, 2, 4, 1, 1, 2, 1, 2, 4]
def baseStart_5813512 : Nat := 118140960795 + 5813512 * 2 ^ 59
def prefixEnd_5813512 : Nat := 4983230072969 + 3 ^ 40 * 5813512 * 2
def baseEnd_5813512 : Nat := 2985125946680963841264151

theorem tailTrace_5813512 : CollatzResearch.WordTrace tailWord_5813512 prefixEnd_5813512 2985125946680963841264151 := by
  unfold tailWord_5813512
  simp only [CollatzResearch.WordTrace]
  refine ⟨106018101057323183824193395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141357468076430911765591193 106018101057323183824193395)
  ·
    refine ⟨159027151585984775736290093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106018101057323183824193395 159027151585984775736290093)
    ·
      refine ⟨59635181844744290901108785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 159027151585984775736290093 59635181844744290901108785)
      ·
        refine ⟨44726386383558218175831589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59635181844744290901108785 44726386383558218175831589)
        ·
          refine ⟨8386197446917165907968423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44726386383558218175831589 8386197446917165907968423)
          ·
            refine ⟨12579296170375748861952635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8386197446917165907968423 12579296170375748861952635)
            ·
              refine ⟨18868944255563623292928953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12579296170375748861952635 18868944255563623292928953)
              ·
                refine ⟨14151708191672717469696715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18868944255563623292928953 14151708191672717469696715)
                ·
                  refine ⟨21227562287509076204545073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14151708191672717469696715 21227562287509076204545073)
                  ·
                    refine ⟨15920671715631807153408805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21227562287509076204545073 15920671715631807153408805)
                    ·
                      refine ⟨2985125946680963841264151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15920671715631807153408805 2985125946680963841264151)
                      ·
                        rfl

theorem cell23_5813512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 2, 1, 2, 4].length) (baseStart_5813512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5813512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5813512 prefixEnd_5813512 := by exact prefixLift 5813512
  have htrace : WordTrace (prefixWord ++ tailWord_5813512) baseStart_5813512 baseEnd_5813512 := by
    simpa [prefixWord, tailWord_5813512, baseEnd_5813512] using wordTrace_append hprefix tailTrace_5813512
  have hstable : (prefixWord ++ tailWord_5813512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5813512).length < 2 ^ (prefixWord ++ tailWord_5813512).sum := by decide
  have hdescent : baseEnd_5813512 < baseStart_5813512 := by decide
  rcases family_descends (prefixWord ++ tailWord_5813512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5813515 : List Nat := [1, 1, 1, 1, 5, 3, 1, 1, 3, 3, 3]
def baseStart_5813515 : Nat := 118140960795 + 5813515 * 2 ^ 59
def prefixEnd_5813515 : Nat := 4983230072969 + 3 ^ 40 * 5813515 * 2
def baseEnd_5813515 : Nat := 2985127487122927329526637

theorem tailTrace_5813515 : CollatzResearch.WordTrace tailWord_5813515 prefixEnd_5813515 2985127487122927329526637 := by
  unfold tailWord_5813515
  simp only [CollatzResearch.WordTrace]
  refine ⟨212036311533635499160745999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141357541022423666107163999 212036311533635499160745999)
  ·
    refine ⟨318054467300453248741118999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212036311533635499160745999 318054467300453248741118999)
    ·
      refine ⟨477081700950679873111678499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 318054467300453248741118999 477081700950679873111678499)
      ·
        refine ⟨715622551426019809667517749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 477081700950679873111678499 715622551426019809667517749)
        ·
          refine ⟨67089614196189357156329789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 715622551426019809667517749 67089614196189357156329789)
          ·
            refine ⟨25158605323571008933623671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67089614196189357156329789 25158605323571008933623671)
            ·
              refine ⟨37737907985356513400435507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25158605323571008933623671 37737907985356513400435507)
              ·
                refine ⟨56606861978034770100653261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37737907985356513400435507 56606861978034770100653261)
                ·
                  refine ⟨21227573241763038787744973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56606861978034770100653261 21227573241763038787744973)
                  ·
                    refine ⟨7960339965661139545404365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21227573241763038787744973 7960339965661139545404365)
                    ·
                      refine ⟨2985127487122927329526637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7960339965661139545404365 2985127487122927329526637)
                      ·
                        rfl

theorem cell23_5813515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 1, 3, 3, 3].length) (baseStart_5813515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5813515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5813515 prefixEnd_5813515 := by exact prefixLift 5813515
  have htrace : WordTrace (prefixWord ++ tailWord_5813515) baseStart_5813515 baseEnd_5813515 := by
    simpa [prefixWord, tailWord_5813515, baseEnd_5813515] using wordTrace_append hprefix tailTrace_5813515
  have hstable : (prefixWord ++ tailWord_5813515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5813515).length < 2 ^ (prefixWord ++ tailWord_5813515).sum := by decide
  have hdescent : baseEnd_5813515 < baseStart_5813515 := by decide
  rcases family_descends (prefixWord ++ tailWord_5813515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5813522 : List Nat := [3, 2, 4, 2, 1, 11]
def baseStart_5813522 : Nat := 118140960795 + 5813522 * 2 ^ 59
def prefixEnd_5813522 : Nat := 4983230072969 + 3 ^ 40 * 5813522 * 2
def baseEnd_5813522 : Nat := 12284490047273698774235

theorem tailTrace_5813522 : CollatzResearch.WordTrace tailWord_5813522 prefixEnd_5813522 12284490047273698774235 := by
  unfold tailWord_5813522
  simp only [CollatzResearch.WordTrace]
  refine ⟨53009141711152534839062705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141357711229740092904167213 53009141711152534839062705)
  ·
    refine ⟨39756856283364401129297029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53009141711152534839062705 39756856283364401129297029)
    ·
      refine ⟨7454410553130825211743193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39756856283364401129297029 7454410553130825211743193)
      ·
        refine ⟨5590807914848118908807395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7454410553130825211743193 5590807914848118908807395)
        ·
          refine ⟨8386211872272178363211093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5590807914848118908807395 8386211872272178363211093)
          ·
            refine ⟨12284490047273698774235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 8386211872272178363211093 12284490047273698774235)
            ·
              rfl

theorem cell23_5813522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 11].length) (baseStart_5813522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5813522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5813522 prefixEnd_5813522 := by exact prefixLift 5813522
  have htrace : WordTrace (prefixWord ++ tailWord_5813522) baseStart_5813522 baseEnd_5813522 := by
    simpa [prefixWord, tailWord_5813522, baseEnd_5813522] using wordTrace_append hprefix tailTrace_5813522
  have hstable : (prefixWord ++ tailWord_5813522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5813522).length < 2 ^ (prefixWord ++ tailWord_5813522).sum := by decide
  have hdescent : baseEnd_5813522 < baseStart_5813522 := by decide
  rcases family_descends (prefixWord ++ tailWord_5813522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5813532 : List Nat := [2, 2, 3, 1, 1, 1, 2, 3, 4, 1, 3]
def baseStart_5813532 : Nat := 118140960795 + 5813532 * 2 ^ 59
def prefixEnd_5813532 : Nat := 4983230072969 + 3 ^ 40 * 5813532 * 2
def baseEnd_5813532 : Nat := 2985136216294053763014059

theorem tailTrace_5813532 : CollatzResearch.WordTrace tailWord_5813532 prefixEnd_5813532 2985136216294053763014059 := by
  unfold tailWord_5813532
  simp only [CollatzResearch.WordTrace]
  refine ⟨106018465787286955532057425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141357954383049274042743233 106018465787286955532057425)
  ·
    refine ⟨79513849340465216649043069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106018465787286955532057425 79513849340465216649043069)
    ·
      refine ⟨29817693502674456243391151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79513849340465216649043069 29817693502674456243391151)
      ·
        refine ⟨44726540254011684365086727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29817693502674456243391151 44726540254011684365086727)
        ·
          refine ⟨67089810381017526547630091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44726540254011684365086727 67089810381017526547630091)
          ·
            refine ⟨100634715571526289821445137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67089810381017526547630091 100634715571526289821445137)
            ·
              refine ⟨75476036678644717366083853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100634715571526289821445137 75476036678644717366083853)
              ·
                refine ⟨28303513754491769012281445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75476036678644717366083853 28303513754491769012281445)
                ·
                  refine ⟨5306908828967206689802771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28303513754491769012281445 5306908828967206689802771)
                  ·
                    refine ⟨7960363243450810034704157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5306908828967206689802771 7960363243450810034704157)
                    ·
                      refine ⟨2985136216294053763014059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7960363243450810034704157 2985136216294053763014059)
                      ·
                        rfl

theorem cell23_5813532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 3, 4, 1, 3].length) (baseStart_5813532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5813532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5813532 prefixEnd_5813532 := by exact prefixLift 5813532
  have htrace : WordTrace (prefixWord ++ tailWord_5813532) baseStart_5813532 baseEnd_5813532 := by
    simpa [prefixWord, tailWord_5813532, baseEnd_5813532] using wordTrace_append hprefix tailTrace_5813532
  have hstable : (prefixWord ++ tailWord_5813532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5813532).length < 2 ^ (prefixWord ++ tailWord_5813532).sum := by decide
  have hdescent : baseEnd_5813532 < baseStart_5813532 := by decide
  rcases family_descends (prefixWord ++ tailWord_5813532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5813533 : List Nat := [1, 4, 2, 3, 1, 2, 1, 4, 1, 2, 2]
def baseStart_5813533 : Nat := 118140960795 + 5813533 * 2 ^ 59
def prefixEnd_5813533 : Nat := 4983230072969 + 3 ^ 40 * 5813533 * 2
def baseEnd_5813533 : Nat := 2985136729774708259101555

theorem tailTrace_5813533 : CollatzResearch.WordTrace tailWord_5813533 prefixEnd_5813533 2985136729774708259101555 := by
  unfold tailWord_5813533
  simp only [CollatzResearch.WordTrace]
  refine ⟨212036968047570288234901253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141357978698380192156600835 212036968047570288234901253)
  ·
    refine ⟨39756931508919429044043985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 212036968047570288234901253 39756931508919429044043985)
    ·
      refine ⟨29817698631689571783032989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39756931508919429044043985 29817698631689571783032989)
      ·
        refine ⟨11181636986883589418637371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29817698631689571783032989 11181636986883589418637371)
        ·
          refine ⟨16772455480325384127956057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11181636986883589418637371 16772455480325384127956057)
          ·
            refine ⟨12579341610244038095967043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16772455480325384127956057 12579341610244038095967043)
            ·
              refine ⟨18869012415366057143950565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12579341610244038095967043 18869012415366057143950565)
              ·
                refine ⟨3537939827881135714490731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18869012415366057143950565 3537939827881135714490731)
                ·
                  refine ⟨5306909741821703571736097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3537939827881135714490731 5306909741821703571736097)
                  ·
                    refine ⟨3980182306366277678802073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5306909741821703571736097 3980182306366277678802073)
                    ·
                      refine ⟨2985136729774708259101555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3980182306366277678802073 2985136729774708259101555)
                      ·
                        rfl

theorem cell23_5813533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 4, 1, 2, 2].length) (baseStart_5813533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5813533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5813533 prefixEnd_5813533 := by exact prefixLift 5813533
  have htrace : WordTrace (prefixWord ++ tailWord_5813533) baseStart_5813533 baseEnd_5813533 := by
    simpa [prefixWord, tailWord_5813533, baseEnd_5813533] using wordTrace_append hprefix tailTrace_5813533
  have hstable : (prefixWord ++ tailWord_5813533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5813533).length < 2 ^ (prefixWord ++ tailWord_5813533).sum := by decide
  have hdescent : baseEnd_5813533 < baseStart_5813533 := by decide
  rcases family_descends (prefixWord ++ tailWord_5813533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5813549 : List Nat := [1, 5, 3, 1, 1, 1, 1, 3, 1, 3, 3]
def baseStart_5813549 : Nat := 118140960795 + 5813549 * 2 ^ 59
def prefixEnd_5813549 : Nat := 4983230072969 + 3 ^ 40 * 5813549 * 2
def baseEnd_5813549 : Nat := 2985144945465180196501481

theorem tailTrace_5813549 : CollatzResearch.WordTrace tailWord_5813549 prefixEnd_5813549 2985144945465180196501481 := by
  unfold tailWord_5813549
  simp only [CollatzResearch.WordTrace]
  refine ⟨212037551615512322967483701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141358367743674881978322467 212037551615512322967483701)
  ·
    refine ⟨19878520463954280278201597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 212037551615512322967483701 19878520463954280278201597)
    ·
      refine ⟨7454445173982855104325599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19878520463954280278201597 7454445173982855104325599)
      ·
        refine ⟨11181667760974282656488399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7454445173982855104325599 11181667760974282656488399)
        ·
          refine ⟨16772501641461423984732599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11181667760974282656488399 16772501641461423984732599)
          ·
            refine ⟨25158752462192135977098899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16772501641461423984732599 25158752462192135977098899)
            ·
              refine ⟨37738128693288203965648349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25158752462192135977098899 37738128693288203965648349)
              ·
                refine ⟨14151798259983076487118131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37738128693288203965648349 14151798259983076487118131)
                ·
                  refine ⟨21227697389974614730677197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14151798259983076487118131 21227697389974614730677197)
                  ·
                    refine ⟨7960386521240480524003949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21227697389974614730677197 7960386521240480524003949)
                    ·
                      refine ⟨2985144945465180196501481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7960386521240480524003949 2985144945465180196501481)
                      ·
                        rfl

theorem cell23_5813549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_5813549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5813549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5813549 prefixEnd_5813549 := by exact prefixLift 5813549
  have htrace : WordTrace (prefixWord ++ tailWord_5813549) baseStart_5813549 baseEnd_5813549 := by
    simpa [prefixWord, tailWord_5813549, baseEnd_5813549] using wordTrace_append hprefix tailTrace_5813549
  have hstable : (prefixWord ++ tailWord_5813549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5813549).length < 2 ^ (prefixWord ++ tailWord_5813549).sum := by decide
  have hdescent : baseEnd_5813549 < baseStart_5813549 := by decide
  rcases family_descends (prefixWord ++ tailWord_5813549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5813585 : List Nat := [1, 2, 2, 1, 4, 1, 1, 1, 4, 2, 4]
def baseStart_5813585 : Nat := 118140960795 + 5813585 * 2 ^ 59
def prefixEnd_5813585 : Nat := 4983230072969 + 3 ^ 40 * 5813585 * 2
def baseEnd_5813585 : Nat := 2985163430768742055651315

theorem tailTrace_5813585 : CollatzResearch.WordTrace tailWord_5813585 prefixEnd_5813585 2985163430768742055651315 := by
  unfold tailWord_5813585
  simp only [CollatzResearch.WordTrace]
  refine ⟨212038864643381901115794209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141359243095587934077196139 212038864643381901115794209)
  ·
    refine ⟨159029148482536425836845657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212038864643381901115794209 159029148482536425836845657)
    ·
      refine ⟨119271861361902319377634243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159029148482536425836845657 119271861361902319377634243)
      ·
        refine ⟨178907792042853479066451365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119271861361902319377634243 178907792042853479066451365)
        ·
          refine ⟨33545211008035027324959631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 178907792042853479066451365 33545211008035027324959631)
          ·
            refine ⟨50317816512052540987439447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33545211008035027324959631 50317816512052540987439447)
            ·
              refine ⟨75476724768078811481159171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50317816512052540987439447 75476724768078811481159171)
              ·
                refine ⟨113215087152118217221738757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75476724768078811481159171 113215087152118217221738757)
                ·
                  refine ⟨21227828841022165729076017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 113215087152118217221738757 21227828841022165729076017)
                  ·
                    refine ⟨15920871630766624296807013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21227828841022165729076017 15920871630766624296807013)
                    ·
                      refine ⟨2985163430768742055651315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15920871630766624296807013 2985163430768742055651315)
                      ·
                        rfl

theorem cell23_5813585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 1, 4, 2, 4].length) (baseStart_5813585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5813585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5813585 prefixEnd_5813585 := by exact prefixLift 5813585
  have htrace : WordTrace (prefixWord ++ tailWord_5813585) baseStart_5813585 baseEnd_5813585 := by
    simpa [prefixWord, tailWord_5813585, baseEnd_5813585] using wordTrace_append hprefix tailTrace_5813585
  have hstable : (prefixWord ++ tailWord_5813585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5813585).length < 2 ^ (prefixWord ++ tailWord_5813585).sum := by decide
  have hdescent : baseEnd_5813585 < baseStart_5813585 := by decide
  rcases family_descends (prefixWord ++ tailWord_5813585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5813602 : List Nat := [3, 3, 2, 1, 1, 1, 1, 3, 2, 2, 4]
def baseStart_5813602 : Nat := 118140960795 + 5813602 * 2 ^ 59
def prefixEnd_5813602 : Nat := 4983230072969 + 3 ^ 40 * 5813602 * 2
def baseEnd_5813602 : Nat := 2985172159939868489138737

theorem tailTrace_5813602 : CollatzResearch.WordTrace tailWord_5813602 prefixEnd_5813602 2985172159939868489138737 := by
  unfold tailWord_5813602
  simp only [CollatzResearch.WordTrace]
  refine ⟨53009871171080078254790765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141359656456213542012775373 53009871171080078254790765)
  ·
    refine ⟨19878701689155029345546537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53009871171080078254790765 19878701689155029345546537)
    ·
      refine ⟨14909026266866272009159903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19878701689155029345546537 14909026266866272009159903)
      ·
        refine ⟨22363539400299408013739855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14909026266866272009159903 22363539400299408013739855)
        ·
          refine ⟨33545309100449112020609783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22363539400299408013739855 33545309100449112020609783)
          ·
            refine ⟨50317963650673668030914675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33545309100449112020609783 50317963650673668030914675)
            ·
              refine ⟨75476945476010502046372013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50317963650673668030914675 75476945476010502046372013)
              ·
                refine ⟨28303854553503938267389505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75476945476010502046372013 28303854553503938267389505)
                ·
                  refine ⟨21227890915127953700542129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28303854553503938267389505 21227890915127953700542129)
                  ·
                    refine ⟨15920918186345965275406597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21227890915127953700542129 15920918186345965275406597)
                    ·
                      refine ⟨2985172159939868489138737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15920918186345965275406597 2985172159939868489138737)
                      ·
                        rfl

theorem cell23_5813602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_5813602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5813602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5813602 prefixEnd_5813602 := by exact prefixLift 5813602
  have htrace : WordTrace (prefixWord ++ tailWord_5813602) baseStart_5813602 baseEnd_5813602 := by
    simpa [prefixWord, tailWord_5813602, baseEnd_5813602] using wordTrace_append hprefix tailTrace_5813602
  have hstable : (prefixWord ++ tailWord_5813602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5813602).length < 2 ^ (prefixWord ++ tailWord_5813602).sum := by decide
  have hdescent : baseEnd_5813602 < baseStart_5813602 := by decide
  rcases family_descends (prefixWord ++ tailWord_5813602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5813625 : List Nat := [1, 2, 1, 3, 2, 1, 4, 1, 1, 7]
def baseStart_5813625 : Nat := 118140960795 + 5813625 * 2 ^ 59
def prefixEnd_5813625 : Nat := 4983230072969 + 3 ^ 40 * 5813625 * 2
def baseEnd_5813625 : Nat := 995061323331640633050377

theorem tailTrace_5813625 : CollatzResearch.WordTrace tailWord_5813625 prefixEnd_5813625 995061323331640633050377 := by
  unfold tailWord_5813625
  simp only [CollatzResearch.WordTrace]
  refine ⟨212040323563236987947250329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141360215708824658631500219 212040323563236987947250329)
  ·
    refine ⟨159030242672427740960437747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212040323563236987947250329 159030242672427740960437747)
    ·
      refine ⟨238545364008641611440656621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159030242672427740960437747 238545364008641611440656621)
      ·
        refine ⟨89454511503240604290246233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 238545364008641611440656621 89454511503240604290246233)
        ·
          refine ⟨67090883627430453217684675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89454511503240604290246233 67090883627430453217684675)
          ·
            refine ⟨100636325441145679826527013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67090883627430453217684675 100636325441145679826527013)
            ·
              refine ⟨18869311020214814967473815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 100636325441145679826527013 18869311020214814967473815)
              ·
                refine ⟨28303966530322222451210723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18869311020214814967473815 28303966530322222451210723)
                ·
                  refine ⟨42455949795483333676816085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28303966530322222451210723 42455949795483333676816085)
                  ·
                    refine ⟨995061323331640633050377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42455949795483333676816085 995061323331640633050377)
                    ·
                      rfl

theorem cell23_5813625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 1, 1, 7].length) (baseStart_5813625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5813625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5813625 prefixEnd_5813625 := by exact prefixLift 5813625
  have htrace : WordTrace (prefixWord ++ tailWord_5813625) baseStart_5813625 baseEnd_5813625 := by
    simpa [prefixWord, tailWord_5813625, baseEnd_5813625] using wordTrace_append hprefix tailTrace_5813625
  have hstable : (prefixWord ++ tailWord_5813625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5813625).length < 2 ^ (prefixWord ++ tailWord_5813625).sum := by decide
  have hdescent : baseEnd_5813625 < baseStart_5813625 := by decide
  rcases family_descends (prefixWord ++ tailWord_5813625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5813646 : List Nat := [4, 1, 1, 4, 3, 1, 1, 1, 7]
def baseStart_5813646 : Nat := 118140960795 + 5813646 * 2 ^ 59
def prefixEnd_5813646 : Nat := 4983230072969 + 3 ^ 40 * 5813646 * 2
def baseEnd_5813646 : Nat := 331688305898740701887615

theorem tailTrace_5813646 : CollatzResearch.WordTrace tailWord_5813646 prefixEnd_5813646 331688305898740701887615 := by
  unfold tailWord_5813646
  simp only [CollatzResearch.WordTrace]
  refine ⟨26505136187020113566720599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 141360726330773939022509861 26505136187020113566720599)
  ·
    refine ⟨39757704280530170350080899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26505136187020113566720599 39757704280530170350080899)
    ·
      refine ⟨59636556420795255525121349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39757704280530170350080899 59636556420795255525121349)
      ·
        refine ⟨11181854328899110410960253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59636556420795255525121349 11181854328899110410960253)
        ·
          refine ⟨4193195373337166404110095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11181854328899110410960253 4193195373337166404110095)
          ·
            refine ⟨6289793060005749606165143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4193195373337166404110095 6289793060005749606165143)
            ·
              refine ⟨9434689590008624409247715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6289793060005749606165143 9434689590008624409247715)
              ·
                refine ⟨14152034385012936613871573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9434689590008624409247715 14152034385012936613871573)
                ·
                  refine ⟨331688305898740701887615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14152034385012936613871573 331688305898740701887615)
                  ·
                    rfl

theorem cell23_5813646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 1, 1, 7].length) (baseStart_5813646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5813646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5813646 prefixEnd_5813646 := by exact prefixLift 5813646
  have htrace : WordTrace (prefixWord ++ tailWord_5813646) baseStart_5813646 baseEnd_5813646 := by
    simpa [prefixWord, tailWord_5813646, baseEnd_5813646] using wordTrace_append hprefix tailTrace_5813646
  have hstable : (prefixWord ++ tailWord_5813646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5813646).length < 2 ^ (prefixWord ++ tailWord_5813646).sum := by decide
  have hdescent : baseEnd_5813646 < baseStart_5813646 := by decide
  rcases family_descends (prefixWord ++ tailWord_5813646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5813652 : List Nat := [2, 4, 2, 1, 2, 1, 1, 1, 1, 1, 7]
def baseStart_5813652 : Nat := 118140960795 + 5813652 * 2 ^ 59
def prefixEnd_5813652 : Nat := 4983230072969 + 3 ^ 40 * 5813652 * 2
def baseEnd_5813652 : Nat := 2985197833972593293513507

theorem tailTrace_5813652 : CollatzResearch.WordTrace tailWord_5813652 prefixEnd_5813652 2985197833972593293513507 := by
  unfold tailWord_5813652
  simp only [CollatzResearch.WordTrace]
  refine ⟨106020654167069585779241605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141360872222759447705655473 106020654167069585779241605)
  ·
    refine ⟨19878872656325547333607801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 106020654167069585779241605 19878872656325547333607801)
    ·
      refine ⟨14909154492244160500205851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19878872656325547333607801 14909154492244160500205851)
      ·
        refine ⟨22363731738366240750308777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14909154492244160500205851 22363731738366240750308777)
        ·
          refine ⟨16772798803774680562731583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22363731738366240750308777 16772798803774680562731583)
          ·
            refine ⟨25159198205662020844097375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16772798803774680562731583 25159198205662020844097375)
            ·
              refine ⟨37738797308493031266146063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25159198205662020844097375 37738797308493031266146063)
              ·
                refine ⟨56608195962739546899219095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37738797308493031266146063 56608195962739546899219095)
                ·
                  refine ⟨84912293944109320348828643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56608195962739546899219095 84912293944109320348828643)
                  ·
                    refine ⟨127368440916163980523242965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 84912293944109320348828643 127368440916163980523242965)
                    ·
                      refine ⟨2985197833972593293513507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 127368440916163980523242965 2985197833972593293513507)
                      ·
                        rfl

theorem cell23_5813652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_5813652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5813652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5813652 prefixEnd_5813652 := by exact prefixLift 5813652
  have htrace : WordTrace (prefixWord ++ tailWord_5813652) baseStart_5813652 baseEnd_5813652 := by
    simpa [prefixWord, tailWord_5813652, baseEnd_5813652] using wordTrace_append hprefix tailTrace_5813652
  have hstable : (prefixWord ++ tailWord_5813652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5813652).length < 2 ^ (prefixWord ++ tailWord_5813652).sum := by decide
  have hdescent : baseEnd_5813652 < baseStart_5813652 := by decide
  rcases family_descends (prefixWord ++ tailWord_5813652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5813705 : List Nat := [1, 2, 1, 1, 2, 1, 3, 3, 1, 2, 6]
def baseStart_5813705 : Nat := 118140960795 + 5813705 * 2 ^ 59
def prefixEnd_5813705 : Nat := 4983230072969 + 3 ^ 40 * 5813705 * 2
def baseEnd_5813705 : Nat := 2985225048447281586150763

theorem tailTrace_5813705 : CollatzResearch.WordTrace tailWord_5813705 prefixEnd_5813705 2985225048447281586150763 := by
  unfold tailWord_5813705
  simp only [CollatzResearch.WordTrace]
  refine ⟨212043241402947161610162569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141362160935298107740108379 212043241402947161610162569)
  ·
    refine ⟨159032431052210371207621927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212043241402947161610162569 159032431052210371207621927)
    ·
      refine ⟨238548646578315556811432891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159032431052210371207621927 238548646578315556811432891)
      ·
        refine ⟨357822969867473335217149337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238548646578315556811432891 357822969867473335217149337)
        ·
          refine ⟨268367227400605001412862003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 357822969867473335217149337 268367227400605001412862003)
          ·
            refine ⟨402550841100907502119293005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 268367227400605001412862003 402550841100907502119293005)
            ·
              refine ⟨150956565412840313294734877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 402550841100907502119293005 150956565412840313294734877)
              ·
                refine ⟨56608712029815117485525579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 150956565412840313294734877 56608712029815117485525579)
                ·
                  refine ⟨84913068044722676228288369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56608712029815117485525579 84913068044722676228288369)
                  ·
                    refine ⟨63684801033542007171216277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 84913068044722676228288369 63684801033542007171216277)
                    ·
                      refine ⟨2985225048447281586150763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63684801033542007171216277 2985225048447281586150763)
                      ·
                        rfl

theorem cell23_5813705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 3, 1, 2, 6].length) (baseStart_5813705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5813705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5813705 prefixEnd_5813705 := by exact prefixLift 5813705
  have htrace : WordTrace (prefixWord ++ tailWord_5813705) baseStart_5813705 baseEnd_5813705 := by
    simpa [prefixWord, tailWord_5813705, baseEnd_5813705] using wordTrace_append hprefix tailTrace_5813705
  have hstable : (prefixWord ++ tailWord_5813705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5813705).length < 2 ^ (prefixWord ++ tailWord_5813705).sum := by decide
  have hdescent : baseEnd_5813705 < baseStart_5813705 := by decide
  rcases family_descends (prefixWord ++ tailWord_5813705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5813706 : List Nat := [3, 1, 2, 1, 2, 4, 1, 4, 1, 4]
def baseStart_5813706 : Nat := 118140960795 + 5813706 * 2 ^ 59
def prefixEnd_5813706 : Nat := 4983230072969 + 3 ^ 40 * 5813706 * 2
def baseEnd_5813706 : Nat := 995075187309312027412753

theorem tailTrace_5813706 : CollatzResearch.WordTrace tailWord_5813706 prefixEnd_5813706 995075187309312027412753 := by
  unfold tailWord_5813706
  simp only [CollatzResearch.WordTrace]
  refine ⟨53010819468985884695237243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141362185250629025853965981 53010819468985884695237243)
  ·
    refine ⟨79516229203478827042855865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53010819468985884695237243 79516229203478827042855865)
    ·
      refine ⟨59637171902609120282141899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79516229203478827042855865 59637171902609120282141899)
      ·
        refine ⟨89455757853913680423212849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59637171902609120282141899 89455757853913680423212849)
        ·
          refine ⟨67091818390435260317409637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89455757853913680423212849 67091818390435260317409637)
          ·
            refine ⟨12579715948206611309514307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67091818390435260317409637 12579715948206611309514307)
            ·
              refine ⟨18869573922309916964271461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12579715948206611309514307 18869573922309916964271461)
              ·
                refine ⟨3538045110433109430800899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18869573922309916964271461 3538045110433109430800899)
                ·
                  refine ⟨5307067665649664146201349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3538045110433109430800899 5307067665649664146201349)
                  ·
                    refine ⟨995075187309312027412753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5307067665649664146201349 995075187309312027412753)
                    ·
                      rfl

theorem cell23_5813706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 4, 1, 4].length) (baseStart_5813706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5813706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5813706 prefixEnd_5813706 := by exact prefixLift 5813706
  have htrace : WordTrace (prefixWord ++ tailWord_5813706) baseStart_5813706 baseEnd_5813706 := by
    simpa [prefixWord, tailWord_5813706, baseEnd_5813706] using wordTrace_append hprefix tailTrace_5813706
  have hstable : (prefixWord ++ tailWord_5813706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5813706).length < 2 ^ (prefixWord ++ tailWord_5813706).sum := by decide
  have hdescent : baseEnd_5813706 < baseStart_5813706 := by decide
  rcases family_descends (prefixWord ++ tailWord_5813706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5813729 : List Nat := [1, 2, 3, 1, 2, 3, 1, 1, 5, 1, 3]
def baseStart_5813729 : Nat := 118140960795 + 5813729 * 2 ^ 59
def prefixEnd_5813729 : Nat := 4983230072969 + 3 ^ 40 * 5813729 * 2
def baseEnd_5813729 : Nat := 2985237371982989492250653

theorem tailTrace_5813729 : CollatzResearch.WordTrace tailWord_5813729 prefixEnd_5813729 2985237371982989492250653 := by
  unfold tailWord_5813729
  simp only [CollatzResearch.WordTrace]
  refine ⟨212044116754860213709036241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141362744503240142472690827 212044116754860213709036241)
  ·
    refine ⟨159033087566145160281777181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212044116754860213709036241 159033087566145160281777181)
    ·
      refine ⟨59637407837304435105666443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 159033087566145160281777181 59637407837304435105666443)
      ·
        refine ⟨89456111755956652658499665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59637407837304435105666443 89456111755956652658499665)
        ·
          refine ⟨67092083816967489493874749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89456111755956652658499665 67092083816967489493874749)
          ·
            refine ⟨25159531431362808560203031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67092083816967489493874749 25159531431362808560203031)
            ·
              refine ⟨37739297147044212840304547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25159531431362808560203031 37739297147044212840304547)
              ·
                refine ⟨56608945720566319260456821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37739297147044212840304547 56608945720566319260456821)
                ·
                  refine ⟨5307088661303092430667827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 56608945720566319260456821 5307088661303092430667827)
                  ·
                    refine ⟨7960632991954638646001741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5307088661303092430667827 7960632991954638646001741)
                    ·
                      refine ⟨2985237371982989492250653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7960632991954638646001741 2985237371982989492250653)
                      ·
                        rfl

theorem cell23_5813729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 1, 5, 1, 3].length) (baseStart_5813729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5813729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5813729 prefixEnd_5813729 := by exact prefixLift 5813729
  have htrace : WordTrace (prefixWord ++ tailWord_5813729) baseStart_5813729 baseEnd_5813729 := by
    simpa [prefixWord, tailWord_5813729, baseEnd_5813729] using wordTrace_append hprefix tailTrace_5813729
  have hstable : (prefixWord ++ tailWord_5813729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5813729).length < 2 ^ (prefixWord ++ tailWord_5813729).sum := by decide
  have hdescent : baseEnd_5813729 < baseStart_5813729 := by decide
  rcases family_descends (prefixWord ++ tailWord_5813729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5813739 : List Nat := [1, 1, 1, 1, 2, 3, 2, 5, 2, 3, 2]
def baseStart_5813739 : Nat := 118140960795 + 5813739 * 2 ^ 59
def prefixEnd_5813739 : Nat := 4983230072969 + 3 ^ 40 * 5813739 * 2
def baseEnd_5813739 : Nat := 2985242506789534453125607

theorem tailTrace_5813739 : CollatzResearch.WordTrace tailWord_5813739 prefixEnd_5813739 2985242506789534453125607 := by
  unfold tailWord_5813739
  simp only [CollatzResearch.WordTrace]
  refine ⟨212044481484823985416900271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141362987656549323611266847 212044481484823985416900271)
  ·
    refine ⟨318066722227235978125350407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212044481484823985416900271 318066722227235978125350407)
    ·
      refine ⟨477100083340853967188025611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 318066722227235978125350407 477100083340853967188025611)
      ·
        refine ⟨715650125011280950782038417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 477100083340853967188025611 715650125011280950782038417)
        ·
          refine ⟨536737593758460713086528813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 715650125011280950782038417 536737593758460713086528813)
          ·
            refine ⟨201276597659422767407448305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 536737593758460713086528813 201276597659422767407448305)
            ·
              refine ⟨150957448244567075555586229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 201276597659422767407448305 150957448244567075555586229)
              ·
                refine ⟨14152260772928163333336209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 150957448244567075555586229 14152260772928163333336209)
                ·
                  refine ⟨10614195579696122500002157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14152260772928163333336209 10614195579696122500002157)
                  ·
                    refine ⟨3980323342386045937500809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10614195579696122500002157 3980323342386045937500809)
                    ·
                      refine ⟨2985242506789534453125607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3980323342386045937500809 2985242506789534453125607)
                      ·
                        rfl

theorem cell23_5813739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 5, 2, 3, 2].length) (baseStart_5813739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5813739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5813739 prefixEnd_5813739 := by exact prefixLift 5813739
  have htrace : WordTrace (prefixWord ++ tailWord_5813739) baseStart_5813739 baseEnd_5813739 := by
    simpa [prefixWord, tailWord_5813739, baseEnd_5813739] using wordTrace_append hprefix tailTrace_5813739
  have hstable : (prefixWord ++ tailWord_5813739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5813739).length < 2 ^ (prefixWord ++ tailWord_5813739).sum := by decide
  have hdescent : baseEnd_5813739 < baseStart_5813739 := by decide
  rcases family_descends (prefixWord ++ tailWord_5813739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5813779 : List Nat := [1, 1, 1, 2, 1, 8, 1, 1, 1, 6]
def baseStart_5813779 : Nat := 118140960795 + 5813779 * 2 ^ 59
def prefixEnd_5813779 : Nat := 4983230072969 + 3 ^ 40 * 5813779 * 2
def baseEnd_5813779 : Nat := 995087682005238098875141

theorem tailTrace_5813779 : CollatzResearch.WordTrace tailWord_5813779 prefixEnd_5813779 995087682005238098875141 := by
  unfold tailWord_5813779
  simp only [CollatzResearch.WordTrace]
  refine ⟨212045940404679072248356391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141363960269786048165570927 212045940404679072248356391)
  ·
    refine ⟨318068910607018608372534587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212045940404679072248356391 318068910607018608372534587)
    ·
      refine ⟨477103365910527912558801881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 318068910607018608372534587 477103365910527912558801881)
      ·
        refine ⟨357827524432895934419101411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 477103365910527912558801881 357827524432895934419101411)
        ·
          refine ⟨536741286649343901628652117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 357827524432895934419101411 536741286649343901628652117)
          ·
            refine ⟨6289936952921998847210767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 536741286649343901628652117 6289936952921998847210767)
            ·
              refine ⟨9434905429382998270816151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6289936952921998847210767 9434905429382998270816151)
              ·
                refine ⟨14152358144074497406224227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9434905429382998270816151 14152358144074497406224227)
                ·
                  refine ⟨21228537216111746109336341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14152358144074497406224227 21228537216111746109336341)
                  ·
                    refine ⟨995087682005238098875141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21228537216111746109336341 995087682005238098875141)
                    ·
                      rfl

theorem cell23_5813779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 1, 1, 1, 6].length) (baseStart_5813779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5813779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5813779 prefixEnd_5813779 := by exact prefixLift 5813779
  have htrace : WordTrace (prefixWord ++ tailWord_5813779) baseStart_5813779 baseEnd_5813779 := by
    simpa [prefixWord, tailWord_5813779, baseEnd_5813779] using wordTrace_append hprefix tailTrace_5813779
  have hstable : (prefixWord ++ tailWord_5813779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5813779).length < 2 ^ (prefixWord ++ tailWord_5813779).sum := by decide
  have hdescent : baseEnd_5813779 < baseStart_5813779 := by decide
  rcases family_descends (prefixWord ++ tailWord_5813779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5813806 : List Nat := [4, 1, 3, 1, 2, 2, 2, 1, 1, 1, 5]
def baseStart_5813806 : Nat := 118140960795 + 5813806 * 2 ^ 59
def prefixEnd_5813806 : Nat := 4983230072969 + 3 ^ 40 * 5813806 * 2
def baseEnd_5813806 : Nat := 2985276909993385690987799

theorem tailTrace_5813806 : CollatzResearch.WordTrace tailWord_5813806 prefixEnd_5813806 2985276909993385690987799 := by
  unfold tailWord_5813806
  simp only [CollatzResearch.WordTrace]
  refine ⟨26505865646947656982448659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 141364616783720837239726181 26505865646947656982448659)
  ·
    refine ⟨39758798470421485473672989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26505865646947656982448659 39758798470421485473672989)
    ·
      refine ⟨14909549426408057052627371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39758798470421485473672989 14909549426408057052627371)
      ·
        refine ⟨22364324139612085578941057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14909549426408057052627371 22364324139612085578941057)
        ·
          refine ⟨16773243104709064184205793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22364324139612085578941057 16773243104709064184205793)
          ·
            refine ⟨12579932328531798138154345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16773243104709064184205793 12579932328531798138154345)
            ·
              refine ⟨9434949246398848603615759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12579932328531798138154345 9434949246398848603615759)
              ·
                refine ⟨14152423869598272905423639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9434949246398848603615759 14152423869598272905423639)
                ·
                  refine ⟨21228635804397409358135459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14152423869598272905423639 21228635804397409358135459)
                  ·
                    refine ⟨31842953706596114037203189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21228635804397409358135459 31842953706596114037203189)
                    ·
                      refine ⟨2985276909993385690987799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31842953706596114037203189 2985276909993385690987799)
                      ·
                        rfl

theorem cell23_5813806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 2, 1, 1, 1, 5].length) (baseStart_5813806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5813806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5813806 prefixEnd_5813806 := by exact prefixLift 5813806
  have htrace : WordTrace (prefixWord ++ tailWord_5813806) baseStart_5813806 baseEnd_5813806 := by
    simpa [prefixWord, tailWord_5813806, baseEnd_5813806] using wordTrace_append hprefix tailTrace_5813806
  have hstable : (prefixWord ++ tailWord_5813806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5813806).length < 2 ^ (prefixWord ++ tailWord_5813806).sum := by decide
  have hdescent : baseEnd_5813806 < baseStart_5813806 := by decide
  rcases family_descends (prefixWord ++ tailWord_5813806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5813820 : List Nat := [2, 2, 2, 2, 4, 2, 1, 1, 3, 2, 2]
def baseStart_5813820 : Nat := 118140960795 + 5813820 * 2 ^ 59
def prefixEnd_5813820 : Nat := 4983230072969 + 3 ^ 40 * 5813820 * 2
def baseEnd_5813820 : Nat := 2985284098722548636212735

theorem tailTrace_5813820 : CollatzResearch.WordTrace tailWord_5813820 prefixEnd_5813820 2985284098722548636212735 := by
  unfold tailWord_5813820
  simp only [CollatzResearch.WordTrace]
  refine ⟨106023717898765268125299457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141364957198353690833732609 106023717898765268125299457)
  ·
    refine ⟨79517788424073951093974593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106023717898765268125299457 79517788424073951093974593)
    ·
      refine ⟨59638341318055463320480945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79517788424073951093974593 59638341318055463320480945)
      ·
        refine ⟨44728755988541597490360709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59638341318055463320480945 44728755988541597490360709)
        ·
          refine ⟨8386641747851549529442633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44728755988541597490360709 8386641747851549529442633)
          ·
            refine ⟨6289981310888662147081975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8386641747851549529442633 6289981310888662147081975)
            ·
              refine ⟨9434971966332993220622963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6289981310888662147081975 9434971966332993220622963)
              ·
                refine ⟨14152457949499489830934445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9434971966332993220622963 14152457949499489830934445)
                ·
                  refine ⟨5307171731062308686600417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14152457949499489830934445 5307171731062308686600417)
                  ·
                    refine ⟨3980378798296731514950313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5307171731062308686600417 3980378798296731514950313)
                    ·
                      refine ⟨2985284098722548636212735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3980378798296731514950313 2985284098722548636212735)
                      ·
                        rfl

theorem cell23_5813820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 1, 1, 3, 2, 2].length) (baseStart_5813820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5813820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5813820 prefixEnd_5813820 := by exact prefixLift 5813820
  have htrace : WordTrace (prefixWord ++ tailWord_5813820) baseStart_5813820 baseEnd_5813820 := by
    simpa [prefixWord, tailWord_5813820, baseEnd_5813820] using wordTrace_append hprefix tailTrace_5813820
  have hstable : (prefixWord ++ tailWord_5813820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5813820).length < 2 ^ (prefixWord ++ tailWord_5813820).sum := by decide
  have hdescent : baseEnd_5813820 < baseStart_5813820 := by decide
  rcases family_descends (prefixWord ++ tailWord_5813820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5813830 : List Nat := [6, 1, 1, 1, 3, 1, 1, 3, 2, 4]
def baseStart_5813830 : Nat := 118140960795 + 5813830 * 2 ^ 59
def prefixEnd_5813830 : Nat := 4983230072969 + 3 ^ 40 * 5813830 * 2
def baseEnd_5813830 : Nat := 995096411176364532362563

theorem tailTrace_5813830 : CollatzResearch.WordTrace tailWord_5813830 prefixEnd_5813830 995096411176364532362563 := by
  unfold tailWord_5813830
  simp only [CollatzResearch.WordTrace]
  refine ⟨6626493766484197123701967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 141365200351662871972308629 6626493766484197123701967)
  ·
    refine ⟨9939740649726295685552951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6626493766484197123701967 9939740649726295685552951)
    ·
      refine ⟨14909610974589443528329427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9939740649726295685552951 14909610974589443528329427)
      ·
        refine ⟨22364416461884165292494141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14909610974589443528329427 22364416461884165292494141)
        ·
          refine ⟨8386656173206561984685303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22364416461884165292494141 8386656173206561984685303)
          ·
            refine ⟨12579984259809842977027955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8386656173206561984685303 12579984259809842977027955)
            ·
              refine ⟨18869976389714764465541933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12579984259809842977027955 18869976389714764465541933)
              ·
                refine ⟨7076241146143036674578225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18869976389714764465541933 7076241146143036674578225)
                ·
                  refine ⟨5307180859607277505933669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7076241146143036674578225 5307180859607277505933669)
                  ·
                    refine ⟨995096411176364532362563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5307180859607277505933669 995096411176364532362563)
                    ·
                      rfl

theorem cell23_5813830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 3, 2, 4].length) (baseStart_5813830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5813830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5813830 prefixEnd_5813830 := by exact prefixLift 5813830
  have htrace : WordTrace (prefixWord ++ tailWord_5813830) baseStart_5813830 baseEnd_5813830 := by
    simpa [prefixWord, tailWord_5813830, baseEnd_5813830] using wordTrace_append hprefix tailTrace_5813830
  have hstable : (prefixWord ++ tailWord_5813830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5813830).length < 2 ^ (prefixWord ++ tailWord_5813830).sum := by decide
  have hdescent : baseEnd_5813830 < baseStart_5813830 := by decide
  rcases family_descends (prefixWord ++ tailWord_5813830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5813870 : List Nat := [4, 1, 2, 2, 3, 1, 2, 2, 2, 1, 3]
def baseStart_5813870 : Nat := 118140960795 + 5813870 * 2 ^ 59
def prefixEnd_5813870 : Nat := 4983230072969 + 3 ^ 40 * 5813870 * 2
def baseEnd_5813870 : Nat := 2985309772755273440587505

theorem tailTrace_5813870 : CollatzResearch.WordTrace tailWord_5813870 prefixEnd_5813870 2985309772755273440587505 := by
  unfold tailWord_5813870
  simp only [CollatzResearch.WordTrace]
  refine ⟨26506157430918674348739883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 141366172964899596526612709 26506157430918674348739883)
  ·
    refine ⟨39759236146378011523109825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26506157430918674348739883 39759236146378011523109825)
    ·
      refine ⟨29819427109783508642332369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39759236146378011523109825 29819427109783508642332369)
      ·
        refine ⟨22364570332337631481749277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29819427109783508642332369 22364570332337631481749277)
        ·
          refine ⟨8386713874626611805655979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22364570332337631481749277 8386713874626611805655979)
          ·
            refine ⟨12580070811939917708483969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8386713874626611805655979 12580070811939917708483969)
            ·
              refine ⟨9435053108954938281362977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12580070811939917708483969 9435053108954938281362977)
              ·
                refine ⟨7076289831716203711022233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9435053108954938281362977 7076289831716203711022233)
                ·
                  refine ⟨5307217373787152783266675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7076289831716203711022233 5307217373787152783266675)
                  ·
                    refine ⟨7960826060680729174900013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5307217373787152783266675 7960826060680729174900013)
                    ·
                      refine ⟨2985309772755273440587505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7960826060680729174900013 2985309772755273440587505)
                      ·
                        rfl

theorem cell23_5813870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 2, 2, 2, 1, 3].length) (baseStart_5813870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5813870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5813870 prefixEnd_5813870 := by exact prefixLift 5813870
  have htrace : WordTrace (prefixWord ++ tailWord_5813870) baseStart_5813870 baseEnd_5813870 := by
    simpa [prefixWord, tailWord_5813870, baseEnd_5813870] using wordTrace_append hprefix tailTrace_5813870
  have hstable : (prefixWord ++ tailWord_5813870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5813870).length < 2 ^ (prefixWord ++ tailWord_5813870).sum := by decide
  have hdescent : baseEnd_5813870 < baseStart_5813870 := by decide
  rcases family_descends (prefixWord ++ tailWord_5813870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5813889 : List Nat := [1, 2, 4, 2, 1, 2, 1, 1, 1, 4, 4]
def baseStart_5813889 : Nat := 118140960795 + 5813889 * 2 ^ 59
def prefixEnd_5813889 : Nat := 4983230072969 + 3 ^ 40 * 5813889 * 2
def baseEnd_5813889 : Nat := 2985319528887708866249917

theorem tailTrace_5813889 : CollatzResearch.WordTrace tailWord_5813889 prefixEnd_5813889 2985319528887708866249917 := by
  unfold tailWord_5813889
  simp only [CollatzResearch.WordTrace]
  refine ⟨212049952434280561034860721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141366634956187040689907147 212049952434280561034860721)
  ·
    refine ⟨159037464325710420776145541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212049952434280561034860721 159037464325710420776145541)
    ·
      refine ⟨29819524561070703895527289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 159037464325710420776145541 29819524561070703895527289)
      ·
        refine ⟨22364643420803027921645467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29819524561070703895527289 22364643420803027921645467)
        ·
          refine ⟨33546965131204541882468201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22364643420803027921645467 33546965131204541882468201)
          ·
            refine ⟨25160223848403406411851151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33546965131204541882468201 25160223848403406411851151)
            ·
              refine ⟨37740335772605109617776727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25160223848403406411851151 37740335772605109617776727)
              ·
                refine ⟨56610503658907664426665091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37740335772605109617776727 56610503658907664426665091)
                ·
                  refine ⟨84915755488361496639997637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56610503658907664426665091 84915755488361496639997637)
                  ·
                    refine ⟨15921704154067780619999557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 84915755488361496639997637 15921704154067780619999557)
                    ·
                      refine ⟨2985319528887708866249917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15921704154067780619999557 2985319528887708866249917)
                      ·
                        rfl

theorem cell23_5813889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_5813889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5813889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5813889 prefixEnd_5813889 := by exact prefixLift 5813889
  have htrace : WordTrace (prefixWord ++ tailWord_5813889) baseStart_5813889 baseEnd_5813889 := by
    simpa [prefixWord, tailWord_5813889, baseEnd_5813889] using wordTrace_append hprefix tailTrace_5813889
  have hstable : (prefixWord ++ tailWord_5813889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5813889).length < 2 ^ (prefixWord ++ tailWord_5813889).sum := by decide
  have hdescent : baseEnd_5813889 < baseStart_5813889 := by decide
  rcases family_descends (prefixWord ++ tailWord_5813889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5813893 : List Nat := [1, 3, 1, 1, 4, 1, 1, 5, 2, 2, 2]
def baseStart_5813893 : Nat := 118140960795 + 5813893 * 2 ^ 59
def prefixEnd_5813893 : Nat := 4983230072969 + 3 ^ 40 * 5813893 * 2
def baseEnd_5813893 : Nat := 2985321582810326850599899

theorem tailTrace_5813893 : CollatzResearch.WordTrace tailWord_5813893 prefixEnd_5813893 2985321582810326850599899 := by
  unfold tailWord_5813893
  simp only [CollatzResearch.WordTrace]
  refine ⟨212050098326266069718006333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141366732217510713145337555 212050098326266069718006333)
  ·
    refine ⟨79518786872349776144252375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 212050098326266069718006333 79518786872349776144252375)
    ·
      refine ⟨119278180308524664216378563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79518786872349776144252375 119278180308524664216378563)
      ·
        refine ⟨178917270462786996324567845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119278180308524664216378563 178917270462786996324567845)
        ·
          refine ⟨33546988211772561810856471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 178917270462786996324567845 33546988211772561810856471)
          ·
            refine ⟨50320482317658842716284707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33546988211772561810856471 50320482317658842716284707)
            ·
              refine ⟨75480723476488264074427061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50320482317658842716284707 75480723476488264074427061)
              ·
                refine ⟨7076317825920774756977537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 75480723476488264074427061 7076317825920774756977537)
                ·
                  refine ⟨5307238369440581067733153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7076317825920774756977537 5307238369440581067733153)
                  ·
                    refine ⟨3980428777080435800799865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5307238369440581067733153 3980428777080435800799865)
                    ·
                      refine ⟨2985321582810326850599899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3980428777080435800799865 2985321582810326850599899)
                      ·
                        rfl

theorem cell23_5813893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 5, 2, 2, 2].length) (baseStart_5813893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5813893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5813893 prefixEnd_5813893 := by exact prefixLift 5813893
  have htrace : WordTrace (prefixWord ++ tailWord_5813893) baseStart_5813893 baseEnd_5813893 := by
    simpa [prefixWord, tailWord_5813893, baseEnd_5813893] using wordTrace_append hprefix tailTrace_5813893
  have hstable : (prefixWord ++ tailWord_5813893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5813893).length < 2 ^ (prefixWord ++ tailWord_5813893).sum := by decide
  have hdescent : baseEnd_5813893 < baseStart_5813893 := by decide
  rcases family_descends (prefixWord ++ tailWord_5813893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5813949 : List Nat := [1, 4, 1, 2, 1, 2, 1, 1, 3, 3, 4]
def baseStart_5813949 : Nat := 118140960795 + 5813949 * 2 ^ 59
def prefixEnd_5813949 : Nat := 4983230072969 + 3 ^ 40 * 5813949 * 2
def baseEnd_5813949 : Nat := 2985350337726978631499641

theorem tailTrace_5813949 : CollatzResearch.WordTrace tailWord_5813949 prefixEnd_5813949 2985350337726978631499641 := by
  unfold tailWord_5813949
  simp only [CollatzResearch.WordTrace]
  refine ⟨212052140814063191282044901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141368093876042127521363267 212052140814063191282044901)
  ·
    refine ⟨39759776402636848365383419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 212052140814063191282044901 39759776402636848365383419)
    ·
      refine ⟨59639664603955272548075129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39759776402636848365383419 59639664603955272548075129)
      ·
        refine ⟨44729748452966454411056347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59639664603955272548075129 44729748452966454411056347)
        ·
          refine ⟨67094622679449681616584521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44729748452966454411056347 67094622679449681616584521)
          ·
            refine ⟨50320967009587261212438391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67094622679449681616584521 50320967009587261212438391)
            ·
              refine ⟨75481450514380891818657587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50320967009587261212438391 75481450514380891818657587)
              ·
                refine ⟨113222175771571337727986381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75481450514380891818657587 113222175771571337727986381)
                ·
                  refine ⟨42458315914339251647994893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 113222175771571337727986381 42458315914339251647994893)
                  ·
                    refine ⟨15921868467877219367998085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42458315914339251647994893 15921868467877219367998085)
                    ·
                      refine ⟨2985350337726978631499641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15921868467877219367998085 2985350337726978631499641)
                      ·
                        rfl

theorem cell23_5813949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 1, 3, 3, 4].length) (baseStart_5813949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5813949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5813949 prefixEnd_5813949 := by exact prefixLift 5813949
  have htrace : WordTrace (prefixWord ++ tailWord_5813949) baseStart_5813949 baseEnd_5813949 := by
    simpa [prefixWord, tailWord_5813949, baseEnd_5813949] using wordTrace_append hprefix tailTrace_5813949
  have hstable : (prefixWord ++ tailWord_5813949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5813949).length < 2 ^ (prefixWord ++ tailWord_5813949).sum := by decide
  have hdescent : baseEnd_5813949 < baseStart_5813949 := by decide
  rcases family_descends (prefixWord ++ tailWord_5813949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5813966 : List Nat := [4, 1, 1, 1, 3, 1, 2, 3, 2, 1, 4]
def baseStart_5813966 : Nat := 118140960795 + 5813966 * 2 ^ 59
def prefixEnd_5813966 : Nat := 4983230072969 + 3 ^ 40 * 5813966 * 2
def baseEnd_5813966 : Nat := 2985359066898105064987063

theorem tailTrace_5813966 : CollatzResearch.WordTrace tailWord_5813966 prefixEnd_5813966 2985359066898105064987063 := by
  unfold tailWord_5813966
  simp only [CollatzResearch.WordTrace]
  refine ⟨26506595106875200398176719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 141368507236667735456942501 26506595106875200398176719)
  ·
    refine ⟨39759892660312800597265079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26506595106875200398176719 39759892660312800597265079)
    ·
      refine ⟨59639838990469200895897619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39759892660312800597265079 59639838990469200895897619)
      ·
        refine ⟨89459758485703801343846429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59639838990469200895897619 89459758485703801343846429)
        ·
          refine ⟨33547409432138925503942411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89459758485703801343846429 33547409432138925503942411)
          ·
            refine ⟨50321114148208388255913617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33547409432138925503942411 50321114148208388255913617)
            ·
              refine ⟨37740835611156291191935213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50321114148208388255913617 37740835611156291191935213)
              ·
                refine ⟨14152813354183609196975705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37740835611156291191935213 14152813354183609196975705)
                ·
                  refine ⟨10614610015637706897731779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14152813354183609196975705 10614610015637706897731779)
                  ·
                    refine ⟨15921915023456560346597669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10614610015637706897731779 15921915023456560346597669)
                    ·
                      refine ⟨2985359066898105064987063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15921915023456560346597669 2985359066898105064987063)
                      ·
                        rfl

theorem cell23_5813966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 3, 2, 1, 4].length) (baseStart_5813966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5813966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5813966 prefixEnd_5813966 := by exact prefixLift 5813966
  have htrace : WordTrace (prefixWord ++ tailWord_5813966) baseStart_5813966 baseEnd_5813966 := by
    simpa [prefixWord, tailWord_5813966, baseEnd_5813966] using wordTrace_append hprefix tailTrace_5813966
  have hstable : (prefixWord ++ tailWord_5813966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5813966).length < 2 ^ (prefixWord ++ tailWord_5813966).sum := by decide
  have hdescent : baseEnd_5813966 < baseStart_5813966 := by decide
  rcases family_descends (prefixWord ++ tailWord_5813966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5813989 : List Nat := [1, 3, 1, 4, 1, 1, 1, 3, 8]
def baseStart_5813989 : Nat := 118140960795 + 5813989 * 2 ^ 59
def prefixEnd_5813989 : Nat := 4983230072969 + 3 ^ 40 * 5813989 * 2
def baseEnd_5813989 : Nat := 331707875217017608333273

theorem tailTrace_5813989 : CollatzResearch.WordTrace tailWord_5813989 prefixEnd_5813989 331707875217017608333273 := by
  unfold tailWord_5813989
  simp only [CollatzResearch.WordTrace]
  refine ⟨212053599733918278113501021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141369066489278852075667347 212053599733918278113501021)
  ·
    refine ⟨79520099900219354292562883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 212053599733918278113501021 79520099900219354292562883)
    ·
      refine ⟨119280149850329031438844325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79520099900219354292562883 119280149850329031438844325)
      ·
        refine ⟨22365028096936693394783311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 119280149850329031438844325 22365028096936693394783311)
        ·
          refine ⟨33547542145405040092174967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22365028096936693394783311 33547542145405040092174967)
          ·
            refine ⟨50321313218107560138262451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33547542145405040092174967 50321313218107560138262451)
            ·
              refine ⟨75481969827161340207393677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50321313218107560138262451 75481969827161340207393677)
              ·
                refine ⟨28305738685185502577772629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75481969827161340207393677 28305738685185502577772629)
                ·
                  refine ⟨331707875217017608333273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28305738685185502577772629 331707875217017608333273)
                  ·
                    rfl

theorem cell23_5813989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 3, 8].length) (baseStart_5813989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5813989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5813989 prefixEnd_5813989 := by exact prefixLift 5813989
  have htrace : WordTrace (prefixWord ++ tailWord_5813989) baseStart_5813989 baseEnd_5813989 := by
    simpa [prefixWord, tailWord_5813989, baseEnd_5813989] using wordTrace_append hprefix tailTrace_5813989
  have hstable : (prefixWord ++ tailWord_5813989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5813989).length < 2 ^ (prefixWord ++ tailWord_5813989).sum := by decide
  have hdescent : baseEnd_5813989 < baseStart_5813989 := by decide
  rcases family_descends (prefixWord ++ tailWord_5813989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5814066 : List Nat := [3, 2, 1, 1, 3, 2, 1, 3, 1, 6]
def baseStart_5814066 : Nat := 118140960795 + 5814066 * 2 ^ 59
def prefixEnd_5814066 : Nat := 4983230072969 + 3 ^ 40 * 5814066 * 2
def baseEnd_5814066 : Nat := 995136804987851557912201

theorem tailTrace_5814066 : CollatzResearch.WordTrace tailWord_5814066 prefixEnd_5814066 995136804987851557912201 := by
  unfold tailWord_5814066
  simp only [CollatzResearch.WordTrace]
  refine ⟨53014102038659830066013513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141370938769759546842702701 53014102038659830066013513)
  ·
    refine ⟨39760576528994872549510135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53014102038659830066013513 39760576528994872549510135)
    ·
      refine ⟨59640864793492308824265203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39760576528994872549510135 59640864793492308824265203)
      ·
        refine ⟨89461297190238463236397805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59640864793492308824265203 89461297190238463236397805)
        ·
          refine ⟨33547986446339423713649177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89461297190238463236397805 33547986446339423713649177)
          ·
            refine ⟨25160989834754567785236883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33547986446339423713649177 25160989834754567785236883)
            ·
              refine ⟨37741484752131851677855325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25160989834754567785236883 37741484752131851677855325)
              ·
                refine ⟨14153056782049444379195747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37741484752131851677855325 14153056782049444379195747)
                ·
                  refine ⟨21229585173074166568793621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14153056782049444379195747 21229585173074166568793621)
                  ·
                    refine ⟨995136804987851557912201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21229585173074166568793621 995136804987851557912201)
                    ·
                      rfl

theorem cell23_5814066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 3, 1, 6].length) (baseStart_5814066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5814066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5814066 prefixEnd_5814066 := by exact prefixLift 5814066
  have htrace : WordTrace (prefixWord ++ tailWord_5814066) baseStart_5814066 baseEnd_5814066 := by
    simpa [prefixWord, tailWord_5814066, baseEnd_5814066] using wordTrace_append hprefix tailTrace_5814066
  have hstable : (prefixWord ++ tailWord_5814066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5814066).length < 2 ^ (prefixWord ++ tailWord_5814066).sum := by decide
  have hdescent : baseEnd_5814066 < baseStart_5814066 := by decide
  rcases family_descends (prefixWord ++ tailWord_5814066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5814077 : List Nat := [1, 4, 1, 4, 1, 3, 1, 1, 2, 3, 2]
def baseStart_5814077 : Nat := 118140960795 + 5814077 * 2 ^ 59
def prefixEnd_5814077 : Nat := 4983230072969 + 3 ^ 40 * 5814077 * 2
def baseEnd_5814077 : Nat := 2985416063250754130699053

theorem tailTrace_5814077 : CollatzResearch.WordTrace tailWord_5814077 prefixEnd_5814077 2985416063250754130699053 := by
  unfold tailWord_5814077
  simp only [CollatzResearch.WordTrace]
  refine ⟨212056809357599469142704485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141371206238399646095136323 212056809357599469142704485)
  ·
    refine ⟨39760651754549900464257091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 212056809357599469142704485 39760651754549900464257091)
    ·
      refine ⟨59640977631824850696385637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39760651754549900464257091 59640977631824850696385637)
      ·
        refine ⟨11182683305967159505572307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59640977631824850696385637 11182683305967159505572307)
        ·
          refine ⟨16774024958950739258358461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11182683305967159505572307 16774024958950739258358461)
          ·
            refine ⟨6290259359606527221884423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16774024958950739258358461 6290259359606527221884423)
            ·
              refine ⟨9435389039409790832826635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6290259359606527221884423 9435389039409790832826635)
              ·
                refine ⟨14153083559114686249239953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9435389039409790832826635 14153083559114686249239953)
                ·
                  refine ⟨10614812669336014686929965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14153083559114686249239953 10614812669336014686929965)
                  ·
                    refine ⟨3980554751001005507598737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10614812669336014686929965 3980554751001005507598737)
                    ·
                      refine ⟨2985416063250754130699053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3980554751001005507598737 2985416063250754130699053)
                      ·
                        rfl

theorem cell23_5814077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 1, 1, 2, 3, 2].length) (baseStart_5814077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5814077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5814077 prefixEnd_5814077 := by exact prefixLift 5814077
  have htrace : WordTrace (prefixWord ++ tailWord_5814077) baseStart_5814077 baseEnd_5814077 := by
    simpa [prefixWord, tailWord_5814077, baseEnd_5814077] using wordTrace_append hprefix tailTrace_5814077
  have hstable : (prefixWord ++ tailWord_5814077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5814077).length < 2 ^ (prefixWord ++ tailWord_5814077).sum := by decide
  have hdescent : baseEnd_5814077 < baseStart_5814077 := by decide
  rcases family_descends (prefixWord ++ tailWord_5814077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5814099 : List Nat := [1, 1, 1, 2, 1, 1, 3, 1, 4, 2, 6]
def baseStart_5814099 : Nat := 118140960795 + 5814099 * 2 ^ 59
def prefixEnd_5814099 : Nat := 4983230072969 + 3 ^ 40 * 5814099 * 2
def baseEnd_5814099 : Nat := 2985427359825153044623951

theorem tailTrace_5814099 : CollatzResearch.WordTrace tailWord_5814099 prefixEnd_5814099 2985427359825153044623951 := by
  unfold tailWord_5814099
  simp only [CollatzResearch.WordTrace]
  refine ⟨212057611763519766900005351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141371741175679844600003567 212057611763519766900005351)
  ·
    refine ⟨318086417645279650350008027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212057611763519766900005351 318086417645279650350008027)
    ·
      refine ⟨477129626467919475525012041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 318086417645279650350008027 477129626467919475525012041)
      ·
        refine ⟨357847219850939606643759031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 477129626467919475525012041 357847219850939606643759031)
        ·
          refine ⟨536770829776409409965638547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 357847219850939606643759031 536770829776409409965638547)
          ·
            refine ⟨805156244664614114948457821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 536770829776409409965638547 805156244664614114948457821)
            ·
              refine ⟨301933591749230293105671683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 805156244664614114948457821 301933591749230293105671683)
              ·
                refine ⟨452900387623845439658507525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 301933591749230293105671683 452900387623845439658507525)
                ·
                  refine ⟨84918822679471019935970161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 452900387623845439658507525 84918822679471019935970161)
                  ·
                    refine ⟨63689117009603264951977621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 84918822679471019935970161 63689117009603264951977621)
                    ·
                      refine ⟨2985427359825153044623951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63689117009603264951977621 2985427359825153044623951)
                      ·
                        rfl

theorem cell23_5814099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 4, 2, 6].length) (baseStart_5814099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5814099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5814099 prefixEnd_5814099 := by exact prefixLift 5814099
  have htrace : WordTrace (prefixWord ++ tailWord_5814099) baseStart_5814099 baseEnd_5814099 := by
    simpa [prefixWord, tailWord_5814099, baseEnd_5814099] using wordTrace_append hprefix tailTrace_5814099
  have hstable : (prefixWord ++ tailWord_5814099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5814099).length < 2 ^ (prefixWord ++ tailWord_5814099).sum := by decide
  have hdescent : baseEnd_5814099 < baseStart_5814099 := by decide
  rcases family_descends (prefixWord ++ tailWord_5814099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5814100 : List Nat := [2, 4, 1, 1, 3, 1, 3, 2, 2, 4]
def baseStart_5814100 : Nat := 118140960795 + 5814100 * 2 ^ 59
def prefixEnd_5814100 : Nat := 4983230072969 + 3 ^ 40 * 5814100 * 2
def baseEnd_5814100 : Nat := 995142624435269180237149

theorem tailTrace_5814100 : CollatzResearch.WordTrace tailWord_5814100 prefixEnd_5814100 995142624435269180237149 := by
  unfold tailWord_5814100
  simp only [CollatzResearch.WordTrace]
  refine ⟨106028824118258072035395877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141371765491010762713861169 106028824118258072035395877)
  ·
    refine ⟨19880404522173388506636727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 106028824118258072035395877 19880404522173388506636727)
    ·
      refine ⟨29820606783260082759955091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19880404522173388506636727 29820606783260082759955091)
      ·
        refine ⟨44730910174890124139932637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29820606783260082759955091 44730910174890124139932637)
        ·
          refine ⟨16774091315583796552474739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44730910174890124139932637 16774091315583796552474739)
          ·
            refine ⟨25161136973375694828712109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16774091315583796552474739 25161136973375694828712109)
            ·
              refine ⟨9435426365015885560767041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25161136973375694828712109 9435426365015885560767041)
              ·
                refine ⟨7076569773761914170575281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9435426365015885560767041 7076569773761914170575281)
                ·
                  refine ⟨5307427330321435627931461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7076569773761914170575281 5307427330321435627931461)
                  ·
                    refine ⟨995142624435269180237149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5307427330321435627931461 995142624435269180237149)
                    ·
                      rfl

theorem cell23_5814100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 3, 2, 2, 4].length) (baseStart_5814100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5814100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5814100 prefixEnd_5814100 := by exact prefixLift 5814100
  have htrace : WordTrace (prefixWord ++ tailWord_5814100) baseStart_5814100 baseEnd_5814100 := by
    simpa [prefixWord, tailWord_5814100, baseEnd_5814100] using wordTrace_append hprefix tailTrace_5814100
  have hstable : (prefixWord ++ tailWord_5814100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5814100).length < 2 ^ (prefixWord ++ tailWord_5814100).sum := by decide
  have hdescent : baseEnd_5814100 < baseStart_5814100 := by decide
  rcases family_descends (prefixWord ++ tailWord_5814100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5814158 : List Nat := [4, 1, 1, 5, 1, 1, 3, 2, 1, 2, 2]
def baseStart_5814158 : Nat := 118140960795 + 5814158 * 2 ^ 59
def prefixEnd_5814158 : Nat := 4983230072969 + 3 ^ 40 * 5814158 * 2
def baseEnd_5814158 : Nat := 2985457655183768313786181

theorem tailTrace_5814158 : CollatzResearch.WordTrace tailWord_5814158 prefixEnd_5814158 2985457655183768313786181 := by
  unfold tailWord_5814158
  simp only [CollatzResearch.WordTrace]
  refine ⟨26507470458788252497050391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 141373175780204013317602085 26507470458788252497050391)
  ·
    refine ⟨39761205688182378745575587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26507470458788252497050391 39761205688182378745575587)
    ·
      refine ⟨59641808532273568118363381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39761205688182378745575587 59641808532273568118363381)
      ·
        refine ⟨5591419549900647011096567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 59641808532273568118363381 5591419549900647011096567)
        ·
          refine ⟨8387129324850970516644851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5591419549900647011096567 8387129324850970516644851)
          ·
            refine ⟨12580693987276455774967277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8387129324850970516644851 12580693987276455774967277)
            ·
              refine ⟨4717760245228670915612729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12580693987276455774967277 4717760245228670915612729)
              ·
                refine ⟨3538320183921503186709547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4717760245228670915612729 3538320183921503186709547)
                ·
                  refine ⟨5307480275882254780064321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3538320183921503186709547 5307480275882254780064321)
                  ·
                    refine ⟨3980610206911691085048241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5307480275882254780064321 3980610206911691085048241)
                    ·
                      refine ⟨2985457655183768313786181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3980610206911691085048241 2985457655183768313786181)
                      ·
                        rfl

theorem cell23_5814158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 3, 2, 1, 2, 2].length) (baseStart_5814158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5814158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5814158 prefixEnd_5814158 := by exact prefixLift 5814158
  have htrace : WordTrace (prefixWord ++ tailWord_5814158) baseStart_5814158 baseEnd_5814158 := by
    simpa [prefixWord, tailWord_5814158, baseEnd_5814158] using wordTrace_append hprefix tailTrace_5814158
  have hstable : (prefixWord ++ tailWord_5814158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5814158).length < 2 ^ (prefixWord ++ tailWord_5814158).sum := by decide
  have hdescent : baseEnd_5814158 < baseStart_5814158 := by decide
  rcases family_descends (prefixWord ++ tailWord_5814158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5814176 : List Nat := [2, 1, 1, 4, 1, 1, 1, 3, 1, 4, 4]
def baseStart_5814176 : Nat := 118140960795 + 5814176 * 2 ^ 59
def prefixEnd_5814176 : Nat := 4983230072969 + 3 ^ 40 * 5814176 * 2
def baseEnd_5814176 : Nat := 2985466897835549243361097

theorem tailTrace_5814176 : CollatzResearch.WordTrace tailWord_5814176 prefixEnd_5814176 2985466897835549243361097 := by
  unfold tailWord_5814176
  simp only [CollatzResearch.WordTrace]
  refine ⟨106030210092120404525279191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141373613456160539367038921 106030210092120404525279191)
  ·
    refine ⟨159045315138180606787918787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106030210092120404525279191 159045315138180606787918787)
    ·
      refine ⟨238567972707270910181878181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159045315138180606787918787 238567972707270910181878181)
      ·
        refine ⟨44731494882613295659102159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 238567972707270910181878181 44731494882613295659102159)
        ·
          refine ⟨67097242323919943488653239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44731494882613295659102159 67097242323919943488653239)
          ·
            refine ⟨100645863485879915232979859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67097242323919943488653239 100645863485879915232979859)
            ·
              refine ⟨150968795228819872849469789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100645863485879915232979859 150968795228819872849469789)
              ·
                refine ⟨56613298210807452318551171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 150968795228819872849469789 56613298210807452318551171)
                ·
                  refine ⟨84919947316211178477826757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56613298210807452318551171 84919947316211178477826757)
                  ·
                    refine ⟨15922490121789595964592517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 84919947316211178477826757 15922490121789595964592517)
                    ·
                      refine ⟨2985466897835549243361097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15922490121789595964592517 2985466897835549243361097)
                      ·
                        rfl

theorem cell23_5814176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 3, 1, 4, 4].length) (baseStart_5814176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5814176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5814176 prefixEnd_5814176 := by exact prefixLift 5814176
  have htrace : WordTrace (prefixWord ++ tailWord_5814176) baseStart_5814176 baseEnd_5814176 := by
    simpa [prefixWord, tailWord_5814176, baseEnd_5814176] using wordTrace_append hprefix tailTrace_5814176
  have hstable : (prefixWord ++ tailWord_5814176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5814176).length < 2 ^ (prefixWord ++ tailWord_5814176).sum := by decide
  have hdescent : baseEnd_5814176 < baseStart_5814176 := by decide
  rcases family_descends (prefixWord ++ tailWord_5814176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5814183 : List Nat := [1, 1, 6, 1, 2, 1, 1, 2, 2, 1, 5]
def baseStart_5814183 : Nat := 118140960795 + 5814183 * 2 ^ 59
def prefixEnd_5814183 : Nat := 4983230072969 + 3 ^ 40 * 5814183 * 2
def baseEnd_5814183 : Nat := 2985470492200130715973565

theorem tailTrace_5814183 : CollatzResearch.WordTrace tailWord_5814183 prefixEnd_5814183 2985470492200130715973565 := by
  unfold tailWord_5814183
  simp only [CollatzResearch.WordTrace]
  refine ⟨212060675495215449246063203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141373783663476966164042135 212060675495215449246063203)
  ·
    refine ⟨318091013242823173869094805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212060675495215449246063203 318091013242823173869094805)
    ·
      refine ⟨14910516245757336275113819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 318091013242823173869094805 14910516245757336275113819)
      ·
        refine ⟨22365774368636004412670729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14910516245757336275113819 22365774368636004412670729)
        ·
          refine ⟨16774330776477003309503047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22365774368636004412670729 16774330776477003309503047)
          ·
            refine ⟨25161496164715504964254571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16774330776477003309503047 25161496164715504964254571)
            ·
              refine ⟨37742244247073257446381857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25161496164715504964254571 37742244247073257446381857)
              ·
                refine ⟨28306683185304943084786393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37742244247073257446381857 28306683185304943084786393)
                ·
                  refine ⟨21230012388978707313589795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28306683185304943084786393 21230012388978707313589795)
                  ·
                    refine ⟨31845018583468060970384693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21230012388978707313589795 31845018583468060970384693)
                    ·
                      refine ⟨2985470492200130715973565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31845018583468060970384693 2985470492200130715973565)
                      ·
                        rfl

theorem cell23_5814183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_5814183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5814183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5814183 prefixEnd_5814183 := by exact prefixLift 5814183
  have htrace : WordTrace (prefixWord ++ tailWord_5814183) baseStart_5814183 baseEnd_5814183 := by
    simpa [prefixWord, tailWord_5814183, baseEnd_5814183] using wordTrace_append hprefix tailTrace_5814183
  have hstable : (prefixWord ++ tailWord_5814183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5814183).length < 2 ^ (prefixWord ++ tailWord_5814183).sum := by decide
  have hdescent : baseEnd_5814183 < baseStart_5814183 := by decide
  rcases family_descends (prefixWord ++ tailWord_5814183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5814184 : List Nat := [2, 1, 6, 2, 1, 1, 1, 1, 3, 3, 2]
def baseStart_5814184 : Nat := 118140960795 + 5814184 * 2 ^ 59
def prefixEnd_5814184 : Nat := 4983230072969 + 3 ^ 40 * 5814184 * 2
def baseEnd_5814184 : Nat := 2985471005680785212061061

theorem tailTrace_5814184 : CollatzResearch.WordTrace tailWord_5814184 prefixEnd_5814184 2985471005680785212061061 := by
  unfold tailWord_5814184
  simp only [CollatzResearch.WordTrace]
  refine ⟨106030355984105913208424803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141373807978807884277899737 106030355984105913208424803)
  ·
    refine ⟨159045533976158869812637205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106030355984105913208424803 159045533976158869812637205)
    ·
      refine ⟨7455259405132447022467369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 159045533976158869812637205 7455259405132447022467369)
      ·
        refine ⟨5591444553849335266850527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7455259405132447022467369 5591444553849335266850527)
        ·
          refine ⟨8387166830774002900275791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5591444553849335266850527 8387166830774002900275791)
          ·
            refine ⟨12580750246161004350413687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8387166830774002900275791 12580750246161004350413687)
            ·
              refine ⟨18871125369241506525620531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12580750246161004350413687 18871125369241506525620531)
              ·
                refine ⟨28306688053862259788430797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18871125369241506525620531 28306688053862259788430797)
                ·
                  refine ⟨10615008020198347420661549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28306688053862259788430797 10615008020198347420661549)
                  ·
                    refine ⟨3980628007574380282748081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10615008020198347420661549 3980628007574380282748081)
                    ·
                      refine ⟨2985471005680785212061061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3980628007574380282748081 2985471005680785212061061)
                      ·
                        rfl

theorem cell23_5814184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_5814184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5814184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5814184 prefixEnd_5814184 := by exact prefixLift 5814184
  have htrace : WordTrace (prefixWord ++ tailWord_5814184) baseStart_5814184 baseEnd_5814184 := by
    simpa [prefixWord, tailWord_5814184, baseEnd_5814184] using wordTrace_append hprefix tailTrace_5814184
  have hstable : (prefixWord ++ tailWord_5814184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5814184).length < 2 ^ (prefixWord ++ tailWord_5814184).sum := by decide
  have hdescent : baseEnd_5814184 < baseStart_5814184 := by decide
  rcases family_descends (prefixWord ++ tailWord_5814184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5814220 : List Nat := [2, 2, 1, 4, 1, 3, 1, 4, 5]
def baseStart_5814220 : Nat := 118140960795 + 5814220 * 2 ^ 59
def prefixEnd_5814220 : Nat := 4983230072969 + 3 ^ 40 * 5814220 * 2
def baseEnd_5814220 : Nat := 331721054553816341245655

theorem tailTrace_5814220 : CollatzResearch.WordTrace tailWord_5814220 prefixEnd_5814220 331721054553816341245655 := by
  unfold tailWord_5814220
  simp only [CollatzResearch.WordTrace]
  refine ⟨106031012498040702282580057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141374683330720936376773409 106031012498040702282580057)
  ·
    refine ⟨79523259373530526711935043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106031012498040702282580057 79523259373530526711935043)
    ·
      refine ⟨119284889060295790067902565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79523259373530526711935043 119284889060295790067902565)
      ·
        refine ⟨22365916698805460637731731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 119284889060295790067902565 22365916698805460637731731)
        ·
          refine ⟨33548875048208190956597597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22365916698805460637731731 33548875048208190956597597)
          ·
            refine ⟨12580828143078071608724099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33548875048208190956597597 12580828143078071608724099)
            ·
              refine ⟨18871242214617107413086149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12580828143078071608724099 18871242214617107413086149)
              ·
                refine ⟨3538357915240707639953653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18871242214617107413086149 3538357915240707639953653)
                ·
                  refine ⟨331721054553816341245655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3538357915240707639953653 331721054553816341245655)
                  ·
                    rfl

theorem cell23_5814220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 4, 5].length) (baseStart_5814220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5814220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5814220 prefixEnd_5814220 := by exact prefixLift 5814220
  have htrace : WordTrace (prefixWord ++ tailWord_5814220) baseStart_5814220 baseEnd_5814220 := by
    simpa [prefixWord, tailWord_5814220, baseEnd_5814220] using wordTrace_append hprefix tailTrace_5814220
  have hstable : (prefixWord ++ tailWord_5814220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5814220).length < 2 ^ (prefixWord ++ tailWord_5814220).sum := by decide
  have hdescent : baseEnd_5814220 < baseStart_5814220 := by decide
  rcases family_descends (prefixWord ++ tailWord_5814220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5814223 : List Nat := [1, 1, 2, 1, 1, 5, 1, 1, 1, 7, 2]
def baseStart_5814223 : Nat := 118140960795 + 5814223 * 2 ^ 59
def prefixEnd_5814223 : Nat := 4983230072969 + 3 ^ 40 * 5814223 * 2
def baseEnd_5814223 : Nat := 2985491031426310559473381

theorem tailTrace_5814223 : CollatzResearch.WordTrace tailWord_5814223 prefixEnd_5814223 2985491031426310559473381 := by
  unfold tailWord_5814223
  simp only [CollatzResearch.WordTrace]
  refine ⟨212062134415070536077519323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141374756276713690718346215 212062134415070536077519323)
  ·
    refine ⟨318093201622605804116278985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212062134415070536077519323 318093201622605804116278985)
    ·
      refine ⟨238569901216954353087209239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 318093201622605804116278985 238569901216954353087209239)
      ·
        refine ⟨357854851825431529630813859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238569901216954353087209239 357854851825431529630813859)
        ·
          refine ⟨536782277738147294446220789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 357854851825431529630813859 536782277738147294446220789)
          ·
            refine ⟨50323338537951308854333199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 536782277738147294446220789 50323338537951308854333199)
            ·
              refine ⟨75485007806926963281499799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50323338537951308854333199 75485007806926963281499799)
              ·
                refine ⟨113227511710390444922249699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75485007806926963281499799 113227511710390444922249699)
                ·
                  refine ⟨169841267565585667383374549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 113227511710390444922249699 169841267565585667383374549)
                  ·
                    refine ⟨3980654708568414079297841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 169841267565585667383374549 3980654708568414079297841)
                    ·
                      refine ⟨2985491031426310559473381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3980654708568414079297841 2985491031426310559473381)
                      ·
                        rfl

theorem cell23_5814223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 1, 1, 7, 2].length) (baseStart_5814223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5814223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5814223 prefixEnd_5814223 := by exact prefixLift 5814223
  have htrace : WordTrace (prefixWord ++ tailWord_5814223) baseStart_5814223 baseEnd_5814223 := by
    simpa [prefixWord, tailWord_5814223, baseEnd_5814223] using wordTrace_append hprefix tailTrace_5814223
  have hstable : (prefixWord ++ tailWord_5814223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5814223).length < 2 ^ (prefixWord ++ tailWord_5814223).sum := by decide
  have hdescent : baseEnd_5814223 < baseStart_5814223 := by decide
  rcases family_descends (prefixWord ++ tailWord_5814223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5814280 : List Nat := [2, 1, 3, 2, 1, 2, 4, 1, 3, 4]
def baseStart_5814280 : Nat := 118140960795 + 5814280 * 2 ^ 59
def prefixEnd_5814280 : Nat := 4983230072969 + 3 ^ 40 * 5814280 * 2
def baseEnd_5814280 : Nat := 995173433274538945486873

theorem tailTrace_5814280 : CollatzResearch.WordTrace tailWord_5814280 prefixEnd_5814280 995173433274538945486873 := by
  unfold tailWord_5814280
  simp only [CollatzResearch.WordTrace]
  refine ⟨106032106687932017406172147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141376142250576023208229529 106032106687932017406172147)
  ·
    refine ⟨159048160031898026109258221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106032106687932017406172147 159048160031898026109258221)
    ·
      refine ⟨59643060011961759790971833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 159048160031898026109258221 59643060011961759790971833)
      ·
        refine ⟨44732295008971319843228875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59643060011961759790971833 44732295008971319843228875)
        ·
          refine ⟨67098442513456979764843313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44732295008971319843228875 67098442513456979764843313)
          ·
            refine ⟨50323831885092734823632485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67098442513456979764843313 50323831885092734823632485)
            ·
              refine ⟨9435718478454887779431091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50323831885092734823632485 9435718478454887779431091)
              ·
                refine ⟨14153577717682331669146637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9435718478454887779431091 14153577717682331669146637)
                ·
                  refine ⟨5307591644130874375929989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14153577717682331669146637 5307591644130874375929989)
                  ·
                    refine ⟨995173433274538945486873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5307591644130874375929989 995173433274538945486873)
                    ·
                      rfl

theorem cell23_5814280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 4, 1, 3, 4].length) (baseStart_5814280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5814280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5814280 prefixEnd_5814280 := by exact prefixLift 5814280
  have htrace : WordTrace (prefixWord ++ tailWord_5814280) baseStart_5814280 baseEnd_5814280 := by
    simpa [prefixWord, tailWord_5814280, baseEnd_5814280] using wordTrace_append hprefix tailTrace_5814280
  have hstable : (prefixWord ++ tailWord_5814280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5814280).length < 2 ^ (prefixWord ++ tailWord_5814280).sum := by decide
  have hdescent : baseEnd_5814280 < baseStart_5814280 := by decide
  rcases family_descends (prefixWord ++ tailWord_5814280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5814303 : List Nat := [1, 1, 2, 4, 1, 2, 1, 1, 2, 5, 3]
def baseStart_5814303 : Nat := 118140960795 + 5814303 * 2 ^ 59
def prefixEnd_5814303 : Nat := 4983230072969 + 3 ^ 40 * 5814303 * 2
def baseEnd_5814303 : Nat := 2985532109878670246473013

theorem tailTrace_5814303 : CollatzResearch.WordTrace tailWord_5814303 prefixEnd_5814303 2985532109878670246473013 := by
  unfold tailWord_5814303
  simp only [CollatzResearch.WordTrace]
  refine ⟨212065052254780709740431563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141376701503187139826954375 212065052254780709740431563)
  ·
    refine ⟨318097578382171064610647345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212065052254780709740431563 318097578382171064610647345)
    ·
      refine ⟨238573183786628298457985509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 318097578382171064610647345 238573183786628298457985509)
      ·
        refine ⟨44732471959992805960872283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 238573183786628298457985509 44732471959992805960872283)
        ·
          refine ⟨67098707939989208941308425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44732471959992805960872283 67098707939989208941308425)
          ·
            refine ⟨50324030954991906705981319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67098707939989208941308425 50324030954991906705981319)
            ·
              refine ⟨75486046432487860058971979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50324030954991906705981319 75486046432487860058971979)
              ·
                refine ⟨113229069648731790088457969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75486046432487860058971979 113229069648731790088457969)
                ·
                  refine ⟨84921802236548842566343477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 113229069648731790088457969 84921802236548842566343477)
                  ·
                    refine ⟨7961418959676453990594701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 84921802236548842566343477 7961418959676453990594701)
                    ·
                      refine ⟨2985532109878670246473013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7961418959676453990594701 2985532109878670246473013)
                      ·
                        rfl

theorem cell23_5814303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 1, 2, 5, 3].length) (baseStart_5814303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5814303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5814303 prefixEnd_5814303 := by exact prefixLift 5814303
  have htrace : WordTrace (prefixWord ++ tailWord_5814303) baseStart_5814303 baseEnd_5814303 := by
    simpa [prefixWord, tailWord_5814303, baseEnd_5814303] using wordTrace_append hprefix tailTrace_5814303
  have hstable : (prefixWord ++ tailWord_5814303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5814303).length < 2 ^ (prefixWord ++ tailWord_5814303).sum := by decide
  have hdescent : baseEnd_5814303 < baseStart_5814303 := by decide
  rcases family_descends (prefixWord ++ tailWord_5814303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5814314 : List Nat := [3, 1, 4, 1, 2, 1, 3, 3, 1, 4]
def baseStart_5814314 : Nat := 118140960795 + 5814314 * 2 ^ 59
def prefixEnd_5814314 : Nat := 4983230072969 + 3 ^ 40 * 5814314 * 2
def baseEnd_5814314 : Nat := 995179252721956567811821

theorem tailTrace_5814314 : CollatzResearch.WordTrace tailWord_5814314 prefixEnd_5814314 995179252721956567811821 := by
  unfold tailWord_5814314
  simp only [CollatzResearch.WordTrace]
  refine ⟨53016363364435214654770499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141376968971827239079387997 53016363364435214654770499)
  ·
    refine ⟨79524545046652821982155749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53016363364435214654770499 79524545046652821982155749)
    ·
      refine ⟨14910852196247404121654203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79524545046652821982155749 14910852196247404121654203)
      ·
        refine ⟨22366278294371106182481305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14910852196247404121654203 22366278294371106182481305)
        ·
          refine ⟨16774708720778329636860979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22366278294371106182481305 16774708720778329636860979)
          ·
            refine ⟨25162063081167494455291469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16774708720778329636860979 25162063081167494455291469)
            ·
              refine ⟨9435773655437810420734301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25162063081167494455291469 9435773655437810420734301)
              ·
                refine ⟨3538415120789178907775363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9435773655437810420734301 3538415120789178907775363)
                ·
                  refine ⟨5307622681183768361663045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3538415120789178907775363 5307622681183768361663045)
                  ·
                    refine ⟨995179252721956567811821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5307622681183768361663045 995179252721956567811821)
                    ·
                      rfl

theorem cell23_5814314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 3, 3, 1, 4].length) (baseStart_5814314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5814314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5814314 prefixEnd_5814314 := by exact prefixLift 5814314
  have htrace : WordTrace (prefixWord ++ tailWord_5814314) baseStart_5814314 baseEnd_5814314 := by
    simpa [prefixWord, tailWord_5814314, baseEnd_5814314] using wordTrace_append hprefix tailTrace_5814314
  have hstable : (prefixWord ++ tailWord_5814314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5814314).length < 2 ^ (prefixWord ++ tailWord_5814314).sum := by decide
  have hdescent : baseEnd_5814314 < baseStart_5814314 := by decide
  rcases family_descends (prefixWord ++ tailWord_5814314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5814324 : List Nat := [2, 5, 1, 2, 2, 1, 1, 2, 2, 2, 3]
def baseStart_5814324 : Nat := 118140960795 + 5814324 * 2 ^ 59
def prefixEnd_5814324 : Nat := 4983230072969 + 3 ^ 40 * 5814324 * 2
def baseEnd_5814324 : Nat := 2985542892972414664310417

theorem tailTrace_5814324 : CollatzResearch.WordTrace tailWord_5814324 prefixEnd_5814324 2985542892972414664310417 := by
  unfold tailWord_5814324
  simp only [CollatzResearch.WordTrace]
  refine ⟨106032909093852315163473013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141377212125136420217964017 106032909093852315163473013)
  ·
    refine ⟨9940585227548654546575595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 106032909093852315163473013 9940585227548654546575595)
    ·
      refine ⟨14910877841322981819863393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9940585227548654546575595 14910877841322981819863393)
      ·
        refine ⟨11183158380992236364897545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14910877841322981819863393 11183158380992236364897545)
        ·
          refine ⟨8387368785744177273673159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11183158380992236364897545 8387368785744177273673159)
          ·
            refine ⟨12581053178616265910509739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8387368785744177273673159 12581053178616265910509739)
            ·
              refine ⟨18871579767924398865764609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12581053178616265910509739 18871579767924398865764609)
              ·
                refine ⟨14153684825943299149323457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18871579767924398865764609 14153684825943299149323457)
                ·
                  refine ⟨10615263619457474361992593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14153684825943299149323457 10615263619457474361992593)
                  ·
                    refine ⟨7961447714593105771494445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10615263619457474361992593 7961447714593105771494445)
                    ·
                      refine ⟨2985542892972414664310417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7961447714593105771494445 2985542892972414664310417)
                      ·
                        rfl

theorem cell23_5814324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_5814324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5814324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5814324 prefixEnd_5814324 := by exact prefixLift 5814324
  have htrace : WordTrace (prefixWord ++ tailWord_5814324) baseStart_5814324 baseEnd_5814324 := by
    simpa [prefixWord, tailWord_5814324, baseEnd_5814324] using wordTrace_append hprefix tailTrace_5814324
  have hstable : (prefixWord ++ tailWord_5814324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5814324).length < 2 ^ (prefixWord ++ tailWord_5814324).sum := by decide
  have hdescent : baseEnd_5814324 < baseStart_5814324 := by decide
  rcases family_descends (prefixWord ++ tailWord_5814324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5814353 : List Nat := [1, 2, 2, 1, 3, 1, 1, 5, 1, 6]
def baseStart_5814353 : Nat := 118140960795 + 5814353 * 2 ^ 59
def prefixEnd_5814353 : Nat := 4983230072969 + 3 ^ 40 * 5814353 * 2
def baseEnd_5814353 : Nat := 995185927970465016949261

theorem tailTrace_5814353 : CollatzResearch.WordTrace tailWord_5814353 prefixEnd_5814353 995185927970465016949261 := by
  unfold tailWord_5814353
  simp only [CollatzResearch.WordTrace]
  refine ⟨212066875904599568279751713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141377917269733045519834475 212066875904599568279751713)
  ·
    refine ⟨159050156928449676209813785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212066875904599568279751713 159050156928449676209813785)
    ·
      refine ⟨119287617696337257157360339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159050156928449676209813785 119287617696337257157360339)
      ·
        refine ⟨178931426544505885736040509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119287617696337257157360339 178931426544505885736040509)
        ·
          refine ⟨67099284954189707151015191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 178931426544505885736040509 67099284954189707151015191)
          ·
            refine ⟨100648927431284560726522787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67099284954189707151015191 100648927431284560726522787)
            ·
              refine ⟨150973391146926841089784181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100648927431284560726522787 150973391146926841089784181)
              ·
                refine ⟨14153755420024391352167267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 150973391146926841089784181 14153755420024391352167267)
                ·
                  refine ⟨21230633130036587028250901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14153755420024391352167267 21230633130036587028250901)
                  ·
                    refine ⟨995185927970465016949261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21230633130036587028250901 995185927970465016949261)
                    ·
                      rfl

theorem cell23_5814353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 5, 1, 6].length) (baseStart_5814353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5814353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5814353 prefixEnd_5814353 := by exact prefixLift 5814353
  have htrace : WordTrace (prefixWord ++ tailWord_5814353) baseStart_5814353 baseEnd_5814353 := by
    simpa [prefixWord, tailWord_5814353, baseEnd_5814353] using wordTrace_append hprefix tailTrace_5814353
  have hstable : (prefixWord ++ tailWord_5814353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5814353).length < 2 ^ (prefixWord ++ tailWord_5814353).sum := by decide
  have hdescent : baseEnd_5814353 < baseStart_5814353 := by decide
  rcases family_descends (prefixWord ++ tailWord_5814353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5814357 : List Nat := [1, 3, 2, 2, 1, 5, 1, 2, 1, 5]
def baseStart_5814357 : Nat := 118140960795 + 5814357 * 2 ^ 59
def prefixEnd_5814357 : Nat := 4983230072969 + 3 ^ 40 * 5814357 * 2
def baseEnd_5814357 : Nat := 995186612611337678399255

theorem tailTrace_5814357 : CollatzResearch.WordTrace tailWord_5814357 prefixEnd_5814357 995186612611337678399255 := by
  unfold tailWord_5814357
  simp only [CollatzResearch.WordTrace]
  refine ⟨212067021796585076962897325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141378014531056717975264883 212067021796585076962897325)
  ·
    refine ⟨79525133173719403861086497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 212067021796585076962897325 79525133173719403861086497)
    ·
      refine ⟨59643849880289552895814873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79525133173719403861086497 59643849880289552895814873)
      ·
        refine ⟨44732887410217164671861155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59643849880289552895814873 44732887410217164671861155)
        ·
          refine ⟨67099331115325747007791733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44732887410217164671861155 67099331115325747007791733)
          ·
            refine ⟨6290562292061788781980475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 67099331115325747007791733 6290562292061788781980475)
            ·
              refine ⟨9435843438092683172970713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6290562292061788781980475 9435843438092683172970713)
              ·
                refine ⟨7076882578569512379728035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9435843438092683172970713 7076882578569512379728035)
                ·
                  refine ⟨10615323867854268569592053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7076882578569512379728035 10615323867854268569592053)
                  ·
                    refine ⟨995186612611337678399255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10615323867854268569592053 995186612611337678399255)
                    ·
                      rfl

theorem cell23_5814357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 1, 2, 1, 5].length) (baseStart_5814357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5814357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5814357 prefixEnd_5814357 := by exact prefixLift 5814357
  have htrace : WordTrace (prefixWord ++ tailWord_5814357) baseStart_5814357 baseEnd_5814357 := by
    simpa [prefixWord, tailWord_5814357, baseEnd_5814357] using wordTrace_append hprefix tailTrace_5814357
  have hstable : (prefixWord ++ tailWord_5814357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5814357).length < 2 ^ (prefixWord ++ tailWord_5814357).sum := by decide
  have hdescent : baseEnd_5814357 < baseStart_5814357 := by decide
  rcases family_descends (prefixWord ++ tailWord_5814357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5814360 : List Nat := [2, 1, 2, 2, 1, 5, 1, 1, 3, 1, 4]
def baseStart_5814360 : Nat := 118140960795 + 5814360 * 2 ^ 59
def prefixEnd_5814360 : Nat := 4983230072969 + 3 ^ 40 * 5814360 * 2
def baseEnd_5814360 : Nat := 2985561378275976523460251

theorem tailTrace_5814360 : CollatzResearch.WordTrace tailWord_5814360 prefixEnd_5814360 2985561378275976523460251 := by
  unfold tailWord_5814360
  simp only [CollatzResearch.WordTrace]
  refine ⟨106033565607787104237628267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141378087477049472316837689 106033565607787104237628267)
  ·
    refine ⟨159050348411680656356442401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106033565607787104237628267 159050348411680656356442401)
    ·
      refine ⟨119287761308760492267331801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159050348411680656356442401 119287761308760492267331801)
      ·
        refine ⟨89465820981570369200498851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119287761308760492267331801 89465820981570369200498851)
        ·
          refine ⟨134198731472355553800748277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89465820981570369200498851 134198731472355553800748277)
          ·
            refine ⟨12581131075533333168820151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 134198731472355553800748277 12581131075533333168820151)
            ·
              refine ⟨18871696613299999753230227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12581131075533333168820151 18871696613299999753230227)
              ·
                refine ⟨28307544919949999629845341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18871696613299999753230227 28307544919949999629845341)
                ·
                  refine ⟨10615329344981249861192003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28307544919949999629845341 10615329344981249861192003)
                  ·
                    refine ⟨15922994017471874791788005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10615329344981249861192003 15922994017471874791788005)
                    ·
                      refine ⟨2985561378275976523460251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15922994017471874791788005 2985561378275976523460251)
                      ·
                        rfl

theorem cell23_5814360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 1, 3, 1, 4].length) (baseStart_5814360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5814360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5814360 prefixEnd_5814360 := by exact prefixLift 5814360
  have htrace : WordTrace (prefixWord ++ tailWord_5814360) baseStart_5814360 baseEnd_5814360 := by
    simpa [prefixWord, tailWord_5814360, baseEnd_5814360] using wordTrace_append hprefix tailTrace_5814360
  have hstable : (prefixWord ++ tailWord_5814360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5814360).length < 2 ^ (prefixWord ++ tailWord_5814360).sum := by decide
  have hdescent : baseEnd_5814360 < baseStart_5814360 := by decide
  rcases family_descends (prefixWord ++ tailWord_5814360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5814364 : List Nat := [2, 2, 4, 1, 1, 3, 2, 1, 2, 3, 2]
def baseStart_5814364 : Nat := 118140960795 + 5814364 * 2 ^ 59
def prefixEnd_5814364 : Nat := 4983230072969 + 3 ^ 40 * 5814364 * 2
def baseEnd_5814364 : Nat := 2985563432198594507810233

theorem tailTrace_5814364 : CollatzResearch.WordTrace tailWord_5814364 prefixEnd_5814364 2985563432198594507810233 := by
  unfold tailWord_5814364
  simp only [CollatzResearch.WordTrace]
  refine ⟨106033638553779858579201073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141378184738373144772268097 106033638553779858579201073)
  ·
    refine ⟨79525228915334893934400805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106033638553779858579201073 79525228915334893934400805)
    ·
      refine ⟨14910980421625292612700151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79525228915334893934400805 14910980421625292612700151)
      ·
        refine ⟨22366470632437938919050227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14910980421625292612700151 22366470632437938919050227)
        ·
          refine ⟨33549705948656908378575341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22366470632437938919050227 33549705948656908378575341)
          ·
            refine ⟨12581139730746340641965753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33549705948656908378575341 12581139730746340641965753)
            ·
              refine ⟨9435854798059755481474315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12581139730746340641965753 9435854798059755481474315)
              ·
                refine ⟨14153782197089633222211473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9435854798059755481474315 14153782197089633222211473)
                ·
                  refine ⟨10615336647817224916658605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14153782197089633222211473 10615336647817224916658605)
                  ·
                    refine ⟨3980751242931459343746977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10615336647817224916658605 3980751242931459343746977)
                    ·
                      refine ⟨2985563432198594507810233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3980751242931459343746977 2985563432198594507810233)
                      ·
                        rfl

theorem cell23_5814364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 2, 1, 2, 3, 2].length) (baseStart_5814364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5814364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5814364 prefixEnd_5814364 := by exact prefixLift 5814364
  have htrace : WordTrace (prefixWord ++ tailWord_5814364) baseStart_5814364 baseEnd_5814364 := by
    simpa [prefixWord, tailWord_5814364, baseEnd_5814364] using wordTrace_append hprefix tailTrace_5814364
  have hstable : (prefixWord ++ tailWord_5814364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5814364).length < 2 ^ (prefixWord ++ tailWord_5814364).sum := by decide
  have hdescent : baseEnd_5814364 < baseStart_5814364 := by decide
  rcases family_descends (prefixWord ++ tailWord_5814364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5814377 : List Nat := [1, 2, 1, 1, 1, 5, 5, 1, 1, 1, 4]
def baseStart_5814377 : Nat := 118140960795 + 5814377 * 2 ^ 59
def prefixEnd_5814377 : Nat := 4983230072969 + 3 ^ 40 * 5814377 * 2
def baseEnd_5814377 : Nat := 2985570107447102956947673

theorem tailTrace_5814377 : CollatzResearch.WordTrace tailWord_5814377 prefixEnd_5814377 2985570107447102956947673 := by
  unfold tailWord_5814377
  simp only [CollatzResearch.WordTrace]
  refine ⟨212067751256512620378625385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141378500837675080252416923 212067751256512620378625385)
  ·
    refine ⟨159050813442384465283969039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212067751256512620378625385 159050813442384465283969039)
    ·
      refine ⟨238576220163576697925953559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159050813442384465283969039 238576220163576697925953559)
      ·
        refine ⟨357864330245365046888930339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238576220163576697925953559 357864330245365046888930339)
        ·
          refine ⟨536796495368047570333395509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 357864330245365046888930339 536796495368047570333395509)
          ·
            refine ⟨50324671440754459718755829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 536796495368047570333395509 50324671440754459718755829)
            ·
              refine ⟨4717937947570730598633359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50324671440754459718755829 4717937947570730598633359)
              ·
                refine ⟨7076906921356095897950039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4717937947570730598633359 7076906921356095897950039)
                ·
                  refine ⟨10615360382034143846925059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7076906921356095897950039 10615360382034143846925059)
                  ·
                    refine ⟨15923040573051215770387589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10615360382034143846925059 15923040573051215770387589)
                    ·
                      refine ⟨2985570107447102956947673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15923040573051215770387589 2985570107447102956947673)
                      ·
                        rfl

theorem cell23_5814377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 5, 1, 1, 1, 4].length) (baseStart_5814377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5814377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5814377 prefixEnd_5814377 := by exact prefixLift 5814377
  have htrace : WordTrace (prefixWord ++ tailWord_5814377) baseStart_5814377 baseEnd_5814377 := by
    simpa [prefixWord, tailWord_5814377, baseEnd_5814377] using wordTrace_append hprefix tailTrace_5814377
  have hstable : (prefixWord ++ tailWord_5814377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5814377).length < 2 ^ (prefixWord ++ tailWord_5814377).sum := by decide
  have hdescent : baseEnd_5814377 < baseStart_5814377 := by decide
  rcases family_descends (prefixWord ++ tailWord_5814377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5814380 : List Nat := [2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 5]
def baseStart_5814380 : Nat := 118140960795 + 5814380 * 2 ^ 59
def prefixEnd_5814380 : Nat := 4983230072969 + 3 ^ 40 * 5814380 * 2
def baseEnd_5814380 : Nat := 2985571647889066445210159

theorem tailTrace_5814380 : CollatzResearch.WordTrace tailWord_5814380 prefixEnd_5814380 2985571647889066445210159 := by
  unfold tailWord_5814380
  simp only [CollatzResearch.WordTrace]
  refine ⟨106033930337750875945492297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141378573783667834593989729 106033930337750875945492297)
  ·
    refine ⟨79525447753313156959119223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106033930337750875945492297 79525447753313156959119223)
    ·
      refine ⟨119288171629969735438678835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79525447753313156959119223 119288171629969735438678835)
      ·
        refine ⟨178932257444954603158018253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119288171629969735438678835 178932257444954603158018253)
        ·
          refine ⟨67099596541857976184256845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 178932257444954603158018253 67099596541857976184256845)
          ·
            refine ⟨25162348703196741069096317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67099596541857976184256845 25162348703196741069096317)
            ·
              refine ⟨9435880763698777900911119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25162348703196741069096317 9435880763698777900911119)
              ·
                refine ⟨14153821145548166851366679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9435880763698777900911119 14153821145548166851366679)
                ·
                  refine ⟨21230731718322250277050019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14153821145548166851366679 21230731718322250277050019)
                  ·
                    refine ⟨31846097577483375415575029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21230731718322250277050019 31846097577483375415575029)
                    ·
                      refine ⟨2985571647889066445210159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31846097577483375415575029 2985571647889066445210159)
                      ·
                        rfl

theorem cell23_5814380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 5].length) (baseStart_5814380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5814380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5814380 prefixEnd_5814380 := by exact prefixLift 5814380
  have htrace : WordTrace (prefixWord ++ tailWord_5814380) baseStart_5814380 baseEnd_5814380 := by
    simpa [prefixWord, tailWord_5814380, baseEnd_5814380] using wordTrace_append hprefix tailTrace_5814380
  have hstable : (prefixWord ++ tailWord_5814380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5814380).length < 2 ^ (prefixWord ++ tailWord_5814380).sum := by decide
  have hdescent : baseEnd_5814380 < baseStart_5814380 := by decide
  rcases family_descends (prefixWord ++ tailWord_5814380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5814431 : List Nat := [1, 1, 2, 6, 1, 3, 2, 1, 1, 2, 3]
def baseStart_5814431 : Nat := 118140960795 + 5814431 * 2 ^ 59
def prefixEnd_5814431 : Nat := 4983230072969 + 3 ^ 40 * 5814431 * 2
def baseEnd_5814431 : Nat := 2985597835402445745672425

theorem tailTrace_5814431 : CollatzResearch.WordTrace tailWord_5814431 prefixEnd_5814431 2985597835402445745672425 := by
  unfold tailWord_5814431
  simp only [CollatzResearch.WordTrace]
  refine ⟨212069720798316987601091147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141379813865544658400727431 212069720798316987601091147)
  ·
    refine ⟨318104581197475481401636721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212069720798316987601091147 318104581197475481401636721)
    ·
      refine ⟨238578435898106611051227541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 318104581197475481401636721 238578435898106611051227541)
      ·
        refine ⟨11183364182723747393026291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 238578435898106611051227541 11183364182723747393026291)
        ·
          refine ⟨16775046274085621089539437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11183364182723747393026291 16775046274085621089539437)
          ·
            refine ⟨6290642352782107908577289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16775046274085621089539437 6290642352782107908577289)
            ·
              refine ⟨4717981764586580931432967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6290642352782107908577289 4717981764586580931432967)
              ·
                refine ⟨7076972646879871397149451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4717981764586580931432967 7076972646879871397149451)
                ·
                  refine ⟨10615458970319807095724177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7076972646879871397149451 10615458970319807095724177)
                  ·
                    refine ⟨7961594227739855321793133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10615458970319807095724177 7961594227739855321793133)
                    ·
                      refine ⟨2985597835402445745672425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7961594227739855321793133 2985597835402445745672425)
                      ·
                        rfl

theorem cell23_5814431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 2, 1, 1, 2, 3].length) (baseStart_5814431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5814431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5814431 prefixEnd_5814431 := by exact prefixLift 5814431
  have htrace : WordTrace (prefixWord ++ tailWord_5814431) baseStart_5814431 baseEnd_5814431 := by
    simpa [prefixWord, tailWord_5814431, baseEnd_5814431] using wordTrace_append hprefix tailTrace_5814431
  have hstable : (prefixWord ++ tailWord_5814431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5814431).length < 2 ^ (prefixWord ++ tailWord_5814431).sum := by decide
  have hdescent : baseEnd_5814431 < baseStart_5814431 := by decide
  rcases family_descends (prefixWord ++ tailWord_5814431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5814473 : List Nat := [1, 2, 1, 1, 2, 1, 1, 5, 9]
def baseStart_5814473 : Nat := 118140960795 + 5814473 * 2 ^ 59
def prefixEnd_5814473 : Nat := 4983230072969 + 3 ^ 40 * 5814473 * 2
def baseEnd_5814473 : Nat := 331735489065548286816359

theorem tailTrace_5814473 : CollatzResearch.WordTrace tailWord_5814473 prefixEnd_5814473 331735489065548286816359 := by
  unfold tailWord_5814473
  simp only [CollatzResearch.WordTrace]
  refine ⟨212071252664164828774120073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141380835109443219182746715 212071252664164828774120073)
  ·
    refine ⟨159053439498123621580590055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212071252664164828774120073 159053439498123621580590055)
    ·
      refine ⟨238580159247185432370885083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159053439498123621580590055 238580159247185432370885083)
      ·
        refine ⟨357870238870778148556327625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238580159247185432370885083 357870238870778148556327625)
        ·
          refine ⟨268402679153083611417245719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 357870238870778148556327625 268402679153083611417245719)
          ·
            refine ⟨402604018729625417125868579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 268402679153083611417245719 402604018729625417125868579)
            ·
              refine ⟨603906028094438125688802869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 402604018729625417125868579 603906028094438125688802869)
              ·
                refine ⟨56616190133853574283325269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 603906028094438125688802869 56616190133853574283325269)
                ·
                  refine ⟨331735489065548286816359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 56616190133853574283325269 331735489065548286816359)
                  ·
                    rfl

theorem cell23_5814473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 5, 9].length) (baseStart_5814473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5814473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5814473 prefixEnd_5814473 := by exact prefixLift 5814473
  have htrace : WordTrace (prefixWord ++ tailWord_5814473) baseStart_5814473 baseEnd_5814473 := by
    simpa [prefixWord, tailWord_5814473, baseEnd_5814473] using wordTrace_append hprefix tailTrace_5814473
  have hstable : (prefixWord ++ tailWord_5814473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5814473).length < 2 ^ (prefixWord ++ tailWord_5814473).sum := by decide
  have hdescent : baseEnd_5814473 < baseStart_5814473 := by decide
  rcases family_descends (prefixWord ++ tailWord_5814473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5814483 : List Nat := [1, 1, 1, 2, 1, 1, 1, 3, 3, 2, 7]
def baseStart_5814483 : Nat := 118140960795 + 5814483 * 2 ^ 59
def prefixEnd_5814483 : Nat := 4983230072969 + 3 ^ 40 * 5814483 * 2
def baseEnd_5814483 : Nat := 2985624536396479542222185

theorem tailTrace_5814483 : CollatzResearch.WordTrace tailWord_5814483 prefixEnd_5814483 2985624536396479542222185 := by
  unfold tailWord_5814483
  simp only [CollatzResearch.WordTrace]
  refine ⟨212071617394128600481984103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141381078262752400321322735 212071617394128600481984103)
  ·
    refine ⟨318107426091192900722976155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212071617394128600481984103 318107426091192900722976155)
    ·
      refine ⟨477161139136789351084464233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 318107426091192900722976155 477161139136789351084464233)
      ·
        refine ⟨357870854352592013313348175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 477161139136789351084464233 357870854352592013313348175)
        ·
          refine ⟨536806281528888019970022263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 357870854352592013313348175 536806281528888019970022263)
          ·
            refine ⟨805209422293332029955033395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 536806281528888019970022263 805209422293332029955033395)
            ·
              refine ⟨1207814133439998044932550093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 805209422293332029955033395 1207814133439998044932550093)
              ·
                refine ⟨452930300039999266849706285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1207814133439998044932550093 452930300039999266849706285)
                ·
                  refine ⟨169848862514999725068639857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 452930300039999266849706285 169848862514999725068639857)
                  ·
                    refine ⟨127386646886249793801479893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 169848862514999725068639857 127386646886249793801479893)
                    ·
                      refine ⟨2985624536396479542222185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 127386646886249793801479893 2985624536396479542222185)
                      ·
                        rfl

theorem cell23_5814483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 3, 2, 7].length) (baseStart_5814483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5814483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5814483 prefixEnd_5814483 := by exact prefixLift 5814483
  have htrace : WordTrace (prefixWord ++ tailWord_5814483) baseStart_5814483 baseEnd_5814483 := by
    simpa [prefixWord, tailWord_5814483, baseEnd_5814483] using wordTrace_append hprefix tailTrace_5814483
  have hstable : (prefixWord ++ tailWord_5814483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5814483).length < 2 ^ (prefixWord ++ tailWord_5814483).sum := by decide
  have hdescent : baseEnd_5814483 < baseStart_5814483 := by decide
  rcases family_descends (prefixWord ++ tailWord_5814483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5814518 : List Nat := [5, 1, 1, 1, 1, 1, 6, 1, 2, 2, 2]
def baseStart_5814518 : Nat := 118140960795 + 5814518 * 2 ^ 59
def prefixEnd_5814518 : Nat := 4983230072969 + 3 ^ 40 * 5814518 * 2
def baseEnd_5814518 : Nat := 2985642508219386905284525

theorem tailTrace_5814518 : CollatzResearch.WordTrace tailWord_5814518 prefixEnd_5814518 2985642508219386905284525 := by
  unfold tailWord_5814518
  simp only [CollatzResearch.WordTrace]
  refine ⟨13254555871812612591219263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 141381929299334534306338805 13254555871812612591219263)
  ·
    refine ⟨19881833807718918886828895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13254555871812612591219263 19881833807718918886828895)
    ·
      refine ⟨29822750711578378330243343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19881833807718918886828895 29822750711578378330243343)
      ·
        refine ⟨44734126067367567495365015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29822750711578378330243343 44734126067367567495365015)
        ·
          refine ⟨67101189101051351243047523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44734126067367567495365015 67101189101051351243047523)
          ·
            refine ⟨100651783651577026864571285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67101189101051351243047523 100651783651577026864571285)
            ·
              refine ⟨4718052358667673134276779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 100651783651577026864571285 4718052358667673134276779)
              ·
                refine ⟨7077078538001509701415169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4718052358667673134276779 7077078538001509701415169)
                ·
                  refine ⟨5307808903501132276061377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7077078538001509701415169 5307808903501132276061377)
                  ·
                    refine ⟨3980856677625849207046033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5307808903501132276061377 3980856677625849207046033)
                    ·
                      refine ⟨2985642508219386905284525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3980856677625849207046033 2985642508219386905284525)
                      ·
                        rfl

theorem cell23_5814518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 6, 1, 2, 2, 2].length) (baseStart_5814518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5814518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5814518 prefixEnd_5814518 := by exact prefixLift 5814518
  have htrace : WordTrace (prefixWord ++ tailWord_5814518) baseStart_5814518 baseEnd_5814518 := by
    simpa [prefixWord, tailWord_5814518, baseEnd_5814518] using wordTrace_append hprefix tailTrace_5814518
  have hstable : (prefixWord ++ tailWord_5814518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5814518).length < 2 ^ (prefixWord ++ tailWord_5814518).sum := by decide
  have hdescent : baseEnd_5814518 < baseStart_5814518 := by decide
  rcases family_descends (prefixWord ++ tailWord_5814518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5814537 : List Nat := [1, 2, 1, 1, 3, 5, 2, 1, 2, 5]
def baseStart_5814537 : Nat := 118140960795 + 5814537 * 2 ^ 59
def prefixEnd_5814537 : Nat := 4983230072969 + 3 ^ 40 * 5814537 * 2
def baseEnd_5814537 : Nat := 995217421450607443648979

theorem tailTrace_5814537 : CollatzResearch.WordTrace tailWord_5814537 prefixEnd_5814537 995217421450607443648979 := by
  unfold tailWord_5814537
  simp only [CollatzResearch.WordTrace]
  refine ⟨212073586935932967704449865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141382391290621978469633243 212073586935932967704449865)
  ·
    refine ⟨159055190201949725778337399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212073586935932967704449865 159055190201949725778337399)
    ·
      refine ⟨238582785302924588667506099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159055190201949725778337399 238582785302924588667506099)
      ·
        refine ⟨357874177954386883001259149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238582785302924588667506099 357874177954386883001259149)
        ·
          refine ⟨134202816732895081125472181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 357874177954386883001259149 134202816732895081125472181)
          ·
            refine ⟨12581514068708913855513017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 134202816732895081125472181 12581514068708913855513017)
            ·
              refine ⟨9436135551531685391634763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12581514068708913855513017 9436135551531685391634763)
              ·
                refine ⟨14154203327297528087452145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9436135551531685391634763 14154203327297528087452145)
                ·
                  refine ⟨10615652495473146065589109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14154203327297528087452145 10615652495473146065589109)
                  ·
                    refine ⟨995217421450607443648979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10615652495473146065589109 995217421450607443648979)
                    ·
                      rfl

theorem cell23_5814537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 2, 1, 2, 5].length) (baseStart_5814537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5814537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5814537 prefixEnd_5814537 := by exact prefixLift 5814537
  have htrace : WordTrace (prefixWord ++ tailWord_5814537) baseStart_5814537 baseEnd_5814537 := by
    simpa [prefixWord, tailWord_5814537, baseEnd_5814537] using wordTrace_append hprefix tailTrace_5814537
  have hstable : (prefixWord ++ tailWord_5814537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5814537).length < 2 ^ (prefixWord ++ tailWord_5814537).sum := by decide
  have hdescent : baseEnd_5814537 < baseStart_5814537 := by decide
  rcases family_descends (prefixWord ++ tailWord_5814537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5814558 : List Nat := [4, 3, 2, 1, 1, 1, 4, 2, 5]
def baseStart_5814558 : Nat := 118140960795 + 5814558 * 2 ^ 59
def prefixEnd_5814558 : Nat := 4983230072969 + 3 ^ 40 * 5814558 * 2
def baseEnd_5814558 : Nat := 331740338605062972087149

theorem tailTrace_5814558 : CollatzResearch.WordTrace tailWord_5814558 prefixEnd_5814558 331740338605062972087149 := by
  unfold tailWord_5814558
  simp only [CollatzResearch.WordTrace]
  refine ⟨26509294108607111036370541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 141382901912571258860642885 26509294108607111036370541)
  ·
    refine ⟨9940985290727666638638953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26509294108607111036370541 9940985290727666638638953)
    ·
      refine ⟨7455738968045749978979215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9940985290727666638638953 7455738968045749978979215)
      ·
        refine ⟨11183608452068624968468823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7455738968045749978979215 11183608452068624968468823)
        ·
          refine ⟨16775412678102937452703235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11183608452068624968468823 16775412678102937452703235)
          ·
            refine ⟨25163119017154406179054853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16775412678102937452703235 25163119017154406179054853)
            ·
              refine ⟨4718084815716451158572785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25163119017154406179054853 4718084815716451158572785)
              ·
                refine ⟨3538563611787338368929589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4718084815716451158572785 3538563611787338368929589)
                ·
                  refine ⟨331740338605062972087149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3538563611787338368929589 331740338605062972087149)
                  ·
                    rfl

theorem cell23_5814558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 4, 2, 5].length) (baseStart_5814558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5814558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5814558 prefixEnd_5814558 := by exact prefixLift 5814558
  have htrace : WordTrace (prefixWord ++ tailWord_5814558) baseStart_5814558 baseEnd_5814558 := by
    simpa [prefixWord, tailWord_5814558, baseEnd_5814558] using wordTrace_append hprefix tailTrace_5814558
  have hstable : (prefixWord ++ tailWord_5814558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5814558).length < 2 ^ (prefixWord ++ tailWord_5814558).sum := by decide
  have hdescent : baseEnd_5814558 < baseStart_5814558 := by decide
  rcases family_descends (prefixWord ++ tailWord_5814558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5814664 : List Nat := [2, 1, 3, 3, 1, 1, 1, 5, 1, 1, 4]
def baseStart_5814664 : Nat := 118140960795 + 5814664 * 2 ^ 59
def prefixEnd_5814664 : Nat := 4983230072969 + 3 ^ 40 * 5814664 * 2
def baseEnd_5814664 : Nat := 2985717476394943334058853

theorem tailTrace_5814664 : CollatzResearch.WordTrace tailWord_5814664 prefixEnd_5814664 2985717476394943334058853 := by
  unfold tailWord_5814664
  simp only [CollatzResearch.WordTrace]
  refine ⟨106039109503236434197161523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141385479337648578929548697 106039109503236434197161523)
  ·
    refine ⟨159058664254854651295742285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106039109503236434197161523 159058664254854651295742285)
    ·
      refine ⟨59646999095570494235903357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 159058664254854651295742285 59646999095570494235903357)
      ·
        refine ⟨22367624660838935338463759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59646999095570494235903357 22367624660838935338463759)
        ·
          refine ⟨33551436991258403007695639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22367624660838935338463759 33551436991258403007695639)
          ·
            refine ⟨50327155486887604511543459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33551436991258403007695639 50327155486887604511543459)
            ·
              refine ⟨75490733230331406767315189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50327155486887604511543459 75490733230331406767315189)
              ·
                refine ⟨7077256240343569384435799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 75490733230331406767315189 7077256240343569384435799)
                ·
                  refine ⟨10615884360515354076653699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7077256240343569384435799 10615884360515354076653699)
                  ·
                    refine ⟨15923826540773031114980549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10615884360515354076653699 15923826540773031114980549)
                    ·
                      refine ⟨2985717476394943334058853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15923826540773031114980549 2985717476394943334058853)
                      ·
                        rfl

theorem cell23_5814664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 5, 1, 1, 4].length) (baseStart_5814664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5814664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5814664 prefixEnd_5814664 := by exact prefixLift 5814664
  have htrace : WordTrace (prefixWord ++ tailWord_5814664) baseStart_5814664 baseEnd_5814664 := by
    simpa [prefixWord, tailWord_5814664, baseEnd_5814664] using wordTrace_append hprefix tailTrace_5814664
  have hstable : (prefixWord ++ tailWord_5814664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5814664).length < 2 ^ (prefixWord ++ tailWord_5814664).sum := by decide
  have hdescent : baseEnd_5814664 < baseStart_5814664 := by decide
  rcases family_descends (prefixWord ++ tailWord_5814664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5814667 : List Nat := [1, 1, 1, 1, 4, 4, 1, 3, 1, 1, 5]
def baseStart_5814667 : Nat := 118140960795 + 5814667 * 2 ^ 59
def prefixEnd_5814667 : Nat := 4983230072969 + 3 ^ 40 * 5814667 * 2
def baseEnd_5814667 : Nat := 2985719016836906822321339

theorem tailTrace_5814667 : CollatzResearch.WordTrace tailWord_5814667 prefixEnd_5814667 2985719016836906822321339 := by
  unfold tailWord_5814667
  simp only [CollatzResearch.WordTrace]
  refine ⟨212078328425461999906682255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141385552283641333271121503 212078328425461999906682255)
  ·
    refine ⟨318117492638192999860023383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212078328425461999906682255 318117492638192999860023383)
    ·
      refine ⟨477176238957289499790035075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 318117492638192999860023383 477176238957289499790035075)
      ·
        refine ⟨715764358435934249685052613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 477176238957289499790035075 715764358435934249685052613)
        ·
          refine ⟨134205817206737671815947365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 715764358435934249685052613 134205817206737671815947365)
          ·
            refine ⟨25163590726263313465490131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 134205817206737671815947365 25163590726263313465490131)
            ·
              refine ⟨37745386089394970198235197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25163590726263313465490131 37745386089394970198235197)
              ·
                refine ⟨14154519783523113824338199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37745386089394970198235197 14154519783523113824338199)
                ·
                  refine ⟨21231779675284670736507299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14154519783523113824338199 21231779675284670736507299)
                  ·
                    refine ⟨31847669512927006104760949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21231779675284670736507299 31847669512927006104760949)
                    ·
                      refine ⟨2985719016836906822321339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31847669512927006104760949 2985719016836906822321339)
                      ·
                        rfl

theorem cell23_5814667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 3, 1, 1, 5].length) (baseStart_5814667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5814667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5814667 prefixEnd_5814667 := by exact prefixLift 5814667
  have htrace : WordTrace (prefixWord ++ tailWord_5814667) baseStart_5814667 baseEnd_5814667 := by
    simpa [prefixWord, tailWord_5814667, baseEnd_5814667] using wordTrace_append hprefix tailTrace_5814667
  have hstable : (prefixWord ++ tailWord_5814667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5814667).length < 2 ^ (prefixWord ++ tailWord_5814667).sum := by decide
  have hdescent : baseEnd_5814667 < baseStart_5814667 := by decide
  rcases family_descends (prefixWord ++ tailWord_5814667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5814687 : List Nat := [1, 1, 2, 5, 1, 1, 4, 8]
def baseStart_5814687 : Nat := 118140960795 + 5814687 * 2 ^ 59
def prefixEnd_5814687 : Nat := 4983230072969 + 3 ^ 40 * 5814687 * 2
def baseEnd_5814687 : Nat := 110582566164814694224861

theorem tailTrace_5814687 : CollatzResearch.WordTrace tailWord_5814687 prefixEnd_5814687 110582566164814694224861 := by
  unfold tailWord_5814687
  simp only [CollatzResearch.WordTrace]
  refine ⟨212079057885389543322410315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141386038590259695548273543 212079057885389543322410315)
  ·
    refine ⟨318118586828084314983615473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212079057885389543322410315 318118586828084314983615473)
    ·
      refine ⟨238588940121063236237711605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 318118586828084314983615473 238588940121063236237711605)
      ·
        refine ⟨22367713136349678397285463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 238588940121063236237711605 22367713136349678397285463)
        ·
          refine ⟨33551569704524517595928195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22367713136349678397285463 33551569704524517595928195)
          ·
            refine ⟨50327354556786776393892293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33551569704524517595928195 50327354556786776393892293)
            ·
              refine ⟨9436378979397520573854805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50327354556786776393892293 9436378979397520573854805)
              ·
                refine ⟨110582566164814694224861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9436378979397520573854805 110582566164814694224861)
                ·
                  rfl

theorem cell23_5814687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 4, 8].length) (baseStart_5814687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5814687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5814687 prefixEnd_5814687 := by exact prefixLift 5814687
  have htrace : WordTrace (prefixWord ++ tailWord_5814687) baseStart_5814687 baseEnd_5814687 := by
    simpa [prefixWord, tailWord_5814687, baseEnd_5814687] using wordTrace_append hprefix tailTrace_5814687
  have hstable : (prefixWord ++ tailWord_5814687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5814687).length < 2 ^ (prefixWord ++ tailWord_5814687).sum := by decide
  have hdescent : baseEnd_5814687 < baseStart_5814687 := by decide
  rcases family_descends (prefixWord ++ tailWord_5814687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5814691 : List Nat := [1, 1, 1, 4, 1, 4, 4, 1, 2, 4]
def baseStart_5814691 : Nat := 118140960795 + 5814691 * 2 ^ 59
def prefixEnd_5814691 : Nat := 4983230072969 + 3 ^ 40 * 5814691 * 2
def baseEnd_5814691 : Nat := 995243780124204909473743

theorem tailTrace_5814691 : CollatzResearch.WordTrace tailWord_5814691 prefixEnd_5814691 995243780124204909473743 := by
  unfold tailWord_5814691
  simp only [CollatzResearch.WordTrace]
  refine ⟨212079203777375052005555927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141386135851583368003703951 212079203777375052005555927)
  ·
    refine ⟨318118805666062578008333891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212079203777375052005555927 318118805666062578008333891)
    ·
      refine ⟨477178208499093867012500837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 318118805666062578008333891 477178208499093867012500837)
      ·
        refine ⟨89470914093580100064843907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 477178208499093867012500837 89470914093580100064843907)
        ·
          refine ⟨134206371140370150097265861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89470914093580100064843907 134206371140370150097265861)
          ·
            refine ⟨25163694588819403143237349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 134206371140370150097265861 25163694588819403143237349)
            ·
              refine ⟨4718192735403638089357003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25163694588819403143237349 4718192735403638089357003)
              ·
                refine ⟨7077289103105457134035505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4718192735403638089357003 7077289103105457134035505)
                ·
                  refine ⟨5307966827329092850526629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7077289103105457134035505 5307966827329092850526629)
                  ·
                    refine ⟨995243780124204909473743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5307966827329092850526629 995243780124204909473743)
                    ·
                      rfl

theorem cell23_5814691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 4, 1, 2, 4].length) (baseStart_5814691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5814691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5814691 prefixEnd_5814691 := by exact prefixLift 5814691
  have htrace : WordTrace (prefixWord ++ tailWord_5814691) baseStart_5814691 baseEnd_5814691 := by
    simpa [prefixWord, tailWord_5814691, baseEnd_5814691] using wordTrace_append hprefix tailTrace_5814691
  have hstable : (prefixWord ++ tailWord_5814691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5814691).length < 2 ^ (prefixWord ++ tailWord_5814691).sum := by decide
  have hdescent : baseEnd_5814691 < baseStart_5814691 := by decide
  rcases family_descends (prefixWord ++ tailWord_5814691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5814697 : List Nat := [1, 2, 1, 1, 1, 1, 3, 2, 5, 3, 3]
def baseStart_5814697 : Nat := 118140960795 + 5814697 * 2 ^ 59
def prefixEnd_5814697 : Nat := 4983230072969 + 3 ^ 40 * 5814697 * 2
def baseEnd_5814697 : Nat := 2985734421256541704946201

theorem tailTrace_5814697 : CollatzResearch.WordTrace tailWord_5814697 prefixEnd_5814697 2985734421256541704946201 := by
  unfold tailWord_5814697
  simp only [CollatzResearch.WordTrace]
  refine ⟨212079422615353315030274345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141386281743568876686849563 212079422615353315030274345)
  ·
    refine ⟨159059566961514986272705759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212079422615353315030274345 159059566961514986272705759)
    ·
      refine ⟨238589350442272479409058639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159059566961514986272705759 238589350442272479409058639)
      ·
        refine ⟨357884025663408719113587959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238589350442272479409058639 357884025663408719113587959)
        ·
          refine ⟨536826038495113078670381939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 357884025663408719113587959 536826038495113078670381939)
          ·
            refine ⟨805239057742669618005572909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 536826038495113078670381939 805239057742669618005572909)
            ·
              refine ⟨301964646653501106752089841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 805239057742669618005572909 301964646653501106752089841)
              ·
                refine ⟨226473484990125830064067381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 301964646653501106752089841 226473484990125830064067381)
                ·
                  refine ⟨21231889217824296568506317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 226473484990125830064067381 21231889217824296568506317)
                  ·
                    refine ⟨7961958456684111213189869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21231889217824296568506317 7961958456684111213189869)
                    ·
                      refine ⟨2985734421256541704946201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7961958456684111213189869 2985734421256541704946201)
                      ·
                        rfl

theorem cell23_5814697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 5, 3, 3].length) (baseStart_5814697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5814697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5814697 prefixEnd_5814697 := by exact prefixLift 5814697
  have htrace : WordTrace (prefixWord ++ tailWord_5814697) baseStart_5814697 baseEnd_5814697 := by
    simpa [prefixWord, tailWord_5814697, baseEnd_5814697] using wordTrace_append hprefix tailTrace_5814697
  have hstable : (prefixWord ++ tailWord_5814697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5814697).length < 2 ^ (prefixWord ++ tailWord_5814697).sum := by decide
  have hdescent : baseEnd_5814697 < baseStart_5814697 := by decide
  rcases family_descends (prefixWord ++ tailWord_5814697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5814708 : List Nat := [2, 5, 2, 2, 1, 1, 1, 2, 1, 6]
def baseStart_5814708 : Nat := 118140960795 + 5814708 * 2 ^ 59
def prefixEnd_5814708 : Nat := 4983230072969 + 3 ^ 40 * 5814708 * 2
def baseEnd_5814708 : Nat := 995246689847913720636217

theorem tailTrace_5814708 : CollatzResearch.WordTrace tailWord_5814708 prefixEnd_5814708 995246689847913720636217 := by
  unfold tailWord_5814708
  simp only [CollatzResearch.WordTrace]
  refine ⟨106039911909156731954462389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141386549212208975939283185 106039911909156731954462389)
  ·
    refine ⟨9941241741483443620730849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 106039911909156731954462389 9941241741483443620730849)
    ·
      refine ⟨7455931306112582715548137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9941241741483443620730849 7455931306112582715548137)
      ·
        refine ⟨5591948479584437036661103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7455931306112582715548137 5591948479584437036661103)
        ·
          refine ⟨8387922719376655554991655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5591948479584437036661103 8387922719376655554991655)
          ·
            refine ⟨12581884079064983332487483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8387922719376655554991655 12581884079064983332487483)
            ·
              refine ⟨18872826118597474998731225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12581884079064983332487483 18872826118597474998731225)
              ·
                refine ⟨14154619588948106249048419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18872826118597474998731225 14154619588948106249048419)
                ·
                  refine ⟨21231929383422159373572629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14154619588948106249048419 21231929383422159373572629)
                  ·
                    refine ⟨995246689847913720636217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21231929383422159373572629 995246689847913720636217)
                    ·
                      rfl

theorem cell23_5814708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_5814708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5814708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5814708 prefixEnd_5814708 := by exact prefixLift 5814708
  have htrace : WordTrace (prefixWord ++ tailWord_5814708) baseStart_5814708 baseEnd_5814708 := by
    simpa [prefixWord, tailWord_5814708, baseEnd_5814708] using wordTrace_append hprefix tailTrace_5814708
  have hstable : (prefixWord ++ tailWord_5814708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5814708).length < 2 ^ (prefixWord ++ tailWord_5814708).sum := by decide
  have hdescent : baseEnd_5814708 < baseStart_5814708 := by decide
  rcases family_descends (prefixWord ++ tailWord_5814708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5814714 : List Nat := [3, 1, 1, 1, 2, 1, 1, 3, 6, 1, 3]
def baseStart_5814714 : Nat := 118140960795 + 5814714 * 2 ^ 59
def prefixEnd_5814714 : Nat := 4983230072969 + 3 ^ 40 * 5814714 * 2
def baseEnd_5814714 : Nat := 2985743150427668138433623

theorem tailTrace_5814714 : CollatzResearch.WordTrace tailWord_5814714 prefixEnd_5814714 2985743150427668138433623 := by
  unfold tailWord_5814714
  simp only [CollatzResearch.WordTrace]
  refine ⟨53020010664072931733410799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141386695104194484622428797 53020010664072931733410799)
  ·
    refine ⟨79530015996109397600116199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53020010664072931733410799 79530015996109397600116199)
    ·
      refine ⟨119295023994164096400174299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79530015996109397600116199 119295023994164096400174299)
      ·
        refine ⟨178942535991246144600261449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119295023994164096400174299 178942535991246144600261449)
        ·
          refine ⟨134206901993434608450196087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 178942535991246144600261449 134206901993434608450196087)
          ·
            refine ⟨201310352990151912675294131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134206901993434608450196087 201310352990151912675294131)
            ·
              refine ⟨301965529485227869012941197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 201310352990151912675294131 301965529485227869012941197)
              ·
                refine ⟨113237073556960450879852949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 301965529485227869012941197 113237073556960450879852949)
                ·
                  refine ⟨5307987822982521134993107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 113237073556960450879852949 5307987822982521134993107)
                  ·
                    refine ⟨7961981734473781702489661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5307987822982521134993107 7961981734473781702489661)
                    ·
                      refine ⟨2985743150427668138433623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7961981734473781702489661 2985743150427668138433623)
                      ·
                        rfl

theorem cell23_5814714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 3, 6, 1, 3].length) (baseStart_5814714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5814714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5814714 prefixEnd_5814714 := by exact prefixLift 5814714
  have htrace : WordTrace (prefixWord ++ tailWord_5814714) baseStart_5814714 baseEnd_5814714 := by
    simpa [prefixWord, tailWord_5814714, baseEnd_5814714] using wordTrace_append hprefix tailTrace_5814714
  have hstable : (prefixWord ++ tailWord_5814714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5814714).length < 2 ^ (prefixWord ++ tailWord_5814714).sum := by decide
  have hdescent : baseEnd_5814714 < baseStart_5814714 := by decide
  rcases family_descends (prefixWord ++ tailWord_5814714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5814721 : List Nat := [1, 2, 7, 1, 1, 11]
def baseStart_5814721 : Nat := 118140960795 + 5814721 * 2 ^ 59
def prefixEnd_5814721 : Nat := 4983230072969 + 3 ^ 40 * 5814721 * 2
def baseEnd_5814721 : Nat := 12287023641120368769737

theorem tailTrace_5814721 : CollatzResearch.WordTrace tailWord_5814721 prefixEnd_5814721 12287023641120368769737 := by
  unfold tailWord_5814721
  simp only [CollatzResearch.WordTrace]
  refine ⟨212080297967266367129148017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141386865311510911419432011 212080297967266367129148017)
  ·
    refine ⟨159060223475449775346861013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212080297967266367129148017 159060223475449775346861013)
    ·
      refine ⟨3727973987705854109692055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 159060223475449775346861013 3727973987705854109692055)
      ·
        refine ⟨5591960981558781164538083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3727973987705854109692055 5591960981558781164538083)
        ·
          refine ⟨8387941472338171746807125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5591960981558781164538083 8387941472338171746807125)
          ·
            refine ⟨12287023641120368769737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 8387941472338171746807125 12287023641120368769737)
            ·
              rfl

theorem cell23_5814721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 11].length) (baseStart_5814721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5814721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5814721 prefixEnd_5814721 := by exact prefixLift 5814721
  have htrace : WordTrace (prefixWord ++ tailWord_5814721) baseStart_5814721 baseEnd_5814721 := by
    simpa [prefixWord, tailWord_5814721, baseEnd_5814721] using wordTrace_append hprefix tailTrace_5814721
  have hstable : (prefixWord ++ tailWord_5814721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5814721).length < 2 ^ (prefixWord ++ tailWord_5814721).sum := by decide
  have hdescent : baseEnd_5814721 < baseStart_5814721 := by decide
  rcases family_descends (prefixWord ++ tailWord_5814721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5814738 : List Nat := [3, 2, 2, 4, 2, 1, 1, 8]
def baseStart_5814738 : Nat := 118140960795 + 5814738 * 2 ^ 59
def prefixEnd_5814738 : Nat := 4983230072969 + 3 ^ 40 * 5814738 * 2
def baseEnd_5814738 : Nat := 110583536072717631279019

theorem tailTrace_5814738 : CollatzResearch.WordTrace tailWord_5814738 prefixEnd_5814738 110583536072717631279019 := by
  unfold tailWord_5814738
  simp only [CollatzResearch.WordTrace]
  refine ⟨53020229502051194758129217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141387278672136519355011245 53020229502051194758129217)
  ·
    refine ⟨39765172126538396068596913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53020229502051194758129217 39765172126538396068596913)
    ·
      refine ⟨29823879094903797051447685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39765172126538396068596913 29823879094903797051447685)
      ·
        refine ⟨5591977330294461947146441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29823879094903797051447685 5591977330294461947146441)
        ·
          refine ⟨4193982997720846460359831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5591977330294461947146441 4193982997720846460359831)
          ·
            refine ⟨6290974496581269690539747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4193982997720846460359831 6290974496581269690539747)
            ·
              refine ⟨9436461744871904535809621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6290974496581269690539747 9436461744871904535809621)
              ·
                refine ⟨110583536072717631279019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9436461744871904535809621 110583536072717631279019)
                ·
                  rfl

theorem cell23_5814738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 1, 8].length) (baseStart_5814738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5814738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5814738 prefixEnd_5814738 := by exact prefixLift 5814738
  have htrace : WordTrace (prefixWord ++ tailWord_5814738) baseStart_5814738 baseEnd_5814738 := by
    simpa [prefixWord, tailWord_5814738, baseEnd_5814738] using wordTrace_append hprefix tailTrace_5814738
  have hstable : (prefixWord ++ tailWord_5814738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5814738).length < 2 ^ (prefixWord ++ tailWord_5814738).sum := by decide
  have hdescent : baseEnd_5814738 < baseStart_5814738 := by decide
  rcases family_descends (prefixWord ++ tailWord_5814738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5814741 : List Nat := [1, 3, 2, 3, 1, 2, 1, 2, 3, 3, 2]
def baseStart_5814741 : Nat := 118140960795 + 5814741 * 2 ^ 59
def prefixEnd_5814741 : Nat := 4983230072969 + 3 ^ 40 * 5814741 * 2
def baseEnd_5814741 : Nat := 2985757014405339532795999

theorem tailTrace_5814741 : CollatzResearch.WordTrace tailWord_5814741 prefixEnd_5814741 2985757014405339532795999 := by
  unfold tailWord_5814741
  simp only [CollatzResearch.WordTrace]
  refine ⟨212081027427193910544876077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141387351618129273696584051 212081027427193910544876077)
  ·
    refine ⟨79530385285197716454328529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 212081027427193910544876077 79530385285197716454328529)
    ·
      refine ⟨59647788963898287340746397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79530385285197716454328529 59647788963898287340746397)
      ·
        refine ⟨22367920861461857752779899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59647788963898287340746397 22367920861461857752779899)
        ·
          refine ⟨33551881292192786629169849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22367920861461857752779899 33551881292192786629169849)
          ·
            refine ⟨25163910969144589971877387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33551881292192786629169849 25163910969144589971877387)
            ·
              refine ⟨37745866453716884957816081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25163910969144589971877387 37745866453716884957816081)
              ·
                refine ⟨28309399840287663718362061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37745866453716884957816081 28309399840287663718362061)
                ·
                  refine ⟨10616024940107873894385773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28309399840287663718362061 10616024940107873894385773)
                  ·
                    refine ⟨3981009352540452710394665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10616024940107873894385773 3981009352540452710394665)
                    ·
                      refine ⟨2985757014405339532795999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3981009352540452710394665 2985757014405339532795999)
                      ·
                        rfl

theorem cell23_5814741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 2, 3, 3, 2].length) (baseStart_5814741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5814741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5814741 prefixEnd_5814741 := by exact prefixLift 5814741
  have htrace : WordTrace (prefixWord ++ tailWord_5814741) baseStart_5814741 baseEnd_5814741 := by
    simpa [prefixWord, tailWord_5814741, baseEnd_5814741] using wordTrace_append hprefix tailTrace_5814741
  have hstable : (prefixWord ++ tailWord_5814741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5814741).length < 2 ^ (prefixWord ++ tailWord_5814741).sum := by decide
  have hdescent : baseEnd_5814741 < baseStart_5814741 := by decide
  rcases family_descends (prefixWord ++ tailWord_5814741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5814767 : List Nat := [1, 1, 2, 1, 4, 1, 1, 1, 3, 4, 4]
def baseStart_5814767 : Nat := 118140960795 + 5814767 * 2 ^ 59
def prefixEnd_5814767 : Nat := 4983230072969 + 3 ^ 40 * 5814767 * 2
def baseEnd_5814767 : Nat := 2985770364902356431070879

theorem tailTrace_5814767 : CollatzResearch.WordTrace tailWord_5814767 prefixEnd_5814767 2985770364902356431070879 := by
  unfold tailWord_5814767
  simp only [CollatzResearch.WordTrace]
  refine ⟨212081975725099716985322555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141387983816733144656881703 212081975725099716985322555)
  ·
    refine ⟨318122963587649575477983833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212081975725099716985322555 318122963587649575477983833)
    ·
      refine ⟨238592222690737181608487875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 318122963587649575477983833 238592222690737181608487875)
      ·
        refine ⟨357888334036105772412731813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238592222690737181608487875 357888334036105772412731813)
        ·
          refine ⟨67104062631769832327387215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 357888334036105772412731813 67104062631769832327387215)
          ·
            refine ⟨100656093947654748491080823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67104062631769832327387215 100656093947654748491080823)
            ·
              refine ⟨150984140921482122736621235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100656093947654748491080823 150984140921482122736621235)
              ·
                refine ⟨226476211382223184104931853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 150984140921482122736621235 226476211382223184104931853)
                ·
                  refine ⟨84928579268333694039349445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 226476211382223184104931853 84928579268333694039349445)
                  ·
                    refine ⟨15924108612812567632378021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 84928579268333694039349445 15924108612812567632378021)
                    ·
                      refine ⟨2985770364902356431070879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15924108612812567632378021 2985770364902356431070879)
                      ·
                        rfl

theorem cell23_5814767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 3, 4, 4].length) (baseStart_5814767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5814767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5814767 prefixEnd_5814767 := by exact prefixLift 5814767
  have htrace : WordTrace (prefixWord ++ tailWord_5814767) baseStart_5814767 baseEnd_5814767 := by
    simpa [prefixWord, tailWord_5814767, baseEnd_5814767] using wordTrace_append hprefix tailTrace_5814767
  have hstable : (prefixWord ++ tailWord_5814767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5814767).length < 2 ^ (prefixWord ++ tailWord_5814767).sum := by decide
  have hdescent : baseEnd_5814767 < baseStart_5814767 := by decide
  rcases family_descends (prefixWord ++ tailWord_5814767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5814771 : List Nat := [1, 1, 1, 2, 2, 2, 4, 2, 4, 2, 2]
def baseStart_5814771 : Nat := 118140960795 + 5814771 * 2 ^ 59
def prefixEnd_5814771 : Nat := 4983230072969 + 3 ^ 40 * 5814771 * 2
def baseEnd_5814771 : Nat := 2985772418824974415420861

theorem tailTrace_5814771 : CollatzResearch.WordTrace tailWord_5814771 prefixEnd_5814771 2985772418824974415420861 := by
  unfold tailWord_5814771
  simp only [CollatzResearch.WordTrace]
  refine ⟨212082121617085225668468167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141388081078056817112312111 212082121617085225668468167)
  ·
    refine ⟨318123182425627838502702251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212082121617085225668468167 318123182425627838502702251)
    ·
      refine ⟨477184773638441757754053377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 318123182425627838502702251 477184773638441757754053377)
      ·
        refine ⟨357888580228831318315540033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 477184773638441757754053377 357888580228831318315540033)
        ·
          refine ⟨268416435171623488736655025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 357888580228831318315540033 268416435171623488736655025)
          ·
            refine ⟨201312326378717616552491269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 268416435171623488736655025 201312326378717616552491269)
            ·
              refine ⟨37746061196009553103592113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 201312326378717616552491269 37746061196009553103592113)
              ·
                refine ⟨28309545897007164827694085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37746061196009553103592113 28309545897007164827694085)
                ·
                  refine ⟨5308039855688843405192641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28309545897007164827694085 5308039855688843405192641)
                  ·
                    refine ⟨3981029891766632553894481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5308039855688843405192641 3981029891766632553894481)
                    ·
                      refine ⟨2985772418824974415420861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3981029891766632553894481 2985772418824974415420861)
                      ·
                        rfl

theorem cell23_5814771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 2, 4, 2, 2].length) (baseStart_5814771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5814771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5814771 prefixEnd_5814771 := by exact prefixLift 5814771
  have htrace : WordTrace (prefixWord ++ tailWord_5814771) baseStart_5814771 baseEnd_5814771 := by
    simpa [prefixWord, tailWord_5814771, baseEnd_5814771] using wordTrace_append hprefix tailTrace_5814771
  have hstable : (prefixWord ++ tailWord_5814771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5814771).length < 2 ^ (prefixWord ++ tailWord_5814771).sum := by decide
  have hdescent : baseEnd_5814771 < baseStart_5814771 := by decide
  rcases family_descends (prefixWord ++ tailWord_5814771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5814774 : List Nat := [5, 1, 1, 1, 2, 1, 2, 1, 1, 3, 5]
def baseStart_5814774 : Nat := 118140960795 + 5814774 * 2 ^ 59
def prefixEnd_5814774 : Nat := 4983230072969 + 3 ^ 40 * 5814774 * 2
def baseEnd_5814774 : Nat := 2985773959266937903683347

theorem tailTrace_5814774 : CollatzResearch.WordTrace tailWord_5814774 prefixEnd_5814774 2985773959266937903683347 := by
  unfold tailWord_5814774
  simp only [CollatzResearch.WordTrace]
  refine ⟨13255139439754647323801711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 141388154024049571453884917 13255139439754647323801711)
  ·
    refine ⟨19882709159631970985702567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13255139439754647323801711 19882709159631970985702567)
    ·
      refine ⟨29824063739447956478553851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19882709159631970985702567 29824063739447956478553851)
      ·
        refine ⟨44736095609171934717830777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29824063739447956478553851 44736095609171934717830777)
        ·
          refine ⟨33552071706878951038373083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44736095609171934717830777 33552071706878951038373083)
          ·
            refine ⟨50328107560318426557559625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33552071706878951038373083 50328107560318426557559625)
            ·
              refine ⟨37746080670238819918169719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50328107560318426557559625 37746080670238819918169719)
              ·
                refine ⟨56619121005358229877254579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37746080670238819918169719 56619121005358229877254579)
                ·
                  refine ⟨84928681508037344815881869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56619121005358229877254579 84928681508037344815881869)
                  ·
                    refine ⟨31848255565514004305955701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 84928681508037344815881869 31848255565514004305955701)
                    ·
                      refine ⟨2985773959266937903683347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31848255565514004305955701 2985773959266937903683347)
                      ·
                        rfl

theorem cell23_5814774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 1, 1, 3, 5].length) (baseStart_5814774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5814774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5814774 prefixEnd_5814774 := by exact prefixLift 5814774
  have htrace : WordTrace (prefixWord ++ tailWord_5814774) baseStart_5814774 baseEnd_5814774 := by
    simpa [prefixWord, tailWord_5814774, baseEnd_5814774] using wordTrace_append hprefix tailTrace_5814774
  have hstable : (prefixWord ++ tailWord_5814774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5814774).length < 2 ^ (prefixWord ++ tailWord_5814774).sum := by decide
  have hdescent : baseEnd_5814774 < baseStart_5814774 := by decide
  rcases family_descends (prefixWord ++ tailWord_5814774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5814794 : List Nat := [3, 1, 2, 2, 2, 1, 4, 1, 7]
def baseStart_5814794 : Nat := 118140960795 + 5814794 * 2 ^ 59
def prefixEnd_5814794 : Nat := 4983230072969 + 3 ^ 40 * 5814794 * 2
def baseEnd_5814794 : Nat := 331753803208891980603695

theorem tailTrace_5814794 : CollatzResearch.WordTrace tailWord_5814794 prefixEnd_5814794 331753803208891980603695 := by
  unfold tailWord_5814794
  simp only [CollatzResearch.WordTrace]
  refine ⟨53020740124000475149138859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141388640330667933731036957 53020740124000475149138859)
  ·
    refine ⟨79531110186000712723708289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53020740124000475149138859 79531110186000712723708289)
    ·
      refine ⟨59648332639500534542781217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79531110186000712723708289 59648332639500534542781217)
      ·
        refine ⟨44736249479625400907085913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59648332639500534542781217 44736249479625400907085913)
        ·
          refine ⟨33552187109719050680314435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44736249479625400907085913 33552187109719050680314435)
          ·
            refine ⟨50328280664578576020471653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33552187109719050680314435 50328280664578576020471653)
            ·
              refine ⟨9436552624608483003838435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50328280664578576020471653 9436552624608483003838435)
              ·
                refine ⟨14154828936912724505757653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9436552624608483003838435 14154828936912724505757653)
                ·
                  refine ⟨331753803208891980603695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14154828936912724505757653 331753803208891980603695)
                  ·
                    rfl

theorem cell23_5814794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 4, 1, 7].length) (baseStart_5814794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5814794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5814794 prefixEnd_5814794 := by exact prefixLift 5814794
  have htrace : WordTrace (prefixWord ++ tailWord_5814794) baseStart_5814794 baseEnd_5814794 := by
    simpa [prefixWord, tailWord_5814794, baseEnd_5814794] using wordTrace_append hprefix tailTrace_5814794
  have hstable : (prefixWord ++ tailWord_5814794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5814794).length < 2 ^ (prefixWord ++ tailWord_5814794).sum := by decide
  have hdescent : baseEnd_5814794 < baseStart_5814794 := by decide
  rcases family_descends (prefixWord ++ tailWord_5814794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5814805 : List Nat := [1, 3, 2, 1, 3, 1, 5, 1, 2, 2, 2]
def baseStart_5814805 : Nat := 118140960795 + 5814805 * 2 ^ 59
def prefixEnd_5814805 : Nat := 4983230072969 + 3 ^ 40 * 5814805 * 2
def baseEnd_5814805 : Nat := 2985789877167227282395705

theorem tailTrace_5814805 : CollatzResearch.WordTrace tailWord_5814805 prefixEnd_5814805 2985789877167227282395705 := by
  unfold tailWord_5814805
  simp only [CollatzResearch.WordTrace]
  refine ⟨212083361698962049475205869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141388907799308032983470579 212083361698962049475205869)
  ·
    refine ⟨79531260637110768553202201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 212083361698962049475205869 79531260637110768553202201)
    ·
      refine ⟨59648445477833076414901651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79531260637110768553202201 59648445477833076414901651)
      ·
        refine ⟨89472668216749614622352477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59648445477833076414901651 89472668216749614622352477)
        ·
          refine ⟨33552250581281105483382179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89472668216749614622352477 33552250581281105483382179)
          ·
            refine ⟨50328375871921658225073269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33552250581281105483382179 50328375871921658225073269)
            ·
              refine ⟨4718285237992655458600619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50328375871921658225073269 4718285237992655458600619)
              ·
                refine ⟨7077427856988983187900929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4718285237992655458600619 7077427856988983187900929)
                ·
                  refine ⟨5308070892741737390925697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7077427856988983187900929 5308070892741737390925697)
                  ·
                    refine ⟨3981053169556303043194273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5308070892741737390925697 3981053169556303043194273)
                    ·
                      refine ⟨2985789877167227282395705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3981053169556303043194273 2985789877167227282395705)
                      ·
                        rfl

theorem cell23_5814805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 5, 1, 2, 2, 2].length) (baseStart_5814805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5814805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5814805 prefixEnd_5814805 := by exact prefixLift 5814805
  have htrace : WordTrace (prefixWord ++ tailWord_5814805) baseStart_5814805 baseEnd_5814805 := by
    simpa [prefixWord, tailWord_5814805, baseEnd_5814805] using wordTrace_append hprefix tailTrace_5814805
  have hstable : (prefixWord ++ tailWord_5814805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5814805).length < 2 ^ (prefixWord ++ tailWord_5814805).sum := by decide
  have hdescent : baseEnd_5814805 < baseStart_5814805 := by decide
  rcases family_descends (prefixWord ++ tailWord_5814805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5814864 : List Nat := [2, 1, 1, 1, 1, 3, 2, 4, 1, 4, 3]
def baseStart_5814864 : Nat := 118140960795 + 5814864 * 2 ^ 59
def prefixEnd_5814864 : Nat := 4983230072969 + 3 ^ 40 * 5814864 * 2
def baseEnd_5814864 : Nat := 2985820172525842551557933

theorem tailTrace_5814864 : CollatzResearch.WordTrace tailWord_5814864 prefixEnd_5814864 2985820172525842551557933 := by
  unfold tailWord_5814864
  simp only [CollatzResearch.WordTrace]
  refine ⟨106042756802874151275801823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141390342403832201701069097 106042756802874151275801823)
  ·
    refine ⟨159064135204311226913702735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106042756802874151275801823 159064135204311226913702735)
    ·
      refine ⟨238596202806466840370554103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159064135204311226913702735 238596202806466840370554103)
      ·
        refine ⟨357894304209700260555831155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238596202806466840370554103 357894304209700260555831155)
        ·
          refine ⟨536841456314550390833746733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 357894304209700260555831155 536841456314550390833746733)
          ·
            refine ⟨201315546117956396562655025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 536841456314550390833746733 201315546117956396562655025)
            ·
              refine ⟨150986659588467297421991269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 201315546117956396562655025 150986659588467297421991269)
              ·
                refine ⟨28309998672837618266623363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 150986659588467297421991269 28309998672837618266623363)
                ·
                  refine ⟨42464998009256427399935045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28309998672837618266623363 42464998009256427399935045)
                  ·
                    refine ⟨7962187126735580137487821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42464998009256427399935045 7962187126735580137487821)
                    ·
                      refine ⟨2985820172525842551557933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7962187126735580137487821 2985820172525842551557933)
                      ·
                        rfl

theorem cell23_5814864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 4, 1, 4, 3].length) (baseStart_5814864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5814864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5814864 prefixEnd_5814864 := by exact prefixLift 5814864
  have htrace : WordTrace (prefixWord ++ tailWord_5814864) baseStart_5814864 baseEnd_5814864 := by
    simpa [prefixWord, tailWord_5814864, baseEnd_5814864] using wordTrace_append hprefix tailTrace_5814864
  have hstable : (prefixWord ++ tailWord_5814864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5814864).length < 2 ^ (prefixWord ++ tailWord_5814864).sum := by decide
  have hdescent : baseEnd_5814864 < baseStart_5814864 := by decide
  rcases family_descends (prefixWord ++ tailWord_5814864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5814881 : List Nat := [1, 2, 3, 1, 1, 4, 1, 3, 2, 2, 3]
def baseStart_5814881 : Nat := 118140960795 + 5814881 * 2 ^ 59
def prefixEnd_5814881 : Nat := 4983230072969 + 3 ^ 40 * 5814881 * 2
def baseEnd_5814881 : Nat := 2985828901696968985045355

theorem tailTrace_5814881 : CollatzResearch.WordTrace tailWord_5814881 prefixEnd_5814881 2985828901696968985045355 := by
  unfold tailWord_5814881
  simp only [CollatzResearch.WordTrace]
  refine ⟨212086133646686714454972497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141390755764457809636648331 212086133646686714454972497)
  ·
    refine ⟨159064600235015035841229373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212086133646686714454972497 159064600235015035841229373)
    ·
      refine ⟨59649225088130638440461015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 159064600235015035841229373 59649225088130638440461015)
      ·
        refine ⟨89473837632195957660691523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59649225088130638440461015 89473837632195957660691523)
        ·
          refine ⟨134210756448293936491037285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89473837632195957660691523 134210756448293936491037285)
          ·
            refine ⟨25164516834055113092069491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 134210756448293936491037285 25164516834055113092069491)
            ·
              refine ⟨37746775251082669638104237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25164516834055113092069491 37746775251082669638104237)
              ·
                refine ⟨14155040719156001114289089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37746775251082669638104237 14155040719156001114289089)
                ·
                  refine ⟨10616280539367000835716817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14155040719156001114289089 10616280539367000835716817)
                  ·
                    refine ⟨7962210404525250626787613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10616280539367000835716817 7962210404525250626787613)
                    ·
                      refine ⟨2985828901696968985045355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7962210404525250626787613 2985828901696968985045355)
                      ·
                        rfl

theorem cell23_5814881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 3, 2, 2, 3].length) (baseStart_5814881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5814881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5814881 prefixEnd_5814881 := by exact prefixLift 5814881
  have htrace : WordTrace (prefixWord ++ tailWord_5814881) baseStart_5814881 baseEnd_5814881 := by
    simpa [prefixWord, tailWord_5814881, baseEnd_5814881] using wordTrace_append hprefix tailTrace_5814881
  have hstable : (prefixWord ++ tailWord_5814881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5814881).length < 2 ^ (prefixWord ++ tailWord_5814881).sum := by decide
  have hdescent : baseEnd_5814881 < baseStart_5814881 := by decide
  rcases family_descends (prefixWord ++ tailWord_5814881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5814905 : List Nat := [1, 2, 1, 3, 3, 2, 4, 2, 1, 4]
def baseStart_5814905 : Nat := 118140960795 + 5814905 * 2 ^ 59
def prefixEnd_5814905 : Nat := 4983230072969 + 3 ^ 40 * 5814905 * 2
def baseEnd_5814905 : Nat := 995280408410892297048415

theorem tailTrace_5814905 : CollatzResearch.WordTrace tailWord_5814905 prefixEnd_5814905 995280408410892297048415 := by
  unfold tailWord_5814905
  simp only [CollatzResearch.WordTrace]
  refine ⟨212087008998599766553846169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141391339332399844369230779 212087008998599766553846169)
  ·
    refine ⟨159065256748949824915384627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212087008998599766553846169 159065256748949824915384627)
    ·
      refine ⟨238597885123424737373076941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159065256748949824915384627 238597885123424737373076941)
      ·
        refine ⟨89474206921284276514903853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 238597885123424737373076941 89474206921284276514903853)
        ·
          refine ⟨33552827595481603693088945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89474206921284276514903853 33552827595481603693088945)
          ·
            refine ⟨25164620696611202769816709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33552827595481603693088945 25164620696611202769816709)
            ·
              refine ⟨4718366380614600519340633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25164620696611202769816709 4718366380614600519340633)
              ·
                refine ⟨3538774785460950389505475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4718366380614600519340633 3538774785460950389505475)
                ·
                  refine ⟨5308162178191425584258213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3538774785460950389505475 5308162178191425584258213)
                  ·
                    refine ⟨995280408410892297048415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5308162178191425584258213 995280408410892297048415)
                    ·
                      rfl

theorem cell23_5814905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 4, 2, 1, 4].length) (baseStart_5814905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5814905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5814905 prefixEnd_5814905 := by exact prefixLift 5814905
  have htrace : WordTrace (prefixWord ++ tailWord_5814905) baseStart_5814905 baseEnd_5814905 := by
    simpa [prefixWord, tailWord_5814905, baseEnd_5814905] using wordTrace_append hprefix tailTrace_5814905
  have hstable : (prefixWord ++ tailWord_5814905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5814905).length < 2 ^ (prefixWord ++ tailWord_5814905).sum := by decide
  have hdescent : baseEnd_5814905 < baseStart_5814905 := by decide
  rcases family_descends (prefixWord ++ tailWord_5814905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5814921 : List Nat := [1, 2, 1, 1, 4, 1, 1, 4, 1, 5, 2]
def baseStart_5814921 : Nat := 118140960795 + 5814921 * 2 ^ 59
def prefixEnd_5814921 : Nat := 4983230072969 + 3 ^ 40 * 5814921 * 2
def baseEnd_5814921 : Nat := 2985849440923148828545171

theorem tailTrace_5814921 : CollatzResearch.WordTrace tailWord_5814921 prefixEnd_5814921 2985849440923148828545171 := by
  unfold tailWord_5814921
  simp only [CollatzResearch.WordTrace]
  refine ⟨212087592566541801286428617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141391728377694534190952411 212087592566541801286428617)
  ·
    refine ⟨159065694424906350964821463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212087592566541801286428617 159065694424906350964821463)
    ·
      refine ⟨238598541637359526447232195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159065694424906350964821463 238598541637359526447232195)
      ·
        refine ⟨357897812456039289670848293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238598541637359526447232195 357897812456039289670848293)
        ·
          refine ⟨67105839835507366813284055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 357897812456039289670848293 67105839835507366813284055)
          ·
            refine ⟨100658759753261050219926083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67105839835507366813284055 100658759753261050219926083)
            ·
              refine ⟨150988139629891575329889125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100658759753261050219926083 150988139629891575329889125)
              ·
                refine ⟨28310276180604670374354211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 150988139629891575329889125 28310276180604670374354211)
                ·
                  refine ⟨42465414270907005561531317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28310276180604670374354211 42465414270907005561531317)
                  ·
                    refine ⟨3981132587897531771393561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42465414270907005561531317 3981132587897531771393561)
                    ·
                      refine ⟨2985849440923148828545171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3981132587897531771393561 2985849440923148828545171)
                      ·
                        rfl

theorem cell23_5814921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 4, 1, 5, 2].length) (baseStart_5814921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5814921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5814921 prefixEnd_5814921 := by exact prefixLift 5814921
  have htrace : WordTrace (prefixWord ++ tailWord_5814921) baseStart_5814921 baseEnd_5814921 := by
    simpa [prefixWord, tailWord_5814921, baseEnd_5814921] using wordTrace_append hprefix tailTrace_5814921
  have hstable : (prefixWord ++ tailWord_5814921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5814921).length < 2 ^ (prefixWord ++ tailWord_5814921).sum := by decide
  have hdescent : baseEnd_5814921 < baseStart_5814921 := by decide
  rcases family_descends (prefixWord ++ tailWord_5814921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5814996 : List Nat := [2, 4, 1, 3, 3, 1, 1, 3, 1, 1, 3]
def baseStart_5814996 : Nat := 118140960795 + 5814996 * 2 ^ 59
def prefixEnd_5814996 : Nat := 4983230072969 + 3 ^ 40 * 5814996 * 2
def baseEnd_5814996 : Nat := 2985887951972236035107327

theorem tailTrace_5814996 : CollatzResearch.WordTrace tailWord_5814996 prefixEnd_5814996 2985887951972236035107327 := by
  unfold tailWord_5814996
  simp only [CollatzResearch.WordTrace]
  refine ⟨106045164020635044547704421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141393552027513392730272561 106045164020635044547704421)
  ·
    refine ⟨19883468253869070852694579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 106045164020635044547704421 19883468253869070852694579)
    ·
      refine ⟨29825202380803606279041869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19883468253869070852694579 29825202380803606279041869)
      ·
        refine ⟨11184450892801352354640701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29825202380803606279041869 11184450892801352354640701)
        ·
          refine ⟨4194169084800507132990263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11184450892801352354640701 4194169084800507132990263)
          ·
            refine ⟨6291253627200760699485395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4194169084800507132990263 6291253627200760699485395)
            ·
              refine ⟨9436880440801141049228093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6291253627200760699485395 9436880440801141049228093)
              ·
                refine ⟨3538830165300427893460535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9436880440801141049228093 3538830165300427893460535)
                ·
                  refine ⟨5308245247950641840190803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3538830165300427893460535 5308245247950641840190803)
                  ·
                    refine ⟨7962367871925962760286205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5308245247950641840190803 7962367871925962760286205)
                    ·
                      refine ⟨2985887951972236035107327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7962367871925962760286205 2985887951972236035107327)
                      ·
                        rfl

theorem cell23_5814996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 1, 3, 1, 1, 3].length) (baseStart_5814996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5814996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5814996 prefixEnd_5814996 := by exact prefixLift 5814996
  have htrace : WordTrace (prefixWord ++ tailWord_5814996) baseStart_5814996 baseEnd_5814996 := by
    simpa [prefixWord, tailWord_5814996, baseEnd_5814996] using wordTrace_append hprefix tailTrace_5814996
  have hstable : (prefixWord ++ tailWord_5814996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5814996).length < 2 ^ (prefixWord ++ tailWord_5814996).sum := by decide
  have hdescent : baseEnd_5814996 < baseStart_5814996 := by decide
  rcases family_descends (prefixWord ++ tailWord_5814996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5815001 : List Nat := [1, 2, 1, 2, 3, 2, 2, 1, 3, 3, 3]
def baseStart_5815001 : Nat := 118140960795 + 5815001 * 2 ^ 59
def prefixEnd_5815001 : Nat := 4983230072969 + 3 ^ 40 * 5815001 * 2
def baseEnd_5815001 : Nat := 2985890519375508515544803

theorem tailTrace_5815001 : CollatzResearch.WordTrace tailWord_5815001 prefixEnd_5815001 2985890519375508515544803 := by
  unfold tailWord_5815001
  simp only [CollatzResearch.WordTrace]
  refine ⟨212090510406251974949340857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141393673604167983299560571 212090510406251974949340857)
  ·
    refine ⟨159067882804688981212005643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212090510406251974949340857 159067882804688981212005643)
    ·
      refine ⟨238601824207033471818008465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159067882804688981212005643 238601824207033471818008465)
      ·
        refine ⟨178951368155275103863506349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 238601824207033471818008465 178951368155275103863506349)
        ·
          refine ⟨67106763058228163948814881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 178951368155275103863506349 67106763058228163948814881)
          ·
            refine ⟨50330072293671122961611161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67106763058228163948814881 50330072293671122961611161)
            ·
              refine ⟨37747554220253342221208371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50330072293671122961611161 37747554220253342221208371)
              ·
                refine ⟨56621331330380013331812557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37747554220253342221208371 56621331330380013331812557)
                ·
                  refine ⟨21232999248892504999429709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56621331330380013331812557 21232999248892504999429709)
                  ·
                    refine ⟨7962374718334689374786141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21232999248892504999429709 7962374718334689374786141)
                    ·
                      refine ⟨2985890519375508515544803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7962374718334689374786141 2985890519375508515544803)
                      ·
                        rfl

theorem cell23_5815001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 1, 3, 3, 3].length) (baseStart_5815001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5815001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5815001 prefixEnd_5815001 := by exact prefixLift 5815001
  have htrace : WordTrace (prefixWord ++ tailWord_5815001) baseStart_5815001 baseEnd_5815001 := by
    simpa [prefixWord, tailWord_5815001, baseEnd_5815001] using wordTrace_append hprefix tailTrace_5815001
  have hstable : (prefixWord ++ tailWord_5815001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5815001).length < 2 ^ (prefixWord ++ tailWord_5815001).sum := by decide
  have hdescent : baseEnd_5815001 < baseStart_5815001 := by decide
  rcases family_descends (prefixWord ++ tailWord_5815001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5815021 : List Nat := [1, 5, 1, 2, 1, 1, 2, 1, 2, 7]
def baseStart_5815021 : Nat := 118140960795 + 5815021 * 2 ^ 59
def prefixEnd_5815021 : Nat := 4983230072969 + 3 ^ 40 * 5815021 * 2
def baseEnd_5815021 : Nat := 995300262996199479098237

theorem tailTrace_5815021 : CollatzResearch.WordTrace tailWord_5815021 prefixEnd_5815021 995300262996199479098237 := by
  unfold tailWord_5815021
  simp only [CollatzResearch.WordTrace]
  refine ⟨212091239866179518365068917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141394159910786345576712611 212091239866179518365068917)
  ·
    refine ⟨19883553737454329846725211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 212091239866179518365068917 19883553737454329846725211)
    ·
      refine ⟨29825330606181494770087817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19883553737454329846725211 29825330606181494770087817)
      ·
        refine ⟨22368997954636121077565863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29825330606181494770087817 22368997954636121077565863)
        ·
          refine ⟨33553496931954181616348795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22368997954636121077565863 33553496931954181616348795)
          ·
            refine ⟨50330245397931272424523193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33553496931954181616348795 50330245397931272424523193)
            ·
              refine ⟨37747684048448454318392395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50330245397931272424523193 37747684048448454318392395)
              ·
                refine ⟨56621526072672681477588593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37747684048448454318392395 56621526072672681477588593)
                ·
                  refine ⟨42466144554504511108191445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56621526072672681477588593 42466144554504511108191445)
                  ·
                    refine ⟨995300262996199479098237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42466144554504511108191445 995300262996199479098237)
                    ·
                      rfl

theorem cell23_5815021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 1, 2, 7].length) (baseStart_5815021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5815021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5815021 prefixEnd_5815021 := by exact prefixLift 5815021
  have htrace : WordTrace (prefixWord ++ tailWord_5815021) baseStart_5815021 baseEnd_5815021 := by
    simpa [prefixWord, tailWord_5815021, baseEnd_5815021] using wordTrace_append hprefix tailTrace_5815021
  have hstable : (prefixWord ++ tailWord_5815021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5815021).length < 2 ^ (prefixWord ++ tailWord_5815021).sum := by decide
  have hdescent : baseEnd_5815021 < baseStart_5815021 := by decide
  rcases family_descends (prefixWord ++ tailWord_5815021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5815029 : List Nat := [1, 3, 6, 1, 1, 1, 1, 3, 2, 4]
def baseStart_5815029 : Nat := 118140960795 + 5815029 * 2 ^ 59
def prefixEnd_5815029 : Nat := 4983230072969 + 3 ^ 40 * 5815029 * 2
def baseEnd_5815029 : Nat := 995301632277944801998225

theorem tailTrace_5815029 : CollatzResearch.WordTrace tailWord_5815029 prefixEnd_5815029 995301632277944801998225 := by
  unfold tailWord_5815029
  simp only [CollatzResearch.WordTrace]
  refine ⟨212091531650150535731360141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141394354433433690487573427 212091531650150535731360141)
  ·
    refine ⟨79534324368806450899260053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 212091531650150535731360141 79534324368806450899260053)
    ·
      refine ⟨3728171454787802385902815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 79534324368806450899260053 3728171454787802385902815)
      ·
        refine ⟨5592257182181703578854223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3728171454787802385902815 5592257182181703578854223)
        ·
          refine ⟨8388385773272555368281335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5592257182181703578854223 8388385773272555368281335)
          ·
            refine ⟨12582578659908833052422003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8388385773272555368281335 12582578659908833052422003)
            ·
              refine ⟨18873867989863249578633005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12582578659908833052422003 18873867989863249578633005)
              ·
                refine ⟨7077700496198718591987377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18873867989863249578633005 7077700496198718591987377)
                ·
                  refine ⟨5308275372149038943990533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7077700496198718591987377 5308275372149038943990533)
                  ·
                    refine ⟨995301632277944801998225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5308275372149038943990533 995301632277944801998225)
                    ·
                      rfl

theorem cell23_5815029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_5815029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5815029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5815029 prefixEnd_5815029 := by exact prefixLift 5815029
  have htrace : WordTrace (prefixWord ++ tailWord_5815029) baseStart_5815029 baseEnd_5815029 := by
    simpa [prefixWord, tailWord_5815029, baseEnd_5815029] using wordTrace_append hprefix tailTrace_5815029
  have hstable : (prefixWord ++ tailWord_5815029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5815029).length < 2 ^ (prefixWord ++ tailWord_5815029).sum := by decide
  have hdescent : baseEnd_5815029 < baseStart_5815029 := by decide
  rcases family_descends (prefixWord ++ tailWord_5815029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5815061 : List Nat := [1, 3, 2, 1, 2, 2, 1, 3, 2, 1, 5]
def baseStart_5815061 : Nat := 118140960795 + 5815061 * 2 ^ 59
def prefixEnd_5815061 : Nat := 4983230072969 + 3 ^ 40 * 5815061 * 2
def baseEnd_5815061 : Nat := 2985921328214778280794527

theorem tailTrace_5815061 : CollatzResearch.WordTrace tailWord_5815061 prefixEnd_5815061 2985921328214778280794527 := by
  unfold tailWord_5815061
  simp only [CollatzResearch.WordTrace]
  refine ⟨212092698786034605196525037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141395132524023070131016691 212092698786034605196525037)
  ·
    refine ⟨79534762044762976948696889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 212092698786034605196525037 79534762044762976948696889)
    ·
      refine ⟨59651071533572232711522667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79534762044762976948696889 59651071533572232711522667)
      ·
        refine ⟨89476607300358349067284001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59651071533572232711522667 89476607300358349067284001)
        ·
          refine ⟨67107455475268761800463001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89476607300358349067284001 67107455475268761800463001)
          ·
            refine ⟨50330591606451571350347251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67107455475268761800463001 50330591606451571350347251)
            ·
              refine ⟨75495887409677357025520877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50330591606451571350347251 75495887409677357025520877)
              ·
                refine ⟨28310957778629008884570329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75495887409677357025520877 28310957778629008884570329)
                ·
                  refine ⟨21233218333971756663427747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28310957778629008884570329 21233218333971756663427747)
                  ·
                    refine ⟨31849827500957634995141621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21233218333971756663427747 31849827500957634995141621)
                    ·
                      refine ⟨2985921328214778280794527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31849827500957634995141621 2985921328214778280794527)
                      ·
                        rfl

theorem cell23_5815061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 3, 2, 1, 5].length) (baseStart_5815061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5815061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5815061 prefixEnd_5815061 := by exact prefixLift 5815061
  have htrace : WordTrace (prefixWord ++ tailWord_5815061) baseStart_5815061 baseEnd_5815061 := by
    simpa [prefixWord, tailWord_5815061, baseEnd_5815061] using wordTrace_append hprefix tailTrace_5815061
  have hstable : (prefixWord ++ tailWord_5815061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5815061).length < 2 ^ (prefixWord ++ tailWord_5815061).sum := by decide
  have hdescent : baseEnd_5815061 < baseStart_5815061 := by decide
  rcases family_descends (prefixWord ++ tailWord_5815061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5815069 : List Nat := [1, 4, 2, 4, 1, 1, 2, 2, 2, 1, 3]
def baseStart_5815069 : Nat := 118140960795 + 5815069 * 2 ^ 59
def prefixEnd_5815069 : Nat := 4983230072969 + 3 ^ 40 * 5815069 * 2
def baseEnd_5815069 : Nat := 2985925436060014249494491

theorem tailTrace_5815069 : CollatzResearch.WordTrace tailWord_5815069 prefixEnd_5815069 2985925436060014249494491 := by
  unfold tailWord_5815069
  simp only [CollatzResearch.WordTrace]
  refine ⟨212092990570005622562816261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141395327046670415041877507 212092990570005622562816261)
  ·
    refine ⟨39767435731876054230528049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 212092990570005622562816261 39767435731876054230528049)
    ·
      refine ⟨29825576798907040672896037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39767435731876054230528049 29825576798907040672896037)
      ·
        refine ⟨5592295649795070126168007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29825576798907040672896037 5592295649795070126168007)
        ·
          refine ⟨8388443474692605189252011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5592295649795070126168007 8388443474692605189252011)
          ·
            refine ⟨12582665212038907783878017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8388443474692605189252011 12582665212038907783878017)
            ·
              refine ⟨9436998909029180837908513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12582665212038907783878017 9436998909029180837908513)
              ·
                refine ⟨7077749181771885628431385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9436998909029180837908513 7077749181771885628431385)
                ·
                  refine ⟨5308311886328914221323539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7077749181771885628431385 5308311886328914221323539)
                  ·
                    refine ⟨7962467829493371331985309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5308311886328914221323539 7962467829493371331985309)
                    ·
                      refine ⟨2985925436060014249494491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7962467829493371331985309 2985925436060014249494491)
                      ·
                        rfl

theorem cell23_5815069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_5815069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5815069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5815069 prefixEnd_5815069 := by exact prefixLift 5815069
  have htrace : WordTrace (prefixWord ++ tailWord_5815069) baseStart_5815069 baseEnd_5815069 := by
    simpa [prefixWord, tailWord_5815069, baseEnd_5815069] using wordTrace_append hprefix tailTrace_5815069
  have hstable : (prefixWord ++ tailWord_5815069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5815069).length < 2 ^ (prefixWord ++ tailWord_5815069).sum := by decide
  have hdescent : baseEnd_5815069 < baseStart_5815069 := by decide
  rcases family_descends (prefixWord ++ tailWord_5815069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5815098 : List Nat := [3, 1, 1, 1, 6, 1, 1, 2, 7]
def baseStart_5815098 : Nat := 118140960795 + 5815098 * 2 ^ 59
def prefixEnd_5815098 : Nat := 4983230072969 + 3 ^ 40 * 5815098 * 2
def baseEnd_5815098 : Nat := 331771147444332737336873

theorem tailTrace_5815098 : CollatzResearch.WordTrace tailWord_5815098 prefixEnd_5815098 331771147444332737336873 := by
  unfold tailWord_5815098
  simp only [CollatzResearch.WordTrace]
  refine ⟨53023512071725140128905487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141396032191267040343747965 53023512071725140128905487)
  ·
    refine ⟨79535268107587710193358231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53023512071725140128905487 79535268107587710193358231)
    ·
      refine ⟨119302902161381565290037347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79535268107587710193358231 119302902161381565290037347)
      ·
        refine ⟨178954353242072347935056021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119302902161381565290037347 178954353242072347935056021)
        ·
          refine ⟨8388485308222141309455751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 178954353242072347935056021 8388485308222141309455751)
          ·
            refine ⟨12582727962333211964183627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8388485308222141309455751 12582727962333211964183627)
            ·
              refine ⟨18874091943499817946275441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12582727962333211964183627 18874091943499817946275441)
              ·
                refine ⟨14155568957624863459706581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18874091943499817946275441 14155568957624863459706581)
                ·
                  refine ⟨331771147444332737336873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14155568957624863459706581 331771147444332737336873)
                  ·
                    rfl

theorem cell23_5815098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 2, 7].length) (baseStart_5815098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5815098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5815098 prefixEnd_5815098 := by exact prefixLift 5815098
  have htrace : WordTrace (prefixWord ++ tailWord_5815098) baseStart_5815098 baseEnd_5815098 := by
    simpa [prefixWord, tailWord_5815098, baseEnd_5815098] using wordTrace_append hprefix tailTrace_5815098
  have hstable : (prefixWord ++ tailWord_5815098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5815098).length < 2 ^ (prefixWord ++ tailWord_5815098).sum := by decide
  have hdescent : baseEnd_5815098 < baseStart_5815098 := by decide
  rcases family_descends (prefixWord ++ tailWord_5815098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5815166 : List Nat := [4, 2, 3, 1, 3, 1, 1, 3, 5]
def baseStart_5815166 : Nat := 118140960795 + 5815166 * 2 ^ 59
def prefixEnd_5815166 : Nat := 4983230072969 + 3 ^ 40 * 5815166 * 2
def baseEnd_5815166 : Nat := 331775027075944485553505

theorem tailTrace_5815166 : CollatzResearch.WordTrace tailWord_5815166 prefixEnd_5815166 331775027075944485553505 := by
  unfold tailWord_5815166
  simp only [CollatzResearch.WordTrace]
  refine ⟨26512066056331776016137169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 141397685633769472086064901 26512066056331776016137169)
  ·
    refine ⟨19884049542248832012102877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26512066056331776016137169 19884049542248832012102877)
    ·
      refine ⟨7456518578343312004538579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19884049542248832012102877 7456518578343312004538579)
      ·
        refine ⟨11184777867514968006807869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7456518578343312004538579 11184777867514968006807869)
        ·
          refine ⟨4194291700318113002552951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11184777867514968006807869 4194291700318113002552951)
          ·
            refine ⟨6291437550477169503829427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4194291700318113002552951 6291437550477169503829427)
            ·
              refine ⟨9437156325715754255744141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6291437550477169503829427 9437156325715754255744141)
              ·
                refine ⟨3538933622143407845904053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9437156325715754255744141 3538933622143407845904053)
                ·
                  refine ⟨331775027075944485553505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3538933622143407845904053 331775027075944485553505)
                  ·
                    rfl

theorem cell23_5815166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 1, 3, 5].length) (baseStart_5815166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5815166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5815166 prefixEnd_5815166 := by exact prefixLift 5815166
  have htrace : WordTrace (prefixWord ++ tailWord_5815166) baseStart_5815166 baseEnd_5815166 := by
    simpa [prefixWord, tailWord_5815166, baseEnd_5815166] using wordTrace_append hprefix tailTrace_5815166
  have hstable : (prefixWord ++ tailWord_5815166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5815166).length < 2 ^ (prefixWord ++ tailWord_5815166).sum := by decide
  have hdescent : baseEnd_5815166 < baseStart_5815166 := by decide
  rcases family_descends (prefixWord ++ tailWord_5815166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5815171 : List Nat := [1, 1, 1, 3, 4, 1, 1, 1, 10]
def baseStart_5815171 : Nat := 118140960795 + 5815171 * 2 ^ 59
def prefixEnd_5815171 : Nat := 4983230072969 + 3 ^ 40 * 5815171 * 2
def baseEnd_5815171 : Nat := 331775312342974761157669

theorem tailTrace_5815171 : CollatzResearch.WordTrace tailWord_5815171 prefixEnd_5815171 331775312342974761157669 := by
  unfold tailWord_5815171
  simp only [CollatzResearch.WordTrace]
  refine ⟨212096710815636093983029367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141397807210424062655352911 212096710815636093983029367)
  ·
    refine ⟨318145066223454140974544051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212096710815636093983029367 318145066223454140974544051)
    ·
      refine ⟨477217599335181211461816077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 318145066223454140974544051 477217599335181211461816077)
      ·
        refine ⟨178956599750692954298181029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 477217599335181211461816077 178956599750692954298181029)
        ·
          refine ⟨33554362453254928930908943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 178956599750692954298181029 33554362453254928930908943)
          ·
            refine ⟨50331543679882393396363415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33554362453254928930908943 50331543679882393396363415)
            ·
              refine ⟨75497315519823590094545123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50331543679882393396363415 75497315519823590094545123)
              ·
                refine ⟨113245973279735385141817685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75497315519823590094545123 113245973279735385141817685)
                ·
                  refine ⟨331775312342974761157669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 113245973279735385141817685 331775312342974761157669)
                  ·
                    rfl

theorem cell23_5815171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 1, 10].length) (baseStart_5815171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5815171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5815171 prefixEnd_5815171 := by exact prefixLift 5815171
  have htrace : WordTrace (prefixWord ++ tailWord_5815171) baseStart_5815171 baseEnd_5815171 := by
    simpa [prefixWord, tailWord_5815171, baseEnd_5815171] using wordTrace_append hprefix tailTrace_5815171
  have hstable : (prefixWord ++ tailWord_5815171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5815171).length < 2 ^ (prefixWord ++ tailWord_5815171).sum := by decide
  have hdescent : baseEnd_5815171 < baseStart_5815171 := by decide
  rcases family_descends (prefixWord ++ tailWord_5815171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5815188 : List Nat := [2, 4, 2, 1, 1, 1, 1, 3, 8]
def baseStart_5815188 : Nat := 118140960795 + 5815188 * 2 ^ 59
def prefixEnd_5815188 : Nat := 4983230072969 + 3 ^ 40 * 5815188 * 2
def baseEnd_5815188 : Nat := 331776282250877698211827

theorem tailTrace_5815188 : CollatzResearch.WordTrace tailWord_5815188 prefixEnd_5815188 331776282250877698211827 := by
  unfold tailWord_5815188
  simp only [CollatzResearch.WordTrace]
  refine ⟨106048665428287252943199109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141398220571049670590932145 106048665428287252943199109)
  ·
    refine ⟨19884124767803859926849833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 106048665428287252943199109 19884124767803859926849833)
    ·
      refine ⟨14913093575852894945137375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19884124767803859926849833 14913093575852894945137375)
      ·
        refine ⟨22369640363779342417706063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14913093575852894945137375 22369640363779342417706063)
        ·
          refine ⟨33554460545669013626559095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22369640363779342417706063 33554460545669013626559095)
          ·
            refine ⟨50331690818503520439838643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33554460545669013626559095 50331690818503520439838643)
            ·
              refine ⟨75497536227755280659757965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50331690818503520439838643 75497536227755280659757965)
              ·
                refine ⟨28311576085408230247409237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75497536227755280659757965 28311576085408230247409237)
                ·
                  refine ⟨331776282250877698211827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28311576085408230247409237 331776282250877698211827)
                  ·
                    rfl

theorem cell23_5815188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 3, 8].length) (baseStart_5815188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5815188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5815188 prefixEnd_5815188 := by exact prefixLift 5815188
  have htrace : WordTrace (prefixWord ++ tailWord_5815188) baseStart_5815188 baseEnd_5815188 := by
    simpa [prefixWord, tailWord_5815188, baseEnd_5815188] using wordTrace_append hprefix tailTrace_5815188
  have hstable : (prefixWord ++ tailWord_5815188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5815188).length < 2 ^ (prefixWord ++ tailWord_5815188).sum := by decide
  have hdescent : baseEnd_5815188 < baseStart_5815188 := by decide
  rcases family_descends (prefixWord ++ tailWord_5815188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5815211 : List Nat := [1, 1, 1, 1, 2, 1, 1, 5, 2, 1, 7]
def baseStart_5815211 : Nat := 118140960795 + 5815211 * 2 ^ 59
def prefixEnd_5815211 : Nat := 4983230072969 + 3 ^ 40 * 5815211 * 2
def baseEnd_5815211 : Nat := 2985998350312952693918837

theorem tailTrace_5815211 : CollatzResearch.WordTrace tailWord_5815211 prefixEnd_5815211 2985998350312952693918837 := by
  unfold tailWord_5815211
  simp only [CollatzResearch.WordTrace]
  refine ⟨212098169735491180814485487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141398779823660787209656991 212098169735491180814485487)
  ·
    refine ⟨318147254603236771221728231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212098169735491180814485487 318147254603236771221728231)
    ·
      refine ⟨477220881904855156832592347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 318147254603236771221728231 477220881904855156832592347)
      ·
        refine ⟨715831322857282735248888521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 477220881904855156832592347 715831322857282735248888521)
        ·
          refine ⟨536873492142962051436666391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 715831322857282735248888521 536873492142962051436666391)
          ·
            refine ⟨805310238214443077154999587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 536873492142962051436666391 805310238214443077154999587)
            ·
              refine ⟨1207965357321664615732499381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 805310238214443077154999587 1207965357321664615732499381)
              ·
                refine ⟨113246752248906057724921817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1207965357321664615732499381 113246752248906057724921817)
                ·
                  refine ⟨84935064186679543293691363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 113246752248906057724921817 84935064186679543293691363)
                  ·
                    refine ⟨127402596280019314940537045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 84935064186679543293691363 127402596280019314940537045)
                    ·
                      refine ⟨2985998350312952693918837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 127402596280019314940537045 2985998350312952693918837)
                      ·
                        rfl

theorem cell23_5815211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 5, 2, 1, 7].length) (baseStart_5815211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5815211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5815211 prefixEnd_5815211 := by exact prefixLift 5815211
  have htrace : WordTrace (prefixWord ++ tailWord_5815211) baseStart_5815211 baseEnd_5815211 := by
    simpa [prefixWord, tailWord_5815211, baseEnd_5815211] using wordTrace_append hprefix tailTrace_5815211
  have hstable : (prefixWord ++ tailWord_5815211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5815211).length < 2 ^ (prefixWord ++ tailWord_5815211).sum := by decide
  have hdescent : baseEnd_5815211 < baseStart_5815211 := by decide
  rcases family_descends (prefixWord ++ tailWord_5815211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5815272 : List Nat := [2, 1, 4, 1, 1, 1, 3, 1, 5, 2, 2]
def baseStart_5815272 : Nat := 118140960795 + 5815272 * 2 ^ 59
def prefixEnd_5815272 : Nat := 4983230072969 + 3 ^ 40 * 5815272 * 2
def baseEnd_5815272 : Nat := 2986029672632876955256057

theorem tailTrace_5815272 : CollatzResearch.WordTrace tailWord_5815272 prefixEnd_5815272 2986029672632876955256057 := by
  unfold tailWord_5815272
  simp only [CollatzResearch.WordTrace]
  refine ⟨106050197294135094116228035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141400263058846792154970713 106050197294135094116228035)
  ·
    refine ⟨159075295941202641174342053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106050197294135094116228035 159075295941202641174342053)
    ·
      refine ⟨29826617988975495220189135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 159075295941202641174342053 29826617988975495220189135)
      ·
        refine ⟨44739926983463242830283703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29826617988975495220189135 44739926983463242830283703)
        ·
          refine ⟨67109890475194864245425555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44739926983463242830283703 67109890475194864245425555)
          ·
            refine ⟨100664835712792296368138333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67109890475194864245425555 100664835712792296368138333)
            ·
              refine ⟨37749313392297111138051875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 100664835712792296368138333 37749313392297111138051875)
              ·
                refine ⟨56623970088445666707077813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37749313392297111138051875 56623970088445666707077813)
                ·
                  refine ⟨5308497195791781253788545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 56623970088445666707077813 5308497195791781253788545)
                  ·
                    refine ⟨3981372896843835940341409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5308497195791781253788545 3981372896843835940341409)
                    ·
                      refine ⟨2986029672632876955256057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3981372896843835940341409 2986029672632876955256057)
                      ·
                        rfl

theorem cell23_5815272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 1, 5, 2, 2].length) (baseStart_5815272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5815272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5815272 prefixEnd_5815272 := by exact prefixLift 5815272
  have htrace : WordTrace (prefixWord ++ tailWord_5815272) baseStart_5815272 baseEnd_5815272 := by
    simpa [prefixWord, tailWord_5815272, baseEnd_5815272] using wordTrace_append hprefix tailTrace_5815272
  have hstable : (prefixWord ++ tailWord_5815272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5815272).length < 2 ^ (prefixWord ++ tailWord_5815272).sum := by decide
  have hdescent : baseEnd_5815272 < baseStart_5815272 := by decide
  rcases family_descends (prefixWord ++ tailWord_5815272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5815292 : List Nat := [2, 2, 2, 1, 2, 4, 1, 3, 1, 2, 3]
def baseStart_5815292 : Nat := 118140960795 + 5815292 * 2 ^ 59
def prefixEnd_5815292 : Nat := 4983230072969 + 3 ^ 40 * 5815292 * 2
def baseEnd_5815292 : Nat := 2986039942245966877005965

theorem tailTrace_5815292 : CollatzResearch.WordTrace tailWord_5815292 prefixEnd_5815292 2986039942245966877005965 := by
  unfold tailWord_5815292
  simp only [CollatzResearch.WordTrace]
  refine ⟨106050562024098865824092065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141400749365465154432122753 106050562024098865824092065)
  ·
    refine ⟨79537921518074149368069049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106050562024098865824092065 79537921518074149368069049)
    ·
      refine ⟨59653441138555612026051787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79537921518074149368069049 59653441138555612026051787)
      ·
        refine ⟨89480161707833418039077681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59653441138555612026051787 89480161707833418039077681)
        ·
          refine ⟨67110121280875063529308261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89480161707833418039077681 67110121280875063529308261)
          ·
            refine ⟨12583147740164074411745299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67110121280875063529308261 12583147740164074411745299)
            ·
              refine ⟨18874721610246111617617949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12583147740164074411745299 18874721610246111617617949)
              ·
                refine ⟨7078020603842291856606731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18874721610246111617617949 7078020603842291856606731)
                ·
                  refine ⟨10617030905763437784910097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7078020603842291856606731 10617030905763437784910097)
                  ·
                    refine ⟨7962773179322578338682573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10617030905763437784910097 7962773179322578338682573)
                    ·
                      refine ⟨2986039942245966877005965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7962773179322578338682573 2986039942245966877005965)
                      ·
                        rfl

theorem cell23_5815292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 3, 1, 2, 3].length) (baseStart_5815292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5815292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5815292 prefixEnd_5815292 := by exact prefixLift 5815292
  have htrace : WordTrace (prefixWord ++ tailWord_5815292) baseStart_5815292 baseEnd_5815292 := by
    simpa [prefixWord, tailWord_5815292, baseEnd_5815292] using wordTrace_append hprefix tailTrace_5815292
  have hstable : (prefixWord ++ tailWord_5815292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5815292).length < 2 ^ (prefixWord ++ tailWord_5815292).sum := by decide
  have hdescent : baseEnd_5815292 < baseStart_5815292 := by decide
  rcases family_descends (prefixWord ++ tailWord_5815292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5815306 : List Nat := [3, 1, 2, 2, 3, 1, 2, 4, 1, 2, 2]
def baseStart_5815306 : Nat := 118140960795 + 5815306 * 2 ^ 59
def prefixEnd_5815306 : Nat := 4983230072969 + 3 ^ 40 * 5815306 * 2
def baseEnd_5815306 : Nat := 2986047130975129822230901

theorem tailTrace_5815306 : CollatzResearch.WordTrace tailWord_5815306 prefixEnd_5815306 2986047130975129822230901 := by
  unfold tailWord_5815306
  simp only [CollatzResearch.WordTrace]
  refine ⟨53025408667536753009798443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141401089780098008026129181 53025408667536753009798443)
  ·
    refine ⟨79538113001305129514697665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53025408667536753009798443 79538113001305129514697665)
    ·
      refine ⟨59653584750978847136023249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79538113001305129514697665 59653584750978847136023249)
      ·
        refine ⟨44740188563234135352017437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59653584750978847136023249 44740188563234135352017437)
        ·
          refine ⟨16777570711212800757006539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44740188563234135352017437 16777570711212800757006539)
          ·
            refine ⟨25166356066819201135509809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16777570711212800757006539 25166356066819201135509809)
            ·
              refine ⟨18874767050114400851632357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25166356066819201135509809 18874767050114400851632357)
              ·
                refine ⟨3539018821896450159681067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18874767050114400851632357 3539018821896450159681067)
                ·
                  refine ⟨5308528232844675239521601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3539018821896450159681067 5308528232844675239521601)
                  ·
                    refine ⟨3981396174633506429641201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5308528232844675239521601 3981396174633506429641201)
                    ·
                      refine ⟨2986047130975129822230901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3981396174633506429641201 2986047130975129822230901)
                      ·
                        rfl

theorem cell23_5815306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 4, 1, 2, 2].length) (baseStart_5815306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5815306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5815306 prefixEnd_5815306 := by exact prefixLift 5815306
  have htrace : WordTrace (prefixWord ++ tailWord_5815306) baseStart_5815306 baseEnd_5815306 := by
    simpa [prefixWord, tailWord_5815306, baseEnd_5815306] using wordTrace_append hprefix tailTrace_5815306
  have hstable : (prefixWord ++ tailWord_5815306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5815306).length < 2 ^ (prefixWord ++ tailWord_5815306).sum := by decide
  have hdescent : baseEnd_5815306 < baseStart_5815306 := by decide
  rcases family_descends (prefixWord ++ tailWord_5815306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5815373 : List Nat := [1, 6, 1, 1, 1, 4, 2, 1, 2, 1, 3]
def baseStart_5815373 : Nat := 118140960795 + 5815373 * 2 ^ 59
def prefixEnd_5815373 : Nat := 4983230072969 + 3 ^ 40 * 5815373 * 2
def baseEnd_5815373 : Nat := 2986081534178981060093093

theorem tailTrace_5815373 : CollatzResearch.WordTrace tailWord_5815373 prefixEnd_5815373 2986081534178981060093093 := by
  unfold tailWord_5815373
  simp only [CollatzResearch.WordTrace]
  refine ⟨212104078360904282481882773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141402718907269521654588515 212104078360904282481882773)
  ·
    refine ⟨9942378673167388241338255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 212104078360904282481882773 9942378673167388241338255)
    ·
      refine ⟨14913568009751082362007383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9942378673167388241338255 14913568009751082362007383)
      ·
        refine ⟨22370352014626623543011075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14913568009751082362007383 22370352014626623543011075)
        ·
          refine ⟨33555528021939935314516613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22370352014626623543011075 33555528021939935314516613)
          ·
            refine ⟨6291661504113737871471865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33555528021939935314516613 6291661504113737871471865)
            ·
              refine ⟨4718746128085303403603899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6291661504113737871471865 4718746128085303403603899)
              ·
                refine ⟨7078119192127955105405849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4718746128085303403603899 7078119192127955105405849)
                ·
                  refine ⟨5308589394095966329054387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7078119192127955105405849 5308589394095966329054387)
                  ·
                    refine ⟨7962884091143949493581581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5308589394095966329054387 7962884091143949493581581)
                    ·
                      refine ⟨2986081534178981060093093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7962884091143949493581581 2986081534178981060093093)
                      ·
                        rfl

theorem cell23_5815373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 2, 1, 2, 1, 3].length) (baseStart_5815373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5815373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5815373 prefixEnd_5815373 := by exact prefixLift 5815373
  have htrace : WordTrace (prefixWord ++ tailWord_5815373) baseStart_5815373 baseEnd_5815373 := by
    simpa [prefixWord, tailWord_5815373, baseEnd_5815373] using wordTrace_append hprefix tailTrace_5815373
  have hstable : (prefixWord ++ tailWord_5815373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5815373).length < 2 ^ (prefixWord ++ tailWord_5815373).sum := by decide
  have hdescent : baseEnd_5815373 < baseStart_5815373 := by decide
  rcases family_descends (prefixWord ++ tailWord_5815373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5815395 : List Nat := [1, 1, 1, 5, 1, 1, 1, 2, 4, 3, 3]
def baseStart_5815395 : Nat := 118140960795 + 5815395 * 2 ^ 59
def prefixEnd_5815395 : Nat := 4983230072969 + 3 ^ 40 * 5815395 * 2
def baseEnd_5815395 : Nat := 2986092830753379974017991

theorem tailTrace_5815395 : CollatzResearch.WordTrace tailWord_5815395 prefixEnd_5815395 2986092830753379974017991 := by
  unfold tailWord_5815395
  simp only [CollatzResearch.WordTrace]
  refine ⟨212104880766824580239183639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141403253844549720159455759 212104880766824580239183639)
  ·
    refine ⟨318157321150236870358775459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212104880766824580239183639 318157321150236870358775459)
    ·
      refine ⟨477235981725355305538163189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 318157321150236870358775459 477235981725355305538163189)
      ·
        refine ⟨44740873286752059894202799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 477235981725355305538163189 44740873286752059894202799)
        ·
          refine ⟨67111309930128089841304199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44740873286752059894202799 67111309930128089841304199)
          ·
            refine ⟨100666964895192134761956299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67111309930128089841304199 100666964895192134761956299)
            ·
              refine ⟨151000447342788202142934449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100666964895192134761956299 151000447342788202142934449)
              ·
                refine ⟨113250335507091151607200837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 151000447342788202142934449 113250335507091151607200837)
                ·
                  refine ⟨21234437907579590926350157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 113250335507091151607200837 21234437907579590926350157)
                  ·
                    refine ⟨7962914215342346597381309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21234437907579590926350157 7962914215342346597381309)
                    ·
                      refine ⟨2986092830753379974017991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7962914215342346597381309 2986092830753379974017991)
                      ·
                        rfl

theorem cell23_5815395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 2, 4, 3, 3].length) (baseStart_5815395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5815395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5815395 prefixEnd_5815395 := by exact prefixLift 5815395
  have htrace : WordTrace (prefixWord ++ tailWord_5815395) baseStart_5815395 baseEnd_5815395 := by
    simpa [prefixWord, tailWord_5815395, baseEnd_5815395] using wordTrace_append hprefix tailTrace_5815395
  have hstable : (prefixWord ++ tailWord_5815395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5815395).length < 2 ^ (prefixWord ++ tailWord_5815395).sum := by decide
  have hdescent : baseEnd_5815395 < baseStart_5815395 := by decide
  rcases family_descends (prefixWord ++ tailWord_5815395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5815415 : List Nat := [1, 1, 3, 1, 1, 4, 1, 4, 2, 5]
def baseStart_5815415 : Nat := 118140960795 + 5815415 * 2 ^ 59
def prefixEnd_5815415 : Nat := 4983230072969 + 3 ^ 40 * 5815415 * 2
def baseEnd_5815415 : Nat := 995367700122156631922633

theorem tailTrace_5815415 : CollatzResearch.WordTrace tailWord_5815415 prefixEnd_5815415 995367700122156631922633 := by
  unfold tailWord_5815415
  simp only [CollatzResearch.WordTrace]
  refine ⟨212105610226752123654911699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141403740151168082436607799 212105610226752123654911699)
  ·
    refine ⟨318158415340128185482367549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212105610226752123654911699 318158415340128185482367549)
    ·
      refine ⟨119309405752548069555887831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 318158415340128185482367549 119309405752548069555887831)
      ·
        refine ⟨178964108628822104333831747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119309405752548069555887831 178964108628822104333831747)
        ·
          refine ⟨268446162943233156500747621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178964108628822104333831747 268446162943233156500747621)
          ·
            refine ⟨50333655551856216843890179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 268446162943233156500747621 50333655551856216843890179)
            ·
              refine ⟨75500483327784325265835269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50333655551856216843890179 75500483327784325265835269)
              ·
                refine ⟨14156340623959560987344113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 75500483327784325265835269 14156340623959560987344113)
                ·
                  refine ⟨10617255467969670740508085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14156340623959560987344113 10617255467969670740508085)
                  ·
                    refine ⟨995367700122156631922633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10617255467969670740508085 995367700122156631922633)
                    ·
                      rfl

theorem cell23_5815415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 4, 2, 5].length) (baseStart_5815415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5815415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5815415 prefixEnd_5815415 := by exact prefixLift 5815415
  have htrace : WordTrace (prefixWord ++ tailWord_5815415) baseStart_5815415 baseEnd_5815415 := by
    simpa [prefixWord, tailWord_5815415, baseEnd_5815415] using wordTrace_append hprefix tailTrace_5815415
  have hstable : (prefixWord ++ tailWord_5815415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5815415).length < 2 ^ (prefixWord ++ tailWord_5815415).sum := by decide
  have hdescent : baseEnd_5815415 < baseStart_5815415 := by decide
  rcases family_descends (prefixWord ++ tailWord_5815415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5815435 : List Nat := [1, 1, 1, 1, 4, 1, 1, 4, 4, 1, 4]
def baseStart_5815435 : Nat := 118140960795 + 5815435 * 2 ^ 59
def prefixEnd_5815435 : Nat := 4983230072969 + 3 ^ 40 * 5815435 * 2
def baseEnd_5815435 : Nat := 2986113369979559817517807

theorem tailTrace_5815435 : CollatzResearch.WordTrace tailWord_5815435 prefixEnd_5815435 2986113369979559817517807 := by
  unfold tailWord_5815435
  simp only [CollatzResearch.WordTrace]
  refine ⟨212106339686679667070639759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141404226457786444713759839 212106339686679667070639759)
  ·
    refine ⟨318159509530019500605959639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212106339686679667070639759 318159509530019500605959639)
    ·
      refine ⟨477239264295029250908939459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 318159509530019500605959639 477239264295029250908939459)
      ·
        refine ⟨715858896442543876363409189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 477239264295029250908939459 715858896442543876363409189)
        ·
          refine ⟨134223543082976976818139223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 715858896442543876363409189 134223543082976976818139223)
          ·
            refine ⟨201335314624465465227208835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134223543082976976818139223 201335314624465465227208835)
            ·
              refine ⟨302002971936698197840813253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 201335314624465465227208835 302002971936698197840813253)
              ·
                refine ⟨56625557238130912095152485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 302002971936698197840813253 56625557238130912095152485)
                ·
                  refine ⟨10617291982149546017841091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56625557238130912095152485 10617291982149546017841091)
                  ·
                    refine ⟨15925937973224319026761637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10617291982149546017841091 15925937973224319026761637)
                    ·
                      refine ⟨2986113369979559817517807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15925937973224319026761637 2986113369979559817517807)
                      ·
                        rfl

theorem cell23_5815435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 4, 4, 1, 4].length) (baseStart_5815435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5815435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5815435 prefixEnd_5815435 := by exact prefixLift 5815435
  have htrace : WordTrace (prefixWord ++ tailWord_5815435) baseStart_5815435 baseEnd_5815435 := by
    simpa [prefixWord, tailWord_5815435, baseEnd_5815435] using wordTrace_append hprefix tailTrace_5815435
  have hstable : (prefixWord ++ tailWord_5815435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5815435).length < 2 ^ (prefixWord ++ tailWord_5815435).sum := by decide
  have hdescent : baseEnd_5815435 < baseStart_5815435 := by decide
  rcases family_descends (prefixWord ++ tailWord_5815435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5815452 : List Nat := [2, 2, 3, 2, 1, 3, 1, 1, 1, 3, 4]
def baseStart_5815452 : Nat := 118140960795 + 5815452 * 2 ^ 59
def prefixEnd_5815452 : Nat := 4983230072969 + 3 ^ 40 * 5815452 * 2
def baseEnd_5815452 : Nat := 2986122099150686251005229

theorem tailTrace_5815452 : CollatzResearch.WordTrace tailWord_5815452 prefixEnd_5815452 2986122099150686251005229 := by
  unfold tailWord_5815452
  simp only [CollatzResearch.WordTrace]
  refine ⟨106053479863809039487004305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141404639818412052649339073 106053479863809039487004305)
  ·
    refine ⟨79540109897856779615253229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106053479863809039487004305 79540109897856779615253229)
    ·
      refine ⟨29827541211696292355719961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79540109897856779615253229 29827541211696292355719961)
      ·
        refine ⟨22370655908772219266789971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29827541211696292355719961 22370655908772219266789971)
        ·
          refine ⟨33555983863158328900184957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22370655908772219266789971 33555983863158328900184957)
          ·
            refine ⟨12583493948684373337569359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33555983863158328900184957 12583493948684373337569359)
            ·
              refine ⟨18875240923026560006354039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12583493948684373337569359 18875240923026560006354039)
              ·
                refine ⟨28312861384539840009531059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18875240923026560006354039 28312861384539840009531059)
                ·
                  refine ⟨42469292076809760014296589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28312861384539840009531059 42469292076809760014296589)
                  ·
                    refine ⟨15925984528803660005361221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42469292076809760014296589 15925984528803660005361221)
                    ·
                      refine ⟨2986122099150686251005229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15925984528803660005361221 2986122099150686251005229)
                      ·
                        rfl

theorem cell23_5815452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_5815452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5815452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5815452 prefixEnd_5815452 := by exact prefixLift 5815452
  have htrace : WordTrace (prefixWord ++ tailWord_5815452) baseStart_5815452 baseEnd_5815452 := by
    simpa [prefixWord, tailWord_5815452, baseEnd_5815452] using wordTrace_append hprefix tailTrace_5815452
  have hstable : (prefixWord ++ tailWord_5815452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5815452).length < 2 ^ (prefixWord ++ tailWord_5815452).sum := by decide
  have hdescent : baseEnd_5815452 < baseStart_5815452 := by decide
  rcases family_descends (prefixWord ++ tailWord_5815452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5815479 : List Nat := [1, 1, 3, 1, 4, 1, 1, 6, 1, 4]
def baseStart_5815479 : Nat := 118140960795 + 5815479 * 2 ^ 59
def prefixEnd_5815479 : Nat := 4983230072969 + 3 ^ 40 * 5815479 * 2
def baseEnd_5815479 : Nat := 995378654376119215122535

theorem tailTrace_5815479 : CollatzResearch.WordTrace tailWord_5815479 prefixEnd_5815479 995378654376119215122535 := by
  unfold tailWord_5815479
  simp only [CollatzResearch.WordTrace]
  refine ⟨212107944498520262585241491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141405296332346841723494327 212107944498520262585241491)
  ·
    refine ⟨318161916747780393877862237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212107944498520262585241491 318161916747780393877862237)
    ·
      refine ⟨119310718780417647704198339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 318161916747780393877862237 119310718780417647704198339)
      ·
        refine ⟨178966078170626471556297509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119310718780417647704198339 178966078170626471556297509)
        ·
          refine ⟨33556139656992463416805783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 178966078170626471556297509 33556139656992463416805783)
          ·
            refine ⟨50334209485488695125208675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33556139656992463416805783 50334209485488695125208675)
            ·
              refine ⟨75501314228233042687813013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50334209485488695125208675 75501314228233042687813013)
              ·
                refine ⟨3539124104448423875991235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 75501314228233042687813013 3539124104448423875991235)
                ·
                  refine ⟨5308686156672635813986853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3539124104448423875991235 5308686156672635813986853)
                  ·
                    refine ⟨995378654376119215122535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5308686156672635813986853 995378654376119215122535)
                    ·
                      rfl

theorem cell23_5815479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 6, 1, 4].length) (baseStart_5815479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5815479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5815479 prefixEnd_5815479 := by exact prefixLift 5815479
  have htrace : WordTrace (prefixWord ++ tailWord_5815479) baseStart_5815479 baseEnd_5815479 := by
    simpa [prefixWord, tailWord_5815479, baseEnd_5815479] using wordTrace_append hprefix tailTrace_5815479
  have hstable : (prefixWord ++ tailWord_5815479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5815479).length < 2 ^ (prefixWord ++ tailWord_5815479).sum := by decide
  have hdescent : baseEnd_5815479 < baseStart_5815479 := by decide
  rcases family_descends (prefixWord ++ tailWord_5815479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5815489 : List Nat := [1, 2, 6, 1, 1, 1, 1, 2, 1, 4, 3]
def baseStart_5815489 : Nat := 118140960795 + 5815489 * 2 ^ 59
def prefixEnd_5815489 : Nat := 4983230072969 + 3 ^ 40 * 5815489 * 2
def baseEnd_5815489 : Nat := 2986141097934902606242559

theorem tailTrace_5815489 : CollatzResearch.WordTrace tailWord_5815489 prefixEnd_5815489 2986141097934902606242559 := by
  unfold tailWord_5815489
  simp only [CollatzResearch.WordTrace]
  refine ⟨212108309228484034293105521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141405539485656022862070347 212108309228484034293105521)
  ·
    refine ⟨159081231921363025719829141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212108309228484034293105521 159081231921363025719829141)
    ·
      refine ⟨7456932746313891830616991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 159081231921363025719829141 7456932746313891830616991)
      ·
        refine ⟨11185399119470837745925487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7456932746313891830616991 11185399119470837745925487)
        ·
          refine ⟨16778098679206256618888231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11185399119470837745925487 16778098679206256618888231)
          ·
            refine ⟨25167148018809384928332347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16778098679206256618888231 25167148018809384928332347)
            ·
              refine ⟨37750722028214077392498521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25167148018809384928332347 37750722028214077392498521)
              ·
                refine ⟨28313041521160558044373891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37750722028214077392498521 28313041521160558044373891)
                ·
                  refine ⟨42469562281740837066560837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28313041521160558044373891 42469562281740837066560837)
                  ·
                    refine ⟨7963042927826406949980157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42469562281740837066560837 7963042927826406949980157)
                    ·
                      refine ⟨2986141097934902606242559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7963042927826406949980157 2986141097934902606242559)
                      ·
                        rfl

theorem cell23_5815489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_5815489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5815489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5815489 prefixEnd_5815489 := by exact prefixLift 5815489
  have htrace : WordTrace (prefixWord ++ tailWord_5815489) baseStart_5815489 baseEnd_5815489 := by
    simpa [prefixWord, tailWord_5815489, baseEnd_5815489] using wordTrace_append hprefix tailTrace_5815489
  have hstable : (prefixWord ++ tailWord_5815489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5815489).length < 2 ^ (prefixWord ++ tailWord_5815489).sum := by decide
  have hdescent : baseEnd_5815489 < baseStart_5815489 := by decide
  rcases family_descends (prefixWord ++ tailWord_5815489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5815542 : List Nat := [5, 1, 1, 1, 1, 1, 1, 1, 2, 5, 4]
def baseStart_5815542 : Nat := 118140960795 + 5815542 * 2 ^ 59
def prefixEnd_5815542 : Nat := 4983230072969 + 3 ^ 40 * 5815542 * 2
def baseEnd_5815542 : Nat := 2986168312409590898879815

theorem tailTrace_5815542 : CollatzResearch.WordTrace tailWord_5815542 prefixEnd_5815542 2986168312409590898879815 := by
  unfold tailWord_5815542
  simp only [CollatzResearch.WordTrace]
  refine ⟨13256890143580751521549055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 141406828198194682896523253 13256890143580751521549055)
  ·
    refine ⟨19885335215371127282323583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13256890143580751521549055 19885335215371127282323583)
    ·
      refine ⟨29828002823056690923485375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19885335215371127282323583 29828002823056690923485375)
      ·
        refine ⟨44742004234585036385228063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29828002823056690923485375 44742004234585036385228063)
        ·
          refine ⟨67113006351877554577842095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44742004234585036385228063 67113006351877554577842095)
          ·
            refine ⟨100669509527816331866763143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67113006351877554577842095 100669509527816331866763143)
            ·
              refine ⟨151004264291724497800144715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100669509527816331866763143 151004264291724497800144715)
              ·
                refine ⟨226506396437586746700217073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 151004264291724497800144715 226506396437586746700217073)
                ·
                  refine ⟨169879797328190060025162805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 226506396437586746700217073 169879797328190060025162805)
                  ·
                    refine ⟨15926230999517818127359013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 169879797328190060025162805 15926230999517818127359013)
                    ·
                      refine ⟨2986168312409590898879815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15926230999517818127359013 2986168312409590898879815)
                      ·
                        rfl

theorem cell23_5815542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 2, 5, 4].length) (baseStart_5815542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5815542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5815542 prefixEnd_5815542 := by exact prefixLift 5815542
  have htrace : WordTrace (prefixWord ++ tailWord_5815542) baseStart_5815542 baseEnd_5815542 := by
    simpa [prefixWord, tailWord_5815542, baseEnd_5815542] using wordTrace_append hprefix tailTrace_5815542
  have hstable : (prefixWord ++ tailWord_5815542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5815542).length < 2 ^ (prefixWord ++ tailWord_5815542).sum := by decide
  have hdescent : baseEnd_5815542 < baseStart_5815542 := by decide
  rcases family_descends (prefixWord ++ tailWord_5815542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5815556 : List Nat := [2, 3, 2, 2, 2, 3, 1, 2, 1, 5]
def baseStart_5815556 : Nat := 118140960795 + 5815556 * 2 ^ 59
def prefixEnd_5815556 : Nat := 4983230072969 + 3 ^ 40 * 5815556 * 2
def baseEnd_5815556 : Nat := 995391833712917948034917

theorem tailTrace_5815556 : CollatzResearch.WordTrace tailWord_5815556 prefixEnd_5815556 995391833712917948034917 := by
  unfold tailWord_5815556
  simp only [CollatzResearch.WordTrace]
  refine ⟨106055376459620652367897261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141407168612827536490529681 106055376459620652367897261)
  ·
    refine ⟨39770766172357744637961473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106055376459620652367897261 39770766172357744637961473)
    ·
      refine ⟨29828074629268308478471105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39770766172357744637961473 29828074629268308478471105)
      ·
        refine ⟨22371055971951231358853329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29828074629268308478471105 22371055971951231358853329)
        ·
          refine ⟨16778291978963423519139997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22371055971951231358853329 16778291978963423519139997)
          ·
            refine ⟨6291859492111283819677499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16778291978963423519139997 6291859492111283819677499)
            ·
              refine ⟨9437789238166925729516249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6291859492111283819677499 9437789238166925729516249)
              ·
                refine ⟨7078341928625194297137187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9437789238166925729516249 7078341928625194297137187)
                ·
                  refine ⟨10617512892937791445705781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7078341928625194297137187 10617512892937791445705781)
                  ·
                    refine ⟨995391833712917948034917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10617512892937791445705781 995391833712917948034917)
                    ·
                      rfl

theorem cell23_5815556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 1, 2, 1, 5].length) (baseStart_5815556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5815556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5815556 prefixEnd_5815556 := by exact prefixLift 5815556
  have htrace : WordTrace (prefixWord ++ tailWord_5815556) baseStart_5815556 baseEnd_5815556 := by
    simpa [prefixWord, tailWord_5815556, baseEnd_5815556] using wordTrace_append hprefix tailTrace_5815556
  have hstable : (prefixWord ++ tailWord_5815556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5815556).length < 2 ^ (prefixWord ++ tailWord_5815556).sum := by decide
  have hdescent : baseEnd_5815556 < baseStart_5815556 := by decide
  rcases family_descends (prefixWord ++ tailWord_5815556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5815576 : List Nat := [2, 1, 2, 3, 1, 4, 3, 1, 1, 1, 4]
def baseStart_5815576 : Nat := 118140960795 + 5815576 * 2 ^ 59
def prefixEnd_5815576 : Nat := 4983230072969 + 3 ^ 40 * 5815576 * 2
def baseEnd_5815576 : Nat := 2986185770751843765854659

theorem tailTrace_5815576 : CollatzResearch.WordTrace tailWord_5815576 prefixEnd_5815576 2986185770751843765854659 := by
  unfold tailWord_5815576
  simp only [CollatzResearch.WordTrace]
  refine ⟨106055741189584424075761291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141407654919445898767681721 106055741189584424075761291)
  ·
    refine ⟨159083611784376636113641937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106055741189584424075761291 159083611784376636113641937)
    ·
      refine ⟨119312708838282477085231453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159083611784376636113641937 119312708838282477085231453)
      ·
        refine ⟨44742265814355928906961795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119312708838282477085231453 44742265814355928906961795)
        ·
          refine ⟨67113398721533893360442693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44742265814355928906961795 67113398721533893360442693)
          ·
            refine ⟨12583762260287605005083005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67113398721533893360442693 12583762260287605005083005)
            ·
              refine ⟨4718910847607851876906127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12583762260287605005083005 4718910847607851876906127)
              ·
                refine ⟨7078366271411777815359191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4718910847607851876906127 7078366271411777815359191)
                ·
                  refine ⟨10617549407117666723038787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7078366271411777815359191 10617549407117666723038787)
                  ·
                    refine ⟨15926324110676500084558181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10617549407117666723038787 15926324110676500084558181)
                    ·
                      refine ⟨2986185770751843765854659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15926324110676500084558181 2986185770751843765854659)
                      ·
                        rfl

theorem cell23_5815576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 3, 1, 1, 1, 4].length) (baseStart_5815576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5815576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5815576 prefixEnd_5815576 := by exact prefixLift 5815576
  have htrace : WordTrace (prefixWord ++ tailWord_5815576) baseStart_5815576 baseEnd_5815576 := by
    simpa [prefixWord, tailWord_5815576, baseEnd_5815576] using wordTrace_append hprefix tailTrace_5815576
  have hstable : (prefixWord ++ tailWord_5815576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5815576).length < 2 ^ (prefixWord ++ tailWord_5815576).sum := by decide
  have hdescent : baseEnd_5815576 < baseStart_5815576 := by decide
  rcases family_descends (prefixWord ++ tailWord_5815576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5815642 : List Nat := [3, 1, 1, 2, 1, 2, 3, 2, 2, 6]
def baseStart_5815642 : Nat := 118140960795 + 5815642 * 2 ^ 59
def prefixEnd_5815642 : Nat := 4983230072969 + 3 ^ 40 * 5815642 * 2
def baseEnd_5815642 : Nat := 995406553491680169209785

theorem tailTrace_5815642 : CollatzResearch.WordTrace tailWord_5815642 prefixEnd_5815642 995406553491680169209785 := by
  unfold tailWord_5815642
  simp only [CollatzResearch.WordTrace]
  refine ⟨53028472399232435355856295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141409259731286494282283453 53028472399232435355856295)
  ·
    refine ⟨79542708598848653033784443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53028472399232435355856295 79542708598848653033784443)
    ·
      refine ⟨119314062898272979550676665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79542708598848653033784443 119314062898272979550676665)
      ·
        refine ⟨89485547173704734663007499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119314062898272979550676665 89485547173704734663007499)
        ·
          refine ⟨134228320760557101994511249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89485547173704734663007499 134228320760557101994511249)
          ·
            refine ⟨100671240570417826495883437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134228320760557101994511249 100671240570417826495883437)
            ·
              refine ⟨37751715213906684935956289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 100671240570417826495883437 37751715213906684935956289)
              ·
                refine ⟨28313786410430013701967217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37751715213906684935956289 28313786410430013701967217)
                ·
                  refine ⟨21235339807822510276475413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28313786410430013701967217 21235339807822510276475413)
                  ·
                    refine ⟨995406553491680169209785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21235339807822510276475413 995406553491680169209785)
                    ·
                      rfl

theorem cell23_5815642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 2, 2, 6].length) (baseStart_5815642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5815642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5815642 prefixEnd_5815642 := by exact prefixLift 5815642
  have htrace : WordTrace (prefixWord ++ tailWord_5815642) baseStart_5815642 baseEnd_5815642 := by
    simpa [prefixWord, tailWord_5815642, baseEnd_5815642] using wordTrace_append hprefix tailTrace_5815642
  have hstable : (prefixWord ++ tailWord_5815642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5815642).length < 2 ^ (prefixWord ++ tailWord_5815642).sum := by decide
  have hdescent : baseEnd_5815642 < baseStart_5815642 := by decide
  rcases family_descends (prefixWord ++ tailWord_5815642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5815649 : List Nat := [1, 2, 3, 1, 1, 1, 1, 4, 3, 4, 2]
def baseStart_5815649 : Nat := 118140960795 + 5815649 * 2 ^ 59
def prefixEnd_5815649 : Nat := 4983230072969 + 3 ^ 40 * 5815649 * 2
def baseEnd_5815649 : Nat := 2986223254839621980241823

theorem tailTrace_5815649 : CollatzResearch.WordTrace tailWord_5815649 prefixEnd_5815649 2986223254839621980241823 := by
  unfold tailWord_5815649
  simp only [CollatzResearch.WordTrace]
  refine ⟨212114144907904381618930001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141409429938602921079286667 212114144907904381618930001)
  ·
    refine ⟨159085608680928286214197501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212114144907904381618930001 159085608680928286214197501)
    ·
      refine ⟨59657103255348107330324063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 159085608680928286214197501 59657103255348107330324063)
      ·
        refine ⟨89485654883022160995486095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59657103255348107330324063 89485654883022160995486095)
        ·
          refine ⟨134228482324533241493229143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89485654883022160995486095 134228482324533241493229143)
          ·
            refine ⟨201342723486799862239843715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134228482324533241493229143 201342723486799862239843715)
            ·
              refine ⟨302014085230199793359765573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 201342723486799862239843715 302014085230199793359765573)
              ·
                refine ⟨56627640980662461254956045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 302014085230199793359765573 56627640980662461254956045)
                ·
                  refine ⟨21235365367748422970608517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56627640980662461254956045 21235365367748422970608517)
                  ·
                    refine ⟨3981631006452829306989097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21235365367748422970608517 3981631006452829306989097)
                    ·
                      refine ⟨2986223254839621980241823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3981631006452829306989097 2986223254839621980241823)
                      ·
                        rfl

theorem cell23_5815649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 4, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 4, 3, 4, 2].length) (baseStart_5815649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5815649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5815649 prefixEnd_5815649 := by exact prefixLift 5815649
  have htrace : WordTrace (prefixWord ++ tailWord_5815649) baseStart_5815649 baseEnd_5815649 := by
    simpa [prefixWord, tailWord_5815649, baseEnd_5815649] using wordTrace_append hprefix tailTrace_5815649
  have hstable : (prefixWord ++ tailWord_5815649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5815649).length < 2 ^ (prefixWord ++ tailWord_5815649).sum := by decide
  have hdescent : baseEnd_5815649 < baseStart_5815649 := by decide
  rcases family_descends (prefixWord ++ tailWord_5815649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5815719 : List Nat := [1, 1, 6, 1, 1, 1, 1, 2, 4, 5]
def baseStart_5815719 : Nat := 118140960795 + 5815719 * 2 ^ 59
def prefixEnd_5815719 : Nat := 4983230072969 + 3 ^ 40 * 5815719 * 2
def baseEnd_5815719 : Nat := 995419732828478902122167

theorem tailTrace_5815719 : CollatzResearch.WordTrace tailWord_5815719 prefixEnd_5815719 995419732828478902122167 := by
  unfold tailWord_5815719
  simp only [CollatzResearch.WordTrace]
  refine ⟨212116698017650783573978211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141411132011767189049318807 212116698017650783573978211)
  ·
    refine ⟨318175047026476175360967317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212116698017650783573978211 318175047026476175360967317)
    ·
      refine ⟨14914455329366070720045343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 318175047026476175360967317 14914455329366070720045343)
      ·
        refine ⟨22371682994049106080068015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14914455329366070720045343 22371682994049106080068015)
        ·
          refine ⟨33557524491073659120102023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22371682994049106080068015 33557524491073659120102023)
          ·
            refine ⟨50336286736610488680153035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33557524491073659120102023 50336286736610488680153035)
            ·
              refine ⟨75504430104915733020229553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50336286736610488680153035 75504430104915733020229553)
              ·
                refine ⟨56628322578686799765172165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75504430104915733020229553 56628322578686799765172165)
                ·
                  refine ⟨10617810483503774955969781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56628322578686799765172165 10617810483503774955969781)
                  ·
                    refine ⟨995419732828478902122167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10617810483503774955969781 995419732828478902122167)
                    ·
                      rfl

theorem cell23_5815719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 2, 4, 5].length) (baseStart_5815719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5815719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5815719 prefixEnd_5815719 := by exact prefixLift 5815719
  have htrace : WordTrace (prefixWord ++ tailWord_5815719) baseStart_5815719 baseEnd_5815719 := by
    simpa [prefixWord, tailWord_5815719, baseEnd_5815719] using wordTrace_append hprefix tailTrace_5815719
  have hstable : (prefixWord ++ tailWord_5815719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5815719).length < 2 ^ (prefixWord ++ tailWord_5815719).sum := by decide
  have hdescent : baseEnd_5815719 < baseStart_5815719 := by decide
  rcases family_descends (prefixWord ++ tailWord_5815719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5815756 : List Nat := [2, 2, 1, 4, 2, 1, 2, 2, 2, 1, 4]
def baseStart_5815756 : Nat := 118140960795 + 5815756 * 2 ^ 59
def prefixEnd_5815756 : Nat := 4983230072969 + 3 ^ 40 * 5815756 * 2
def baseEnd_5815756 : Nat := 2986278197269653061603831

theorem tailTrace_5815756 : CollatzResearch.WordTrace tailWord_5815756 prefixEnd_5815756 2986278197269653061603831 := by
  unfold tailWord_5815756
  simp only [CollatzResearch.WordTrace]
  refine ⟨106059023759258369446537561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141412031679011159262050081 106059023759258369446537561)
  ·
    refine ⟨79544267819443777084903171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106059023759258369446537561 79544267819443777084903171)
    ·
      refine ⟨119316401729165665627354757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79544267819443777084903171 119316401729165665627354757)
      ·
        refine ⟨22371825324218562305129017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 119316401729165665627354757 22371825324218562305129017)
        ·
          refine ⟨16778868993163921728846763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22371825324218562305129017 16778868993163921728846763)
          ·
            refine ⟨25168303489745882593270145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16778868993163921728846763 25168303489745882593270145)
            ·
              refine ⟨18876227617309411944952609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25168303489745882593270145 18876227617309411944952609)
              ·
                refine ⟨14157170712982058958714457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18876227617309411944952609 14157170712982058958714457)
                ·
                  refine ⟨10617878034736544219035843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14157170712982058958714457 10617878034736544219035843)
                  ·
                    refine ⟨15926817052104816328553765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10617878034736544219035843 15926817052104816328553765)
                    ·
                      refine ⟨2986278197269653061603831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15926817052104816328553765 2986278197269653061603831)
                      ·
                        rfl

theorem cell23_5815756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_5815756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5815756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5815756 prefixEnd_5815756 := by exact prefixLift 5815756
  have htrace : WordTrace (prefixWord ++ tailWord_5815756) baseStart_5815756 baseEnd_5815756 := by
    simpa [prefixWord, tailWord_5815756, baseEnd_5815756] using wordTrace_append hprefix tailTrace_5815756
  have hstable : (prefixWord ++ tailWord_5815756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5815756).length < 2 ^ (prefixWord ++ tailWord_5815756).sum := by decide
  have hdescent : baseEnd_5815756 < baseStart_5815756 := by decide
  rcases family_descends (prefixWord ++ tailWord_5815756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5815773 : List Nat := [1, 4, 3, 1, 1, 3, 1, 1, 2, 4, 2]
def baseStart_5815773 : Nat := 118140960795 + 5815773 * 2 ^ 59
def prefixEnd_5815773 : Nat := 4983230072969 + 3 ^ 40 * 5815773 * 2
def baseEnd_5815773 : Nat := 2986286926440779495091253

theorem tailTrace_5815773 : CollatzResearch.WordTrace tailWord_5815773 prefixEnd_5815773 2986286926440779495091253 := by
  unfold tailWord_5815773
  simp only [CollatzResearch.WordTrace]
  refine ⟨212118667559455150796443973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141412445039636767197629315 212118667559455150796443973)
  ·
    refine ⟨39772250167397840774333245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 212118667559455150796443973 39772250167397840774333245)
    ·
      refine ⟨14914593812774190290374967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39772250167397840774333245 14914593812774190290374967)
      ·
        refine ⟨22371890719161285435562451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14914593812774190290374967 22371890719161285435562451)
        ·
          refine ⟨33557836078741928153343677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22371890719161285435562451 33557836078741928153343677)
          ·
            refine ⟨12584188529528223057503879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33557836078741928153343677 12584188529528223057503879)
            ·
              refine ⟨18876282794292334586255819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12584188529528223057503879 18876282794292334586255819)
              ·
                refine ⟨28314424191438501879383729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18876282794292334586255819 28314424191438501879383729)
                ·
                  refine ⟨21235818143578876409537797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28314424191438501879383729 21235818143578876409537797)
                  ·
                    refine ⟨3981715901921039326788337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21235818143578876409537797 3981715901921039326788337)
                    ·
                      refine ⟨2986286926440779495091253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3981715901921039326788337 2986286926440779495091253)
                      ·
                        rfl

theorem cell23_5815773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 1, 2, 4, 2].length) (baseStart_5815773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5815773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5815773 prefixEnd_5815773 := by exact prefixLift 5815773
  have htrace : WordTrace (prefixWord ++ tailWord_5815773) baseStart_5815773 baseEnd_5815773 := by
    simpa [prefixWord, tailWord_5815773, baseEnd_5815773] using wordTrace_append hprefix tailTrace_5815773
  have hstable : (prefixWord ++ tailWord_5815773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5815773).length < 2 ^ (prefixWord ++ tailWord_5815773).sum := by decide
  have hdescent : baseEnd_5815773 < baseStart_5815773 := by decide
  rcases family_descends (prefixWord ++ tailWord_5815773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5815793 : List Nat := [1, 2, 2, 2, 3, 4, 1, 1, 2, 2, 3]
def baseStart_5815793 : Nat := 118140960795 + 5815793 * 2 ^ 59
def prefixEnd_5815793 : Nat := 4983230072969 + 3 ^ 40 * 5815793 * 2
def baseEnd_5815793 : Nat := 2986297196053869416841161

theorem tailTrace_5815793 : CollatzResearch.WordTrace tailWord_5815793 prefixEnd_5815793 2986297196053869416841161 := by
  unfold tailWord_5815793
  simp only [CollatzResearch.WordTrace]
  refine ⟨212119397019382694212172033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141412931346255129474781355 212119397019382694212172033)
  ·
    refine ⟨159089547764537020659129025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212119397019382694212172033 159089547764537020659129025)
    ·
      refine ⟨119317160823402765494346769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159089547764537020659129025 119317160823402765494346769)
      ·
        refine ⟨89487870617552074120760077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119317160823402765494346769 89487870617552074120760077)
        ·
          refine ⟨33557951481582027795285029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89487870617552074120760077 33557951481582027795285029)
          ·
            refine ⟨6292115902796630211615943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33557951481582027795285029 6292115902796630211615943)
            ·
              refine ⟨9438173854194945317423915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6292115902796630211615943 9438173854194945317423915)
              ·
                refine ⟨14157260781292417976135873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9438173854194945317423915 14157260781292417976135873)
                ·
                  refine ⟨10617945585969313482101905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14157260781292417976135873 10617945585969313482101905)
                  ·
                    refine ⟨7963459189476985111576429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10617945585969313482101905 7963459189476985111576429)
                    ·
                      refine ⟨2986297196053869416841161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7963459189476985111576429 2986297196053869416841161)
                      ·
                        rfl

theorem cell23_5815793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 1, 1, 2, 2, 3].length) (baseStart_5815793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5815793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5815793 prefixEnd_5815793 := by exact prefixLift 5815793
  have htrace : WordTrace (prefixWord ++ tailWord_5815793) baseStart_5815793 baseEnd_5815793 := by
    simpa [prefixWord, tailWord_5815793, baseEnd_5815793] using wordTrace_append hprefix tailTrace_5815793
  have hstable : (prefixWord ++ tailWord_5815793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5815793).length < 2 ^ (prefixWord ++ tailWord_5815793).sum := by decide
  have hdescent : baseEnd_5815793 < baseStart_5815793 := by decide
  rcases family_descends (prefixWord ++ tailWord_5815793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5815843 : List Nat := [1, 1, 1, 4, 5, 1, 2, 2, 1, 5]
def baseStart_5815843 : Nat := 118140960795 + 5815843 * 2 ^ 59
def prefixEnd_5815843 : Nat := 4983230072969 + 3 ^ 40 * 5815843 * 2
def baseEnd_5815843 : Nat := 995440956695531407071977

theorem tailTrace_5815843 : CollatzResearch.WordTrace tailWord_5815843 prefixEnd_5815843 995440956695531407071977 := by
  unfold tailWord_5815843
  simp only [CollatzResearch.WordTrace]
  refine ⟨212121220669201552751492183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141414147112801035167661455 212121220669201552751492183)
  ·
    refine ⟨318181831003802329127238275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212121220669201552751492183 318181831003802329127238275)
    ·
      refine ⟨477272746505703493690857413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 318181831003802329127238275 477272746505703493690857413)
      ·
        refine ⟨89488639969819405067035765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 477272746505703493690857413 89488639969819405067035765)
        ·
          refine ⟨8389559997170569225034603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 89488639969819405067035765 8389559997170569225034603)
          ·
            refine ⟨12584339995755853837551905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8389559997170569225034603 12584339995755853837551905)
            ·
              refine ⟨9438254996816890378163929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12584339995755853837551905 9438254996816890378163929)
              ·
                refine ⟨7078691247612667783622947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9438254996816890378163929 7078691247612667783622947)
                ·
                  refine ⟨10618036871419001675434421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7078691247612667783622947 10618036871419001675434421)
                  ·
                    refine ⟨995440956695531407071977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10618036871419001675434421 995440956695531407071977)
                    ·
                      rfl

theorem cell23_5815843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 2, 2, 1, 5].length) (baseStart_5815843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5815843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5815843 prefixEnd_5815843 := by exact prefixLift 5815843
  have htrace : WordTrace (prefixWord ++ tailWord_5815843) baseStart_5815843 baseEnd_5815843 := by
    simpa [prefixWord, tailWord_5815843, baseEnd_5815843] using wordTrace_append hprefix tailTrace_5815843
  have hstable : (prefixWord ++ tailWord_5815843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5815843).length < 2 ^ (prefixWord ++ tailWord_5815843).sum := by decide
  have hdescent : baseEnd_5815843 < baseStart_5815843 := by decide
  rcases family_descends (prefixWord ++ tailWord_5815843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5815866 : List Nat := [3, 1, 1, 1, 3, 2, 4, 1, 1, 1, 5]
def baseStart_5815866 : Nat := 118140960795 + 5815866 * 2 ^ 59
def prefixEnd_5815866 : Nat := 4983230072969 + 3 ^ 40 * 5815866 * 2
def baseEnd_5815866 : Nat := 2986334680141647631228325

theorem tailTrace_5815866 : CollatzResearch.WordTrace tailWord_5815866 prefixEnd_5815866 2986334680141647631228325 := by
  unfold tailWord_5815866
  simp only [CollatzResearch.WordTrace]
  refine ⟨53030514887029556919894863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141414706365412151786386301 53030514887029556919894863)
  ·
    refine ⟨79545772330544335379842295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53030514887029556919894863 79545772330544335379842295)
    ·
      refine ⟨119318658495816503069763443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79545772330544335379842295 119318658495816503069763443)
      ·
        refine ⟨178977987743724754604645165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119318658495816503069763443 178977987743724754604645165)
        ·
          refine ⟨67116745403896782976741937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 178977987743724754604645165 67116745403896782976741937)
          ·
            refine ⟨50337559052922587232556453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67116745403896782976741937 50337559052922587232556453)
            ·
              refine ⟨9438292322422985106104335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50337559052922587232556453 9438292322422985106104335)
              ·
                refine ⟨14157438483634477659156503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9438292322422985106104335 14157438483634477659156503)
                ·
                  refine ⟨21236157725451716488734755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14157438483634477659156503 21236157725451716488734755)
                  ·
                    refine ⟨31854236588177574733102133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21236157725451716488734755 31854236588177574733102133)
                    ·
                      refine ⟨2986334680141647631228325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31854236588177574733102133 2986334680141647631228325)
                      ·
                        rfl

theorem cell23_5815866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 4, 1, 1, 1, 5].length) (baseStart_5815866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5815866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5815866 prefixEnd_5815866 := by exact prefixLift 5815866
  have htrace : WordTrace (prefixWord ++ tailWord_5815866) baseStart_5815866 baseEnd_5815866 := by
    simpa [prefixWord, tailWord_5815866, baseEnd_5815866] using wordTrace_append hprefix tailTrace_5815866
  have hstable : (prefixWord ++ tailWord_5815866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5815866).length < 2 ^ (prefixWord ++ tailWord_5815866).sum := by decide
  have hdescent : baseEnd_5815866 < baseStart_5815866 := by decide
  rcases family_descends (prefixWord ++ tailWord_5815866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5815873 : List Nat := [1, 2, 5, 1, 1, 1, 2, 4, 2, 4]
def baseStart_5815873 : Nat := 118140960795 + 5815873 * 2 ^ 59
def prefixEnd_5815873 : Nat := 4983230072969 + 3 ^ 40 * 5815873 * 2
def baseEnd_5815873 : Nat := 995446091502076367946931

theorem tailTrace_5815873 : CollatzResearch.WordTrace tailWord_5815873 prefixEnd_5815873 995446091502076367946931 := by
  unfold tailWord_5815873
  simp only [CollatzResearch.WordTrace]
  refine ⟨212122314859092867875084273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141414876572728578583389515 212122314859092867875084273)
  ·
    refine ⟨159091736144319650906313205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212122314859092867875084273 159091736144319650906313205)
    ·
      refine ⟨14914850263529967272466863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 159091736144319650906313205 14914850263529967272466863)
      ·
        refine ⟨22372275395294950908700295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14914850263529967272466863 22372275395294950908700295)
        ·
          refine ⟨33558413092942426363050443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22372275395294950908700295 33558413092942426363050443)
          ·
            refine ⟨50337619639413639544575665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33558413092942426363050443 50337619639413639544575665)
            ·
              refine ⟨37753214729560229658431749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50337619639413639544575665 37753214729560229658431749)
              ·
                refine ⟨7078727761792543060955953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37753214729560229658431749 7078727761792543060955953)
                ·
                  refine ⟨5309045821344407295716965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7078727761792543060955953 5309045821344407295716965)
                  ·
                    refine ⟨995446091502076367946931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5309045821344407295716965 995446091502076367946931)
                    ·
                      rfl

theorem cell23_5815873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 4, 2, 4].length) (baseStart_5815873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5815873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5815873 prefixEnd_5815873 := by exact prefixLift 5815873
  have htrace : WordTrace (prefixWord ++ tailWord_5815873) baseStart_5815873 baseEnd_5815873 := by
    simpa [prefixWord, tailWord_5815873, baseEnd_5815873] using wordTrace_append hprefix tailTrace_5815873
  have hstable : (prefixWord ++ tailWord_5815873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5815873).length < 2 ^ (prefixWord ++ tailWord_5815873).sum := by decide
  have hdescent : baseEnd_5815873 < baseStart_5815873 := by decide
  rcases family_descends (prefixWord ++ tailWord_5815873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5815889 : List Nat := [1, 2, 2, 1, 3, 2, 1, 1, 2, 2, 6]
def baseStart_5815889 : Nat := 118140960795 + 5815889 * 2 ^ 59
def prefixEnd_5815889 : Nat := 4983230072969 + 3 ^ 40 * 5815889 * 2
def baseEnd_5815889 : Nat := 2986346490196701041240719

theorem tailTrace_5815889 : CollatzResearch.WordTrace tailWord_5815889 prefixEnd_5815889 2986346490196701041240719 := by
  unfold tailWord_5815889
  simp only [CollatzResearch.WordTrace]
  refine ⟨212122898427034902607666721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141415265618023268405111147 212122898427034902607666721)
  ·
    refine ⟨159092173820276176955750041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212122898427034902607666721 159092173820276176955750041)
    ·
      refine ⟨119319130365207132716812531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159092173820276176955750041 119319130365207132716812531)
      ·
        refine ⟨178978695547810699075218797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119319130365207132716812531 178978695547810699075218797)
        ·
          refine ⟨67117010830429012153207049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 178978695547810699075218797 67117010830429012153207049)
          ·
            refine ⟨50337758122821759114905287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67117010830429012153207049 50337758122821759114905287)
            ·
              refine ⟨75506637184232638672357931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50337758122821759114905287 75506637184232638672357931)
              ·
                refine ⟨113259955776348958008536897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75506637184232638672357931 113259955776348958008536897)
                ·
                  refine ⟨84944966832261718506402673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 113259955776348958008536897 84944966832261718506402673)
                  ·
                    refine ⟨63708725124196288879802005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 84944966832261718506402673 63708725124196288879802005)
                    ·
                      refine ⟨2986346490196701041240719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63708725124196288879802005 2986346490196701041240719)
                      ·
                        rfl

theorem cell23_5815889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 1, 2, 2, 6].length) (baseStart_5815889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5815889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5815889 prefixEnd_5815889 := by exact prefixLift 5815889
  have htrace : WordTrace (prefixWord ++ tailWord_5815889) baseStart_5815889 baseEnd_5815889 := by
    simpa [prefixWord, tailWord_5815889, baseEnd_5815889] using wordTrace_append hprefix tailTrace_5815889
  have hstable : (prefixWord ++ tailWord_5815889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5815889).length < 2 ^ (prefixWord ++ tailWord_5815889).sum := by decide
  have hdescent : baseEnd_5815889 < baseStart_5815889 := by decide
  rcases family_descends (prefixWord ++ tailWord_5815889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5815890 : List Nat := [3, 2, 2, 1, 2, 2, 4, 1, 2, 4]
def baseStart_5815890 : Nat := 118140960795 + 5815890 * 2 ^ 59
def prefixEnd_5815890 : Nat := 4983230072969 + 3 ^ 40 * 5815890 * 2
def baseEnd_5815890 : Nat := 995449001225785179109405

theorem tailTrace_5815890 : CollatzResearch.WordTrace tailWord_5815890 prefixEnd_5815890 995449001225785179109405 := by
  unfold tailWord_5815890
  simp only [CollatzResearch.WordTrace]
  refine ⟨53030733725007819944613281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141415289933354186518968749 53030733725007819944613281)
  ·
    refine ⟨39773050293755864958459961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53030733725007819944613281 39773050293755864958459961)
    ·
      refine ⟨29829787720316898718844971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39773050293755864958459961 29829787720316898718844971)
      ·
        refine ⟨44744681580475348078267457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29829787720316898718844971 44744681580475348078267457)
        ·
          refine ⟨33558511185356511058700593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44744681580475348078267457 33558511185356511058700593)
          ·
            refine ⟨25168883389017383294025445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33558511185356511058700593 25168883389017383294025445)
            ·
              refine ⟨4719165635440759367629771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25168883389017383294025445 4719165635440759367629771)
              ·
                refine ⟨7078748453161139051444657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4719165635440759367629771 7078748453161139051444657)
                ·
                  refine ⟨5309061339870854288583493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7078748453161139051444657 5309061339870854288583493)
                  ·
                    refine ⟨995449001225785179109405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5309061339870854288583493 995449001225785179109405)
                    ·
                      rfl

theorem cell23_5815890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 4, 1, 2, 4].length) (baseStart_5815890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5815890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5815890 prefixEnd_5815890 := by exact prefixLift 5815890
  have htrace : WordTrace (prefixWord ++ tailWord_5815890) baseStart_5815890 baseEnd_5815890 := by
    simpa [prefixWord, tailWord_5815890, baseEnd_5815890] using wordTrace_append hprefix tailTrace_5815890
  have hstable : (prefixWord ++ tailWord_5815890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5815890).length < 2 ^ (prefixWord ++ tailWord_5815890).sum := by decide
  have hdescent : baseEnd_5815890 < baseStart_5815890 := by decide
  rcases family_descends (prefixWord ++ tailWord_5815890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5815894 : List Nat := [5, 2, 2, 2, 1, 2, 1, 2, 1, 5]
def baseStart_5815894 : Nat := 118140960795 + 5815894 * 2 ^ 59
def prefixEnd_5815894 : Nat := 4983230072969 + 3 ^ 40 * 5815894 * 2
def baseEnd_5815894 : Nat := 995449685866657840559399

theorem tailTrace_5815894 : CollatzResearch.WordTrace tailWord_5815894 prefixEnd_5815894 995449685866657840559399 := by
  unfold tailWord_5815894
  simp only [CollatzResearch.WordTrace]
  refine ⟨13257692549501049278849921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 141415387194677858974399157 13257692549501049278849921)
  ·
    refine ⟨9943269412125786959137441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13257692549501049278849921 9943269412125786959137441)
    ·
      refine ⟨7457452059094340219353081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9943269412125786959137441 7457452059094340219353081)
      ·
        refine ⟨5593089044320755164514811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7457452059094340219353081 5593089044320755164514811)
        ·
          refine ⟨8389633566481132746772217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5593089044320755164514811 8389633566481132746772217)
          ·
            refine ⟨6292225174860849560079163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8389633566481132746772217 6292225174860849560079163)
            ·
              refine ⟨9438337762291274340118745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6292225174860849560079163 9438337762291274340118745)
              ·
                refine ⟨7078753321718455755089059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9438337762291274340118745 7078753321718455755089059)
                ·
                  refine ⟨10618129982577683632633589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7078753321718455755089059 10618129982577683632633589)
                  ·
                    refine ⟨995449685866657840559399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10618129982577683632633589 995449685866657840559399)
                    ·
                      rfl

theorem cell23_5815894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_5815894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5815894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5815894 prefixEnd_5815894 := by exact prefixLift 5815894
  have htrace : WordTrace (prefixWord ++ tailWord_5815894) baseStart_5815894 baseEnd_5815894 := by
    simpa [prefixWord, tailWord_5815894, baseEnd_5815894] using wordTrace_append hprefix tailTrace_5815894
  have hstable : (prefixWord ++ tailWord_5815894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5815894).length < 2 ^ (prefixWord ++ tailWord_5815894).sum := by decide
  have hdescent : baseEnd_5815894 < baseStart_5815894 := by decide
  rcases family_descends (prefixWord ++ tailWord_5815894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5815896 : List Nat := [2, 1, 2, 2, 1, 2, 1, 5, 1, 3, 3]
def baseStart_5815896 : Nat := 118140960795 + 5815896 * 2 ^ 59
def prefixEnd_5815896 : Nat := 4983230072969 + 3 ^ 40 * 5815896 * 2
def baseEnd_5815896 : Nat := 2986350084561282513853187

theorem tailTrace_5815896 : CollatzResearch.WordTrace tailWord_5815896 prefixEnd_5815896 2986350084561282513853187 := by
  unfold tailWord_5815896
  simp only [CollatzResearch.WordTrace]
  refine ⟨106061576869004771401585771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141415435825339695202114361 106061576869004771401585771)
  ·
    refine ⟨159092365303507157102378657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106061576869004771401585771 159092365303507157102378657)
    ·
      refine ⟨119319273977630367826783993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159092365303507157102378657 119319273977630367826783993)
      ·
        refine ⟨89489455483222775870087995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119319273977630367826783993 89489455483222775870087995)
        ·
          refine ⟨134234183224834163805131993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89489455483222775870087995 134234183224834163805131993)
          ·
            refine ⟨100675637418625622853848995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134234183224834163805131993 100675637418625622853848995)
            ·
              refine ⟨151013456127938434280773493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100675637418625622853848995 151013456127938434280773493)
              ·
                refine ⟨14157511511994228213822515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 151013456127938434280773493 14157511511994228213822515)
                ·
                  refine ⟨21236267267991342320733773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14157511511994228213822515 21236267267991342320733773)
                  ·
                    refine ⟨7963600225496753370275165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21236267267991342320733773 7963600225496753370275165)
                    ·
                      refine ⟨2986350084561282513853187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7963600225496753370275165 2986350084561282513853187)
                      ·
                        rfl

theorem cell23_5815896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 5, 1, 3, 3].length) (baseStart_5815896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5815896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5815896 prefixEnd_5815896 := by exact prefixLift 5815896
  have htrace : WordTrace (prefixWord ++ tailWord_5815896) baseStart_5815896 baseEnd_5815896 := by
    simpa [prefixWord, tailWord_5815896, baseEnd_5815896] using wordTrace_append hprefix tailTrace_5815896
  have hstable : (prefixWord ++ tailWord_5815896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5815896).length < 2 ^ (prefixWord ++ tailWord_5815896).sum := by decide
  have hdescent : baseEnd_5815896 < baseStart_5815896 := by decide
  rcases family_descends (prefixWord ++ tailWord_5815896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5815900 : List Nat := [2, 2, 4, 1, 2, 1, 3, 2, 1, 2, 3]
def baseStart_5815900 : Nat := 118140960795 + 5815900 * 2 ^ 59
def prefixEnd_5815900 : Nat := 4983230072969 + 3 ^ 40 * 5815900 * 2
def baseEnd_5815900 : Nat := 2986352138483900498203169

theorem tailTrace_5815900 : CollatzResearch.WordTrace tailWord_5815900 prefixEnd_5815900 2986352138483900498203169 := by
  unfold tailWord_5815900
  simp only [CollatzResearch.WordTrace]
  refine ⟨106061649814997525743158577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141415533086663367657544769 106061649814997525743158577)
  ·
    refine ⟨79546237361248144307368933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106061649814997525743158577 79546237361248144307368933)
    ·
      refine ⟨14914919505234027057631675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79546237361248144307368933 14914919505234027057631675)
      ·
        refine ⟨22372379257851040586447513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14914919505234027057631675 22372379257851040586447513)
        ·
          refine ⟨16779284443388280439835635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22372379257851040586447513 16779284443388280439835635)
          ·
            refine ⟨25168926665082420659753453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16779284443388280439835635 25168926665082420659753453)
            ·
              refine ⟨9438347499405907747407545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25168926665082420659753453 9438347499405907747407545)
              ·
                refine ⟨7078760624554430810555659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9438347499405907747407545 7078760624554430810555659)
                ·
                  refine ⟨10618140936831646215833489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7078760624554430810555659 10618140936831646215833489)
                  ·
                    refine ⟨7963605702623734661875117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10618140936831646215833489 7963605702623734661875117)
                    ·
                      refine ⟨2986352138483900498203169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7963605702623734661875117 2986352138483900498203169)
                      ·
                        rfl

theorem cell23_5815900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 3, 2, 1, 2, 3].length) (baseStart_5815900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5815900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5815900 prefixEnd_5815900 := by exact prefixLift 5815900
  have htrace : WordTrace (prefixWord ++ tailWord_5815900) baseStart_5815900 baseEnd_5815900 := by
    simpa [prefixWord, tailWord_5815900, baseEnd_5815900] using wordTrace_append hprefix tailTrace_5815900
  have hstable : (prefixWord ++ tailWord_5815900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5815900).length < 2 ^ (prefixWord ++ tailWord_5815900).sum := by decide
  have hdescent : baseEnd_5815900 < baseStart_5815900 := by decide
  rcases family_descends (prefixWord ++ tailWord_5815900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5815917 : List Nat := [1, 5, 1, 1, 4, 1, 3, 1, 1, 2, 3]
def baseStart_5815917 : Nat := 118140960795 + 5815917 * 2 ^ 59
def prefixEnd_5815917 : Nat := 4983230072969 + 3 ^ 40 * 5815917 * 2
def baseEnd_5815917 : Nat := 2986360867655026931690591

theorem tailTrace_5815917 : CollatzResearch.WordTrace tailWord_5815917 prefixEnd_5815917 2986360867655026931690591 := by
  unfold tailWord_5815917
  simp only [CollatzResearch.WordTrace]
  refine ⟨212123919670933463389686005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141415946447288975593124003 212123919670933463389686005)
  ·
    refine ⟨19886617469150012192783063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 212123919670933463389686005 19886617469150012192783063)
    ·
      refine ⟨29829926203725018289174595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19886617469150012192783063 29829926203725018289174595)
      ·
        refine ⟨44744889305587527433761893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29829926203725018289174595 44744889305587527433761893)
        ·
          refine ⟨8389666744797661393830355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44744889305587527433761893 8389666744797661393830355)
          ·
            refine ⟨12584500117196492090745533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8389666744797661393830355 12584500117196492090745533)
            ·
              refine ⟨4719187543948684534029575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12584500117196492090745533 4719187543948684534029575)
              ·
                refine ⟨7078781315923026801044363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4719187543948684534029575 7078781315923026801044363)
                ·
                  refine ⟨10618171973884540201566545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7078781315923026801044363 10618171973884540201566545)
                  ·
                    refine ⟨7963628980413405151174909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10618171973884540201566545 7963628980413405151174909)
                    ·
                      refine ⟨2986360867655026931690591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7963628980413405151174909 2986360867655026931690591)
                      ·
                        rfl

theorem cell23_5815917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 3, 1, 1, 2, 3].length) (baseStart_5815917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5815917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5815917 prefixEnd_5815917 := by exact prefixLift 5815917
  have htrace : WordTrace (prefixWord ++ tailWord_5815917) baseStart_5815917 baseEnd_5815917 := by
    simpa [prefixWord, tailWord_5815917, baseEnd_5815917] using wordTrace_append hprefix tailTrace_5815917
  have hstable : (prefixWord ++ tailWord_5815917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5815917).length < 2 ^ (prefixWord ++ tailWord_5815917).sum := by decide
  have hdescent : baseEnd_5815917 < baseStart_5815917 := by decide
  rcases family_descends (prefixWord ++ tailWord_5815917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5815946 : List Nat := [3, 1, 2, 3, 2, 1, 1, 1, 1, 8]
def baseStart_5815946 : Nat := 118140960795 + 5815946 * 2 ^ 59
def prefixEnd_5815946 : Nat := 4983230072969 + 3 ^ 40 * 5815946 * 2
def baseEnd_5815946 : Nat := 995458586198002439409319

theorem tailTrace_5815946 : CollatzResearch.WordTrace tailWord_5815946 prefixEnd_5815946 995458586198002439409319 := by
  unfold tailWord_5815946
  simp only [CollatzResearch.WordTrace]
  refine ⟨53031244346957100335622923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141416651591885600894994461 53031244346957100335622923)
  ·
    refine ⟨79546866520435650503434385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53031244346957100335622923 79546866520435650503434385)
    ·
      refine ⟨59660149890326737877575789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79546866520435650503434385 59660149890326737877575789)
      ·
        refine ⟨22372556208872526704090921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59660149890326737877575789 22372556208872526704090921)
        ·
          refine ⟨16779417156654395028068191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22372556208872526704090921 16779417156654395028068191)
          ·
            refine ⟨25169125734981592542102287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16779417156654395028068191 25169125734981592542102287)
            ·
              refine ⟨37753688602472388813153431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25169125734981592542102287 37753688602472388813153431)
              ·
                refine ⟨56630532903708583219730147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37753688602472388813153431 56630532903708583219730147)
                ·
                  refine ⟨84945799355562874829595221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56630532903708583219730147 84945799355562874829595221)
                  ·
                    refine ⟨995458586198002439409319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 84945799355562874829595221 995458586198002439409319)
                    ·
                      rfl

theorem cell23_5815946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 1, 1, 8].length) (baseStart_5815946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5815946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5815946 prefixEnd_5815946 := by exact prefixLift 5815946
  have htrace : WordTrace (prefixWord ++ tailWord_5815946) baseStart_5815946 baseEnd_5815946 := by
    simpa [prefixWord, tailWord_5815946, baseEnd_5815946] using wordTrace_append hprefix tailTrace_5815946
  have hstable : (prefixWord ++ tailWord_5815946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5815946).length < 2 ^ (prefixWord ++ tailWord_5815946).sum := by decide
  have hdescent : baseEnd_5815946 < baseStart_5815946 := by decide
  rcases family_descends (prefixWord ++ tailWord_5815946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5815993 : List Nat := [1, 2, 1, 4, 1, 1, 4, 4, 5]
def baseStart_5815993 : Nat := 118140960795 + 5815993 * 2 ^ 59
def prefixEnd_5815993 : Nat := 4983230072969 + 3 ^ 40 * 5815993 * 2
def baseEnd_5815993 : Nat := 331822210242752070482249

theorem tailTrace_5815993 : CollatzResearch.WordTrace tailWord_5815993 prefixEnd_5815993 331822210242752070482249 := by
  unfold tailWord_5815993
  simp only [CollatzResearch.WordTrace]
  refine ⟨212126691618658128369452633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141417794412438752246301755 212126691618658128369452633)
  ·
    refine ⟨159095018713993596277089475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212126691618658128369452633 159095018713993596277089475)
    ·
      refine ⟨238642528070990394415634213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159095018713993596277089475 238642528070990394415634213)
      ·
        refine ⟨44745474013310698952931415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 238642528070990394415634213 44745474013310698952931415)
        ·
          refine ⟨67118211019966048429397123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44745474013310698952931415 67118211019966048429397123)
          ·
            refine ⟨100677316529949072644095685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67118211019966048429397123 100677316529949072644095685)
            ·
              refine ⟨18876996849365451120767941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 100677316529949072644095685 18876996849365451120767941)
              ·
                refine ⟨3539436909256022085143989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18876996849365451120767941 3539436909256022085143989)
                ·
                  refine ⟨331822210242752070482249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3539436909256022085143989 331822210242752070482249)
                  ·
                    rfl

theorem cell23_5815993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 4, 5].length) (baseStart_5815993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5815993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5815993 prefixEnd_5815993 := by exact prefixLift 5815993
  have htrace : WordTrace (prefixWord ++ tailWord_5815993) baseStart_5815993 baseEnd_5815993 := by
    simpa [prefixWord, tailWord_5815993, baseEnd_5815993] using wordTrace_append hprefix tailTrace_5815993
  have hstable : (prefixWord ++ tailWord_5815993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5815993).length < 2 ^ (prefixWord ++ tailWord_5815993).sum := by decide
  have hdescent : baseEnd_5815993 < baseStart_5815993 := by decide
  rcases family_descends (prefixWord ++ tailWord_5815993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5816004 : List Nat := [2, 3, 3, 1, 1, 1, 5, 1, 2, 2, 2]
def baseStart_5816004 : Nat := 118140960795 + 5816004 * 2 ^ 59
def prefixEnd_5816004 : Nat := 4983230072969 + 3 ^ 40 * 5816004 * 2
def baseEnd_5816004 : Nat := 2986405540471968091302691

theorem tailTrace_5816004 : CollatzResearch.WordTrace tailWord_5816004 prefixEnd_5816004 2986405540471968091302691 := by
  unfold tailWord_5816004
  simp only [CollatzResearch.WordTrace]
  refine ⟨106063546410809138624051533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141418061881078851498735377 106063546410809138624051533)
  ·
    refine ⟨39773829904053426984019325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106063546410809138624051533 39773829904053426984019325)
    ·
      refine ⟨14915186214020035119007247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39773829904053426984019325 14915186214020035119007247)
      ·
        refine ⟨22372779321030052678510871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14915186214020035119007247 22372779321030052678510871)
        ·
          refine ⟨33559168981545079017766307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22372779321030052678510871 33559168981545079017766307)
          ·
            refine ⟨50338753472317618526649461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33559168981545079017766307 50338753472317618526649461)
            ·
              refine ⟨4719258138029776736873387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50338753472317618526649461 4719258138029776736873387)
              ·
                refine ⟨7078887207044665105310081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4719258138029776736873387 7078887207044665105310081)
                ·
                  refine ⟨5309165405283498828982561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7078887207044665105310081 5309165405283498828982561)
                  ·
                    refine ⟨3981874053962624121736921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5309165405283498828982561 3981874053962624121736921)
                    ·
                      refine ⟨2986405540471968091302691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3981874053962624121736921 2986405540471968091302691)
                      ·
                        rfl

theorem cell23_5816004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 5, 1, 2, 2, 2].length) (baseStart_5816004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5816004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5816004 prefixEnd_5816004 := by exact prefixLift 5816004
  have htrace : WordTrace (prefixWord ++ tailWord_5816004) baseStart_5816004 baseEnd_5816004 := by
    simpa [prefixWord, tailWord_5816004, baseEnd_5816004] using wordTrace_append hprefix tailTrace_5816004
  have hstable : (prefixWord ++ tailWord_5816004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5816004).length < 2 ^ (prefixWord ++ tailWord_5816004).sum := by decide
  have hdescent : baseEnd_5816004 < baseStart_5816004 := by decide
  rcases family_descends (prefixWord ++ tailWord_5816004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5816043 : List Nat := [1, 1, 1, 1, 2, 4, 2, 1, 4, 4, 2]
def baseStart_5816043 : Nat := 118140960795 + 5816043 * 2 ^ 59
def prefixEnd_5816043 : Nat := 4983230072969 + 3 ^ 40 * 5816043 * 2
def baseEnd_5816043 : Nat := 2986425566217493438715011

theorem tailTrace_5816043 : CollatzResearch.WordTrace tailWord_5816043 prefixEnd_5816043 2986425566217493438715011 := by
  unfold tailWord_5816043
  simp only [CollatzResearch.WordTrace]
  refine ⟨212128515268476986908772783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141419010178984657939181855 212128515268476986908772783)
  ·
    refine ⟨318192772902715480363159175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212128515268476986908772783 318192772902715480363159175)
    ·
      refine ⟨477289159354073220544738763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 318192772902715480363159175 477289159354073220544738763)
      ·
        refine ⟨715933739031109830817108145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 477289159354073220544738763 715933739031109830817108145)
        ·
          refine ⟨536950304273332373112831109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 715933739031109830817108145 536950304273332373112831109)
          ·
            refine ⟨100678182051249819958655833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 536950304273332373112831109 100678182051249819958655833)
            ·
              refine ⟨75508636538437364968991875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100678182051249819958655833 75508636538437364968991875)
              ·
                refine ⟨113262954807656047453487813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75508636538437364968991875 113262954807656047453487813)
                ·
                  refine ⟨21236804026435508897528965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 113262954807656047453487813 21236804026435508897528965)
                  ·
                    refine ⟨3981900754956657918286681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21236804026435508897528965 3981900754956657918286681)
                    ·
                      refine ⟨2986425566217493438715011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3981900754956657918286681 2986425566217493438715011)
                      ·
                        rfl

theorem cell23_5816043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 1, 4, 4, 2].length) (baseStart_5816043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5816043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5816043 prefixEnd_5816043 := by exact prefixLift 5816043
  have htrace : WordTrace (prefixWord ++ tailWord_5816043) baseStart_5816043 baseEnd_5816043 := by
    simpa [prefixWord, tailWord_5816043, baseEnd_5816043] using wordTrace_append hprefix tailTrace_5816043
  have hstable : (prefixWord ++ tailWord_5816043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5816043).length < 2 ^ (prefixWord ++ tailWord_5816043).sum := by decide
  have hdescent : baseEnd_5816043 < baseStart_5816043 := by decide
  rcases family_descends (prefixWord ++ tailWord_5816043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5816056 : List Nat := [2, 1, 2, 1, 1, 2, 2, 2, 2, 4, 4]
def baseStart_5816056 : Nat := 118140960795 + 5816056 * 2 ^ 59
def prefixEnd_5816056 : Nat := 4983230072969 + 3 ^ 40 * 5816056 * 2
def baseEnd_5816056 : Nat := 2986432241466001887852451

theorem tailTrace_5816056 : CollatzResearch.WordTrace tailWord_5816056 prefixEnd_5816056 2986432241466001887852451 := by
  unfold tailWord_5816056
  simp only [CollatzResearch.WordTrace]
  refine ⟨106064494708714945064498011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141419326278286593419330681 106064494708714945064498011)
  ·
    refine ⟨159096742063072417596747017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106064494708714945064498011 159096742063072417596747017)
    ·
      refine ⟨119322556547304313197560263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159096742063072417596747017 119322556547304313197560263)
      ·
        refine ⟨178983834820956469796340395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119322556547304313197560263 178983834820956469796340395)
        ·
          refine ⟨268475752231434704694510593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178983834820956469796340395 268475752231434704694510593)
          ·
            refine ⟨201356814173576028520882945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 268475752231434704694510593 201356814173576028520882945)
            ·
              refine ⟨151017610630182021390662209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 201356814173576028520882945 151017610630182021390662209)
              ·
                refine ⟨113263207972636516042996657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 151017610630182021390662209 113263207972636516042996657)
                ·
                  refine ⟨84947405979477387032247493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 113263207972636516042996657 84947405979477387032247493)
                  ·
                    refine ⟨15927638621152010068546405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 84947405979477387032247493 15927638621152010068546405)
                    ·
                      refine ⟨2986432241466001887852451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15927638621152010068546405 2986432241466001887852451)
                      ·
                        rfl

theorem cell23_5816056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 2, 4, 4].length) (baseStart_5816056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5816056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5816056 prefixEnd_5816056 := by exact prefixLift 5816056
  have htrace : WordTrace (prefixWord ++ tailWord_5816056) baseStart_5816056 baseEnd_5816056 := by
    simpa [prefixWord, tailWord_5816056, baseEnd_5816056] using wordTrace_append hprefix tailTrace_5816056
  have hstable : (prefixWord ++ tailWord_5816056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5816056).length < 2 ^ (prefixWord ++ tailWord_5816056).sum := by decide
  have hdescent : baseEnd_5816056 < baseStart_5816056 := by decide
  rcases family_descends (prefixWord ++ tailWord_5816056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5816100 : List Nat := [2, 3, 1, 3, 2, 2, 2, 2, 6]
def baseStart_5816100 : Nat := 118140960795 + 5816100 * 2 ^ 59
def prefixEnd_5816100 : Nat := 4983230072969 + 3 ^ 40 * 5816100 * 2
def baseEnd_5816100 : Nat := 331828314957199968411361

theorem tailTrace_5816100 : CollatzResearch.WordTrace tailWord_5816100 prefixEnd_5816100 331828314957199968411361 := by
  unfold tailWord_5816100
  simp only [CollatzResearch.WordTrace]
  refine ⟨106065297114635242821798877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141420396152846990429065169 106065297114635242821798877)
  ·
    refine ⟨39774486417988216058174579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106065297114635242821798877 39774486417988216058174579)
    ·
      refine ⟨59661729626982324087261869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39774486417988216058174579 59661729626982324087261869)
      ·
        refine ⟨22373148610118371532723201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59661729626982324087261869 22373148610118371532723201)
        ·
          refine ⟨16779861457588778649542401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22373148610118371532723201 16779861457588778649542401)
          ·
            refine ⟨12584896093191583987156801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16779861457588778649542401 12584896093191583987156801)
            ·
              refine ⟨9438672069893687990367601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12584896093191583987156801 9438672069893687990367601)
              ·
                refine ⟨7079004052420265992775701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9438672069893687990367601 7079004052420265992775701)
                ·
                  refine ⟨331828314957199968411361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7079004052420265992775701 331828314957199968411361)
                  ·
                    rfl

theorem cell23_5816100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 2, 2, 6].length) (baseStart_5816100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5816100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5816100 prefixEnd_5816100 := by exact prefixLift 5816100
  have htrace : WordTrace (prefixWord ++ tailWord_5816100) baseStart_5816100 baseEnd_5816100 := by
    simpa [prefixWord, tailWord_5816100, baseEnd_5816100] using wordTrace_append hprefix tailTrace_5816100
  have hstable : (prefixWord ++ tailWord_5816100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5816100).length < 2 ^ (prefixWord ++ tailWord_5816100).sum := by decide
  have hdescent : baseEnd_5816100 < baseStart_5816100 := by decide
  rcases family_descends (prefixWord ++ tailWord_5816100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5816104 : List Nat := [2, 1, 5, 1, 1, 2, 4, 2, 1, 4]
def baseStart_5816104 : Nat := 118140960795 + 5816104 * 2 ^ 59
def prefixEnd_5816104 : Nat := 4983230072969 + 3 ^ 40 * 5816104 * 2
def baseEnd_5816104 : Nat := 995485629512472566684077

theorem tailTrace_5816104 : CollatzResearch.WordTrace tailWord_5816104 prefixEnd_5816104 995485629512472566684077 := by
  unfold tailWord_5816104
  simp only [CollatzResearch.WordTrace]
  refine ⟨106065370060627997163371683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141420493414170662884495577 106065370060627997163371683)
  ·
    refine ⟨159098055090941995745057525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106065370060627997163371683 159098055090941995745057525)
    ·
      refine ⟨14915442664775812101099143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 159098055090941995745057525 14915442664775812101099143)
      ·
        refine ⟨22373163997163718151648715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14915442664775812101099143 22373163997163718151648715)
        ·
          refine ⟨33559745995745577227473073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22373163997163718151648715 33559745995745577227473073)
          ·
            refine ⟨25169809496809182920604805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33559745995745577227473073 25169809496809182920604805)
            ·
              refine ⟨4719339280651721797613401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25169809496809182920604805 4719339280651721797613401)
              ·
                refine ⟨3539504460488791348210051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4719339280651721797613401 3539504460488791348210051)
                ·
                  refine ⟨5309256690733187022315077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3539504460488791348210051 5309256690733187022315077)
                  ·
                    refine ⟨995485629512472566684077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5309256690733187022315077 995485629512472566684077)
                    ·
                      rfl

theorem cell23_5816104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 4, 2, 1, 4].length) (baseStart_5816104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5816104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5816104 prefixEnd_5816104 := by exact prefixLift 5816104
  have htrace : WordTrace (prefixWord ++ tailWord_5816104) baseStart_5816104 baseEnd_5816104 := by
    simpa [prefixWord, tailWord_5816104, baseEnd_5816104] using wordTrace_append hprefix tailTrace_5816104
  have hstable : (prefixWord ++ tailWord_5816104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5816104).length < 2 ^ (prefixWord ++ tailWord_5816104).sum := by decide
  have hdescent : baseEnd_5816104 < baseStart_5816104 := by decide
  rcases family_descends (prefixWord ++ tailWord_5816104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5816113 : List Nat := [1, 2, 2, 3, 2, 2, 1, 2, 3, 5]
def baseStart_5816113 : Nat := 118140960795 + 5816113 * 2 ^ 59
def prefixEnd_5816113 : Nat := 4983230072969 + 3 ^ 40 * 5816113 * 2
def baseEnd_5816113 : Nat := 995487169954436054946563

theorem tailTrace_5816113 : CollatzResearch.WordTrace tailWord_5816113 prefixEnd_5816113 995487169954436054946563 := by
  unfold tailWord_5816113
  simp only [CollatzResearch.WordTrace]
  refine ⟨212131068378223388863820993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141420712252148925909213995 212131068378223388863820993)
  ·
    refine ⟨159098301283667541647865745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212131068378223388863820993 159098301283667541647865745)
    ·
      refine ⟨119323725962750656235899309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159098301283667541647865745 119323725962750656235899309)
      ·
        refine ⟨44746397236031496088462241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119323725962750656235899309 44746397236031496088462241)
        ·
          refine ⟨33559797927023622066346681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44746397236031496088462241 33559797927023622066346681)
          ·
            refine ⟨25169848445267716549760011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33559797927023622066346681 25169848445267716549760011)
            ·
              refine ⟨37754772667901574824640017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25169848445267716549760011 37754772667901574824640017)
              ·
                refine ⟨28316079500926181118480013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37754772667901574824640017 28316079500926181118480013)
                ·
                  refine ⟨10618529812847317919430005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28316079500926181118480013 10618529812847317919430005)
                  ·
                    refine ⟨995487169954436054946563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10618529812847317919430005 995487169954436054946563)
                    ·
                      rfl

theorem cell23_5816113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 2, 3, 5].length) (baseStart_5816113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5816113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5816113 prefixEnd_5816113 := by exact prefixLift 5816113
  have htrace : WordTrace (prefixWord ++ tailWord_5816113) baseStart_5816113 baseEnd_5816113 := by
    simpa [prefixWord, tailWord_5816113, baseEnd_5816113] using wordTrace_append hprefix tailTrace_5816113
  have hstable : (prefixWord ++ tailWord_5816113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5816113).length < 2 ^ (prefixWord ++ tailWord_5816113).sum := by decide
  have hdescent : baseEnd_5816113 < baseStart_5816113 := by decide
  rcases family_descends (prefixWord ++ tailWord_5816113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5816127 : List Nat := [1, 1, 2, 2, 6, 1, 1, 2, 3, 1, 3]
def baseStart_5816127 : Nat := 118140960795 + 5816127 * 2 ^ 59
def prefixEnd_5816127 : Nat := 4983230072969 + 3 ^ 40 * 5816127 * 2
def baseEnd_5816127 : Nat := 2986468698592471110064625

theorem tailTrace_5816127 : CollatzResearch.WordTrace tailWord_5816127 prefixEnd_5816127 2986468698592471110064625 := by
  unfold tailWord_5816127
  simp only [CollatzResearch.WordTrace]
  refine ⟨212131579000172669254830635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141421052666781779503220423 212131579000172669254830635)
  ·
    refine ⟨318197368500259003882245953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212131579000172669254830635 318197368500259003882245953)
    ·
      refine ⟨238648026375194252911684465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 318197368500259003882245953 238648026375194252911684465)
      ·
        refine ⟨178986019781395689683763349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 238648026375194252911684465 178986019781395689683763349)
        ·
          refine ⟨8389969677252922953926407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 178986019781395689683763349 8389969677252922953926407)
          ·
            refine ⟨12584954515879384430889611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8389969677252922953926407 12584954515879384430889611)
            ·
              refine ⟨18877431773819076646334417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12584954515879384430889611 18877431773819076646334417)
              ·
                refine ⟨14158073830364307484750813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18877431773819076646334417 14158073830364307484750813)
                ·
                  refine ⟨5309277686386615306781555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14158073830364307484750813 5309277686386615306781555)
                  ·
                    refine ⟨7963916529579922960172333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5309277686386615306781555 7963916529579922960172333)
                    ·
                      refine ⟨2986468698592471110064625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7963916529579922960172333 2986468698592471110064625)
                      ·
                        rfl

theorem cell23_5816127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 2, 3, 1, 3].length) (baseStart_5816127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5816127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5816127 prefixEnd_5816127 := by exact prefixLift 5816127
  have htrace : WordTrace (prefixWord ++ tailWord_5816127) baseStart_5816127 baseEnd_5816127 := by
    simpa [prefixWord, tailWord_5816127, baseEnd_5816127] using wordTrace_append hprefix tailTrace_5816127
  have hstable : (prefixWord ++ tailWord_5816127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5816127).length < 2 ^ (prefixWord ++ tailWord_5816127).sum := by decide
  have hdescent : baseEnd_5816127 < baseStart_5816127 := by decide
  rcases family_descends (prefixWord ++ tailWord_5816127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5816133 : List Nat := [1, 3, 1, 1, 1, 2, 3, 3, 3, 1, 4]
def baseStart_5816133 : Nat := 118140960795 + 5816133 * 2 ^ 59
def prefixEnd_5816133 : Nat := 4983230072969 + 3 ^ 40 * 5816133 * 2
def baseEnd_5816133 : Nat := 2986471779476398086589597

theorem tailTrace_5816133 : CollatzResearch.WordTrace tailWord_5816133 prefixEnd_5816133 2986471779476398086589597 := by
  unfold tailWord_5816133
  simp only [CollatzResearch.WordTrace]
  refine ⟨212131797838150932279549053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141421198558767288186366035 212131797838150932279549053)
  ·
    refine ⟨79549424189306599604830895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 212131797838150932279549053 79549424189306599604830895)
    ·
      refine ⟨119324136283959899407246343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79549424189306599604830895 119324136283959899407246343)
      ·
        refine ⟨178986204425939849110869515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119324136283959899407246343 178986204425939849110869515)
        ·
          refine ⟨268479306638909773666304273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178986204425939849110869515 268479306638909773666304273)
          ·
            refine ⟨201359479979182330249728205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 268479306638909773666304273 201359479979182330249728205)
            ·
              refine ⟨75509804992193373843648077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 201359479979182330249728205 75509804992193373843648077)
              ·
                refine ⟨28316176872072515191368029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75509804992193373843648077 28316176872072515191368029)
                ·
                  refine ⟨10618566327027193196763011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28316176872072515191368029 10618566327027193196763011)
                  ·
                    refine ⟨15927849490540789795144517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10618566327027193196763011 15927849490540789795144517)
                    ·
                      refine ⟨2986471779476398086589597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15927849490540789795144517 2986471779476398086589597)
                      ·
                        rfl

theorem cell23_5816133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 3, 3, 1, 4].length) (baseStart_5816133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5816133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5816133 prefixEnd_5816133 := by exact prefixLift 5816133
  have htrace : WordTrace (prefixWord ++ tailWord_5816133) baseStart_5816133 baseEnd_5816133 := by
    simpa [prefixWord, tailWord_5816133, baseEnd_5816133] using wordTrace_append hprefix tailTrace_5816133
  have hstable : (prefixWord ++ tailWord_5816133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5816133).length < 2 ^ (prefixWord ++ tailWord_5816133).sum := by decide
  have hdescent : baseEnd_5816133 < baseStart_5816133 := by decide
  rcases family_descends (prefixWord ++ tailWord_5816133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5816153 : List Nat := [1, 2, 1, 2, 2, 3, 2, 3, 1, 1, 5]
def baseStart_5816153 : Nat := 118140960795 + 5816153 * 2 ^ 59
def prefixEnd_5816153 : Nat := 4983230072969 + 3 ^ 40 * 5816153 * 2
def baseEnd_5816153 : Nat := 2986482049089488008339505

theorem tailTrace_5816153 : CollatzResearch.WordTrace tailWord_5816153 prefixEnd_5816153 2986482049089488008339505 := by
  unfold tailWord_5816153
  simp only [CollatzResearch.WordTrace]
  refine ⟨212132527298078475695277113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141421684865385650463518075 212132527298078475695277113)
  ·
    refine ⟨159099395473558856771457835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212132527298078475695277113 159099395473558856771457835)
    ·
      refine ⟨238649093210338285157186753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159099395473558856771457835 238649093210338285157186753)
      ·
        refine ⟨178986819907753713867890065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 238649093210338285157186753 178986819907753713867890065)
        ·
          refine ⟨134240114930815285400917549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 178986819907753713867890065 134240114930815285400917549)
          ·
            refine ⟨50340043099055732025344081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 134240114930815285400917549 50340043099055732025344081)
            ·
              refine ⟨37755032324291799019008061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50340043099055732025344081 37755032324291799019008061)
              ·
                refine ⟨14158137121609424632128023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37755032324291799019008061 14158137121609424632128023)
                ·
                  refine ⟨21237205682414136948192035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14158137121609424632128023 21237205682414136948192035)
                  ·
                    refine ⟨31855808523621205422288053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21237205682414136948192035 31855808523621205422288053)
                    ·
                      refine ⟨2986482049089488008339505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31855808523621205422288053 2986482049089488008339505)
                      ·
                        rfl

theorem cell23_5816153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 3, 1, 1, 5].length) (baseStart_5816153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5816153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5816153 prefixEnd_5816153 := by exact prefixLift 5816153
  have htrace : WordTrace (prefixWord ++ tailWord_5816153) baseStart_5816153 baseEnd_5816153 := by
    simpa [prefixWord, tailWord_5816153, baseEnd_5816153] using wordTrace_append hprefix tailTrace_5816153
  have hstable : (prefixWord ++ tailWord_5816153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5816153).length < 2 ^ (prefixWord ++ tailWord_5816153).sum := by decide
  have hdescent : baseEnd_5816153 < baseStart_5816153 := by decide
  rcases family_descends (prefixWord ++ tailWord_5816153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5816160 : List Nat := [2, 1, 1, 3, 3, 3, 1, 1, 4, 4]
def baseStart_5816160 : Nat := 118140960795 + 5816160 * 2 ^ 59
def prefixEnd_5816160 : Nat := 4983230072969 + 3 ^ 40 * 5816160 * 2
def baseEnd_5816160 : Nat := 995495214484689826983991

theorem tailTrace_5816160 : CollatzResearch.WordTrace tailWord_5816160 prefixEnd_5816160 995495214484689826983991 := by
  unfold tailWord_5816160
  simp only [CollatzResearch.WordTrace]
  refine ⟨106066391304526557945390967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141421855072702077260521289 106066391304526557945390967)
  ·
    refine ⟨159099586956789836918086451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106066391304526557945390967 159099586956789836918086451)
    ·
      refine ⟨238649380435184755377129677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159099586956789836918086451 238649380435184755377129677)
      ·
        refine ⟨89493517663194283266423629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 238649380435184755377129677 89493517663194283266423629)
        ·
          refine ⟨33560069123697856224908861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89493517663194283266423629 33560069123697856224908861)
          ·
            refine ⟨12585025921386696084340823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33560069123697856224908861 12585025921386696084340823)
            ·
              refine ⟨18877538882080044126511235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12585025921386696084340823 18877538882080044126511235)
              ·
                refine ⟨28316308323120066189766853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18877538882080044126511235 28316308323120066189766853)
                ·
                  refine ⟨5309307810585012410581285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28316308323120066189766853 5309307810585012410581285)
                  ·
                    refine ⟨995495214484689826983991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5309307810585012410581285 995495214484689826983991)
                    ·
                      rfl

theorem cell23_5816160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 1, 4, 4].length) (baseStart_5816160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5816160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5816160 prefixEnd_5816160 := by exact prefixLift 5816160
  have htrace : WordTrace (prefixWord ++ tailWord_5816160) baseStart_5816160 baseEnd_5816160 := by
    simpa [prefixWord, tailWord_5816160, baseEnd_5816160] using wordTrace_append hprefix tailTrace_5816160
  have hstable : (prefixWord ++ tailWord_5816160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5816160).length < 2 ^ (prefixWord ++ tailWord_5816160).sum := by decide
  have hdescent : baseEnd_5816160 < baseStart_5816160 := by decide
  rcases family_descends (prefixWord ++ tailWord_5816160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5816177 : List Nat := [1, 2, 2, 2, 1, 3, 5, 1, 2, 4]
def baseStart_5816177 : Nat := 118140960795 + 5816177 * 2 ^ 59
def prefixEnd_5816177 : Nat := 4983230072969 + 3 ^ 40 * 5816177 * 2
def baseEnd_5816177 : Nat := 995498124208398638146465

theorem tailTrace_5816177 : CollatzResearch.WordTrace tailWord_5816177 prefixEnd_5816177 995498124208398638146465 := by
  unfold tailWord_5816177
  simp only [CollatzResearch.WordTrace]
  refine ⟨212133402649991527794150785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141422268433327685196100523 212133402649991527794150785)
  ·
    refine ⟨159100051987493645845613089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212133402649991527794150785 159100051987493645845613089)
    ·
      refine ⟨119325038990620234384209817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159100051987493645845613089 119325038990620234384209817)
      ·
        refine ⟨89493779242965175788157363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119325038990620234384209817 89493779242965175788157363)
        ·
          refine ⟨134240668864447763682236045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89493779242965175788157363 134240668864447763682236045)
          ·
            refine ⟨50340250824167911380838517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 134240668864447763682236045 50340250824167911380838517)
            ·
              refine ⟨4719398514765741691953611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50340250824167911380838517 4719398514765741691953611)
              ·
                refine ⟨7079097772148612537930417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4719398514765741691953611 7079097772148612537930417)
                ·
                  refine ⟨5309323329111459403447813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7079097772148612537930417 5309323329111459403447813)
                  ·
                    refine ⟨995498124208398638146465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5309323329111459403447813 995498124208398638146465)
                    ·
                      rfl

theorem cell23_5816177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 5, 1, 2, 4].length) (baseStart_5816177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5816177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5816177 prefixEnd_5816177 := by exact prefixLift 5816177
  have htrace : WordTrace (prefixWord ++ tailWord_5816177) baseStart_5816177 baseEnd_5816177 := by
    simpa [prefixWord, tailWord_5816177, baseEnd_5816177] using wordTrace_append hprefix tailTrace_5816177
  have hstable : (prefixWord ++ tailWord_5816177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5816177).length < 2 ^ (prefixWord ++ tailWord_5816177).sum := by decide
  have hdescent : baseEnd_5816177 < baseStart_5816177 := by decide
  rcases family_descends (prefixWord ++ tailWord_5816177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5816213 : List Nat := [1, 3, 2, 1, 1, 3, 1, 2, 2, 2, 5]
def baseStart_5816213 : Nat := 118140960795 + 5816213 * 2 ^ 59
def prefixEnd_5816213 : Nat := 4983230072969 + 3 ^ 40 * 5816213 * 2
def baseEnd_5816213 : Nat := 2986512857928757773589229

theorem tailTrace_5816213 : CollatzResearch.WordTrace tailWord_5816213 prefixEnd_5816213 2986512857928757773589229 := by
  unfold tailWord_5816213
  simp only [CollatzResearch.WordTrace]
  refine ⟨212134715677861105942461293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141423143785240737294974195 212134715677861105942461293)
  ·
    refine ⟨79550518379197914728422985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 212134715677861105942461293 79550518379197914728422985)
    ·
      refine ⟨59662888784398436046317239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79550518379197914728422985 59662888784398436046317239)
      ·
        refine ⟨89494333176597654069475859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59662888784398436046317239 89494333176597654069475859)
        ·
          refine ⟨134241499764896481104213789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89494333176597654069475859 134241499764896481104213789)
          ·
            refine ⟨50340562411836180414080171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 134241499764896481104213789 50340562411836180414080171)
            ·
              refine ⟨75510843617754270621120257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50340562411836180414080171 75510843617754270621120257)
              ·
                refine ⟨56633132713315702965840193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75510843617754270621120257 56633132713315702965840193)
                ·
                  refine ⟨42474849534986777224380145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56633132713315702965840193 42474849534986777224380145)
                  ·
                    refine ⟨31856137151240082918285109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42474849534986777224380145 31856137151240082918285109)
                    ·
                      refine ⟨2986512857928757773589229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31856137151240082918285109 2986512857928757773589229)
                      ·
                        rfl

theorem cell23_5816213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 2, 2, 2, 5].length) (baseStart_5816213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5816213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5816213 prefixEnd_5816213 := by exact prefixLift 5816213
  have htrace : WordTrace (prefixWord ++ tailWord_5816213) baseStart_5816213 baseEnd_5816213 := by
    simpa [prefixWord, tailWord_5816213, baseEnd_5816213] using wordTrace_append hprefix tailTrace_5816213
  have hstable : (prefixWord ++ tailWord_5816213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5816213).length < 2 ^ (prefixWord ++ tailWord_5816213).sum := by decide
  have hdescent : baseEnd_5816213 < baseStart_5816213 := by decide
  rcases family_descends (prefixWord ++ tailWord_5816213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5816218 : List Nat := [3, 1, 1, 4, 2, 2, 3, 2, 1, 2, 2]
def baseStart_5816218 : Nat := 118140960795 + 5816218 * 2 ^ 59
def prefixEnd_5816218 : Nat := 4983230072969 + 3 ^ 40 * 5816218 * 2
def baseEnd_5816218 : Nat := 2986515425332030254026707

theorem tailTrace_5816218 : CollatzResearch.WordTrace tailWord_5816218 prefixEnd_5816218 2986515425332030254026707 := by
  unfold tailWord_5816218
  simp only [CollatzResearch.WordTrace]
  refine ⟨53033724510710747949098327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141423265361895327864262205 53033724510710747949098327)
  ·
    refine ⟨79550586766066121923647491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53033724510710747949098327 79550586766066121923647491)
    ·
      refine ⟨119325880149099182885471237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79550586766066121923647491 119325880149099182885471237)
      ·
        refine ⟨22373602527956096791025857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 119325880149099182885471237 22373602527956096791025857)
        ·
          refine ⟨16780201895967072593269393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22373602527956096791025857 16780201895967072593269393)
          ·
            refine ⟨12585151421975304444952045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16780201895967072593269393 12585151421975304444952045)
            ·
              refine ⟨4719431783240739166857017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12585151421975304444952045 4719431783240739166857017)
              ·
                refine ⟨3539573837430554375142763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4719431783240739166857017 3539573837430554375142763)
                ·
                  refine ⟨5309360756145831562714145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3539573837430554375142763 5309360756145831562714145)
                  ·
                    refine ⟨3982020567109373672035609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5309360756145831562714145 3982020567109373672035609)
                    ·
                      refine ⟨2986515425332030254026707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3982020567109373672035609 2986515425332030254026707)
                      ·
                        rfl

theorem cell23_5816218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 3, 2, 1, 2, 2].length) (baseStart_5816218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5816218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5816218 prefixEnd_5816218 := by exact prefixLift 5816218
  have htrace : WordTrace (prefixWord ++ tailWord_5816218) baseStart_5816218 baseEnd_5816218 := by
    simpa [prefixWord, tailWord_5816218, baseEnd_5816218] using wordTrace_append hprefix tailTrace_5816218
  have hstable : (prefixWord ++ tailWord_5816218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5816218).length < 2 ^ (prefixWord ++ tailWord_5816218).sum := by decide
  have hdescent : baseEnd_5816218 < baseStart_5816218 := by decide
  rcases family_descends (prefixWord ++ tailWord_5816218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5816240 : List Nat := [2, 1, 1, 1, 2, 1, 1, 1, 7, 4, 2]
def baseStart_5816240 : Nat := 118140960795 + 5816240 * 2 ^ 59
def prefixEnd_5816240 : Nat := 4983230072969 + 3 ^ 40 * 5816240 * 2
def baseEnd_5816240 : Nat := 2986526721906429167951605

theorem tailTrace_5816240 : CollatzResearch.WordTrace tailWord_5816240 prefixEnd_5816240 2986526721906429167951605 := by
  unfold tailWord_5816240
  simp only [CollatzResearch.WordTrace]
  refine ⟨106067850224381644776847087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141423800299175526369129449 106067850224381644776847087)
  ·
    refine ⟨159101775336572467165270631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106067850224381644776847087 159101775336572467165270631)
    ·
      refine ⟨238652663004858700747905947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159101775336572467165270631 238652663004858700747905947)
      ·
        refine ⟨357978994507288051121858921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238652663004858700747905947 357978994507288051121858921)
        ·
          refine ⟨268484245880466038341394191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 357978994507288051121858921 268484245880466038341394191)
          ·
            refine ⟨402726368820699057512091287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 268484245880466038341394191 402726368820699057512091287)
            ·
              refine ⟨604089553231048586268136931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 402726368820699057512091287 604089553231048586268136931)
              ·
                refine ⟨906134329846572879402205397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 604089553231048586268136931 906134329846572879402205397)
                ·
                  refine ⟨21237523355779051860989189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 906134329846572879402205397 21237523355779051860989189)
                  ·
                    refine ⟨3982035629208572223935473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21237523355779051860989189 3982035629208572223935473)
                    ·
                      refine ⟨2986526721906429167951605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3982035629208572223935473 2986526721906429167951605)
                      ·
                        rfl

theorem cell23_5816240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 7, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 7, 4, 2].length) (baseStart_5816240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5816240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5816240 prefixEnd_5816240 := by exact prefixLift 5816240
  have htrace : WordTrace (prefixWord ++ tailWord_5816240) baseStart_5816240 baseEnd_5816240 := by
    simpa [prefixWord, tailWord_5816240, baseEnd_5816240] using wordTrace_append hprefix tailTrace_5816240
  have hstable : (prefixWord ++ tailWord_5816240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5816240).length < 2 ^ (prefixWord ++ tailWord_5816240).sum := by decide
  have hdescent : baseEnd_5816240 < baseStart_5816240 := by decide
  rcases family_descends (prefixWord ++ tailWord_5816240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5816243 : List Nat := [1, 1, 1, 2, 3, 1, 3, 1, 4, 1, 5]
def baseStart_5816243 : Nat := 118140960795 + 5816243 * 2 ^ 59
def prefixEnd_5816243 : Nat := 4983230072969 + 3 ^ 40 * 5816243 * 2
def baseEnd_5816243 : Nat := 2986528262348392656214091

theorem tailTrace_5816243 : CollatzResearch.WordTrace tailWord_5816243 prefixEnd_5816243 2986528262348392656214091 := by
  unfold tailWord_5816243
  simp only [CollatzResearch.WordTrace]
  refine ⟨212135809867752421066053383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141423873245168280710702255 212135809867752421066053383)
  ·
    refine ⟨318203714801628631599080075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212135809867752421066053383 318203714801628631599080075)
    ·
      refine ⟨477305572202442947398620113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 318203714801628631599080075 477305572202442947398620113)
      ·
        refine ⟨357979179151832210548965085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 477305572202442947398620113 357979179151832210548965085)
        ·
          refine ⟨134242192181937078955861907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 357979179151832210548965085 134242192181937078955861907)
          ·
            refine ⟨201363288272905618433792861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134242192181937078955861907 201363288272905618433792861)
            ·
              refine ⟨75511233102339606912672323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 201363288272905618433792861 75511233102339606912672323)
              ·
                refine ⟨113266849653509410369008485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75511233102339606912672323 113266849653509410369008485)
                ·
                  refine ⟨21237534310033014444189091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 113266849653509410369008485 21237534310033014444189091)
                  ·
                    refine ⟨31856301465049521666283637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21237534310033014444189091 31856301465049521666283637)
                    ·
                      refine ⟨2986528262348392656214091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31856301465049521666283637 2986528262348392656214091)
                      ·
                        rfl

theorem cell23_5816243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 1, 4, 1, 5].length) (baseStart_5816243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5816243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5816243 prefixEnd_5816243 := by exact prefixLift 5816243
  have htrace : WordTrace (prefixWord ++ tailWord_5816243) baseStart_5816243 baseEnd_5816243 := by
    simpa [prefixWord, tailWord_5816243, baseEnd_5816243] using wordTrace_append hprefix tailTrace_5816243
  have hstable : (prefixWord ++ tailWord_5816243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5816243).length < 2 ^ (prefixWord ++ tailWord_5816243).sum := by decide
  have hdescent : baseEnd_5816243 < baseStart_5816243 := by decide
  rcases family_descends (prefixWord ++ tailWord_5816243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5816270 : List Nat := [4, 1, 1, 1, 2, 2, 2, 2, 2, 2, 4]
def baseStart_5816270 : Nat := 118140960795 + 5816270 * 2 ^ 59
def prefixEnd_5816270 : Nat := 4983230072969 + 3 ^ 40 * 5816270 * 2
def baseEnd_5816270 : Nat := 2986542126326064050576467

theorem tailTrace_5816270 : CollatzResearch.WordTrace tailWord_5816270 prefixEnd_5816270 2986542126326064050576467 := by
  unfold tailWord_5816270
  simp only [CollatzResearch.WordTrace]
  refine ⟨26517099329831825584660783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 141424529759103069784857509 26517099329831825584660783)
  ·
    refine ⟨39775648994747738376991175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26517099329831825584660783 39775648994747738376991175)
    ·
      refine ⟨59663473492121607565486763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39775648994747738376991175 59663473492121607565486763)
      ·
        refine ⟨89495210238182411348230145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59663473492121607565486763 89495210238182411348230145)
        ·
          refine ⟨67121407678636808511172609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89495210238182411348230145 67121407678636808511172609)
          ·
            refine ⟨50341055758977606383379457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67121407678636808511172609 50341055758977606383379457)
            ·
              refine ⟨37755791819233204787534593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50341055758977606383379457 37755791819233204787534593)
              ·
                refine ⟨28316843864424903590650945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37755791819233204787534593 28316843864424903590650945)
                ·
                  refine ⟨21237632898318677692988209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28316843864424903590650945 21237632898318677692988209)
                  ·
                    refine ⟨15928224673739008269741157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21237632898318677692988209 15928224673739008269741157)
                    ·
                      refine ⟨2986542126326064050576467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15928224673739008269741157 2986542126326064050576467)
                      ·
                        rfl

theorem cell23_5816270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 2, 2, 2, 4].length) (baseStart_5816270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5816270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5816270 prefixEnd_5816270 := by exact prefixLift 5816270
  have htrace : WordTrace (prefixWord ++ tailWord_5816270) baseStart_5816270 baseEnd_5816270 := by
    simpa [prefixWord, tailWord_5816270, baseEnd_5816270] using wordTrace_append hprefix tailTrace_5816270
  have hstable : (prefixWord ++ tailWord_5816270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5816270).length < 2 ^ (prefixWord ++ tailWord_5816270).sum := by decide
  have hdescent : baseEnd_5816270 < baseStart_5816270 := by decide
  rcases family_descends (prefixWord ++ tailWord_5816270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5816323 : List Nat := [1, 1, 1, 3, 2, 1, 1, 2, 1, 10]
def baseStart_5816323 : Nat := 118140960795 + 5816323 * 2 ^ 59
def prefixEnd_5816323 : Nat := 4983230072969 + 3 ^ 40 * 5816323 * 2
def baseEnd_5816323 : Nat := 995523113600250781071241

theorem tailTrace_5816323 : CollatzResearch.WordTrace tailWord_5816323 prefixEnd_5816323 995523113600250781071241 := by
  unfold tailWord_5816323
  simp only [CollatzResearch.WordTrace]
  refine ⟨212138727707462594728965623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141425818471641729819310415 212138727707462594728965623)
  ·
    refine ⟨318208091561193892093448435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212138727707462594728965623 318208091561193892093448435)
    ·
      refine ⟨477312137341790838140172653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 318208091561193892093448435 477312137341790838140172653)
      ·
        refine ⟨178992051503171564302564745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 477312137341790838140172653 178992051503171564302564745)
        ·
          refine ⟨134244038627378673226923559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 178992051503171564302564745 134244038627378673226923559)
          ·
            refine ⟨201366057941068009840385339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134244038627378673226923559 201366057941068009840385339)
            ·
              refine ⟨302049086911602014760578009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 201366057941068009840385339 302049086911602014760578009)
              ·
                refine ⟨226536815183701511070433507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 302049086911602014760578009 226536815183701511070433507)
                ·
                  refine ⟨339805222775552266605650261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 226536815183701511070433507 339805222775552266605650261)
                  ·
                    refine ⟨995523113600250781071241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 339805222775552266605650261 995523113600250781071241)
                    ·
                      rfl

theorem cell23_5816323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 10].length) (baseStart_5816323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5816323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5816323 prefixEnd_5816323 := by exact prefixLift 5816323
  have htrace : WordTrace (prefixWord ++ tailWord_5816323) baseStart_5816323 baseEnd_5816323 := by
    simpa [prefixWord, tailWord_5816323, baseEnd_5816323] using wordTrace_append hprefix tailTrace_5816323
  have hstable : (prefixWord ++ tailWord_5816323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5816323).length < 2 ^ (prefixWord ++ tailWord_5816323).sum := by decide
  have hdescent : baseEnd_5816323 < baseStart_5816323 := by decide
  rcases family_descends (prefixWord ++ tailWord_5816323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5816357 : List Nat := [1, 3, 1, 2, 2, 3, 2, 2, 3, 4]
def baseStart_5816357 : Nat := 118140960795 + 5816357 * 2 ^ 59
def prefixEnd_5816357 : Nat := 4983230072969 + 3 ^ 40 * 5816357 * 2
def baseEnd_5816357 : Nat := 995528933047668403396189

theorem tailTrace_5816357 : CollatzResearch.WordTrace tailWord_5816357 prefixEnd_5816357 995528933047668403396189 := by
  unfold tailWord_5816357
  simp only [CollatzResearch.WordTrace]
  refine ⟨212139967789339418535703325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141426645192892945690468883 212139967789339418535703325)
  ·
    refine ⟨79552487921002281950888747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 212139967789339418535703325 79552487921002281950888747)
    ·
      refine ⟨119328731881503422926333121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79552487921002281950888747 119328731881503422926333121)
      ·
        refine ⟨89496548911127567194749841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119328731881503422926333121 89496548911127567194749841)
        ·
          refine ⟨67122411683345675396062381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89496548911127567194749841 67122411683345675396062381)
          ·
            refine ⟨25170904381254628273523393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67122411683345675396062381 25170904381254628273523393)
            ·
              refine ⟨18878178285940971205142545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25170904381254628273523393 18878178285940971205142545)
              ·
                refine ⟨14158633714455728403856909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18878178285940971205142545 14158633714455728403856909)
                ·
                  refine ⟨5309487642920898151446341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14158633714455728403856909 5309487642920898151446341)
                  ·
                    refine ⟨995528933047668403396189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5309487642920898151446341 995528933047668403396189)
                    ·
                      rfl

theorem cell23_5816357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 2, 3, 4].length) (baseStart_5816357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5816357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5816357 prefixEnd_5816357 := by exact prefixLift 5816357
  have htrace : WordTrace (prefixWord ++ tailWord_5816357) baseStart_5816357 baseEnd_5816357 := by
    simpa [prefixWord, tailWord_5816357, baseEnd_5816357] using wordTrace_append hprefix tailTrace_5816357
  have hstable : (prefixWord ++ tailWord_5816357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5816357).length < 2 ^ (prefixWord ++ tailWord_5816357).sum := by decide
  have hdescent : baseEnd_5816357 < baseStart_5816357 := by decide
  rcases family_descends (prefixWord ++ tailWord_5816357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5816370 : List Nat := [3, 2, 1, 1, 2, 3, 1, 2, 8]
def baseStart_5816370 : Nat := 118140960795 + 5816370 * 2 ^ 59
def prefixEnd_5816370 : Nat := 4983230072969 + 3 ^ 40 * 5816370 * 2
def baseEnd_5816370 : Nat := 331843719376834851036223

theorem tailTrace_5816370 : CollatzResearch.WordTrace tailWord_5816370 prefixEnd_5816370 331843719376834851036223 := by
  unfold tailWord_5816370
  simp only [CollatzResearch.WordTrace]
  refine ⟨53035110484573080438981641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141426961292194881170617709 53035110484573080438981641)
  ·
    refine ⟨39776332863429810329236231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53035110484573080438981641 39776332863429810329236231)
    ·
      refine ⟨59664499295144715493854347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39776332863429810329236231 59664499295144715493854347)
      ·
        refine ⟨89496748942717073240781521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59664499295144715493854347 89496748942717073240781521)
        ·
          refine ⟨67122561707037804930586141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89496748942717073240781521 67122561707037804930586141)
          ·
            refine ⟨25170960640139176848969803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67122561707037804930586141 25170960640139176848969803)
            ·
              refine ⟨37756440960208765273454705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25170960640139176848969803 37756440960208765273454705)
              ·
                refine ⟨28317330720156573955091029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37756440960208765273454705 28317330720156573955091029)
                ·
                  refine ⟨331843719376834851036223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28317330720156573955091029 331843719376834851036223)
                  ·
                    rfl

theorem cell23_5816370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 2, 8].length) (baseStart_5816370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5816370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5816370 prefixEnd_5816370 := by exact prefixLift 5816370
  have htrace : WordTrace (prefixWord ++ tailWord_5816370) baseStart_5816370 baseEnd_5816370 := by
    simpa [prefixWord, tailWord_5816370, baseEnd_5816370] using wordTrace_append hprefix tailTrace_5816370
  have hstable : (prefixWord ++ tailWord_5816370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5816370).length < 2 ^ (prefixWord ++ tailWord_5816370).sum := by decide
  have hdescent : baseEnd_5816370 < baseStart_5816370 := by decide
  rcases family_descends (prefixWord ++ tailWord_5816370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5816391 : List Nat := [1, 1, 4, 1, 3, 1, 5, 2, 1, 4]
def baseStart_5816391 : Nat := 118140960795 + 5816391 * 2 ^ 59
def prefixEnd_5816391 : Nat := 4983230072969 + 3 ^ 40 * 5816391 * 2
def baseEnd_5816391 : Nat := 995534752495086025721137

theorem tailTrace_5816391 : CollatzResearch.WordTrace tailWord_5816391 prefixEnd_5816391 995534752495086025721137 := by
  unfold tailWord_5816391
  simp only [CollatzResearch.WordTrace]
  refine ⟨212141207871216242342441027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141427471914144161561627351 212141207871216242342441027)
  ·
    refine ⟨318211811806824363513661541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212141207871216242342441027 318211811806824363513661541)
    ·
      refine ⟨59664714713779568158811539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 318211811806824363513661541 59664714713779568158811539)
      ·
        refine ⟨89497072070669352238217309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59664714713779568158811539 89497072070669352238217309)
        ·
          refine ⟨33561402026501007089331491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89497072070669352238217309 33561402026501007089331491)
          ·
            refine ⟨50342103039751510633997237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33561402026501007089331491 50342103039751510633997237)
            ·
              refine ⟨4719572159976704121937241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50342103039751510633997237 4719572159976704121937241)
              ·
                refine ⟨3539679119982528091452931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4719572159976704121937241 3539679119982528091452931)
                ·
                  refine ⟨5309518679973792137179397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3539679119982528091452931 5309518679973792137179397)
                  ·
                    refine ⟨995534752495086025721137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5309518679973792137179397 995534752495086025721137)
                    ·
                      rfl

theorem cell23_5816391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 5, 2, 1, 4].length) (baseStart_5816391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5816391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5816391 prefixEnd_5816391 := by exact prefixLift 5816391
  have htrace : WordTrace (prefixWord ++ tailWord_5816391) baseStart_5816391 baseEnd_5816391 := by
    simpa [prefixWord, tailWord_5816391, baseEnd_5816391] using wordTrace_append hprefix tailTrace_5816391
  have hstable : (prefixWord ++ tailWord_5816391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5816391).length < 2 ^ (prefixWord ++ tailWord_5816391).sum := by decide
  have hdescent : baseEnd_5816391 < baseStart_5816391 := by decide
  rcases family_descends (prefixWord ++ tailWord_5816391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5816407 : List Nat := [1, 1, 3, 2, 2, 1, 2, 1, 3, 5, 2]
def baseStart_5816407 : Nat := 118140960795 + 5816407 * 2 ^ 59
def prefixEnd_5816407 : Nat := 4983230072969 + 3 ^ 40 * 5816407 * 2
def baseEnd_5816407 : Nat := 2986612473175730014563337

theorem tailTrace_5816407 : CollatzResearch.WordTrace tailWord_5816407 prefixEnd_5816407 2986612473175730014563337 := by
  unfold tailWord_5816407
  simp only [CollatzResearch.WordTrace]
  refine ⟨212141791439158277075023475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141427860959438851383348983 212141791439158277075023475)
  ·
    refine ⟨318212687158737415612535213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212141791439158277075023475 318212687158737415612535213)
    ·
      refine ⟨119329757684526530854700705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 318212687158737415612535213 119329757684526530854700705)
      ·
        refine ⟨89497318263394898141025529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119329757684526530854700705 89497318263394898141025529)
        ·
          refine ⟨67122988697546173605769147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89497318263394898141025529 67122988697546173605769147)
          ·
            refine ⟨100684483046319260408653721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67122988697546173605769147 100684483046319260408653721)
            ·
              refine ⟨75513362284739445306490291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100684483046319260408653721 75513362284739445306490291)
              ·
                refine ⟨113270043427109167959735437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75513362284739445306490291 113270043427109167959735437)
                ·
                  refine ⟨42476266285165937984900789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 113270043427109167959735437 42476266285165937984900789)
                  ·
                    refine ⟨3982149964234306686084449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42476266285165937984900789 3982149964234306686084449)
                    ·
                      refine ⟨2986612473175730014563337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3982149964234306686084449 2986612473175730014563337)
                      ·
                        rfl

theorem cell23_5816407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 1, 3, 5, 2].length) (baseStart_5816407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5816407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5816407 prefixEnd_5816407 := by exact prefixLift 5816407
  have htrace : WordTrace (prefixWord ++ tailWord_5816407) baseStart_5816407 baseEnd_5816407 := by
    simpa [prefixWord, tailWord_5816407, baseEnd_5816407] using wordTrace_append hprefix tailTrace_5816407
  have hstable : (prefixWord ++ tailWord_5816407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5816407).length < 2 ^ (prefixWord ++ tailWord_5816407).sum := by decide
  have hdescent : baseEnd_5816407 < baseStart_5816407 := by decide
  rcases family_descends (prefixWord ++ tailWord_5816407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5816457 : List Nat := [1, 2, 1, 1, 4, 2, 1, 1, 5, 2, 3]
def baseStart_5816457 : Nat := 118140960795 + 5816457 * 2 ^ 59
def prefixEnd_5816457 : Nat := 4983230072969 + 3 ^ 40 * 5816457 * 2
def baseEnd_5816457 : Nat := 2986638147208454818938107

theorem tailTrace_5816457 : CollatzResearch.WordTrace tailWord_5816457 prefixEnd_5816457 2986638147208454818938107 := by
  unfold tailWord_5816457
  simp only [CollatzResearch.WordTrace]
  refine ⟨212143615088977135614343625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141429076725984757076229083 212143615088977135614343625)
  ·
    refine ⟨159107711316732851710757719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212143615088977135614343625 159107711316732851710757719)
    ·
      refine ⟨238661566975099277566136579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159107711316732851710757719 238661566975099277566136579)
      ·
        refine ⟨357992350462648916349204869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238661566975099277566136579 357992350462648916349204869)
        ·
          refine ⟨67123565711746671815475913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 357992350462648916349204869 67123565711746671815475913)
          ·
            refine ⟨50342674283810003861606935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67123565711746671815475913 50342674283810003861606935)
            ·
              refine ⟨75514011425715005792410403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50342674283810003861606935 75514011425715005792410403)
              ·
                refine ⟨113271017138572508688615605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75514011425715005792410403 113271017138572508688615605)
                ·
                  refine ⟨10619157856741172689557713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 113271017138572508688615605 10619157856741172689557713)
                  ·
                    refine ⟨7964368392555879517168285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10619157856741172689557713 7964368392555879517168285)
                    ·
                      refine ⟨2986638147208454818938107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7964368392555879517168285 2986638147208454818938107)
                      ·
                        rfl

theorem cell23_5816457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 1, 5, 2, 3].length) (baseStart_5816457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5816457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5816457 prefixEnd_5816457 := by exact prefixLift 5816457
  have htrace : WordTrace (prefixWord ++ tailWord_5816457) baseStart_5816457 baseEnd_5816457 := by
    simpa [prefixWord, tailWord_5816457, baseEnd_5816457] using wordTrace_append hprefix tailTrace_5816457
  have hstable : (prefixWord ++ tailWord_5816457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5816457).length < 2 ^ (prefixWord ++ tailWord_5816457).sum := by decide
  have hdescent : baseEnd_5816457 < baseStart_5816457 := by decide
  rcases family_descends (prefixWord ++ tailWord_5816457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5816504 : List Nat := [2, 1, 2, 1, 2, 1, 5, 1, 4, 1, 3]
def baseStart_5816504 : Nat := 118140960795 + 5816504 * 2 ^ 59
def prefixEnd_5816504 : Nat := 4983230072969 + 3 ^ 40 * 5816504 * 2
def baseEnd_5816504 : Nat := 2986662280799216135050391

theorem tailTrace_5816504 : CollatzResearch.WordTrace tailWord_5816504 prefixEnd_5816504 2986662280799216135050391 := by
  unfold tailWord_5816504
  simp only [CollatzResearch.WordTrace]
  refine ⟨106072664659903431320652283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141430219546537908427536377 106072664659903431320652283)
  ·
    refine ⟨159108996989855146980978425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106072664659903431320652283 159108996989855146980978425)
    ·
      refine ⟨119331747742391360235733819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159108996989855146980978425 119331747742391360235733819)
      ·
        refine ⟨178997621613587040353600729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119331747742391360235733819 178997621613587040353600729)
        ·
          refine ⟨134248216210190280265200547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 178997621613587040353600729 134248216210190280265200547)
          ·
            refine ⟨201372324315285420397800821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134248216210190280265200547 201372324315285420397800821)
            ·
              refine ⟨18878655404558008162293827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 201372324315285420397800821 18878655404558008162293827)
              ·
                refine ⟨28317983106837012243440741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18878655404558008162293827 28317983106837012243440741)
                ·
                  refine ⟨5309621832531939795645139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28317983106837012243440741 5309621832531939795645139)
                  ·
                    refine ⟨7964432748797909693467709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5309621832531939795645139 7964432748797909693467709)
                    ·
                      refine ⟨2986662280799216135050391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7964432748797909693467709 2986662280799216135050391)
                      ·
                        rfl

theorem cell23_5816504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 1, 4, 1, 3].length) (baseStart_5816504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5816504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5816504 prefixEnd_5816504 := by exact prefixLift 5816504
  have htrace : WordTrace (prefixWord ++ tailWord_5816504) baseStart_5816504 baseEnd_5816504 := by
    simpa [prefixWord, tailWord_5816504, baseEnd_5816504] using wordTrace_append hprefix tailTrace_5816504
  have hstable : (prefixWord ++ tailWord_5816504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5816504).length < 2 ^ (prefixWord ++ tailWord_5816504).sum := by decide
  have hdescent : baseEnd_5816504 < baseStart_5816504 := by decide
  rcases family_descends (prefixWord ++ tailWord_5816504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5816544 : List Nat := [2, 1, 1, 3, 1, 3, 2, 1, 3, 4, 2]
def baseStart_5816544 : Nat := 118140960795 + 5816544 * 2 ^ 59
def prefixEnd_5816544 : Nat := 4983230072969 + 3 ^ 40 * 5816544 * 2
def baseEnd_5816544 : Nat := 2986682820025395978550207

theorem tailTrace_5816544 : CollatzResearch.WordTrace tailWord_5816544 prefixEnd_5816544 2986682820025395978550207 := by
  unfold tailWord_5816544
  simp only [CollatzResearch.WordTrace]
  refine ⟨106073394119830974736380343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141431192159774632981840457 106073394119830974736380343)
  ·
    refine ⟨159110091179746462104570515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106073394119830974736380343 159110091179746462104570515)
    ·
      refine ⟨238665136769619693156855773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159110091179746462104570515 238665136769619693156855773)
      ·
        refine ⟨89499426288607384933820915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 238665136769619693156855773 89499426288607384933820915)
        ·
          refine ⟨134249139432911077400731373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89499426288607384933820915 134249139432911077400731373)
          ·
            refine ⟨50343427287341654025274265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 134249139432911077400731373 50343427287341654025274265)
            ·
              refine ⟨37757570465506240518955699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50343427287341654025274265 37757570465506240518955699)
              ·
                refine ⟨56636355698259360778433549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37757570465506240518955699 56636355698259360778433549)
                ·
                  refine ⟨21238633386847260291912581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56636355698259360778433549 21238633386847260291912581)
                  ·
                    refine ⟨3982243760033861304733609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21238633386847260291912581 3982243760033861304733609)
                    ·
                      refine ⟨2986682820025395978550207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3982243760033861304733609 2986682820025395978550207)
                      ·
                        rfl

theorem cell23_5816544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 1, 3, 4, 2].length) (baseStart_5816544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5816544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5816544 prefixEnd_5816544 := by exact prefixLift 5816544
  have htrace : WordTrace (prefixWord ++ tailWord_5816544) baseStart_5816544 baseEnd_5816544 := by
    simpa [prefixWord, tailWord_5816544, baseEnd_5816544] using wordTrace_append hprefix tailTrace_5816544
  have hstable : (prefixWord ++ tailWord_5816544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5816544).length < 2 ^ (prefixWord ++ tailWord_5816544).sum := by decide
  have hdescent : baseEnd_5816544 < baseStart_5816544 := by decide
  rcases family_descends (prefixWord ++ tailWord_5816544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5816561 : List Nat := [1, 2, 2, 2, 2, 1, 4, 1, 4, 2, 2]
def baseStart_5816561 : Nat := 118140960795 + 5816561 * 2 ^ 59
def prefixEnd_5816561 : Nat := 4983230072969 + 3 ^ 40 * 5816561 * 2
def baseEnd_5816561 : Nat := 2986691549196522412037629

theorem tailTrace_5816561 : CollatzResearch.WordTrace tailWord_5816561 prefixEnd_5816561 2986691549196522412037629 := by
  unfold tailWord_5816561
  simp only [CollatzResearch.WordTrace]
  refine ⟨212147408280600361376129537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141431605520400240917419691 212147408280600361376129537)
  ·
    refine ⟨159110556210450271032097153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212147408280600361376129537 159110556210450271032097153)
    ·
      refine ⟨119332917157837703274072865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159110556210450271032097153 119332917157837703274072865)
      ·
        refine ⟨89499687868378277455554649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119332917157837703274072865 89499687868378277455554649)
        ·
          refine ⟨67124765901283708091665987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89499687868378277455554649 67124765901283708091665987)
          ·
            refine ⟨100687148851925562137498981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67124765901283708091665987 100687148851925562137498981)
            ·
              refine ⟨18878840409736042900781059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 100687148851925562137498981 18878840409736042900781059)
              ·
                refine ⟨28318260614604064351171589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18878840409736042900781059 28318260614604064351171589)
                ·
                  refine ⟨5309673865238262065844673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28318260614604064351171589 5309673865238262065844673)
                  ·
                    refine ⟨3982255398928696549383505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5309673865238262065844673 3982255398928696549383505)
                    ·
                      refine ⟨2986691549196522412037629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3982255398928696549383505 2986691549196522412037629)
                      ·
                        rfl

theorem cell23_5816561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 1, 4, 2, 2].length) (baseStart_5816561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5816561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5816561 prefixEnd_5816561 := by exact prefixLift 5816561
  have htrace : WordTrace (prefixWord ++ tailWord_5816561) baseStart_5816561 baseEnd_5816561 := by
    simpa [prefixWord, tailWord_5816561, baseEnd_5816561] using wordTrace_append hprefix tailTrace_5816561
  have hstable : (prefixWord ++ tailWord_5816561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5816561).length < 2 ^ (prefixWord ++ tailWord_5816561).sum := by decide
  have hdescent : baseEnd_5816561 < baseStart_5816561 := by decide
  rcases family_descends (prefixWord ++ tailWord_5816561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5816574 : List Nat := [4, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4]
def baseStart_5816574 : Nat := 118140960795 + 5816574 * 2 ^ 59
def prefixEnd_5816574 : Nat := 4983230072969 + 3 ^ 40 * 5816574 * 2
def baseEnd_5816574 : Nat := 2986698224445030861175069

theorem tailTrace_5816574 : CollatzResearch.WordTrace tailWord_5816574 prefixEnd_5816574 2986698224445030861175069 := by
  unfold tailWord_5816574
  simp only [CollatzResearch.WordTrace]
  refine ⟨26518485303694158074544097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 141431921619702176397568517 26518485303694158074544097)
  ·
    refine ⟨19888863977770618555908073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26518485303694158074544097 19888863977770618555908073)
    ·
      refine ⟨14916647983327963916931055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19888863977770618555908073 14916647983327963916931055)
      ·
        refine ⟨22374971974991945875396583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14916647983327963916931055 22374971974991945875396583)
        ·
          refine ⟨33562457962487918813094875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22374971974991945875396583 33562457962487918813094875)
          ·
            refine ⟨50343686943731878219642313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33562457962487918813094875 50343686943731878219642313)
            ·
              refine ⟨37757765207798908664731735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50343686943731878219642313 37757765207798908664731735)
              ·
                refine ⟨56636647811698362997097603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37757765207798908664731735 56636647811698362997097603)
                ·
                  refine ⟨84954971717547544495646405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56636647811698362997097603 84954971717547544495646405)
                  ·
                    refine ⟨15929057197040164592933701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 84954971717547544495646405 15929057197040164592933701)
                    ·
                      refine ⟨2986698224445030861175069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15929057197040164592933701 2986698224445030861175069)
                      ·
                        rfl

theorem cell23_5816574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_5816574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5816574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5816574 prefixEnd_5816574 := by exact prefixLift 5816574
  have htrace : WordTrace (prefixWord ++ tailWord_5816574) baseStart_5816574 baseEnd_5816574 := by
    simpa [prefixWord, tailWord_5816574, baseEnd_5816574] using wordTrace_append hprefix tailTrace_5816574
  have hstable : (prefixWord ++ tailWord_5816574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5816574).length < 2 ^ (prefixWord ++ tailWord_5816574).sum := by decide
  have hdescent : baseEnd_5816574 < baseStart_5816574 := by decide
  rcases family_descends (prefixWord ++ tailWord_5816574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5816597 : List Nat := [1, 3, 2, 1, 2, 1, 2, 3, 1, 7]
def baseStart_5816597 : Nat := 118140960795 + 5816597 * 2 ^ 59
def prefixEnd_5816597 : Nat := 4983230072969 + 3 ^ 40 * 5816597 * 2
def baseEnd_5816597 : Nat := 995570011500028090395821

theorem tailTrace_5816597 : CollatzResearch.WordTrace tailWord_5816597 prefixEnd_5816597 995570011500028090395821 := by
  unfold tailWord_5816597
  simp only [CollatzResearch.WordTrace]
  refine ⟨212148721308469939524440045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141432480872313293016293363 212148721308469939524440045)
  ·
    refine ⟨79555770490676227321665017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 212148721308469939524440045 79555770490676227321665017)
    ·
      refine ⟨59666827868007170491248763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79555770490676227321665017 59666827868007170491248763)
      ·
        refine ⟨89500241802010755736873145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59666827868007170491248763 89500241802010755736873145)
        ·
          refine ⟨67125181351508066802654859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89500241802010755736873145 67125181351508066802654859)
          ·
            refine ⟨100687772027262100203982289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67125181351508066802654859 100687772027262100203982289)
            ·
              refine ⟨75515829020446575152986717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100687772027262100203982289 75515829020446575152986717)
              ·
                refine ⟨28318435882667465682370019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75515829020446575152986717 28318435882667465682370019)
                ·
                  refine ⟨42477653824001198523555029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28318435882667465682370019 42477653824001198523555029)
                  ·
                    refine ⟨995570011500028090395821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42477653824001198523555029 995570011500028090395821)
                    ·
                      rfl

theorem cell23_5816597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 3, 1, 7].length) (baseStart_5816597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5816597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5816597 prefixEnd_5816597 := by exact prefixLift 5816597
  have htrace : WordTrace (prefixWord ++ tailWord_5816597) baseStart_5816597 baseEnd_5816597 := by
    simpa [prefixWord, tailWord_5816597, baseEnd_5816597] using wordTrace_append hprefix tailTrace_5816597
  have hstable : (prefixWord ++ tailWord_5816597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5816597).length < 2 ^ (prefixWord ++ tailWord_5816597).sum := by decide
  have hdescent : baseEnd_5816597 < baseStart_5816597 := by decide
  rcases family_descends (prefixWord ++ tailWord_5816597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5816618 : List Nat := [3, 1, 4, 2, 2, 1, 1, 4, 5]
def baseStart_5816618 : Nat := 118140960795 + 5816618 * 2 ^ 59
def prefixEnd_5816618 : Nat := 4983230072969 + 3 ^ 40 * 5816618 * 2
def baseEnd_5816618 : Nat := 331857868621536521002763

theorem tailTrace_5816618 : CollatzResearch.WordTrace tailWord_5816618 prefixEnd_5816618 331857868621536521002763 := by
  unfold tailWord_5816618
  simp only [CollatzResearch.WordTrace]
  refine ⟨53037371810348465027738627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141432991494262573407303005 53037371810348465027738627)
  ·
    refine ⟨79556057715522697541607941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53037371810348465027738627 79556057715522697541607941)
    ·
      refine ⟨14916760821660505789051489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79556057715522697541607941 14916760821660505789051489)
      ·
        refine ⟨11187570616245379341788617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14916760821660505789051489 11187570616245379341788617)
        ·
          refine ⟨8390677962184034506341463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11187570616245379341788617 8390677962184034506341463)
          ·
            refine ⟨12586016943276051759512195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8390677962184034506341463 12586016943276051759512195)
            ·
              refine ⟨18879025414914077639268293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12586016943276051759512195 18879025414914077639268293)
              ·
                refine ⟨3539817265296389557362805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18879025414914077639268293 3539817265296389557362805)
                ·
                  refine ⟨331857868621536521002763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3539817265296389557362805 331857868621536521002763)
                  ·
                    rfl

theorem cell23_5816618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 4, 5].length) (baseStart_5816618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5816618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5816618 prefixEnd_5816618 := by exact prefixLift 5816618
  have htrace : WordTrace (prefixWord ++ tailWord_5816618) baseStart_5816618 baseEnd_5816618 := by
    simpa [prefixWord, tailWord_5816618, baseEnd_5816618] using wordTrace_append hprefix tailTrace_5816618
  have hstable : (prefixWord ++ tailWord_5816618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5816618).length < 2 ^ (prefixWord ++ tailWord_5816618).sum := by decide
  have hdescent : baseEnd_5816618 < baseStart_5816618 := by decide
  rcases family_descends (prefixWord ++ tailWord_5816618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5816687 : List Nat := [1, 1, 2, 1, 3, 1, 2, 1, 2, 9]
def baseStart_5816687 : Nat := 118140960795 + 5816687 * 2 ^ 59
def prefixEnd_5816687 : Nat := 4983230072969 + 3 ^ 40 * 5816687 * 2
def baseEnd_5816687 : Nat := 995585415919662973020683

theorem tailTrace_5816687 : CollatzResearch.WordTrace tailWord_5816687 prefixEnd_5816687 995585415919662973020683 := by
  unfold tailWord_5816687
  simp only [CollatzResearch.WordTrace]
  refine ⟨212152003878143884895216315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141434669252095923263477543 212152003878143884895216315)
  ·
    refine ⟨318228005817215827342824473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212152003878143884895216315 318228005817215827342824473)
    ·
      refine ⟨238671004362911870507118355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 318228005817215827342824473 238671004362911870507118355)
      ·
        refine ⟨358006506544367805760677533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238671004362911870507118355 358006506544367805760677533)
        ·
          refine ⟨134252439954137927160254075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 358006506544367805760677533 134252439954137927160254075)
          ·
            refine ⟨201378659931206890740381113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134252439954137927160254075 201378659931206890740381113)
            ·
              refine ⟨151033994948405168055285835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 201378659931206890740381113 151033994948405168055285835)
              ·
                refine ⟨226550992422607752082928753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 151033994948405168055285835 226550992422607752082928753)
                ·
                  refine ⟨169913244316955814062196565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 226550992422607752082928753 169913244316955814062196565)
                  ·
                    refine ⟨995585415919662973020683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 169913244316955814062196565 995585415919662973020683)
                    ·
                      rfl

theorem cell23_5816687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 2, 9].length) (baseStart_5816687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5816687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5816687 prefixEnd_5816687 := by exact prefixLift 5816687
  have htrace : WordTrace (prefixWord ++ tailWord_5816687) baseStart_5816687 baseEnd_5816687 := by
    simpa [prefixWord, tailWord_5816687, baseEnd_5816687] using wordTrace_append hprefix tailTrace_5816687
  have hstable : (prefixWord ++ tailWord_5816687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5816687).length < 2 ^ (prefixWord ++ tailWord_5816687).sum := by decide
  have hdescent : baseEnd_5816687 < baseStart_5816687 := by decide
  rcases family_descends (prefixWord ++ tailWord_5816687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5816711 : List Nat := [1, 1, 4, 2, 2, 1, 1, 3, 1, 5, 2]
def baseStart_5816711 : Nat := 118140960795 + 5816711 * 2 ^ 59
def prefixEnd_5816711 : Nat := 4983230072969 + 3 ^ 40 * 5816711 * 2
def baseEnd_5816711 : Nat := 2986768571294696825161939

theorem tailTrace_5816711 : CollatzResearch.WordTrace tailWord_5816711 prefixEnd_5816711 2986768571294696825161939 := by
  unfold tailWord_5816711
  simp only [CollatzResearch.WordTrace]
  refine ⟨212152879230056936994089987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141435252820037957996059991 212152879230056936994089987)
  ·
    refine ⟨318229318845085405491134981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212152879230056936994089987 318229318845085405491134981)
    ·
      refine ⟨59667997283453513529587809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 318229318845085405491134981 59667997283453513529587809)
      ·
        refine ⟨44750997962590135147190857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59667997283453513529587809 44750997962590135147190857)
        ·
          refine ⟨33563248471942601360393143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44750997962590135147190857 33563248471942601360393143)
          ·
            refine ⟨50344872707913902040589715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33563248471942601360393143 50344872707913902040589715)
            ·
              refine ⟨75517309061870853060884573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50344872707913902040589715 75517309061870853060884573)
              ·
                refine ⟨28318990898201569897831715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75517309061870853060884573 28318990898201569897831715)
                ·
                  refine ⟨42478486347302354846747573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28318990898201569897831715 42478486347302354846747573)
                  ·
                    refine ⟨3982358095059595766882585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42478486347302354846747573 3982358095059595766882585)
                    ·
                      refine ⟨2986768571294696825161939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3982358095059595766882585 2986768571294696825161939)
                      ·
                        rfl

theorem cell23_5816711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 3, 1, 5, 2].length) (baseStart_5816711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5816711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5816711 prefixEnd_5816711 := by exact prefixLift 5816711
  have htrace : WordTrace (prefixWord ++ tailWord_5816711) baseStart_5816711 baseEnd_5816711 := by
    simpa [prefixWord, tailWord_5816711, baseEnd_5816711] using wordTrace_append hprefix tailTrace_5816711
  have hstable : (prefixWord ++ tailWord_5816711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5816711).length < 2 ^ (prefixWord ++ tailWord_5816711).sum := by decide
  have hdescent : baseEnd_5816711 < baseStart_5816711 := by decide
  rcases family_descends (prefixWord ++ tailWord_5816711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5816728 : List Nat := [2, 1, 2, 5, 1, 1, 1, 1, 4, 3, 2]
def baseStart_5816728 : Nat := 118140960795 + 5816728 * 2 ^ 59
def prefixEnd_5816728 : Nat := 4983230072969 + 3 ^ 40 * 5816728 * 2
def baseEnd_5816728 : Nat := 2986777300465823258649361

theorem tailTrace_5816728 : CollatzResearch.WordTrace tailWord_5816728 prefixEnd_5816728 2986777300465823258649361 := by
  unfold tailWord_5816728
  simp only [CollatzResearch.WordTrace]
  refine ⟨106076749635497674448729419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141435666180663565931639225 106076749635497674448729419)
  ·
    refine ⟨159115124453246511673094129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106076749635497674448729419 159115124453246511673094129)
    ·
      refine ⟨119336343339934883754820597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159115124453246511673094129 119336343339934883754820597)
      ·
        refine ⟨11187782188118895352014431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 119336343339934883754820597 11187782188118895352014431)
        ·
          refine ⟨16781673282178343028021647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11187782188118895352014431 16781673282178343028021647)
          ·
            refine ⟨25172509923267514542032471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16781673282178343028021647 25172509923267514542032471)
            ·
              refine ⟨37758764884901271813048707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25172509923267514542032471 37758764884901271813048707)
              ·
                refine ⟨56638147327351907719573061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37758764884901271813048707 56638147327351907719573061)
                ·
                  refine ⟨10619652623878482697419949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56638147327351907719573061 10619652623878482697419949)
                  ·
                    refine ⟨3982369733954431011532481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10619652623878482697419949 3982369733954431011532481)
                    ·
                      refine ⟨2986777300465823258649361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3982369733954431011532481 2986777300465823258649361)
                      ·
                        rfl

theorem cell23_5816728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 1, 4, 3, 2].length) (baseStart_5816728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5816728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5816728 prefixEnd_5816728 := by exact prefixLift 5816728
  have htrace : WordTrace (prefixWord ++ tailWord_5816728) baseStart_5816728 baseEnd_5816728 := by
    simpa [prefixWord, tailWord_5816728, baseEnd_5816728] using wordTrace_append hprefix tailTrace_5816728
  have hstable : (prefixWord ++ tailWord_5816728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5816728).length < 2 ^ (prefixWord ++ tailWord_5816728).sum := by decide
  have hdescent : baseEnd_5816728 < baseStart_5816728 := by decide
  rcases family_descends (prefixWord ++ tailWord_5816728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5816754 : List Nat := [3, 2, 1, 1, 1, 1, 3, 3, 1, 1, 6]
def baseStart_5816754 : Nat := 118140960795 + 5816754 * 2 ^ 59
def prefixEnd_5816754 : Nat := 4983230072969 + 3 ^ 40 * 5816754 * 2
def baseEnd_5816754 : Nat := 2986790650962840156924241

theorem tailTrace_5816754 : CollatzResearch.WordTrace tailWord_5816754 prefixEnd_5816754 2986790650962840156924241 := by
  unfold tailWord_5816754
  simp only [CollatzResearch.WordTrace]
  refine ⟨53038611892225288834476329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141436298379267436891936877 53038611892225288834476329)
  ·
    refine ⟨39778958919168966625857247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53038611892225288834476329 39778958919168966625857247)
    ·
      refine ⟨59668438378753449938785871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39778958919168966625857247 59668438378753449938785871)
      ·
        refine ⟨89502657568130174908178807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59668438378753449938785871 89502657568130174908178807)
        ·
          refine ⟨134253986352195262362268211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89502657568130174908178807 134253986352195262362268211)
          ·
            refine ⟨201380979528292893543402317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134253986352195262362268211 201380979528292893543402317)
            ·
              refine ⟨75517867323109835078775869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 201380979528292893543402317 75517867323109835078775869)
              ·
                refine ⟨28319200246166188154540951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75517867323109835078775869 28319200246166188154540951)
                ·
                  refine ⟨42478800369249282231811427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28319200246166188154540951 42478800369249282231811427)
                  ·
                    refine ⟨63718200553873923347717141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42478800369249282231811427 63718200553873923347717141)
                    ·
                      refine ⟨2986790650962840156924241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63718200553873923347717141 2986790650962840156924241)
                      ·
                        rfl

theorem cell23_5816754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 3, 1, 1, 6].length) (baseStart_5816754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5816754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5816754 prefixEnd_5816754 := by exact prefixLift 5816754
  have htrace : WordTrace (prefixWord ++ tailWord_5816754) baseStart_5816754 baseEnd_5816754 := by
    simpa [prefixWord, tailWord_5816754, baseEnd_5816754] using wordTrace_append hprefix tailTrace_5816754
  have hstable : (prefixWord ++ tailWord_5816754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5816754).length < 2 ^ (prefixWord ++ tailWord_5816754).sum := by decide
  have hdescent : baseEnd_5816754 < baseStart_5816754 := by decide
  rcases family_descends (prefixWord ++ tailWord_5816754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5816786 : List Nat := [3, 2, 2, 4, 1, 2, 2, 2, 1, 1, 3]
def baseStart_5816786 : Nat := 118140960795 + 5816786 * 2 ^ 59
def prefixEnd_5816786 : Nat := 4983230072969 + 3 ^ 40 * 5816786 * 2
def baseEnd_5816786 : Nat := 2986807082343784031724095

theorem tailTrace_5816786 : CollatzResearch.WordTrace tailWord_5816786 prefixEnd_5816786 2986807082343784031724095 := by
  unfold tailWord_5816786
  simp only [CollatzResearch.WordTrace]
  refine ⟨53038903676196306200767553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141437076469856816535380141 53038903676196306200767553)
  ·
    refine ⟨39779177757147229650575665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53038903676196306200767553 39779177757147229650575665)
    ·
      refine ⟨29834383317860422237931749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39779177757147229650575665 29834383317860422237931749)
      ·
        refine ⟨5593946872098829169612203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29834383317860422237931749 5593946872098829169612203)
        ·
          refine ⟨8390920308148243754418305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5593946872098829169612203 8390920308148243754418305)
          ·
            refine ⟨6293190231111182815813729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8390920308148243754418305 6293190231111182815813729)
            ·
              refine ⟨4719892673333387111860297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6293190231111182815813729 4719892673333387111860297)
              ·
                refine ⟨3539919505000040333895223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4719892673333387111860297 3539919505000040333895223)
                ·
                  refine ⟨5309879257500060500842835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3539919505000040333895223 5309879257500060500842835)
                  ·
                    refine ⟨7964818886250090751264253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5309879257500060500842835 7964818886250090751264253)
                    ·
                      refine ⟨2986807082343784031724095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7964818886250090751264253 2986807082343784031724095)
                      ·
                        rfl

theorem cell23_5816786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 2, 2, 1, 1, 3].length) (baseStart_5816786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5816786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5816786 prefixEnd_5816786 := by exact prefixLift 5816786
  have htrace : WordTrace (prefixWord ++ tailWord_5816786) baseStart_5816786 baseEnd_5816786 := by
    simpa [prefixWord, tailWord_5816786, baseEnd_5816786] using wordTrace_append hprefix tailTrace_5816786
  have hstable : (prefixWord ++ tailWord_5816786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5816786).length < 2 ^ (prefixWord ++ tailWord_5816786).sum := by decide
  have hdescent : baseEnd_5816786 < baseStart_5816786 := by decide
  rcases family_descends (prefixWord ++ tailWord_5816786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5816794 : List Nat := [3, 1, 1, 2, 3, 1, 1, 1, 1, 9]
def baseStart_5816794 : Nat := 118140960795 + 5816794 * 2 ^ 59
def prefixEnd_5816794 : Nat := 4983230072969 + 3 ^ 40 * 5816794 * 2
def baseEnd_5816794 : Nat := 995603730063006666808019

theorem tailTrace_5816794 : CollatzResearch.WordTrace tailWord_5816794 prefixEnd_5816794 995603730063006666808019 := by
  unfold tailWord_5816794
  simp only [CollatzResearch.WordTrace]
  refine ⟨53038976622189060542340359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141437270992504161446240957 53038976622189060542340359)
  ·
    refine ⟨79558464933283590813510539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53038976622189060542340359 79558464933283590813510539)
    ·
      refine ⟨119337697399925386220265809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79558464933283590813510539 119337697399925386220265809)
      ·
        refine ⟨89503273049944039665199357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119337697399925386220265809 89503273049944039665199357)
        ·
          refine ⟨33563727393729014874449759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89503273049944039665199357 33563727393729014874449759)
          ·
            refine ⟨50345591090593522311674639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33563727393729014874449759 50345591090593522311674639)
            ·
              refine ⟨75518386635890283467511959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50345591090593522311674639 75518386635890283467511959)
              ·
                refine ⟨113277579953835425201267939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75518386635890283467511959 113277579953835425201267939)
                ·
                  refine ⟨169916369930753137801901909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 113277579953835425201267939 169916369930753137801901909)
                  ·
                    refine ⟨995603730063006666808019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 169916369930753137801901909 995603730063006666808019)
                    ·
                      rfl

theorem cell23_5816794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 1, 9].length) (baseStart_5816794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5816794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5816794 prefixEnd_5816794 := by exact prefixLift 5816794
  have htrace : WordTrace (prefixWord ++ tailWord_5816794) baseStart_5816794 baseEnd_5816794 := by
    simpa [prefixWord, tailWord_5816794, baseEnd_5816794] using wordTrace_append hprefix tailTrace_5816794
  have hstable : (prefixWord ++ tailWord_5816794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5816794).length < 2 ^ (prefixWord ++ tailWord_5816794).sum := by decide
  have hdescent : baseEnd_5816794 < baseStart_5816794 := by decide
  rcases family_descends (prefixWord ++ tailWord_5816794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5816804 : List Nat := [2, 3, 1, 1, 1, 1, 1, 1, 3, 4, 5]
def baseStart_5816804 : Nat := 118140960795 + 5816804 * 2 ^ 59
def prefixEnd_5816804 : Nat := 4983230072969 + 3 ^ 40 * 5816804 * 2
def baseEnd_5816804 : Nat := 2986816324995564961299011

theorem tailTrace_5816804 : CollatzResearch.WordTrace tailWord_5816804 prefixEnd_5816804 2986816324995564961299011 := by
  unfold tailWord_5816804
  simp only [CollatzResearch.WordTrace]
  refine ⟨106078135609360006938612733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141437514145813342584816977 106078135609360006938612733)
  ·
    refine ⟨39779300853510002601979775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106078135609360006938612733 39779300853510002601979775)
    ·
      refine ⟨59668951280265003902969663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39779300853510002601979775 59668951280265003902969663)
      ·
        refine ⟨89503426920397505854454495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59668951280265003902969663 89503426920397505854454495)
        ·
          refine ⟨134255140380596258781681743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89503426920397505854454495 134255140380596258781681743)
          ·
            refine ⟨201382710570894388172522615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134255140380596258781681743 201382710570894388172522615)
            ·
              refine ⟨302074065856341582258783923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 201382710570894388172522615 302074065856341582258783923)
              ·
                refine ⟨453111098784512373388175885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 302074065856341582258783923 453111098784512373388175885)
                ·
                  refine ⟨169916662044192140020565957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 453111098784512373388175885 169916662044192140020565957)
                  ·
                    refine ⟨31859374133286026253856117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 169916662044192140020565957 31859374133286026253856117)
                    ·
                      refine ⟨2986816324995564961299011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31859374133286026253856117 2986816324995564961299011)
                      ·
                        rfl

theorem cell23_5816804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 3, 4, 5].length) (baseStart_5816804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5816804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5816804 prefixEnd_5816804 := by exact prefixLift 5816804
  have htrace : WordTrace (prefixWord ++ tailWord_5816804) baseStart_5816804 baseEnd_5816804 := by
    simpa [prefixWord, tailWord_5816804, baseEnd_5816804] using wordTrace_append hprefix tailTrace_5816804
  have hstable : (prefixWord ++ tailWord_5816804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5816804).length < 2 ^ (prefixWord ++ tailWord_5816804).sum := by decide
  have hdescent : baseEnd_5816804 < baseStart_5816804 := by decide
  rcases family_descends (prefixWord ++ tailWord_5816804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5816808 : List Nat := [2, 1, 4, 1, 1, 4, 2, 1, 1, 3, 3]
def baseStart_5816808 : Nat := 118140960795 + 5816808 * 2 ^ 59
def prefixEnd_5816808 : Nat := 4983230072969 + 3 ^ 40 * 5816808 * 2
def baseEnd_5816808 : Nat := 2986818378918182945648993

theorem tailTrace_5816808 : CollatzResearch.WordTrace tailWord_5816808 prefixEnd_5816808 2986818378918182945648993 := by
  unfold tailWord_5816808
  simp only [CollatzResearch.WordTrace]
  refine ⟨106078208555352761280185539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141437611407137015040247385 106078208555352761280185539)
  ·
    refine ⟨159117312833029141920278309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106078208555352761280185539 159117312833029141920278309)
    ·
      refine ⟨29834496156192964110052183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 159117312833029141920278309 29834496156192964110052183)
      ·
        refine ⟨44751744234289446165078275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29834496156192964110052183 44751744234289446165078275)
        ·
          refine ⟨67127616351434169247617413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44751744234289446165078275 67127616351434169247617413)
          ·
            refine ⟨12586428065893906733928265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67127616351434169247617413 12586428065893906733928265)
            ·
              refine ⟨9439821049420430050446199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12586428065893906733928265 9439821049420430050446199)
              ·
                refine ⟨14159731574130645075669299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9439821049420430050446199 14159731574130645075669299)
                ·
                  refine ⟨21239597361195967613503949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14159731574130645075669299 21239597361195967613503949)
                  ·
                    refine ⟨7964849010448487855063981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21239597361195967613503949 7964849010448487855063981)
                    ·
                      refine ⟨2986818378918182945648993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7964849010448487855063981 2986818378918182945648993)
                      ·
                        rfl

theorem cell23_5816808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 2, 1, 1, 3, 3].length) (baseStart_5816808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5816808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5816808 prefixEnd_5816808 := by exact prefixLift 5816808
  have htrace : WordTrace (prefixWord ++ tailWord_5816808) baseStart_5816808 baseEnd_5816808 := by
    simpa [prefixWord, tailWord_5816808, baseEnd_5816808] using wordTrace_append hprefix tailTrace_5816808
  have hstable : (prefixWord ++ tailWord_5816808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5816808).length < 2 ^ (prefixWord ++ tailWord_5816808).sum := by decide
  have hdescent : baseEnd_5816808 < baseStart_5816808 := by decide
  rcases family_descends (prefixWord ++ tailWord_5816808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5816824 : List Nat := [2, 1, 2, 1, 1, 4, 1, 2, 1, 8]
def baseStart_5816824 : Nat := 118140960795 + 5816824 * 2 ^ 59
def prefixEnd_5816824 : Nat := 4983230072969 + 3 ^ 40 * 5816824 * 2
def baseEnd_5816824 : Nat := 995608864869551627682973

theorem tailTrace_5816824 : CollatzResearch.WordTrace tailWord_5816824 prefixEnd_5816824 995608864869551627682973 := by
  unfold tailWord_5816824
  simp only [CollatzResearch.WordTrace]
  refine ⟨106078500339323778646476763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141438000452431704861969017 106078500339323778646476763)
  ·
    refine ⟨159117750508985667969715145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106078500339323778646476763 159117750508985667969715145)
    ·
      refine ⟨119338312881739250977286359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159117750508985667969715145 119338312881739250977286359)
      ·
        refine ⟨179007469322608876465929539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119338312881739250977286359 179007469322608876465929539)
        ·
          refine ⟨268511203983913314698894309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179007469322608876465929539 268511203983913314698894309)
          ·
            refine ⟨50345850746983746506042683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 268511203983913314698894309 50345850746983746506042683)
            ·
              refine ⟨75518776120475619759064025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50345850746983746506042683 75518776120475619759064025)
              ·
                refine ⟨56639082090356714819298019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75518776120475619759064025 56639082090356714819298019)
                ·
                  refine ⟨84958623135535072228947029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56639082090356714819298019 84958623135535072228947029)
                  ·
                    refine ⟨995608864869551627682973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 84958623135535072228947029 995608864869551627682973)
                    ·
                      rfl

theorem cell23_5816824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 2, 1, 8].length) (baseStart_5816824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5816824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5816824 prefixEnd_5816824 := by exact prefixLift 5816824
  have htrace : WordTrace (prefixWord ++ tailWord_5816824) baseStart_5816824 baseEnd_5816824 := by
    simpa [prefixWord, tailWord_5816824, baseEnd_5816824] using wordTrace_append hprefix tailTrace_5816824
  have hstable : (prefixWord ++ tailWord_5816824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5816824).length < 2 ^ (prefixWord ++ tailWord_5816824).sum := by decide
  have hdescent : baseEnd_5816824 < baseStart_5816824 := by decide
  rcases family_descends (prefixWord ++ tailWord_5816824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5816881 : List Nat := [1, 2, 2, 3, 1, 1, 2, 2, 1, 5, 3]
def baseStart_5816881 : Nat := 118140960795 + 5816881 * 2 ^ 59
def prefixEnd_5816881 : Nat := 4983230072969 + 3 ^ 40 * 5816881 * 2
def baseEnd_5816881 : Nat := 2986855863005961160036157

theorem tailTrace_5816881 : CollatzResearch.WordTrace tailWord_5816881 prefixEnd_5816881 2986855863005961160036157 := by
  unfold tailWord_5816881
  simp only [CollatzResearch.WordTrace]
  refine ⟨212159079639441056027778497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141439386426294037351852331 212159079639441056027778497)
  ·
    refine ⟨159119309729580792020833873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212159079639441056027778497 159119309729580792020833873)
    ·
      refine ⟨119339482297185594015625405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159119309729580792020833873 119339482297185594015625405)
      ·
        refine ⟨44752305861444597755859527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119339482297185594015625405 44752305861444597755859527)
        ·
          refine ⟨67128458792166896633789291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44752305861444597755859527 67128458792166896633789291)
          ·
            refine ⟨100692688188250344950683937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67128458792166896633789291 100692688188250344950683937)
            ·
              refine ⟨75519516141187758713012953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100692688188250344950683937 75519516141187758713012953)
              ·
                refine ⟨56639637105890819034759715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75519516141187758713012953 56639637105890819034759715)
                ·
                  refine ⟨84959455658836228552139573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56639637105890819034759715 84959455658836228552139573)
                  ·
                    refine ⟨7964948968015896426763085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 84959455658836228552139573 7964948968015896426763085)
                    ·
                      refine ⟨2986855863005961160036157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7964948968015896426763085 2986855863005961160036157)
                      ·
                        rfl

theorem cell23_5816881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 2, 1, 5, 3].length) (baseStart_5816881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5816881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5816881 prefixEnd_5816881 := by exact prefixLift 5816881
  have htrace : WordTrace (prefixWord ++ tailWord_5816881) baseStart_5816881 baseEnd_5816881 := by
    simpa [prefixWord, tailWord_5816881, baseEnd_5816881] using wordTrace_append hprefix tailTrace_5816881
  have hstable : (prefixWord ++ tailWord_5816881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5816881).length < 2 ^ (prefixWord ++ tailWord_5816881).sum := by decide
  have hdescent : baseEnd_5816881 < baseStart_5816881 := by decide
  rcases family_descends (prefixWord ++ tailWord_5816881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5816901 : List Nat := [1, 3, 1, 1, 1, 5, 1, 1, 4, 5]
def baseStart_5816901 : Nat := 118140960795 + 5816901 * 2 ^ 59
def prefixEnd_5816901 : Nat := 4983230072969 + 3 ^ 40 * 5816901 * 2
def baseEnd_5816901 : Nat := 995622044206350360595355

theorem tailTrace_5816901 : CollatzResearch.WordTrace tailWord_5816901 prefixEnd_5816901 995622044206350360595355 := by
  unfold tailWord_5816901
  simp only [CollatzResearch.WordTrace]
  refine ⟨212159809099368599443506557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141439872732912399629004371 212159809099368599443506557)
  ·
    refine ⟨79559928412263224791314959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 212159809099368599443506557 79559928412263224791314959)
    ·
      refine ⟨119339892618394837186972439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79559928412263224791314959 119339892618394837186972439)
      ·
        refine ⟨179009838927592255780458659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119339892618394837186972439 179009838927592255780458659)
        ·
          refine ⟨268514758391388383670687989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179009838927592255780458659 268514758391388383670687989)
          ·
            refine ⟨25173258599192660969126999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 268514758391388383670687989 25173258599192660969126999)
            ·
              refine ⟨37759887898788991453690499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25173258599192660969126999 37759887898788991453690499)
              ·
                refine ⟨56639831848183487180535749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37759887898788991453690499 56639831848183487180535749)
                ·
                  refine ⟨10619968471534403846350453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56639831848183487180535749 10619968471534403846350453)
                  ·
                    refine ⟨995622044206350360595355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10619968471534403846350453 995622044206350360595355)
                    ·
                      rfl

theorem cell23_5816901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 1, 4, 5].length) (baseStart_5816901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5816901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5816901 prefixEnd_5816901 := by exact prefixLift 5816901
  have htrace : WordTrace (prefixWord ++ tailWord_5816901) baseStart_5816901 baseEnd_5816901 := by
    simpa [prefixWord, tailWord_5816901, baseEnd_5816901] using wordTrace_append hprefix tailTrace_5816901
  have hstable : (prefixWord ++ tailWord_5816901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5816901).length < 2 ^ (prefixWord ++ tailWord_5816901).sum := by decide
  have hdescent : baseEnd_5816901 < baseStart_5816901 := by decide
  rcases family_descends (prefixWord ++ tailWord_5816901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5816908 : List Nat := [2, 2, 1, 3, 1, 2, 2, 1, 2, 5, 2]
def baseStart_5816908 : Nat := 118140960795 + 5816908 * 2 ^ 59
def prefixEnd_5816908 : Nat := 4983230072969 + 3 ^ 40 * 5816908 * 2
def baseEnd_5816908 : Nat := 2986869726983632554398533

theorem tailTrace_5816908 : CollatzResearch.WordTrace tailWord_5816908 prefixEnd_5816908 2986869726983632554398533 := by
  unfold tailWord_5816908
  simp only [CollatzResearch.WordTrace]
  refine ⟨106080032205171619819505689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141440042940228826426007585 106080032205171619819505689)
  ·
    refine ⟨79560024153878714864629267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106080032205171619819505689 79560024153878714864629267)
    ·
      refine ⟨119340036230818072296943901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79560024153878714864629267 119340036230818072296943901)
      ·
        refine ⟨44752513586556777111353963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119340036230818072296943901 44752513586556777111353963)
        ·
          refine ⟨67128770379835165667030945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44752513586556777111353963 67128770379835165667030945)
          ·
            refine ⟨50346577784876374250273209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67128770379835165667030945 50346577784876374250273209)
            ·
              refine ⟨37759933338657280687704907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50346577784876374250273209 37759933338657280687704907)
              ·
                refine ⟨56639900007985921031557361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37759933338657280687704907 56639900007985921031557361)
                ·
                  refine ⟨42479925005989440773668021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56639900007985921031557361 42479925005989440773668021)
                  ·
                    refine ⟨3982492969311510072531377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42479925005989440773668021 3982492969311510072531377)
                    ·
                      refine ⟨2986869726983632554398533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3982492969311510072531377 2986869726983632554398533)
                      ·
                        rfl

theorem cell23_5816908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 1, 2, 5, 2].length) (baseStart_5816908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5816908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5816908 prefixEnd_5816908 := by exact prefixLift 5816908
  have htrace : WordTrace (prefixWord ++ tailWord_5816908) baseStart_5816908 baseEnd_5816908 := by
    simpa [prefixWord, tailWord_5816908, baseEnd_5816908] using wordTrace_append hprefix tailTrace_5816908
  have hstable : (prefixWord ++ tailWord_5816908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5816908).length < 2 ^ (prefixWord ++ tailWord_5816908).sum := by decide
  have hdescent : baseEnd_5816908 < baseStart_5816908 := by decide
  rcases family_descends (prefixWord ++ tailWord_5816908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5816992 : List Nat := [2, 1, 1, 4, 4, 2, 1, 1, 2, 2, 3]
def baseStart_5816992 : Nat := 118140960795 + 5816992 * 2 ^ 59
def prefixEnd_5816992 : Nat := 4983230072969 + 3 ^ 40 * 5816992 * 2
def baseEnd_5816992 : Nat := 2986912859358610225748147

theorem tailTrace_5816992 : CollatzResearch.WordTrace tailWord_5816992 prefixEnd_5816992 2986912859358610225748147 := by
  unfold tailWord_5816992
  simp only [CollatzResearch.WordTrace]
  refine ⟨106081564071019460992534615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141442085428025947990046153 106081564071019460992534615)
  ·
    refine ⟨159122346106529191488801923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106081564071019460992534615 159122346106529191488801923)
    ·
      refine ⟨238683519159793787233202885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159122346106529191488801923 238683519159793787233202885)
      ·
        refine ⟨44753159842461335106225541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 238683519159793787233202885 44753159842461335106225541)
        ·
          refine ⟨8391217470461500332417289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44753159842461335106225541 8391217470461500332417289)
          ·
            refine ⟨6293413102846125249312967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8391217470461500332417289 6293413102846125249312967)
            ·
              refine ⟨9440119654269187873969451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6293413102846125249312967 9440119654269187873969451)
              ·
                refine ⟨14160179481403781810954177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9440119654269187873969451 14160179481403781810954177)
                ·
                  refine ⟨10620134611052836358215633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14160179481403781810954177 10620134611052836358215633)
                  ·
                    refine ⟨7965100958289627268661725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10620134611052836358215633 7965100958289627268661725)
                    ·
                      refine ⟨2986912859358610225748147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7965100958289627268661725 2986912859358610225748147)
                      ·
                        rfl

theorem cell23_5816992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 1, 1, 2, 2, 3].length) (baseStart_5816992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5816992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5816992 prefixEnd_5816992 := by exact prefixLift 5816992
  have htrace : WordTrace (prefixWord ++ tailWord_5816992) baseStart_5816992 baseEnd_5816992 := by
    simpa [prefixWord, tailWord_5816992, baseEnd_5816992] using wordTrace_append hprefix tailTrace_5816992
  have hstable : (prefixWord ++ tailWord_5816992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5816992).length < 2 ^ (prefixWord ++ tailWord_5816992).sum := by decide
  have hdescent : baseEnd_5816992 < baseStart_5816992 := by decide
  rcases family_descends (prefixWord ++ tailWord_5816992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5817022 : List Nat := [4, 2, 1, 1, 2, 1, 4, 1, 3, 1, 3]
def baseStart_5817022 : Nat := 118140960795 + 5817022 * 2 ^ 59
def prefixEnd_5817022 : Nat := 4983230072969 + 3 ^ 40 * 5817022 * 2
def baseEnd_5817022 : Nat := 2986928263778245108373009

theorem tailTrace_5817022 : CollatzResearch.WordTrace tailWord_5817022 prefixEnd_5817022 2986928263778245108373009 := by
  unfold tailWord_5817022
  simp only [CollatzResearch.WordTrace]
  refine ⟨26520527791491279638582665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 141442814887953491405774213 26520527791491279638582665)
  ·
    refine ⟨19890395843618459728936999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26520527791491279638582665 19890395843618459728936999)
    ·
      refine ⟨29835593765427689593405499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19890395843618459728936999 29835593765427689593405499)
      ·
        refine ⟨44753390648141534390108249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29835593765427689593405499 44753390648141534390108249)
        ·
          refine ⟨33565042986106150792581187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44753390648141534390108249 33565042986106150792581187)
          ·
            refine ⟨50347564479159226188871781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33565042986106150792581187 50347564479159226188871781)
            ·
              refine ⟨9440168339842354910413459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50347564479159226188871781 9440168339842354910413459)
              ·
                refine ⟨14160252509763532365620189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9440168339842354910413459 14160252509763532365620189)
                ·
                  refine ⟨5310094691161324637107571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14160252509763532365620189 5310094691161324637107571)
                  ·
                    refine ⟨7965142036741986955661357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5310094691161324637107571 7965142036741986955661357)
                    ·
                      refine ⟨2986928263778245108373009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7965142036741986955661357 2986928263778245108373009)
                      ·
                        rfl

theorem cell23_5817022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 4, 1, 3, 1, 3].length) (baseStart_5817022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5817022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5817022 prefixEnd_5817022 := by exact prefixLift 5817022
  have htrace : WordTrace (prefixWord ++ tailWord_5817022) baseStart_5817022 baseEnd_5817022 := by
    simpa [prefixWord, tailWord_5817022, baseEnd_5817022] using wordTrace_append hprefix tailTrace_5817022
  have hstable : (prefixWord ++ tailWord_5817022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5817022).length < 2 ^ (prefixWord ++ tailWord_5817022).sum := by decide
  have hdescent : baseEnd_5817022 < baseStart_5817022 := by decide
  rcases family_descends (prefixWord ++ tailWord_5817022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5817042 : List Nat := [3, 2, 2, 2, 3, 1, 2, 2, 1, 5]
def baseStart_5817042 : Nat := 118140960795 + 5817042 * 2 ^ 59
def prefixEnd_5817042 : Nat := 4983230072969 + 3 ^ 40 * 5817042 * 2
def baseEnd_5817042 : Nat := 995646177797111676707639

theorem tailTrace_5817042 : CollatzResearch.WordTrace tailWord_5817042 prefixEnd_5817042 995646177797111676707639 := by
  unfold tailWord_5817042
  simp only [CollatzResearch.WordTrace]
  refine ⟨53041237947964445131097345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141443301194571853682926253 53041237947964445131097345)
  ·
    refine ⟨39780928460973333848323009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53041237947964445131097345 39780928460973333848323009)
    ·
      refine ⟨29835696345730000386242257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39780928460973333848323009 29835696345730000386242257)
      ·
        refine ⟨22376772259297500289681693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29835696345730000386242257 22376772259297500289681693)
        ·
          refine ⟨8391289597236562608630635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22376772259297500289681693 8391289597236562608630635)
          ·
            refine ⟨12586934395854843912945953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8391289597236562608630635 12586934395854843912945953)
            ·
              refine ⟨9440200796891132934709465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12586934395854843912945953 9440200796891132934709465)
              ·
                refine ⟨7080150597668349701032099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9440200796891132934709465 7080150597668349701032099)
                ·
                  refine ⟨10620225896502524551548149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7080150597668349701032099 10620225896502524551548149)
                  ·
                    refine ⟨995646177797111676707639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10620225896502524551548149 995646177797111676707639)
                    ·
                      rfl

theorem cell23_5817042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 2, 2, 1, 5].length) (baseStart_5817042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5817042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5817042 prefixEnd_5817042 := by exact prefixLift 5817042
  have htrace : WordTrace (prefixWord ++ tailWord_5817042) baseStart_5817042 baseEnd_5817042 := by
    simpa [prefixWord, tailWord_5817042, baseEnd_5817042] using wordTrace_append hprefix tailTrace_5817042
  have hstable : (prefixWord ++ tailWord_5817042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5817042).length < 2 ^ (prefixWord ++ tailWord_5817042).sum := by decide
  have hdescent : baseEnd_5817042 < baseStart_5817042 := by decide
  rcases family_descends (prefixWord ++ tailWord_5817042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5817065 : List Nat := [1, 2, 1, 1, 1, 2, 6, 3, 1, 2, 3]
def baseStart_5817065 : Nat := 118140960795 + 5817065 * 2 ^ 59
def prefixEnd_5817065 : Nat := 4983230072969 + 3 ^ 40 * 5817065 * 2
def baseEnd_5817065 : Nat := 2986950343446388440135311

theorem tailTrace_5817065 : CollatzResearch.WordTrace tailWord_5817065 prefixEnd_5817065 2986950343446388440135311 := by
  unfold tailWord_5817065
  simp only [CollatzResearch.WordTrace]
  refine ⟨212165790670774455452476649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141443860447182970301651099 212165790670774455452476649)
  ·
    refine ⟨159124343003080841589357487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212165790670774455452476649 159124343003080841589357487)
    ·
      refine ⟨238686514504621262384036231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159124343003080841589357487 238686514504621262384036231)
      ·
        refine ⟨358029771756931893576054347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238686514504621262384036231 358029771756931893576054347)
        ·
          refine ⟨537044657635397840364081521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 358029771756931893576054347 537044657635397840364081521)
          ·
            refine ⟨402783493226548380273061141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 537044657635397840364081521 402783493226548380273061141)
            ·
              refine ⟨18880476244994455325299741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 402783493226548380273061141 18880476244994455325299741)
              ·
                refine ⟨7080178591872920746987403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18880476244994455325299741 7080178591872920746987403)
                ·
                  refine ⟨10620267887809381120481105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7080178591872920746987403 10620267887809381120481105)
                  ·
                    refine ⟨7965200915857035840360829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10620267887809381120481105 7965200915857035840360829)
                    ·
                      refine ⟨2986950343446388440135311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7965200915857035840360829 2986950343446388440135311)
                      ·
                        rfl

theorem cell23_5817065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 3, 1, 2, 3].length) (baseStart_5817065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5817065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5817065 prefixEnd_5817065 := by exact prefixLift 5817065
  have htrace : WordTrace (prefixWord ++ tailWord_5817065) baseStart_5817065 baseEnd_5817065 := by
    simpa [prefixWord, tailWord_5817065, baseEnd_5817065] using wordTrace_append hprefix tailTrace_5817065
  have hstable : (prefixWord ++ tailWord_5817065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5817065).length < 2 ^ (prefixWord ++ tailWord_5817065).sum := by decide
  have hdescent : baseEnd_5817065 < baseStart_5817065 := by decide
  rcases family_descends (prefixWord ++ tailWord_5817065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5817186 : List Nat := [3, 3, 2, 1, 3, 1, 1, 1, 4, 2, 2]
def baseStart_5817186 : Nat := 118140960795 + 5817186 * 2 ^ 59
def prefixEnd_5817186 : Nat := 4983230072969 + 3 ^ 40 * 5817186 * 2
def baseEnd_5817186 : Nat := 2987012474605582466722255

theorem tailTrace_5817186 : CollatzResearch.WordTrace tailWord_5817186 prefixEnd_5817186 2987012474605582466722255 := by
  unfold tailWord_5817186
  simp only [CollatzResearch.WordTrace]
  refine ⟨53042550975834023279407853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141446802602224062078420941 53042550975834023279407853)
  ·
    refine ⟨19890956615937758729777945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53042550975834023279407853 19890956615937758729777945)
    ·
      refine ⟨14918217461953319047333459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19890956615937758729777945 14918217461953319047333459)
      ·
        refine ⟨22377326192929978571000189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14918217461953319047333459 22377326192929978571000189)
        ·
          refine ⟨8391497322348741964125071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22377326192929978571000189 8391497322348741964125071)
          ·
            refine ⟨12587245983523112946187607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8391497322348741964125071 12587245983523112946187607)
            ·
              refine ⟨18880868975284669419281411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12587245983523112946187607 18880868975284669419281411)
              ·
                refine ⟨28321303462927004128922117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18880868975284669419281411 28321303462927004128922117)
                ·
                  refine ⟨5310244399298813274172897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28321303462927004128922117 5310244399298813274172897)
                  ·
                    refine ⟨3982683299474109955629673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5310244399298813274172897 3982683299474109955629673)
                    ·
                      refine ⟨2987012474605582466722255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3982683299474109955629673 2987012474605582466722255)
                      ·
                        rfl

theorem cell23_5817186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 1, 4, 2, 2].length) (baseStart_5817186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5817186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5817186 prefixEnd_5817186 := by exact prefixLift 5817186
  have htrace : WordTrace (prefixWord ++ tailWord_5817186) baseStart_5817186 baseEnd_5817186 := by
    simpa [prefixWord, tailWord_5817186, baseEnd_5817186] using wordTrace_append hprefix tailTrace_5817186
  have hstable : (prefixWord ++ tailWord_5817186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5817186).length < 2 ^ (prefixWord ++ tailWord_5817186).sum := by decide
  have hdescent : baseEnd_5817186 < baseStart_5817186 := by decide
  rcases family_descends (prefixWord ++ tailWord_5817186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5817192 : List Nat := [2, 1, 4, 2, 1, 2, 2, 4, 5]
def baseStart_5817192 : Nat := 118140960795 + 5817192 * 2 ^ 59
def prefixEnd_5817192 : Nat := 4983230072969 + 3 ^ 40 * 5817192 * 2
def baseEnd_5817192 : Nat := 331890617276612160360803

theorem tailTrace_5817192 : CollatzResearch.WordTrace tailWord_5817192 prefixEnd_5817192 331890617276612160360803 := by
  unfold tailWord_5817192
  simp only [CollatzResearch.WordTrace]
  refine ⟨106085211370657178071174915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141446948494209570761566553 106085211370657178071174915)
  ·
    refine ⟨159127817055985767106762373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106085211370657178071174915 159127817055985767106762373)
    ·
      refine ⟨29836465697997331332517945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 159127817055985767106762373 29836465697997331332517945)
      ·
        refine ⟨22377349273497998499388459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29836465697997331332517945 22377349273497998499388459)
        ·
          refine ⟨33566023910246997749082689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22377349273497998499388459 33566023910246997749082689)
          ·
            refine ⟨25174517932685248311812017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33566023910246997749082689 25174517932685248311812017)
            ·
              refine ⟨18880888449513936233859013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25174517932685248311812017 18880888449513936233859013)
              ·
                refine ⟨3540166584283863043848565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18880888449513936233859013 3540166584283863043848565)
                ·
                  refine ⟨331890617276612160360803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3540166584283863043848565 331890617276612160360803)
                  ·
                    rfl

theorem cell23_5817192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 4, 5].length) (baseStart_5817192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5817192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5817192 prefixEnd_5817192 := by exact prefixLift 5817192
  have htrace : WordTrace (prefixWord ++ tailWord_5817192) baseStart_5817192 baseEnd_5817192 := by
    simpa [prefixWord, tailWord_5817192, baseEnd_5817192] using wordTrace_append hprefix tailTrace_5817192
  have hstable : (prefixWord ++ tailWord_5817192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5817192).length < 2 ^ (prefixWord ++ tailWord_5817192).sum := by decide
  have hdescent : baseEnd_5817192 < baseStart_5817192 := by decide
  rcases family_descends (prefixWord ++ tailWord_5817192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5817195 : List Nat := [1, 1, 1, 1, 2, 2, 4, 1, 1, 7, 2]
def baseStart_5817195 : Nat := 118140960795 + 5817195 * 2 ^ 59
def prefixEnd_5817195 : Nat := 4983230072969 + 3 ^ 40 * 5817195 * 2
def baseEnd_5817195 : Nat := 2987017095931472931509713

theorem tailTrace_5817195 : CollatzResearch.WordTrace tailWord_5817195 prefixEnd_5817195 2987017095931472931509713 := by
  unfold tailWord_5817195
  simp only [CollatzResearch.WordTrace]
  refine ⟨212170532160303487654709039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141447021440202325103139359 212170532160303487654709039)
  ·
    refine ⟨318255798240455231482063559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212170532160303487654709039 318255798240455231482063559)
    ·
      refine ⟨477383697360682847223095339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 318255798240455231482063559 477383697360682847223095339)
      ·
        refine ⟨716075546041024270834643009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 477383697360682847223095339 716075546041024270834643009)
        ·
          refine ⟨537056659530768203125982257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 716075546041024270834643009 537056659530768203125982257)
          ·
            refine ⟨402792494648076152344486693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 537056659530768203125982257 402792494648076152344486693)
            ·
              refine ⟨75523592746514278564591255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 402792494648076152344486693 75523592746514278564591255)
              ·
                refine ⟨113285389119771417846886883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75523592746514278564591255 113285389119771417846886883)
                ·
                  refine ⟨169928083679657126770330325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 113285389119771417846886883 169928083679657126770330325)
                  ·
                    refine ⟨3982689461241963908679617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 169928083679657126770330325 3982689461241963908679617)
                    ·
                      refine ⟨2987017095931472931509713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3982689461241963908679617 2987017095931472931509713)
                      ·
                        rfl

theorem cell23_5817195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 1, 1, 7, 2].length) (baseStart_5817195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5817195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5817195 prefixEnd_5817195 := by exact prefixLift 5817195
  have htrace : WordTrace (prefixWord ++ tailWord_5817195) baseStart_5817195 baseEnd_5817195 := by
    simpa [prefixWord, tailWord_5817195, baseEnd_5817195] using wordTrace_append hprefix tailTrace_5817195
  have hstable : (prefixWord ++ tailWord_5817195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5817195).length < 2 ^ (prefixWord ++ tailWord_5817195).sum := by decide
  have hdescent : baseEnd_5817195 < baseStart_5817195 := by decide
  rcases family_descends (prefixWord ++ tailWord_5817195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5817205 : List Nat := [1, 3, 4, 1, 1, 2, 1, 2, 1, 7]
def baseStart_5817205 : Nat := 118140960795 + 5817205 * 2 ^ 59
def prefixEnd_5817205 : Nat := 4983230072969 + 3 ^ 40 * 5817205 * 2
def baseEnd_5817205 : Nat := 995674076912672630794889

theorem tailTrace_5817205 : CollatzResearch.WordTrace tailWord_5817205 prefixEnd_5817205 995674076912672630794889 := by
  unfold tailWord_5817205
  simp only [CollatzResearch.WordTrace]
  refine ⟨212170896890267259362573069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141447264593511506241715379 212170896890267259362573069)
  ·
    refine ⟨79564086333850222260964901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 212170896890267259362573069 79564086333850222260964901)
    ·
      refine ⟨14918266187596916673930919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79564086333850222260964901 14918266187596916673930919)
      ·
        refine ⟨22377399281395375010896379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14918266187596916673930919 22377399281395375010896379)
        ·
          refine ⟨33566098922093062516344569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22377399281395375010896379 33566098922093062516344569)
          ·
            refine ⟨25174574191569796887258427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33566098922093062516344569 25174574191569796887258427)
            ·
              refine ⟨37761861287354695330887641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25174574191569796887258427 37761861287354695330887641)
              ·
                refine ⟨28321395965516021498165731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37761861287354695330887641 28321395965516021498165731)
                ·
                  refine ⟨42482093948274032247248597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28321395965516021498165731 42482093948274032247248597)
                  ·
                    refine ⟨995674076912672630794889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42482093948274032247248597 995674076912672630794889)
                    ·
                      rfl

theorem cell23_5817205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 2, 1, 7].length) (baseStart_5817205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5817205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5817205 prefixEnd_5817205 := by exact prefixLift 5817205
  have htrace : WordTrace (prefixWord ++ tailWord_5817205) baseStart_5817205 baseEnd_5817205 := by
    simpa [prefixWord, tailWord_5817205, baseEnd_5817205] using wordTrace_append hprefix tailTrace_5817205
  have hstable : (prefixWord ++ tailWord_5817205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5817205).length < 2 ^ (prefixWord ++ tailWord_5817205).sum := by decide
  have hdescent : baseEnd_5817205 < baseStart_5817205 := by decide
  rcases family_descends (prefixWord ++ tailWord_5817205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5817225 : List Nat := [1, 2, 1, 1, 5, 2, 2, 1, 1, 3, 4]
def baseStart_5817225 : Nat := 118140960795 + 5817225 * 2 ^ 59
def prefixEnd_5817225 : Nat := 4983230072969 + 3 ^ 40 * 5817225 * 2
def baseEnd_5817225 : Nat := 2987032500351107814134575

theorem tailTrace_5817225 : CollatzResearch.WordTrace tailWord_5817225 prefixEnd_5817225 2987032500351107814134575 := by
  unfold tailWord_5817225
  simp only [CollatzResearch.WordTrace]
  refine ⟨212171626350194802778301129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141447750900129868518867419 212171626350194802778301129)
  ·
    refine ⟨159128719762646102083725847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212171626350194802778301129 159128719762646102083725847)
    ·
      refine ⟨238693079643969153125588771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159128719762646102083725847 238693079643969153125588771)
      ·
        refine ⟨358039619465953729688383157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238693079643969153125588771 358039619465953729688383157)
        ·
          refine ⟨33566214324933162158285921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 358039619465953729688383157 33566214324933162158285921)
          ·
            refine ⟨25174660743699871618714441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33566214324933162158285921 25174660743699871618714441)
            ·
              refine ⟨18880995557774903714035831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25174660743699871618714441 18880995557774903714035831)
              ·
                refine ⟨28321493336662355571053747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18880995557774903714035831 28321493336662355571053747)
                ·
                  refine ⟨42482240004993533356580621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28321493336662355571053747 42482240004993533356580621)
                  ·
                    refine ⟨15930840001872575008717733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42482240004993533356580621 15930840001872575008717733)
                    ·
                      refine ⟨2987032500351107814134575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15930840001872575008717733 2987032500351107814134575)
                      ·
                        rfl

theorem cell23_5817225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 1, 1, 3, 4].length) (baseStart_5817225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5817225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5817225 prefixEnd_5817225 := by exact prefixLift 5817225
  have htrace : WordTrace (prefixWord ++ tailWord_5817225) baseStart_5817225 baseEnd_5817225 := by
    simpa [prefixWord, tailWord_5817225, baseEnd_5817225] using wordTrace_append hprefix tailTrace_5817225
  have hstable : (prefixWord ++ tailWord_5817225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5817225).length < 2 ^ (prefixWord ++ tailWord_5817225).sum := by decide
  have hdescent : baseEnd_5817225 < baseStart_5817225 := by decide
  rcases family_descends (prefixWord ++ tailWord_5817225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5817326 : List Nat := [4, 1, 2, 1, 4, 1, 1, 2, 3, 1, 3]
def baseStart_5817326 : Nat := 118140960795 + 5817326 * 2 ^ 59
def prefixEnd_5817326 : Nat := 4983230072969 + 3 ^ 40 * 5817326 * 2
def baseEnd_5817326 : Nat := 2987084361897211918971611

theorem tailTrace_5817326 : CollatzResearch.WordTrace tailWord_5817326 prefixEnd_5817326 2987084361897211918971611 := by
  unfold tailWord_5817326
  simp only [CollatzResearch.WordTrace]
  refine ⟨26521913765353612128465979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 141450206748552598018485221 26521913765353612128465979)
  ·
    refine ⟨39782870648030418192698969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26521913765353612128465979 39782870648030418192698969)
    ·
      refine ⟨29837152986022813644524227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39782870648030418192698969 29837152986022813644524227)
      ·
        refine ⟨44755729479034220466786341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29837152986022813644524227 44755729479034220466786341)
        ·
          refine ⟨8391699277318916337522439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44755729479034220466786341 8391699277318916337522439)
          ·
            refine ⟨12587548915978374506283659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8391699277318916337522439 12587548915978374506283659)
            ·
              refine ⟨18881323373967561759425489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12587548915978374506283659 18881323373967561759425489)
              ·
                refine ⟨14160992530475671319569117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18881323373967561759425489 14160992530475671319569117)
                ·
                  refine ⟨5310372198928376744838419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14160992530475671319569117 5310372198928376744838419)
                  ·
                    refine ⟨7965558298392565117257629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5310372198928376744838419 7965558298392565117257629)
                    ·
                      refine ⟨2987084361897211918971611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7965558298392565117257629 2987084361897211918971611)
                      ·
                        rfl

theorem cell23_5817326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 2, 3, 1, 3].length) (baseStart_5817326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5817326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5817326 prefixEnd_5817326 := by exact prefixLift 5817326
  have htrace : WordTrace (prefixWord ++ tailWord_5817326) baseStart_5817326 baseEnd_5817326 := by
    simpa [prefixWord, tailWord_5817326, baseEnd_5817326] using wordTrace_append hprefix tailTrace_5817326
  have hstable : (prefixWord ++ tailWord_5817326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5817326).length < 2 ^ (prefixWord ++ tailWord_5817326).sum := by decide
  have hdescent : baseEnd_5817326 < baseStart_5817326 := by decide
  rcases family_descends (prefixWord ++ tailWord_5817326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5817349 : List Nat := [1, 3, 1, 1, 2, 3, 1, 2, 5, 2, 2]
def baseStart_5817349 : Nat := 118140960795 + 5817349 * 2 ^ 59
def prefixEnd_5817349 : Nat := 4983230072969 + 3 ^ 40 * 5817349 * 2
def baseEnd_5817349 : Nat := 2987096171952265328984005

theorem tailTrace_5817349 : CollatzResearch.WordTrace tailWord_5817349 prefixEnd_5817349 2987096171952265328984005 := by
  unfold tailWord_5817349
  simp only [CollatzResearch.WordTrace]
  refine ⟨212176149001745571955815101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141450766001163714637210067 212176149001745571955815101)
  ·
    refine ⟨79566055875654589483430663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 212176149001745571955815101 79566055875654589483430663)
    ·
      refine ⟨119349083813481884225145995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79566055875654589483430663 119349083813481884225145995)
      ·
        refine ⟨179023625720222826337718993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119349083813481884225145995 179023625720222826337718993)
        ·
          refine ⟨134267719290167119753289245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179023625720222826337718993 134267719290167119753289245)
          ·
            refine ⟨50350394733812669907483467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 134267719290167119753289245 50350394733812669907483467)
            ·
              refine ⟨75525592100719004861225201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50350394733812669907483467 75525592100719004861225201)
              ·
                refine ⟨56644194075539253645918901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75525592100719004861225201 56644194075539253645918901)
                ·
                  refine ⟨5310393194581805029304897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 56644194075539253645918901 5310393194581805029304897)
                  ·
                    refine ⟨3982794895936353771978673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5310393194581805029304897 3982794895936353771978673)
                    ·
                      refine ⟨2987096171952265328984005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3982794895936353771978673 2987096171952265328984005)
                      ·
                        rfl

theorem cell23_5817349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 2, 5, 2, 2].length) (baseStart_5817349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5817349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5817349 prefixEnd_5817349 := by exact prefixLift 5817349
  have htrace : WordTrace (prefixWord ++ tailWord_5817349) baseStart_5817349 baseEnd_5817349 := by
    simpa [prefixWord, tailWord_5817349, baseEnd_5817349] using wordTrace_append hprefix tailTrace_5817349
  have hstable : (prefixWord ++ tailWord_5817349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5817349).length < 2 ^ (prefixWord ++ tailWord_5817349).sum := by decide
  have hdescent : baseEnd_5817349 < baseStart_5817349 := by decide
  rcases family_descends (prefixWord ++ tailWord_5817349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5817355 : List Nat := [1, 1, 1, 1, 6, 3, 10]
def baseStart_5817355 : Nat := 118140960795 + 5817355 * 2 ^ 59
def prefixEnd_5817355 : Nat := 4983230072969 + 3 ^ 40 * 5817355 * 2
def baseEnd_5817355 : Nat := 36877768553533238339617

theorem tailTrace_5817355 : CollatzResearch.WordTrace tailWord_5817355 prefixEnd_5817355 36877768553533238339617 := by
  unfold tailWord_5817355
  simp only [CollatzResearch.WordTrace]
  refine ⟨212176367839723834980533519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141450911893149223320355679 212176367839723834980533519)
  ·
    refine ⟨318264551759585752470800279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212176367839723834980533519 318264551759585752470800279)
    ·
      refine ⟨477396827639378628706200419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 318264551759585752470800279 477396827639378628706200419)
      ·
        refine ⟨716095241459067943059300629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 477396827639378628706200419 716095241459067943059300629)
        ·
          refine ⟨33566964443393809830904717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 716095241459067943059300629 33566964443393809830904717)
          ·
            refine ⟨12587611666272678686589269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33566964443393809830904717 12587611666272678686589269)
            ·
              refine ⟨36877768553533238339617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 12587611666272678686589269 36877768553533238339617)
              ·
                rfl

theorem cell23_5817355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 10].length) (baseStart_5817355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5817355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5817355 prefixEnd_5817355 := by exact prefixLift 5817355
  have htrace : WordTrace (prefixWord ++ tailWord_5817355) baseStart_5817355 baseEnd_5817355 := by
    simpa [prefixWord, tailWord_5817355, baseEnd_5817355] using wordTrace_append hprefix tailTrace_5817355
  have hstable : (prefixWord ++ tailWord_5817355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5817355).length < 2 ^ (prefixWord ++ tailWord_5817355).sum := by decide
  have hdescent : baseEnd_5817355 < baseStart_5817355 := by decide
  rcases family_descends (prefixWord ++ tailWord_5817355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5817376 : List Nat := [2, 1, 1, 7, 1, 2, 1, 1, 1, 6]
def baseStart_5817376 : Nat := 118140960795 + 5817376 * 2 ^ 59
def prefixEnd_5817376 : Nat := 4983230072969 + 3 ^ 40 * 5817376 * 2
def baseEnd_5817376 : Nat := 995703345309978907782127

theorem tailTrace_5817376 : CollatzResearch.WordTrace tailWord_5817376 prefixEnd_5817376 995703345309978907782127 := by
  unfold tailWord_5817376
  simp only [CollatzResearch.WordTrace]
  refine ⟨106088566886323877783523991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141451422515098503711365321 106088566886323877783523991)
  ·
    refine ⟨159132850329485816675285987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106088566886323877783523991 159132850329485816675285987)
    ·
      refine ⟨238699275494228725012928981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159132850329485816675285987 238699275494228725012928981)
      ·
        refine ⟨5594514269395985742490523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 238699275494228725012928981 5594514269395985742490523)
        ·
          refine ⟨8391771404093978613735785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5594514269395985742490523 8391771404093978613735785)
          ·
            refine ⟨6293828553070483960301839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8391771404093978613735785 6293828553070483960301839)
            ·
              refine ⟨9440742829605725940452759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6293828553070483960301839 9440742829605725940452759)
              ·
                refine ⟨14161114244408588910679139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9440742829605725940452759 14161114244408588910679139)
                ·
                  refine ⟨21241671366612883366018709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14161114244408588910679139 21241671366612883366018709)
                  ·
                    refine ⟨995703345309978907782127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21241671366612883366018709 995703345309978907782127)
                    ·
                      rfl

theorem cell23_5817376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 1, 1, 1, 6].length) (baseStart_5817376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5817376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5817376 prefixEnd_5817376 := by exact prefixLift 5817376
  have htrace : WordTrace (prefixWord ++ tailWord_5817376) baseStart_5817376 baseEnd_5817376 := by
    simpa [prefixWord, tailWord_5817376, baseEnd_5817376] using wordTrace_append hprefix tailTrace_5817376
  have hstable : (prefixWord ++ tailWord_5817376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5817376).length < 2 ^ (prefixWord ++ tailWord_5817376).sum := by decide
  have hdescent : baseEnd_5817376 < baseStart_5817376 := by decide
  rcases family_descends (prefixWord ++ tailWord_5817376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5817379 : List Nat := [1, 1, 1, 4, 3, 4, 1, 1, 1, 2, 4]
def baseStart_5817379 : Nat := 118140960795 + 5817379 * 2 ^ 59
def prefixEnd_5817379 : Nat := 4983230072969 + 3 ^ 40 * 5817379 * 2
def baseEnd_5817379 : Nat := 2987111576371900211608867

theorem tailTrace_5817379 : CollatzResearch.WordTrace tailWord_5817379 prefixEnd_5817379 2987111576371900211608867 := by
  unfold tailWord_5817379
  simp only [CollatzResearch.WordTrace]
  refine ⟨212177243191636887079407191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141451495461091258052938127 212177243191636887079407191)
  ·
    refine ⟨318265864787455330619110787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212177243191636887079407191 318265864787455330619110787)
    ·
      refine ⟨477398797181182995928666181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 318265864787455330619110787 477398797181182995928666181)
      ·
        refine ⟨89512274471471811736624909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 477398797181182995928666181 89512274471471811736624909)
        ·
          refine ⟨33567102926801929401234341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89512274471471811736624909 33567102926801929401234341)
          ·
            refine ⟨6293831798775361762731439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33567102926801929401234341 6293831798775361762731439)
            ·
              refine ⟨9440747698163042644097159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6293831798775361762731439 9440747698163042644097159)
              ·
                refine ⟨14161121547244563966145739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9440747698163042644097159 14161121547244563966145739)
                ·
                  refine ⟨21241682320866845949218609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14161121547244563966145739 21241682320866845949218609)
                  ·
                    refine ⟨15931261740650134461913957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21241682320866845949218609 15931261740650134461913957)
                    ·
                      refine ⟨2987111576371900211608867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15931261740650134461913957 2987111576371900211608867)
                      ·
                        rfl

theorem cell23_5817379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 1, 1, 1, 2, 4].length) (baseStart_5817379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5817379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5817379 prefixEnd_5817379 := by exact prefixLift 5817379
  have htrace : WordTrace (prefixWord ++ tailWord_5817379) baseStart_5817379 baseEnd_5817379 := by
    simpa [prefixWord, tailWord_5817379, baseEnd_5817379] using wordTrace_append hprefix tailTrace_5817379
  have hstable : (prefixWord ++ tailWord_5817379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5817379).length < 2 ^ (prefixWord ++ tailWord_5817379).sum := by decide
  have hdescent : baseEnd_5817379 < baseStart_5817379 := by decide
  rcases family_descends (prefixWord ++ tailWord_5817379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5817383 : List Nat := [1, 1, 7, 1, 1, 1, 2, 2, 3, 2, 2]
def baseStart_5817383 : Nat := 118140960795 + 5817383 * 2 ^ 59
def prefixEnd_5817383 : Nat := 4983230072969 + 3 ^ 40 * 5817383 * 2
def baseEnd_5817383 : Nat := 2987113630294518195958849

theorem tailTrace_5817383 : CollatzResearch.WordTrace tailWord_5817383 prefixEnd_5817383 2987113630294518195958849 := by
  unfold tailWord_5817383
  simp only [CollatzResearch.WordTrace]
  refine ⟨212177389083622395762552803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141451592722414930508368535 212177389083622395762552803)
  ·
    refine ⟨318266083625433593643829205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212177389083622395762552803 318266083625433593643829205)
    ·
      refine ⟨7459361334971099851027247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 318266083625433593643829205 7459361334971099851027247)
      ·
        refine ⟨11189042002456649776540871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7459361334971099851027247 11189042002456649776540871)
        ·
          refine ⟨16783563003684974664811307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11189042002456649776540871 16783563003684974664811307)
          ·
            refine ⟨25175344505527461997216961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16783563003684974664811307 25175344505527461997216961)
            ·
              refine ⟨18881508379145596497912721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25175344505527461997216961 18881508379145596497912721)
              ·
                refine ⟨14161131284359197373434541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18881508379145596497912721 14161131284359197373434541)
                ·
                  refine ⟨5310424231634699015037953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14161131284359197373434541 5310424231634699015037953)
                  ·
                    refine ⟨3982818173726024261278465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5310424231634699015037953 3982818173726024261278465)
                    ·
                      refine ⟨2987113630294518195958849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3982818173726024261278465 2987113630294518195958849)
                      ·
                        rfl

theorem cell23_5817383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 2, 3, 2, 2].length) (baseStart_5817383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5817383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5817383 prefixEnd_5817383 := by exact prefixLift 5817383
  have htrace : WordTrace (prefixWord ++ tailWord_5817383) baseStart_5817383 baseEnd_5817383 := by
    simpa [prefixWord, tailWord_5817383, baseEnd_5817383] using wordTrace_append hprefix tailTrace_5817383
  have hstable : (prefixWord ++ tailWord_5817383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5817383).length < 2 ^ (prefixWord ++ tailWord_5817383).sum := by decide
  have hdescent : baseEnd_5817383 < baseStart_5817383 := by decide
  rcases family_descends (prefixWord ++ tailWord_5817383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5817400 : List Nat := [2, 1, 2, 1, 5, 3, 1, 3, 1, 2, 2]
def baseStart_5817400 : Nat := 118140960795 + 5817400 * 2 ^ 59
def prefixEnd_5817400 : Nat := 4983230072969 + 3 ^ 40 * 5817400 * 2
def baseEnd_5817400 : Nat := 2987122359465644629446271

theorem tailTrace_5817400 : CollatzResearch.WordTrace tailWord_5817400 prefixEnd_5817400 2987122359465644629446271 := by
  unfold tailWord_5817400
  simp only [CollatzResearch.WordTrace]
  refine ⟨106089004562280403832960827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141452006083040538443947769 106089004562280403832960827)
  ·
    refine ⟨159133506843420605749441241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106089004562280403832960827 159133506843420605749441241)
    ·
      refine ⟨119350130132565454312080931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159133506843420605749441241 119350130132565454312080931)
      ·
        refine ⟨179025195198848181468121397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119350130132565454312080931 179025195198848181468121397)
        ·
          refine ⟨16783612049892017012636381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 179025195198848181468121397 16783612049892017012636381)
          ·
            refine ⟨6293854518709506379738643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16783612049892017012636381 6293854518709506379738643)
            ·
              refine ⟨9440781778064259569607965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6293854518709506379738643 9440781778064259569607965)
              ·
                refine ⟨3540293166774097338602987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9440781778064259569607965 3540293166774097338602987)
                ·
                  refine ⟨5310439750161146007904481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3540293166774097338602987 5310439750161146007904481)
                  ·
                    refine ⟨3982829812620859505928361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5310439750161146007904481 3982829812620859505928361)
                    ·
                      refine ⟨2987122359465644629446271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3982829812620859505928361 2987122359465644629446271)
                      ·
                        rfl

theorem cell23_5817400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 1, 3, 1, 2, 2].length) (baseStart_5817400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5817400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5817400 prefixEnd_5817400 := by exact prefixLift 5817400
  have htrace : WordTrace (prefixWord ++ tailWord_5817400) baseStart_5817400 baseEnd_5817400 := by
    simpa [prefixWord, tailWord_5817400, baseEnd_5817400] using wordTrace_append hprefix tailTrace_5817400
  have hstable : (prefixWord ++ tailWord_5817400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5817400).length < 2 ^ (prefixWord ++ tailWord_5817400).sum := by decide
  have hdescent : baseEnd_5817400 < baseStart_5817400 := by decide
  rcases family_descends (prefixWord ++ tailWord_5817400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5817422 : List Nat := [4, 1, 1, 1, 1, 3, 2, 1, 2, 3, 4]
def baseStart_5817422 : Nat := 118140960795 + 5817422 * 2 ^ 59
def prefixEnd_5817422 : Nat := 4983230072969 + 3 ^ 40 * 5817422 * 2
def baseEnd_5817422 : Nat := 2987133656040043543371169

theorem tailTrace_5817422 : CollatzResearch.WordTrace tailWord_5817422 prefixEnd_5817422 2987133656040043543371169 := by
  unfold tailWord_5817422
  simp only [CollatzResearch.WordTrace]
  refine ⟨26522351441310138177902815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 141452541020320736948815013 26522351441310138177902815)
  ·
    refine ⟨39783527161965207266854223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26522351441310138177902815 39783527161965207266854223)
    ·
      refine ⟨59675290742947810900281335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39783527161965207266854223 59675290742947810900281335)
      ·
        refine ⟨89512936114421716350422003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59675290742947810900281335 89512936114421716350422003)
        ·
          refine ⟨134269404171632574525633005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89512936114421716350422003 134269404171632574525633005)
          ·
            refine ⟨50351026564362215447112377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 134269404171632574525633005 50351026564362215447112377)
            ·
              refine ⟨37763269923271661585334283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50351026564362215447112377 37763269923271661585334283)
              ·
                refine ⟨56644904884907492378001425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37763269923271661585334283 56644904884907492378001425)
                ·
                  refine ⟨42483678663680619283501069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56644904884907492378001425 42483678663680619283501069)
                  ·
                    refine ⟨15931379498880232231312901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42483678663680619283501069 15931379498880232231312901)
                    ·
                      refine ⟨2987133656040043543371169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15931379498880232231312901 2987133656040043543371169)
                      ·
                        rfl

theorem cell23_5817422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 1, 2, 3, 4].length) (baseStart_5817422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5817422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5817422 prefixEnd_5817422 := by exact prefixLift 5817422
  have htrace : WordTrace (prefixWord ++ tailWord_5817422) baseStart_5817422 baseEnd_5817422 := by
    simpa [prefixWord, tailWord_5817422, baseEnd_5817422] using wordTrace_append hprefix tailTrace_5817422
  have hstable : (prefixWord ++ tailWord_5817422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5817422).length < 2 ^ (prefixWord ++ tailWord_5817422).sum := by decide
  have hdescent : baseEnd_5817422 < baseStart_5817422 := by decide
  rcases family_descends (prefixWord ++ tailWord_5817422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5817439 : List Nat := [1, 1, 2, 3, 1, 1, 4, 3, 1, 4, 2]
def baseStart_5817439 : Nat := 118140960795 + 5817439 * 2 ^ 59
def prefixEnd_5817439 : Nat := 4983230072969 + 3 ^ 40 * 5817439 * 2
def baseEnd_5817439 : Nat := 2987142385211169976858591

theorem tailTrace_5817439 : CollatzResearch.WordTrace tailWord_5817439 prefixEnd_5817439 2987142385211169976858591 := by
  unfold tailWord_5817439
  simp only [CollatzResearch.WordTrace]
  refine ⟨212179431571419517326591371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141452954380946344884394247 212179431571419517326591371)
  ·
    refine ⟨318269147357129275989887057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212179431571419517326591371 318269147357129275989887057)
    ·
      refine ⟨238701860517846956992415293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 318269147357129275989887057 238701860517846956992415293)
      ·
        refine ⟨89513197694192608872155735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 238701860517846956992415293 89513197694192608872155735)
        ·
          refine ⟨134269796541288913308233603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89513197694192608872155735 134269796541288913308233603)
          ·
            refine ⟨201404694811933369962350405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134269796541288913308233603 201404694811933369962350405)
            ·
              refine ⟨37763380277237506867940701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 201404694811933369962350405 37763380277237506867940701)
              ·
                refine ⟨14161267603964065075477763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37763380277237506867940701 14161267603964065075477763)
                ·
                  refine ⟨21241901405946097613216645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14161267603964065075477763 21241901405946097613216645)
                  ·
                    refine ⟨3982856513614893302478121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21241901405946097613216645 3982856513614893302478121)
                    ·
                      refine ⟨2987142385211169976858591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3982856513614893302478121 2987142385211169976858591)
                      ·
                        rfl

theorem cell23_5817439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 3, 1, 4, 2].length) (baseStart_5817439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5817439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5817439 prefixEnd_5817439 := by exact prefixLift 5817439
  have htrace : WordTrace (prefixWord ++ tailWord_5817439) baseStart_5817439 baseEnd_5817439 := by
    simpa [prefixWord, tailWord_5817439, baseEnd_5817439] using wordTrace_append hprefix tailTrace_5817439
  have hstable : (prefixWord ++ tailWord_5817439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5817439).length < 2 ^ (prefixWord ++ tailWord_5817439).sum := by decide
  have hdescent : baseEnd_5817439 < baseStart_5817439 := by decide
  rcases family_descends (prefixWord ++ tailWord_5817439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5817473 : List Nat := [1, 2, 4, 2, 2, 1, 1, 4, 2, 2, 2]
def baseStart_5817473 : Nat := 118140960795 + 5817473 * 2 ^ 59
def prefixEnd_5817473 : Nat := 4983230072969 + 3 ^ 40 * 5817473 * 2
def baseEnd_5817473 : Nat := 2987159843553422843833435

theorem tailTrace_5817473 : CollatzResearch.WordTrace tailWord_5817473 prefixEnd_5817473 2987159843553422843833435 := by
  unfold tailWord_5817473
  simp only [CollatzResearch.WordTrace]
  refine ⟨212180671653296341133329073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141453781102197560755552715 212180671653296341133329073)
  ·
    refine ⟨159135503739972255849996805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212180671653296341133329073 159135503739972255849996805)
    ·
      refine ⟨29837906951244797971874401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 159135503739972255849996805 29837906951244797971874401)
      ·
        refine ⟨22378430213433598478905801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29837906951244797971874401 22378430213433598478905801)
        ·
          refine ⟨16783822660075198859179351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22378430213433598478905801 16783822660075198859179351)
          ·
            refine ⟨25175733990112798288769027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16783822660075198859179351 25175733990112798288769027)
            ·
              refine ⟨37763600985169197433153541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25175733990112798288769027 37763600985169197433153541)
              ·
                refine ⟨7080675184719224518716289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37763600985169197433153541 7080675184719224518716289)
                ·
                  refine ⟨5310506388539418389037217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7080675184719224518716289 5310506388539418389037217)
                  ·
                    refine ⟨3982879791404563791777913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5310506388539418389037217 3982879791404563791777913)
                    ·
                      refine ⟨2987159843553422843833435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3982879791404563791777913 2987159843553422843833435)
                      ·
                        rfl

theorem cell23_5817473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 4, 2, 2, 2].length) (baseStart_5817473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5817473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5817473 prefixEnd_5817473 := by exact prefixLift 5817473
  have htrace : WordTrace (prefixWord ++ tailWord_5817473) baseStart_5817473 baseEnd_5817473 := by
    simpa [prefixWord, tailWord_5817473, baseEnd_5817473] using wordTrace_append hprefix tailTrace_5817473
  have hstable : (prefixWord ++ tailWord_5817473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5817473).length < 2 ^ (prefixWord ++ tailWord_5817473).sum := by decide
  have hdescent : baseEnd_5817473 < baseStart_5817473 := by decide
  rcases family_descends (prefixWord ++ tailWord_5817473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5817509 : List Nat := [1, 3, 1, 2, 1, 4, 3, 1, 2, 5]
def baseStart_5817509 : Nat := 118140960795 + 5817509 * 2 ^ 59
def prefixEnd_5817509 : Nat := 4983230072969 + 3 ^ 40 * 5817509 * 2
def baseEnd_5817509 : Nat := 995726109618994900994423

theorem tailTrace_5817509 : CollatzResearch.WordTrace tailWord_5817509 prefixEnd_5817509 995726109618994900994423 := by
  unfold tailWord_5817509
  simp only [CollatzResearch.WordTrace]
  refine ⟨212181984681165919281639581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141454656454110612854426387 212181984681165919281639581)
  ·
    refine ⟨79568244255437219730614843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 212181984681165919281639581 79568244255437219730614843)
    ·
      refine ⟨119352366383155829595922265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79568244255437219730614843 119352366383155829595922265)
      ·
        refine ⟨89514274787366872196941699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119352366383155829595922265 89514274787366872196941699)
        ·
          refine ⟨134271412181050308295412549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89514274787366872196941699 134271412181050308295412549)
          ·
            refine ⟨25175889783946932805389853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 134271412181050308295412549 25175889783946932805389853)
            ·
              refine ⟨9440958668980099802021195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25175889783946932805389853 9440958668980099802021195)
              ·
                refine ⟨14161438003470149703031793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9440958668980099802021195 14161438003470149703031793)
                ·
                  refine ⟨10621078502602612277273845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14161438003470149703031793 10621078502602612277273845)
                  ·
                    refine ⟨995726109618994900994423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10621078502602612277273845 995726109618994900994423)
                    ·
                      rfl

theorem cell23_5817509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 3, 1, 2, 5].length) (baseStart_5817509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5817509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5817509 prefixEnd_5817509 := by exact prefixLift 5817509
  have htrace : WordTrace (prefixWord ++ tailWord_5817509) baseStart_5817509 baseEnd_5817509 := by
    simpa [prefixWord, tailWord_5817509, baseEnd_5817509] using wordTrace_append hprefix tailTrace_5817509
  have hstable : (prefixWord ++ tailWord_5817509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5817509).length < 2 ^ (prefixWord ++ tailWord_5817509).sum := by decide
  have hdescent : baseEnd_5817509 < baseStart_5817509 := by decide
  rcases family_descends (prefixWord ++ tailWord_5817509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5817546 : List Nat := [3, 1, 2, 1, 3, 2, 2, 1, 2, 4, 2]
def baseStart_5817546 : Nat := 118140960795 + 5817546 * 2 ^ 59
def prefixEnd_5817546 : Nat := 4983230072969 + 3 ^ 40 * 5817546 * 2
def baseEnd_5817546 : Nat := 2987197327641201058220599

theorem tailTrace_5817546 : CollatzResearch.WordTrace tailWord_5817546 prefixEnd_5817546 2987197327641201058220599 := by
  unfold tailWord_5817546
  simp only [CollatzResearch.WordTrace]
  refine ⟨53045833545507968650184123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141455556121354583067157661 53045833545507968650184123)
  ·
    refine ⟨79568750318261952975276185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53045833545507968650184123 79568750318261952975276185)
    ·
      refine ⟨59676562738696464731457139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79568750318261952975276185 59676562738696464731457139)
      ·
        refine ⟨89514844108044697097185709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59676562738696464731457139 89514844108044697097185709)
        ·
          refine ⟨33568066540516761411444641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89514844108044697097185709 33568066540516761411444641)
          ·
            refine ⟨25176049905387571058583481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33568066540516761411444641 25176049905387571058583481)
            ·
              refine ⟨18882037429040678293937611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25176049905387571058583481 18882037429040678293937611)
              ·
                refine ⟨28323056143561017440906417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18882037429040678293937611 28323056143561017440906417)
                ·
                  refine ⟨21242292107670763080679813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28323056143561017440906417 21242292107670763080679813)
                  ·
                    refine ⟨3982929770188268077627465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21242292107670763080679813 3982929770188268077627465)
                    ·
                      refine ⟨2987197327641201058220599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3982929770188268077627465 2987197327641201058220599)
                      ·
                        rfl

theorem cell23_5817546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 1, 2, 4, 2].length) (baseStart_5817546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5817546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5817546 prefixEnd_5817546 := by exact prefixLift 5817546
  have htrace : WordTrace (prefixWord ++ tailWord_5817546) baseStart_5817546 baseEnd_5817546 := by
    simpa [prefixWord, tailWord_5817546, baseEnd_5817546] using wordTrace_append hprefix tailTrace_5817546
  have hstable : (prefixWord ++ tailWord_5817546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5817546).length < 2 ^ (prefixWord ++ tailWord_5817546).sum := by decide
  have hdescent : baseEnd_5817546 < baseStart_5817546 := by decide
  rcases family_descends (prefixWord ++ tailWord_5817546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5817592 : List Nat := [2, 1, 2, 1, 1, 2, 1, 1, 4, 1, 7]
def baseStart_5817592 : Nat := 118140960795 + 5817592 * 2 ^ 59
def prefixEnd_5817592 : Nat := 4983230072969 + 3 ^ 40 * 5817592 * 2
def baseEnd_5817592 : Nat := 2987220947751307878245387

theorem tailTrace_5817592 : CollatzResearch.WordTrace tailWord_5817592 prefixEnd_5817592 2987220947751307878245387 := by
  unfold tailWord_5817592
  simp only [CollatzResearch.WordTrace]
  refine ⟨106092505969932612228455515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141456674626576816304607353 106092505969932612228455515)
  ·
    refine ⟨159138758954898918342683273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106092505969932612228455515 159138758954898918342683273)
    ·
      refine ⟨119354069216174188757012455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159138758954898918342683273 119354069216174188757012455)
      ·
        refine ⟨179031103824261283135518683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119354069216174188757012455 179031103824261283135518683)
        ·
          refine ⟨268546655736391924703278025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179031103824261283135518683 268546655736391924703278025)
          ·
            refine ⟨201409991802293943527458519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 268546655736391924703278025 201409991802293943527458519)
            ·
              refine ⟨302114987703440915291187779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 201409991802293943527458519 302114987703440915291187779)
              ·
                refine ⟨453172481555161372936781669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 302114987703440915291187779 453172481555161372936781669)
                ·
                  refine ⟨84969840291592757425646563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 453172481555161372936781669 84969840291592757425646563)
                  ·
                    refine ⟨127454760437389136138469845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 84969840291592757425646563 127454760437389136138469845)
                    ·
                      refine ⟨2987220947751307878245387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 127454760437389136138469845 2987220947751307878245387)
                      ·
                        rfl

theorem cell23_5817592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 4, 1, 7].length) (baseStart_5817592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5817592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5817592 prefixEnd_5817592 := by exact prefixLift 5817592
  have htrace : WordTrace (prefixWord ++ tailWord_5817592) baseStart_5817592 baseEnd_5817592 := by
    simpa [prefixWord, tailWord_5817592, baseEnd_5817592] using wordTrace_append hprefix tailTrace_5817592
  have hstable : (prefixWord ++ tailWord_5817592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5817592).length < 2 ^ (prefixWord ++ tailWord_5817592).sum := by decide
  have hdescent : baseEnd_5817592 < baseStart_5817592 := by decide
  rcases family_descends (prefixWord ++ tailWord_5817592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5817623 : List Nat := [1, 1, 3, 4, 1, 1, 4, 1, 2, 3, 2]
def baseStart_5817623 : Nat := 118140960795 + 5817623 * 2 ^ 59
def prefixEnd_5817623 : Nat := 4983230072969 + 3 ^ 40 * 5817623 * 2
def baseEnd_5817623 : Nat := 2987236865651597256957745

theorem tailTrace_5817623 : CollatzResearch.WordTrace tailWord_5817623 prefixEnd_5817623 2987236865651597256957745 := by
  unfold tailWord_5817623
  simp only [CollatzResearch.WordTrace]
  refine ⟨212186142602752916751289523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141457428401835277834193015 212186142602752916751289523)
  ·
    refine ⟨318279213904129375126934285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212186142602752916751289523 318279213904129375126934285)
    ·
      refine ⟨119354705214048515672600357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 318279213904129375126934285 119354705214048515672600357)
      ·
        refine ⟨22379007227634096688612567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 119354705214048515672600357 22379007227634096688612567)
        ·
          refine ⟨33568510841451145032918851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22379007227634096688612567 33568510841451145032918851)
          ·
            refine ⟨50352766262176717549378277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33568510841451145032918851 50352766262176717549378277)
            ·
              refine ⟨9441143674158134540508427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50352766262176717549378277 9441143674158134540508427)
              ·
                refine ⟨14161715511237201810762641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9441143674158134540508427 14161715511237201810762641)
                ·
                  refine ⟨10621286633427901358071981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14161715511237201810762641 10621286633427901358071981)
                  ·
                    refine ⟨3982982487535463009276993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10621286633427901358071981 3982982487535463009276993)
                    ·
                      refine ⟨2987236865651597256957745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3982982487535463009276993 2987236865651597256957745)
                      ·
                        rfl

theorem cell23_5817623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 4, 1, 2, 3, 2].length) (baseStart_5817623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5817623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5817623 prefixEnd_5817623 := by exact prefixLift 5817623
  have htrace : WordTrace (prefixWord ++ tailWord_5817623) baseStart_5817623 baseEnd_5817623 := by
    simpa [prefixWord, tailWord_5817623, baseEnd_5817623] using wordTrace_append hprefix tailTrace_5817623
  have hstable : (prefixWord ++ tailWord_5817623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5817623).length < 2 ^ (prefixWord ++ tailWord_5817623).sum := by decide
  have hdescent : baseEnd_5817623 < baseStart_5817623 := by decide
  rcases family_descends (prefixWord ++ tailWord_5817623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5817676 : List Nat := [2, 2, 1, 3, 2, 3, 3, 7]
def baseStart_5817676 : Nat := 118140960795 + 5817676 * 2 ^ 59
def prefixEnd_5817676 : Nat := 4983230072969 + 3 ^ 40 * 5817676 * 2
def baseEnd_5817676 : Nat := 110639410375047612947963

theorem tailTrace_5817676 : CollatzResearch.WordTrace tailWord_5817676 prefixEnd_5817676 110639410375047612947963 := by
  unfold tailWord_5817676
  simp only [CollatzResearch.WordTrace]
  refine ⟨106094037835780453401484441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141458717114373937868645921 106094037835780453401484441)
  ·
    refine ⟨79570528376835340051113331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106094037835780453401484441 79570528376835340051113331)
    ·
      refine ⟨119355792565253010076669997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79570528376835340051113331 119355792565253010076669997)
      ·
        refine ⟨44758422211969878778751249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119355792565253010076669997 44758422211969878778751249)
        ·
          refine ⟨33568816658977409084063437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44758422211969878778751249 33568816658977409084063437)
          ·
            refine ⟨12588306247116528406523789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33568816658977409084063437 12588306247116528406523789)
            ·
              refine ⟨4720614842668698152446421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12588306247116528406523789 4720614842668698152446421)
              ·
                refine ⟨110639410375047612947963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4720614842668698152446421 110639410375047612947963)
                ·
                  rfl

theorem cell23_5817676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 3, 7].length) (baseStart_5817676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5817676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5817676 prefixEnd_5817676 := by exact prefixLift 5817676
  have htrace : WordTrace (prefixWord ++ tailWord_5817676) baseStart_5817676 baseEnd_5817676 := by
    simpa [prefixWord, tailWord_5817676, baseEnd_5817676] using wordTrace_append hprefix tailTrace_5817676
  have hstable : (prefixWord ++ tailWord_5817676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5817676).length < 2 ^ (prefixWord ++ tailWord_5817676).sum := by decide
  have hdescent : baseEnd_5817676 < baseStart_5817676 := by decide
  rcases family_descends (prefixWord ++ tailWord_5817676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5817687 : List Nat := [1, 1, 3, 2, 3, 3, 2, 3, 1, 2, 2]
def baseStart_5817687 : Nat := 118140960795 + 5817687 * 2 ^ 59
def prefixEnd_5817687 : Nat := 4983230072969 + 3 ^ 40 * 5817687 * 2
def baseEnd_5817687 : Nat := 2987269728413485006557451

theorem tailTrace_5817687 : CollatzResearch.WordTrace tailWord_5817687 prefixEnd_5817687 2987269728413485006557451 := by
  unfold tailWord_5817687
  simp only [CollatzResearch.WordTrace]
  refine ⟨212188476874521055681619315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141458984583014037121079543 212188476874521055681619315)
  ·
    refine ⟨318282715311781583522428973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212188476874521055681619315 318282715311781583522428973)
    ·
      refine ⟨119356018241918093820910865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 318282715311781583522428973 119356018241918093820910865)
      ·
        refine ⟨89517013681438570365683149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119356018241918093820910865 89517013681438570365683149)
        ·
          refine ⟨33568880130539463887131181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89517013681438570365683149 33568880130539463887131181)
          ·
            refine ⟨12588330048952298957674193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33568880130539463887131181 12588330048952298957674193)
            ·
              refine ⟨9441247536714224218255645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12588330048952298957674193 9441247536714224218255645)
              ·
                refine ⟨3540467826267834081845867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9441247536714224218255645 3540467826267834081845867)
                ·
                  refine ⟨5310701739401751122768801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3540467826267834081845867 5310701739401751122768801)
                  ·
                    refine ⟨3983026304551313342076601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5310701739401751122768801 3983026304551313342076601)
                    ·
                      refine ⟨2987269728413485006557451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3983026304551313342076601 2987269728413485006557451)
                      ·
                        rfl

theorem cell23_5817687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 2, 3, 1, 2, 2].length) (baseStart_5817687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5817687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5817687 prefixEnd_5817687 := by exact prefixLift 5817687
  have htrace : WordTrace (prefixWord ++ tailWord_5817687) baseStart_5817687 baseEnd_5817687 := by
    simpa [prefixWord, tailWord_5817687, baseEnd_5817687] using wordTrace_append hprefix tailTrace_5817687
  have hstable : (prefixWord ++ tailWord_5817687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5817687).length < 2 ^ (prefixWord ++ tailWord_5817687).sum := by decide
  have hdescent : baseEnd_5817687 < baseStart_5817687 := by decide
  rcases family_descends (prefixWord ++ tailWord_5817687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5817719 : List Nat := [1, 1, 3, 1, 1, 2, 3, 3, 2, 6]
def baseStart_5817719 : Nat := 118140960795 + 5817719 * 2 ^ 59
def prefixEnd_5817719 : Nat := 4983230072969 + 3 ^ 40 * 5817719 * 2
def baseEnd_5817719 : Nat := 995762053264809627119101

theorem tailTrace_5817719 : CollatzResearch.WordTrace tailWord_5817719 prefixEnd_5817719 995762053264809627119101 := by
  unfold tailWord_5817719
  simp only [CollatzResearch.WordTrace]
  refine ⟨212189644010405125146784211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141459762673603416764522807 212189644010405125146784211)
  ·
    refine ⟨318284466015607687720176317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212189644010405125146784211 318284466015607687720176317)
    ·
      refine ⟨119356674755852882895066119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 318284466015607687720176317 119356674755852882895066119)
      ·
        refine ⟨179035012133779324342599179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119356674755852882895066119 179035012133779324342599179)
        ·
          refine ⟨268552518200668986513898769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179035012133779324342599179 268552518200668986513898769)
          ·
            refine ⟨201414388650501739885424077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 268552518200668986513898769 201414388650501739885424077)
            ·
              refine ⟨75530395743938152457034029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 201414388650501739885424077 75530395743938152457034029)
              ·
                refine ⟨28323898403976807171387761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75530395743938152457034029 28323898403976807171387761)
                ·
                  refine ⟨21242923802982605378540821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28323898403976807171387761 21242923802982605378540821)
                  ·
                    refine ⟨995762053264809627119101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21242923802982605378540821 995762053264809627119101)
                    ·
                      rfl

theorem cell23_5817719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 3, 2, 6].length) (baseStart_5817719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5817719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5817719 prefixEnd_5817719 := by exact prefixLift 5817719
  have htrace : WordTrace (prefixWord ++ tailWord_5817719) baseStart_5817719 baseEnd_5817719 := by
    simpa [prefixWord, tailWord_5817719, baseEnd_5817719] using wordTrace_append hprefix tailTrace_5817719
  have hstable : (prefixWord ++ tailWord_5817719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5817719).length < 2 ^ (prefixWord ++ tailWord_5817719).sum := by decide
  have hdescent : baseEnd_5817719 < baseStart_5817719 := by decide
  rcases family_descends (prefixWord ++ tailWord_5817719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5817749 : List Nat := [1, 3, 2, 1, 1, 2, 2, 2, 9]
def baseStart_5817749 : Nat := 118140960795 + 5817749 * 2 ^ 59
def prefixEnd_5817749 : Nat := 4983230072969 + 3 ^ 40 * 5817749 * 2
def baseEnd_5817749 : Nat := 331922396023784862664685

theorem tailTrace_5817749 : CollatzResearch.WordTrace tailWord_5817749 prefixEnd_5817749 331922396023784862664685 := by
  unfold tailWord_5817749
  simp only [CollatzResearch.WordTrace]
  refine ⟨212190738200296440270376301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141460492133530960180250867 212190738200296440270376301)
  ·
    refine ⟨79571526825111165101391113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 212190738200296440270376301 79571526825111165101391113)
    ·
      refine ⟨59678645118833373826043335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79571526825111165101391113 59678645118833373826043335)
      ·
        refine ⟨89517967678250060739065003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59678645118833373826043335 89517967678250060739065003)
        ·
          refine ⟨134276951517375091108597505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89517967678250060739065003 134276951517375091108597505)
          ·
            refine ⟨100707713638031318331448129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134276951517375091108597505 100707713638031318331448129)
            ·
              refine ⟨75530785228523488748586097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100707713638031318331448129 75530785228523488748586097)
              ·
                refine ⟨56648088921392616561439573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75530785228523488748586097 56648088921392616561439573)
                ·
                  refine ⟨331922396023784862664685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 56648088921392616561439573 331922396023784862664685)
                  ·
                    rfl

theorem cell23_5817749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 2, 9].length) (baseStart_5817749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5817749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5817749 prefixEnd_5817749 := by exact prefixLift 5817749
  have htrace : WordTrace (prefixWord ++ tailWord_5817749) baseStart_5817749 baseEnd_5817749 := by
    simpa [prefixWord, tailWord_5817749, baseEnd_5817749] using wordTrace_append hprefix tailTrace_5817749
  have hstable : (prefixWord ++ tailWord_5817749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5817749).length < 2 ^ (prefixWord ++ tailWord_5817749).sum := by decide
  have hdescent : baseEnd_5817749 < baseStart_5817749 := by decide
  rcases family_descends (prefixWord ++ tailWord_5817749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5817760 : List Nat := [2, 1, 1, 4, 1, 2, 2, 4, 2, 2, 2]
def baseStart_5817760 : Nat := 118140960795 + 5817760 * 2 ^ 59
def prefixEnd_5817760 : Nat := 4983230072969 + 3 ^ 40 * 5817760 * 2
def baseEnd_5817760 : Nat := 2987307212501263220944615

theorem tailTrace_5817760 : CollatzResearch.WordTrace tailWord_5817760 prefixEnd_5817760 2987307212501263220944615 := by
  unfold tailWord_5817760
  simp only [CollatzResearch.WordTrace]
  refine ⟨106095569701628294574513367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141460759602171059432684489 106095569701628294574513367)
  ·
    refine ⟨159143354552442441861770051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106095569701628294574513367 159143354552442441861770051)
    ·
      refine ⟨238715031828663662792655077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159143354552442441861770051 238715031828663662792655077)
      ·
        refine ⟨44759068467874436773622827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 238715031828663662792655077 44759068467874436773622827)
        ·
          refine ⟨67138602701811655160434241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44759068467874436773622827 67138602701811655160434241)
          ·
            refine ⟨50353952026358741370325681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67138602701811655160434241 50353952026358741370325681)
            ·
              refine ⟨37765464019769056027744261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50353952026358741370325681 37765464019769056027744261)
              ·
                refine ⟨7081024503706698005202049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37765464019769056027744261 7081024503706698005202049)
                ·
                  refine ⟨5310768377780023503901537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7081024503706698005202049 5310768377780023503901537)
                  ·
                    refine ⟨3983076283335017627926153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5310768377780023503901537 3983076283335017627926153)
                    ·
                      refine ⟨2987307212501263220944615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3983076283335017627926153 2987307212501263220944615)
                      ·
                        rfl

theorem cell23_5817760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 4, 2, 2, 2].length) (baseStart_5817760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5817760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5817760 prefixEnd_5817760 := by exact prefixLift 5817760
  have htrace : WordTrace (prefixWord ++ tailWord_5817760) baseStart_5817760 baseEnd_5817760 := by
    simpa [prefixWord, tailWord_5817760, baseEnd_5817760] using wordTrace_append hprefix tailTrace_5817760
  have hstable : (prefixWord ++ tailWord_5817760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5817760).length < 2 ^ (prefixWord ++ tailWord_5817760).sum := by decide
  have hdescent : baseEnd_5817760 < baseStart_5817760 := by decide
  rcases family_descends (prefixWord ++ tailWord_5817760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5817779 : List Nat := [1, 1, 1, 2, 3, 1, 1, 3, 3, 7]
def baseStart_5817779 : Nat := 118140960795 + 5817779 * 2 ^ 59
def prefixEnd_5817779 : Nat := 4983230072969 + 3 ^ 40 * 5817779 * 2
def baseEnd_5817779 : Nat := 995772322877899548869009

theorem tailTrace_5817779 : CollatzResearch.WordTrace tailWord_5817779 prefixEnd_5817779 995772322877899548869009 := by
  unfold tailWord_5817779
  simp only [CollatzResearch.WordTrace]
  refine ⟨212191832390187755393968391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141461221593458503595978927 212191832390187755393968391)
  ·
    refine ⟨318287748585281633090952587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212191832390187755393968391 318287748585281633090952587)
    ·
      refine ⟨477431622877922449636428881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 318287748585281633090952587 477431622877922449636428881)
      ·
        refine ⟨358073717158441837227321661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 477431622877922449636428881 358073717158441837227321661)
        ·
          refine ⟨134277643934415688960245623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 358073717158441837227321661 134277643934415688960245623)
          ·
            refine ⟨201416465901623533440368435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134277643934415688960245623 201416465901623533440368435)
            ·
              refine ⟨302124698852435300160552653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 201416465901623533440368435 302124698852435300160552653)
              ·
                refine ⟨113296762069663237560207245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 302124698852435300160552653 113296762069663237560207245)
                ·
                  refine ⟨42486285776123714085077717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 113296762069663237560207245 42486285776123714085077717)
                  ·
                    refine ⟨995772322877899548869009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42486285776123714085077717 995772322877899548869009)
                    ·
                      rfl

theorem cell23_5817779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 3, 3, 7].length) (baseStart_5817779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5817779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5817779 prefixEnd_5817779 := by exact prefixLift 5817779
  have htrace : WordTrace (prefixWord ++ tailWord_5817779) baseStart_5817779 baseEnd_5817779 := by
    simpa [prefixWord, tailWord_5817779, baseEnd_5817779] using wordTrace_append hprefix tailTrace_5817779
  have hstable : (prefixWord ++ tailWord_5817779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5817779).length < 2 ^ (prefixWord ++ tailWord_5817779).sum := by decide
  have hdescent : baseEnd_5817779 < baseStart_5817779 := by decide
  rcases family_descends (prefixWord ++ tailWord_5817779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5817806 : List Nat := [4, 1, 1, 1, 2, 1, 3, 2, 1, 2, 5]
def baseStart_5817806 : Nat := 118140960795 + 5817806 * 2 ^ 59
def prefixEnd_5817806 : Nat := 4983230072969 + 3 ^ 40 * 5817806 * 2
def baseEnd_5817806 : Nat := 2987330832611370040969403

theorem tailTrace_5817806 : CollatzResearch.WordTrace tailWord_5817806 prefixEnd_5817806 2987330832611370040969403 := by
  unfold tailWord_5817806
  simp only [CollatzResearch.WordTrace]
  refine ⟨26524102145136242375650159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 141461878107393292670134181 26524102145136242375650159)
  ·
    refine ⟨39786153217704363563475239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26524102145136242375650159 39786153217704363563475239)
    ·
      refine ⟨59679229826556545345212859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39786153217704363563475239 59679229826556545345212859)
      ·
        refine ⟨89518844739834818017819289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59679229826556545345212859 89518844739834818017819289)
        ·
          refine ⟨67139133554876113513364467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89518844739834818017819289 67139133554876113513364467)
          ·
            refine ⟨100708700332314170270046701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67139133554876113513364467 100708700332314170270046701)
            ·
              refine ⟨37765762624617813851267513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 100708700332314170270046701 37765762624617813851267513)
              ·
                refine ⟨28324321968463360388450635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37765762624617813851267513 28324321968463360388450635)
                ·
                  refine ⟨42486482952695040582675953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28324321968463360388450635 42486482952695040582675953)
                  ·
                    refine ⟨31864862214521280437006965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42486482952695040582675953 31864862214521280437006965)
                    ·
                      refine ⟨2987330832611370040969403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31864862214521280437006965 2987330832611370040969403)
                      ·
                        rfl

theorem cell23_5817806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 2, 1, 2, 5].length) (baseStart_5817806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5817806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5817806 prefixEnd_5817806 := by exact prefixLift 5817806
  have htrace : WordTrace (prefixWord ++ tailWord_5817806) baseStart_5817806 baseEnd_5817806 := by
    simpa [prefixWord, tailWord_5817806, baseEnd_5817806] using wordTrace_append hprefix tailTrace_5817806
  have hstable : (prefixWord ++ tailWord_5817806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5817806).length < 2 ^ (prefixWord ++ tailWord_5817806).sum := by decide
  have hdescent : baseEnd_5817806 < baseStart_5817806 := by decide
  rcases family_descends (prefixWord ++ tailWord_5817806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5817819 : List Nat := [1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 9]
def baseStart_5817819 : Nat := 118140960795 + 5817819 * 2 ^ 59
def prefixEnd_5817819 : Nat := 4983230072969 + 3 ^ 40 * 5817819 * 2
def baseEnd_5817819 : Nat := 2987337507859878490106843

theorem tailTrace_5817819 : CollatzResearch.WordTrace tailWord_5817819 prefixEnd_5817819 2987337507859878490106843 := by
  unfold tailWord_5817819
  simp only [CollatzResearch.WordTrace]
  refine ⟨212193291310042842225424511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141462194206695228150283007 212193291310042842225424511)
  ·
    refine ⟨318289936965064263338136767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212193291310042842225424511 318289936965064263338136767)
    ·
      refine ⟨477434905447596395007205151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 318289936965064263338136767 477434905447596395007205151)
      ·
        refine ⟨716152358171394592510807727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 477434905447596395007205151 716152358171394592510807727)
        ·
          refine ⟨1074228537257091888766211591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 716152358171394592510807727 1074228537257091888766211591)
          ·
            refine ⟨1611342805885637833149317387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1074228537257091888766211591 1611342805885637833149317387)
            ·
              refine ⟨2417014208828456749723976081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1611342805885637833149317387 2417014208828456749723976081)
              ·
                refine ⟨1812760656621342562292982061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2417014208828456749723976081 1812760656621342562292982061)
                ·
                  refine ⟨679785246233003460859868273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1812760656621342562292982061 679785246233003460859868273)
                  ·
                    refine ⟨509838934674752595644901205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 679785246233003460859868273 509838934674752595644901205)
                    ·
                      refine ⟨2987337507859878490106843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 509838934674752595644901205 2987337507859878490106843)
                      ·
                        rfl

theorem cell23_5817819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 9].length) (baseStart_5817819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5817819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5817819 prefixEnd_5817819 := by exact prefixLift 5817819
  have htrace : WordTrace (prefixWord ++ tailWord_5817819) baseStart_5817819 baseEnd_5817819 := by
    simpa [prefixWord, tailWord_5817819, baseEnd_5817819] using wordTrace_append hprefix tailTrace_5817819
  have hstable : (prefixWord ++ tailWord_5817819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5817819).length < 2 ^ (prefixWord ++ tailWord_5817819).sum := by decide
  have hdescent : baseEnd_5817819 < baseStart_5817819 := by decide
  rcases family_descends (prefixWord ++ tailWord_5817819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5817853 : List Nat := [1, 4, 1, 1, 1, 5, 1, 1, 1, 4, 3]
def baseStart_5817853 : Nat := 118140960795 + 5817853 * 2 ^ 59
def prefixEnd_5817853 : Nat := 4983230072969 + 3 ^ 40 * 5817853 * 2
def baseEnd_5817853 : Nat := 2987354966202131357081687

theorem tailTrace_5817853 : CollatzResearch.WordTrace tailWord_5817853 prefixEnd_5817853 2987354966202131357081687 := by
  unfold tailWord_5817853
  simp only [CollatzResearch.WordTrace]
  refine ⟨212194531391919666032162213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141463020927946444021441475 212194531391919666032162213)
  ·
    refine ⟨39786474635984937381030415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 212194531391919666032162213 39786474635984937381030415)
    ·
      refine ⟨59679711953977406071545623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39786474635984937381030415 59679711953977406071545623)
      ·
        refine ⟨89519567930966109107318435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59679711953977406071545623 89519567930966109107318435)
        ·
          refine ⟨134279351896449163660977653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89519567930966109107318435 134279351896449163660977653)
          ·
            refine ⟨12588689240292109093216655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 134279351896449163660977653 12588689240292109093216655)
            ·
              refine ⟨18883033860438163639824983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12588689240292109093216655 18883033860438163639824983)
              ·
                refine ⟨28324550790657245459737475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18883033860438163639824983 28324550790657245459737475)
                ·
                  refine ⟨42486826185985868189606213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28324550790657245459737475 42486826185985868189606213)
                  ·
                    refine ⟨7966279909872350285551165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42486826185985868189606213 7966279909872350285551165)
                    ·
                      refine ⟨2987354966202131357081687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7966279909872350285551165 2987354966202131357081687)
                      ·
                        rfl

theorem cell23_5817853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 1, 1, 4, 3].length) (baseStart_5817853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5817853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5817853 prefixEnd_5817853 := by exact prefixLift 5817853
  have htrace : WordTrace (prefixWord ++ tailWord_5817853) baseStart_5817853 baseEnd_5817853 := by
    simpa [prefixWord, tailWord_5817853, baseEnd_5817853] using wordTrace_append hprefix tailTrace_5817853
  have hstable : (prefixWord ++ tailWord_5817853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5817853).length < 2 ^ (prefixWord ++ tailWord_5817853).sum := by decide
  have hdescent : baseEnd_5817853 < baseStart_5817853 := by decide
  rcases family_descends (prefixWord ++ tailWord_5817853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5817927 : List Nat := [1, 1, 4, 1, 5, 1, 1, 2, 2, 3, 2]
def baseStart_5817927 : Nat := 118140960795 + 5817927 * 2 ^ 59
def prefixEnd_5817927 : Nat := 4983230072969 + 3 ^ 40 * 5817927 * 2
def baseEnd_5817927 : Nat := 2987392963770564067556347

theorem tailTrace_5817927 : CollatzResearch.WordTrace tailWord_5817927 prefixEnd_5817927 2987392963770564067556347 := by
  unfold tailWord_5817927
  simp only [CollatzResearch.WordTrace]
  refine ⟨212197230393651576670356035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141464820262434384446904023 212197230393651576670356035)
  ·
    refine ⟨318295845590477365005534053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212197230393651576670356035 318295845590477365005534053)
    ·
      refine ⟨59680471048214505938537635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 318295845590477365005534053 59680471048214505938537635)
      ·
        refine ⟨89520706572321758907806453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59680471048214505938537635 89520706572321758907806453)
        ·
          refine ⟨8392566241155164897606855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 89520706572321758907806453 8392566241155164897606855)
          ·
            refine ⟨12588849361732747346410283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8392566241155164897606855 12588849361732747346410283)
            ·
              refine ⟨18883274042599121019615425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12588849361732747346410283 18883274042599121019615425)
              ·
                refine ⟨14162455531949340764711569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18883274042599121019615425 14162455531949340764711569)
                ·
                  refine ⟨10621841648962005573533677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14162455531949340764711569 10621841648962005573533677)
                  ·
                    refine ⟨3983190618360752090075129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10621841648962005573533677 3983190618360752090075129)
                    ·
                      refine ⟨2987392963770564067556347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3983190618360752090075129 2987392963770564067556347)
                      ·
                        rfl

theorem cell23_5817927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 2, 2, 3, 2].length) (baseStart_5817927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5817927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5817927 prefixEnd_5817927 := by exact prefixLift 5817927
  have htrace : WordTrace (prefixWord ++ tailWord_5817927) baseStart_5817927 baseEnd_5817927 := by
    simpa [prefixWord, tailWord_5817927, baseEnd_5817927] using wordTrace_append hprefix tailTrace_5817927
  have hstable : (prefixWord ++ tailWord_5817927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5817927).length < 2 ^ (prefixWord ++ tailWord_5817927).sum := by decide
  have hdescent : baseEnd_5817927 < baseStart_5817927 := by decide
  rcases family_descends (prefixWord ++ tailWord_5817927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5817936 : List Nat := [2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 6]
def baseStart_5817936 : Nat := 118140960795 + 5817936 * 2 ^ 59
def prefixEnd_5817936 : Nat := 4983230072969 + 3 ^ 40 * 5817936 * 2
def baseEnd_5817936 : Nat := 2987397585096454532343805

theorem tailTrace_5817936 : CollatzResearch.WordTrace tailWord_5817936 prefixEnd_5817936 2987397585096454532343805 := by
  unfold tailWord_5817936
  simp only [CollatzResearch.WordTrace]
  refine ⟨106098779325309485603716831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141465039100412647471622441 106098779325309485603716831)
  ·
    refine ⟨159148168987964228405575247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106098779325309485603716831 159148168987964228405575247)
    ·
      refine ⟨238722253481946342608362871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159148168987964228405575247 238722253481946342608362871)
      ·
        refine ⟨358083380222919513912544307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238722253481946342608362871 358083380222919513912544307)
        ·
          refine ⟨537125070334379270868816461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 358083380222919513912544307 537125070334379270868816461)
          ·
            refine ⟨201421901375392226575806173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 537125070334379270868816461 201421901375392226575806173)
            ·
              refine ⟨75533213015772084965927315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 201421901375392226575806173 75533213015772084965927315)
              ·
                refine ⟨113299819523658127448890973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75533213015772084965927315 113299819523658127448890973)
                ·
                  refine ⟨42487432321371797793334115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 113299819523658127448890973 42487432321371797793334115)
                  ·
                    refine ⟨63731148482057696690001173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42487432321371797793334115 63731148482057696690001173)
                    ·
                      refine ⟨2987397585096454532343805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63731148482057696690001173 2987397585096454532343805)
                      ·
                        rfl

theorem cell23_5817936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 6].length) (baseStart_5817936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5817936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5817936 prefixEnd_5817936 := by exact prefixLift 5817936
  have htrace : WordTrace (prefixWord ++ tailWord_5817936) baseStart_5817936 baseEnd_5817936 := by
    simpa [prefixWord, tailWord_5817936, baseEnd_5817936] using wordTrace_append hprefix tailTrace_5817936
  have hstable : (prefixWord ++ tailWord_5817936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5817936).length < 2 ^ (prefixWord ++ tailWord_5817936).sum := by decide
  have hdescent : baseEnd_5817936 < baseStart_5817936 := by decide
  rcases family_descends (prefixWord ++ tailWord_5817936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5817943 : List Nat := [1, 1, 3, 2, 2, 3, 2, 2, 1, 1, 5]
def baseStart_5817943 : Nat := 118140960795 + 5817943 * 2 ^ 59
def prefixEnd_5817943 : Nat := 4983230072969 + 3 ^ 40 * 5817943 * 2
def baseEnd_5817943 : Nat := 2987401179461036004956273

theorem tailTrace_5817943 : CollatzResearch.WordTrace tailWord_5817943 prefixEnd_5817943 2987401179461036004956273 := by
  unfold tailWord_5817943
  simp only [CollatzResearch.WordTrace]
  refine ⟨212197813961593611402938483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141465209307729074268625655 212197813961593611402938483)
  ·
    refine ⟨318296720942390417104407725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212197813961593611402938483 318296720942390417104407725)
    ·
      refine ⟨119361270353396406414152897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 318296720942390417104407725 119361270353396406414152897)
      ·
        refine ⟨89520952765047304810614673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119361270353396406414152897 89520952765047304810614673)
        ·
          refine ⟨67140714573785478607961005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89520952765047304810614673 67140714573785478607961005)
          ·
            refine ⟨25177767965169554477985377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67140714573785478607961005 25177767965169554477985377)
            ·
              refine ⟨18883325973877165858489033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25177767965169554477985377 18883325973877165858489033)
              ·
                refine ⟨14162494480407874393866775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18883325973877165858489033 14162494480407874393866775)
                ·
                  refine ⟨21243741720611811590800163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14162494480407874393866775 21243741720611811590800163)
                  ·
                    refine ⟨31865612580917717386200245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21243741720611811590800163 31865612580917717386200245)
                    ·
                      refine ⟨2987401179461036004956273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31865612580917717386200245 2987401179461036004956273)
                      ·
                        rfl

theorem cell23_5817943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 2, 1, 1, 5].length) (baseStart_5817943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5817943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5817943 prefixEnd_5817943 := by exact prefixLift 5817943
  have htrace : WordTrace (prefixWord ++ tailWord_5817943) baseStart_5817943 baseEnd_5817943 := by
    simpa [prefixWord, tailWord_5817943, baseEnd_5817943] using wordTrace_append hprefix tailTrace_5817943
  have hstable : (prefixWord ++ tailWord_5817943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5817943).length < 2 ^ (prefixWord ++ tailWord_5817943).sum := by decide
  have hdescent : baseEnd_5817943 < baseStart_5817943 := by decide
  rcases family_descends (prefixWord ++ tailWord_5817943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5817953 : List Nat := [1, 2, 3, 1, 1, 3, 2, 3, 1, 2, 4]
def baseStart_5817953 : Nat := 118140960795 + 5817953 * 2 ^ 59
def prefixEnd_5817953 : Nat := 4983230072969 + 3 ^ 40 * 5817953 * 2
def baseEnd_5817953 : Nat := 2987406314267580965831227

theorem tailTrace_5817953 : CollatzResearch.WordTrace tailWord_5817953 prefixEnd_5817953 2987406314267580965831227 := by
  unfold tailWord_5817953
  simp only [CollatzResearch.WordTrace]
  refine ⟨212198178691557383110802513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141465452461038255407201675 212198178691557383110802513)
  ·
    refine ⟨159148634018668037333101885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212198178691557383110802513 159148634018668037333101885)
    ·
      refine ⟨59680737757000513999913207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 159148634018668037333101885 59680737757000513999913207)
      ·
        refine ⟨89521106635500770999869811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59680737757000513999913207 89521106635500770999869811)
        ·
          refine ⟨134281659953251156499804717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89521106635500770999869811 134281659953251156499804717)
          ·
            refine ⟨50355622482469183687426769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 134281659953251156499804717 50355622482469183687426769)
            ·
              refine ⟨37766716861851887765570077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50355622482469183687426769 37766716861851887765570077)
              ·
                refine ⟨14162518823194457912088779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37766716861851887765570077 14162518823194457912088779)
                ·
                  refine ⟨21243778234791686868133169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14162518823194457912088779 21243778234791686868133169)
                  ·
                    refine ⟨15932833676093765151099877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21243778234791686868133169 15932833676093765151099877)
                    ·
                      refine ⟨2987406314267580965831227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15932833676093765151099877 2987406314267580965831227)
                      ·
                        rfl

theorem cell23_5817953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 3, 1, 2, 4].length) (baseStart_5817953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5817953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5817953 prefixEnd_5817953 := by exact prefixLift 5817953
  have htrace : WordTrace (prefixWord ++ tailWord_5817953) baseStart_5817953 baseEnd_5817953 := by
    simpa [prefixWord, tailWord_5817953, baseEnd_5817953] using wordTrace_append hprefix tailTrace_5817953
  have hstable : (prefixWord ++ tailWord_5817953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5817953).length < 2 ^ (prefixWord ++ tailWord_5817953).sum := by decide
  have hdescent : baseEnd_5817953 < baseStart_5817953 := by decide
  rcases family_descends (prefixWord ++ tailWord_5817953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5817957 : List Nat := [1, 3, 1, 3, 3, 3, 1, 2, 1, 1, 4]
def baseStart_5817957 : Nat := 118140960795 + 5817957 * 2 ^ 59
def prefixEnd_5817957 : Nat := 4983230072969 + 3 ^ 40 * 5817957 * 2
def baseEnd_5817957 : Nat := 2987408368190198950181209

theorem tailTrace_5817957 : CollatzResearch.WordTrace tailWord_5817957 prefixEnd_5817957 2987408368190198950181209 := by
  unfold tailWord_5817957
  simp only [CollatzResearch.WordTrace]
  refine ⟨212198324583542891793948125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141465549722361927862632083 212198324583542891793948125)
  ·
    refine ⟨79574371718828584422730547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 212198324583542891793948125 79574371718828584422730547)
    ·
      refine ⟨119361557578242876634095821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79574371718828584422730547 119361557578242876634095821)
      ·
        refine ⟨44760584091841078737785933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119361557578242876634095821 44760584091841078737785933)
        ·
          refine ⟨16785219034440404526669725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44760584091841078737785933 16785219034440404526669725)
          ·
            refine ⟨6294457137915151697501147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16785219034440404526669725 6294457137915151697501147)
            ·
              refine ⟨9441685706872727546251721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6294457137915151697501147 9441685706872727546251721)
              ·
                refine ⟨7081264280154545659688791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9441685706872727546251721 7081264280154545659688791)
                ·
                  refine ⟨10621896420231818489533187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7081264280154545659688791 10621896420231818489533187)
                  ·
                    refine ⟨15932844630347727734299781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10621896420231818489533187 15932844630347727734299781)
                    ·
                      refine ⟨2987408368190198950181209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15932844630347727734299781 2987408368190198950181209)
                      ·
                        rfl

theorem cell23_5817957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 1, 2, 1, 1, 4].length) (baseStart_5817957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5817957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5817957 prefixEnd_5817957 := by exact prefixLift 5817957
  have htrace : WordTrace (prefixWord ++ tailWord_5817957) baseStart_5817957 baseEnd_5817957 := by
    simpa [prefixWord, tailWord_5817957, baseEnd_5817957] using wordTrace_append hprefix tailTrace_5817957
  have hstable : (prefixWord ++ tailWord_5817957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5817957).length < 2 ^ (prefixWord ++ tailWord_5817957).sum := by decide
  have hdescent : baseEnd_5817957 < baseStart_5817957 := by decide
  rcases family_descends (prefixWord ++ tailWord_5817957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5817970 : List Nat := [3, 2, 1, 2, 3, 2, 1, 2, 1, 2, 4]
def baseStart_5817970 : Nat := 118140960795 + 5817970 * 2 ^ 59
def prefixEnd_5817970 : Nat := 4983230072969 + 3 ^ 40 * 5817970 * 2
def baseEnd_5817970 : Nat := 2987415043438707399318649

theorem tailTrace_5817970 : CollatzResearch.WordTrace tailWord_5817970 prefixEnd_5817970 2987415043438707399318649 := by
  unfold tailWord_5817970
  simp only [CollatzResearch.WordTrace]
  refine ⟨53049699683123948753542841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141465865821663863342780909 53049699683123948753542841)
  ·
    refine ⟨39787274762342961565157131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53049699683123948753542841 39787274762342961565157131)
    ·
      refine ⟨59680912143514442347735697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39787274762342961565157131 59680912143514442347735697)
      ·
        refine ⟨44760684107635831760801773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59680912143514442347735697 44760684107635831760801773)
        ·
          refine ⟨16785256540363436910300665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44760684107635831760801773 16785256540363436910300665)
          ·
            refine ⟨12588942405272577682725499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16785256540363436910300665 12588942405272577682725499)
            ·
              refine ⟨18883413607908866524088249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12588942405272577682725499 18883413607908866524088249)
              ·
                refine ⟨14162560205931649893066187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18883413607908866524088249 14162560205931649893066187)
                ·
                  refine ⟨21243840308897474839599281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14162560205931649893066187 21243840308897474839599281)
                  ·
                    refine ⟨15932880231673106129699461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21243840308897474839599281 15932880231673106129699461)
                    ·
                      refine ⟨2987415043438707399318649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15932880231673106129699461 2987415043438707399318649)
                      ·
                        rfl

theorem cell23_5817970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 2, 1, 2, 4].length) (baseStart_5817970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5817970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5817970 prefixEnd_5817970 := by exact prefixLift 5817970
  have htrace : WordTrace (prefixWord ++ tailWord_5817970) baseStart_5817970 baseEnd_5817970 := by
    simpa [prefixWord, tailWord_5817970, baseEnd_5817970] using wordTrace_append hprefix tailTrace_5817970
  have hstable : (prefixWord ++ tailWord_5817970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5817970).length < 2 ^ (prefixWord ++ tailWord_5817970).sum := by decide
  have hdescent : baseEnd_5817970 < baseStart_5817970 := by decide
  rcases family_descends (prefixWord ++ tailWord_5817970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5817974 : List Nat := [5, 1, 1, 2, 2, 2, 3, 1, 1, 1, 4]
def baseStart_5817974 : Nat := 118140960795 + 5817974 * 2 ^ 59
def prefixEnd_5817974 : Nat := 4983230072969 + 3 ^ 40 * 5817974 * 2
def baseEnd_5817974 : Nat := 2987417097361325383668631

theorem tailTrace_5817974 : CollatzResearch.WordTrace tailWord_5817974 prefixEnd_5817974 2987417097361325383668631 := by
  unfold tailWord_5817974
  simp only [CollatzResearch.WordTrace]
  refine ⟨13262434039030081481082311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 141465963082987535798211317 13262434039030081481082311)
  ·
    refine ⟨19893651058545122221623467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13262434039030081481082311 19893651058545122221623467)
    ·
      refine ⟨29840476587817683332435201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19893651058545122221623467 29840476587817683332435201)
      ·
        refine ⟨22380357440863262499326401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29840476587817683332435201 22380357440863262499326401)
        ·
          refine ⟨16785268080647446874494801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22380357440863262499326401 16785268080647446874494801)
          ·
            refine ⟨12588951060485585155871101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16785268080647446874494801 12588951060485585155871101)
            ·
              refine ⟨4720856647682094433451663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12588951060485585155871101 4720856647682094433451663)
              ·
                refine ⟨7081284971523141650177495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4720856647682094433451663 7081284971523141650177495)
                ·
                  refine ⟨10621927457284712475266243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7081284971523141650177495 10621927457284712475266243)
                  ·
                    refine ⟨15932891185927068712899365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10621927457284712475266243 15932891185927068712899365)
                    ·
                      refine ⟨2987417097361325383668631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15932891185927068712899365 2987417097361325383668631)
                      ·
                        rfl

theorem cell23_5817974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 3, 1, 1, 1, 4].length) (baseStart_5817974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5817974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5817974 prefixEnd_5817974 := by exact prefixLift 5817974
  have htrace : WordTrace (prefixWord ++ tailWord_5817974) baseStart_5817974 baseEnd_5817974 := by
    simpa [prefixWord, tailWord_5817974, baseEnd_5817974] using wordTrace_append hprefix tailTrace_5817974
  have hstable : (prefixWord ++ tailWord_5817974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5817974).length < 2 ^ (prefixWord ++ tailWord_5817974).sum := by decide
  have hdescent : baseEnd_5817974 < baseStart_5817974 := by decide
  rcases family_descends (prefixWord ++ tailWord_5817974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5817976 : List Nat := [2, 1, 2, 1, 1, 1, 2, 1, 3, 9]
def baseStart_5817976 : Nat := 118140960795 + 5817976 * 2 ^ 59
def prefixEnd_5817976 : Nat := 4983230072969 + 3 ^ 40 * 5817976 * 2
def baseEnd_5817976 : Nat := 995806041440878125281207

theorem tailTrace_5817976 : CollatzResearch.WordTrace tailWord_5817976 prefixEnd_5817976 995806041440878125281207 := by
  unfold tailWord_5817976
  simp only [CollatzResearch.WordTrace]
  refine ⟨106099508785237029019444891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141466011713649372025926521 106099508785237029019444891)
  ·
    refine ⟨159149263177855543529167337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106099508785237029019444891 159149263177855543529167337)
    ·
      refine ⟨119361947383391657646875503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159149263177855543529167337 119361947383391657646875503)
      ·
        refine ⟨179042921075087486470313255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119361947383391657646875503 179042921075087486470313255)
        ·
          refine ⟨268564381612631229705469883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179042921075087486470313255 268564381612631229705469883)
          ·
            refine ⟨402846572418946844558204825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 268564381612631229705469883 402846572418946844558204825)
            ·
              refine ⟨302134929314210133418653619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 402846572418946844558204825 302134929314210133418653619)
              ·
                refine ⟨453202393971315200127980429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 302134929314210133418653619 453202393971315200127980429)
                ·
                  refine ⟨169950897739243200047992661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 453202393971315200127980429 169950897739243200047992661)
                  ·
                    refine ⟨995806041440878125281207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 169950897739243200047992661 995806041440878125281207)
                    ·
                      rfl

theorem cell23_5817976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 3, 9].length) (baseStart_5817976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5817976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5817976 prefixEnd_5817976 := by exact prefixLift 5817976
  have htrace : WordTrace (prefixWord ++ tailWord_5817976) baseStart_5817976 baseEnd_5817976 := by
    simpa [prefixWord, tailWord_5817976, baseEnd_5817976] using wordTrace_append hprefix tailTrace_5817976
  have hstable : (prefixWord ++ tailWord_5817976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5817976).length < 2 ^ (prefixWord ++ tailWord_5817976).sum := by decide
  have hdescent : baseEnd_5817976 < baseStart_5817976 := by decide
  rcases family_descends (prefixWord ++ tailWord_5817976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5817977 : List Nat := [1, 2, 1, 3, 3, 1, 5, 1, 1, 2, 3]
def baseStart_5817977 : Nat := 118140960795 + 5817977 * 2 ^ 59
def prefixEnd_5817977 : Nat := 4983230072969 + 3 ^ 40 * 5817977 * 2
def baseEnd_5817977 : Nat := 2987418637803288871931117

theorem tailTrace_5817977 : CollatzResearch.WordTrace tailWord_5817977 prefixEnd_5817977 2987418637803288871931117 := by
  unfold tailWord_5817977
  simp only [CollatzResearch.WordTrace]
  refine ⟨212199054043470435209676185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141466036028980290139784123 212199054043470435209676185)
  ·
    refine ⟨159149290532602826407257139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212199054043470435209676185 159149290532602826407257139)
    ·
      refine ⟨238723935798904239610885709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159149290532602826407257139 238723935798904239610885709)
      ·
        refine ⟨89521475924589089854082141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 238723935798904239610885709 89521475924589089854082141)
        ·
          refine ⟨33570553471720908695280803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89521475924589089854082141 33570553471720908695280803)
          ·
            refine ⟨50355830207581363042921205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33570553471720908695280803 50355830207581363042921205)
            ·
              refine ⟨4720859081960752785273863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50355830207581363042921205 4720859081960752785273863)
              ·
                refine ⟨7081288622941129177910795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4720859081960752785273863 7081288622941129177910795)
                ·
                  refine ⟨10621932934411693766866193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7081288622941129177910795 10621932934411693766866193)
                  ·
                    refine ⟨7966449700808770325149645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10621932934411693766866193 7966449700808770325149645)
                    ·
                      refine ⟨2987418637803288871931117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7966449700808770325149645 2987418637803288871931117)
                      ·
                        rfl

theorem cell23_5817977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 5, 1, 1, 2, 3].length) (baseStart_5817977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5817977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5817977 prefixEnd_5817977 := by exact prefixLift 5817977
  have htrace : WordTrace (prefixWord ++ tailWord_5817977) baseStart_5817977 baseEnd_5817977 := by
    simpa [prefixWord, tailWord_5817977, baseEnd_5817977] using wordTrace_append hprefix tailTrace_5817977
  have hstable : (prefixWord ++ tailWord_5817977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5817977).length < 2 ^ (prefixWord ++ tailWord_5817977).sum := by decide
  have hdescent : baseEnd_5817977 < baseStart_5817977 := by decide
  rcases family_descends (prefixWord ++ tailWord_5817977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5817991 : List Nat := [1, 1, 4, 2, 1, 3, 4, 2, 1, 2, 2]
def baseStart_5817991 : Nat := 118140960795 + 5817991 * 2 ^ 59
def prefixEnd_5817991 : Nat := 4983230072969 + 3 ^ 40 * 5817991 * 2
def baseEnd_5817991 : Nat := 2987425826532451817156053

theorem tailTrace_5817991 : CollatzResearch.WordTrace tailWord_5817991 prefixEnd_5817991 2987425826532451817156053 := by
  unfold tailWord_5817991
  simp only [CollatzResearch.WordTrace]
  refine ⟨212199564665419715600685827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141466376443613143733790551 212199564665419715600685827)
  ·
    refine ⟨318299346998129573401028741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212199564665419715600685827 318299346998129573401028741)
    ·
      refine ⟨59681127562149295012692889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 318299346998129573401028741 59681127562149295012692889)
      ·
        refine ⟨44760845671611971259519667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59681127562149295012692889 44760845671611971259519667)
        ·
          refine ⟨67141268507417956889279501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44760845671611971259519667 67141268507417956889279501)
          ·
            refine ⟨25177975690281733833479813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67141268507417956889279501 25177975690281733833479813)
            ·
              refine ⟨4720870441927825093777465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25177975690281733833479813 4720870441927825093777465)
              ·
                refine ⟨3540652831445868820333099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4720870441927825093777465 3540652831445868820333099)
                ·
                  refine ⟨5310979247168803230499649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3540652831445868820333099 5310979247168803230499649)
                  ·
                    refine ⟨3983234435376602422874737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5310979247168803230499649 3983234435376602422874737)
                    ·
                      refine ⟨2987425826532451817156053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3983234435376602422874737 2987425826532451817156053)
                      ·
                        rfl

theorem cell23_5817991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 4, 2, 1, 2, 2].length) (baseStart_5817991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5817991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5817991 prefixEnd_5817991 := by exact prefixLift 5817991
  have htrace : WordTrace (prefixWord ++ tailWord_5817991) baseStart_5817991 baseEnd_5817991 := by
    simpa [prefixWord, tailWord_5817991, baseEnd_5817991] using wordTrace_append hprefix tailTrace_5817991
  have hstable : (prefixWord ++ tailWord_5817991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5817991).length < 2 ^ (prefixWord ++ tailWord_5817991).sum := by decide
  have hdescent : baseEnd_5817991 < baseStart_5817991 := by decide
  rcases family_descends (prefixWord ++ tailWord_5817991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5818007 : List Nat := [1, 1, 3, 3, 2, 2, 2, 3, 2, 1, 3]
def baseStart_5818007 : Nat := 118140960795 + 5818007 * 2 ^ 59
def prefixEnd_5818007 : Nat := 4983230072969 + 3 ^ 40 * 5818007 * 2
def baseEnd_5818007 : Nat := 2987434042222923754555979

theorem tailTrace_5818007 : CollatzResearch.WordTrace tailWord_5818007 prefixEnd_5818007 2987434042222923754555979 := by
  unfold tailWord_5818007
  simp only [CollatzResearch.WordTrace]
  refine ⟨212200148233361750333268275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141466765488907833555512183 212200148233361750333268275)
  ·
    refine ⟨318300222350042625499902413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212200148233361750333268275 318300222350042625499902413)
    ·
      refine ⟨119362583381265984562463405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 318300222350042625499902413 119362583381265984562463405)
      ·
        refine ⟨44760968767974744210923777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119362583381265984562463405 44760968767974744210923777)
        ·
          refine ⟨33570726575981058158192833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44760968767974744210923777 33570726575981058158192833)
          ·
            refine ⟨25178044931985793618644625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33570726575981058158192833 25178044931985793618644625)
            ·
              refine ⟨18883533698989345213983469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25178044931985793618644625 18883533698989345213983469)
              ·
                refine ⟨7081325137121004455243801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18883533698989345213983469 7081325137121004455243801)
                ·
                  refine ⟨5310993852840753341432851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7081325137121004455243801 5310993852840753341432851)
                  ·
                    refine ⟨7966490779261130012149277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5310993852840753341432851 7966490779261130012149277)
                    ·
                      refine ⟨2987434042222923754555979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7966490779261130012149277 2987434042222923754555979)
                      ·
                        rfl

theorem cell23_5818007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 3, 2, 1, 3].length) (baseStart_5818007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5818007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5818007 prefixEnd_5818007 := by exact prefixLift 5818007
  have htrace : WordTrace (prefixWord ++ tailWord_5818007) baseStart_5818007 baseEnd_5818007 := by
    simpa [prefixWord, tailWord_5818007, baseEnd_5818007] using wordTrace_append hprefix tailTrace_5818007
  have hstable : (prefixWord ++ tailWord_5818007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5818007).length < 2 ^ (prefixWord ++ tailWord_5818007).sum := by decide
  have hdescent : baseEnd_5818007 < baseStart_5818007 := by decide
  rcases family_descends (prefixWord ++ tailWord_5818007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5818013 : List Nat := [1, 4, 2, 1, 1, 1, 1, 1, 4, 3, 4]
def baseStart_5818013 : Nat := 118140960795 + 5818013 * 2 ^ 59
def prefixEnd_5818013 : Nat := 4983230072969 + 3 ^ 40 * 5818013 * 2
def baseEnd_5818013 : Nat := 2987437123106850731080951

theorem tailTrace_5818013 : CollatzResearch.WordTrace tailWord_5818013 prefixEnd_5818013 2987437123106850731080951 := by
  unfold tailWord_5818013
  simp only [CollatzResearch.WordTrace]
  refine ⟨212200367071340013357986693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141466911380893342238657795 212200367071340013357986693)
  ·
    refine ⟨39787568825876252504622505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 212200367071340013357986693 39787568825876252504622505)
    ·
      refine ⟨29840676619407189378466879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39787568825876252504622505 29840676619407189378466879)
      ·
        refine ⟨44761014929110784067700319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29840676619407189378466879 44761014929110784067700319)
        ·
          refine ⟨67141522393666176101550479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44761014929110784067700319 67141522393666176101550479)
          ·
            refine ⟨100712283590499264152325719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67141522393666176101550479 100712283590499264152325719)
            ·
              refine ⟨151068425385748896228488579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100712283590499264152325719 151068425385748896228488579)
              ·
                refine ⟨226602638078623344342732869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 151068425385748896228488579 226602638078623344342732869)
                ·
                  refine ⟨42487994639741877064262413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 226602638078623344342732869 42487994639741877064262413)
                  ·
                    refine ⟨15932997989903203899098405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42487994639741877064262413 15932997989903203899098405)
                    ·
                      refine ⟨2987437123106850731080951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15932997989903203899098405 2987437123106850731080951)
                      ·
                        rfl

theorem cell23_5818013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 4, 3, 4].length) (baseStart_5818013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5818013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5818013 prefixEnd_5818013 := by exact prefixLift 5818013
  have htrace : WordTrace (prefixWord ++ tailWord_5818013) baseStart_5818013 baseEnd_5818013 := by
    simpa [prefixWord, tailWord_5818013, baseEnd_5818013] using wordTrace_append hprefix tailTrace_5818013
  have hstable : (prefixWord ++ tailWord_5818013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5818013).length < 2 ^ (prefixWord ++ tailWord_5818013).sum := by decide
  have hdescent : baseEnd_5818013 < baseStart_5818013 := by decide
  rcases family_descends (prefixWord ++ tailWord_5818013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5818017 : List Nat := [1, 2, 3, 3, 2, 1, 2, 1, 3, 3, 2]
def baseStart_5818017 : Nat := 118140960795 + 5818017 * 2 ^ 59
def prefixEnd_5818017 : Nat := 4983230072969 + 3 ^ 40 * 5818017 * 2
def baseEnd_5818017 : Nat := 2987439177029468715430933

theorem tailTrace_5818017 : CollatzResearch.WordTrace tailWord_5818017 prefixEnd_5818017 2987439177029468715430933 := by
  unfold tailWord_5818017
  simp only [CollatzResearch.WordTrace]
  refine ⟨212200512963325522041132305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141467008642217014694088203 212200512963325522041132305)
  ·
    refine ⟨159150384722494141530849229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212200512963325522041132305 159150384722494141530849229)
    ·
      refine ⟨59681394270935303074068461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 159150384722494141530849229 59681394270935303074068461)
      ·
        refine ⟨22380522851600738652775673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59681394270935303074068461 22380522851600738652775673)
        ·
          refine ⟨16785392138700553989581755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22380522851600738652775673 16785392138700553989581755)
          ·
            refine ⟨25178088208050830984372633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16785392138700553989581755 25178088208050830984372633)
            ·
              refine ⟨18883566156038123238279475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25178088208050830984372633 18883566156038123238279475)
              ·
                refine ⟨28325349234057184857419213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18883566156038123238279475 28325349234057184857419213)
                ·
                  refine ⟨10622005962771444321532205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28325349234057184857419213 10622005962771444321532205)
                  ·
                    refine ⟨3983252236039291620574577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10622005962771444321532205 3983252236039291620574577)
                    ·
                      refine ⟨2987439177029468715430933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3983252236039291620574577 2987439177029468715430933)
                      ·
                        rfl

theorem cell23_5818017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 1, 3, 3, 2].length) (baseStart_5818017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5818017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5818017 prefixEnd_5818017 := by exact prefixLift 5818017
  have htrace : WordTrace (prefixWord ++ tailWord_5818017) baseStart_5818017 baseEnd_5818017 := by
    simpa [prefixWord, tailWord_5818017, baseEnd_5818017] using wordTrace_append hprefix tailTrace_5818017
  have hstable : (prefixWord ++ tailWord_5818017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5818017).length < 2 ^ (prefixWord ++ tailWord_5818017).sum := by decide
  have hdescent : baseEnd_5818017 < baseStart_5818017 := by decide
  rcases family_descends (prefixWord ++ tailWord_5818017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5818034 : List Nat := [3, 2, 1, 1, 1, 2, 6, 1, 1, 3, 2]
def baseStart_5818034 : Nat := 118140960795 + 5818034 * 2 ^ 59
def prefixEnd_5818034 : Nat := 4983230072969 + 3 ^ 40 * 5818034 * 2
def baseEnd_5818034 : Nat := 2987447906200595148918355

theorem tailTrace_5818034 : CollatzResearch.WordTrace tailWord_5818034 prefixEnd_5818034 2987447906200595148918355 := by
  unfold tailWord_5818034
  simp only [CollatzResearch.WordTrace]
  refine ⟨53050283251065983486125289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141467422002842622629667437 53050283251065983486125289)
  ·
    refine ⟨39787712438299487614593967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53050283251065983486125289 39787712438299487614593967)
    ·
      refine ⟨59681568657449231421890951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39787712438299487614593967 59681568657449231421890951)
      ·
        refine ⟨89522352986173847132836427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59681568657449231421890951 89522352986173847132836427)
        ·
          refine ⟨134283529479260770699254641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89522352986173847132836427 134283529479260770699254641)
          ·
            refine ⟨100712647109445578024440981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134283529479260770699254641 100712647109445578024440981)
            ·
              refine ⟨4720905333255261469895671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 100712647109445578024440981 4720905333255261469895671)
              ·
                refine ⟨7081357999882892204843507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4720905333255261469895671 7081357999882892204843507)
                ·
                  refine ⟨10622036999824338307265261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7081357999882892204843507 10622036999824338307265261)
                  ·
                    refine ⟨3983263874934126865224473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10622036999824338307265261 3983263874934126865224473)
                    ·
                      refine ⟨2987447906200595148918355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3983263874934126865224473 2987447906200595148918355)
                      ·
                        rfl

theorem cell23_5818034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 6, 1, 1, 3, 2].length) (baseStart_5818034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5818034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5818034 prefixEnd_5818034 := by exact prefixLift 5818034
  have htrace : WordTrace (prefixWord ++ tailWord_5818034) baseStart_5818034 baseEnd_5818034 := by
    simpa [prefixWord, tailWord_5818034, baseEnd_5818034] using wordTrace_append hprefix tailTrace_5818034
  have hstable : (prefixWord ++ tailWord_5818034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5818034).length < 2 ^ (prefixWord ++ tailWord_5818034).sum := by decide
  have hdescent : baseEnd_5818034 < baseStart_5818034 := by decide
  rcases family_descends (prefixWord ++ tailWord_5818034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5818047 : List Nat := [1, 1, 2, 2, 2, 3, 3, 1, 4, 2, 2]
def baseStart_5818047 : Nat := 118140960795 + 5818047 * 2 ^ 59
def prefixEnd_5818047 : Nat := 4983230072969 + 3 ^ 40 * 5818047 * 2
def baseEnd_5818047 : Nat := 2987454581449103598055795

theorem tailTrace_5818047 : CollatzResearch.WordTrace tailWord_5818047 prefixEnd_5818047 2987454581449103598055795 := by
  unfold tailWord_5818047
  simp only [CollatzResearch.WordTrace]
  refine ⟨212201607153216837164724395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141467738102144558109816263 212201607153216837164724395)
  ·
    refine ⟨318302410729825255747086593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212201607153216837164724395 318302410729825255747086593)
    ·
      refine ⟨238726808047368941810314945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 318302410729825255747086593 238726808047368941810314945)
      ·
        refine ⟨179045106035526706357736209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 238726808047368941810314945 179045106035526706357736209)
        ·
          refine ⟨134283829526645029768302157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179045106035526706357736209 134283829526645029768302157)
          ·
            refine ⟨50356436072491886163113309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 134283829526645029768302157 50356436072491886163113309)
            ·
              refine ⟨18883663527184457311167491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50356436072491886163113309 18883663527184457311167491)
              ·
                refine ⟨28325495290776685966751237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18883663527184457311167491 28325495290776685966751237)
                ·
                  refine ⟨5311030367020628618765857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28325495290776685966751237 5311030367020628618765857)
                  ·
                    refine ⟨3983272775265471464074393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5311030367020628618765857 3983272775265471464074393)
                    ·
                      refine ⟨2987454581449103598055795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3983272775265471464074393 2987454581449103598055795)
                      ·
                        rfl

theorem cell23_5818047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 1, 4, 2, 2].length) (baseStart_5818047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5818047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5818047 prefixEnd_5818047 := by exact prefixLift 5818047
  have htrace : WordTrace (prefixWord ++ tailWord_5818047) baseStart_5818047 baseEnd_5818047 := by
    simpa [prefixWord, tailWord_5818047, baseEnd_5818047] using wordTrace_append hprefix tailTrace_5818047
  have hstable : (prefixWord ++ tailWord_5818047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5818047).length < 2 ^ (prefixWord ++ tailWord_5818047).sum := by decide
  have hdescent : baseEnd_5818047 < baseStart_5818047 := by decide
  rcases family_descends (prefixWord ++ tailWord_5818047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5818120 : List Nat := [2, 1, 3, 2, 2, 1, 1, 2, 4, 1, 4]
def baseStart_5818120 : Nat := 118140960795 + 5818120 * 2 ^ 59
def prefixEnd_5818120 : Nat := 4983230072969 + 3 ^ 40 * 5818120 * 2
def baseEnd_5818120 : Nat := 2987492065536881812442959

theorem tailTrace_5818120 : CollatzResearch.WordTrace tailWord_5818120 prefixEnd_5818120 2987492065536881812442959 := by
  unfold tailWord_5818120
  simp only [CollatzResearch.WordTrace]
  refine ⟨106102134840976185316065907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141469513121301580421421209 106102134840976185316065907)
  ·
    refine ⟨159153202261464277974098861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106102134840976185316065907 159153202261464277974098861)
    ·
      refine ⟨59682450848049104240287073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 159153202261464277974098861 59682450848049104240287073)
      ·
        refine ⟨44761838136036828180215305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59682450848049104240287073 44761838136036828180215305)
        ·
          refine ⟨33571378602027621135161479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44761838136036828180215305 33571378602027621135161479)
          ·
            refine ⟨50357067903041431702742219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33571378602027621135161479 50357067903041431702742219)
            ·
              refine ⟨75535601854562147554113329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50357067903041431702742219 75535601854562147554113329)
              ·
                refine ⟨56651701390921610665584997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75535601854562147554113329 56651701390921610665584997)
                ·
                  refine ⟨10622194010797801999797187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56651701390921610665584997 10622194010797801999797187)
                  ·
                    refine ⟨15933291016196702999695781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10622194010797801999797187 15933291016196702999695781)
                    ·
                      refine ⟨2987492065536881812442959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15933291016196702999695781 2987492065536881812442959)
                      ·
                        rfl

theorem cell23_5818120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 2, 4, 1, 4].length) (baseStart_5818120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5818120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5818120 prefixEnd_5818120 := by exact prefixLift 5818120
  have htrace : WordTrace (prefixWord ++ tailWord_5818120) baseStart_5818120 baseEnd_5818120 := by
    simpa [prefixWord, tailWord_5818120, baseEnd_5818120] using wordTrace_append hprefix tailTrace_5818120
  have hstable : (prefixWord ++ tailWord_5818120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5818120).length < 2 ^ (prefixWord ++ tailWord_5818120).sum := by decide
  have hdescent : baseEnd_5818120 < baseStart_5818120 := by decide
  rcases family_descends (prefixWord ++ tailWord_5818120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5818207 : List Nat := [1, 1, 2, 3, 1, 5, 1, 3, 1, 5]
def baseStart_5818207 : Nat := 118140960795 + 5818207 * 2 ^ 59
def prefixEnd_5818207 : Nat := 4983230072969 + 3 ^ 40 * 5818207 * 2
def baseEnd_5818207 : Nat := 995845579451274324018353

theorem tailTrace_5818207 : CollatzResearch.WordTrace tailWord_5818207 prefixEnd_5818207 995845579451274324018353 := by
  unfold tailWord_5818207
  simp only [CollatzResearch.WordTrace]
  refine ⟨212207442832637184490548875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141471628555091456327032583 212207442832637184490548875)
  ·
    refine ⟨318311164248955776735823313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212207442832637184490548875 318311164248955776735823313)
    ·
      refine ⟨238733373186716832551867485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 318311164248955776735823313 238733373186716832551867485)
      ·
        refine ⟨89525014945018812206950307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 238733373186716832551867485 89525014945018812206950307)
        ·
          refine ⟨134287522417528218310425461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89525014945018812206950307 134287522417528218310425461)
          ·
            refine ⟨12589455226643270466602387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 134287522417528218310425461 12589455226643270466602387)
            ·
              refine ⟨18884182839964905699903581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12589455226643270466602387 18884182839964905699903581)
              ·
                refine ⟨7081568564986839637463843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18884182839964905699903581 7081568564986839637463843)
                ·
                  refine ⟨10622352847480259456195765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7081568564986839637463843 10622352847480259456195765)
                  ·
                    refine ⟨995845579451274324018353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10622352847480259456195765 995845579451274324018353)
                    ·
                      rfl

theorem cell23_5818207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 3, 1, 5].length) (baseStart_5818207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5818207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5818207 prefixEnd_5818207 := by exact prefixLift 5818207
  have htrace : WordTrace (prefixWord ++ tailWord_5818207) baseStart_5818207 baseEnd_5818207 := by
    simpa [prefixWord, tailWord_5818207, baseEnd_5818207] using wordTrace_append hprefix tailTrace_5818207
  have hstable : (prefixWord ++ tailWord_5818207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5818207).length < 2 ^ (prefixWord ++ tailWord_5818207).sum := by decide
  have hdescent : baseEnd_5818207 < baseStart_5818207 := by decide
  rcases family_descends (prefixWord ++ tailWord_5818207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5818221 : List Nat := [1, 5, 1, 1, 1, 1, 4, 4, 1, 1, 3]
def baseStart_5818221 : Nat := 118140960795 + 5818221 * 2 ^ 59
def prefixEnd_5818221 : Nat := 4983230072969 + 3 ^ 40 * 5818221 * 2
def baseEnd_5818221 : Nat := 2987543927082985917279995

theorem tailTrace_5818221 : CollatzResearch.WordTrace tailWord_5818221 prefixEnd_5818221 2987543927082985917279995 := by
  unfold tailWord_5818221
  simp only [CollatzResearch.WordTrace]
  refine ⟨212207953454586464881558517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141471968969724309921039011 212207953454586464881558517)
  ·
    refine ⟨19894495636367481082646111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 212207953454586464881558517 19894495636367481082646111)
    ·
      refine ⟨29841743454551221623969167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19894495636367481082646111 29841743454551221623969167)
      ·
        refine ⟨44762615181826832435953751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29841743454551221623969167 44762615181826832435953751)
        ·
          refine ⟨67143922772740248653930627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44762615181826832435953751 67143922772740248653930627)
          ·
            refine ⟨100715884159110372980895941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67143922772740248653930627 100715884159110372980895941)
            ·
              refine ⟨18884228279833194933917989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 100715884159110372980895941 18884228279833194933917989)
              ·
                refine ⟨3540792802468724050109623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18884228279833194933917989 3540792802468724050109623)
                ·
                  refine ⟨5311189203703086075164435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3540792802468724050109623 5311189203703086075164435)
                  ·
                    refine ⟨7966783805554629112746653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5311189203703086075164435 7966783805554629112746653)
                    ·
                      refine ⟨2987543927082985917279995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7966783805554629112746653 2987543927082985917279995)
                      ·
                        rfl

theorem cell23_5818221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 4, 1, 1, 3].length) (baseStart_5818221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5818221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5818221 prefixEnd_5818221 := by exact prefixLift 5818221
  have htrace : WordTrace (prefixWord ++ tailWord_5818221) baseStart_5818221 baseEnd_5818221 := by
    simpa [prefixWord, tailWord_5818221, baseEnd_5818221] using wordTrace_append hprefix tailTrace_5818221
  have hstable : (prefixWord ++ tailWord_5818221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5818221).length < 2 ^ (prefixWord ++ tailWord_5818221).sum := by decide
  have hdescent : baseEnd_5818221 < baseStart_5818221 := by decide
  rcases family_descends (prefixWord ++ tailWord_5818221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5818240 : List Nat := [2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 6]
def baseStart_5818240 : Nat := 118140960795 + 5818240 * 2 ^ 59
def prefixEnd_5818240 : Nat := 4983230072969 + 3 ^ 40 * 5818240 * 2
def baseEnd_5818240 : Nat := 2987553683215421342942407

theorem tailTrace_5818240 : CollatzResearch.WordTrace tailWord_5818240 prefixEnd_5818240 2987553683215421342942407 := by
  unfold tailWord_5818240
  simp only [CollatzResearch.WordTrace]
  refine ⟨106104323220758815563250087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141472430961011754084333449 106104323220758815563250087)
  ·
    refine ⟨159156484831138223344875131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106104323220758815563250087 159156484831138223344875131)
    ·
      refine ⟨238734727246707335017312697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159156484831138223344875131 238734727246707335017312697)
      ·
        refine ⟨179051045435030501262984523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 238734727246707335017312697 179051045435030501262984523)
        ·
          refine ⟨268576568152545751894476785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179051045435030501262984523 268576568152545751894476785)
          ·
            refine ⟨201432426114409313920857589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 268576568152545751894476785 201432426114409313920857589)
            ·
              refine ⟨18884289948225873180080399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 201432426114409313920857589 18884289948225873180080399)
              ·
                refine ⟨28326434922338809770120599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18884289948225873180080399 28326434922338809770120599)
                ·
                  refine ⟨42489652383508214655180899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28326434922338809770120599 42489652383508214655180899)
                  ·
                    refine ⟨63734478575262321982771349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42489652383508214655180899 63734478575262321982771349)
                    ·
                      refine ⟨2987553683215421342942407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63734478575262321982771349 2987553683215421342942407)
                      ·
                        rfl

theorem cell23_5818240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 6].length) (baseStart_5818240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5818240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5818240 prefixEnd_5818240 := by exact prefixLift 5818240
  have htrace : WordTrace (prefixWord ++ tailWord_5818240) baseStart_5818240 baseEnd_5818240 := by
    simpa [prefixWord, tailWord_5818240, baseEnd_5818240] using wordTrace_append hprefix tailTrace_5818240
  have hstable : (prefixWord ++ tailWord_5818240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5818240).length < 2 ^ (prefixWord ++ tailWord_5818240).sum := by decide
  have hdescent : baseEnd_5818240 < baseStart_5818240 := by decide
  rcases family_descends (prefixWord ++ tailWord_5818240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5818241 : List Nat := [1, 2, 4, 4, 1, 1, 2, 2, 1, 5]
def baseStart_5818241 : Nat := 118140960795 + 5818241 * 2 ^ 59
def prefixEnd_5818241 : Nat := 4983230072969 + 3 ^ 40 * 5818241 * 2
def baseEnd_5818241 : Nat := 995851398898691946343301

theorem tailTrace_5818241 : CollatzResearch.WordTrace tailWord_5818241 prefixEnd_5818241 995851398898691946343301 := by
  unfold tailWord_5818241
  simp only [CollatzResearch.WordTrace]
  refine ⟨212208682914514008297286577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141472455276342672198191051 212208682914514008297286577)
  ·
    refine ⟨159156512185885506222964933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212208682914514008297286577 159156512185885506222964933)
    ·
      refine ⟨29841846034853532416805925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 159156512185885506222964933 29841846034853532416805925)
      ·
        refine ⟨5595346131535037328151111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29841846034853532416805925 5595346131535037328151111)
        ·
          refine ⟨8393019197302555992226667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5595346131535037328151111 8393019197302555992226667)
          ·
            refine ⟨12589528795953833988340001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8393019197302555992226667 12589528795953833988340001)
            ·
              refine ⟨9442146596965375491255001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12589528795953833988340001 9442146596965375491255001)
              ·
                refine ⟨7081609947724031618441251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9442146596965375491255001 7081609947724031618441251)
                ·
                  refine ⟨10622414921586047427661877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7081609947724031618441251 10622414921586047427661877)
                  ·
                    refine ⟨995851398898691946343301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10622414921586047427661877 995851398898691946343301)
                    ·
                      rfl

theorem cell23_5818241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 2, 2, 1, 5].length) (baseStart_5818241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5818241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5818241 prefixEnd_5818241 := by exact prefixLift 5818241
  have htrace : WordTrace (prefixWord ++ tailWord_5818241) baseStart_5818241 baseEnd_5818241 := by
    simpa [prefixWord, tailWord_5818241, baseEnd_5818241] using wordTrace_append hprefix tailTrace_5818241
  have hstable : (prefixWord ++ tailWord_5818241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5818241).length < 2 ^ (prefixWord ++ tailWord_5818241).sum := by decide
  have hdescent : baseEnd_5818241 < baseStart_5818241 := by decide
  rcases family_descends (prefixWord ++ tailWord_5818241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5818304 : List Nat := [2, 1, 1, 2, 3, 2, 3, 1, 3, 3, 2]
def baseStart_5818304 : Nat := 118140960795 + 5818304 * 2 ^ 59
def prefixEnd_5818304 : Nat := 4983230072969 + 3 ^ 40 * 5818304 * 2
def baseEnd_5818304 : Nat := 2987586545977309092542113

theorem tailTrace_5818304 : CollatzResearch.WordTrace tailWord_5818304 prefixEnd_5818304 2987586545977309092542113 := by
  unfold tailWord_5818304
  simp only [CollatzResearch.WordTrace]
  refine ⟨106105490356642885028414983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141473987142190513371219977 106105490356642885028414983)
  ·
    refine ⟨159158235534964327542622475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106105490356642885028414983 159158235534964327542622475)
    ·
      refine ⟨238737353302446491313933713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159158235534964327542622475 238737353302446491313933713)
      ·
        refine ⟨179053014976834868485450285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 238737353302446491313933713 179053014976834868485450285)
        ·
          refine ⟨67144880616313075682043857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 179053014976834868485450285 67144880616313075682043857)
          ·
            refine ⟨50358660462234806761532893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67144880616313075682043857 50358660462234806761532893)
            ·
              refine ⟨18884497673338052535574835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50358660462234806761532893 18884497673338052535574835)
              ·
                refine ⟨28326746510007078803362253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18884497673338052535574835 28326746510007078803362253)
                ·
                  refine ⟨10622529941252654551260845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28326746510007078803362253 10622529941252654551260845)
                  ·
                    refine ⟨3983448727969745456722817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10622529941252654551260845 3983448727969745456722817)
                    ·
                      refine ⟨2987586545977309092542113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3983448727969745456722817 2987586545977309092542113)
                      ·
                        rfl

theorem cell23_5818304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 1, 3, 3, 2].length) (baseStart_5818304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5818304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5818304 prefixEnd_5818304 := by exact prefixLift 5818304
  have htrace : WordTrace (prefixWord ++ tailWord_5818304) baseStart_5818304 baseEnd_5818304 := by
    simpa [prefixWord, tailWord_5818304, baseEnd_5818304] using wordTrace_append hprefix tailTrace_5818304
  have hstable : (prefixWord ++ tailWord_5818304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5818304).length < 2 ^ (prefixWord ++ tailWord_5818304).sum := by decide
  have hdescent : baseEnd_5818304 < baseStart_5818304 := by decide
  rcases family_descends (prefixWord ++ tailWord_5818304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5818337 : List Nat := [1, 2, 3, 1, 2, 1, 3, 1, 2, 4, 3]
def baseStart_5818337 : Nat := 118140960795 + 5818337 * 2 ^ 59
def prefixEnd_5818337 : Nat := 4983230072969 + 3 ^ 40 * 5818337 * 2
def baseEnd_5818337 : Nat := 2987603490838907463429461

theorem tailTrace_5818337 : CollatzResearch.WordTrace tailWord_5818337 prefixEnd_5818337 2987603490838907463429461 := by
  unfold tailWord_5818337
  simp only [CollatzResearch.WordTrace]
  refine ⟨212212184322166216692781265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141474789548110811128520843 212212184322166216692781265)
  ·
    refine ⟨159159138241624662519585949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212212184322166216692781265 159159138241624662519585949)
    ·
      refine ⟨59684676840609248444844731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 159159138241624662519585949 59684676840609248444844731)
      ·
        refine ⟨89527015260913872667267097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59684676840609248444844731 89527015260913872667267097)
        ·
          refine ⟨67145261445685404500450323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89527015260913872667267097 67145261445685404500450323)
          ·
            refine ⟨100717892168528106750675485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67145261445685404500450323 100717892168528106750675485)
            ·
              refine ⟨37769209563198040031503307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 100717892168528106750675485 37769209563198040031503307)
              ·
                refine ⟨56653814344797060047254961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37769209563198040031503307 56653814344797060047254961)
                ·
                  refine ⟨42490360758597795035441221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56653814344797060047254961 42490360758597795035441221)
                  ·
                    refine ⟨7966942642237086569145229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42490360758597795035441221 7966942642237086569145229)
                    ·
                      refine ⟨2987603490838907463429461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7966942642237086569145229 2987603490838907463429461)
                      ·
                        rfl

theorem cell23_5818337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 1, 2, 4, 3].length) (baseStart_5818337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5818337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5818337 prefixEnd_5818337 := by exact prefixLift 5818337
  have htrace : WordTrace (prefixWord ++ tailWord_5818337) baseStart_5818337 baseEnd_5818337 := by
    simpa [prefixWord, tailWord_5818337, baseEnd_5818337] using wordTrace_append hprefix tailTrace_5818337
  have hstable : (prefixWord ++ tailWord_5818337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5818337).length < 2 ^ (prefixWord ++ tailWord_5818337).sum := by decide
  have hdescent : baseEnd_5818337 < baseStart_5818337 := by decide
  rcases family_descends (prefixWord ++ tailWord_5818337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5818351 : List Nat := [1, 1, 2, 1, 4, 2, 1, 5, 2, 2, 2]
def baseStart_5818351 : Nat := 118140960795 + 5818351 * 2 ^ 59
def prefixEnd_5818351 : Nat := 4983230072969 + 3 ^ 40 * 5818351 * 2
def baseEnd_5818351 : Nat := 2987610679568070408654397

theorem tailTrace_5818351 : CollatzResearch.WordTrace tailWord_5818351 prefixEnd_5818351 2987610679568070408654397 := by
  unfold tailWord_5818351
  simp only [CollatzResearch.WordTrace]
  refine ⟨212212694944115497083790907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141475129962743664722527271 212212694944115497083790907)
  ·
    refine ⟨318319042416173245625686361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212212694944115497083790907 318319042416173245625686361)
    ·
      refine ⟨238739281812129934219264771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 318319042416173245625686361 238739281812129934219264771)
      ·
        refine ⟨358108922718194901328897157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238739281812129934219264771 358108922718194901328897157)
        ·
          refine ⟨67145423009661543999168217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 358108922718194901328897157 67145423009661543999168217)
          ·
            refine ⟨50359067257246157999376163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67145423009661543999168217 50359067257246157999376163)
            ·
              refine ⟨75538600885869236999064245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50359067257246157999376163 75538600885869236999064245)
              ·
                refine ⟨7081743833050240968662273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 75538600885869236999064245 7081743833050240968662273)
                ·
                  refine ⟨5311307874787680726496705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7081743833050240968662273 5311307874787680726496705)
                  ·
                    refine ⟨3983480906090760544872529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5311307874787680726496705 3983480906090760544872529)
                    ·
                      refine ⟨2987610679568070408654397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3983480906090760544872529 2987610679568070408654397)
                      ·
                        rfl

theorem cell23_5818351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 5, 2, 2, 2].length) (baseStart_5818351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5818351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5818351 prefixEnd_5818351 := by exact prefixLift 5818351
  have htrace : WordTrace (prefixWord ++ tailWord_5818351) baseStart_5818351 baseEnd_5818351 := by
    simpa [prefixWord, tailWord_5818351, baseEnd_5818351] using wordTrace_append hprefix tailTrace_5818351
  have hstable : (prefixWord ++ tailWord_5818351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5818351).length < 2 ^ (prefixWord ++ tailWord_5818351).sum := by decide
  have hdescent : baseEnd_5818351 < baseStart_5818351 := by decide
  rcases family_descends (prefixWord ++ tailWord_5818351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5818372 : List Nat := [2, 3, 2, 4, 1, 2, 2, 1, 1, 3, 2]
def baseStart_5818372 : Nat := 118140960795 + 5818372 * 2 ^ 59
def prefixEnd_5818372 : Nat := 4983230072969 + 3 ^ 40 * 5818372 * 2
def baseEnd_5818372 : Nat := 2987621462661814826491801

theorem tailTrace_5818372 : CollatzResearch.WordTrace tailWord_5818372 prefixEnd_5818372 2987621462661814826491801 := by
  unfold tailWord_5818372
  simp only [CollatzResearch.WordTrace]
  refine ⟨106106730438519708835152685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141475640584692945113536913 106106730438519708835152685)
  ·
    refine ⟨39790023914444890813182257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106106730438519708835152685 39790023914444890813182257)
    ·
      refine ⟨29842517935833668109886693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39790023914444890813182257 29842517935833668109886693)
      ·
        refine ⟨5595472112968812770603755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29842517935833668109886693 5595472112968812770603755)
        ·
          refine ⟨8393208169453219155905633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5595472112968812770603755 8393208169453219155905633)
          ·
            refine ⟨6294906127089914366929225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8393208169453219155905633 6294906127089914366929225)
            ·
              refine ⟨4721179595317435775196919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6294906127089914366929225 4721179595317435775196919)
              ·
                refine ⟨7081769392976153662795379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4721179595317435775196919 7081769392976153662795379)
                ·
                  refine ⟨10622654089464230494193069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7081769392976153662795379 10622654089464230494193069)
                  ·
                    refine ⟨3983495283549086435322401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10622654089464230494193069 3983495283549086435322401)
                    ·
                      refine ⟨2987621462661814826491801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3983495283549086435322401 2987621462661814826491801)
                      ·
                        rfl

theorem cell23_5818372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_5818372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5818372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5818372 prefixEnd_5818372 := by exact prefixLift 5818372
  have htrace : WordTrace (prefixWord ++ tailWord_5818372) baseStart_5818372 baseEnd_5818372 := by
    simpa [prefixWord, tailWord_5818372, baseEnd_5818372] using wordTrace_append hprefix tailTrace_5818372
  have hstable : (prefixWord ++ tailWord_5818372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5818372).length < 2 ^ (prefixWord ++ tailWord_5818372).sum := by decide
  have hdescent : baseEnd_5818372 < baseStart_5818372 := by decide
  rcases family_descends (prefixWord ++ tailWord_5818372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5818387 : List Nat := [1, 1, 1, 2, 1, 4, 2, 4, 2, 5]
def baseStart_5818387 : Nat := 118140960795 + 5818387 * 2 ^ 59
def prefixEnd_5818387 : Nat := 4983230072969 + 3 ^ 40 * 5818387 * 2
def baseEnd_5818387 : Nat := 995876388290544089268077

theorem tailTrace_5818387 : CollatzResearch.WordTrace tailWord_5818387 prefixEnd_5818387 995876388290544089268077 := by
  unfold tailWord_5818387
  simp only [CollatzResearch.WordTrace]
  refine ⟨212214007971985075232101415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141476005314656716821400943 212214007971985075232101415)
  ·
    refine ⟨318321011957977612848152123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212214007971985075232101415 318321011957977612848152123)
    ·
      refine ⟨477481517936966419272228185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 318321011957977612848152123 477481517936966419272228185)
      ·
        refine ⟨358111138452724814454171139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 477481517936966419272228185 358111138452724814454171139)
        ·
          refine ⟨537166707679087221681256709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 358111138452724814454171139 537166707679087221681256709)
          ·
            refine ⟨100718757689828854065235633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 537166707679087221681256709 100718757689828854065235633)
            ·
              refine ⟨75539068267371640548926725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100718757689828854065235633 75539068267371640548926725)
              ·
                refine ⟨14163575300132182602923761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 75539068267371640548926725 14163575300132182602923761)
                ·
                  refine ⟨10622681475099136952192821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14163575300132182602923761 10622681475099136952192821)
                  ·
                    refine ⟨995876388290544089268077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10622681475099136952192821 995876388290544089268077)
                    ·
                      rfl

theorem cell23_5818387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 4, 2, 5].length) (baseStart_5818387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5818387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5818387 prefixEnd_5818387 := by exact prefixLift 5818387
  have htrace : WordTrace (prefixWord ++ tailWord_5818387) baseStart_5818387 baseEnd_5818387 := by
    simpa [prefixWord, tailWord_5818387, baseEnd_5818387] using wordTrace_append hprefix tailTrace_5818387
  have hstable : (prefixWord ++ tailWord_5818387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5818387).length < 2 ^ (prefixWord ++ tailWord_5818387).sum := by decide
  have hdescent : baseEnd_5818387 < baseStart_5818387 := by decide
  rcases family_descends (prefixWord ++ tailWord_5818387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5818444 : List Nat := [2, 2, 1, 3, 1, 1, 3, 1, 4, 2, 3]
def baseStart_5818444 : Nat := 118140960795 + 5818444 * 2 ^ 59
def prefixEnd_5818444 : Nat := 4983230072969 + 3 ^ 40 * 5818444 * 2
def baseEnd_5818444 : Nat := 2987658433268938544791469

theorem tailTrace_5818444 : CollatzResearch.WordTrace tailWord_5818444 prefixEnd_5818444 2987658433268938544791469 := by
  unfold tailWord_5818444
  simp only [CollatzResearch.WordTrace]
  refine ⟨106108043466389286983463193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141477391288519049311284257 106108043466389286983463193)
  ·
    refine ⟨79581032599791965237597395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106108043466389286983463193 79581032599791965237597395)
    ·
      refine ⟨119371548899687947856396093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79581032599791965237597395 119371548899687947856396093)
      ·
        refine ⟨44764330837382980446148535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119371548899687947856396093 44764330837382980446148535)
        ·
          refine ⟨67146496256074470669222803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44764330837382980446148535 67146496256074470669222803)
          ·
            refine ⟨100719744384111706003834205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67146496256074470669222803 100719744384111706003834205)
            ·
              refine ⟨37769904144041889751437827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 100719744384111706003834205 37769904144041889751437827)
              ·
                refine ⟨56654856216062834627156741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37769904144041889751437827 56654856216062834627156741)
                ·
                  refine ⟨10622785540511781492591889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56654856216062834627156741 10622785540511781492591889)
                  ·
                    refine ⟨7967089155383836119443917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10622785540511781492591889 7967089155383836119443917)
                    ·
                      refine ⟨2987658433268938544791469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7967089155383836119443917 2987658433268938544791469)
                      ·
                        rfl

theorem cell23_5818444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 1, 4, 2, 3].length) (baseStart_5818444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5818444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5818444 prefixEnd_5818444 := by exact prefixLift 5818444
  have htrace : WordTrace (prefixWord ++ tailWord_5818444) baseStart_5818444 baseEnd_5818444 := by
    simpa [prefixWord, tailWord_5818444, baseEnd_5818444] using wordTrace_append hprefix tailTrace_5818444
  have hstable : (prefixWord ++ tailWord_5818444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5818444).length < 2 ^ (prefixWord ++ tailWord_5818444).sum := by decide
  have hdescent : baseEnd_5818444 < baseStart_5818444 := by decide
  rcases family_descends (prefixWord ++ tailWord_5818444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5818464 : List Nat := [2, 1, 1, 3, 2, 4, 1, 3, 6]
def baseStart_5818464 : Nat := 118140960795 + 5818464 * 2 ^ 59
def prefixEnd_5818464 : Nat := 4983230072969 + 3 ^ 40 * 5818464 * 2
def baseEnd_5818464 : Nat := 331963189209114274060153

theorem tailTrace_5818464 : CollatzResearch.WordTrace tailWord_5818464 prefixEnd_5818464 331963189209114274060153 := by
  unfold tailWord_5818464
  simp only [CollatzResearch.WordTrace]
  refine ⟨106108408196353058691327223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141477877595137411588436297 106108408196353058691327223)
  ·
    refine ⟨159162612294529588036990835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106108408196353058691327223 159162612294529588036990835)
    ·
      refine ⟨238743918441794382055486253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159162612294529588036990835 238743918441794382055486253)
      ·
        refine ⟨89528969415672893270807345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 238743918441794382055486253 89528969415672893270807345)
        ·
          refine ⟨67146727061754669953105509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89528969415672893270807345 67146727061754669953105509)
          ·
            refine ⟨12590011324079000616207283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67146727061754669953105509 12590011324079000616207283)
            ·
              refine ⟨18885016986118500924310925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12590011324079000616207283 18885016986118500924310925)
              ·
                refine ⟨7081881369794437846616597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18885016986118500924310925 7081881369794437846616597)
                ·
                  refine ⟨331963189209114274060153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7081881369794437846616597 331963189209114274060153)
                  ·
                    rfl

theorem cell23_5818464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 3, 6].length) (baseStart_5818464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5818464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5818464 prefixEnd_5818464 := by exact prefixLift 5818464
  have htrace : WordTrace (prefixWord ++ tailWord_5818464) baseStart_5818464 baseEnd_5818464 := by
    simpa [prefixWord, tailWord_5818464, baseEnd_5818464] using wordTrace_append hprefix tailTrace_5818464
  have hstable : (prefixWord ++ tailWord_5818464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5818464).length < 2 ^ (prefixWord ++ tailWord_5818464).sum := by decide
  have hdescent : baseEnd_5818464 < baseStart_5818464 := by decide
  rcases family_descends (prefixWord ++ tailWord_5818464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5818467 : List Nat := [1, 1, 1, 5, 1, 1, 2, 2, 1, 2, 6]
def baseStart_5818467 : Nat := 118140960795 + 5818467 * 2 ^ 59
def prefixEnd_5818467 : Nat := 4983230072969 + 3 ^ 40 * 5818467 * 2
def baseEnd_5818467 : Nat := 2987670243323991954803863

theorem tailTrace_5818467 : CollatzResearch.WordTrace tailWord_5818467 prefixEnd_5818467 2987670243323991954803863 := by
  unfold tailWord_5818467
  simp only [CollatzResearch.WordTrace]
  refine ⟨212216925811695248895013655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141477950541130165930009103 212216925811695248895013655)
  ·
    refine ⟨318325388717542873342520483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212216925811695248895013655 318325388717542873342520483)
    ·
      refine ⟨477488083076314310013780725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 318325388717542873342520483 477488083076314310013780725)
      ·
        refine ⟨44764507788404466563791943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 477488083076314310013780725 44764507788404466563791943)
        ·
          refine ⟨67146761682606699845687915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44764507788404466563791943 67146761682606699845687915)
          ·
            refine ⟨100720142523910049768531873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67146761682606699845687915 100720142523910049768531873)
            ·
              refine ⟨75540106892932537326398905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100720142523910049768531873 75540106892932537326398905)
              ·
                refine ⟨56655080169699402994799179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75540106892932537326398905 56655080169699402994799179)
                ·
                  refine ⟨84982620254549104492198769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56655080169699402994799179 84982620254549104492198769)
                  ·
                    refine ⟨63736965190911828369149077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 84982620254549104492198769 63736965190911828369149077)
                    ·
                      refine ⟨2987670243323991954803863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63736965190911828369149077 2987670243323991954803863)
                      ·
                        rfl

theorem cell23_5818467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 2, 1, 2, 6].length) (baseStart_5818467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5818467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5818467 prefixEnd_5818467 := by exact prefixLift 5818467
  have htrace : WordTrace (prefixWord ++ tailWord_5818467) baseStart_5818467 baseEnd_5818467 := by
    simpa [prefixWord, tailWord_5818467, baseEnd_5818467] using wordTrace_append hprefix tailTrace_5818467
  have hstable : (prefixWord ++ tailWord_5818467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5818467).length < 2 ^ (prefixWord ++ tailWord_5818467).sum := by decide
  have hdescent : baseEnd_5818467 < baseStart_5818467 := by decide
  rcases family_descends (prefixWord ++ tailWord_5818467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5818541 : List Nat := [1, 5, 2, 1, 2, 1, 2, 2, 1, 6]
def baseStart_5818541 : Nat := 118140960795 + 5818541 * 2 ^ 59
def prefixEnd_5818541 : Nat := 4983230072969 + 3 ^ 40 * 5818541 * 2
def baseEnd_5818541 : Nat := 995902746964141555092841

theorem tailTrace_5818541 : CollatzResearch.WordTrace tailWord_5818541 prefixEnd_5818541 995902746964141555092841 := by
  unfold tailWord_5818541
  simp only [CollatzResearch.WordTrace]
  refine ⟨212219624813427159533207477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141479749875618106355471651 212219624813427159533207477)
  ·
    refine ⟨19895589826258796206238201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 212219624813427159533207477 19895589826258796206238201)
    ·
      refine ⟨14921692369694097154678651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19895589826258796206238201 14921692369694097154678651)
      ·
        refine ⟨22382538554541145732017977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14921692369694097154678651 22382538554541145732017977)
        ·
          refine ⟨16786903915905859299013483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22382538554541145732017977 16786903915905859299013483)
          ·
            refine ⟨25180355873858788948520225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16786903915905859299013483 25180355873858788948520225)
            ·
              refine ⟨18885266905394091711390169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25180355873858788948520225 18885266905394091711390169)
              ·
                refine ⟨14163950179045568783542627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18885266905394091711390169 14163950179045568783542627)
                ·
                  refine ⟨21245925268568353175313941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14163950179045568783542627 21245925268568353175313941)
                  ·
                    refine ⟨995902746964141555092841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21245925268568353175313941 995902746964141555092841)
                    ·
                      rfl

theorem cell23_5818541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 2, 1, 6].length) (baseStart_5818541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5818541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5818541 prefixEnd_5818541 := by exact prefixLift 5818541
  have htrace : WordTrace (prefixWord ++ tailWord_5818541) baseStart_5818541 baseEnd_5818541 := by
    simpa [prefixWord, tailWord_5818541, baseEnd_5818541] using wordTrace_append hprefix tailTrace_5818541
  have hstable : (prefixWord ++ tailWord_5818541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5818541).length < 2 ^ (prefixWord ++ tailWord_5818541).sum := by decide
  have hdescent : baseEnd_5818541 < baseStart_5818541 := by decide
  rcases family_descends (prefixWord ++ tailWord_5818541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5818545 : List Nat := [1, 2, 2, 5, 2, 2, 2, 1, 1, 5]
def baseStart_5818545 : Nat := 118140960795 + 5818545 * 2 ^ 59
def prefixEnd_5818545 : Nat := 4983230072969 + 3 ^ 40 * 5818545 * 2
def baseEnd_5818545 : Nat := 995903431605014216542835

theorem tailTrace_5818545 : CollatzResearch.WordTrace tailWord_5818545 prefixEnd_5818545 995903431605014216542835 := by
  unfold tailWord_5818545
  simp only [CollatzResearch.WordTrace]
  refine ⟨212219770705412668216353089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141479847136941778810902059 212219770705412668216353089)
  ·
    refine ⟨159164828029059501162264817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212219770705412668216353089 159164828029059501162264817)
    ·
      refine ⟨119373621021794625871698613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159164828029059501162264817 119373621021794625871698613)
      ·
        refine ⟨11191276970793246175471745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 119373621021794625871698613 11191276970793246175471745)
        ·
          refine ⟨8393457728094934631603809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11191276970793246175471745 8393457728094934631603809)
          ·
            refine ⟨6295093296071200973702857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8393457728094934631603809 6295093296071200973702857)
            ·
              refine ⟨4721319972053400730277143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6295093296071200973702857 4721319972053400730277143)
              ·
                refine ⟨7081979958080101095415715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4721319972053400730277143 7081979958080101095415715)
                ·
                  refine ⟨10622969937120151643123573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7081979958080101095415715 10622969937120151643123573)
                  ·
                    refine ⟨995903431605014216542835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10622969937120151643123573 995903431605014216542835)
                    ·
                      rfl

theorem cell23_5818545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 2, 1, 1, 5].length) (baseStart_5818545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5818545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5818545 prefixEnd_5818545 := by exact prefixLift 5818545
  have htrace : WordTrace (prefixWord ++ tailWord_5818545) baseStart_5818545 baseEnd_5818545 := by
    simpa [prefixWord, tailWord_5818545, baseEnd_5818545] using wordTrace_append hprefix tailTrace_5818545
  have hstable : (prefixWord ++ tailWord_5818545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5818545).length < 2 ^ (prefixWord ++ tailWord_5818545).sum := by decide
  have hdescent : baseEnd_5818545 < baseStart_5818545 := by decide
  rcases family_descends (prefixWord ++ tailWord_5818545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5818558 : List Nat := [4, 2, 1, 1, 4, 1, 1, 1, 4, 4]
def baseStart_5818558 : Nat := 118140960795 + 5818558 * 2 ^ 59
def prefixEnd_5818558 : Nat := 4983230072969 + 3 ^ 40 * 5818558 * 2
def baseEnd_5818558 : Nat := 995905656687850366255315

theorem tailTrace_5818558 : CollatzResearch.WordTrace tailWord_5818558 prefixEnd_5818558 995905656687850366255315 := by
  unfold tailWord_5818558
  simp only [CollatzResearch.WordTrace]
  refine ⟨26527530606795696429572041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 141480163236243714291050885 26527530606795696429572041)
  ·
    refine ⟨19895647955096772322179031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26527530606795696429572041 19895647955096772322179031)
    ·
      refine ⟨29843471932645158483268547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19895647955096772322179031 29843471932645158483268547)
      ·
        refine ⟨44765207898967737724902821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29843471932645158483268547 44765207898967737724902821)
        ·
          refine ⟨8393476481056450823419279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44765207898967737724902821 8393476481056450823419279)
          ·
            refine ⟨12590214721584676235128919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8393476481056450823419279 12590214721584676235128919)
            ·
              refine ⟨18885322082377014352693379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12590214721584676235128919 18885322082377014352693379)
              ·
                refine ⟨28327983123565521529040069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18885322082377014352693379 28327983123565521529040069)
                ·
                  refine ⟨5311496835668535286695013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28327983123565521529040069 5311496835668535286695013)
                  ·
                    refine ⟨995905656687850366255315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5311496835668535286695013 995905656687850366255315)
                    ·
                      rfl

theorem cell23_5818558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 1, 4, 4].length) (baseStart_5818558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5818558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5818558 prefixEnd_5818558 := by exact prefixLift 5818558
  have htrace : WordTrace (prefixWord ++ tailWord_5818558) baseStart_5818558 baseEnd_5818558 := by
    simpa [prefixWord, tailWord_5818558, baseEnd_5818558] using wordTrace_append hprefix tailTrace_5818558
  have hstable : (prefixWord ++ tailWord_5818558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5818558).length < 2 ^ (prefixWord ++ tailWord_5818558).sum := by decide
  have hdescent : baseEnd_5818558 < baseStart_5818558 := by decide
  rcases family_descends (prefixWord ++ tailWord_5818558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5818565 : List Nat := [1, 3, 1, 1, 1, 1, 6, 4, 1, 2, 2]
def baseStart_5818565 : Nat := 118140960795 + 5818565 * 2 ^ 59
def prefixEnd_5818565 : Nat := 4983230072969 + 3 ^ 40 * 5818565 * 2
def baseEnd_5818565 : Nat := 2987720564428132571378413

theorem tailTrace_5818565 : CollatzResearch.WordTrace tailWord_5818565 prefixEnd_5818565 2987720564428132571378413 := by
  unfold tailWord_5818565
  simp only [CollatzResearch.WordTrace]
  refine ⟨212220500165340211632081149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141480333443560141088054099 212220500165340211632081149)
  ·
    refine ⟨79582687562002579362030431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 212220500165340211632081149 79582687562002579362030431)
    ·
      refine ⟨119374031343003869043045647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79582687562002579362030431 119374031343003869043045647)
      ·
        refine ⟨179061047014505803564568471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119374031343003869043045647 179061047014505803564568471)
        ·
          refine ⟨268591570521758705346852707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179061047014505803564568471 268591570521758705346852707)
          ·
            refine ⟨402887355782638058020279061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 268591570521758705346852707 402887355782638058020279061)
            ·
              refine ⟨18885344802311158969700581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 402887355782638058020279061 18885344802311158969700581)
              ·
                refine ⟨3541002150433342306818859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18885344802311158969700581 3541002150433342306818859)
                ·
                  refine ⟨5311503225650013460228289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3541002150433342306818859 5311503225650013460228289)
                  ·
                    refine ⟨3983627419237510095171217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5311503225650013460228289 3983627419237510095171217)
                    ·
                      refine ⟨2987720564428132571378413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3983627419237510095171217 2987720564428132571378413)
                      ·
                        rfl

theorem cell23_5818565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 4, 1, 2, 2].length) (baseStart_5818565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5818565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5818565 prefixEnd_5818565 := by exact prefixLift 5818565
  have htrace : WordTrace (prefixWord ++ tailWord_5818565) baseStart_5818565 baseEnd_5818565 := by
    simpa [prefixWord, tailWord_5818565, baseEnd_5818565] using wordTrace_append hprefix tailTrace_5818565
  have hstable : (prefixWord ++ tailWord_5818565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5818565).length < 2 ^ (prefixWord ++ tailWord_5818565).sum := by decide
  have hdescent : baseEnd_5818565 < baseStart_5818565 := by decide
  rcases family_descends (prefixWord ++ tailWord_5818565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5818578 : List Nat := [3, 2, 2, 2, 1, 4, 1, 1, 1, 2, 4]
def baseStart_5818578 : Nat := 118140960795 + 5818578 * 2 ^ 59
def prefixEnd_5818578 : Nat := 4983230072969 + 3 ^ 40 * 5818578 * 2
def baseEnd_5818578 : Nat := 2987727239676641020515853

theorem tailTrace_5818578 : CollatzResearch.WordTrace tailWord_5818578 prefixEnd_5818578 2987727239676641020515853 := by
  unfold tailWord_5818578
  simp only [CollatzResearch.WordTrace]
  refine ⟨53055243578573278713076097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141480649542862076568202925 53055243578573278713076097)
  ·
    refine ⟨39791432683929959034807073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53055243578573278713076097 39791432683929959034807073)
    ·
      refine ⟨29843574512947469276105305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39791432683929959034807073 29843574512947469276105305)
      ·
        refine ⟨22382680884710601957078979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29843574512947469276105305 22382680884710601957078979)
        ·
          refine ⟨33574021327065902935618469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22382680884710601957078979 33574021327065902935618469)
          ·
            refine ⟨6295128998824856800428463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33574021327065902935618469 6295128998824856800428463)
            ·
              refine ⟨9442693498237285200642695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6295128998824856800428463 9442693498237285200642695)
              ·
                refine ⟨14164040247355927800964043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9442693498237285200642695 14164040247355927800964043)
                ·
                  refine ⟨21246060371033891701446065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14164040247355927800964043 21246060371033891701446065)
                  ·
                    refine ⟨15934545278275418776084549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21246060371033891701446065 15934545278275418776084549)
                    ·
                      refine ⟨2987727239676641020515853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15934545278275418776084549 2987727239676641020515853)
                      ·
                        rfl

theorem cell23_5818578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 1, 1, 1, 2, 4].length) (baseStart_5818578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5818578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5818578 prefixEnd_5818578 := by exact prefixLift 5818578
  have htrace : WordTrace (prefixWord ++ tailWord_5818578) baseStart_5818578 baseEnd_5818578 := by
    simpa [prefixWord, tailWord_5818578, baseEnd_5818578] using wordTrace_append hprefix tailTrace_5818578
  have hstable : (prefixWord ++ tailWord_5818578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5818578).length < 2 ^ (prefixWord ++ tailWord_5818578).sum := by decide
  have hdescent : baseEnd_5818578 < baseStart_5818578 := by decide
  rcases family_descends (prefixWord ++ tailWord_5818578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5818582 : List Nat := [5, 2, 1, 2, 1, 1, 2, 2, 3, 2, 2]
def baseStart_5818582 : Nat := 118140960795 + 5818582 * 2 ^ 59
def prefixEnd_5818582 : Nat := 4983230072969 + 3 ^ 40 * 5818582 * 2
def baseEnd_5818582 : Nat := 2987729293599259004865835

theorem tailTrace_5818582 : CollatzResearch.WordTrace tailWord_5818582 prefixEnd_5818582 2987729293599259004865835 := by
  unfold tailWord_5818582
  simp only [CollatzResearch.WordTrace]
  refine ⟨13263820012892413970965625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 141480746804185749023633333 13263820012892413970965625)
  ·
    refine ⟨9947865009669310478224219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13263820012892413970965625 9947865009669310478224219)
    ·
      refine ⟨14921797514503965717336329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9947865009669310478224219 14921797514503965717336329)
      ·
        refine ⟨11191348135877974288002247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14921797514503965717336329 11191348135877974288002247)
        ·
          refine ⟨16787022203816961432003371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11191348135877974288002247 16787022203816961432003371)
          ·
            refine ⟨25180533305725442148005057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16787022203816961432003371 25180533305725442148005057)
            ·
              refine ⟨18885399979294081611003793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25180533305725442148005057 18885399979294081611003793)
              ·
                refine ⟨14164049984470561208252845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18885399979294081611003793 14164049984470561208252845)
                ·
                  refine ⟨5311518744176460453094817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14164049984470561208252845 5311518744176460453094817)
                  ·
                    refine ⟨3983639058132345339821113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5311518744176460453094817 3983639058132345339821113)
                    ·
                      refine ⟨2987729293599259004865835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3983639058132345339821113 2987729293599259004865835)
                      ·
                        rfl

theorem cell23_5818582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 2, 3, 2, 2].length) (baseStart_5818582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5818582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5818582 prefixEnd_5818582 := by exact prefixLift 5818582
  have htrace : WordTrace (prefixWord ++ tailWord_5818582) baseStart_5818582 baseEnd_5818582 := by
    simpa [prefixWord, tailWord_5818582, baseEnd_5818582] using wordTrace_append hprefix tailTrace_5818582
  have hstable : (prefixWord ++ tailWord_5818582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5818582).length < 2 ^ (prefixWord ++ tailWord_5818582).sum := by decide
  have hdescent : baseEnd_5818582 < baseStart_5818582 := by decide
  rcases family_descends (prefixWord ++ tailWord_5818582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5818588 : List Nat := [2, 2, 5, 2, 1, 1, 1, 9]
def baseStart_5818588 : Nat := 118140960795 + 5818588 * 2 ^ 59
def prefixEnd_5818588 : Nat := 4983230072969 + 3 ^ 40 * 5818588 * 2
def baseEnd_5818588 : Nat := 110656754610488369681141

theorem tailTrace_5818588 : CollatzResearch.WordTrace tailWord_5818588 prefixEnd_5818588 110656754610488369681141 := by
  unfold tailWord_5818588
  simp only [CollatzResearch.WordTrace]
  refine ⟨106110669522128443280084209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141480892696171257706778945 106110669522128443280084209)
  ·
    refine ⟨79583002141596332460063157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106110669522128443280084209 79583002141596332460063157)
    ·
      refine ⟨7460906450774656168130921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 79583002141596332460063157 7460906450774656168130921)
      ·
        refine ⟨5595679838080992126098191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7460906450774656168130921 5595679838080992126098191)
        ·
          refine ⟨8393519757121488189147287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5595679838080992126098191 8393519757121488189147287)
          ·
            refine ⟨12590279635682232283720931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8393519757121488189147287 12590279635682232283720931)
            ·
              refine ⟨18885419453523348425581397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12590279635682232283720931 18885419453523348425581397)
              ·
                refine ⟨110656754610488369681141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18885419453523348425581397 110656754610488369681141)
                ·
                  rfl

theorem cell23_5818588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 9].length) (baseStart_5818588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5818588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5818588 prefixEnd_5818588 := by exact prefixLift 5818588
  have htrace : WordTrace (prefixWord ++ tailWord_5818588) baseStart_5818588 baseEnd_5818588 := by
    simpa [prefixWord, tailWord_5818588, baseEnd_5818588] using wordTrace_append hprefix tailTrace_5818588
  have hstable : (prefixWord ++ tailWord_5818588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5818588).length < 2 ^ (prefixWord ++ tailWord_5818588).sum := by decide
  have hdescent : baseEnd_5818588 < baseStart_5818588 := by decide
  rcases family_descends (prefixWord ++ tailWord_5818588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5818599 : List Nat := [1, 1, 5, 3, 1, 3, 1, 3, 1, 2, 2]
def baseStart_5818599 : Nat := 118140960795 + 5818599 * 2 ^ 59
def prefixEnd_5818599 : Nat := 4983230072969 + 3 ^ 40 * 5818599 * 2
def baseEnd_5818599 : Nat := 2987738022770385438353257

theorem tailTrace_5818599 : CollatzResearch.WordTrace tailWord_5818599 prefixEnd_5818599 2987738022770385438353257 := by
  unfold tailWord_5818599
  simp only [CollatzResearch.WordTrace]
  refine ⟨212221740247217035438818851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141481160164811356959212567 212221740247217035438818851)
  ·
    refine ⟨318332610370825553158228277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212221740247217035438818851 318332610370825553158228277)
    ·
      refine ⟨29843682222264895608583901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 318332610370825553158228277 29843682222264895608583901)
      ·
        refine ⟨11191380833349335853218963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29843682222264895608583901 11191380833349335853218963)
        ·
          refine ⟨16787071250024003779828445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11191380833349335853218963 16787071250024003779828445)
          ·
            refine ⟨6295151718759001417435667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16787071250024003779828445 6295151718759001417435667)
            ·
              refine ⟨9442727578138502126153501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6295151718759001417435667 9442727578138502126153501)
              ·
                refine ⟨3541022841801938297307563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9442727578138502126153501 3541022841801938297307563)
                ·
                  refine ⟨5311534262702907445961345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3541022841801938297307563 5311534262702907445961345)
                  ·
                    refine ⟨3983650697027180584471009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5311534262702907445961345 3983650697027180584471009)
                    ·
                      refine ⟨2987738022770385438353257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3983650697027180584471009 2987738022770385438353257)
                      ·
                        rfl

theorem cell23_5818599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 1, 3, 1, 2, 2].length) (baseStart_5818599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5818599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5818599 prefixEnd_5818599 := by exact prefixLift 5818599
  have htrace : WordTrace (prefixWord ++ tailWord_5818599) baseStart_5818599 baseEnd_5818599 := by
    simpa [prefixWord, tailWord_5818599, baseEnd_5818599] using wordTrace_append hprefix tailTrace_5818599
  have hstable : (prefixWord ++ tailWord_5818599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5818599).length < 2 ^ (prefixWord ++ tailWord_5818599).sum := by decide
  have hdescent : baseEnd_5818599 < baseStart_5818599 := by decide
  rcases family_descends (prefixWord ++ tailWord_5818599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5818632 : List Nat := [2, 1, 3, 2, 3, 3, 2, 1, 2, 1, 3]
def baseStart_5818632 : Nat := 118140960795 + 5818632 * 2 ^ 59
def prefixEnd_5818632 : Nat := 4983230072969 + 3 ^ 40 * 5818632 * 2
def baseEnd_5818632 : Nat := 2987754967631983809240605

theorem tailTrace_5818632 : CollatzResearch.WordTrace tailWord_5818632 prefixEnd_5818632 2987754967631983809240605 := by
  unfold tailWord_5818632
  simp only [CollatzResearch.WordTrace]
  refine ⟨106111471928048741037385075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141481962570731654716513433 106111471928048741037385075)
  ·
    refine ⟨159167207892073111556077613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106111471928048741037385075 159167207892073111556077613)
    ·
      refine ⟨59687702959527416833529105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 159167207892073111556077613 59687702959527416833529105)
      ·
        refine ⟨44765777219645562625146829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59687702959527416833529105 44765777219645562625146829)
        ·
          refine ⟨16787166457367085984430061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44765777219645562625146829 16787166457367085984430061)
          ·
            refine ⟨6295187421512657244161273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16787166457367085984430061 6295187421512657244161273)
            ·
              refine ⟨4721390566134492933120955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6295187421512657244161273 4721390566134492933120955)
              ·
                refine ⟨7082085849201739399681433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4721390566134492933120955 7082085849201739399681433)
                ·
                  refine ⟨5311564386901304549761075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7082085849201739399681433 5311564386901304549761075)
                  ·
                    refine ⟨7967346580351956824641613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5311564386901304549761075 7967346580351956824641613)
                    ·
                      refine ⟨2987754967631983809240605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7967346580351956824641613 2987754967631983809240605)
                      ·
                        rfl

theorem cell23_5818632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 2, 1, 2, 1, 3].length) (baseStart_5818632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5818632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5818632 prefixEnd_5818632 := by exact prefixLift 5818632
  have htrace : WordTrace (prefixWord ++ tailWord_5818632) baseStart_5818632 baseEnd_5818632 := by
    simpa [prefixWord, tailWord_5818632, baseEnd_5818632] using wordTrace_append hprefix tailTrace_5818632
  have hstable : (prefixWord ++ tailWord_5818632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5818632).length < 2 ^ (prefixWord ++ tailWord_5818632).sum := by decide
  have hdescent : baseEnd_5818632 < baseStart_5818632 := by decide
  rcases family_descends (prefixWord ++ tailWord_5818632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5818638 : List Nat := [4, 1, 1, 2, 1, 2, 2, 3, 1, 4, 2]
def baseStart_5818638 : Nat := 118140960795 + 5818638 * 2 ^ 59
def prefixEnd_5818638 : Nat := 4983230072969 + 3 ^ 40 * 5818638 * 2
def baseEnd_5818638 : Nat := 2987758048515910785765577

theorem tailTrace_5818638 : CollatzResearch.WordTrace tailWord_5818638 prefixEnd_5818638 2987758048515910785765577 := by
  unfold tailWord_5818638
  simp only [CollatzResearch.WordTrace]
  refine ⟨26527895336759468137436071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 141482108462717163399659045 26527895336759468137436071)
  ·
    refine ⟨39791843005139202206154107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26527895336759468137436071 39791843005139202206154107)
    ·
      refine ⟨59687764507708803309231161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39791843005139202206154107 59687764507708803309231161)
      ·
        refine ⟨44765823380781602481923371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59687764507708803309231161 44765823380781602481923371)
        ·
          refine ⟨67148735071172403722885057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44765823380781602481923371 67148735071172403722885057)
          ·
            refine ⟨50361551303379302792163793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67148735071172403722885057 50361551303379302792163793)
            ·
              refine ⟨37771163477534477094122845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50361551303379302792163793 37771163477534477094122845)
              ·
                refine ⟨14164186304075428910296067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37771163477534477094122845 14164186304075428910296067)
                ·
                  refine ⟨21246279456113143365444101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14164186304075428910296067 21246279456113143365444101)
                  ·
                    refine ⟨3983677398021214381020769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21246279456113143365444101 3983677398021214381020769)
                    ·
                      refine ⟨2987758048515910785765577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3983677398021214381020769 2987758048515910785765577)
                      ·
                        rfl

theorem cell23_5818638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 3, 1, 4, 2].length) (baseStart_5818638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5818638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5818638 prefixEnd_5818638 := by exact prefixLift 5818638
  have htrace : WordTrace (prefixWord ++ tailWord_5818638) baseStart_5818638 baseEnd_5818638 := by
    simpa [prefixWord, tailWord_5818638, baseEnd_5818638] using wordTrace_append hprefix tailTrace_5818638
  have hstable : (prefixWord ++ tailWord_5818638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5818638).length < 2 ^ (prefixWord ++ tailWord_5818638).sum := by decide
  have hdescent : baseEnd_5818638 < baseStart_5818638 := by decide
  rcases family_descends (prefixWord ++ tailWord_5818638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5818708 : List Nat := [2, 4, 1, 1, 2, 2, 3, 1, 2, 5]
def baseStart_5818708 : Nat := 118140960795 + 5818708 * 2 ^ 59
def prefixEnd_5818708 : Nat := 4983230072969 + 3 ^ 40 * 5818708 * 2
def baseEnd_5818708 : Nat := 995931330720575170630085

theorem tailTrace_5818708 : CollatzResearch.WordTrace tailWord_5818708 prefixEnd_5818708 995931330720575170630085 := by
  unfold tailWord_5818708
  simp only [CollatzResearch.WordTrace]
  refine ⟨106112857901911073527268389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141483810535881431369691185 106112857901911073527268389)
  ·
    refine ⟨19896160856608326286362823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 106112857901911073527268389 19896160856608326286362823)
    ·
      refine ⟨29844241284912489429544235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19896160856608326286362823 29844241284912489429544235)
      ·
        refine ⟨44766361927368734144316353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29844241284912489429544235 44766361927368734144316353)
        ·
          refine ⟨33574771445526550608237265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44766361927368734144316353 33574771445526550608237265)
          ·
            refine ⟨25181078584144912956177949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33574771445526550608237265 25181078584144912956177949)
            ·
              refine ⟨9442904469054342358566731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25181078584144912956177949 9442904469054342358566731)
              ·
                refine ⟨14164356703581513537850097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9442904469054342358566731 14164356703581513537850097)
                ·
                  refine ⟨10623267527686135153387573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14164356703581513537850097 10623267527686135153387573)
                  ·
                    refine ⟨995931330720575170630085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10623267527686135153387573 995931330720575170630085)
                    ·
                      rfl

theorem cell23_5818708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 3, 1, 2, 5].length) (baseStart_5818708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5818708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5818708 prefixEnd_5818708 := by exact prefixLift 5818708
  have htrace : WordTrace (prefixWord ++ tailWord_5818708) baseStart_5818708 baseEnd_5818708 := by
    simpa [prefixWord, tailWord_5818708, baseEnd_5818708] using wordTrace_append hprefix tailTrace_5818708
  have hstable : (prefixWord ++ tailWord_5818708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5818708).length < 2 ^ (prefixWord ++ tailWord_5818708).sum := by decide
  have hdescent : baseEnd_5818708 < baseStart_5818708 := by decide
  rcases family_descends (prefixWord ++ tailWord_5818708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5818711 : List Nat := [1, 1, 3, 2, 3, 1, 3, 1, 1, 3, 4]
def baseStart_5818711 : Nat := 118140960795 + 5818711 * 2 ^ 59
def prefixEnd_5818711 : Nat := 4983230072969 + 3 ^ 40 * 5818711 * 2
def baseEnd_5818711 : Nat := 2987795532603689000152741

theorem tailTrace_5818711 : CollatzResearch.WordTrace tailWord_5818711 prefixEnd_5818711 2987795532603689000152741 := by
  unfold tailWord_5818711
  simp only [CollatzResearch.WordTrace]
  refine ⟨212225825222811278566895987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141483883481874185711263991 212225825222811278566895987)
  ·
    refine ⟨318338737834216917850343981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212225825222811278566895987 318338737834216917850343981)
    ·
      refine ⟨119377026687831344193878993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 318338737834216917850343981 119377026687831344193878993)
      ·
        refine ⟨89532770015873508145409245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119377026687831344193878993 89532770015873508145409245)
        ·
          refine ⟨33574788755952565554528467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89532770015873508145409245 33574788755952565554528467)
          ·
            refine ⟨50362183133928848331792701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33574788755952565554528467 50362183133928848331792701)
            ·
              refine ⟨18885818675223318124422263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50362183133928848331792701 18885818675223318124422263)
              ·
                refine ⟨28328728012834977186633395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18885818675223318124422263 28328728012834977186633395)
                ·
                  refine ⟨42493092019252465779950093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28328728012834977186633395 42493092019252465779950093)
                  ·
                    refine ⟨15934909507219674667481285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42493092019252465779950093 15934909507219674667481285)
                    ·
                      refine ⟨2987795532603689000152741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15934909507219674667481285 2987795532603689000152741)
                      ·
                        rfl

theorem cell23_5818711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 1, 1, 3, 4].length) (baseStart_5818711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5818711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5818711 prefixEnd_5818711 := by exact prefixLift 5818711
  have htrace : WordTrace (prefixWord ++ tailWord_5818711) baseStart_5818711 baseEnd_5818711 := by
    simpa [prefixWord, tailWord_5818711, baseEnd_5818711] using wordTrace_append hprefix tailTrace_5818711
  have hstable : (prefixWord ++ tailWord_5818711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5818711).length < 2 ^ (prefixWord ++ tailWord_5818711).sum := by decide
  have hdescent : baseEnd_5818711 < baseStart_5818711 := by decide
  rcases family_descends (prefixWord ++ tailWord_5818711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5818738 : List Nat := [3, 2, 1, 2, 1, 3, 1, 3, 3, 4]
def baseStart_5818738 : Nat := 118140960795 + 5818738 * 2 ^ 59
def prefixEnd_5818738 : Nat := 4983230072969 + 3 ^ 40 * 5818738 * 2
def baseEnd_5818738 : Nat := 995936465527120131505039

theorem tailTrace_5818738 : CollatzResearch.WordTrace tailWord_5818738 prefixEnd_5818738 995936465527120131505039 := by
  unfold tailWord_5818738
  simp only [CollatzResearch.WordTrace]
  refine ⟨53056702498428365544532217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141484539995808974785419245 53056702498428365544532217)
  ·
    refine ⟨39792526873821274158399163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53056702498428365544532217 39792526873821274158399163)
    ·
      refine ⟨59688790310731911237598745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39792526873821274158399163 59688790310731911237598745)
      ·
        refine ⟨44766592733048933428199059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59688790310731911237598745 44766592733048933428199059)
        ·
          refine ⟨67149889099573400142298589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44766592733048933428199059 67149889099573400142298589)
          ·
            refine ⟨25181208412340025053361971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67149889099573400142298589 25181208412340025053361971)
            ·
              refine ⟨37771812618510037580042957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25181208412340025053361971 37771812618510037580042957)
              ·
                refine ⟨14164429731941264092516109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37771812618510037580042957 14164429731941264092516109)
                ·
                  refine ⟨5311661149477974034693541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14164429731941264092516109 5311661149477974034693541)
                  ·
                    refine ⟨995936465527120131505039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5311661149477974034693541 995936465527120131505039)
                    ·
                      rfl

theorem cell23_5818738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 3, 3, 4].length) (baseStart_5818738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5818738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5818738 prefixEnd_5818738 := by exact prefixLift 5818738
  have htrace : WordTrace (prefixWord ++ tailWord_5818738) baseStart_5818738 baseEnd_5818738 := by
    simpa [prefixWord, tailWord_5818738, baseEnd_5818738] using wordTrace_append hprefix tailTrace_5818738
  have hstable : (prefixWord ++ tailWord_5818738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5818738).length < 2 ^ (prefixWord ++ tailWord_5818738).sum := by decide
  have hdescent : baseEnd_5818738 < baseStart_5818738 := by decide
  rcases family_descends (prefixWord ++ tailWord_5818738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5818782 : List Nat := [4, 3, 1, 2, 1, 2, 1, 2, 2, 2, 3]
def baseStart_5818782 : Nat := 118140960795 + 5818782 * 2 ^ 59
def prefixEnd_5818782 : Nat := 4983230072969 + 3 ^ 40 * 5818782 * 2
def baseEnd_5818782 : Nat := 2987831989730158222364915

theorem tailTrace_5818782 : CollatzResearch.WordTrace tailWord_5818782 prefixEnd_5818782 2987831989730158222364915 := by
  unfold tailWord_5818782
  simp only [CollatzResearch.WordTrace]
  refine ⟨26528551850694257211591325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 141485609870369371795153733 26528551850694257211591325)
  ·
    refine ⟨9948206944010346454346747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26528551850694257211591325 9948206944010346454346747)
    ·
      refine ⟨14922310416015519681520121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9948206944010346454346747 14922310416015519681520121)
      ·
        refine ⟨11191732812011639761140091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14922310416015519681520121 11191732812011639761140091)
        ·
          refine ⟨16787599218017459641710137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11191732812011639761140091 16787599218017459641710137)
          ·
            refine ⟨12590699413513094731282603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16787599218017459641710137 12590699413513094731282603)
            ·
              refine ⟨18886049120269642096923905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12590699413513094731282603 18886049120269642096923905)
              ·
                refine ⟨14164536840202231572692929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18886049120269642096923905 14164536840202231572692929)
                ·
                  refine ⟨10623402630151673679519697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14164536840202231572692929 10623402630151673679519697)
                  ·
                    refine ⟨7967551972613755259639773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10623402630151673679519697 7967551972613755259639773)
                    ·
                      refine ⟨2987831989730158222364915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7967551972613755259639773 2987831989730158222364915)
                      ·
                        rfl

theorem cell23_5818782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_5818782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5818782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5818782 prefixEnd_5818782 := by exact prefixLift 5818782
  have htrace : WordTrace (prefixWord ++ tailWord_5818782) baseStart_5818782 baseEnd_5818782 := by
    simpa [prefixWord, tailWord_5818782, baseEnd_5818782] using wordTrace_append hprefix tailTrace_5818782
  have hstable : (prefixWord ++ tailWord_5818782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5818782).length < 2 ^ (prefixWord ++ tailWord_5818782).sum := by decide
  have hdescent : baseEnd_5818782 < baseStart_5818782 := by decide
  rcases family_descends (prefixWord ++ tailWord_5818782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5818858 : List Nat := [3, 1, 3, 1, 3, 1, 3, 8]
def baseStart_5818858 : Nat := 118140960795 + 5818858 * 2 ^ 59
def prefixEnd_5818858 : Nat := 4983230072969 + 3 ^ 40 * 5818858 * 2
def baseEnd_5818858 : Nat := 110661889417033330556095

theorem tailTrace_5818858 : CollatzResearch.WordTrace tailWord_5818858 prefixEnd_5818858 110661889417033330556095 := by
  unfold tailWord_5818858
  simp only [CollatzResearch.WordTrace]
  refine ⟨53057796688319680668124307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141487457835519148448331485 53057796688319680668124307)
  ·
    refine ⟨79586695032479521002186461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53057796688319680668124307 79586695032479521002186461)
    ·
      refine ⟨29845010637179820375819923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79586695032479521002186461 29845010637179820375819923)
      ·
        refine ⟨44767515955769730563729885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29845010637179820375819923 44767515955769730563729885)
        ·
          refine ⟨16787818483413648961398707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44767515955769730563729885 16787818483413648961398707)
          ·
            refine ⟨25181727725120473442098061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16787818483413648961398707 25181727725120473442098061)
            ·
              refine ⟨9443147896920177540786773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25181727725120473442098061 9443147896920177540786773)
              ·
                refine ⟨110661889417033330556095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9443147896920177540786773 110661889417033330556095)
                ·
                  rfl

theorem cell23_5818858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 3, 8].length) (baseStart_5818858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5818858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5818858 prefixEnd_5818858 := by exact prefixLift 5818858
  have htrace : WordTrace (prefixWord ++ tailWord_5818858) baseStart_5818858 baseEnd_5818858 := by
    simpa [prefixWord, tailWord_5818858, baseEnd_5818858] using wordTrace_append hprefix tailTrace_5818858
  have hstable : (prefixWord ++ tailWord_5818858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5818858).length < 2 ^ (prefixWord ++ tailWord_5818858).sum := by decide
  have hdescent : baseEnd_5818858 < baseStart_5818858 := by decide
  rcases family_descends (prefixWord ++ tailWord_5818858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5818886 : List Nat := [6, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4]
def baseStart_5818886 : Nat := 118140960795 + 5818886 * 2 ^ 59
def prefixEnd_5818886 : Nat := 4983230072969 + 3 ^ 40 * 5818886 * 2
def baseEnd_5818886 : Nat := 2987885391718225815464437

theorem tailTrace_5818886 : CollatzResearch.WordTrace tailWord_5818886 prefixEnd_5818886 2987885391718225815464437 := by
  unfold tailWord_5818886
  simp only [CollatzResearch.WordTrace]
  refine ⟨6632256499911790107953641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 141488138664784855636344341 6632256499911790107953641)
  ·
    refine ⟨4974192374933842580965231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6632256499911790107953641 4974192374933842580965231)
    ·
      refine ⟨7461288562400763871447847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4974192374933842580965231 7461288562400763871447847)
      ·
        refine ⟨11191932843601145807171771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7461288562400763871447847 11191932843601145807171771)
        ·
          refine ⟨16787899265401718710757657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11191932843601145807171771 16787899265401718710757657)
          ·
            refine ⟨12590924449051289033068243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16787899265401718710757657 12590924449051289033068243)
            ·
              refine ⟨18886386673576933549602365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12590924449051289033068243 18886386673576933549602365)
              ·
                refine ⟨7082395002591350081100887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18886386673576933549602365 7082395002591350081100887)
                ·
                  refine ⟨10623592503887025121651331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7082395002591350081100887 10623592503887025121651331)
                  ·
                    refine ⟨15935388755830537682476997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10623592503887025121651331 15935388755830537682476997)
                    ·
                      refine ⟨2987885391718225815464437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15935388755830537682476997 2987885391718225815464437)
                      ·
                        rfl

theorem cell23_5818886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_5818886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5818886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5818886 prefixEnd_5818886 := by exact prefixLift 5818886
  have htrace : WordTrace (prefixWord ++ tailWord_5818886) baseStart_5818886 baseEnd_5818886 := by
    simpa [prefixWord, tailWord_5818886, baseEnd_5818886] using wordTrace_append hprefix tailTrace_5818886
  have hstable : (prefixWord ++ tailWord_5818886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5818886).length < 2 ^ (prefixWord ++ tailWord_5818886).sum := by decide
  have hdescent : baseEnd_5818886 < baseStart_5818886 := by decide
  rcases family_descends (prefixWord ++ tailWord_5818886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5818921 : List Nat := [1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 12]
def baseStart_5818921 : Nat := 118140960795 + 5818921 * 2 ^ 59
def prefixEnd_5818921 : Nat := 4983230072969 + 3 ^ 40 * 5818921 * 2
def baseEnd_5818921 : Nat := 2987903363541133178526775

theorem tailTrace_5818921 : CollatzResearch.WordTrace tailWord_5818921 prefixEnd_5818921 2987903363541133178526775 := by
  unfold tailWord_5818921
  simp only [CollatzResearch.WordTrace]
  refine ⟨212233484552050484432040617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141488989701366989621360411 212233484552050484432040617)
  ·
    refine ⟨159175113414037863324030463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212233484552050484432040617 159175113414037863324030463)
    ·
      refine ⟨238762670121056794986045695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159175113414037863324030463 238762670121056794986045695)
      ·
        refine ⟨358144005181585192479068543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238762670121056794986045695 358144005181585192479068543)
        ·
          refine ⟨537216007772377788718602815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 358144005181585192479068543 537216007772377788718602815)
          ·
            refine ⟨805824011658566683077904223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 537216007772377788718602815 805824011658566683077904223)
            ·
              refine ⟨1208736017487850024616856335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 805824011658566683077904223 1208736017487850024616856335)
              ·
                refine ⟨1813104026231775036925284503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1208736017487850024616856335 1813104026231775036925284503)
                ·
                  refine ⟨2719656039347662555387926755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1813104026231775036925284503 2719656039347662555387926755)
                  ·
                    refine ⟨4079484059021493833081890133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2719656039347662555387926755 4079484059021493833081890133)
                    ·
                      refine ⟨2987903363541133178526775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 12 4079484059021493833081890133 2987903363541133178526775)
                      ·
                        rfl

theorem cell23_5818921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 12].length) (baseStart_5818921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5818921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5818921 prefixEnd_5818921 := by exact prefixLift 5818921
  have htrace : WordTrace (prefixWord ++ tailWord_5818921) baseStart_5818921 baseEnd_5818921 := by
    simpa [prefixWord, tailWord_5818921, baseEnd_5818921] using wordTrace_append hprefix tailTrace_5818921
  have hstable : (prefixWord ++ tailWord_5818921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5818921).length < 2 ^ (prefixWord ++ tailWord_5818921).sum := by decide
  have hdescent : baseEnd_5818921 < baseStart_5818921 := by decide
  rcases family_descends (prefixWord ++ tailWord_5818921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5818928 : List Nat := [2, 1, 1, 1, 2, 3, 2, 2, 2, 4, 3]
def baseStart_5818928 : Nat := 118140960795 + 5818928 * 2 ^ 59
def prefixEnd_5818928 : Nat := 4983230072969 + 3 ^ 40 * 5818928 * 2
def baseEnd_5818928 : Nat := 2987906957905714651139243

theorem tailTrace_5818928 : CollatzResearch.WordTrace tailWord_5818928 prefixEnd_5818928 2987906957905714651139243 := by
  unfold tailWord_5818928
  simp only [CollatzResearch.WordTrace]
  refine ⟨106116869931512562313772719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141489159908683416418363625 106116869931512562313772719)
  ·
    refine ⟨159175304897268843470659079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106116869931512562313772719 159175304897268843470659079)
    ·
      refine ⟨238762957345903265205988619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159175304897268843470659079 238762957345903265205988619)
      ·
        refine ⟨358144436018854897808982929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238762957345903265205988619 358144436018854897808982929)
        ·
          refine ⟨268608327014141173356737197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 358144436018854897808982929 268608327014141173356737197)
          ·
            refine ⟨100728122630302940008776449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 268608327014141173356737197 100728122630302940008776449)
            ·
              refine ⟨75546091972727205006582337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100728122630302940008776449 75546091972727205006582337)
              ·
                refine ⟨56659568979545403754936753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75546091972727205006582337 56659568979545403754936753)
                ·
                  refine ⟨42494676734659052816202565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56659568979545403754936753 42494676734659052816202565)
                  ·
                    refine ⟨7967751887748572403037981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42494676734659052816202565 7967751887748572403037981)
                    ·
                      refine ⟨2987906957905714651139243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7967751887748572403037981 2987906957905714651139243)
                      ·
                        rfl

theorem cell23_5818928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 2, 2, 4, 3].length) (baseStart_5818928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5818928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5818928 prefixEnd_5818928 := by exact prefixLift 5818928
  have htrace : WordTrace (prefixWord ++ tailWord_5818928) baseStart_5818928 baseEnd_5818928 := by
    simpa [prefixWord, tailWord_5818928, baseEnd_5818928] using wordTrace_append hprefix tailTrace_5818928
  have hstable : (prefixWord ++ tailWord_5818928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5818928).length < 2 ^ (prefixWord ++ tailWord_5818928).sum := by decide
  have hdescent : baseEnd_5818928 < baseStart_5818928 := by decide
  rcases family_descends (prefixWord ++ tailWord_5818928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5818945 : List Nat := [1, 2, 5, 1, 1, 3, 1, 1, 2, 1, 5]
def baseStart_5818945 : Nat := 118140960795 + 5818945 * 2 ^ 59
def prefixEnd_5818945 : Nat := 4983230072969 + 3 ^ 40 * 5818945 * 2
def baseEnd_5818945 : Nat := 2987915687076841084626665

theorem tailTrace_5818945 : CollatzResearch.WordTrace tailWord_5818945 prefixEnd_5818945 2987915687076841084626665 := by
  unfold tailWord_5818945
  simp only [CollatzResearch.WordTrace]
  refine ⟨212234359903963536530914289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141489573269309024353942859 212234359903963536530914289)
  ·
    refine ⟨159175769927972652398185717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212234359903963536530914289 159175769927972652398185717)
    ·
      refine ⟨14922728430747436162329911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 159175769927972652398185717 14922728430747436162329911)
      ·
        refine ⟨22384092646121154243494867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14922728430747436162329911 22384092646121154243494867)
        ·
          refine ⟨33576138969181731365242301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22384092646121154243494867 33576138969181731365242301)
          ·
            refine ⟨12591052113443149261965863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33576138969181731365242301 12591052113443149261965863)
            ·
              refine ⟨18886578170164723892948795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12591052113443149261965863 18886578170164723892948795)
              ·
                refine ⟨28329867255247085839423193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18886578170164723892948795 28329867255247085839423193)
                ·
                  refine ⟨21247400441435314379567395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28329867255247085839423193 21247400441435314379567395)
                  ·
                    refine ⟨31871100662152971569351093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21247400441435314379567395 31871100662152971569351093)
                    ·
                      refine ⟨2987915687076841084626665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31871100662152971569351093 2987915687076841084626665)
                      ·
                        rfl

theorem cell23_5818945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_5818945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5818945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5818945 prefixEnd_5818945 := by exact prefixLift 5818945
  have htrace : WordTrace (prefixWord ++ tailWord_5818945) baseStart_5818945 baseEnd_5818945 := by
    simpa [prefixWord, tailWord_5818945, baseEnd_5818945] using wordTrace_append hprefix tailTrace_5818945
  have hstable : (prefixWord ++ tailWord_5818945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5818945).length < 2 ^ (prefixWord ++ tailWord_5818945).sum := by decide
  have hdescent : baseEnd_5818945 < baseStart_5818945 := by decide
  rcases family_descends (prefixWord ++ tailWord_5818945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5818965 : List Nat := [1, 3, 2, 2, 1, 1, 2, 6, 5]
def baseStart_5818965 : Nat := 118140960795 + 5818965 * 2 ^ 59
def prefixEnd_5818965 : Nat := 4983230072969 + 3 ^ 40 * 5818965 * 2
def baseEnd_5818965 : Nat := 331991772965547889597397

theorem tailTrace_5818965 : CollatzResearch.WordTrace tailWord_5818965 prefixEnd_5818965 331991772965547889597397 := by
  unfold tailWord_5818965
  simp only [CollatzResearch.WordTrace]
  refine ⟨212235089363891079946642349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141490059575927386631094899 212235089363891079946642349)
  ·
    refine ⟨79588158511459154979990881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 212235089363891079946642349 79588158511459154979990881)
    ·
      refine ⟨59691118883594366234993161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79588158511459154979990881 59691118883594366234993161)
      ·
        refine ⟨44768339162695774676244871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59691118883594366234993161 44768339162695774676244871)
        ·
          refine ⟨67152508744043662014367307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44768339162695774676244871 67152508744043662014367307)
          ·
            refine ⟨100728763116065493021550961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67152508744043662014367307 100728763116065493021550961)
            ·
              refine ⟨75546572337049119766163221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100728763116065493021550961 75546572337049119766163221)
              ·
                refine ⟨3541245578299177489038901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 75546572337049119766163221 3541245578299177489038901)
                ·
                  refine ⟨331991772965547889597397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3541245578299177489038901 331991772965547889597397)
                  ·
                    rfl

theorem cell23_5818965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 6, 5].length) (baseStart_5818965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5818965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5818965 prefixEnd_5818965 := by exact prefixLift 5818965
  have htrace : WordTrace (prefixWord ++ tailWord_5818965) baseStart_5818965 baseEnd_5818965 := by
    simpa [prefixWord, tailWord_5818965, baseEnd_5818965] using wordTrace_append hprefix tailTrace_5818965
  have hstable : (prefixWord ++ tailWord_5818965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5818965).length < 2 ^ (prefixWord ++ tailWord_5818965).sum := by decide
  have hdescent : baseEnd_5818965 < baseStart_5818965 := by decide
  rcases family_descends (prefixWord ++ tailWord_5818965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5819015 : List Nat := [1, 1, 4, 2, 1, 2, 1, 4, 2, 1, 4]
def baseStart_5819015 : Nat := 118140960795 + 5819015 * 2 ^ 59
def prefixEnd_5819015 : Nat := 4983230072969 + 3 ^ 40 * 5819015 * 2
def baseEnd_5819015 : Nat := 2987951630722655810751343

theorem tailTrace_5819015 : CollatzResearch.WordTrace tailWord_5819015 prefixEnd_5819015 2987951630722655810751343 := by
  unfold tailWord_5819015
  simp only [CollatzResearch.WordTrace]
  refine ⟨212236913013709938485962499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141491275342473292323974999 212236913013709938485962499)
  ·
    refine ⟨318355369520564907728943749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212236913013709938485962499 318355369520564907728943749)
    ·
      refine ⟨59691631785105920199176953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 318355369520564907728943749 59691631785105920199176953)
      ·
        refine ⟨44768723838829440149382715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59691631785105920199176953 44768723838829440149382715)
        ·
          refine ⟨67153085758244160224074073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44768723838829440149382715 67153085758244160224074073)
          ·
            refine ⟨50364814318683120168055555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67153085758244160224074073 50364814318683120168055555)
            ·
              refine ⟨75547221478024680252083333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50364814318683120168055555 75547221478024680252083333)
              ·
                refine ⟨14165104027129627547265625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 75547221478024680252083333 14165104027129627547265625)
                ·
                  refine ⟨10623828020347220660449219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14165104027129627547265625 10623828020347220660449219)
                  ·
                    refine ⟨15935742030520830990673829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10623828020347220660449219 15935742030520830990673829)
                    ·
                      refine ⟨2987951630722655810751343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15935742030520830990673829 2987951630722655810751343)
                      ·
                        rfl

theorem cell23_5819015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 4, 2, 1, 4].length) (baseStart_5819015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5819015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5819015 prefixEnd_5819015 := by exact prefixLift 5819015
  have htrace : WordTrace (prefixWord ++ tailWord_5819015) baseStart_5819015 baseEnd_5819015 := by
    simpa [prefixWord, tailWord_5819015, baseEnd_5819015] using wordTrace_append hprefix tailTrace_5819015
  have hstable : (prefixWord ++ tailWord_5819015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5819015).length < 2 ^ (prefixWord ++ tailWord_5819015).sum := by decide
  have hdescent : baseEnd_5819015 < baseStart_5819015 := by decide
  rcases family_descends (prefixWord ++ tailWord_5819015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5819032 : List Nat := [2, 1, 2, 4, 1, 1, 3, 1, 2, 4, 2]
def baseStart_5819032 : Nat := 118140960795 + 5819032 * 2 ^ 59
def prefixEnd_5819032 : Nat := 4983230072969 + 3 ^ 40 * 5819032 * 2
def baseEnd_5819032 : Nat := 2987960359893782244238765

theorem tailTrace_5819032 : CollatzResearch.WordTrace tailWord_5819032 prefixEnd_5819032 2987960359893782244238765 := by
  unfold tailWord_5819032
  simp only [CollatzResearch.WordTrace]
  refine ⟨106118766527324175194665675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141491688703098900259554233 106118766527324175194665675)
  ·
    refine ⟨159178149790986262791998513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106118766527324175194665675 159178149790986262791998513)
    ·
      refine ⟨119383612343239697093998885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159178149790986262791998513 119383612343239697093998885)
      ·
        refine ⟨22384427314357443205124791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 119383612343239697093998885 22384427314357443205124791)
        ·
          refine ⟨33576640971536164807687187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22384427314357443205124791 33576640971536164807687187)
          ·
            refine ⟨50364961457304247211530781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33576640971536164807687187 50364961457304247211530781)
            ·
              refine ⟨18886860546489092704324043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50364961457304247211530781 18886860546489092704324043)
              ·
                refine ⟨28330290819733639056486065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18886860546489092704324043 28330290819733639056486065)
                ·
                  refine ⟨21247718114800229292364549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28330290819733639056486065 21247718114800229292364549)
                  ·
                    refine ⟨3983947146525042992318353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21247718114800229292364549 3983947146525042992318353)
                    ·
                      refine ⟨2987960359893782244238765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3983947146525042992318353 2987960359893782244238765)
                      ·
                        rfl

theorem cell23_5819032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 1, 2, 4, 2].length) (baseStart_5819032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5819032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5819032 prefixEnd_5819032 := by exact prefixLift 5819032
  have htrace : WordTrace (prefixWord ++ tailWord_5819032) baseStart_5819032 baseEnd_5819032 := by
    simpa [prefixWord, tailWord_5819032, baseEnd_5819032] using wordTrace_append hprefix tailTrace_5819032
  have hstable : (prefixWord ++ tailWord_5819032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5819032).length < 2 ^ (prefixWord ++ tailWord_5819032).sum := by decide
  have hdescent : baseEnd_5819032 < baseStart_5819032 := by decide
  rcases family_descends (prefixWord ++ tailWord_5819032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5819059 : List Nat := [1, 1, 1, 2, 3, 5, 2, 3, 1, 4]
def baseStart_5819059 : Nat := 118140960795 + 5819059 * 2 ^ 59
def prefixEnd_5819059 : Nat := 4983230072969 + 3 ^ 40 * 5819059 * 2
def baseEnd_5819059 : Nat := 995991407957151212867047

theorem tailTrace_5819059 : CollatzResearch.WordTrace tailWord_5819059 prefixEnd_5819059 995991407957151212867047 := by
  unfold tailWord_5819059
  simp only [CollatzResearch.WordTrace]
  refine ⟨212238517825550534000564231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141492345217033689333709487 212238517825550534000564231)
  ·
    refine ⟨318357776738325801000846347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212238517825550534000564231 318357776738325801000846347)
    ·
      refine ⟨477536665107488701501269521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 318357776738325801000846347 477536665107488701501269521)
      ·
        refine ⟨358152498830616526125952141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 477536665107488701501269521 358152498830616526125952141)
        ·
          refine ⟨134307187061481197297232053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 358152498830616526125952141 134307187061481197297232053)
          ·
            refine ⟨12591298787013862246615505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 134307187061481197297232053 12591298787013862246615505)
            ·
              refine ⟨9443474090260396684961629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12591298787013862246615505 9443474090260396684961629)
              ·
                refine ⟨3541302783847648756860611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9443474090260396684961629 3541302783847648756860611)
                ·
                  refine ⟨5311954175771473135290917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3541302783847648756860611 5311954175771473135290917)
                  ·
                    refine ⟨995991407957151212867047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5311954175771473135290917 995991407957151212867047)
                    ·
                      rfl

theorem cell23_5819059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 2, 3, 1, 4].length) (baseStart_5819059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5819059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5819059 prefixEnd_5819059 := by exact prefixLift 5819059
  have htrace : WordTrace (prefixWord ++ tailWord_5819059) baseStart_5819059 baseEnd_5819059 := by
    simpa [prefixWord, tailWord_5819059, baseEnd_5819059] using wordTrace_append hprefix tailTrace_5819059
  have hstable : (prefixWord ++ tailWord_5819059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5819059).length < 2 ^ (prefixWord ++ tailWord_5819059).sum := by decide
  have hdescent : baseEnd_5819059 < baseStart_5819059 := by decide
  rcases family_descends (prefixWord ++ tailWord_5819059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5819072 : List Nat := [2, 1, 1, 2, 4, 4, 1, 2, 6]
def baseStart_5819072 : Nat := 118140960795 + 5819072 * 2 ^ 59
def prefixEnd_5819072 : Nat := 4983230072969 + 3 ^ 40 * 5819072 * 2
def baseEnd_5819072 : Nat := 331997877679995787526509

theorem tailTrace_5819072 : CollatzResearch.WordTrace tailWord_5819072 prefixEnd_5819072 331997877679995787526509 := by
  unfold tailWord_5819072
  simp only [CollatzResearch.WordTrace]
  refine ⟨106119495987251718610393735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141492661316335624813858313 106119495987251718610393735)
  ·
    refine ⟨159179243980877577915590603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106119495987251718610393735 159179243980877577915590603)
    ·
      refine ⟨238768865971316366873385905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159179243980877577915590603 238768865971316366873385905)
      ·
        refine ⟨179076649478487275155039429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 238768865971316366873385905 179076649478487275155039429)
        ·
          refine ⟨33576871777216364091569893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 179076649478487275155039429 33576871777216364091569893)
          ·
            refine ⟨6295663458228068267169355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33576871777216364091569893 6295663458228068267169355)
            ·
              refine ⟨9443495187342102400754033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6295663458228068267169355 9443495187342102400754033)
              ·
                refine ⟨7082621390506576800565525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9443495187342102400754033 7082621390506576800565525)
                ·
                  refine ⟨331997877679995787526509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7082621390506576800565525 331997877679995787526509)
                  ·
                    rfl

theorem cell23_5819072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 1, 2, 6].length) (baseStart_5819072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5819072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5819072 prefixEnd_5819072 := by exact prefixLift 5819072
  have htrace : WordTrace (prefixWord ++ tailWord_5819072) baseStart_5819072 baseEnd_5819072 := by
    simpa [prefixWord, tailWord_5819072, baseEnd_5819072] using wordTrace_append hprefix tailTrace_5819072
  have hstable : (prefixWord ++ tailWord_5819072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5819072).length < 2 ^ (prefixWord ++ tailWord_5819072).sum := by decide
  have hdescent : baseEnd_5819072 < baseStart_5819072 := by decide
  rcases family_descends (prefixWord ++ tailWord_5819072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5819132 : List Nat := [2, 2, 2, 1, 3, 2, 2, 1, 4, 4]
def baseStart_5819132 : Nat := 118140960795 + 5819132 * 2 ^ 59
def prefixEnd_5819132 : Nat := 4983230072969 + 3 ^ 40 * 5819132 * 2
def baseEnd_5819132 : Nat := 996003902653077284329435

theorem tailTrace_5819132 : CollatzResearch.WordTrace tailWord_5819132 prefixEnd_5819132 996003902653077284329435 := by
  unfold tailWord_5819132
  simp only [CollatzResearch.WordTrace]
  refine ⟨106120590177143033733985825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141494120236190711645314433 106120590177143033733985825)
  ·
    refine ⟨79590442632857275300489369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106120590177143033733985825 79590442632857275300489369)
    ·
      refine ⟨59692831974642956475367027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79590442632857275300489369 59692831974642956475367027)
      ·
        refine ⟨89539247961964434713050541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59692831974642956475367027 89539247961964434713050541)
        ·
          refine ⟨33577217985736663017393953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89539247961964434713050541 33577217985736663017393953)
          ·
            refine ⟨25182913489302497263045465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33577217985736663017393953 25182913489302497263045465)
            ·
              refine ⟨18887185116976872947284099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25182913489302497263045465 18887185116976872947284099)
              ·
                refine ⟨28330777675465309420926149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18887185116976872947284099 28330777675465309420926149)
                ·
                  refine ⟨5312020814149745516423653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28330777675465309420926149 5312020814149745516423653)
                  ·
                    refine ⟨996003902653077284329435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5312020814149745516423653 996003902653077284329435)
                    ·
                      rfl

theorem cell23_5819132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 1, 4, 4].length) (baseStart_5819132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5819132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5819132 prefixEnd_5819132 := by exact prefixLift 5819132
  have htrace : WordTrace (prefixWord ++ tailWord_5819132) baseStart_5819132 baseEnd_5819132 := by
    simpa [prefixWord, tailWord_5819132, baseEnd_5819132] using wordTrace_append hprefix tailTrace_5819132
  have hstable : (prefixWord ++ tailWord_5819132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5819132).length < 2 ^ (prefixWord ++ tailWord_5819132).sum := by decide
  have hdescent : baseEnd_5819132 < baseStart_5819132 := by decide
  rcases family_descends (prefixWord ++ tailWord_5819132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5819159 : List Nat := [1, 1, 3, 4, 3, 1, 1, 1, 3, 2, 3]
def baseStart_5819159 : Nat := 118140960795 + 5819159 * 2 ^ 59
def prefixEnd_5819159 : Nat := 4983230072969 + 3 ^ 40 * 5819159 * 2
def baseEnd_5819159 : Nat := 2988025571936903247350681

theorem tailTrace_5819159 : CollatzResearch.WordTrace tailWord_5819159 prefixEnd_5819159 2988025571936903247350681 := by
  unfold tailWord_5819159
  simp only [CollatzResearch.WordTrace]
  refine ⟨212242165125188251079204531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141494776750125500719469687 212242165125188251079204531)
  ·
    refine ⟨318363247687782376618806797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212242165125188251079204531 318363247687782376618806797)
    ·
      refine ⟨119386217882918391232052549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 318363247687782376618806797 119386217882918391232052549)
      ·
        refine ⟨22384915853047198356009853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 119386217882918391232052549 22384915853047198356009853)
        ·
          refine ⟨8394343444892699383503695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22384915853047198356009853 8394343444892699383503695)
          ·
            refine ⟨12591515167339049075255543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8394343444892699383503695 12591515167339049075255543)
            ·
              refine ⟨18887272751008573612883315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12591515167339049075255543 18887272751008573612883315)
              ·
                refine ⟨28330909126512860419324973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18887272751008573612883315 28330909126512860419324973)
                ·
                  refine ⟨10624090922442322657246865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28330909126512860419324973 10624090922442322657246865)
                  ·
                    refine ⟨7968068191831741992935149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10624090922442322657246865 7968068191831741992935149)
                    ·
                      refine ⟨2988025571936903247350681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7968068191831741992935149 2988025571936903247350681)
                      ·
                        rfl

theorem cell23_5819159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 1, 3, 2, 3].length) (baseStart_5819159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5819159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5819159 prefixEnd_5819159 := by exact prefixLift 5819159
  have htrace : WordTrace (prefixWord ++ tailWord_5819159) baseStart_5819159 baseEnd_5819159 := by
    simpa [prefixWord, tailWord_5819159, baseEnd_5819159] using wordTrace_append hprefix tailTrace_5819159
  have hstable : (prefixWord ++ tailWord_5819159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5819159).length < 2 ^ (prefixWord ++ tailWord_5819159).sum := by decide
  have hdescent : baseEnd_5819159 < baseStart_5819159 := by decide
  rcases family_descends (prefixWord ++ tailWord_5819159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5819176 : List Nat := [2, 1, 5, 1, 1, 1, 5, 1, 1, 2, 3]
def baseStart_5819176 : Nat := 118140960795 + 5819176 * 2 ^ 59
def prefixEnd_5819176 : Nat := 4983230072969 + 3 ^ 40 * 5819176 * 2
def baseEnd_5819176 : Nat := 2988034301108029680838103

theorem tailTrace_5819176 : CollatzResearch.WordTrace tailWord_5819176 prefixEnd_5819176 2988034301108029680838103 := by
  unfold tailWord_5819176
  simp only [CollatzResearch.WordTrace]
  refine ⟨106121392583063331491286691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141495190110751108655048921 106121392583063331491286691)
  ·
    refine ⟨159182088874594997236930037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106121392583063331491286691 159182088874594997236930037)
    ·
      refine ⟨14923320831993280990962191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 159182088874594997236930037 14923320831993280990962191)
      ·
        refine ⟨22384981247989921486443287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14923320831993280990962191 22384981247989921486443287)
        ·
          refine ⟨33577471871984882229664931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22384981247989921486443287 33577471871984882229664931)
          ·
            refine ⟨50366207807977323344497397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33577471871984882229664931 50366207807977323344497397)
            ·
              refine ⟨4721831981997874063546631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50366207807977323344497397 4721831981997874063546631)
              ·
                refine ⟨7082747972996811095319947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4721831981997874063546631 7082747972996811095319947)
                ·
                  refine ⟨10624121959495216642979921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7082747972996811095319947 10624121959495216642979921)
                  ·
                    refine ⟨7968091469621412482234941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10624121959495216642979921 7968091469621412482234941)
                    ·
                      refine ⟨2988034301108029680838103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7968091469621412482234941 2988034301108029680838103)
                      ·
                        rfl

theorem cell23_5819176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 5, 1, 1, 2, 3].length) (baseStart_5819176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5819176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5819176 prefixEnd_5819176 := by exact prefixLift 5819176
  have htrace : WordTrace (prefixWord ++ tailWord_5819176) baseStart_5819176 baseEnd_5819176 := by
    simpa [prefixWord, tailWord_5819176, baseEnd_5819176] using wordTrace_append hprefix tailTrace_5819176
  have hstable : (prefixWord ++ tailWord_5819176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5819176).length < 2 ^ (prefixWord ++ tailWord_5819176).sum := by decide
  have hdescent : baseEnd_5819176 < baseStart_5819176 := by decide
  rcases family_descends (prefixWord ++ tailWord_5819176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5819199 : List Nat := [1, 1, 2, 2, 5, 1, 1, 2, 3, 3, 2]
def baseStart_5819199 : Nat := 118140960795 + 5819199 * 2 ^ 59
def prefixEnd_5819199 : Nat := 4983230072969 + 3 ^ 40 * 5819199 * 2
def baseEnd_5819199 : Nat := 2988046111163083090850497

theorem tailTrace_5819199 : CollatzResearch.WordTrace tailWord_5819199 prefixEnd_5819199 2988046111163083090850497 := by
  unfold tailWord_5819199
  simp only [CollatzResearch.WordTrace]
  refine ⟨212243624045043337910660651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141495749363362225273773767 212243624045043337910660651)
  ·
    refine ⟨318365436067565006865990977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212243624045043337910660651 318365436067565006865990977)
    ·
      refine ⟨238774077050673755149493233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 318365436067565006865990977 238774077050673755149493233)
      ·
        refine ⟨179080557788005316362119925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 238774077050673755149493233 179080557788005316362119925)
        ·
          refine ⟨16788802292625498408948743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 179080557788005316362119925 16788802292625498408948743)
          ·
            refine ⟨25183203438938247613423115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16788802292625498408948743 25183203438938247613423115)
            ·
              refine ⟨37774805158407371420134673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25183203438938247613423115 37774805158407371420134673)
              ·
                refine ⟨28331103868805528565101005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37774805158407371420134673 28331103868805528565101005)
                ·
                  refine ⟨10624163950802073211912877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28331103868805528565101005 10624163950802073211912877)
                  ·
                    refine ⟨3984061481550777454467329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10624163950802073211912877 3984061481550777454467329)
                    ·
                      refine ⟨2988046111163083090850497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3984061481550777454467329 2988046111163083090850497)
                      ·
                        rfl

theorem cell23_5819199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 2, 3, 3, 2].length) (baseStart_5819199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5819199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5819199 prefixEnd_5819199 := by exact prefixLift 5819199
  have htrace : WordTrace (prefixWord ++ tailWord_5819199) baseStart_5819199 baseEnd_5819199 := by
    simpa [prefixWord, tailWord_5819199, baseEnd_5819199] using wordTrace_append hprefix tailTrace_5819199
  have hstable : (prefixWord ++ tailWord_5819199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5819199).length < 2 ^ (prefixWord ++ tailWord_5819199).sum := by decide
  have hdescent : baseEnd_5819199 < baseStart_5819199 := by decide
  rcases family_descends (prefixWord ++ tailWord_5819199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5819303 : List Nat := [1, 1, 6, 1, 3, 1, 3, 2, 5]
def baseStart_5819303 : Nat := 118140960795 + 5819303 * 2 ^ 59
def prefixEnd_5819303 : Nat := 4983230072969 + 3 ^ 40 * 5819303 * 2
def baseEnd_5819303 : Nat := 332011057016794520438891

theorem tailTrace_5819303 : CollatzResearch.WordTrace tailWord_5819303 prefixEnd_5819303 332011057016794520438891 := by
  unfold tailWord_5819303
  simp only [CollatzResearch.WordTrace]
  refine ⟨212247417236666563672446563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141498278157777709114964375 212247417236666563672446563)
  ·
    refine ⟨318371125854999845508669845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212247417236666563672446563 318371125854999845508669845)
    ·
      refine ⟨14923646524453117758218899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 318371125854999845508669845 14923646524453117758218899)
      ·
        refine ⟨22385469786679676637328349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14923646524453117758218899 22385469786679676637328349)
        ·
          refine ⟨8394551170004878738998131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22385469786679676637328349 8394551170004878738998131)
          ·
            refine ⟨12591826755007318108497197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8394551170004878738998131 12591826755007318108497197)
            ·
              refine ⟨4721935033127744290686449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12591826755007318108497197 4721935033127744290686449)
              ·
                refine ⟨3541451274845808218014837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4721935033127744290686449 3541451274845808218014837)
                ·
                  refine ⟨332011057016794520438891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3541451274845808218014837 332011057016794520438891)
                  ·
                    rfl

theorem cell23_5819303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 3, 2, 5].length) (baseStart_5819303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5819303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5819303 prefixEnd_5819303 := by exact prefixLift 5819303
  have htrace : WordTrace (prefixWord ++ tailWord_5819303) baseStart_5819303 baseEnd_5819303 := by
    simpa [prefixWord, tailWord_5819303, baseEnd_5819303] using wordTrace_append hprefix tailTrace_5819303
  have hstable : (prefixWord ++ tailWord_5819303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5819303).length < 2 ^ (prefixWord ++ tailWord_5819303).sum := by decide
  have hdescent : baseEnd_5819303 < baseStart_5819303 := by decide
  rcases family_descends (prefixWord ++ tailWord_5819303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5819319 : List Nat := [1, 1, 3, 1, 3, 1, 2, 3, 2, 4, 2]
def baseStart_5819319 : Nat := 118140960795 + 5819319 * 2 ^ 59
def prefixEnd_5819319 : Nat := 4983230072969 + 3 ^ 40 * 5819319 * 2
def baseEnd_5819319 : Nat := 2988107728841622621349945

theorem tailTrace_5819319 : CollatzResearch.WordTrace tailWord_5819319 prefixEnd_5819319 2988107728841622621349945 := by
  unfold tailWord_5819319
  simp only [CollatzResearch.WordTrace]
  refine ⟨212248000804608598405029011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141498667203072398936686007 212248000804608598405029011)
  ·
    refine ⟨318372001206912897607543517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212248000804608598405029011 318372001206912897607543517)
    ·
      refine ⟨119389500452592336602828819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 318372001206912897607543517 119389500452592336602828819)
      ·
        refine ⟨179084250678888504904243229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119389500452592336602828819 179084250678888504904243229)
        ·
          refine ⟨67156594004583189339091211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 179084250678888504904243229 67156594004583189339091211)
          ·
            refine ⟨100734891006874784008636817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67156594004583189339091211 100734891006874784008636817)
            ·
              refine ⟨75551168255156088006477613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100734891006874784008636817 75551168255156088006477613)
              ·
                refine ⟨28331688095683533002429105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75551168255156088006477613 28331688095683533002429105)
                ·
                  refine ⟨21248766071762649751821829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28331688095683533002429105 21248766071762649751821829)
                  ·
                    refine ⟨3984143638455496828466593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21248766071762649751821829 3984143638455496828466593)
                    ·
                      refine ⟨2988107728841622621349945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3984143638455496828466593 2988107728841622621349945)
                      ·
                        rfl

theorem cell23_5819319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 3, 2, 4, 2].length) (baseStart_5819319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5819319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5819319 prefixEnd_5819319 := by exact prefixLift 5819319
  have htrace : WordTrace (prefixWord ++ tailWord_5819319) baseStart_5819319 baseEnd_5819319 := by
    simpa [prefixWord, tailWord_5819319, baseEnd_5819319] using wordTrace_append hprefix tailTrace_5819319
  have hstable : (prefixWord ++ tailWord_5819319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5819319).length < 2 ^ (prefixWord ++ tailWord_5819319).sum := by decide
  have hdescent : baseEnd_5819319 < baseStart_5819319 := by decide
  rcases family_descends (prefixWord ++ tailWord_5819319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5819336 : List Nat := [2, 1, 3, 1, 5, 1, 2, 1, 2, 1, 4]
def baseStart_5819336 : Nat := 118140960795 + 5819336 * 2 ^ 59
def prefixEnd_5819336 : Nat := 4983230072969 + 3 ^ 40 * 5819336 * 2
def baseEnd_5819336 : Nat := 2988116458012749054837367

theorem tailTrace_5819336 : CollatzResearch.WordTrace tailWord_5819336 prefixEnd_5819336 2988116458012749054837367 := by
  unfold tailWord_5819336
  simp only [CollatzResearch.WordTrace]
  refine ⟨106124310422773505154198931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141499080563698006872265241 106124310422773505154198931)
  ·
    refine ⟨159186465634160257731298397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106124310422773505154198931 159186465634160257731298397)
    ·
      refine ⟨59694924612810096649236899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 159186465634160257731298397 59694924612810096649236899)
      ·
        refine ⟨89542386919215144973855349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59694924612810096649236899 89542386919215144973855349)
        ·
          refine ⟨8394598773676419841298939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 89542386919215144973855349 8394598773676419841298939)
          ·
            refine ⟨12591898160514629761948409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8394598773676419841298939 12591898160514629761948409)
            ·
              refine ⟨9443923620385972321461307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12591898160514629761948409 9443923620385972321461307)
              ·
                refine ⟨14165885430578958482191961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9443923620385972321461307 14165885430578958482191961)
                ·
                  refine ⟨10624414072934218861643971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14165885430578958482191961 10624414072934218861643971)
                  ·
                    refine ⟨15936621109401328292465957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10624414072934218861643971 15936621109401328292465957)
                    ·
                      refine ⟨2988116458012749054837367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15936621109401328292465957 2988116458012749054837367)
                      ·
                        rfl

theorem cell23_5819336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 2, 1, 2, 1, 4].length) (baseStart_5819336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5819336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5819336 prefixEnd_5819336 := by exact prefixLift 5819336
  have htrace : WordTrace (prefixWord ++ tailWord_5819336) baseStart_5819336 baseEnd_5819336 := by
    simpa [prefixWord, tailWord_5819336, baseEnd_5819336] using wordTrace_append hprefix tailTrace_5819336
  have hstable : (prefixWord ++ tailWord_5819336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5819336).length < 2 ^ (prefixWord ++ tailWord_5819336).sum := by decide
  have hdescent : baseEnd_5819336 < baseStart_5819336 := by decide
  rcases family_descends (prefixWord ++ tailWord_5819336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5819339 : List Nat := [1, 1, 1, 1, 3, 5, 1, 3, 2, 2, 3]
def baseStart_5819339 : Nat := 118140960795 + 5819339 * 2 ^ 59
def prefixEnd_5819339 : Nat := 4983230072969 + 3 ^ 40 * 5819339 * 2
def baseEnd_5819339 : Nat := 2988117998454712543099853

theorem tailTrace_5819339 : CollatzResearch.WordTrace tailWord_5819339 prefixEnd_5819339 2988117998454712543099853 := by
  unfold tailWord_5819339
  simp only [CollatzResearch.WordTrace]
  refine ⟨212248730264536141820757071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141499153509690761213838047 212248730264536141820757071)
  ·
    refine ⟨318373095396804212731135607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212248730264536141820757071 318373095396804212731135607)
    ·
      refine ⟨477559643095206319096703411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 318373095396804212731135607 477559643095206319096703411)
      ·
        refine ⟨716339464642809478645055117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 477559643095206319096703411 716339464642809478645055117)
        ·
          refine ⟨268627299241053554491895669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 716339464642809478645055117 268627299241053554491895669)
          ·
            refine ⟨25183809303848770733615219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 268627299241053554491895669 25183809303848770733615219)
            ·
              refine ⟨37775713955773156100422829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25183809303848770733615219 37775713955773156100422829)
              ·
                refine ⟨14165892733414933537658561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37775713955773156100422829 14165892733414933537658561)
                ·
                  refine ⟨10624419550061200153243921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14165892733414933537658561 10624419550061200153243921)
                  ·
                    refine ⟨7968314662545900114932941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10624419550061200153243921 7968314662545900114932941)
                    ·
                      refine ⟨2988117998454712543099853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7968314662545900114932941 2988117998454712543099853)
                      ·
                        rfl

theorem cell23_5819339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 3, 2, 2, 3].length) (baseStart_5819339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5819339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5819339 prefixEnd_5819339 := by exact prefixLift 5819339
  have htrace : WordTrace (prefixWord ++ tailWord_5819339) baseStart_5819339 baseEnd_5819339 := by
    simpa [prefixWord, tailWord_5819339, baseEnd_5819339] using wordTrace_append hprefix tailTrace_5819339
  have hstable : (prefixWord ++ tailWord_5819339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5819339).length < 2 ^ (prefixWord ++ tailWord_5819339).sum := by decide
  have hdescent : baseEnd_5819339 < baseStart_5819339 := by decide
  rcases family_descends (prefixWord ++ tailWord_5819339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5819369 : List Nat := [1, 2, 1, 1, 1, 2, 1, 1, 9, 1, 3]
def baseStart_5819369 : Nat := 118140960795 + 5819369 * 2 ^ 59
def prefixEnd_5819369 : Nat := 4983230072969 + 3 ^ 40 * 5819369 * 2
def baseEnd_5819369 : Nat := 2988133402874347425724715

theorem tailTrace_5819369 : CollatzResearch.WordTrace tailWord_5819369 prefixEnd_5819369 2988133402874347425724715 := by
  unfold tailWord_5819369
  simp only [CollatzResearch.WordTrace]
  refine ⟨212249824454427456944349161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141499882969618304629566107 212249824454427456944349161)
  ·
    refine ⟨159187368340820592708261871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212249824454427456944349161 159187368340820592708261871)
    ·
      refine ⟨238781052511230889062392807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159187368340820592708261871 238781052511230889062392807)
      ·
        refine ⟨358171578766846333593589211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238781052511230889062392807 358171578766846333593589211)
        ·
          refine ⟨537257368150269500390383817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 358171578766846333593589211 537257368150269500390383817)
          ·
            refine ⟨402943026112702125292787863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 537257368150269500390383817 402943026112702125292787863)
            ·
              refine ⟨604414539169053187939181795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 402943026112702125292787863 604414539169053187939181795)
              ·
                refine ⟨906621808753579781908772693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 604414539169053187939181795 906621808753579781908772693)
                ·
                  refine ⟨5312237160665506534621715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 906621808753579781908772693 5312237160665506534621715)
                  ·
                    refine ⟨7968355740998259801932573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5312237160665506534621715 7968355740998259801932573)
                    ·
                      refine ⟨2988133402874347425724715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7968355740998259801932573 2988133402874347425724715)
                      ·
                        rfl

theorem cell23_5819369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 9, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 9, 1, 3].length) (baseStart_5819369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5819369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5819369 prefixEnd_5819369 := by exact prefixLift 5819369
  have htrace : WordTrace (prefixWord ++ tailWord_5819369) baseStart_5819369 baseEnd_5819369 := by
    simpa [prefixWord, tailWord_5819369, baseEnd_5819369] using wordTrace_append hprefix tailTrace_5819369
  have hstable : (prefixWord ++ tailWord_5819369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5819369).length < 2 ^ (prefixWord ++ tailWord_5819369).sum := by decide
  have hdescent : baseEnd_5819369 < baseStart_5819369 := by decide
  rcases family_descends (prefixWord ++ tailWord_5819369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
