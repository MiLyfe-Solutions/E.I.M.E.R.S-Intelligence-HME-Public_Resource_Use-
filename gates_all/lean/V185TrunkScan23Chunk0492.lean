import V185TrunkScan23Chunk0491

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2910926 : List Nat := [4, 1, 1, 1, 3, 2, 1, 2, 3, 2, 3]
def baseStart_2910926 : Nat := 118140960795 + 2910926 * 2 ^ 59
def prefixEnd_2910926 : Nat := 4983230072969 + 3 ^ 40 * 2910926 * 2
def baseEnd_2910926 : Nat := 1494704187669783222337901

theorem tailTrace_2910926 : CollatzResearch.WordTrace tailWord_2910926 prefixEnd_2910926 1494704187669783222337901 := by
  unfold tailWord_2910926
  simp only [CollatzResearch.WordTrace]
  refine ⟨13271274181527465428256079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70780128968146482284032421 13271274181527465428256079)
  ·
    refine ⟨19906911272291198142384119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13271274181527465428256079 19906911272291198142384119)
    ·
      refine ⟨29860366908436797213576179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19906911272291198142384119 29860366908436797213576179)
      ·
        refine ⟨44790550362655195820364269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29860366908436797213576179 44790550362655195820364269)
        ·
          refine ⟨16796456385995698432636601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44790550362655195820364269 16796456385995698432636601)
          ·
            refine ⟨12597342289496773824477451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16796456385995698432636601 12597342289496773824477451)
            ·
              refine ⟨18896013434245160736716177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12597342289496773824477451 18896013434245160736716177)
              ·
                refine ⟨14172010075683870552537133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18896013434245160736716177 14172010075683870552537133)
                ·
                  refine ⟨5314503778381451457201425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14172010075683870552537133 5314503778381451457201425)
                  ·
                    refine ⟨3985877833786088592901069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5314503778381451457201425 3985877833786088592901069)
                    ·
                      refine ⟨1494704187669783222337901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3985877833786088592901069 1494704187669783222337901)
                      ·
                        rfl

theorem cell23_2910926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 2, 3, 2, 3].length) (baseStart_2910926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2910926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2910926 prefixEnd_2910926 := by exact prefixLift 2910926
  have htrace : WordTrace (prefixWord ++ tailWord_2910926) baseStart_2910926 baseEnd_2910926 := by
    simpa [prefixWord, tailWord_2910926, baseEnd_2910926] using wordTrace_append hprefix tailTrace_2910926
  have hstable : (prefixWord ++ tailWord_2910926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2910926).length < 2 ^ (prefixWord ++ tailWord_2910926).sum := by decide
  have hdescent : baseEnd_2910926 < baseStart_2910926 := by decide
  rcases family_descends (prefixWord ++ tailWord_2910926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2910933 : List Nat := [1, 3, 2, 5, 1, 1, 2, 1, 1, 6]
def baseStart_2910933 : Nat := 118140960795 + 2910933 * 2 ^ 59
def prefixEnd_2910933 : Nat := 4983230072969 + 3 ^ 40 * 2910933 * 2
def baseEnd_2910933 : Nat := 498235927344788231650123

theorem tailTrace_2910933 : CollatzResearch.WordTrace tailWord_2910933 prefixEnd_2910933 498235927344788231650123 := by
  unfold tailWord_2910933
  simp only [CollatzResearch.WordTrace]
  refine ⟨106170448763194363621553453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70780299175462909081035635 106170448763194363621553453)
  ·
    refine ⟨39813918286197886358082545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106170448763194363621553453 39813918286197886358082545)
    ·
      refine ⟨29860438714648414768561909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39813918286197886358082545 29860438714648414768561909)
      ·
        refine ⟨2799416129498288884552679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29860438714648414768561909 2799416129498288884552679)
        ·
          refine ⟨4199124194247433326829019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2799416129498288884552679 4199124194247433326829019)
          ·
            refine ⟨6298686291371149990243529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4199124194247433326829019 6298686291371149990243529)
            ·
              refine ⟨4724014718528362492682647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6298686291371149990243529 4724014718528362492682647)
              ·
                refine ⟨7086022077792543739023971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4724014718528362492682647 7086022077792543739023971)
                ·
                  refine ⟨10629033116688815608535957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7086022077792543739023971 10629033116688815608535957)
                  ·
                    refine ⟨498235927344788231650123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10629033116688815608535957 498235927344788231650123)
                    ·
                      rfl

theorem cell23_2910933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 2, 1, 1, 6].length) (baseStart_2910933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2910933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2910933 prefixEnd_2910933 := by exact prefixLift 2910933
  have htrace : WordTrace (prefixWord ++ tailWord_2910933) baseStart_2910933 baseEnd_2910933 := by
    simpa [prefixWord, tailWord_2910933, baseEnd_2910933] using wordTrace_append hprefix tailTrace_2910933
  have hstable : (prefixWord ++ tailWord_2910933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2910933).length < 2 ^ (prefixWord ++ tailWord_2910933).sum := by decide
  have hdescent : baseEnd_2910933 < baseStart_2910933 := by decide
  rcases family_descends (prefixWord ++ tailWord_2910933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2910936 : List Nat := [2, 1, 2, 2, 3, 3, 2, 1, 1, 2, 4]
def baseStart_2910936 : Nat := 118140960795 + 2910936 * 2 ^ 59
def prefixEnd_2910936 : Nat := 4983230072969 + 3 ^ 40 * 2910936 * 2
def baseEnd_2910936 : Nat := 1494709322476328183212855

theorem tailTrace_2910936 : CollatzResearch.WordTrace tailWord_2910936 prefixEnd_2910936 1494709322476328183212855 := by
  unfold tailWord_2910936
  simp only [CollatzResearch.WordTrace]
  refine ⟨53085279091091747566956331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70780372121455663422608441 53085279091091747566956331)
  ·
    refine ⟨79627918636637621350434497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53085279091091747566956331 79627918636637621350434497)
    ·
      refine ⟨59720938977478216012825873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79627918636637621350434497 59720938977478216012825873)
      ·
        refine ⟨44790704233108662009619405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59720938977478216012825873 44790704233108662009619405)
        ·
          refine ⟨16796514087415748253607277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44790704233108662009619405 16796514087415748253607277)
          ·
            refine ⟨6298692782780905595102729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16796514087415748253607277 6298692782780905595102729)
            ·
              refine ⟨4724019587085679196327047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6298692782780905595102729 4724019587085679196327047)
              ·
                refine ⟨7086029380628518794490571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4724019587085679196327047 7086029380628518794490571)
                ·
                  refine ⟨10629044070942778191735857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7086029380628518794490571 10629044070942778191735857)
                  ·
                    refine ⟨7971783053207083643801893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10629044070942778191735857 7971783053207083643801893)
                    ·
                      refine ⟨1494709322476328183212855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7971783053207083643801893 1494709322476328183212855)
                      ·
                        rfl

theorem cell23_2910936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 2, 1, 1, 2, 4].length) (baseStart_2910936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2910936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2910936 prefixEnd_2910936 := by exact prefixLift 2910936
  have htrace : WordTrace (prefixWord ++ tailWord_2910936) baseStart_2910936 baseEnd_2910936 := by
    simpa [prefixWord, tailWord_2910936, baseEnd_2910936] using wordTrace_append hprefix tailTrace_2910936
  have hstable : (prefixWord ++ tailWord_2910936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2910936).length < 2 ^ (prefixWord ++ tailWord_2910936).sum := by decide
  have hdescent : baseEnd_2910936 < baseStart_2910936 := by decide
  rcases family_descends (prefixWord ++ tailWord_2910936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2910940 : List Nat := [2, 2, 5, 1, 1, 1, 1, 1, 5, 2, 2]
def baseStart_2910940 : Nat := 118140960795 + 2910940 * 2 ^ 59
def prefixEnd_2910940 : Nat := 4983230072969 + 3 ^ 40 * 2910940 * 2
def baseEnd_2910940 : Nat := 1494711376398946167562837

theorem tailTrace_2910940 : CollatzResearch.WordTrace tailWord_2910940 prefixEnd_2910940 1494711376398946167562837 := by
  unfold tailWord_2910940
  simp only [CollatzResearch.WordTrace]
  refine ⟨53085352037084501908529137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70780469382779335878038849 53085352037084501908529137)
  ·
    refine ⟨39814014027813376431396853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53085352037084501908529137 39814014027813376431396853)
    ·
      refine ⟨3732563815107504040443455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 39814014027813376431396853 3732563815107504040443455)
      ·
        refine ⟨5598845722661256060665183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3732563815107504040443455 5598845722661256060665183)
        ·
          refine ⟨8398268583991884090997775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5598845722661256060665183 8398268583991884090997775)
          ·
            refine ⟨12597402875987826136496663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8398268583991884090997775 12597402875987826136496663)
            ·
              refine ⟨18896104313981739204744995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12597402875987826136496663 18896104313981739204744995)
              ·
                refine ⟨28344156470972608807117493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18896104313981739204744995 28344156470972608807117493)
                ·
                  refine ⟨2657264669153682075667265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28344156470972608807117493 2657264669153682075667265)
                  ·
                    refine ⟨1992948501865261556750449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2657264669153682075667265 1992948501865261556750449)
                    ·
                      refine ⟨1494711376398946167562837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1992948501865261556750449 1494711376398946167562837)
                      ·
                        rfl

theorem cell23_2910940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 1, 5, 2, 2].length) (baseStart_2910940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2910940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2910940 prefixEnd_2910940 := by exact prefixLift 2910940
  have htrace : WordTrace (prefixWord ++ tailWord_2910940) baseStart_2910940 baseEnd_2910940 := by
    simpa [prefixWord, tailWord_2910940, baseEnd_2910940] using wordTrace_append hprefix tailTrace_2910940
  have hstable : (prefixWord ++ tailWord_2910940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2910940).length < 2 ^ (prefixWord ++ tailWord_2910940).sum := by decide
  have hdescent : baseEnd_2910940 < baseStart_2910940 := by decide
  rcases family_descends (prefixWord ++ tailWord_2910940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2910956 : List Nat := [2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 3]
def baseStart_2910956 : Nat := 118140960795 + 2910956 * 2 ^ 59
def prefixEnd_2910956 : Nat := 4983230072969 + 3 ^ 40 * 2910956 * 2
def baseEnd_2910956 : Nat := 1494719592089418104962763

theorem tailTrace_2910956 : CollatzResearch.WordTrace tailWord_2910956 prefixEnd_2910956 1494719592089418104962763 := by
  unfold tailWord_2910956
  simp only [CollatzResearch.WordTrace]
  refine ⟨53085643821055519274820361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70780858428074025699760481 53085643821055519274820361)
  ·
    refine ⟨39814232865791639456115271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53085643821055519274820361 39814232865791639456115271)
    ·
      refine ⟨59721349298687459184172907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39814232865791639456115271 59721349298687459184172907)
      ·
        refine ⟨89582023948031188776259361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59721349298687459184172907 89582023948031188776259361)
        ·
          refine ⟨67186517961023391582194521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89582023948031188776259361 67186517961023391582194521)
          ·
            refine ⟨50389888470767543686645891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67186517961023391582194521 50389888470767543686645891)
            ·
              refine ⟨75584832706151315529968837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50389888470767543686645891 75584832706151315529968837)
              ·
                refine ⟨14172156132403371661869157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 75584832706151315529968837 14172156132403371661869157)
                ·
                  refine ⟨2657279274825632186600467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14172156132403371661869157 2657279274825632186600467)
                  ·
                    refine ⟨3985918912238448279900701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2657279274825632186600467 3985918912238448279900701)
                    ·
                      refine ⟨1494719592089418104962763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3985918912238448279900701 1494719592089418104962763)
                      ·
                        rfl

theorem cell23_2910956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 3].length) (baseStart_2910956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2910956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2910956 prefixEnd_2910956 := by exact prefixLift 2910956
  have htrace : WordTrace (prefixWord ++ tailWord_2910956) baseStart_2910956 baseEnd_2910956 := by
    simpa [prefixWord, tailWord_2910956, baseEnd_2910956] using wordTrace_append hprefix tailTrace_2910956
  have hstable : (prefixWord ++ tailWord_2910956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2910956).length < 2 ^ (prefixWord ++ tailWord_2910956).sum := by decide
  have hdescent : baseEnd_2910956 < baseStart_2910956 := by decide
  rcases family_descends (prefixWord ++ tailWord_2910956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2910957 : List Nat := [1, 5, 1, 2, 1, 1, 4, 3, 1, 2, 2]
def baseStart_2910957 : Nat := 118140960795 + 2910957 * 2 ^ 59
def prefixEnd_2910957 : Nat := 4983230072969 + 3 ^ 40 * 2910957 * 2
def baseEnd_2910957 : Nat := 1494720105570072601050259

theorem tailTrace_2910957 : CollatzResearch.WordTrace tailWord_2910957 prefixEnd_2910957 1494720105570072601050259 := by
  unfold tailWord_2910957
  simp only [CollatzResearch.WordTrace]
  refine ⟨106171324115107415720427125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70780882743404943813618083 106171324115107415720427125)
  ·
    refine ⟨9953561635791320223790043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 106171324115107415720427125 9953561635791320223790043)
    ·
      refine ⟨14930342453686980335685065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9953561635791320223790043 14930342453686980335685065)
      ·
        refine ⟨11197756840265235251763799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14930342453686980335685065 11197756840265235251763799)
        ·
          refine ⟨16796635260397852877645699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11197756840265235251763799 16796635260397852877645699)
          ·
            refine ⟨25194952890596779316468549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16796635260397852877645699 25194952890596779316468549)
            ·
              refine ⟨4724053666986896121837853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25194952890596779316468549 4724053666986896121837853)
              ·
                refine ⟨1771520125120086045689195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4724053666986896121837853 1771520125120086045689195)
                ·
                  refine ⟨2657280187680129068533793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1771520125120086045689195 2657280187680129068533793)
                  ·
                    refine ⟨1992960140760096801400345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2657280187680129068533793 1992960140760096801400345)
                    ·
                      refine ⟨1494720105570072601050259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1992960140760096801400345 1494720105570072601050259)
                      ·
                        rfl

theorem cell23_2910957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 4, 3, 1, 2, 2].length) (baseStart_2910957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2910957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2910957 prefixEnd_2910957 := by exact prefixLift 2910957
  have htrace : WordTrace (prefixWord ++ tailWord_2910957) baseStart_2910957 baseEnd_2910957 := by
    simpa [prefixWord, tailWord_2910957, baseEnd_2910957] using wordTrace_append hprefix tailTrace_2910957
  have hstable : (prefixWord ++ tailWord_2910957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2910957).length < 2 ^ (prefixWord ++ tailWord_2910957).sum := by decide
  have hdescent : baseEnd_2910957 < baseStart_2910957 := by decide
  rcases family_descends (prefixWord ++ tailWord_2910957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2911013 : List Nat := [1, 3, 1, 2, 3, 1, 1, 1, 6, 2, 2]
def baseStart_2911013 : Nat := 118140960795 + 2911013 * 2 ^ 59
def prefixEnd_2911013 : Nat := 4983230072969 + 3 ^ 40 * 2911013 * 2
def baseEnd_2911013 : Nat := 1494748860486724381950001

theorem tailTrace_2911013 : CollatzResearch.WordTrace tailWord_2911013 prefixEnd_2911013 1494748860486724381950001 := by
  unfold tailWord_2911013
  simp only [CollatzResearch.WordTrace]
  refine ⟨106173366602904537284465693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70782244401936358189643795 106173366602904537284465693)
  ·
    refine ⟨39815012476089201481674635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106173366602904537284465693 39815012476089201481674635)
    ·
      refine ⟨59722518714133802222511953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39815012476089201481674635 59722518714133802222511953)
      ·
        refine ⟨44791889035600351666883965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59722518714133802222511953 44791889035600351666883965)
        ·
          refine ⟨16796958388350131875081487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44791889035600351666883965 16796958388350131875081487)
          ·
            refine ⟨25195437582525197812622231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16796958388350131875081487 25195437582525197812622231)
            ·
              refine ⟨37793156373787796718933347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25195437582525197812622231 37793156373787796718933347)
              ·
                refine ⟨56689734560681695078400021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37793156373787796718933347 56689734560681695078400021)
                ·
                  refine ⟨2657331307531954456800001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 56689734560681695078400021 2657331307531954456800001)
                  ·
                    refine ⟨1992998480648965842600001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2657331307531954456800001 1992998480648965842600001)
                    ·
                      refine ⟨1494748860486724381950001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1992998480648965842600001 1494748860486724381950001)
                      ·
                        rfl

theorem cell23_2911013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 1, 6, 2, 2].length) (baseStart_2911013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2911013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2911013 prefixEnd_2911013 := by exact prefixLift 2911013
  have htrace : WordTrace (prefixWord ++ tailWord_2911013) baseStart_2911013 baseEnd_2911013 := by
    simpa [prefixWord, tailWord_2911013, baseEnd_2911013] using wordTrace_append hprefix tailTrace_2911013
  have hstable : (prefixWord ++ tailWord_2911013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2911013).length < 2 ^ (prefixWord ++ tailWord_2911013).sum := by decide
  have hdescent : baseEnd_2911013 < baseStart_2911013 := by decide
  rcases family_descends (prefixWord ++ tailWord_2911013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2911016 : List Nat := [2, 1, 5, 1, 1, 1, 3, 1, 2, 1, 5]
def baseStart_2911016 : Nat := 118140960795 + 2911016 * 2 ^ 59
def prefixEnd_2911016 : Nat := 4983230072969 + 3 ^ 40 * 2911016 * 2
def baseEnd_2911016 : Nat := 1494750400928687870212487

theorem tailTrace_2911016 : CollatzResearch.WordTrace tailWord_2911016 prefixEnd_2911016 1494750400928687870212487 := by
  unfold tailWord_2911016
  simp only [CollatzResearch.WordTrace]
  refine ⟨53086738010946834398412451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70782317347929112531216601 53086738010946834398412451)
  ·
    refine ⟨79630107016420251597618677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53086738010946834398412451 79630107016420251597618677)
    ·
      refine ⟨7465322532789398587276751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 79630107016420251597618677 7465322532789398587276751)
      ·
        refine ⟨11197983799184097880915127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7465322532789398587276751 11197983799184097880915127)
        ·
          refine ⟨16796975698776146821372691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11197983799184097880915127 16796975698776146821372691)
          ·
            refine ⟨25195463548164220232059037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16796975698776146821372691 25195463548164220232059037)
            ·
              refine ⟨9448298830561582587022139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25195463548164220232059037 9448298830561582587022139)
              ·
                refine ⟨14172448245842373880533209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9448298830561582587022139 14172448245842373880533209)
                ·
                  refine ⟨10629336184381780410399907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14172448245842373880533209 10629336184381780410399907)
                  ·
                    refine ⟨15944004276572670615599861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10629336184381780410399907 15944004276572670615599861)
                    ·
                      refine ⟨1494750400928687870212487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15944004276572670615599861 1494750400928687870212487)
                      ·
                        rfl

theorem cell23_2911016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_2911016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2911016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2911016 prefixEnd_2911016 := by exact prefixLift 2911016
  have htrace : WordTrace (prefixWord ++ tailWord_2911016) baseStart_2911016 baseEnd_2911016 := by
    simpa [prefixWord, tailWord_2911016, baseEnd_2911016] using wordTrace_append hprefix tailTrace_2911016
  have hstable : (prefixWord ++ tailWord_2911016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2911016).length < 2 ^ (prefixWord ++ tailWord_2911016).sum := by decide
  have hdescent : baseEnd_2911016 < baseStart_2911016 := by decide
  rcases family_descends (prefixWord ++ tailWord_2911016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2911041 : List Nat := [1, 2, 5, 3, 2, 1, 2, 1, 2, 1, 3]
def baseStart_2911041 : Nat := 118140960795 + 2911041 * 2 ^ 59
def prefixEnd_2911041 : Nat := 4983230072969 + 3 ^ 40 * 2911041 * 2
def baseEnd_2911041 : Nat := 1494763237945050272399873

theorem tailTrace_2911041 : CollatzResearch.WordTrace tailWord_2911041 prefixEnd_2911041 1494763237945050272399873 := by
  unfold tailWord_2911041
  simp only [CollatzResearch.WordTrace]
  refine ⟨106174387846803098066484977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70782925231202065377656651 106174387846803098066484977)
  ·
    refine ⟨79630790885102323549863733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106174387846803098066484977 79630790885102323549863733)
    ·
      refine ⟨7465386645478342832799725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 79630790885102323549863733 7465386645478342832799725)
      ·
        refine ⟨2799519992054378562299897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7465386645478342832799725 2799519992054378562299897)
        ·
          refine ⟨2099639994040783921724923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2799519992054378562299897 2099639994040783921724923)
          ·
            refine ⟨3149459991061175882587385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2099639994040783921724923 3149459991061175882587385)
            ·
              refine ⟨2362094993295881911940539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3149459991061175882587385 2362094993295881911940539)
              ·
                refine ⟨3543142489943822867910809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2362094993295881911940539 3543142489943822867910809)
                ·
                  refine ⟨2657356867457867150933107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3543142489943822867910809 2657356867457867150933107)
                  ·
                    refine ⟨3986035301186800726399661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2657356867457867150933107 3986035301186800726399661)
                    ·
                      refine ⟨1494763237945050272399873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3986035301186800726399661 1494763237945050272399873)
                      ·
                        rfl

theorem cell23_2911041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_2911041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2911041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2911041 prefixEnd_2911041 := by exact prefixLift 2911041
  have htrace : WordTrace (prefixWord ++ tailWord_2911041) baseStart_2911041 baseEnd_2911041 := by
    simpa [prefixWord, tailWord_2911041, baseEnd_2911041] using wordTrace_append hprefix tailTrace_2911041
  have hstable : (prefixWord ++ tailWord_2911041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2911041).length < 2 ^ (prefixWord ++ tailWord_2911041).sum := by decide
  have hdescent : baseEnd_2911041 < baseStart_2911041 := by decide
  rcases family_descends (prefixWord ++ tailWord_2911041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2911066 : List Nat := [3, 1, 1, 2, 1, 4, 1, 3, 2, 5]
def baseStart_2911066 : Nat := 118140960795 + 2911066 * 2 ^ 59
def prefixEnd_2911066 : Nat := 4983230072969 + 3 ^ 40 * 2911066 * 2
def baseEnd_2911066 : Nat := 498258691653804224862419

theorem tailTrace_2911066 : CollatzResearch.WordTrace tailWord_2911066 prefixEnd_2911066 498258691653804224862419 := by
  unfold tailWord_2911066
  simp only [CollatzResearch.WordTrace]
  refine ⟨26543824917928131834036263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70783533114475018224096701 26543824917928131834036263)
  ·
    refine ⟨39815737376892197751054395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26543824917928131834036263 39815737376892197751054395)
    ·
      refine ⟨59723606065338296626581593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39815737376892197751054395 59723606065338296626581593)
      ·
        refine ⟨44792704549003722469936195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59723606065338296626581593 44792704549003722469936195)
        ·
          refine ⟨67189056823505583704904293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44792704549003722469936195 67189056823505583704904293)
          ·
            refine ⟨12597948154407296944669555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67189056823505583704904293 12597948154407296944669555)
            ·
              refine ⟨18896922231610945417004333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12597948154407296944669555 18896922231610945417004333)
              ·
                refine ⟨7086345836854104531376625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18896922231610945417004333 7086345836854104531376625)
                ·
                  refine ⟨5314759377640578398532469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7086345836854104531376625 5314759377640578398532469)
                  ·
                    refine ⟨498258691653804224862419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5314759377640578398532469 498258691653804224862419)
                    ·
                      rfl

theorem cell23_2911066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 3, 2, 5].length) (baseStart_2911066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2911066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2911066 prefixEnd_2911066 := by exact prefixLift 2911066
  have htrace : WordTrace (prefixWord ++ tailWord_2911066) baseStart_2911066 baseEnd_2911066 := by
    simpa [prefixWord, tailWord_2911066, baseEnd_2911066] using wordTrace_append hprefix tailTrace_2911066
  have hstable : (prefixWord ++ tailWord_2911066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2911066).length < 2 ^ (prefixWord ++ tailWord_2911066).sum := by decide
  have hdescent : baseEnd_2911066 < baseStart_2911066 := by decide
  rcases family_descends (prefixWord ++ tailWord_2911066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2911076 : List Nat := [2, 3, 1, 1, 4, 1, 1, 2, 1, 2, 5]
def baseStart_2911076 : Nat := 118140960795 + 2911076 * 2 ^ 59
def prefixEnd_2911076 : Nat := 4983230072969 + 3 ^ 40 * 2911076 * 2
def baseEnd_2911076 : Nat := 1494781209767957635462211

theorem tailTrace_2911076 : CollatzResearch.WordTrace tailWord_2911076 prefixEnd_2911076 1494781209767957635462211 := by
  unfold tailWord_2911076
  simp only [CollatzResearch.WordTrace]
  refine ⟨53087832200838149522004541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70783776267784199362672721 53087832200838149522004541)
  ·
    refine ⟨19907937075314306070751703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53087832200838149522004541 19907937075314306070751703)
    ·
      refine ⟨29861905612971459106127555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19907937075314306070751703 29861905612971459106127555)
      ·
        refine ⟨44792858419457188659191333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29861905612971459106127555 44792858419457188659191333)
        ·
          refine ⟨8398660953648222873598375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44792858419457188659191333 8398660953648222873598375)
          ·
            refine ⟨12597991430472334310397563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8398660953648222873598375 12597991430472334310397563)
            ·
              refine ⟨18896987145708501465596345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12597991430472334310397563 18896987145708501465596345)
              ·
                refine ⟨14172740359281376099197259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18896987145708501465596345 14172740359281376099197259)
                ·
                  refine ⟨21259110538922064148795889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14172740359281376099197259 21259110538922064148795889)
                  ·
                    refine ⟨15944332904191548111596917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21259110538922064148795889 15944332904191548111596917)
                    ·
                      refine ⟨1494781209767957635462211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15944332904191548111596917 1494781209767957635462211)
                      ·
                        rfl

theorem cell23_2911076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 2, 1, 2, 5].length) (baseStart_2911076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2911076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2911076 prefixEnd_2911076 := by exact prefixLift 2911076
  have htrace : WordTrace (prefixWord ++ tailWord_2911076) baseStart_2911076 baseEnd_2911076 := by
    simpa [prefixWord, tailWord_2911076, baseEnd_2911076] using wordTrace_append hprefix tailTrace_2911076
  have hstable : (prefixWord ++ tailWord_2911076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2911076).length < 2 ^ (prefixWord ++ tailWord_2911076).sum := by decide
  have hdescent : baseEnd_2911076 < baseStart_2911076 := by decide
  rcases family_descends (prefixWord ++ tailWord_2911076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2911113 : List Nat := [1, 2, 1, 1, 5, 3, 1, 2, 3, 4]
def baseStart_2911113 : Nat := 118140960795 + 2911113 * 2 ^ 59
def prefixEnd_2911113 : Nat := 4983230072969 + 3 ^ 40 * 2911113 * 2
def baseEnd_2911113 : Nat := 498266736184057996899847

theorem tailTrace_2911113 : CollatzResearch.WordTrace tailWord_2911113 prefixEnd_2911113 498266736184057996899847 := by
  unfold tailWord_2911113
  simp only [CollatzResearch.WordTrace]
  refine ⟨106177013902542254363105993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70784675935028169575403995 106177013902542254363105993)
  ·
    refine ⟨79632760426906690772329495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106177013902542254363105993 79632760426906690772329495)
    ·
      refine ⟨119449140640360036158494243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79632760426906690772329495 119449140640360036158494243)
      ·
        refine ⟨179173710960540054237741365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119449140640360036158494243 179173710960540054237741365)
        ·
          refine ⟨16797535402550630084788253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 179173710960540054237741365 16797535402550630084788253)
          ·
            refine ⟨6299075775956486281795595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16797535402550630084788253 6299075775956486281795595)
            ·
              refine ⟨9448613663934729422693393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6299075775956486281795595 9448613663934729422693393)
              ·
                refine ⟨7086460247951047067020045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9448613663934729422693393 7086460247951047067020045)
                ·
                  refine ⟨2657422592981642650132517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7086460247951047067020045 2657422592981642650132517)
                  ·
                    refine ⟨498266736184057996899847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2657422592981642650132517 498266736184057996899847)
                    ·
                      rfl

theorem cell23_2911113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 2, 3, 4].length) (baseStart_2911113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2911113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2911113 prefixEnd_2911113 := by exact prefixLift 2911113
  have htrace : WordTrace (prefixWord ++ tailWord_2911113) baseStart_2911113 baseEnd_2911113 := by
    simpa [prefixWord, tailWord_2911113, baseEnd_2911113] using wordTrace_append hprefix tailTrace_2911113
  have hstable : (prefixWord ++ tailWord_2911113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2911113).length < 2 ^ (prefixWord ++ tailWord_2911113).sum := by decide
  have hdescent : baseEnd_2911113 < baseStart_2911113 := by decide
  rcases family_descends (prefixWord ++ tailWord_2911113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2911143 : List Nat := [1, 1, 6, 1, 3, 1, 1, 1, 8]
def baseStart_2911143 : Nat := 118140960795 + 2911143 * 2 ^ 59
def prefixEnd_2911143 : Nat := 4983230072969 + 3 ^ 40 * 2911143 * 2
def baseEnd_2911143 : Nat := 166090623663534319258267

theorem tailTrace_2911143 : CollatzResearch.WordTrace tailWord_2911143 prefixEnd_2911143 166090623663534319258267 := by
  unfold tailWord_2911143
  simp only [CollatzResearch.WordTrace]
  refine ⟨106178108092433569486698083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70785405394955712991132055 106178108092433569486698083)
  ·
    refine ⟨159267162138650354230047125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106178108092433569486698083 159267162138650354230047125)
    ·
      refine ⟨7465648225249235354533459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 159267162138650354230047125 7465648225249235354533459)
      ·
        refine ⟨11198472337873853031800189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7465648225249235354533459 11198472337873853031800189)
        ·
          refine ⟨4199427126702694886925071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11198472337873853031800189 4199427126702694886925071)
          ·
            refine ⟨6299140690054042330387607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4199427126702694886925071 6299140690054042330387607)
            ·
              refine ⟨9448711035081063495581411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6299140690054042330387607 9448711035081063495581411)
              ·
                refine ⟨14173066552621595243372117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9448711035081063495581411 14173066552621595243372117)
                ·
                  refine ⟨166090623663534319258267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14173066552621595243372117 166090623663534319258267)
                  ·
                    rfl

theorem cell23_2911143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 1, 8].length) (baseStart_2911143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2911143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2911143 prefixEnd_2911143 := by exact prefixLift 2911143
  have htrace : WordTrace (prefixWord ++ tailWord_2911143) baseStart_2911143 baseEnd_2911143 := by
    simpa [prefixWord, tailWord_2911143, baseEnd_2911143] using wordTrace_append hprefix tailTrace_2911143
  have hstable : (prefixWord ++ tailWord_2911143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2911143).length < 2 ^ (prefixWord ++ tailWord_2911143).sum := by decide
  have hdescent : baseEnd_2911143 < baseStart_2911143 := by decide
  rcases family_descends (prefixWord ++ tailWord_2911143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2911180 : List Nat := [2, 2, 1, 4, 1, 1, 2, 3, 2, 3, 2]
def baseStart_2911180 : Nat := 118140960795 + 2911180 * 2 ^ 59
def prefixEnd_2911180 : Nat := 4983230072969 + 3 ^ 40 * 2911180 * 2
def baseEnd_2911180 : Nat := 1494834611756025228561733

theorem tailTrace_2911180 : CollatzResearch.WordTrace tailWord_2911180 prefixEnd_2911180 1494834611756025228561733 := by
  unfold tailWord_2911180
  simp only [CollatzResearch.WordTrace]
  refine ⟨53089728796649762402897497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70786305062199683203863329 53089728796649762402897497)
  ·
    refine ⟨39817296597487321802173123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53089728796649762402897497 39817296597487321802173123)
    ·
      refine ⟨59725944896230982703259685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39817296597487321802173123 59725944896230982703259685)
      ·
        refine ⟨11198614668043309256861191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59725944896230982703259685 11198614668043309256861191)
        ·
          refine ⟨16797922002064963885291787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11198614668043309256861191 16797922002064963885291787)
          ·
            refine ⟨25196883003097445827937681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16797922002064963885291787 25196883003097445827937681)
            ·
              refine ⟨18897662252323084370953261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25196883003097445827937681 18897662252323084370953261)
              ·
                refine ⟨7086623344621156639107473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18897662252323084370953261 7086623344621156639107473)
                ·
                  refine ⟨5314967508465867479330605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7086623344621156639107473 5314967508465867479330605)
                  ·
                    refine ⟨1993112815674700304748977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5314967508465867479330605 1993112815674700304748977)
                    ·
                      refine ⟨1494834611756025228561733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1993112815674700304748977 1494834611756025228561733)
                      ·
                        rfl

theorem cell23_2911180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 3, 2, 3, 2].length) (baseStart_2911180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2911180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2911180 prefixEnd_2911180 := by exact prefixLift 2911180
  have htrace : WordTrace (prefixWord ++ tailWord_2911180) baseStart_2911180 baseEnd_2911180 := by
    simpa [prefixWord, tailWord_2911180, baseEnd_2911180] using wordTrace_append hprefix tailTrace_2911180
  have hstable : (prefixWord ++ tailWord_2911180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2911180).length < 2 ^ (prefixWord ++ tailWord_2911180).sum := by decide
  have hdescent : baseEnd_2911180 < baseStart_2911180 := by decide
  rcases family_descends (prefixWord ++ tailWord_2911180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2911197 : List Nat := [1, 4, 3, 1, 2, 2, 1, 2, 2, 3, 2]
def baseStart_2911197 : Nat := 118140960795 + 2911197 * 2 ^ 59
def prefixEnd_2911197 : Nat := 4983230072969 + 3 ^ 40 * 2911197 * 2
def baseEnd_2911197 : Nat := 1494843340927151662049155

theorem tailTrace_2911197 : CollatzResearch.WordTrace tailWord_2911197 prefixEnd_2911197 1494843340927151662049155 := by
  unfold tailWord_2911197
  simp only [CollatzResearch.WordTrace]
  refine ⟨106180077634237936709163845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70786718422825291139442563 106180077634237936709163845)
  ·
    refine ⟨19908764556419613132968221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 106180077634237936709163845 19908764556419613132968221)
    ·
      refine ⟨7465786708657354924863083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19908764556419613132968221 7465786708657354924863083)
      ·
        refine ⟨11198680062986032387294625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7465786708657354924863083 11198680062986032387294625)
        ·
          refine ⟨8399010047239524290470969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11198680062986032387294625 8399010047239524290470969)
          ·
            refine ⟨6299257535429643217853227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8399010047239524290470969 6299257535429643217853227)
            ·
              refine ⟨9448886303144464826779841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6299257535429643217853227 9448886303144464826779841)
              ·
                refine ⟨7086664727358348620084881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9448886303144464826779841 7086664727358348620084881)
                ·
                  refine ⟨5314998545518761465063661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7086664727358348620084881 5314998545518761465063661)
                  ·
                    refine ⟨1993124454569535549398873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5314998545518761465063661 1993124454569535549398873)
                    ·
                      refine ⟨1494843340927151662049155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1993124454569535549398873 1494843340927151662049155)
                      ·
                        rfl

theorem cell23_2911197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 2, 2, 3, 2].length) (baseStart_2911197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2911197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2911197 prefixEnd_2911197 := by exact prefixLift 2911197
  have htrace : WordTrace (prefixWord ++ tailWord_2911197) baseStart_2911197 baseEnd_2911197 := by
    simpa [prefixWord, tailWord_2911197, baseEnd_2911197] using wordTrace_append hprefix tailTrace_2911197
  have hstable : (prefixWord ++ tailWord_2911197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2911197).length < 2 ^ (prefixWord ++ tailWord_2911197).sum := by decide
  have hdescent : baseEnd_2911197 < baseStart_2911197 := by decide
  rcases family_descends (prefixWord ++ tailWord_2911197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2911203 : List Nat := [1, 1, 1, 6, 1, 1, 1, 3, 4, 4]
def baseStart_2911203 : Nat := 118140960795 + 2911203 * 2 ^ 59
def prefixEnd_2911203 : Nat := 4983230072969 + 3 ^ 40 * 2911203 * 2
def baseEnd_2911203 : Nat := 498282140603692879524709

theorem tailTrace_2911203 : CollatzResearch.WordTrace tailWord_2911203 prefixEnd_2911203 498282140603692879524709 := by
  unfold tailWord_2911203
  simp only [CollatzResearch.WordTrace]
  refine ⟨106180296472216199733882263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70786864314810799822588175 106180296472216199733882263)
  ·
    refine ⟨159270444708324299600823395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106180296472216199733882263 159270444708324299600823395)
    ·
      refine ⟨238905667062486449401235093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159270444708324299600823395 238905667062486449401235093)
      ·
        refine ⟨11198703143554052315682895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 238905667062486449401235093 11198703143554052315682895)
        ·
          refine ⟨16798054715331078473524343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11198703143554052315682895 16798054715331078473524343)
          ·
            refine ⟨25197082072996617710286515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16798054715331078473524343 25197082072996617710286515)
            ·
              refine ⟨37795623109494926565429773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25197082072996617710286515 37795623109494926565429773)
              ·
                refine ⟨14173358666060597462036165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37795623109494926565429773 14173358666060597462036165)
                ·
                  refine ⟨2657504749886362024131781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14173358666060597462036165 2657504749886362024131781)
                  ·
                    refine ⟨498282140603692879524709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2657504749886362024131781 498282140603692879524709)
                    ·
                      rfl

theorem cell23_2911203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 3, 4, 4].length) (baseStart_2911203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2911203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2911203 prefixEnd_2911203 := by exact prefixLift 2911203
  have htrace : WordTrace (prefixWord ++ tailWord_2911203) baseStart_2911203 baseEnd_2911203 := by
    simpa [prefixWord, tailWord_2911203, baseEnd_2911203] using wordTrace_append hprefix tailTrace_2911203
  have hstable : (prefixWord ++ tailWord_2911203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2911203).length < 2 ^ (prefixWord ++ tailWord_2911203).sum := by decide
  have hdescent : baseEnd_2911203 < baseStart_2911203 := by decide
  rcases family_descends (prefixWord ++ tailWord_2911203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2911243 : List Nat := [1, 1, 1, 1, 6, 2, 1, 1, 3, 3, 3]
def baseStart_2911243 : Nat := 118140960795 + 2911243 * 2 ^ 59
def prefixEnd_2911243 : Nat := 4983230072969 + 3 ^ 40 * 2911243 * 2
def baseEnd_2911243 : Nat := 1494866961037258482073943

theorem tailTrace_2911243 : CollatzResearch.WordTrace tailWord_2911243 prefixEnd_2911243 1494866961037258482073943 := by
  unfold tailWord_2911243
  simp only [CollatzResearch.WordTrace]
  refine ⟨106181755392071286565338383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70787836928047524376892255 106181755392071286565338383)
  ·
    refine ⟨159272633088106929848007575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106181755392071286565338383 159272633088106929848007575)
    ·
      refine ⟨238908949632160394772011363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159272633088106929848007575 238908949632160394772011363)
      ·
        refine ⟨358363424448240592158017045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238908949632160394772011363 358363424448240592158017045)
        ·
          refine ⟨16798285521011277757407049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 358363424448240592158017045 16798285521011277757407049)
          ·
            refine ⟨12598714140758458318055287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16798285521011277757407049 12598714140758458318055287)
            ·
              refine ⟨18898071211137687477082931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12598714140758458318055287 18898071211137687477082931)
              ·
                refine ⟨28347106816706531215624397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18898071211137687477082931 28347106816706531215624397)
                ·
                  refine ⟨10630165056264949205859149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28347106816706531215624397 10630165056264949205859149)
                  ·
                    refine ⟨3986311896099355952197181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10630165056264949205859149 3986311896099355952197181)
                    ·
                      refine ⟨1494866961037258482073943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3986311896099355952197181 1494866961037258482073943)
                      ·
                        rfl

theorem cell23_2911243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 1, 3, 3, 3].length) (baseStart_2911243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2911243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2911243 prefixEnd_2911243 := by exact prefixLift 2911243
  have htrace : WordTrace (prefixWord ++ tailWord_2911243) baseStart_2911243 baseEnd_2911243 := by
    simpa [prefixWord, tailWord_2911243, baseEnd_2911243] using wordTrace_append hprefix tailTrace_2911243
  have hstable : (prefixWord ++ tailWord_2911243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2911243).length < 2 ^ (prefixWord ++ tailWord_2911243).sum := by decide
  have hdescent : baseEnd_2911243 < baseStart_2911243 := by decide
  rcases family_descends (prefixWord ++ tailWord_2911243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2911250 : List Nat := [3, 2, 5, 1, 12]
def baseStart_2911250 : Nat := 118140960795 + 2911250 * 2 ^ 59
def prefixEnd_2911250 : Nat := 4983230072969 + 3 ^ 40 * 2911250 * 2
def baseEnd_2911250 : Nat := 2050576893555336014659

theorem tailTrace_2911250 : CollatzResearch.WordTrace tailWord_2911250 prefixEnd_2911250 2050576893555336014659 := by
  unfold tailWord_2911250
  simp only [CollatzResearch.WordTrace]
  refine ⟨26545502675761481690210801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70788007135363951173895469 26545502675761481690210801)
  ·
    refine ⟨19909127006821111267658101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26545502675761481690210801 19909127006821111267658101)
    ·
      refine ⟨1866480656889479181342947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19909127006821111267658101 1866480656889479181342947)
      ·
        refine ⟨2799720985334218772014421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1866480656889479181342947 2799720985334218772014421)
        ·
          refine ⟨2050576893555336014659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 2799720985334218772014421 2050576893555336014659)
          ·
            rfl

theorem cell23_2911250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 12].length) (baseStart_2911250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2911250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2911250 prefixEnd_2911250 := by exact prefixLift 2911250
  have htrace : WordTrace (prefixWord ++ tailWord_2911250) baseStart_2911250 baseEnd_2911250 := by
    simpa [prefixWord, tailWord_2911250, baseEnd_2911250] using wordTrace_append hprefix tailTrace_2911250
  have hstable : (prefixWord ++ tailWord_2911250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2911250).length < 2 ^ (prefixWord ++ tailWord_2911250).sum := by decide
  have hdescent : baseEnd_2911250 < baseStart_2911250 := by decide
  rcases family_descends (prefixWord ++ tailWord_2911250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2911261 : List Nat := [1, 4, 2, 2, 3, 1, 1, 4, 1, 2, 2]
def baseStart_2911261 : Nat := 118140960795 + 2911261 * 2 ^ 59
def prefixEnd_2911261 : Nat := 4983230072969 + 3 ^ 40 * 2911261 * 2
def baseEnd_2911261 : Nat := 1494876203689039411648861

theorem tailTrace_2911261 : CollatzResearch.WordTrace tailWord_2911261 prefixEnd_2911261 1494876203689039411648861 := by
  unfold tailWord_2911261
  simp only [CollatzResearch.WordTrace]
  refine ⟨106182411906006075639493637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70788274604004050426329091 106182411906006075639493637)
  ·
    refine ⟨19909202232376139182405057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 106182411906006075639493637 19909202232376139182405057)
    ·
      refine ⟨14931901674282104386803793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19909202232376139182405057 14931901674282104386803793)
      ·
        refine ⟨11198926255711578290102845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14931901674282104386803793 11198926255711578290102845)
        ·
          refine ⟨4199597345891841858788567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11198926255711578290102845 4199597345891841858788567)
          ·
            refine ⟨6299396018837762788182851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4199597345891841858788567 6299396018837762788182851)
            ·
              refine ⟨9449094028256644182274277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6299396018837762788182851 9449094028256644182274277)
              ·
                refine ⟨1771705130298120784176427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9449094028256644182274277 1771705130298120784176427)
                ·
                  refine ⟨2657557695447181176264641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1771705130298120784176427 2657557695447181176264641)
                  ·
                    refine ⟨1993168271585385882198481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2657557695447181176264641 1993168271585385882198481)
                    ·
                      refine ⟨1494876203689039411648861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1993168271585385882198481 1494876203689039411648861)
                      ·
                        rfl

theorem cell23_2911261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 4, 1, 2, 2].length) (baseStart_2911261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2911261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2911261 prefixEnd_2911261 := by exact prefixLift 2911261
  have htrace : WordTrace (prefixWord ++ tailWord_2911261) baseStart_2911261 baseEnd_2911261 := by
    simpa [prefixWord, tailWord_2911261, baseEnd_2911261] using wordTrace_append hprefix tailTrace_2911261
  have hstable : (prefixWord ++ tailWord_2911261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2911261).length < 2 ^ (prefixWord ++ tailWord_2911261).sum := by decide
  have hdescent : baseEnd_2911261 < baseStart_2911261 := by decide
  rcases family_descends (prefixWord ++ tailWord_2911261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2911313 : List Nat := [1, 2, 2, 1, 3, 1, 3, 2, 2, 2, 4]
def baseStart_2911313 : Nat := 118140960795 + 2911313 * 2 ^ 59
def prefixEnd_2911313 : Nat := 4983230072969 + 3 ^ 40 * 2911313 * 2
def baseEnd_2911313 : Nat := 1494902904683073208198621

theorem tailTrace_2911313 : CollatzResearch.WordTrace tailWord_2911313 prefixEnd_2911313 1494902904683073208198621 := by
  unfold tailWord_2911313
  simp only [CollatzResearch.WordTrace]
  refine ⟨106184308501817688520386593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70789539001211792346924395 106184308501817688520386593)
  ·
    refine ⟨79638231376363266390289945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106184308501817688520386593 79638231376363266390289945)
    ·
      refine ⟨59728673532272449792717459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79638231376363266390289945 59728673532272449792717459)
      ·
        refine ⟨89593010298408674689076189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59728673532272449792717459 89593010298408674689076189)
        ·
          refine ⟨33597378861903253008403571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89593010298408674689076189 33597378861903253008403571)
          ·
            refine ⟨50396068292854879512605357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33597378861903253008403571 50396068292854879512605357)
            ·
              refine ⟨18898525609820579817227009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50396068292854879512605357 18898525609820579817227009)
              ·
                refine ⟨14173894207365434862920257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18898525609820579817227009 14173894207365434862920257)
                ·
                  refine ⟨10630420655524076147190193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14173894207365434862920257 10630420655524076147190193)
                  ·
                    refine ⟨7972815491643057110392645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10630420655524076147190193 7972815491643057110392645)
                    ·
                      refine ⟨1494902904683073208198621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7972815491643057110392645 1494902904683073208198621)
                      ·
                        rfl

theorem cell23_2911313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 2, 2, 2, 4].length) (baseStart_2911313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2911313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2911313 prefixEnd_2911313 := by exact prefixLift 2911313
  have htrace : WordTrace (prefixWord ++ tailWord_2911313) baseStart_2911313 baseEnd_2911313 := by
    simpa [prefixWord, tailWord_2911313, baseEnd_2911313] using wordTrace_append hprefix tailTrace_2911313
  have hstable : (prefixWord ++ tailWord_2911313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2911313).length < 2 ^ (prefixWord ++ tailWord_2911313).sum := by decide
  have hdescent : baseEnd_2911313 < baseStart_2911313 := by decide
  rcases family_descends (prefixWord ++ tailWord_2911313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2911317 : List Nat := [1, 3, 2, 2, 1, 2, 3, 1, 4, 2, 2]
def baseStart_2911317 : Nat := 118140960795 + 2911317 * 2 ^ 59
def prefixEnd_2911317 : Nat := 4983230072969 + 3 ^ 40 * 2911317 * 2
def baseEnd_2911317 : Nat := 1494904958605691192548603

theorem tailTrace_2911317 : CollatzResearch.WordTrace tailWord_2911317 prefixEnd_2911317 1494904958605691192548603 := by
  unfold tailWord_2911317
  simp only [CollatzResearch.WordTrace]
  refine ⟨106184454393803197203532205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70789636262535464802354803 106184454393803197203532205)
  ·
    refine ⟨39819170397676198951324577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106184454393803197203532205 39819170397676198951324577)
    ·
      refine ⟨29864377798257149213493433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39819170397676198951324577 29864377798257149213493433)
      ·
        refine ⟨22398283348692861910120075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29864377798257149213493433 22398283348692861910120075)
        ·
          refine ⟨33597425023039292865180113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22398283348692861910120075 33597425023039292865180113)
          ·
            refine ⟨25198068767279469648885085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33597425023039292865180113 25198068767279469648885085)
            ·
              refine ⟨9449275787729801118331907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25198068767279469648885085 9449275787729801118331907)
              ·
                refine ⟨14173913681594701677497861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9449275787729801118331907 14173913681594701677497861)
                ·
                  refine ⟨2657608815299006564530849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14173913681594701677497861 2657608815299006564530849)
                  ·
                    refine ⟨1993206611474254923398137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2657608815299006564530849 1993206611474254923398137)
                    ·
                      refine ⟨1494904958605691192548603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1993206611474254923398137 1494904958605691192548603)
                      ·
                        rfl

theorem cell23_2911317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 1, 4, 2, 2].length) (baseStart_2911317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2911317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2911317 prefixEnd_2911317 := by exact prefixLift 2911317
  have htrace : WordTrace (prefixWord ++ tailWord_2911317) baseStart_2911317 baseEnd_2911317 := by
    simpa [prefixWord, tailWord_2911317, baseEnd_2911317] using wordTrace_append hprefix tailTrace_2911317
  have hstable : (prefixWord ++ tailWord_2911317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2911317).length < 2 ^ (prefixWord ++ tailWord_2911317).sum := by decide
  have hdescent : baseEnd_2911317 < baseStart_2911317 := by decide
  rcases family_descends (prefixWord ++ tailWord_2911317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2911363 : List Nat := [1, 1, 1, 3, 3, 2, 2, 2, 1, 2, 5]
def baseStart_2911363 : Nat := 118140960795 + 2911363 * 2 ^ 59
def prefixEnd_2911363 : Nat := 4983230072969 + 3 ^ 40 * 2911363 * 2
def baseEnd_2911363 : Nat := 1494928578715798012573391

theorem tailTrace_2911363 : CollatzResearch.WordTrace tailWord_2911363 prefixEnd_2911363 1494928578715798012573391 := by
  unfold tailWord_2911363
  simp only [CollatzResearch.WordTrace]
  refine ⟨106186132151636547059706743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70790754767757698039804495 106186132151636547059706743)
  ·
    refine ⟨159279198227454820589560115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106186132151636547059706743 159279198227454820589560115)
    ·
      refine ⟨238918797341182230884340173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159279198227454820589560115 238918797341182230884340173)
      ·
        refine ⟨89594549002943336581627565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 238918797341182230884340173 89594549002943336581627565)
        ·
          refine ⟨33597955876103751218110337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89594549002943336581627565 33597955876103751218110337)
          ·
            refine ⟨25198466907077813413582753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33597955876103751218110337 25198466907077813413582753)
            ·
              refine ⟨18898850180308360060187065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25198466907077813413582753 18898850180308360060187065)
              ·
                refine ⟨14174137635231270045140299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18898850180308360060187065 14174137635231270045140299)
                ·
                  refine ⟨21261206452846905067710449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14174137635231270045140299 21261206452846905067710449)
                  ·
                    refine ⟨15945904839635178800782837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21261206452846905067710449 15945904839635178800782837)
                    ·
                      refine ⟨1494928578715798012573391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15945904839635178800782837 1494928578715798012573391)
                      ·
                        rfl

theorem cell23_2911363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 2, 1, 2, 5].length) (baseStart_2911363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2911363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2911363 prefixEnd_2911363 := by exact prefixLift 2911363
  have htrace : WordTrace (prefixWord ++ tailWord_2911363) baseStart_2911363 baseEnd_2911363 := by
    simpa [prefixWord, tailWord_2911363, baseEnd_2911363] using wordTrace_append hprefix tailTrace_2911363
  have hstable : (prefixWord ++ tailWord_2911363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2911363).length < 2 ^ (prefixWord ++ tailWord_2911363).sum := by decide
  have hdescent : baseEnd_2911363 < baseStart_2911363 := by decide
  rcases family_descends (prefixWord ++ tailWord_2911363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2911370 : List Nat := [3, 1, 2, 3, 1, 1, 3, 2, 2, 5]
def baseStart_2911370 : Nat := 118140960795 + 2911370 * 2 ^ 59
def prefixEnd_2911370 : Nat := 4983230072969 + 3 ^ 40 * 2911370 * 2
def baseEnd_2911370 : Nat := 498310724360126495061953

theorem tailTrace_2911370 : CollatzResearch.WordTrace tailWord_2911370 prefixEnd_2911370 498310724360126495061953 := by
  unfold tailWord_2911370
  simp only [CollatzResearch.WordTrace]
  refine ⟨26546596865652796813802891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70790924975074124836807709 26546596865652796813802891)
  ·
    refine ⟨39819895298479195220704337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26546596865652796813802891 39819895298479195220704337)
    ·
      refine ⟨29864921473859396415528253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39819895298479195220704337 29864921473859396415528253)
      ·
        refine ⟨11199345552697273655823095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29864921473859396415528253 11199345552697273655823095)
        ·
          refine ⟨16799018329045910483734643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11199345552697273655823095 16799018329045910483734643)
          ·
            refine ⟨25198527493568865725601965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16799018329045910483734643 25198527493568865725601965)
            ·
              refine ⟨9449447810088324647100737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25198527493568865725601965 9449447810088324647100737)
              ·
                refine ⟨7087085857566243485325553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9449447810088324647100737 7087085857566243485325553)
                ·
                  refine ⟨5315314393174682613994165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7087085857566243485325553 5315314393174682613994165)
                  ·
                    refine ⟨498310724360126495061953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5315314393174682613994165 498310724360126495061953)
                    ·
                      rfl

theorem cell23_2911370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 2, 2, 5].length) (baseStart_2911370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2911370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2911370 prefixEnd_2911370 := by exact prefixLift 2911370
  have htrace : WordTrace (prefixWord ++ tailWord_2911370) baseStart_2911370 baseEnd_2911370 := by
    simpa [prefixWord, tailWord_2911370, baseEnd_2911370] using wordTrace_append hprefix tailTrace_2911370
  have hstable : (prefixWord ++ tailWord_2911370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2911370).length < 2 ^ (prefixWord ++ tailWord_2911370).sum := by decide
  have hdescent : baseEnd_2911370 < baseStart_2911370 := by decide
  rcases family_descends (prefixWord ++ tailWord_2911370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2911374 : List Nat := [4, 1, 1, 3, 2, 2, 3, 2, 5]
def baseStart_2911374 : Nat := 118140960795 + 2911374 * 2 ^ 59
def prefixEnd_2911374 : Nat := 4983230072969 + 3 ^ 40 * 2911374 * 2
def baseEnd_2911374 : Nat := 166103803000333052170649

theorem tailTrace_2911374 : CollatzResearch.WordTrace tailWord_2911374 prefixEnd_2911374 166103803000333052170649 := by
  unfold tailWord_2911374
  simp only [CollatzResearch.WordTrace]
  refine ⟨13273316669324586992294647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70791022236397797292238117 13273316669324586992294647)
  ·
    refine ⟨19909975003986880488441971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13273316669324586992294647 19909975003986880488441971)
    ·
      refine ⟨29864962505980320732662957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19909975003986880488441971 29864962505980320732662957)
      ·
        refine ⟨11199360939742620274748609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29864962505980320732662957 11199360939742620274748609)
        ·
          refine ⟨8399520704806965206061457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11199360939742620274748609 8399520704806965206061457)
          ·
            refine ⟨6299640528605223904546093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8399520704806965206061457 6299640528605223904546093)
            ·
              refine ⟨2362365198226958964204785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6299640528605223904546093 2362365198226958964204785)
              ·
                refine ⟨1771773898670219223153589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2362365198226958964204785 1771773898670219223153589)
                ·
                  refine ⟨166103803000333052170649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1771773898670219223153589 166103803000333052170649)
                  ·
                    rfl

theorem cell23_2911374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 3, 2, 5].length) (baseStart_2911374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2911374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2911374 prefixEnd_2911374 := by exact prefixLift 2911374
  have htrace : WordTrace (prefixWord ++ tailWord_2911374) baseStart_2911374 baseEnd_2911374 := by
    simpa [prefixWord, tailWord_2911374, baseEnd_2911374] using wordTrace_append hprefix tailTrace_2911374
  have hstable : (prefixWord ++ tailWord_2911374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2911374).length < 2 ^ (prefixWord ++ tailWord_2911374).sum := by decide
  have hdescent : baseEnd_2911374 < baseStart_2911374 := by decide
  rcases family_descends (prefixWord ++ tailWord_2911374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2911434 : List Nat := [3, 1, 2, 1, 3, 3, 1, 4, 1, 4]
def baseStart_2911434 : Nat := 118140960795 + 2911434 * 2 ^ 59
def prefixEnd_2911434 : Nat := 4983230072969 + 3 ^ 40 * 2911434 * 2
def baseEnd_2911434 : Nat := 498321678614089078261855

theorem tailTrace_2911434 : CollatzResearch.WordTrace tailWord_2911434 prefixEnd_2911434 498321678614089078261855 := by
  unfold tailWord_2911434
  simp only [CollatzResearch.WordTrace]
  refine ⟨26547180433594831546385339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70792481156252884123694237 26547180433594831546385339)
  ·
    refine ⟨39820770650392247319578009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26547180433594831546385339 39820770650392247319578009)
    ·
      refine ⟨29865577987794185489683507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39820770650392247319578009 29865577987794185489683507)
      ·
        refine ⟨44798366981691278234525261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29865577987794185489683507 44798366981691278234525261)
        ·
          refine ⟨16799387618134229337946973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44798366981691278234525261 16799387618134229337946973)
          ·
            refine ⟨6299770356800336001730115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16799387618134229337946973 6299770356800336001730115)
            ·
              refine ⟨9449655535200504002595173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6299770356800336001730115 9449655535200504002595173)
              ·
                refine ⟨1771810412850094500486595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9449655535200504002595173 1771810412850094500486595)
                ·
                  refine ⟨2657715619275141750729893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1771810412850094500486595 2657715619275141750729893)
                  ·
                    refine ⟨498321678614089078261855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2657715619275141750729893 498321678614089078261855)
                    ·
                      rfl

theorem cell23_2911434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 4, 1, 4].length) (baseStart_2911434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2911434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2911434 prefixEnd_2911434 := by exact prefixLift 2911434
  have htrace : WordTrace (prefixWord ++ tailWord_2911434) baseStart_2911434 baseEnd_2911434 := by
    simpa [prefixWord, tailWord_2911434, baseEnd_2911434] using wordTrace_append hprefix tailTrace_2911434
  have hstable : (prefixWord ++ tailWord_2911434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2911434).length < 2 ^ (prefixWord ++ tailWord_2911434).sum := by decide
  have hdescent : baseEnd_2911434 < baseStart_2911434 := by decide
  rcases family_descends (prefixWord ++ tailWord_2911434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2911457 : List Nat := [1, 2, 3, 1, 3, 2, 1, 1, 5, 1, 3]
def baseStart_2911457 : Nat := 118140960795 + 2911457 * 2 ^ 59
def prefixEnd_2911457 : Nat := 4983230072969 + 3 ^ 40 * 2911457 * 2
def baseEnd_2911457 : Nat := 1494976845897320644797959

theorem tailTrace_2911457 : CollatzResearch.WordTrace tailWord_2911457 prefixEnd_2911457 1494976845897320644797959 := by
  unfold tailWord_2911457
  simp only [CollatzResearch.WordTrace]
  refine ⟨106189560613296001113628625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70793040408864000742419083 106189560613296001113628625)
  ·
    refine ⟨79642170459972000835221469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106189560613296001113628625 79642170459972000835221469)
    ·
      refine ⟨29865813922489500313208051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79642170459972000835221469 29865813922489500313208051)
      ·
        refine ⟨44798720883734250469812077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29865813922489500313208051 44798720883734250469812077)
        ·
          refine ⟨16799520331400343926179529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44798720883734250469812077 16799520331400343926179529)
          ·
            refine ⟨12599640248550257944634647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16799520331400343926179529 12599640248550257944634647)
            ·
              refine ⟨18899460372825386916951971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12599640248550257944634647 18899460372825386916951971)
              ·
                refine ⟨28349190559238080375427957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18899460372825386916951971 28349190559238080375427957)
                ·
                  refine ⟨2657736614928570035196371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28349190559238080375427957 2657736614928570035196371)
                  ·
                    refine ⟨3986604922392855052794557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2657736614928570035196371 3986604922392855052794557)
                    ·
                      refine ⟨1494976845897320644797959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3986604922392855052794557 1494976845897320644797959)
                      ·
                        rfl

theorem cell23_2911457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 1, 5, 1, 3].length) (baseStart_2911457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2911457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2911457 prefixEnd_2911457 := by exact prefixLift 2911457
  have htrace : WordTrace (prefixWord ++ tailWord_2911457) baseStart_2911457 baseEnd_2911457 := by
    simpa [prefixWord, tailWord_2911457, baseEnd_2911457] using wordTrace_append hprefix tailTrace_2911457
  have hstable : (prefixWord ++ tailWord_2911457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2911457).length < 2 ^ (prefixWord ++ tailWord_2911457).sum := by decide
  have hdescent : baseEnd_2911457 < baseStart_2911457 := by decide
  rcases family_descends (prefixWord ++ tailWord_2911457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2911460 : List Nat := [2, 3, 1, 1, 1, 2, 4, 1, 3, 5]
def baseStart_2911460 : Nat := 118140960795 + 2911460 * 2 ^ 59
def prefixEnd_2911460 : Nat := 4983230072969 + 3 ^ 40 * 2911460 * 2
def baseEnd_2911460 : Nat := 498326128779761377686815

theorem tailTrace_2911460 : CollatzResearch.WordTrace tailWord_2911460 prefixEnd_2911460 498326128779761377686815 := by
  unfold tailWord_2911460
  simp only [CollatzResearch.WordTrace]
  refine ⟨53094835016142566312993917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70793113354856755083991889 53094835016142566312993917)
  ·
    refine ⟨19910563131053462367372719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53094835016142566312993917 19910563131053462367372719)
    ·
      refine ⟨29865844696580193551059079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19910563131053462367372719 29865844696580193551059079)
      ·
        refine ⟨44798767044870290326588619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29865844696580193551059079 44798767044870290326588619)
        ·
          refine ⟨67198150567305435489882929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44798767044870290326588619 67198150567305435489882929)
          ·
            refine ⟨50398612925479076617412197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67198150567305435489882929 50398612925479076617412197)
            ·
              refine ⟨9449739923527326865764787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50398612925479076617412197 9449739923527326865764787)
              ·
                refine ⟨14174609885290990298647181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9449739923527326865764787 14174609885290990298647181)
                ·
                  refine ⟨5315478706984121361992693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14174609885290990298647181 5315478706984121361992693)
                  ·
                    refine ⟨498326128779761377686815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5315478706984121361992693 498326128779761377686815)
                    ·
                      rfl

theorem cell23_2911460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 1, 3, 5].length) (baseStart_2911460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2911460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2911460 prefixEnd_2911460 := by exact prefixLift 2911460
  have htrace : WordTrace (prefixWord ++ tailWord_2911460) baseStart_2911460 baseEnd_2911460 := by
    simpa [prefixWord, tailWord_2911460, baseEnd_2911460] using wordTrace_append hprefix tailTrace_2911460
  have hstable : (prefixWord ++ tailWord_2911460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2911460).length < 2 ^ (prefixWord ++ tailWord_2911460).sum := by decide
  have hdescent : baseEnd_2911460 < baseStart_2911460 := by decide
  rcases family_descends (prefixWord ++ tailWord_2911460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2911461 : List Nat := [1, 3, 1, 4, 4, 1, 1, 1, 2, 2, 3]
def baseStart_2911461 : Nat := 118140960795 + 2911461 * 2 ^ 59
def prefixEnd_2911461 : Nat := 4983230072969 + 3 ^ 40 * 2911461 * 2
def baseEnd_2911461 : Nat := 1494978899819938629147941

theorem tailTrace_2911461 : CollatzResearch.WordTrace tailWord_2911461 prefixEnd_2911461 1494978899819938629147941 := by
  unfold tailWord_2911461
  simp only [CollatzResearch.WordTrace]
  refine ⟨106189706505281509796774237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70793137670187673197849491 106189706505281509796774237)
  ·
    refine ⟨39821139939480566173790339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106189706505281509796774237 39821139939480566173790339)
    ·
      refine ⟨59731709909220849260685509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39821139939480566173790339 59731709909220849260685509)
      ·
        refine ⟨11199695607978909236378533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59731709909220849260685509 11199695607978909236378533)
        ·
          refine ⟨2099942926496045481820975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11199695607978909236378533 2099942926496045481820975)
          ·
            refine ⟨3149914389744068222731463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2099942926496045481820975 3149914389744068222731463)
            ·
              refine ⟨4724871584616102334097195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3149914389744068222731463 4724871584616102334097195)
              ·
                refine ⟨7087307376924153501145793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4724871584616102334097195 7087307376924153501145793)
                ·
                  refine ⟨5315480532693115125859345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7087307376924153501145793 5315480532693115125859345)
                  ·
                    refine ⟨3986610399519836344394509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5315480532693115125859345 3986610399519836344394509)
                    ·
                      refine ⟨1494978899819938629147941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3986610399519836344394509 1494978899819938629147941)
                      ·
                        rfl

theorem cell23_2911461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 1, 1, 2, 2, 3].length) (baseStart_2911461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2911461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2911461 prefixEnd_2911461 := by exact prefixLift 2911461
  have htrace : WordTrace (prefixWord ++ tailWord_2911461) baseStart_2911461 baseEnd_2911461 := by
    simpa [prefixWord, tailWord_2911461, baseEnd_2911461] using wordTrace_append hprefix tailTrace_2911461
  have hstable : (prefixWord ++ tailWord_2911461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2911461).length < 2 ^ (prefixWord ++ tailWord_2911461).sum := by decide
  have hdescent : baseEnd_2911461 < baseStart_2911461 := by decide
  rcases family_descends (prefixWord ++ tailWord_2911461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2911467 : List Nat := [1, 1, 1, 1, 2, 7, 1, 1, 1, 5, 2]
def baseStart_2911467 : Nat := 118140960795 + 2911467 * 2 ^ 59
def prefixEnd_2911467 : Nat := 4983230072969 + 3 ^ 40 * 2911467 * 2
def baseEnd_2911467 : Nat := 1494981980703865605672913

theorem tailTrace_2911467 : CollatzResearch.WordTrace tailWord_2911467 prefixEnd_2911467 1494981980703865605672913 := by
  unfold tailWord_2911467
  simp only [CollatzResearch.WordTrace]
  refine ⟨106189925343259772821492655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70793283562173181880995103 106189925343259772821492655)
  ·
    refine ⟨159284888014889659232238983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106189925343259772821492655 159284888014889659232238983)
    ·
      refine ⟨238927332022334488848358475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159284888014889659232238983 238927332022334488848358475)
      ·
        refine ⟨358390998033501733272537713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238927332022334488848358475 358390998033501733272537713)
        ·
          refine ⟨268793248525126299954403285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 358390998033501733272537713 268793248525126299954403285)
          ·
            refine ⟨6299841762307647655181327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 268793248525126299954403285 6299841762307647655181327)
            ·
              refine ⟨9449762643461471482771991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6299841762307647655181327 9449762643461471482771991)
              ·
                refine ⟨14174643965192207224157987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9449762643461471482771991 14174643965192207224157987)
                ·
                  refine ⟨21261965947788310836236981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14174643965192207224157987 21261965947788310836236981)
                  ·
                    refine ⟨1993309307605154140897217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21261965947788310836236981 1993309307605154140897217)
                    ·
                      refine ⟨1494981980703865605672913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1993309307605154140897217 1494981980703865605672913)
                      ·
                        rfl

theorem cell23_2911467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 1, 1, 5, 2].length) (baseStart_2911467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2911467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2911467 prefixEnd_2911467 := by exact prefixLift 2911467
  have htrace : WordTrace (prefixWord ++ tailWord_2911467) baseStart_2911467 baseEnd_2911467 := by
    simpa [prefixWord, tailWord_2911467, baseEnd_2911467] using wordTrace_append hprefix tailTrace_2911467
  have hstable : (prefixWord ++ tailWord_2911467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2911467).length < 2 ^ (prefixWord ++ tailWord_2911467).sum := by decide
  have hdescent : baseEnd_2911467 < baseStart_2911467 := by decide
  rcases family_descends (prefixWord ++ tailWord_2911467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2911500 : List Nat := [2, 2, 1, 2, 2, 3, 1, 1, 3, 1, 5]
def baseStart_2911500 : Nat := 118140960795 + 2911500 * 2 ^ 59
def prefixEnd_2911500 : Nat := 4983230072969 + 3 ^ 40 * 2911500 * 2
def baseEnd_2911500 : Nat := 1494998925565463976560261

theorem tailTrace_2911500 : CollatzResearch.WordTrace tailWord_2911500 prefixEnd_2911500 1494998925565463976560261 := by
  unfold tailWord_2911500
  simp only [CollatzResearch.WordTrace]
  refine ⟨53095564476070109728721977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70794085968093479638295969 53095564476070109728721977)
  ·
    refine ⟨39821673357052582296541483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53095564476070109728721977 39821673357052582296541483)
    ·
      refine ⟨59732510035578873444812225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39821673357052582296541483 59732510035578873444812225)
      ·
        refine ⟨44799382526684155083609169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59732510035578873444812225 44799382526684155083609169)
        ·
          refine ⟨33599536895013116312706877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44799382526684155083609169 33599536895013116312706877)
          ·
            refine ⟨12599826335629918617265079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33599536895013116312706877 12599826335629918617265079)
            ·
              refine ⟨18899739503444877925897619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12599826335629918617265079 18899739503444877925897619)
              ·
                refine ⟨28349609255167316888846429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18899739503444877925897619 28349609255167316888846429)
                ·
                  refine ⟨10631103470687743833317411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28349609255167316888846429 10631103470687743833317411)
                  ·
                    refine ⟨15946655206031615749976117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10631103470687743833317411 15946655206031615749976117)
                    ·
                      refine ⟨1494998925565463976560261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15946655206031615749976117 1494998925565463976560261)
                      ·
                        rfl

theorem cell23_2911500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 1, 3, 1, 5].length) (baseStart_2911500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2911500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2911500 prefixEnd_2911500 := by exact prefixLift 2911500
  have htrace : WordTrace (prefixWord ++ tailWord_2911500) baseStart_2911500 baseEnd_2911500 := by
    simpa [prefixWord, tailWord_2911500, baseEnd_2911500] using wordTrace_append hprefix tailTrace_2911500
  have hstable : (prefixWord ++ tailWord_2911500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2911500).length < 2 ^ (prefixWord ++ tailWord_2911500).sum := by decide
  have hdescent : baseEnd_2911500 < baseStart_2911500 := by decide
  rcases family_descends (prefixWord ++ tailWord_2911500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2911514 : List Nat := [3, 1, 1, 3, 3, 2, 2, 2, 1, 1, 4]
def baseStart_2911514 : Nat := 118140960795 + 2911514 * 2 ^ 59
def prefixEnd_2911514 : Nat := 4983230072969 + 3 ^ 40 * 2911514 * 2
def baseEnd_2911514 : Nat := 1495006114294626921785197

theorem tailTrace_2911514 : CollatzResearch.WordTrace tailWord_2911514 prefixEnd_2911514 1495006114294626921785197 := by
  unfold tailWord_2911514
  simp only [CollatzResearch.WordTrace]
  refine ⟨26547909893522374962113399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70794426382726333232302397 26547909893522374962113399)
  ·
    refine ⟨39821864840283562443170099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26547909893522374962113399 39821864840283562443170099)
    ·
      refine ⟨59732797260425343664755149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39821864840283562443170099 59732797260425343664755149)
      ·
        refine ⟨22399798972659503874283181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59732797260425343664755149 22399798972659503874283181)
        ·
          refine ⟨8399924614747313952856193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22399798972659503874283181 8399924614747313952856193)
          ·
            refine ⟨6299943461060485464642145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8399924614747313952856193 6299943461060485464642145)
            ·
              refine ⟨4724957595795364098481609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6299943461060485464642145 4724957595795364098481609)
              ·
                refine ⟨3543718196846523073861207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4724957595795364098481609 3543718196846523073861207)
                ·
                  refine ⟨5315577295269784610791811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3543718196846523073861207 5315577295269784610791811)
                  ·
                    refine ⟨7973365942904676916187717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5315577295269784610791811 7973365942904676916187717)
                    ·
                      refine ⟨1495006114294626921785197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7973365942904676916187717 1495006114294626921785197)
                      ·
                        rfl

theorem cell23_2911514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 2, 2, 1, 1, 4].length) (baseStart_2911514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2911514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2911514 prefixEnd_2911514 := by exact prefixLift 2911514
  have htrace : WordTrace (prefixWord ++ tailWord_2911514) baseStart_2911514 baseEnd_2911514 := by
    simpa [prefixWord, tailWord_2911514, baseEnd_2911514] using wordTrace_append hprefix tailTrace_2911514
  have hstable : (prefixWord ++ tailWord_2911514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2911514).length < 2 ^ (prefixWord ++ tailWord_2911514).sum := by decide
  have hdescent : baseEnd_2911514 < baseStart_2911514 := by decide
  rcases family_descends (prefixWord ++ tailWord_2911514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2911542 : List Nat := [5, 1, 2, 3, 1, 1, 3, 2, 1, 1, 3]
def baseStart_2911542 : Nat := 118140960795 + 2911542 * 2 ^ 59
def prefixEnd_2911542 : Nat := 4983230072969 + 3 ^ 40 * 2911542 * 2
def baseEnd_2911542 : Nat := 1495020491752952812235069

theorem tailTrace_2911542 : CollatzResearch.WordTrace tailWord_2911542 prefixEnd_2911542 1495020491752952812235069 := by
  unfold tailWord_2911542
  simp only [CollatzResearch.WordTrace]
  refine ⟨6637041301124253789404555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 70795107211992040420315253 6637041301124253789404555)
  ·
    refine ⟨9955561951686380684106833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6637041301124253789404555 9955561951686380684106833)
    ·
      refine ⟨7466671463764785513080125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9955561951686380684106833 7466671463764785513080125)
      ·
        refine ⟨2800001798911794567405047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7466671463764785513080125 2800001798911794567405047)
        ·
          refine ⟨4200002698367691851107571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2800001798911794567405047 4200002698367691851107571)
          ·
            refine ⟨6300004047551537776661357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4200002698367691851107571 6300004047551537776661357)
            ·
              refine ⟨2362501517831826666248009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6300004047551537776661357 2362501517831826666248009)
              ·
                refine ⟨1771876138373869999686007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2362501517831826666248009 1771876138373869999686007)
                ·
                  refine ⟨2657814207560804999529011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1771876138373869999686007 2657814207560804999529011)
                  ·
                    refine ⟨3986721311341207499293517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2657814207560804999529011 3986721311341207499293517)
                    ·
                      refine ⟨1495020491752952812235069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3986721311341207499293517 1495020491752952812235069)
                      ·
                        rfl

theorem cell23_2911542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 3, 2, 1, 1, 3].length) (baseStart_2911542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2911542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2911542 prefixEnd_2911542 := by exact prefixLift 2911542
  have htrace : WordTrace (prefixWord ++ tailWord_2911542) baseStart_2911542 baseEnd_2911542 := by
    simpa [prefixWord, tailWord_2911542, baseEnd_2911542] using wordTrace_append hprefix tailTrace_2911542
  have hstable : (prefixWord ++ tailWord_2911542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2911542).length < 2 ^ (prefixWord ++ tailWord_2911542).sum := by decide
  have hdescent : baseEnd_2911542 < baseStart_2911542 := by decide
  rcases family_descends (prefixWord ++ tailWord_2911542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2911565 : List Nat := [1, 6, 1, 3, 2, 1, 1, 2, 1, 1, 4]
def baseStart_2911565 : Nat := 118140960795 + 2911565 * 2 ^ 59
def prefixEnd_2911565 : Nat := 4983230072969 + 3 ^ 40 * 2911565 * 2
def baseEnd_2911565 : Nat := 1495032301808006222247463

theorem tailTrace_2911565 : CollatzResearch.WordTrace tailWord_2911565 prefixEnd_2911565 1495032301808006222247463 := by
  unfold tailWord_2911565
  simp only [CollatzResearch.WordTrace]
  refine ⟨106193499696904735558560149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70795666464603157039040099 106193499696904735558560149)
  ·
    refine ⟨4977820298292409479307507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 106193499696904735558560149 4977820298292409479307507)
    ·
      refine ⟨7466730447438614218961261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4977820298292409479307507 7466730447438614218961261)
      ·
        refine ⟨2800023917789480332110473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7466730447438614218961261 2800023917789480332110473)
        ·
          refine ⟨2100017938342110249082855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2800023917789480332110473 2100017938342110249082855)
          ·
            refine ⟨3150026907513165373624283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2100017938342110249082855 3150026907513165373624283)
            ·
              refine ⟨4725040361269748060436425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3150026907513165373624283 4725040361269748060436425)
              ·
                refine ⟨3543780270952311045327319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4725040361269748060436425 3543780270952311045327319)
                ·
                  refine ⟨5315670406428466567990979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3543780270952311045327319 5315670406428466567990979)
                  ·
                    refine ⟨7973505609642699851986469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5315670406428466567990979 7973505609642699851986469)
                    ·
                      refine ⟨1495032301808006222247463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7973505609642699851986469 1495032301808006222247463)
                      ·
                        rfl

theorem cell23_2911565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_2911565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2911565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2911565 prefixEnd_2911565 := by exact prefixLift 2911565
  have htrace : WordTrace (prefixWord ++ tailWord_2911565) baseStart_2911565 baseEnd_2911565 := by
    simpa [prefixWord, tailWord_2911565, baseEnd_2911565] using wordTrace_append hprefix tailTrace_2911565
  have hstable : (prefixWord ++ tailWord_2911565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2911565).length < 2 ^ (prefixWord ++ tailWord_2911565).sum := by decide
  have hdescent : baseEnd_2911565 < baseStart_2911565 := by decide
  rcases family_descends (prefixWord ++ tailWord_2911565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2911570 : List Nat := [3, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8]
def baseStart_2911570 : Nat := 118140960795 + 2911570 * 2 ^ 59
def prefixEnd_2911570 : Nat := 4983230072969 + 3 ^ 40 * 2911570 * 2
def baseEnd_2911570 : Nat := 1495034869211278702684939

theorem tailTrace_2911570 : CollatzResearch.WordTrace tailWord_2911570 prefixEnd_2911570 1495034869211278702684939 := by
  unfold tailWord_2911570
  simp only [CollatzResearch.WordTrace]
  refine ⟨26548420515471655353123041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70795788041257747608328109 26548420515471655353123041)
  ·
    refine ⟨19911315386603741514842281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26548420515471655353123041 19911315386603741514842281)
    ·
      refine ⟨14933486539952806136131711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19911315386603741514842281 14933486539952806136131711)
      ·
        refine ⟨22400229809929209204197567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14933486539952806136131711 22400229809929209204197567)
        ·
          refine ⟨33600344714893813806296351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22400229809929209204197567 33600344714893813806296351)
          ·
            refine ⟨50400517072340720709444527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33600344714893813806296351 50400517072340720709444527)
            ·
              refine ⟨75600775608511081064166791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50400517072340720709444527 75600775608511081064166791)
              ·
                refine ⟨113401163412766621596250187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75600775608511081064166791 113401163412766621596250187)
                ·
                  refine ⟨170101745119149932394375281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 113401163412766621596250187 170101745119149932394375281)
                  ·
                    refine ⟨127576308839362449295781461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 170101745119149932394375281 127576308839362449295781461)
                    ·
                      refine ⟨1495034869211278702684939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 127576308839362449295781461 1495034869211278702684939)
                      ·
                        rfl

theorem cell23_2911570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8].length) (baseStart_2911570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2911570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2911570 prefixEnd_2911570 := by exact prefixLift 2911570
  have htrace : WordTrace (prefixWord ++ tailWord_2911570) baseStart_2911570 baseEnd_2911570 := by
    simpa [prefixWord, tailWord_2911570, baseEnd_2911570] using wordTrace_append hprefix tailTrace_2911570
  have hstable : (prefixWord ++ tailWord_2911570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2911570).length < 2 ^ (prefixWord ++ tailWord_2911570).sum := by decide
  have hdescent : baseEnd_2911570 < baseStart_2911570 := by decide
  rcases family_descends (prefixWord ++ tailWord_2911570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2911621 : List Nat := [1, 3, 1, 1, 3, 1, 4, 3, 2, 2, 2]
def baseStart_2911621 : Nat := 118140960795 + 2911621 * 2 ^ 59
def prefixEnd_2911621 : Nat := 4983230072969 + 3 ^ 40 * 2911621 * 2
def baseEnd_2911621 : Nat := 1495061056724658003147205

theorem tailTrace_2911621 : CollatzResearch.WordTrace tailWord_2911621 prefixEnd_2911621 1495061056724658003147205 := by
  unfold tailWord_2911621
  simp only [CollatzResearch.WordTrace]
  refine ⟨106195542184701857122598717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70797028123134571415065811 106195542184701857122598717)
  ·
    refine ⟨39823328319263196420974519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106195542184701857122598717 39823328319263196420974519)
    ·
      refine ⟨59734992478894794631461779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39823328319263196420974519 59734992478894794631461779)
      ·
        refine ⟨89602488718342191947192669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59734992478894794631461779 89602488718342191947192669)
        ·
          refine ⟨33600933269378321980197251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89602488718342191947192669 33600933269378321980197251)
          ·
            refine ⟨50401399904067482970295877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33600933269378321980197251 50401399904067482970295877)
            ·
              refine ⟨9450262482012653056930477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50401399904067482970295877 9450262482012653056930477)
              ·
                refine ⟨3543848430754744896348929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9450262482012653056930477 3543848430754744896348929)
                ·
                  refine ⟨2657886323066058672261697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3543848430754744896348929 2657886323066058672261697)
                  ·
                    refine ⟨1993414742299544004196273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2657886323066058672261697 1993414742299544004196273)
                    ·
                      refine ⟨1495061056724658003147205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1993414742299544004196273 1495061056724658003147205)
                      ·
                        rfl

theorem cell23_2911621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 3, 2, 2, 2].length) (baseStart_2911621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2911621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2911621 prefixEnd_2911621 := by exact prefixLift 2911621
  have htrace : WordTrace (prefixWord ++ tailWord_2911621) baseStart_2911621 baseEnd_2911621 := by
    simpa [prefixWord, tailWord_2911621, baseEnd_2911621] using wordTrace_append hprefix tailTrace_2911621
  have hstable : (prefixWord ++ tailWord_2911621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2911621).length < 2 ^ (prefixWord ++ tailWord_2911621).sum := by decide
  have hdescent : baseEnd_2911621 < baseStart_2911621 := by decide
  rcases family_descends (prefixWord ++ tailWord_2911621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2911661 : List Nat := [1, 5, 2, 2, 1, 1, 2, 4, 5]
def baseStart_2911661 : Nat := 118140960795 + 2911661 * 2 ^ 59
def prefixEnd_2911661 : Nat := 4983230072969 + 3 ^ 40 * 2911661 * 2
def baseEnd_2911661 : Nat := 166120177327870871849669

theorem tailTrace_2911661 : CollatzResearch.WordTrace tailWord_2911661 prefixEnd_2911661 166120177327870871849669 := by
  unfold tailWord_2911661
  simp only [CollatzResearch.WordTrace]
  refine ⟨106197001104556943954054837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70798000736371295969369891 106197001104556943954054837)
  ·
    refine ⟨9955968853552213495692641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 106197001104556943954054837 9955968853552213495692641)
    ·
      refine ⟨7466976640164160121769481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9955968853552213495692641 7466976640164160121769481)
      ·
        refine ⟨5600232480123120091327111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7466976640164160121769481 5600232480123120091327111)
        ·
          refine ⟨8400348720184680136990667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5600232480123120091327111 8400348720184680136990667)
          ·
            refine ⟨12600523080277020205486001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8400348720184680136990667 12600523080277020205486001)
            ·
              refine ⟨9450392310207765154114501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12600523080277020205486001 9450392310207765154114501)
              ·
                refine ⟨1771948558163955966396469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9450392310207765154114501 1771948558163955966396469)
                ·
                  refine ⟨166120177327870871849669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1771948558163955966396469 166120177327870871849669)
                  ·
                    rfl

theorem cell23_2911661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 4, 5].length) (baseStart_2911661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2911661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2911661 prefixEnd_2911661 := by exact prefixLift 2911661
  have htrace : WordTrace (prefixWord ++ tailWord_2911661) baseStart_2911661 baseEnd_2911661 := by
    simpa [prefixWord, tailWord_2911661, baseEnd_2911661] using wordTrace_append hprefix tailTrace_2911661
  have hstable : (prefixWord ++ tailWord_2911661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2911661).length < 2 ^ (prefixWord ++ tailWord_2911661).sum := by decide
  have hdescent : baseEnd_2911661 < baseStart_2911661 := by decide
  rcases family_descends (prefixWord ++ tailWord_2911661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2911677 : List Nat := [1, 4, 1, 2, 2, 1, 1, 1, 3, 3, 4]
def baseStart_2911677 : Nat := 118140960795 + 2911677 * 2 ^ 59
def prefixEnd_2911677 : Nat := 4983230072969 + 3 ^ 40 * 2911677 * 2
def baseEnd_2911677 : Nat := 1495089811641309784046947

theorem tailTrace_2911677 : CollatzResearch.WordTrace tailWord_2911677 prefixEnd_2911677 1495089811641309784046947 := by
  unfold tailWord_2911677
  simp only [CollatzResearch.WordTrace]
  refine ⟨106197584672498978686637285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70798389781665985791091523 106197584672498978686637285)
  ·
    refine ⟨19912047126093558503744491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 106197584672498978686637285 19912047126093558503744491)
    ·
      refine ⟨29868070689140337755616737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19912047126093558503744491 29868070689140337755616737)
      ·
        refine ⟨22401053016855253316712553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29868070689140337755616737 22401053016855253316712553)
        ·
          refine ⟨16800789762641439987534415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22401053016855253316712553 16800789762641439987534415)
          ·
            refine ⟨25201184643962159981301623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16800789762641439987534415 25201184643962159981301623)
            ·
              refine ⟨37801776965943239971952435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25201184643962159981301623 37801776965943239971952435)
              ·
                refine ⟨56702665448914859957928653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37801776965943239971952435 56702665448914859957928653)
                ·
                  refine ⟨21263499543343072484223245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56702665448914859957928653 21263499543343072484223245)
                  ·
                    refine ⟨7973812328753652181583717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21263499543343072484223245 7973812328753652181583717)
                    ·
                      refine ⟨1495089811641309784046947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7973812328753652181583717 1495089811641309784046947)
                      ·
                        rfl

theorem cell23_2911677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 1, 3, 3, 4].length) (baseStart_2911677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2911677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2911677 prefixEnd_2911677 := by exact prefixLift 2911677
  have htrace : WordTrace (prefixWord ++ tailWord_2911677) baseStart_2911677 baseEnd_2911677 := by
    simpa [prefixWord, tailWord_2911677, baseEnd_2911677] using wordTrace_append hprefix tailTrace_2911677
  have hstable : (prefixWord ++ tailWord_2911677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2911677).length < 2 ^ (prefixWord ++ tailWord_2911677).sum := by decide
  have hdescent : baseEnd_2911677 < baseStart_2911677 := by decide
  rcases family_descends (prefixWord ++ tailWord_2911677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2911694 : List Nat := [4, 1, 1, 1, 2, 1, 2, 2, 1, 6, 2]
def baseStart_2911694 : Nat := 118140960795 + 2911694 * 2 ^ 59
def prefixEnd_2911694 : Nat := 4983230072969 + 3 ^ 40 * 2911694 * 2
def baseEnd_2911694 : Nat := 1495098540812436217534369

theorem tailTrace_2911694 : CollatzResearch.WordTrace tailWord_2911694 prefixEnd_2911694 1495098540812436217534369 := by
  unfold tailWord_2911694
  simp only [CollatzResearch.WordTrace]
  refine ⟨13274775589179673823750767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70798803142291593726670757 13274775589179673823750767)
  ·
    refine ⟨19912163383769510735626151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13274775589179673823750767 19912163383769510735626151)
    ·
      refine ⟨29868245075654266103439227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19912163383769510735626151 29868245075654266103439227)
      ·
        refine ⟨44802367613481399155158841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29868245075654266103439227 44802367613481399155158841)
        ·
          refine ⟨33601775710111049366369131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44802367613481399155158841 33601775710111049366369131)
          ·
            refine ⟨50402663565166574049553697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33601775710111049366369131 50402663565166574049553697)
            ·
              refine ⟨37801997673874930537165273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50402663565166574049553697 37801997673874930537165273)
              ·
                refine ⟨28351498255406197902873955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37801997673874930537165273 28351498255406197902873955)
                ·
                  refine ⟨42527247383109296854310933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28351498255406197902873955 42527247383109296854310933)
                  ·
                    refine ⟨1993464721083248290045825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 42527247383109296854310933 1993464721083248290045825)
                    ·
                      refine ⟨1495098540812436217534369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1993464721083248290045825 1495098540812436217534369)
                      ·
                        rfl

theorem cell23_2911694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 2, 1, 6, 2].length) (baseStart_2911694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2911694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2911694 prefixEnd_2911694 := by exact prefixLift 2911694
  have htrace : WordTrace (prefixWord ++ tailWord_2911694) baseStart_2911694 baseEnd_2911694 := by
    simpa [prefixWord, tailWord_2911694, baseEnd_2911694] using wordTrace_append hprefix tailTrace_2911694
  have hstable : (prefixWord ++ tailWord_2911694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2911694).length < 2 ^ (prefixWord ++ tailWord_2911694).sum := by decide
  have hdescent : baseEnd_2911694 < baseStart_2911694 := by decide
  rcases family_descends (prefixWord ++ tailWord_2911694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2911748 : List Nat := [2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 3]
def baseStart_2911748 : Nat := 118140960795 + 2911748 * 2 ^ 59
def prefixEnd_2911748 : Nat := 4983230072969 + 3 ^ 40 * 2911748 * 2
def baseEnd_2911748 : Nat := 1495126268767779006259121

theorem tailTrace_2911748 : CollatzResearch.WordTrace tailWord_2911748 prefixEnd_2911748 1495126268767779006259121 := by
  unfold tailWord_2911748
  simp only [CollatzResearch.WordTrace]
  refine ⟨53100087127620878906235949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70800116170161171874981265 53100087127620878906235949)
  ·
    refine ⟨19912532672857829589838481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53100087127620878906235949 19912532672857829589838481)
    ·
      refine ⟨14934399504643372192378861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19912532672857829589838481 14934399504643372192378861)
      ·
        refine ⟨5600399814241264572142073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14934399504643372192378861 5600399814241264572142073)
        ·
          refine ⟨4200299860680948429106555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5600399814241264572142073 4200299860680948429106555)
          ·
            refine ⟨6300449791021422643659833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4200299860680948429106555 6300449791021422643659833)
            ·
              refine ⟨4725337343266066982744875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6300449791021422643659833 4725337343266066982744875)
              ·
                refine ⟨7088006014899100474117313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4725337343266066982744875 7088006014899100474117313)
                ·
                  refine ⟨5316004511174325355587985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7088006014899100474117313 5316004511174325355587985)
                  ·
                    refine ⟨3987003383380744016690989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5316004511174325355587985 3987003383380744016690989)
                    ·
                      refine ⟨1495126268767779006259121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3987003383380744016690989 1495126268767779006259121)
                      ·
                        rfl

theorem cell23_2911748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_2911748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2911748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2911748 prefixEnd_2911748 := by exact prefixLift 2911748
  have htrace : WordTrace (prefixWord ++ tailWord_2911748) baseStart_2911748 baseEnd_2911748 := by
    simpa [prefixWord, tailWord_2911748, baseEnd_2911748] using wordTrace_append hprefix tailTrace_2911748
  have hstable : (prefixWord ++ tailWord_2911748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2911748).length < 2 ^ (prefixWord ++ tailWord_2911748).sum := by decide
  have hdescent : baseEnd_2911748 < baseStart_2911748 := by decide
  rcases family_descends (prefixWord ++ tailWord_2911748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2911794 : List Nat := [3, 2, 1, 1, 2, 1, 1, 2, 6, 4]
def baseStart_2911794 : Nat := 118140960795 + 2911794 * 2 ^ 59
def prefixEnd_2911794 : Nat := 4983230072969 + 3 ^ 40 * 2911794 * 2
def baseEnd_2911794 : Nat := 498383296292628608761303

theorem tailTrace_2911794 : CollatzResearch.WordTrace tailWord_2911794 prefixEnd_2911794 498383296292628608761303 := by
  unfold tailWord_2911794
  simp only [CollatzResearch.WordTrace]
  refine ⟨26550463003268776917161609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70801234675383405112430957 26550463003268776917161609)
  ·
    refine ⟨19912847252451582687871207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26550463003268776917161609 19912847252451582687871207)
    ·
      refine ⟨29869270878677374031806811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19912847252451582687871207 29869270878677374031806811)
      ·
        refine ⟨44803906318016061047710217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29869270878677374031806811 44803906318016061047710217)
        ·
          refine ⟨33602929738512045785782663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44803906318016061047710217 33602929738512045785782663)
          ·
            refine ⟨50404394607768068678673995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33602929738512045785782663 50404394607768068678673995)
            ·
              refine ⟨75606591911652103018010993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50404394607768068678673995 75606591911652103018010993)
              ·
                refine ⟨56704943933739077263508245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75606591911652103018010993 56704943933739077263508245)
                ·
                  refine ⟨2658044246894019246726949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 56704943933739077263508245 2658044246894019246726949)
                  ·
                    refine ⟨498383296292628608761303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2658044246894019246726949 498383296292628608761303)
                    ·
                      rfl

theorem cell23_2911794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 2, 6, 4].length) (baseStart_2911794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2911794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2911794 prefixEnd_2911794 := by exact prefixLift 2911794
  have htrace : WordTrace (prefixWord ++ tailWord_2911794) baseStart_2911794 baseEnd_2911794 := by
    simpa [prefixWord, tailWord_2911794, baseEnd_2911794] using wordTrace_append hprefix tailTrace_2911794
  have hstable : (prefixWord ++ tailWord_2911794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2911794).length < 2 ^ (prefixWord ++ tailWord_2911794).sum := by decide
  have hdescent : baseEnd_2911794 < baseStart_2911794 := by decide
  rcases family_descends (prefixWord ++ tailWord_2911794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2911805 : List Nat := [1, 4, 1, 3, 3, 2, 1, 1, 2, 3, 2]
def baseStart_2911805 : Nat := 118140960795 + 2911805 * 2 ^ 59
def prefixEnd_2911805 : Nat := 4983230072969 + 3 ^ 40 * 2911805 * 2
def baseEnd_2911805 : Nat := 1495155537165085283246359

theorem tailTrace_2911805 : CollatzResearch.WordTrace tailWord_2911805 prefixEnd_2911805 1495155537165085283246359 := by
  unfold tailWord_2911805
  simp only [CollatzResearch.WordTrace]
  refine ⟨106202253216035256547296869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70801502144023504364864579 106202253216035256547296869)
  ·
    refine ⟨19912922478006610602618163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 106202253216035256547296869 19912922478006610602618163)
    ·
      refine ⟨29869383717009915903927245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19912922478006610602618163 29869383717009915903927245)
      ·
        refine ⟨11201018893878718463972717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29869383717009915903927245 11201018893878718463972717)
        ·
          refine ⟨4200382085204519423989769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11201018893878718463972717 4200382085204519423989769)
          ·
            refine ⟨3150286563903389567992327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4200382085204519423989769 3150286563903389567992327)
            ·
              refine ⟨4725429845855084351988491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3150286563903389567992327 4725429845855084351988491)
              ·
                refine ⟨7088144768782626527982737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4725429845855084351988491 7088144768782626527982737)
                ·
                  refine ⟨5316108576586969895987053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7088144768782626527982737 5316108576586969895987053)
                  ·
                    refine ⟨1993540716220113710995145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5316108576586969895987053 1993540716220113710995145)
                    ·
                      refine ⟨1495155537165085283246359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1993540716220113710995145 1495155537165085283246359)
                      ·
                        rfl

theorem cell23_2911805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 1, 1, 2, 3, 2].length) (baseStart_2911805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2911805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2911805 prefixEnd_2911805 := by exact prefixLift 2911805
  have htrace : WordTrace (prefixWord ++ tailWord_2911805) baseStart_2911805 baseEnd_2911805 := by
    simpa [prefixWord, tailWord_2911805, baseEnd_2911805] using wordTrace_append hprefix tailTrace_2911805
  have hstable : (prefixWord ++ tailWord_2911805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2911805).length < 2 ^ (prefixWord ++ tailWord_2911805).sum := by decide
  have hdescent : baseEnd_2911805 < baseStart_2911805 := by decide
  rcases family_descends (prefixWord ++ tailWord_2911805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2911815 : List Nat := [1, 1, 4, 1, 6, 1, 2, 1, 1, 5]
def baseStart_2911815 : Nat := 118140960795 + 2911815 * 2 ^ 59
def prefixEnd_2911815 : Nat := 4983230072969 + 3 ^ 40 * 2911815 * 2
def baseEnd_2911815 : Nat := 498386890657210081373771

theorem tailTrace_2911815 : CollatzResearch.WordTrace tailWord_2911815 prefixEnd_2911815 498386890657210081373771 := by
  unfold tailWord_2911815
  simp only [CollatzResearch.WordTrace]
  refine ⟨106202617945999028255160899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70801745297332685503440599 106202617945999028255160899)
  ·
    refine ⟨159303926918998542382741349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106202617945999028255160899 159303926918998542382741349)
    ·
      refine ⟨29869486297312226696764003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 159303926918998542382741349 29869486297312226696764003)
      ·
        refine ⟨44804229445968340045146005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29869486297312226696764003 44804229445968340045146005)
        ·
          refine ⟨2100198255279765939616219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 44804229445968340045146005 2100198255279765939616219)
          ·
            refine ⟨3150297382919648909424329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2100198255279765939616219 3150297382919648909424329)
            ·
              refine ⟨2362723037189736682068247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3150297382919648909424329 2362723037189736682068247)
              ·
                refine ⟨3544084555784605023102371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2362723037189736682068247 3544084555784605023102371)
                ·
                  refine ⟨5316126833676907534653557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3544084555784605023102371 5316126833676907534653557)
                  ·
                    refine ⟨498386890657210081373771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5316126833676907534653557 498386890657210081373771)
                    ·
                      rfl

theorem cell23_2911815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 2, 1, 1, 5].length) (baseStart_2911815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2911815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2911815 prefixEnd_2911815 := by exact prefixLift 2911815
  have htrace : WordTrace (prefixWord ++ tailWord_2911815) baseStart_2911815 baseEnd_2911815 := by
    simpa [prefixWord, tailWord_2911815, baseEnd_2911815] using wordTrace_append hprefix tailTrace_2911815
  have hstable : (prefixWord ++ tailWord_2911815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2911815).length < 2 ^ (prefixWord ++ tailWord_2911815).sum := by decide
  have hdescent : baseEnd_2911815 < baseStart_2911815 := by decide
  rcases family_descends (prefixWord ++ tailWord_2911815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2911834 : List Nat := [3, 1, 1, 2, 1, 1, 1, 4, 3, 3, 3]
def baseStart_2911834 : Nat := 118140960795 + 2911834 * 2 ^ 59
def prefixEnd_2911834 : Nat := 4983230072969 + 3 ^ 40 * 2911834 * 2
def baseEnd_2911834 : Nat := 1495170428104065669783725

theorem tailTrace_2911834 : CollatzResearch.WordTrace tailWord_2911834 prefixEnd_2911834 1495170428104065669783725 := by
  unfold tailWord_2911834
  simp only [CollatzResearch.WordTrace]
  refine ⟨26550827733232548625025639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70802207288620129666735037 26550827733232548625025639)
  ·
    refine ⟨39826241599848822937538459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26550827733232548625025639 39826241599848822937538459)
    ·
      refine ⟨59739362399773234406307689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39826241599848822937538459 59739362399773234406307689)
      ·
        refine ⟨44804521799829925804730767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59739362399773234406307689 44804521799829925804730767)
        ·
          refine ⟨67206782699744888707096151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44804521799829925804730767 67206782699744888707096151)
          ·
            refine ⟨100810174049617333060644227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67206782699744888707096151 100810174049617333060644227)
            ·
              refine ⟨151215261074425999590966341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100810174049617333060644227 151215261074425999590966341)
              ·
                refine ⟨28352861451454874923306189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 151215261074425999590966341 28352861451454874923306189)
                ·
                  refine ⟨10632323044295578096239821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28352861451454874923306189 10632323044295578096239821)
                  ·
                    refine ⟨3987121141610841786089933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10632323044295578096239821 3987121141610841786089933)
                    ·
                      refine ⟨1495170428104065669783725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3987121141610841786089933 1495170428104065669783725)
                      ·
                        rfl

theorem cell23_2911834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 4, 3, 3, 3].length) (baseStart_2911834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2911834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2911834 prefixEnd_2911834 := by exact prefixLift 2911834
  have htrace : WordTrace (prefixWord ++ tailWord_2911834) baseStart_2911834 baseEnd_2911834 := by
    simpa [prefixWord, tailWord_2911834, baseEnd_2911834] using wordTrace_append hprefix tailTrace_2911834
  have hstable : (prefixWord ++ tailWord_2911834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2911834).length < 2 ^ (prefixWord ++ tailWord_2911834).sum := by decide
  have hdescent : baseEnd_2911834 < baseStart_2911834 := by decide
  rcases family_descends (prefixWord ++ tailWord_2911834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2911848 : List Nat := [2, 1, 4, 3, 1, 3, 1, 1, 1, 2, 4]
def baseStart_2911848 : Nat := 118140960795 + 2911848 * 2 ^ 59
def prefixEnd_2911848 : Nat := 4983230072969 + 3 ^ 40 * 2911848 * 2
def baseEnd_2911848 : Nat := 1495177616833228615008661

theorem tailTrace_2911848 : CollatzResearch.WordTrace tailWord_2911848 prefixEnd_2911848 1495177616833228615008661 := by
  unfold tailWord_2911848
  simp only [CollatzResearch.WordTrace]
  refine ⟨53101910777439737445556099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70802547703252983260741465 53101910777439737445556099)
  ·
    refine ⟨79652866166159606168334149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53101910777439737445556099 79652866166159606168334149)
    ·
      refine ⟨14934912406154926156562653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79652866166159606168334149 14934912406154926156562653)
      ·
        refine ⟨5600592152308097308710995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14934912406154926156562653 5600592152308097308710995)
        ·
          refine ⟨8400888228462145963066493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5600592152308097308710995 8400888228462145963066493)
          ·
            refine ⟨3150333085673304736149935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8400888228462145963066493 3150333085673304736149935)
            ·
              refine ⟨4725499628509957104224903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3150333085673304736149935 4725499628509957104224903)
              ·
                refine ⟨7088249442764935656337355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4725499628509957104224903 7088249442764935656337355)
                ·
                  refine ⟨10632374164147403484506033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7088249442764935656337355 10632374164147403484506033)
                  ·
                    refine ⟨7974280623110552613379525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10632374164147403484506033 7974280623110552613379525)
                    ·
                      refine ⟨1495177616833228615008661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7974280623110552613379525 1495177616833228615008661)
                      ·
                        rfl

theorem cell23_2911848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_2911848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2911848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2911848 prefixEnd_2911848 := by exact prefixLift 2911848
  have htrace : WordTrace (prefixWord ++ tailWord_2911848) baseStart_2911848 baseEnd_2911848 := by
    simpa [prefixWord, tailWord_2911848, baseEnd_2911848] using wordTrace_append hprefix tailTrace_2911848
  have hstable : (prefixWord ++ tailWord_2911848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2911848).length < 2 ^ (prefixWord ++ tailWord_2911848).sum := by decide
  have hdescent : baseEnd_2911848 < baseStart_2911848 := by decide
  rcases family_descends (prefixWord ++ tailWord_2911848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2911902 : List Nat := [4, 3, 1, 1, 1, 2, 4, 1, 2, 1, 3]
def baseStart_2911902 : Nat := 118140960795 + 2911902 * 2 ^ 59
def prefixEnd_2911902 : Nat := 4983230072969 + 3 ^ 40 * 2911902 * 2
def baseEnd_2911902 : Nat := 1495205344788571403733413

theorem tailTrace_2911902 : CollatzResearch.WordTrace tailWord_2911902 prefixEnd_2911902 1495205344788571403733413 := by
  unfold tailWord_2911902
  simp only [CollatzResearch.WordTrace]
  refine ⟨13275723887085480264197245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70803860731122561409051973 13275723887085480264197245)
  ·
    refine ⟨4978396457657055099073967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13275723887085480264197245 4978396457657055099073967)
    ·
      refine ⟨7467594686485582648610951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4978396457657055099073967 7467594686485582648610951)
      ·
        refine ⟨11201392029728373972916427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7467594686485582648610951 11201392029728373972916427)
        ·
          refine ⟨16802088044592560959374641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11201392029728373972916427 16802088044592560959374641)
          ·
            refine ⟨12601566033444420719530981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16802088044592560959374641 12601566033444420719530981)
            ·
              refine ⟨2362793631270828884912059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12601566033444420719530981 2362793631270828884912059)
              ·
                refine ⟨3544190446906243327368089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2362793631270828884912059 3544190446906243327368089)
                ·
                  refine ⟨2658142835179682495526067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3544190446906243327368089 2658142835179682495526067)
                  ·
                    refine ⟨3987214252769523743289101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2658142835179682495526067 3987214252769523743289101)
                    ·
                      refine ⟨1495205344788571403733413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3987214252769523743289101 1495205344788571403733413)
                      ·
                        rfl

theorem cell23_2911902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 4, 1, 2, 1, 3].length) (baseStart_2911902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2911902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2911902 prefixEnd_2911902 := by exact prefixLift 2911902
  have htrace : WordTrace (prefixWord ++ tailWord_2911902) baseStart_2911902 baseEnd_2911902 := by
    simpa [prefixWord, tailWord_2911902, baseEnd_2911902] using wordTrace_append hprefix tailTrace_2911902
  have hstable : (prefixWord ++ tailWord_2911902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2911902).length < 2 ^ (prefixWord ++ tailWord_2911902).sum := by decide
  have hdescent : baseEnd_2911902 < baseStart_2911902 := by decide
  rcases family_descends (prefixWord ++ tailWord_2911902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2911925 : List Nat := [1, 3, 3, 3, 2, 1, 1, 2, 1, 4, 2]
def baseStart_2911925 : Nat := 118140960795 + 2911925 * 2 ^ 59
def prefixEnd_2911925 : Nat := 4983230072969 + 3 ^ 40 * 2911925 * 2
def baseEnd_2911925 : Nat := 1495217154843624813745807

theorem tailTrace_2911925 : CollatzResearch.WordTrace tailWord_2911925 prefixEnd_2911925 1495217154843624813745807 := by
  unfold tailWord_2911925
  simp only [CollatzResearch.WordTrace]
  refine ⟨106206629975600517041665229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70804419983733678027776819 106206629975600517041665229)
  ·
    refine ⟨39827486240850193890624461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106206629975600517041665229 39827486240850193890624461)
    ·
      refine ⟨14935307340318822708984173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39827486240850193890624461 14935307340318822708984173)
      ·
        refine ⟨5600740252619558515869065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14935307340318822708984173 5600740252619558515869065)
        ·
          refine ⟨4200555189464668886901799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5600740252619558515869065 4200555189464668886901799)
          ·
            refine ⟨6300832784197003330352699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4200555189464668886901799 6300832784197003330352699)
            ·
              refine ⟨9451249176295504995529049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6300832784197003330352699 9451249176295504995529049)
              ·
                refine ⟨7088436882221628746646787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9451249176295504995529049 7088436882221628746646787)
                ·
                  refine ⟨10632655323332443119970181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7088436882221628746646787 10632655323332443119970181)
                  ·
                    refine ⟨1993622873124833084994409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10632655323332443119970181 1993622873124833084994409)
                    ·
                      refine ⟨1495217154843624813745807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1993622873124833084994409 1495217154843624813745807)
                      ·
                        rfl

theorem cell23_2911925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 2, 1, 4, 2].length) (baseStart_2911925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2911925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2911925 prefixEnd_2911925 := by exact prefixLift 2911925
  have htrace : WordTrace (prefixWord ++ tailWord_2911925) baseStart_2911925 baseEnd_2911925 := by
    simpa [prefixWord, tailWord_2911925, baseEnd_2911925] using wordTrace_append hprefix tailTrace_2911925
  have hstable : (prefixWord ++ tailWord_2911925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2911925).length < 2 ^ (prefixWord ++ tailWord_2911925).sum := by decide
  have hdescent : baseEnd_2911925 < baseStart_2911925 := by decide
  rcases family_descends (prefixWord ++ tailWord_2911925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2911984 : List Nat := [2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 5]
def baseStart_2911984 : Nat := 118140960795 + 2911984 * 2 ^ 59
def prefixEnd_2911984 : Nat := 4983230072969 + 3 ^ 40 * 2911984 * 2
def baseEnd_2911984 : Nat := 1495247450202240082908035

theorem tailTrace_2911984 : CollatzResearch.WordTrace tailWord_2911984 prefixEnd_2911984 1495247450202240082908035 := by
  unfold tailWord_2911984
  simp only [CollatzResearch.WordTrace]
  refine ⟨53104390941193385059031503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70805854588257846745375337 53104390941193385059031503)
  ·
    refine ⟨79656586411790077588547255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53104390941193385059031503 79656586411790077588547255)
    ·
      refine ⟨119484879617685116382820883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79656586411790077588547255 119484879617685116382820883)
      ·
        refine ⟨179227319426527674574231325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119484879617685116382820883 179227319426527674574231325)
        ·
          refine ⟨67210244784947877965336747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 179227319426527674574231325 67210244784947877965336747)
          ·
            refine ⟨100815367177421816948005121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67210244784947877965336747 100815367177421816948005121)
            ·
              refine ⟨75611525383066362711003841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100815367177421816948005121 75611525383066362711003841)
              ·
                refine ⟨56708644037299772033252881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75611525383066362711003841 56708644037299772033252881)
                ·
                  refine ⟨42531483027974829024939661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56708644037299772033252881 42531483027974829024939661)
                  ·
                    refine ⟨15949306135490560884352373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42531483027974829024939661 15949306135490560884352373)
                    ·
                      refine ⟨1495247450202240082908035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15949306135490560884352373 1495247450202240082908035)
                      ·
                        rfl

theorem cell23_2911984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 5].length) (baseStart_2911984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2911984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2911984 prefixEnd_2911984 := by exact prefixLift 2911984
  have htrace : WordTrace (prefixWord ++ tailWord_2911984) baseStart_2911984 baseEnd_2911984 := by
    simpa [prefixWord, tailWord_2911984, baseEnd_2911984] using wordTrace_append hprefix tailTrace_2911984
  have hstable : (prefixWord ++ tailWord_2911984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2911984).length < 2 ^ (prefixWord ++ tailWord_2911984).sum := by decide
  have hdescent : baseEnd_2911984 < baseStart_2911984 := by decide
  rcases family_descends (prefixWord ++ tailWord_2911984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2912008 : List Nat := [2, 1, 3, 2, 2, 1, 4, 1, 3, 4]
def baseStart_2912008 : Nat := 118140960795 + 2912008 * 2 ^ 59
def prefixEnd_2912008 : Nat := 4983230072969 + 3 ^ 40 * 2912008 * 2
def baseEnd_2912008 : Nat := 498419924579315996335975

theorem tailTrace_2912008 : CollatzResearch.WordTrace tailWord_2912008 prefixEnd_2912008 498419924579315996335975 := by
  unfold tailWord_2912008
  simp only [CollatzResearch.WordTrace]
  refine ⟨53104828617149911108468339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70806438156199881477957785 53104828617149911108468339)
  ·
    refine ⟨79657242925724866662702509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53104828617149911108468339 79657242925724866662702509)
    ·
      refine ⟨29871466097146824998513441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79657242925724866662702509 29871466097146824998513441)
      ·
        refine ⟨22403599572860118748885081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29871466097146824998513441 22403599572860118748885081)
        ·
          refine ⟨16802699679645089061663811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22403599572860118748885081 16802699679645089061663811)
          ·
            refine ⟨25204049519467633592495717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16802699679645089061663811 25204049519467633592495717)
            ·
              refine ⟨4725759284900181298592947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25204049519467633592495717 4725759284900181298592947)
              ·
                refine ⟨7088638927350271947889421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4725759284900181298592947 7088638927350271947889421)
                ·
                  refine ⟨2658239597756351980458533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7088638927350271947889421 2658239597756351980458533)
                  ·
                    refine ⟨498419924579315996335975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2658239597756351980458533 498419924579315996335975)
                    ·
                      rfl

theorem cell23_2912008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 4, 1, 3, 4].length) (baseStart_2912008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2912008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2912008 prefixEnd_2912008 := by exact prefixLift 2912008
  have htrace : WordTrace (prefixWord ++ tailWord_2912008) baseStart_2912008 baseEnd_2912008 := by
    simpa [prefixWord, tailWord_2912008, baseEnd_2912008] using wordTrace_append hprefix tailTrace_2912008
  have hstable : (prefixWord ++ tailWord_2912008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2912008).length < 2 ^ (prefixWord ++ tailWord_2912008).sum := by decide
  have hdescent : baseEnd_2912008 < baseStart_2912008 := by decide
  rcases family_descends (prefixWord ++ tailWord_2912008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2912031 : List Nat := [1, 1, 2, 4, 2, 1, 1, 1, 2, 5, 3]
def baseStart_2912031 : Nat := 118140960795 + 2912031 * 2 ^ 59
def prefixEnd_2912031 : Nat := 4983230072969 + 3 ^ 40 * 2912031 * 2
def baseEnd_2912031 : Nat := 1495271583793001399020319

theorem tailTrace_2912031 : CollatzResearch.WordTrace tailWord_2912031 prefixEnd_2912031 1495271583793001399020319 := by
  unfold tailWord_2912031
  simp only [CollatzResearch.WordTrace]
  refine ⟨106210496113216497145023947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70806997408810998096682631 106210496113216497145023947)
  ·
    refine ⟨159315744169824745717535921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106210496113216497145023947 159315744169824745717535921)
    ·
      refine ⟨119486808127368559288151941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159315744169824745717535921 119486808127368559288151941)
      ·
        refine ⟨22403776523881604866528489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 119486808127368559288151941 22403776523881604866528489)
        ·
          refine ⟨16802832392911203649896367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22403776523881604866528489 16802832392911203649896367)
          ·
            refine ⟨25204248589366805474844551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16802832392911203649896367 25204248589366805474844551)
            ·
              refine ⟨37806372884050208212266827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25204248589366805474844551 37806372884050208212266827)
              ·
                refine ⟨56709559326075312318400241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37806372884050208212266827 56709559326075312318400241)
                ·
                  refine ⟨42532169494556484238800181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56709559326075312318400241 42532169494556484238800181)
                  ·
                    refine ⟨3987390890114670397387517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42532169494556484238800181 3987390890114670397387517)
                    ·
                      refine ⟨1495271583793001399020319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3987390890114670397387517 1495271583793001399020319)
                      ·
                        rfl

theorem cell23_2912031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 1, 2, 5, 3].length) (baseStart_2912031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2912031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2912031 prefixEnd_2912031 := by exact prefixLift 2912031
  have htrace : WordTrace (prefixWord ++ tailWord_2912031) baseStart_2912031 baseEnd_2912031 := by
    simpa [prefixWord, tailWord_2912031, baseEnd_2912031] using wordTrace_append hprefix tailTrace_2912031
  have hstable : (prefixWord ++ tailWord_2912031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2912031).length < 2 ^ (prefixWord ++ tailWord_2912031).sum := by decide
  have hdescent : baseEnd_2912031 < baseStart_2912031 := by decide
  rcases family_descends (prefixWord ++ tailWord_2912031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2912085 : List Nat := [1, 3, 2, 2, 2, 4, 1, 2, 1, 5]
def baseStart_2912085 : Nat := 118140960795 + 2912085 * 2 ^ 59
def prefixEnd_2912085 : Nat := 4983230072969 + 3 ^ 40 * 2912085 * 2
def baseEnd_2912085 : Nat := 498433103916114729248357

theorem tailTrace_2912085 : CollatzResearch.WordTrace tailWord_2912085 prefixEnd_2912085 498433103916114729248357 := by
  unfold tailWord_2912085
  simp only [CollatzResearch.WordTrace]
  refine ⟨106212465655020864367489709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70808310436680576244993139 106212465655020864367489709)
  ·
    refine ⟨39829674620632824137808641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106212465655020864367489709 39829674620632824137808641)
    ·
      refine ⟨29872255965474618103356481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39829674620632824137808641 29872255965474618103356481)
      ·
        refine ⟨22404191974105963577517361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29872255965474618103356481 22404191974105963577517361)
        ·
          refine ⟨16803143980579472683138021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22404191974105963577517361 16803143980579472683138021)
          ·
            refine ⟨3150589496358651128088379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16803143980579472683138021 3150589496358651128088379)
            ·
              refine ⟨4725884244537976692132569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3150589496358651128088379 4725884244537976692132569)
              ·
                refine ⟨3544413183403482519099427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4725884244537976692132569 3544413183403482519099427)
                ·
                  refine ⟨5316619775105223778649141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3544413183403482519099427 5316619775105223778649141)
                  ·
                    refine ⟨498433103916114729248357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5316619775105223778649141 498433103916114729248357)
                    ·
                      rfl

theorem cell23_2912085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 1, 2, 1, 5].length) (baseStart_2912085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2912085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2912085 prefixEnd_2912085 := by exact prefixLift 2912085
  have htrace : WordTrace (prefixWord ++ tailWord_2912085) baseStart_2912085 baseEnd_2912085 := by
    simpa [prefixWord, tailWord_2912085, baseEnd_2912085] using wordTrace_append hprefix tailTrace_2912085
  have hstable : (prefixWord ++ tailWord_2912085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2912085).length < 2 ^ (prefixWord ++ tailWord_2912085).sum := by decide
  have hdescent : baseEnd_2912085 < baseStart_2912085 := by decide
  rcases family_descends (prefixWord ++ tailWord_2912085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2912098 : List Nat := [3, 3, 2, 1, 2, 1, 1, 1, 3, 6]
def baseStart_2912098 : Nat := 118140960795 + 2912098 * 2 ^ 59
def prefixEnd_2912098 : Nat := 4983230072969 + 3 ^ 40 * 2912098 * 2
def baseEnd_2912098 : Nat := 498435328998950878960837

theorem tailTrace_2912098 : CollatzResearch.WordTrace tailWord_2912098 prefixEnd_2912098 498435328998950878960837 := by
  unfold tailWord_2912098
  simp only [CollatzResearch.WordTrace]
  refine ⟨26553234950993441896928237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70808626535982511725141965 26553234950993441896928237)
  ·
    refine ⟨9957463106622540711348089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26553234950993441896928237 9957463106622540711348089)
    ·
      refine ⟨7468097329966905533511067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9957463106622540711348089 7468097329966905533511067)
      ·
        refine ⟨11202145994950358300266601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7468097329966905533511067 11202145994950358300266601)
        ·
          refine ⟨8401609496212768725199951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11202145994950358300266601 8401609496212768725199951)
          ·
            refine ⟨12602414244319153087799927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8401609496212768725199951 12602414244319153087799927)
            ·
              refine ⟨18903621366478729631699891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12602414244319153087799927 18903621366478729631699891)
              ·
                refine ⟨28355432049718094447549837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18903621366478729631699891 28355432049718094447549837)
                ·
                  refine ⟨10633287018644285417831189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28355432049718094447549837 10633287018644285417831189)
                  ·
                    refine ⟨498435328998950878960837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10633287018644285417831189 498435328998950878960837)
                    ·
                      rfl

theorem cell23_2912098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 1, 3, 6].length) (baseStart_2912098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2912098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2912098 prefixEnd_2912098 := by exact prefixLift 2912098
  have htrace : WordTrace (prefixWord ++ tailWord_2912098) baseStart_2912098 baseEnd_2912098 := by
    simpa [prefixWord, tailWord_2912098, baseEnd_2912098] using wordTrace_append hprefix tailTrace_2912098
  have hstable : (prefixWord ++ tailWord_2912098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2912098).length < 2 ^ (prefixWord ++ tailWord_2912098).sum := by decide
  have hdescent : baseEnd_2912098 < baseStart_2912098 := by decide
  rcases family_descends (prefixWord ++ tailWord_2912098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2912108 : List Nat := [2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 5]
def baseStart_2912108 : Nat := 118140960795 + 2912108 * 2 ^ 59
def prefixEnd_2912108 : Nat := 4983230072969 + 3 ^ 40 * 2912108 * 2
def baseEnd_2912108 : Nat := 1495311121803397597757465

theorem tailTrace_2912108 : CollatzResearch.WordTrace tailWord_2912108 prefixEnd_2912108 1495311121803397597757465 := by
  unfold tailWord_2912108
  simp only [CollatzResearch.WordTrace]
  refine ⟨53106652266968769647788489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70808869689291692863717985 53106652266968769647788489)
  ·
    refine ⟨39829989200226577235841367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53106652266968769647788489 39829989200226577235841367)
    ·
      refine ⟨59744983800339865853762051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39829989200226577235841367 59744983800339865853762051)
      ·
        refine ⟨89617475700509798780643077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59744983800339865853762051 89617475700509798780643077)
        ·
          refine ⟨16803276693845587271370577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 89617475700509798780643077 16803276693845587271370577)
          ·
            refine ⟨12602457520384190453527933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16803276693845587271370577 12602457520384190453527933)
            ·
              refine ⟨4725921570144071420072975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12602457520384190453527933 4725921570144071420072975)
              ·
                refine ⟨7088882355216107130109463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4725921570144071420072975 7088882355216107130109463)
                ·
                  refine ⟨10633323532824160695164195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7088882355216107130109463 10633323532824160695164195)
                  ·
                    refine ⟨15949985299236241042746293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10633323532824160695164195 15949985299236241042746293)
                    ·
                      refine ⟨1495311121803397597757465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15949985299236241042746293 1495311121803397597757465)
                      ·
                        rfl

theorem cell23_2912108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 5].length) (baseStart_2912108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2912108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2912108 prefixEnd_2912108 := by exact prefixLift 2912108
  have htrace : WordTrace (prefixWord ++ tailWord_2912108) baseStart_2912108 baseEnd_2912108 := by
    simpa [prefixWord, tailWord_2912108, baseEnd_2912108] using wordTrace_append hprefix tailTrace_2912108
  have hstable : (prefixWord ++ tailWord_2912108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2912108).length < 2 ^ (prefixWord ++ tailWord_2912108).sum := by decide
  have hdescent : baseEnd_2912108 < baseStart_2912108 := by decide
  rcases family_descends (prefixWord ++ tailWord_2912108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2912135 : List Nat := [1, 1, 4, 2, 4, 1, 2, 1, 1, 2, 4]
def baseStart_2912135 : Nat := 118140960795 + 2912135 * 2 ^ 59
def prefixEnd_2912135 : Nat := 4983230072969 + 3 ^ 40 * 2912135 * 2
def baseEnd_2912135 : Nat := 1495324985781068992119841

theorem tailTrace_2912135 : CollatzResearch.WordTrace tailWord_2912135 prefixEnd_2912135 1495324985781068992119841 := by
  unfold tailWord_2912135
  simp only [CollatzResearch.WordTrace]
  refine ⟨106214289304839722906809859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70809526203226481937873239 106214289304839722906809859)
  ·
    refine ⟨159321433957259584360214789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106214289304839722906809859 159321433957259584360214789)
    ·
      refine ⟨29872768866986172067540273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 159321433957259584360214789 29872768866986172067540273)
      ·
        refine ⟨22404576650239629050655205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29872768866986172067540273 22404576650239629050655205)
        ·
          refine ⟨4200858121919930446997851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22404576650239629050655205 4200858121919930446997851)
          ·
            refine ⟨6301287182879895670496777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4200858121919930446997851 6301287182879895670496777)
            ·
              refine ⟨4725965387159921752872583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6301287182879895670496777 4725965387159921752872583)
              ·
                refine ⟨7088948080739882629308875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4725965387159921752872583 7088948080739882629308875)
                ·
                  refine ⟨10633422121109823943963313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7088948080739882629308875 10633422121109823943963313)
                  ·
                    refine ⟨7975066590832367957972485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10633422121109823943963313 7975066590832367957972485)
                    ·
                      refine ⟨1495324985781068992119841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7975066590832367957972485 1495324985781068992119841)
                      ·
                        rfl

theorem cell23_2912135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 2, 1, 1, 2, 4].length) (baseStart_2912135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2912135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2912135 prefixEnd_2912135 := by exact prefixLift 2912135
  have htrace : WordTrace (prefixWord ++ tailWord_2912135) baseStart_2912135 baseEnd_2912135 := by
    simpa [prefixWord, tailWord_2912135, baseEnd_2912135] using wordTrace_append hprefix tailTrace_2912135
  have hstable : (prefixWord ++ tailWord_2912135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2912135).length < 2 ^ (prefixWord ++ tailWord_2912135).sum := by decide
  have hdescent : baseEnd_2912135 < baseStart_2912135 := by decide
  rcases family_descends (prefixWord ++ tailWord_2912135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2912156 : List Nat := [2, 2, 3, 3, 1, 2, 2, 3, 1, 2, 2]
def baseStart_2912156 : Nat := 118140960795 + 2912156 * 2 ^ 59
def prefixEnd_2912156 : Nat := 4983230072969 + 3 ^ 40 * 2912156 * 2
def baseEnd_2912156 : Nat := 1495335768874813409957245

theorem tailTrace_2912156 : CollatzResearch.WordTrace tailWord_2912156 prefixEnd_2912156 1495335768874813409957245 := by
  unfold tailWord_2912156
  simp only [CollatzResearch.WordTrace]
  refine ⟨53107527618881821746662161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70810036825175762328882881 53107527618881821746662161)
  ·
    refine ⟨39830645714161366309996621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53107527618881821746662161 39830645714161366309996621)
    ·
      refine ⟨14936492142810512366248733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39830645714161366309996621 14936492142810512366248733)
      ·
        refine ⟨5601184553553942137343275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14936492142810512366248733 5601184553553942137343275)
        ·
          refine ⟨8401776830330913206014913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5601184553553942137343275 8401776830330913206014913)
          ·
            refine ⟨6301332622748184904511185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8401776830330913206014913 6301332622748184904511185)
            ·
              refine ⟨4725999467061138678383389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6301332622748184904511185 4725999467061138678383389)
              ·
                refine ⟨1772249800147927004393771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4725999467061138678383389 1772249800147927004393771)
                ·
                  refine ⟨2658374700221890506590657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1772249800147927004393771 2658374700221890506590657)
                  ·
                    refine ⟨1993781025166417879942993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2658374700221890506590657 1993781025166417879942993)
                    ·
                      refine ⟨1495335768874813409957245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1993781025166417879942993 1495335768874813409957245)
                      ·
                        rfl

theorem cell23_2912156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 2, 3, 1, 2, 2].length) (baseStart_2912156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2912156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2912156 prefixEnd_2912156 := by exact prefixLift 2912156
  have htrace : WordTrace (prefixWord ++ tailWord_2912156) baseStart_2912156 baseEnd_2912156 := by
    simpa [prefixWord, tailWord_2912156, baseEnd_2912156] using wordTrace_append hprefix tailTrace_2912156
  have hstable : (prefixWord ++ tailWord_2912156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2912156).length < 2 ^ (prefixWord ++ tailWord_2912156).sum := by decide
  have hdescent : baseEnd_2912156 < baseStart_2912156 := by decide
  rcases family_descends (prefixWord ++ tailWord_2912156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2912159 : List Nat := [1, 1, 2, 5, 3, 2, 2, 1, 1, 2, 3]
def baseStart_2912159 : Nat := 118140960795 + 2912159 * 2 ^ 59
def prefixEnd_2912159 : Nat := 4983230072969 + 3 ^ 40 * 2912159 * 2
def baseEnd_2912159 : Nat := 1495337309316776898219731

theorem tailTrace_2912159 : CollatzResearch.WordTrace tailWord_2912159 prefixEnd_2912159 1495337309316776898219731 := by
  unfold tailWord_2912159
  simp only [CollatzResearch.WordTrace]
  refine ⟨106215164656752775005683531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70810109771168516670455687 106215164656752775005683531)
  ·
    refine ⟨159322746985129162508525297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106215164656752775005683531 159322746985129162508525297)
    ·
      refine ⟨119492060238846871881393973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159322746985129162508525297 119492060238846871881393973)
      ·
        refine ⟨11202380647391894238880685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 119492060238846871881393973 11202380647391894238880685)
        ·
          refine ⟨4200892742771960339580257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11202380647391894238880685 4200892742771960339580257)
          ·
            refine ⟨3150669557078970254685193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4200892742771960339580257 3150669557078970254685193)
            ·
              refine ⟨2363002167809227691013895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3150669557078970254685193 2363002167809227691013895)
              ·
                refine ⟨3544503251713841536520843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2363002167809227691013895 3544503251713841536520843)
                ·
                  refine ⟨5316754877570762304781265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3544503251713841536520843 5316754877570762304781265)
                  ·
                    refine ⟨3987566158178071728585949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5316754877570762304781265 3987566158178071728585949)
                    ·
                      refine ⟨1495337309316776898219731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3987566158178071728585949 1495337309316776898219731)
                      ·
                        rfl

theorem cell23_2912159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 2, 1, 1, 2, 3].length) (baseStart_2912159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2912159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2912159 prefixEnd_2912159 := by exact prefixLift 2912159
  have htrace : WordTrace (prefixWord ++ tailWord_2912159) baseStart_2912159 baseEnd_2912159 := by
    simpa [prefixWord, tailWord_2912159, baseEnd_2912159] using wordTrace_append hprefix tailTrace_2912159
  have hstable : (prefixWord ++ tailWord_2912159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2912159).length < 2 ^ (prefixWord ++ tailWord_2912159).sum := by decide
  have hdescent : baseEnd_2912159 < baseStart_2912159 := by decide
  rcases family_descends (prefixWord ++ tailWord_2912159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2912189 : List Nat := [1, 4, 1, 2, 3, 2, 3, 1, 2, 1, 3]
def baseStart_2912189 : Nat := 118140960795 + 2912189 * 2 ^ 59
def prefixEnd_2912189 : Nat := 4983230072969 + 3 ^ 40 * 2912189 * 2
def baseEnd_2912189 : Nat := 1495352713736411780844593

theorem tailTrace_2912189 : CollatzResearch.WordTrace tailWord_2912189 prefixEnd_2912189 1495352713736411780844593 := by
  unfold tailWord_2912189
  simp only [CollatzResearch.WordTrace]
  refine ⟨106216258846644090129275621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70810839231096060086183747 106216258846644090129275621)
  ·
    refine ⟨19915548533745766899239179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 106216258846644090129275621 19915548533745766899239179)
    ·
      refine ⟨29873322800618650348858769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19915548533745766899239179 29873322800618650348858769)
      ·
        refine ⟨22404992100463987761644077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29873322800618650348858769 22404992100463987761644077)
        ·
          refine ⟨8401872037673995410616529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22404992100463987761644077 8401872037673995410616529)
          ·
            refine ⟨6301404028255496557962397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8401872037673995410616529 6301404028255496557962397)
            ·
              refine ⟨2363026510595811209235899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6301404028255496557962397 2363026510595811209235899)
              ·
                refine ⟨3544539765893716813853849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2363026510595811209235899 3544539765893716813853849)
                ·
                  refine ⟨2658404824420287610390387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3544539765893716813853849 2658404824420287610390387)
                  ·
                    refine ⟨3987607236630431415585581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2658404824420287610390387 3987607236630431415585581)
                    ·
                      refine ⟨1495352713736411780844593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3987607236630431415585581 1495352713736411780844593)
                      ·
                        rfl

theorem cell23_2912189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 3, 1, 2, 1, 3].length) (baseStart_2912189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2912189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2912189 prefixEnd_2912189 := by exact prefixLift 2912189
  have htrace : WordTrace (prefixWord ++ tailWord_2912189) baseStart_2912189 baseEnd_2912189 := by
    simpa [prefixWord, tailWord_2912189, baseEnd_2912189] using wordTrace_append hprefix tailTrace_2912189
  have hstable : (prefixWord ++ tailWord_2912189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2912189).length < 2 ^ (prefixWord ++ tailWord_2912189).sum := by decide
  have hdescent : baseEnd_2912189 < baseStart_2912189 := by decide
  rcases family_descends (prefixWord ++ tailWord_2912189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2912195 : List Nat := [1, 1, 1, 3, 1, 1, 2, 1, 8, 2, 2]
def baseStart_2912195 : Nat := 118140960795 + 2912195 * 2 ^ 59
def prefixEnd_2912195 : Nat := 4983230072969 + 3 ^ 40 * 2912195 * 2
def baseEnd_2912195 : Nat := 1495355794620338757369565

theorem tailTrace_2912195 : CollatzResearch.WordTrace tailWord_2912195 prefixEnd_2912195 1495355794620338757369565 := by
  unfold tailWord_2912195
  simp only [CollatzResearch.WordTrace]
  refine ⟨106216477684622353153994039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70810985123081568769329359 106216477684622353153994039)
  ·
    refine ⟨159324716526933529730991059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106216477684622353153994039 159324716526933529730991059)
    ·
      refine ⟨238987074790400294596486589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159324716526933529730991059 238987074790400294596486589)
      ·
        refine ⟨89620153046400110473682471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 238987074790400294596486589 89620153046400110473682471)
        ·
          refine ⟨134430229569600165710523707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89620153046400110473682471 134430229569600165710523707)
          ·
            refine ⟨201645344354400248565785561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134430229569600165710523707 201645344354400248565785561)
            ·
              refine ⟨151234008265800186424339171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 201645344354400248565785561 151234008265800186424339171)
              ·
                refine ⟨226851012398700279636508757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 151234008265800186424339171 226851012398700279636508757)
                ·
                  refine ⟨2658410301547268901990337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 226851012398700279636508757 2658410301547268901990337)
                  ·
                    refine ⟨1993807726160451676492753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2658410301547268901990337 1993807726160451676492753)
                    ·
                      refine ⟨1495355794620338757369565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1993807726160451676492753 1495355794620338757369565)
                      ·
                        rfl

theorem cell23_2912195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 8, 2, 2].length) (baseStart_2912195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2912195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2912195 prefixEnd_2912195 := by exact prefixLift 2912195
  have htrace : WordTrace (prefixWord ++ tailWord_2912195) baseStart_2912195 baseEnd_2912195 := by
    simpa [prefixWord, tailWord_2912195, baseEnd_2912195] using wordTrace_append hprefix tailTrace_2912195
  have hstable : (prefixWord ++ tailWord_2912195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2912195).length < 2 ^ (prefixWord ++ tailWord_2912195).sum := by decide
  have hdescent : baseEnd_2912195 < baseStart_2912195 := by decide
  rcases family_descends (prefixWord ++ tailWord_2912195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2912212 : List Nat := [2, 4, 1, 2, 1, 1, 1, 1, 6, 2, 2]
def baseStart_2912212 : Nat := 118140960795 + 2912212 * 2 ^ 59
def prefixEnd_2912212 : Nat := 4983230072969 + 3 ^ 40 * 2912212 * 2
def baseEnd_2912212 : Nat := 1495364523791465190856987

theorem tailTrace_2912212 : CollatzResearch.WordTrace tailWord_2912212 prefixEnd_2912212 1495364523791465190856987 := by
  unfold tailWord_2912212
  simp only [CollatzResearch.WordTrace]
  refine ⟨53108548862780382528681445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70811398483707176704908593 53108548862780382528681445)
  ·
    refine ⟨9957852911771321724127771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53108548862780382528681445 9957852911771321724127771)
    ·
      refine ⟨14936779367656982586191657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9957852911771321724127771 14936779367656982586191657)
      ·
        refine ⟨11202584525742736939643743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14936779367656982586191657 11202584525742736939643743)
        ·
          refine ⟨16803876788614105409465615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11202584525742736939643743 16803876788614105409465615)
          ·
            refine ⟨25205815182921158114198423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16803876788614105409465615 25205815182921158114198423)
            ·
              refine ⟨37808722774381737171297635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25205815182921158114198423 37808722774381737171297635)
              ·
                refine ⟨56713084161572605756946453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37808722774381737171297635 56713084161572605756946453)
                ·
                  refine ⟨2658425820073715894856865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 56713084161572605756946453 2658425820073715894856865)
                  ·
                    refine ⟨1993819365055286921142649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2658425820073715894856865 1993819365055286921142649)
                    ·
                      refine ⟨1495364523791465190856987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1993819365055286921142649 1495364523791465190856987)
                      ·
                        rfl

theorem cell23_2912212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 1, 6, 2, 2].length) (baseStart_2912212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2912212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2912212 prefixEnd_2912212 := by exact prefixLift 2912212
  have htrace : WordTrace (prefixWord ++ tailWord_2912212) baseStart_2912212 baseEnd_2912212 := by
    simpa [prefixWord, tailWord_2912212, baseEnd_2912212] using wordTrace_append hprefix tailTrace_2912212
  have hstable : (prefixWord ++ tailWord_2912212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2912212).length < 2 ^ (prefixWord ++ tailWord_2912212).sum := by decide
  have hdescent : baseEnd_2912212 < baseStart_2912212 := by decide
  rcases family_descends (prefixWord ++ tailWord_2912212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2912246 : List Nat := [5, 1, 1, 1, 4, 1, 1, 3, 2, 2, 2]
def baseStart_2912246 : Nat := 118140960795 + 2912246 * 2 ^ 59
def prefixEnd_2912246 : Nat := 4983230072969 + 3 ^ 40 * 2912246 * 2
def baseEnd_2912246 : Nat := 1495381982133718057831831

theorem tailTrace_2912246 : CollatzResearch.WordTrace tailWord_2912246 prefixEnd_2912246 1495381982133718057831831 := by
  unfold tailWord_2912246
  simp only [CollatzResearch.WordTrace]
  refine ⟨6638646112964849304006287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 70812225204958392576067061 6638646112964849304006287)
  ·
    refine ⟨9957969169447273956009431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6638646112964849304006287 9957969169447273956009431)
    ·
      refine ⟨14936953754170910934014147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9957969169447273956009431 14936953754170910934014147)
      ·
        refine ⟨22405430631256366401021221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14936953754170910934014147 22405430631256366401021221)
        ·
          refine ⟨4201018243360568700191479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22405430631256366401021221 4201018243360568700191479)
          ·
            refine ⟨6301527365040853050287219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4201018243360568700191479 6301527365040853050287219)
            ·
              refine ⟨9452291047561279575430829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6301527365040853050287219 9452291047561279575430829)
              ·
                refine ⟨3544609142835479840786561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9452291047561279575430829 3544609142835479840786561)
                ·
                  refine ⟨2658456857126609880589921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3544609142835479840786561 2658456857126609880589921)
                  ·
                    refine ⟨1993842642844957410442441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2658456857126609880589921 1993842642844957410442441)
                    ·
                      refine ⟨1495381982133718057831831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1993842642844957410442441 1495381982133718057831831)
                      ·
                        rfl

theorem cell23_2912246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 3, 2, 2, 2].length) (baseStart_2912246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2912246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2912246 prefixEnd_2912246 := by exact prefixLift 2912246
  have htrace : WordTrace (prefixWord ++ tailWord_2912246) baseStart_2912246 baseEnd_2912246 := by
    simpa [prefixWord, tailWord_2912246, baseEnd_2912246] using wordTrace_append hprefix tailTrace_2912246
  have hstable : (prefixWord ++ tailWord_2912246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2912246).length < 2 ^ (prefixWord ++ tailWord_2912246).sum := by decide
  have hdescent : baseEnd_2912246 < baseStart_2912246 := by decide
  rcases family_descends (prefixWord ++ tailWord_2912246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2912302 : List Nat := [4, 1, 3, 1, 1, 2, 1, 1, 1, 6, 2]
def baseStart_2912302 : Nat := 118140960795 + 2912302 * 2 ^ 59
def prefixEnd_2912302 : Nat := 4983230072969 + 3 ^ 40 * 2912302 * 2
def baseEnd_2912302 : Nat := 1495410737050369838731573

theorem tailTrace_2912302 : CollatzResearch.WordTrace tailWord_2912302 prefixEnd_2912302 1495410737050369838731573 := by
  unfold tailWord_2912302
  simp only [CollatzResearch.WordTrace]
  refine ⟨13277547536904338803517395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70813586863489806952092773 13277547536904338803517395)
  ·
    refine ⟨19916321305356508205276093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13277547536904338803517395 19916321305356508205276093)
    ·
      refine ⟨7468620489508690576978535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19916321305356508205276093 7468620489508690576978535)
      ·
        refine ⟨11202930734263035865467803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7468620489508690576978535 11202930734263035865467803)
        ·
          refine ⟨16804396101394553798201705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11202930734263035865467803 16804396101394553798201705)
          ·
            refine ⟨12603297076045915348651279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16804396101394553798201705 12603297076045915348651279)
            ·
              refine ⟨18904945614068873022976919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12603297076045915348651279 18904945614068873022976919)
              ·
                refine ⟨28357418421103309534465379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18904945614068873022976919 28357418421103309534465379)
                ·
                  refine ⟨42536127631654964301698069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28357418421103309534465379 42536127631654964301698069)
                  ·
                    refine ⟨1993880982733826451642097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 42536127631654964301698069 1993880982733826451642097)
                    ·
                      refine ⟨1495410737050369838731573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1993880982733826451642097 1495410737050369838731573)
                      ·
                        rfl

theorem cell23_2912302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 1, 1, 6, 2].length) (baseStart_2912302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2912302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2912302 prefixEnd_2912302 := by exact prefixLift 2912302
  have htrace : WordTrace (prefixWord ++ tailWord_2912302) baseStart_2912302 baseEnd_2912302 := by
    simpa [prefixWord, tailWord_2912302, baseEnd_2912302] using wordTrace_append hprefix tailTrace_2912302
  have hstable : (prefixWord ++ tailWord_2912302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2912302).length < 2 ^ (prefixWord ++ tailWord_2912302).sum := by decide
  have hdescent : baseEnd_2912302 < baseStart_2912302 := by decide
  rcases family_descends (prefixWord ++ tailWord_2912302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2912312 : List Nat := [2, 1, 2, 1, 6, 1, 1, 2, 3, 4]
def baseStart_2912312 : Nat := 118140960795 + 2912312 * 2 ^ 59
def prefixEnd_2912312 : Nat := 4983230072969 + 3 ^ 40 * 2912312 * 2
def baseEnd_2912312 : Nat := 498471957285638266535509

theorem tailTrace_2912312 : CollatzResearch.WordTrace tailWord_2912312 prefixEnd_2912312 498471957285638266535509 := by
  unfold tailWord_2912312
  simp only [CollatzResearch.WordTrace]
  refine ⟨53110372512599241068001595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70813830016798988090668793 53110372512599241068001595)
  ·
    refine ⟨79665558768898861602002393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53110372512599241068001595 79665558768898861602002393)
    ·
      refine ⟨59749169076674146201501795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79665558768898861602002393 59749169076674146201501795)
      ·
        refine ⟨89623753615011219302252693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59749169076674146201501795 89623753615011219302252693)
        ·
          refine ⟨4201113450703650904793095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 89623753615011219302252693 4201113450703650904793095)
          ·
            refine ⟨6301670176055476357189643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4201113450703650904793095 6301670176055476357189643)
            ·
              refine ⟨9452505264083214535784465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6301670176055476357189643 9452505264083214535784465)
              ·
                refine ⟨7089378948062410901838349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9452505264083214535784465 7089378948062410901838349)
                ·
                  refine ⟨2658517105523404088189381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7089378948062410901838349 2658517105523404088189381)
                  ·
                    refine ⟨498471957285638266535509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2658517105523404088189381 498471957285638266535509)
                    ·
                      rfl

theorem cell23_2912312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 2, 3, 4].length) (baseStart_2912312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2912312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2912312 prefixEnd_2912312 := by exact prefixLift 2912312
  have htrace : WordTrace (prefixWord ++ tailWord_2912312) baseStart_2912312 baseEnd_2912312 := by
    simpa [prefixWord, tailWord_2912312, baseEnd_2912312] using wordTrace_append hprefix tailTrace_2912312
  have hstable : (prefixWord ++ tailWord_2912312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2912312).length < 2 ^ (prefixWord ++ tailWord_2912312).sum := by decide
  have hdescent : baseEnd_2912312 < baseStart_2912312 := by decide
  rcases family_descends (prefixWord ++ tailWord_2912312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2912352 : List Nat := [2, 1, 1, 3, 2, 3, 1, 3, 3, 1, 3]
def baseStart_2912352 : Nat := 118140960795 + 2912352 * 2 ^ 59
def prefixEnd_2912352 : Nat := 4983230072969 + 3 ^ 40 * 2912352 * 2
def baseEnd_2912352 : Nat := 1495436411083094643106343

theorem tailTrace_2912352 : CollatzResearch.WordTrace tailWord_2912352 prefixEnd_2912352 1495436411083094643106343 := by
  unfold tailWord_2912352
  simp only [CollatzResearch.WordTrace]
  refine ⟨53111101972526784483729655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70814802630035712644972873 53111101972526784483729655)
  ·
    refine ⟨79666652958790176725594483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53111101972526784483729655 79666652958790176725594483)
    ·
      refine ⟨119499979438185265088391725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79666652958790176725594483 119499979438185265088391725)
      ·
        refine ⟨44812492289319474408146897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119499979438185265088391725 44812492289319474408146897)
        ·
          refine ⟨33609369216989605806110173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44812492289319474408146897 33609369216989605806110173)
          ·
            refine ⟨12603513456371102177291315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33609369216989605806110173 12603513456371102177291315)
            ·
              refine ⟨18905270184556653265936973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12603513456371102177291315 18905270184556653265936973)
              ·
                refine ⟨7089476319208744974726365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18905270184556653265936973 7089476319208744974726365)
                ·
                  refine ⟨2658553619703279365522387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7089476319208744974726365 2658553619703279365522387)
                  ·
                    refine ⟨3987830429554919048283581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2658553619703279365522387 3987830429554919048283581)
                    ·
                      refine ⟨1495436411083094643106343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3987830429554919048283581 1495436411083094643106343)
                      ·
                        rfl

theorem cell23_2912352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 3, 3, 1, 3].length) (baseStart_2912352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2912352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2912352 prefixEnd_2912352 := by exact prefixLift 2912352
  have htrace : WordTrace (prefixWord ++ tailWord_2912352) baseStart_2912352 baseEnd_2912352 := by
    simpa [prefixWord, tailWord_2912352, baseEnd_2912352] using wordTrace_append hprefix tailTrace_2912352
  have hstable : (prefixWord ++ tailWord_2912352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2912352).length < 2 ^ (prefixWord ++ tailWord_2912352).sum := by decide
  have hdescent : baseEnd_2912352 < baseStart_2912352 := by decide
  rcases family_descends (prefixWord ++ tailWord_2912352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2912395 : List Nat := [1, 1, 1, 1, 4, 1, 1, 1, 7, 2, 3]
def baseStart_2912395 : Nat := 118140960795 + 2912395 * 2 ^ 59
def prefixEnd_2912395 : Nat := 4983230072969 + 3 ^ 40 * 2912395 * 2
def baseEnd_2912395 : Nat := 1495458490751237974868645

theorem tailTrace_2912395 : CollatzResearch.WordTrace tailWord_2912395 prefixEnd_2912395 1495458490751237974868645 := by
  unfold tailWord_2912395
  simp only [CollatzResearch.WordTrace]
  refine ⟨106223772283897787311274639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70815848189265191540849759 106223772283897787311274639)
  ·
    refine ⟨159335658425846680966911959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106223772283897787311274639 159335658425846680966911959)
    ·
      refine ⟨239003487638770021450367939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159335658425846680966911959 239003487638770021450367939)
      ·
        refine ⟨358505231458155032175551909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239003487638770021450367939 358505231458155032175551909)
        ·
          refine ⟨67219730898404068532915983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 358505231458155032175551909 67219730898404068532915983)
          ·
            refine ⟨100829596347606102799373975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67219730898404068532915983 100829596347606102799373975)
            ·
              refine ⟨151244394521409154199060963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100829596347606102799373975 151244394521409154199060963)
              ·
                refine ⟨226866591782113731298591445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 151244394521409154199060963 226866591782113731298591445)
                ·
                  refine ⟨5317185744893290577310737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 226866591782113731298591445 5317185744893290577310737)
                  ·
                    refine ⟨3987889308669967932983053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5317185744893290577310737 3987889308669967932983053)
                    ·
                      refine ⟨1495458490751237974868645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3987889308669967932983053 1495458490751237974868645)
                      ·
                        rfl

theorem cell23_2912395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 7, 2, 3].length) (baseStart_2912395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2912395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2912395 prefixEnd_2912395 := by exact prefixLift 2912395
  have htrace : WordTrace (prefixWord ++ tailWord_2912395) baseStart_2912395 baseEnd_2912395 := by
    simpa [prefixWord, tailWord_2912395, baseEnd_2912395] using wordTrace_append hprefix tailTrace_2912395
  have hstable : (prefixWord ++ tailWord_2912395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2912395).length < 2 ^ (prefixWord ++ tailWord_2912395).sum := by decide
  have hdescent : baseEnd_2912395 < baseStart_2912395 := by decide
  rcases family_descends (prefixWord ++ tailWord_2912395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2912402 : List Nat := [3, 2, 3, 1, 1, 1, 1, 3, 4, 4]
def baseStart_2912402 : Nat := 118140960795 + 2912402 * 2 ^ 59
def prefixEnd_2912402 : Nat := 4983230072969 + 3 ^ 40 * 2912402 * 2
def baseEnd_2912402 : Nat := 498487361705273149160371

theorem tailTrace_2912402 : CollatzResearch.WordTrace tailWord_2912402 prefixEnd_2912402 498487361705273149160371 := by
  unfold tailWord_2912402
  simp only [CollatzResearch.WordTrace]
  refine ⟨26556006898718106876694865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70816018396581618337852973 26556006898718106876694865)
  ·
    refine ⟨19917005174038580157521149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26556006898718106876694865 19917005174038580157521149)
    ·
      refine ⟨7468876940264467559070431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19917005174038580157521149 7468876940264467559070431)
      ·
        refine ⟨11203315410396701338605647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7468876940264467559070431 11203315410396701338605647)
        ·
          refine ⟨16804973115595052007908471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11203315410396701338605647 16804973115595052007908471)
          ·
            refine ⟨25207459673392578011862707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16804973115595052007908471 25207459673392578011862707)
            ·
              refine ⟨37811189510088867017794061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25207459673392578011862707 37811189510088867017794061)
              ·
                refine ⟨14179196066283325131672773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37811189510088867017794061 14179196066283325131672773)
                ·
                  refine ⟨2658599262428123462188645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14179196066283325131672773 2658599262428123462188645)
                  ·
                    refine ⟨498487361705273149160371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2658599262428123462188645 498487361705273149160371)
                    ·
                      rfl

theorem cell23_2912402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 3, 4, 4].length) (baseStart_2912402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2912402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2912402 prefixEnd_2912402 := by exact prefixLift 2912402
  have htrace : WordTrace (prefixWord ++ tailWord_2912402) baseStart_2912402 baseEnd_2912402 := by
    simpa [prefixWord, tailWord_2912402, baseEnd_2912402] using wordTrace_append hprefix tailTrace_2912402
  have hstable : (prefixWord ++ tailWord_2912402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2912402).length < 2 ^ (prefixWord ++ tailWord_2912402).sum := by decide
  have hdescent : baseEnd_2912402 < baseStart_2912402 := by decide
  rcases family_descends (prefixWord ++ tailWord_2912402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2912412 : List Nat := [2, 2, 3, 2, 1, 1, 2, 2, 3, 2, 3]
def baseStart_2912412 : Nat := 118140960795 + 2912412 * 2 ^ 59
def prefixEnd_2912412 : Nat := 4983230072969 + 3 ^ 40 * 2912412 * 2
def baseEnd_2912412 : Nat := 1495467219922364408356067

theorem tailTrace_2912412 : CollatzResearch.WordTrace tailWord_2912412 prefixEnd_2912412 1495467219922364408356067 := by
  unfold tailWord_2912412
  simp only [CollatzResearch.WordTrace]
  refine ⟨53112196162418099607321745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70816261549890799476428993 53112196162418099607321745)
  ·
    refine ⟨39834147121813574705491309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53112196162418099607321745 39834147121813574705491309)
    ·
      refine ⟨14937805170680090514559241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39834147121813574705491309 14937805170680090514559241)
      ·
        refine ⟨11203353878010067885919431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14937805170680090514559241 11203353878010067885919431)
        ·
          refine ⟨16805030817015101828879147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11203353878010067885919431 16805030817015101828879147)
          ·
            refine ⟨25207546225522652743318721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16805030817015101828879147 25207546225522652743318721)
            ·
              refine ⟨18905659669141989557489041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25207546225522652743318721 18905659669141989557489041)
              ·
                refine ⟨14179244751856492168116781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18905659669141989557489041 14179244751856492168116781)
                ·
                  refine ⟨5317216781946184563043793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14179244751856492168116781 5317216781946184563043793)
                  ·
                    refine ⟨3987912586459638422282845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5317216781946184563043793 3987912586459638422282845)
                    ·
                      refine ⟨1495467219922364408356067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3987912586459638422282845 1495467219922364408356067)
                      ·
                        rfl

theorem cell23_2912412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 2, 3, 2, 3].length) (baseStart_2912412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2912412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2912412 prefixEnd_2912412 := by exact prefixLift 2912412
  have htrace : WordTrace (prefixWord ++ tailWord_2912412) baseStart_2912412 baseEnd_2912412 := by
    simpa [prefixWord, tailWord_2912412, baseEnd_2912412] using wordTrace_append hprefix tailTrace_2912412
  have hstable : (prefixWord ++ tailWord_2912412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2912412).length < 2 ^ (prefixWord ++ tailWord_2912412).sum := by decide
  have hdescent : baseEnd_2912412 < baseStart_2912412 := by decide
  rcases family_descends (prefixWord ++ tailWord_2912412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2912415 : List Nat := [1, 1, 2, 6, 1, 1, 1, 10]
def baseStart_2912415 : Nat := 118140960795 + 2912415 * 2 ^ 59
def prefixEnd_2912415 : Nat := 4983230072969 + 3 ^ 40 * 2912415 * 2
def baseEnd_2912415 : Nat := 55387731865345477652539

theorem tailTrace_2912415 : CollatzResearch.WordTrace tailWord_2912415 prefixEnd_2912415 55387731865345477652539 := by
  unfold tailWord_2912415
  simp only [CollatzResearch.WordTrace]
  refine ⟨106224501743825330727002699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70816334495883553818001799 106224501743825330727002699)
  ·
    refine ⟨159336752615737996090504049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106224501743825330727002699 159336752615737996090504049)
    ·
      refine ⟨119502564461803497067878037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159336752615737996090504049 119502564461803497067878037)
      ·
        refine ⟨5601682709147038925056783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 119502564461803497067878037 5601682709147038925056783)
        ·
          refine ⟨8402524063720558387585175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5601682709147038925056783 8402524063720558387585175)
          ·
            refine ⟨12603786095580837581377763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8402524063720558387585175 12603786095580837581377763)
            ·
              refine ⟨18905679143371256372066645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12603786095580837581377763 18905679143371256372066645)
              ·
                refine ⟨55387731865345477652539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 18905679143371256372066645 55387731865345477652539)
                ·
                  rfl

theorem cell23_2912415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 10].length) (baseStart_2912415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2912415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2912415 prefixEnd_2912415 := by exact prefixLift 2912415
  have htrace : WordTrace (prefixWord ++ tailWord_2912415) baseStart_2912415 baseEnd_2912415 := by
    simpa [prefixWord, tailWord_2912415, baseEnd_2912415] using wordTrace_append hprefix tailTrace_2912415
  have hstable : (prefixWord ++ tailWord_2912415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2912415).length < 2 ^ (prefixWord ++ tailWord_2912415).sum := by decide
  have hdescent : baseEnd_2912415 < baseStart_2912415 := by decide
  rcases family_descends (prefixWord ++ tailWord_2912415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2912429 : List Nat := [1, 5, 2, 1, 2, 2, 1, 1, 3, 2, 3]
def baseStart_2912429 : Nat := 118140960795 + 2912429 * 2 ^ 59
def prefixEnd_2912429 : Nat := 4983230072969 + 3 ^ 40 * 2912429 * 2
def baseEnd_2912429 : Nat := 1495475949093490841843489

theorem tailTrace_2912429 : CollatzResearch.WordTrace tailWord_2912429 prefixEnd_2912429 1495475949093490841843489 := by
  unfold tailWord_2912429
  simp only [CollatzResearch.WordTrace]
  refine ⟨106225012365774611118012341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70816674910516407412008227 106225012365774611118012341)
  ·
    refine ⟨9958594909291369792313657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 106225012365774611118012341 9958594909291369792313657)
    ·
      refine ⟨7468946181968527344235243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9958594909291369792313657 7468946181968527344235243)
      ·
        refine ⟨11203419272952791016352865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7468946181968527344235243 11203419272952791016352865)
        ·
          refine ⟨8402564454714593262264649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11203419272952791016352865 8402564454714593262264649)
          ·
            refine ⟨6301923341035944946698487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8402564454714593262264649 6301923341035944946698487)
            ·
              refine ⟨9452885011553917420047731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6301923341035944946698487 9452885011553917420047731)
              ·
                refine ⟨14179327517330876130071597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9452885011553917420047731 14179327517330876130071597)
                ·
                  refine ⟨5317247818999078548776849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14179327517330876130071597 5317247818999078548776849)
                  ·
                    refine ⟨3987935864249308911582637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5317247818999078548776849 3987935864249308911582637)
                    ·
                      refine ⟨1495475949093490841843489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3987935864249308911582637 1495475949093490841843489)
                      ·
                        rfl

theorem cell23_2912429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 1, 3, 2, 3].length) (baseStart_2912429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2912429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2912429 prefixEnd_2912429 := by exact prefixLift 2912429
  have htrace : WordTrace (prefixWord ++ tailWord_2912429) baseStart_2912429 baseEnd_2912429 := by
    simpa [prefixWord, tailWord_2912429, baseEnd_2912429] using wordTrace_append hprefix tailTrace_2912429
  have hstable : (prefixWord ++ tailWord_2912429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2912429).length < 2 ^ (prefixWord ++ tailWord_2912429).sum := by decide
  have hdescent : baseEnd_2912429 < baseStart_2912429 := by decide
  rcases family_descends (prefixWord ++ tailWord_2912429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2912442 : List Nat := [3, 1, 1, 1, 2, 2, 2, 1, 6, 1, 3]
def baseStart_2912442 : Nat := 118140960795 + 2912442 * 2 ^ 59
def prefixEnd_2912442 : Nat := 4983230072969 + 3 ^ 40 * 2912442 * 2
def baseEnd_2912442 : Nat := 1495482624341999290980929

theorem tailTrace_2912442 : CollatzResearch.WordTrace tailWord_2912442 prefixEnd_2912442 1495482624341999290980929 := by
  unfold tailWord_2912442
  simp only [CollatzResearch.WordTrace]
  refine ⟨26556371628681878584558895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70816991009818342892157053 26556371628681878584558895)
  ·
    refine ⟨39834557443022817876838343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26556371628681878584558895 39834557443022817876838343)
    ·
      refine ⟨59751836164534226815257515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39834557443022817876838343 59751836164534226815257515)
      ·
        refine ⟨89627754246801340222886273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59751836164534226815257515 89627754246801340222886273)
        ·
          refine ⟨67220815685101005167164705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89627754246801340222886273 67220815685101005167164705)
          ·
            refine ⟨50415611763825753875373529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67220815685101005167164705 50415611763825753875373529)
            ·
              refine ⟨37811708822869315406530147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50415611763825753875373529 37811708822869315406530147)
              ·
                refine ⟨56717563234303973109795221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37811708822869315406530147 56717563234303973109795221)
                ·
                  refine ⟨2658635776607998739521651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 56717563234303973109795221 2658635776607998739521651)
                  ·
                    refine ⟨3987953664911998109282477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2658635776607998739521651 3987953664911998109282477)
                    ·
                      refine ⟨1495482624341999290980929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3987953664911998109282477 1495482624341999290980929)
                      ·
                        rfl

theorem cell23_2912442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 1, 6, 1, 3].length) (baseStart_2912442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2912442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2912442 prefixEnd_2912442 := by exact prefixLift 2912442
  have htrace : WordTrace (prefixWord ++ tailWord_2912442) baseStart_2912442 baseEnd_2912442 := by
    simpa [prefixWord, tailWord_2912442, baseEnd_2912442] using wordTrace_append hprefix tailTrace_2912442
  have hstable : (prefixWord ++ tailWord_2912442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2912442).length < 2 ^ (prefixWord ++ tailWord_2912442).sum := by decide
  have hdescent : baseEnd_2912442 < baseStart_2912442 := by decide
  rcases family_descends (prefixWord ++ tailWord_2912442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2912446 : List Nat := [4, 2, 1, 1, 5, 1, 1, 1, 1, 1, 5]
def baseStart_2912446 : Nat := 118140960795 + 2912446 * 2 ^ 59
def prefixEnd_2912446 : Nat := 4983230072969 + 3 ^ 40 * 2912446 * 2
def baseEnd_2912446 : Nat := 1495484678264617275330911

theorem tailTrace_2912446 : CollatzResearch.WordTrace tailWord_2912446 prefixEnd_2912446 1495484678264617275330911 := by
  unfold tailWord_2912446
  simp only [CollatzResearch.WordTrace]
  refine ⟨13278204050839127877672649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70817088271142015347587461 13278204050839127877672649)
  ·
    refine ⟨9958653038129345908254487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13278204050839127877672649 9958653038129345908254487)
    ·
      refine ⟨14937979557194018862381731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9958653038129345908254487 14937979557194018862381731)
      ·
        refine ⟨22406969335791028293572597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14937979557194018862381731 22406969335791028293572597)
        ·
          refine ⟨2100653375230408902522431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22406969335791028293572597 2100653375230408902522431)
          ·
            refine ⟨3150980062845613353783647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2100653375230408902522431 3150980062845613353783647)
            ·
              refine ⟨4726470094268420030675471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3150980062845613353783647 4726470094268420030675471)
              ·
                refine ⟨7089705141402630046013207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4726470094268420030675471 7089705141402630046013207)
                ·
                  refine ⟨10634557712103945069019811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7089705141402630046013207 10634557712103945069019811)
                  ·
                    refine ⟨15951836568155917603529717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10634557712103945069019811 15951836568155917603529717)
                    ·
                      refine ⟨1495484678264617275330911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15951836568155917603529717 1495484678264617275330911)
                      ·
                        rfl

theorem cell23_2912446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 1, 1, 1, 1, 5].length) (baseStart_2912446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2912446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2912446 prefixEnd_2912446 := by exact prefixLift 2912446
  have htrace : WordTrace (prefixWord ++ tailWord_2912446) baseStart_2912446 baseEnd_2912446 := by
    simpa [prefixWord, tailWord_2912446, baseEnd_2912446] using wordTrace_append hprefix tailTrace_2912446
  have hstable : (prefixWord ++ tailWord_2912446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2912446).length < 2 ^ (prefixWord ++ tailWord_2912446).sum := by decide
  have hdescent : baseEnd_2912446 < baseStart_2912446 := by decide
  rcases family_descends (prefixWord ++ tailWord_2912446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2912459 : List Nat := [1, 1, 1, 1, 3, 2, 6, 2, 2, 1, 3]
def baseStart_2912459 : Nat := 118140960795 + 2912459 * 2 ^ 59
def prefixEnd_2912459 : Nat := 4983230072969 + 3 ^ 40 * 2912459 * 2
def baseEnd_2912459 : Nat := 1495491353513125724468351

theorem tailTrace_2912459 : CollatzResearch.WordTrace tailWord_2912459 prefixEnd_2912459 1495491353513125724468351 := by
  unfold tailWord_2912459
  simp only [CollatzResearch.WordTrace]
  refine ⟨106226106555665926241604431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70817404370443950827736287 106226106555665926241604431)
  ·
    refine ⟨159339159833498889362406647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106226106555665926241604431 159339159833498889362406647)
    ·
      refine ⟨239008739750248334043609971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159339159833498889362406647 239008739750248334043609971)
      ·
        refine ⟨358513109625372501065414957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239008739750248334043609971 358513109625372501065414957)
        ·
          refine ⟨134442416109514687899530609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 358513109625372501065414957 134442416109514687899530609)
          ·
            refine ⟨100831812082136015924647957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134442416109514687899530609 100831812082136015924647957)
            ·
              refine ⟨4726491191350125746467873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 100831812082136015924647957 4726491191350125746467873)
              ·
                refine ⟨3544868393512594309850905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4726491191350125746467873 3544868393512594309850905)
                ·
                  refine ⟨2658651295134445732388179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3544868393512594309850905 2658651295134445732388179)
                  ·
                    refine ⟨3987976942701668598582269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2658651295134445732388179 3987976942701668598582269)
                    ·
                      refine ⟨1495491353513125724468351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3987976942701668598582269 1495491353513125724468351)
                      ·
                        rfl

theorem cell23_2912459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 6, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 6, 2, 2, 1, 3].length) (baseStart_2912459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2912459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2912459 prefixEnd_2912459 := by exact prefixLift 2912459
  have htrace : WordTrace (prefixWord ++ tailWord_2912459) baseStart_2912459 baseEnd_2912459 := by
    simpa [prefixWord, tailWord_2912459, baseEnd_2912459] using wordTrace_append hprefix tailTrace_2912459
  have hstable : (prefixWord ++ tailWord_2912459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2912459).length < 2 ^ (prefixWord ++ tailWord_2912459).sum := by decide
  have hdescent : baseEnd_2912459 < baseStart_2912459 := by decide
  rcases family_descends (prefixWord ++ tailWord_2912459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2912460 : List Nat := [2, 2, 1, 6, 1, 1, 1, 4, 1, 2, 2]
def baseStart_2912460 : Nat := 118140960795 + 2912460 * 2 ^ 59
def prefixEnd_2912460 : Nat := 4983230072969 + 3 ^ 40 * 2912460 * 2
def baseEnd_2912460 : Nat := 1495491866993780220555847

theorem tailTrace_2912460 : CollatzResearch.WordTrace tailWord_2912460 prefixEnd_2912460 1495491866993780220555847 := by
  unfold tailWord_2912460
  simp only [CollatzResearch.WordTrace]
  refine ⟨53113071514331151706195417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70817428685774868941593889 53113071514331151706195417)
  ·
    refine ⟨39834803635748363779646563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53113071514331151706195417 39834803635748363779646563)
    ·
      refine ⟨59752205453622545669469845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39834803635748363779646563 59752205453622545669469845)
      ·
        refine ⟨2800884630638556828256399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 59752205453622545669469845 2800884630638556828256399)
        ·
          refine ⟨4201326945957835242384599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2800884630638556828256399 4201326945957835242384599)
          ·
            refine ⟨6301990418936752863576899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4201326945957835242384599 6301990418936752863576899)
            ·
              refine ⟨9452985628405129295365349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6301990418936752863576899 9452985628405129295365349)
              ·
                refine ⟨1772434805325961742881003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9452985628405129295365349 1772434805325961742881003)
                ·
                  refine ⟨2658652207988942614321505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1772434805325961742881003 2658652207988942614321505)
                  ·
                    refine ⟨1993989155991706960741129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2658652207988942614321505 1993989155991706960741129)
                    ·
                      refine ⟨1495491866993780220555847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1993989155991706960741129 1495491866993780220555847)
                      ·
                        rfl

theorem cell23_2912460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 4, 1, 2, 2].length) (baseStart_2912460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2912460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2912460 prefixEnd_2912460 := by exact prefixLift 2912460
  have htrace : WordTrace (prefixWord ++ tailWord_2912460) baseStart_2912460 baseEnd_2912460 := by
    simpa [prefixWord, tailWord_2912460, baseEnd_2912460] using wordTrace_append hprefix tailTrace_2912460
  have hstable : (prefixWord ++ tailWord_2912460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2912460).length < 2 ^ (prefixWord ++ tailWord_2912460).sum := by decide
  have hdescent : baseEnd_2912460 < baseStart_2912460 := by decide
  rcases family_descends (prefixWord ++ tailWord_2912460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2912465 : List Nat := [1, 2, 2, 1, 2, 2, 3, 1, 2, 3, 4]
def baseStart_2912465 : Nat := 118140960795 + 2912465 * 2 ^ 59
def prefixEnd_2912465 : Nat := 4983230072969 + 3 ^ 40 * 2912465 * 2
def baseEnd_2912465 : Nat := 1495494434397052700993323

theorem tailTrace_2912465 : CollatzResearch.WordTrace tailWord_2912465 prefixEnd_2912465 1495494434397052700993323 := by
  unfold tailWord_2912465
  simp only [CollatzResearch.WordTrace]
  refine ⟨106226325393644189266322849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70817550262429459510881899 106226325393644189266322849)
  ·
    refine ⟨79669744045233141949742137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106226325393644189266322849 79669744045233141949742137)
    ·
      refine ⟨59752308033924856462306603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79669744045233141949742137 59752308033924856462306603)
      ·
        refine ⟨89628462050887284693459905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59752308033924856462306603 89628462050887284693459905)
        ·
          refine ⟨67221346538165463520094929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89628462050887284693459905 67221346538165463520094929)
          ·
            refine ⟨50416009903624097640071197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67221346538165463520094929 50416009903624097640071197)
            ·
              refine ⟨18906003713859036615026699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50416009903624097640071197 18906003713859036615026699)
              ·
                refine ⟨28359005570788554922540049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18906003713859036615026699 28359005570788554922540049)
                ·
                  refine ⟨21269254178091416191905037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28359005570788554922540049 21269254178091416191905037)
                  ·
                    refine ⟨7975970316784281071964389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21269254178091416191905037 7975970316784281071964389)
                    ·
                      refine ⟨1495494434397052700993323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7975970316784281071964389 1495494434397052700993323)
                      ·
                        rfl

theorem cell23_2912465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 1, 2, 3, 4].length) (baseStart_2912465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2912465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2912465 prefixEnd_2912465 := by exact prefixLift 2912465
  have htrace : WordTrace (prefixWord ++ tailWord_2912465) baseStart_2912465 baseEnd_2912465 := by
    simpa [prefixWord, tailWord_2912465, baseEnd_2912465] using wordTrace_append hprefix tailTrace_2912465
  have hstable : (prefixWord ++ tailWord_2912465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2912465).length < 2 ^ (prefixWord ++ tailWord_2912465).sum := by decide
  have hdescent : baseEnd_2912465 < baseStart_2912465 := by decide
  rcases family_descends (prefixWord ++ tailWord_2912465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2912499 : List Nat := [1, 1, 1, 2, 2, 4, 2, 2, 4, 2, 2]
def baseStart_2912499 : Nat := 118140960795 + 2912499 * 2 ^ 59
def prefixEnd_2912499 : Nat := 4983230072969 + 3 ^ 40 * 2912499 * 2
def baseEnd_2912499 : Nat := 1495511892739305567968167

theorem tailTrace_2912499 : CollatzResearch.WordTrace tailWord_2912499 prefixEnd_2912499 1495511892739305567968167 := by
  unfold tailWord_2912499
  simp only [CollatzResearch.WordTrace]
  refine ⟨106227565475521013073060551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70818376983680675382040367 106227565475521013073060551)
  ·
    refine ⟨159341348213281519609590827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106227565475521013073060551 159341348213281519609590827)
    ·
      refine ⟨239012022319922279414386241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159341348213281519609590827 239012022319922279414386241)
      ·
        refine ⟨179259016739941709560789681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 239012022319922279414386241 179259016739941709560789681)
        ·
          refine ⟨134444262554956282170592261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179259016739941709560789681 134444262554956282170592261)
          ·
            refine ⟨25208299229054302906986049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 134444262554956282170592261 25208299229054302906986049)
            ·
              refine ⟨18906224421790727180239537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25208299229054302906986049 18906224421790727180239537)
              ·
                refine ⟨14179668316343045385179653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18906224421790727180239537 14179668316343045385179653)
                ·
                  refine ⟨2658687809314321009721185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14179668316343045385179653 2658687809314321009721185)
                  ·
                    refine ⟨1994015856985740757290889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2658687809314321009721185 1994015856985740757290889)
                    ·
                      refine ⟨1495511892739305567968167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1994015856985740757290889 1495511892739305567968167)
                      ·
                        rfl

theorem cell23_2912499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 2, 4, 2, 2].length) (baseStart_2912499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2912499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2912499 prefixEnd_2912499 := by exact prefixLift 2912499
  have htrace : WordTrace (prefixWord ++ tailWord_2912499) baseStart_2912499 baseEnd_2912499 := by
    simpa [prefixWord, tailWord_2912499, baseEnd_2912499] using wordTrace_append hprefix tailTrace_2912499
  have hstable : (prefixWord ++ tailWord_2912499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2912499).length < 2 ^ (prefixWord ++ tailWord_2912499).sum := by decide
  have hdescent : baseEnd_2912499 < baseStart_2912499 := by decide
  rcases family_descends (prefixWord ++ tailWord_2912499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2912502 : List Nat := [5, 1, 1, 1, 1, 1, 2, 3, 2, 1, 5]
def baseStart_2912502 : Nat := 118140960795 + 2912502 * 2 ^ 59
def prefixEnd_2912502 : Nat := 4983230072969 + 3 ^ 40 * 2912502 * 2
def baseEnd_2912502 : Nat := 1495513433181269056230653

theorem tailTrace_2912502 : CollatzResearch.WordTrace tailWord_2912502 prefixEnd_2912502 1495513433181269056230653 := by
  unfold tailWord_2912502
  simp only [CollatzResearch.WordTrace]
  refine ⟨6639229680906884036588735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 70818449929673429723613173 6639229680906884036588735)
  ·
    refine ⟨9958844521360326054883103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6639229680906884036588735 9958844521360326054883103)
    ·
      refine ⟨14938266782040489082324655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9958844521360326054883103 14938266782040489082324655)
      ·
        refine ⟨22407400173060733623486983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14938266782040489082324655 22407400173060733623486983)
        ·
          refine ⟨33611100259591100435230475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22407400173060733623486983 33611100259591100435230475)
          ·
            refine ⟨50416650389386650652845713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33611100259591100435230475 50416650389386650652845713)
            ·
              refine ⟨37812487792039987989634285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50416650389386650652845713 37812487792039987989634285)
              ·
                refine ⟨14179682922014995496112857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37812487792039987989634285 14179682922014995496112857)
                ·
                  refine ⟨10634762191511246622084643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14179682922014995496112857 10634762191511246622084643)
                  ·
                    refine ⟨15952143287266869933126965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10634762191511246622084643 15952143287266869933126965)
                    ·
                      refine ⟨1495513433181269056230653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15952143287266869933126965 1495513433181269056230653)
                      ·
                        rfl

theorem cell23_2912502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 3, 2, 1, 5].length) (baseStart_2912502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2912502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2912502 prefixEnd_2912502 := by exact prefixLift 2912502
  have htrace : WordTrace (prefixWord ++ tailWord_2912502) baseStart_2912502 baseEnd_2912502 := by
    simpa [prefixWord, tailWord_2912502, baseEnd_2912502] using wordTrace_append hprefix tailTrace_2912502
  have hstable : (prefixWord ++ tailWord_2912502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2912502).length < 2 ^ (prefixWord ++ tailWord_2912502).sum := by decide
  have hdescent : baseEnd_2912502 < baseStart_2912502 := by decide
  rcases family_descends (prefixWord ++ tailWord_2912502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2912569 : List Nat := [1, 2, 1, 6, 1, 2, 1, 2, 2, 5]
def baseStart_2912569 : Nat := 118140960795 + 2912569 * 2 ^ 59
def prefixEnd_2912569 : Nat := 4983230072969 + 3 ^ 40 * 2912569 * 2
def baseEnd_2912569 : Nat := 498515945461706764697615

theorem tailTrace_2912569 : CollatzResearch.WordTrace tailWord_2912569 prefixEnd_2912569 498515945461706764697615 := by
  unfold tailWord_2912569
  simp only [CollatzResearch.WordTrace]
  refine ⟨106230118585267415028108761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70820079056844943352072507 106230118585267415028108761)
  ·
    refine ⟨79672588938950561271081571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106230118585267415028108761 79672588938950561271081571)
    ·
      refine ⟨119508883408425841906622357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79672588938950561271081571 119508883408425841906622357)
      ·
        refine ⟨5601978909769961339372923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 119508883408425841906622357 5601978909769961339372923)
        ·
          refine ⟨8402968364654942009059385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5601978909769961339372923 8402968364654942009059385)
          ·
            refine ⟨6302226273491206506794539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8402968364654942009059385 6302226273491206506794539)
            ·
              refine ⟨9453339410236809760191809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6302226273491206506794539 9453339410236809760191809)
              ·
                refine ⟨7090004557677607320143857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9453339410236809760191809 7090004557677607320143857)
                ·
                  refine ⟨5317503418258205490107893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7090004557677607320143857 5317503418258205490107893)
                  ·
                    refine ⟨498515945461706764697615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5317503418258205490107893 498515945461706764697615)
                    ·
                      rfl

theorem cell23_2912569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 2, 2, 5].length) (baseStart_2912569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2912569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2912569 prefixEnd_2912569 := by exact prefixLift 2912569
  have htrace : WordTrace (prefixWord ++ tailWord_2912569) baseStart_2912569 baseEnd_2912569 := by
    simpa [prefixWord, tailWord_2912569, baseEnd_2912569] using wordTrace_append hprefix tailTrace_2912569
  have hstable : (prefixWord ++ tailWord_2912569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2912569).length < 2 ^ (prefixWord ++ tailWord_2912569).sum := by decide
  have hdescent : baseEnd_2912569 < baseStart_2912569 := by decide
  rcases family_descends (prefixWord ++ tailWord_2912569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2912595 : List Nat := [1, 1, 1, 2, 1, 1, 4, 2, 10]
def baseStart_2912595 : Nat := 118140960795 + 2912595 * 2 ^ 59
def prefixEnd_2912595 : Nat := 4983230072969 + 3 ^ 40 * 2912595 * 2
def baseEnd_2912595 : Nat := 166173465209126354707525

theorem tailTrace_2912595 : CollatzResearch.WordTrace tailWord_2912595 prefixEnd_2912595 166173465209126354707525 := by
  unfold tailWord_2912595
  simp only [CollatzResearch.WordTrace]
  refine ⟨106231066883173221468555239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70820711255448814312370159 106231066883173221468555239)
  ·
    refine ⟨159346600324759832202832859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106231066883173221468555239 159346600324759832202832859)
    ·
      refine ⟨239019900487139748304249289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159346600324759832202832859 239019900487139748304249289)
      ·
        refine ⟨179264925365354811228186967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 239019900487139748304249289 179264925365354811228186967)
        ·
          refine ⟨268897388048032216842280451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179264925365354811228186967 268897388048032216842280451)
          ·
            refine ⟨403346082072048325263420677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 268897388048032216842280451 403346082072048325263420677)
            ·
              refine ⟨75627390388509060986891377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 403346082072048325263420677 75627390388509060986891377)
              ·
                refine ⟨56720542791381795740168533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75627390388509060986891377 56720542791381795740168533)
                ·
                  refine ⟨166173465209126354707525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 56720542791381795740168533 166173465209126354707525)
                  ·
                    rfl

theorem cell23_2912595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 2, 10].length) (baseStart_2912595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2912595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2912595 prefixEnd_2912595 := by exact prefixLift 2912595
  have htrace : WordTrace (prefixWord ++ tailWord_2912595) baseStart_2912595 baseEnd_2912595 := by
    simpa [prefixWord, tailWord_2912595, baseEnd_2912595] using wordTrace_append hprefix tailTrace_2912595
  have hstable : (prefixWord ++ tailWord_2912595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2912595).length < 2 ^ (prefixWord ++ tailWord_2912595).sum := by decide
  have hdescent : baseEnd_2912595 < baseStart_2912595 := by decide
  rcases family_descends (prefixWord ++ tailWord_2912595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2912629 : List Nat := [1, 3, 4, 1, 2, 1, 1, 4, 6]
def baseStart_2912629 : Nat := 118140960795 + 2912629 * 2 ^ 59
def prefixEnd_2912629 : Nat := 4983230072969 + 3 ^ 40 * 2912629 * 2
def baseEnd_2912629 : Nat := 166175405024932228815841

theorem tailTrace_2912629 : CollatzResearch.WordTrace tailWord_2912629 prefixEnd_2912629 166175405024932228815841 := by
  unfold tailWord_2912629
  simp only [CollatzResearch.WordTrace]
  refine ⟨106232306965050045275292941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70821537976700030183528627 106232306965050045275292941)
  ·
    refine ⟨39837115111893766978234853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106232306965050045275292941 39837115111893766978234853)
    ·
      refine ⟨7469459083480081308419035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39837115111893766978234853 7469459083480081308419035)
      ·
        refine ⟨11204188625220121962628553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7469459083480081308419035 11204188625220121962628553)
        ·
          refine ⟨8403141468915091471971415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11204188625220121962628553 8403141468915091471971415)
          ·
            refine ⟨12604712203372637207957123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8403141468915091471971415 12604712203372637207957123)
            ·
              refine ⟨18907068305058955811935685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12604712203372637207957123 18907068305058955811935685)
              ·
                refine ⟨3545075307198554214737941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18907068305058955811935685 3545075307198554214737941)
                ·
                  refine ⟨166175405024932228815841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3545075307198554214737941 166175405024932228815841)
                  ·
                    rfl

theorem cell23_2912629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 4, 6].length) (baseStart_2912629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2912629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2912629 prefixEnd_2912629 := by exact prefixLift 2912629
  have htrace : WordTrace (prefixWord ++ tailWord_2912629) baseStart_2912629 baseEnd_2912629 := by
    simpa [prefixWord, tailWord_2912629, baseEnd_2912629] using wordTrace_append hprefix tailTrace_2912629
  have hstable : (prefixWord ++ tailWord_2912629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2912629).length < 2 ^ (prefixWord ++ tailWord_2912629).sum := by decide
  have hdescent : baseEnd_2912629 < baseStart_2912629 := by decide
  rcases family_descends (prefixWord ++ tailWord_2912629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2912660 : List Nat := [2, 4, 2, 1, 4, 1, 1, 1, 2, 2, 3]
def baseStart_2912660 : Nat := 118140960795 + 2912660 * 2 ^ 59
def prefixEnd_2912660 : Nat := 4983230072969 + 3 ^ 40 * 2912660 * 2
def baseEnd_2912660 : Nat := 1495594563124679438054927

theorem tailTrace_2912660 : CollatzResearch.WordTrace tailWord_2912660 prefixEnd_2912660 1495594563124679438054927 := by
  unfold tailWord_2912660
  simp only [CollatzResearch.WordTrace]
  refine ⟨53116718813968868784835717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70822291751958491713114289 53116718813968868784835717)
  ·
    refine ⟨9959384777619162897156697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53116718813968868784835717 9959384777619162897156697)
    ·
      refine ⟨7469538583214372172867523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9959384777619162897156697 7469538583214372172867523)
      ·
        refine ⟨11204307874821558259301285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7469538583214372172867523 11204307874821558259301285)
        ·
          refine ⟨2100807726529042173618991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11204307874821558259301285 2100807726529042173618991)
          ·
            refine ⟨3151211589793563260428487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2100807726529042173618991 3151211589793563260428487)
            ·
              refine ⟨4726817384690344890642731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3151211589793563260428487 4726817384690344890642731)
              ·
                refine ⟨7090226077035517335964097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4726817384690344890642731 7090226077035517335964097)
                ·
                  refine ⟨5317669557776638001973073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7090226077035517335964097 5317669557776638001973073)
                  ·
                    refine ⟨3988252168332478501479805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5317669557776638001973073 3988252168332478501479805)
                    ·
                      refine ⟨1495594563124679438054927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3988252168332478501479805 1495594563124679438054927)
                      ·
                        rfl

theorem cell23_2912660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 1, 1, 2, 2, 3].length) (baseStart_2912660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2912660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2912660 prefixEnd_2912660 := by exact prefixLift 2912660
  have htrace : WordTrace (prefixWord ++ tailWord_2912660) baseStart_2912660 baseEnd_2912660 := by
    simpa [prefixWord, tailWord_2912660, baseEnd_2912660] using wordTrace_append hprefix tailTrace_2912660
  have hstable : (prefixWord ++ tailWord_2912660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2912660).length < 2 ^ (prefixWord ++ tailWord_2912660).sum := by decide
  have hdescent : baseEnd_2912660 < baseStart_2912660 := by decide
  rcases family_descends (prefixWord ++ tailWord_2912660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2912666 : List Nat := [3, 1, 1, 4, 1, 3, 1, 1, 1, 5, 2]
def baseStart_2912666 : Nat := 118140960795 + 2912666 * 2 ^ 59
def prefixEnd_2912666 : Nat := 4983230072969 + 3 ^ 40 * 2912666 * 2
def baseEnd_2912666 : Nat := 1495597644008606414579899

theorem tailTrace_2912666 : CollatzResearch.WordTrace tailWord_2912666 prefixEnd_2912666 1495597644008606414579899 := by
  unfold tailWord_2912666
  simp only [CollatzResearch.WordTrace]
  refine ⟨26558414116479000148597463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70822437643944000396259901 26558414116479000148597463)
  ·
    refine ⟨39837621174718500222896195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26558414116479000148597463 39837621174718500222896195)
    ·
      refine ⟨59756431762077750334344293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39837621174718500222896195 59756431762077750334344293)
      ·
        refine ⟨11204330955389578187689555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59756431762077750334344293 11204330955389578187689555)
        ·
          refine ⟨16806496433084367281534333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11204330955389578187689555 16806496433084367281534333)
          ·
            refine ⟨6302436162406637730575375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16806496433084367281534333 6302436162406637730575375)
            ·
              refine ⟨9453654243609956595863063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6302436162406637730575375 9453654243609956595863063)
              ·
                refine ⟨14180481365414934893794595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9453654243609956595863063 14180481365414934893794595)
                ·
                  refine ⟨21270722048122402340691893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14180481365414934893794595 21270722048122402340691893)
                  ·
                    refine ⟨1994130192011475219439865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21270722048122402340691893 1994130192011475219439865)
                    ·
                      refine ⟨1495597644008606414579899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1994130192011475219439865 1495597644008606414579899)
                      ·
                        rfl

theorem cell23_2912666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 1, 1, 5, 2].length) (baseStart_2912666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2912666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2912666 prefixEnd_2912666 := by exact prefixLift 2912666
  have htrace : WordTrace (prefixWord ++ tailWord_2912666) baseStart_2912666 baseEnd_2912666 := by
    simpa [prefixWord, tailWord_2912666, baseEnd_2912666] using wordTrace_append hprefix tailTrace_2912666
  have hstable : (prefixWord ++ tailWord_2912666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2912666).length < 2 ^ (prefixWord ++ tailWord_2912666).sum := by decide
  have hdescent : baseEnd_2912666 < baseStart_2912666 := by decide
  rcases family_descends (prefixWord ++ tailWord_2912666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2912676 : List Nat := [2, 3, 1, 2, 1, 1, 6, 1, 1, 5]
def baseStart_2912676 : Nat := 118140960795 + 2912676 * 2 ^ 59
def prefixEnd_2912676 : Nat := 4983230072969 + 3 ^ 40 * 2912676 * 2
def baseEnd_2912676 : Nat := 498534259605050458484951

theorem tailTrace_2912676 : CollatzResearch.WordTrace tailWord_2912676 prefixEnd_2912676 498534259605050458484951 := by
  unfold tailWord_2912676
  simp only [CollatzResearch.WordTrace]
  refine ⟨53117010597939886151126941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70822680797253181534835921 53117010597939886151126941)
  ·
    refine ⟨19918878974227457306672603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53117010597939886151126941 19918878974227457306672603)
    ·
      refine ⟨29878318461341185960008905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19918878974227457306672603 29878318461341185960008905)
      ·
        refine ⟨22408738846005889470006679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29878318461341185960008905 22408738846005889470006679)
        ·
          refine ⟨33613108269008834205010019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22408738846005889470006679 33613108269008834205010019)
          ·
            refine ⟨50419662403513251307515029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33613108269008834205010019 50419662403513251307515029)
            ·
              refine ⟨2363421675164683655039767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 50419662403513251307515029 2363421675164683655039767)
              ·
                refine ⟨3545132512747025482559651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2363421675164683655039767 3545132512747025482559651)
                ·
                  refine ⟨5317698769120538223839477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3545132512747025482559651 5317698769120538223839477)
                  ·
                    refine ⟨498534259605050458484951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5317698769120538223839477 498534259605050458484951)
                    ·
                      rfl

theorem cell23_2912676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 6, 1, 1, 5].length) (baseStart_2912676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2912676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2912676 prefixEnd_2912676 := by exact prefixLift 2912676
  have htrace : WordTrace (prefixWord ++ tailWord_2912676) baseStart_2912676 baseEnd_2912676 := by
    simpa [prefixWord, tailWord_2912676, baseEnd_2912676] using wordTrace_append hprefix tailTrace_2912676
  have hstable : (prefixWord ++ tailWord_2912676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2912676).length < 2 ^ (prefixWord ++ tailWord_2912676).sum := by decide
  have hdescent : baseEnd_2912676 < baseStart_2912676 := by decide
  rcases family_descends (prefixWord ++ tailWord_2912676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2912726 : List Nat := [5, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4]
def baseStart_2912726 : Nat := 118140960795 + 2912726 * 2 ^ 59
def prefixEnd_2912726 : Nat := 4983230072969 + 3 ^ 40 * 2912726 * 2
def baseEnd_2912726 : Nat := 1495628452847876179829623

theorem tailTrace_2912726 : CollatzResearch.WordTrace tailWord_2912726 prefixEnd_2912726 1495628452847876179829623 := by
  unfold tailWord_2912726
  simp only [CollatzResearch.WordTrace]
  refine ⟨6639740302856164427598377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 70823896563799087227716021 6639740302856164427598377)
  ·
    refine ⟨4979805227142123320698783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6639740302856164427598377 4979805227142123320698783)
    ·
      refine ⟨7469707840713184981048175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4979805227142123320698783 7469707840713184981048175)
      ·
        refine ⟨11204561761069777471572263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7469707840713184981048175 11204561761069777471572263)
        ·
          refine ⟨16806842641604666207358395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11204561761069777471572263 16806842641604666207358395)
          ·
            refine ⟨25210263962406999311037593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16806842641604666207358395 25210263962406999311037593)
            ·
              refine ⟨18907697971805249483278195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25210263962406999311037593 18907697971805249483278195)
              ·
                refine ⟨28361546957707874224917293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18907697971805249483278195 28361546957707874224917293)
                ·
                  refine ⟨10635580109140452834343985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28361546957707874224917293 10635580109140452834343985)
                  ·
                    refine ⟨7976685081855339625757989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10635580109140452834343985 7976685081855339625757989)
                    ·
                      refine ⟨1495628452847876179829623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7976685081855339625757989 1495628452847876179829623)
                      ·
                        rfl

theorem cell23_2912726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_2912726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2912726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2912726 prefixEnd_2912726 := by exact prefixLift 2912726
  have htrace : WordTrace (prefixWord ++ tailWord_2912726) baseStart_2912726 baseEnd_2912726 := by
    simpa [prefixWord, tailWord_2912726, baseEnd_2912726] using wordTrace_append hprefix tailTrace_2912726
  have hstable : (prefixWord ++ tailWord_2912726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2912726).length < 2 ^ (prefixWord ++ tailWord_2912726).sum := by decide
  have hdescent : baseEnd_2912726 < baseStart_2912726 := by decide
  rcases family_descends (prefixWord ++ tailWord_2912726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2912729 : List Nat := [1, 2, 1, 2, 4, 1, 2, 1, 3, 3, 3]
def baseStart_2912729 : Nat := 118140960795 + 2912729 * 2 ^ 59
def prefixEnd_2912729 : Nat := 4983230072969 + 3 ^ 40 * 2912729 * 2
def baseEnd_2912729 : Nat := 1495629993289839668092109

theorem tailTrace_2912729 : CollatzResearch.WordTrace tailWord_2912729 prefixEnd_2912729 1495629993289839668092109 := by
  unfold tailWord_2912729
  simp only [CollatzResearch.WordTrace]
  refine ⟨106235954264687762353933241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70823969509791841569288827 106235954264687762353933241)
  ·
    refine ⟨79676965698515821765449931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106235954264687762353933241 79676965698515821765449931)
    ·
      refine ⟨119515448547773732648174897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79676965698515821765449931 119515448547773732648174897)
      ·
        refine ⟨89636586410830299486131173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119515448547773732648174897 89636586410830299486131173)
        ·
          refine ⟨16806859952030681153649595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 89636586410830299486131173 16806859952030681153649595)
          ·
            refine ⟨25210289928046021730474393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16806859952030681153649595 25210289928046021730474393)
            ·
              refine ⟨18907717446034516297855795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25210289928046021730474393 18907717446034516297855795)
              ·
                refine ⟨28361576169051774446783693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18907717446034516297855795 28361576169051774446783693)
                ·
                  refine ⟨10635591063394415417543885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28361576169051774446783693 10635591063394415417543885)
                  ·
                    refine ⟨3988346648772905781578957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10635591063394415417543885 3988346648772905781578957)
                    ·
                      refine ⟨1495629993289839668092109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3988346648772905781578957 1495629993289839668092109)
                      ·
                        rfl

theorem cell23_2912729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 1, 3, 3, 3].length) (baseStart_2912729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2912729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2912729 prefixEnd_2912729 := by exact prefixLift 2912729
  have htrace : WordTrace (prefixWord ++ tailWord_2912729) baseStart_2912729 baseEnd_2912729 := by
    simpa [prefixWord, tailWord_2912729, baseEnd_2912729] using wordTrace_append hprefix tailTrace_2912729
  have hstable : (prefixWord ++ tailWord_2912729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2912729).length < 2 ^ (prefixWord ++ tailWord_2912729).sum := by decide
  have hdescent : baseEnd_2912729 < baseStart_2912729 := by decide
  rcases family_descends (prefixWord ++ tailWord_2912729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2912757 : List Nat := [1, 3, 5, 1, 2, 2, 2, 1, 2, 4]
def baseStart_2912757 : Nat := 118140960795 + 2912757 * 2 ^ 59
def prefixEnd_2912757 : Nat := 4983230072969 + 3 ^ 40 * 2912757 * 2
def baseEnd_2912757 : Nat := 498548123582721852847327

theorem tailTrace_2912757 : CollatzResearch.WordTrace tailWord_2912757 prefixEnd_2912757 498548123582721852847327 := by
  unfold tailWord_2912757
  simp only [CollatzResearch.WordTrace]
  refine ⟨106236975508586323135952525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70824650339057548757301683 106236975508586323135952525)
  ·
    refine ⟨39838865815719871175982197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106236975508586323135952525 39838865815719871175982197)
    ·
      refine ⟨3734893670223737922748331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 39838865815719871175982197 3734893670223737922748331)
      ·
        refine ⟨5602340505335606884122497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3734893670223737922748331 5602340505335606884122497)
        ·
          refine ⟨4201755379001705163091873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5602340505335606884122497 4201755379001705163091873)
          ·
            refine ⟨3151316534251278872318905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4201755379001705163091873 3151316534251278872318905)
            ·
              refine ⟨2363487400688459154239179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3151316534251278872318905 2363487400688459154239179)
              ·
                refine ⟨3545231101032688731358769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2363487400688459154239179 3545231101032688731358769)
                ·
                  refine ⟨2658923325774516548519077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3545231101032688731358769 2658923325774516548519077)
                  ·
                    refine ⟨498548123582721852847327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2658923325774516548519077 498548123582721852847327)
                    ·
                      rfl

theorem cell23_2912757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_2912757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2912757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2912757 prefixEnd_2912757 := by exact prefixLift 2912757
  have htrace : WordTrace (prefixWord ++ tailWord_2912757) baseStart_2912757 baseEnd_2912757 := by
    simpa [prefixWord, tailWord_2912757, baseEnd_2912757] using wordTrace_append hprefix tailTrace_2912757
  have hstable : (prefixWord ++ tailWord_2912757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2912757).length < 2 ^ (prefixWord ++ tailWord_2912757).sum := by decide
  have hdescent : baseEnd_2912757 < baseStart_2912757 := by decide
  rcases family_descends (prefixWord ++ tailWord_2912757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2912773 : List Nat := [1, 3, 1, 1, 2, 2, 5, 2, 1, 3, 2]
def baseStart_2912773 : Nat := 118140960795 + 2912773 * 2 ^ 59
def prefixEnd_2912773 : Nat := 4983230072969 + 3 ^ 40 * 2912773 * 2
def baseEnd_2912773 : Nat := 1495652586438637495941907

theorem tailTrace_2912773 : CollatzResearch.WordTrace tailWord_2912773 prefixEnd_2912773 1495652586438637495941907 := by
  unfold tailWord_2912773
  simp only [CollatzResearch.WordTrace]
  refine ⟨106237559076528357868534973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70825039384352238579023315 106237559076528357868534973)
  ·
    refine ⟨39839084653698134200700615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106237559076528357868534973 39839084653698134200700615)
    ·
      refine ⟨59758626980547201301050923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39839084653698134200700615 59758626980547201301050923)
      ·
        refine ⟨89637940470820801951576385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59758626980547201301050923 89637940470820801951576385)
        ·
          refine ⟨67228455353115601463682289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89637940470820801951576385 67228455353115601463682289)
          ·
            refine ⟨50421341514836701097761717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67228455353115601463682289 50421341514836701097761717)
            ·
              refine ⟨4727000767015940727915161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50421341514836701097761717 4727000767015940727915161)
              ·
                refine ⟨3545250575261955545936371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4727000767015940727915161 3545250575261955545936371)
                ·
                  refine ⟨5317875862892933318904557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3545250575261955545936371 5317875862892933318904557)
                  ·
                    refine ⟨1994203448584849994589209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5317875862892933318904557 1994203448584849994589209)
                    ·
                      refine ⟨1495652586438637495941907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1994203448584849994589209 1495652586438637495941907)
                      ·
                        rfl

theorem cell23_2912773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 5, 2, 1, 3, 2].length) (baseStart_2912773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2912773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2912773 prefixEnd_2912773 := by exact prefixLift 2912773
  have htrace : WordTrace (prefixWord ++ tailWord_2912773) baseStart_2912773 baseEnd_2912773 := by
    simpa [prefixWord, tailWord_2912773, baseEnd_2912773] using wordTrace_append hprefix tailTrace_2912773
  have hstable : (prefixWord ++ tailWord_2912773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2912773).length < 2 ^ (prefixWord ++ tailWord_2912773).sum := by decide
  have hdescent : baseEnd_2912773 < baseStart_2912773 := by decide
  rcases family_descends (prefixWord ++ tailWord_2912773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2912789 : List Nat := [1, 3, 2, 1, 3, 1, 1, 3, 2, 1, 5]
def baseStart_2912789 : Nat := 118140960795 + 2912789 * 2 ^ 59
def prefixEnd_2912789 : Nat := 4983230072969 + 3 ^ 40 * 2912789 * 2
def baseEnd_2912789 : Nat := 1495660802129109433341833

theorem tailTrace_2912789 : CollatzResearch.WordTrace tailWord_2912789 prefixEnd_2912789 1495660802129109433341833 := by
  unfold tailWord_2912789
  simp only [CollatzResearch.WordTrace]
  refine ⟨106238142644470392601117421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70825428429646928400744947 106238142644470392601117421)
  ·
    refine ⟨39839303491676397225419033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106238142644470392601117421 39839303491676397225419033)
    ·
      refine ⟨29879477618757297919064275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39839303491676397225419033 29879477618757297919064275)
      ·
        refine ⟨44819216428135946878596413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29879477618757297919064275 44819216428135946878596413)
        ·
          refine ⟨16807206160550980079473655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44819216428135946878596413 16807206160550980079473655)
          ·
            refine ⟨25210809240826470119210483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16807206160550980079473655 25210809240826470119210483)
            ·
              refine ⟨37816213861239705178815725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25210809240826470119210483 37816213861239705178815725)
              ·
                refine ⟨14181080197964889442055897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37816213861239705178815725 14181080197964889442055897)
                ·
                  refine ⟨10635810148473667081541923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14181080197964889442055897 10635810148473667081541923)
                  ·
                    refine ⟨15953715222710500622312885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10635810148473667081541923 15953715222710500622312885)
                    ·
                      refine ⟨1495660802129109433341833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15953715222710500622312885 1495660802129109433341833)
                      ·
                        rfl

theorem cell23_2912789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 3, 2, 1, 5].length) (baseStart_2912789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2912789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2912789 prefixEnd_2912789 := by exact prefixLift 2912789
  have htrace : WordTrace (prefixWord ++ tailWord_2912789) baseStart_2912789 baseEnd_2912789 := by
    simpa [prefixWord, tailWord_2912789, baseEnd_2912789] using wordTrace_append hprefix tailTrace_2912789
  have hstable : (prefixWord ++ tailWord_2912789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2912789).length < 2 ^ (prefixWord ++ tailWord_2912789).sum := by decide
  have hdescent : baseEnd_2912789 < baseStart_2912789 := by decide
  rcases family_descends (prefixWord ++ tailWord_2912789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2912799 : List Nat := [1, 1, 2, 4, 1, 1, 1, 4, 2, 2, 4]
def baseStart_2912799 : Nat := 118140960795 + 2912799 * 2 ^ 59
def prefixEnd_2912799 : Nat := 4983230072969 + 3 ^ 40 * 2912799 * 2
def baseEnd_2912799 : Nat := 1495665936935654394216787

theorem tailTrace_2912799 : CollatzResearch.WordTrace tailWord_2912799 prefixEnd_2912799 1495665936935654394216787 := by
  unfold tailWord_2912799
  simp only [CollatzResearch.WordTrace]
  refine ⟨106238507374434164308981451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70825671582956109539320967 106238507374434164308981451)
  ·
    refine ⟨159357761061651246463472177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106238507374434164308981451 159357761061651246463472177)
    ·
      refine ⟨119518320796238434847604133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159357761061651246463472177 119518320796238434847604133)
      ·
        refine ⟨22409685149294706533925775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 119518320796238434847604133 22409685149294706533925775)
        ·
          refine ⟨33614527723942059800888663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22409685149294706533925775 33614527723942059800888663)
          ·
            refine ⟨50421791585913089701332995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33614527723942059800888663 50421791585913089701332995)
            ·
              refine ⟨75632687378869634551999493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50421791585913089701332995 75632687378869634551999493)
              ·
                refine ⟨14181128883538056478499905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 75632687378869634551999493 14181128883538056478499905)
                ·
                  refine ⟨10635846662653542358874929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14181128883538056478499905 10635846662653542358874929)
                  ·
                    refine ⟨7976884996990156769156197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10635846662653542358874929 7976884996990156769156197)
                    ·
                      refine ⟨1495665936935654394216787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7976884996990156769156197 1495665936935654394216787)
                      ·
                        rfl

theorem cell23_2912799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 4, 2, 2, 4].length) (baseStart_2912799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2912799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2912799 prefixEnd_2912799 := by exact prefixLift 2912799
  have htrace : WordTrace (prefixWord ++ tailWord_2912799) baseStart_2912799 baseEnd_2912799 := by
    simpa [prefixWord, tailWord_2912799, baseEnd_2912799] using wordTrace_append hprefix tailTrace_2912799
  have hstable : (prefixWord ++ tailWord_2912799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2912799).length < 2 ^ (prefixWord ++ tailWord_2912799).sum := by decide
  have hdescent : baseEnd_2912799 < baseStart_2912799 := by decide
  rcases family_descends (prefixWord ++ tailWord_2912799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2912896 : List Nat := [2, 1, 1, 2, 1, 5, 2, 1, 1, 4, 3]
def baseStart_2912896 : Nat := 118140960795 + 2912896 * 2 ^ 59
def prefixEnd_2912896 : Nat := 4983230072969 + 3 ^ 40 * 2912896 * 2
def baseEnd_2912896 : Nat := 1495715744559140514703841

theorem tailTrace_2912896 : CollatzResearch.WordTrace tailWord_2912896 prefixEnd_2912896 1495715744559140514703841 := by
  unfold tailWord_2912896
  simp only [CollatzResearch.WordTrace]
  refine ⟨53121022627541374937631271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70828030170055166583508361 53121022627541374937631271)
  ·
    refine ⟨79681533941312062406446907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53121022627541374937631271 79681533941312062406446907)
    ·
      refine ⟨119522300911968093609670361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79681533941312062406446907 119522300911968093609670361)
      ·
        refine ⟨89641725683976070207252771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119522300911968093609670361 89641725683976070207252771)
        ·
          refine ⟨134462588525964105310879157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89641725683976070207252771 134462588525964105310879157)
          ·
            refine ⟨12605867674309134872894921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 134462588525964105310879157 12605867674309134872894921)
            ·
              refine ⟨9454400755731851154671191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12605867674309134872894921 9454400755731851154671191)
              ·
                refine ⟨14181601133597776732006787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9454400755731851154671191 14181601133597776732006787)
                ·
                  refine ⟨21272401700396665098010181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14181601133597776732006787 21272401700396665098010181)
                  ·
                    refine ⟨3988575318824374705876909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21272401700396665098010181 3988575318824374705876909)
                    ·
                      refine ⟨1495715744559140514703841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3988575318824374705876909 1495715744559140514703841)
                      ·
                        rfl

theorem cell23_2912896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 1, 1, 4, 3].length) (baseStart_2912896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2912896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2912896 prefixEnd_2912896 := by exact prefixLift 2912896
  have htrace : WordTrace (prefixWord ++ tailWord_2912896) baseStart_2912896 baseEnd_2912896 := by
    simpa [prefixWord, tailWord_2912896, baseEnd_2912896] using wordTrace_append hprefix tailTrace_2912896
  have hstable : (prefixWord ++ tailWord_2912896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2912896).length < 2 ^ (prefixWord ++ tailWord_2912896).sum := by decide
  have hdescent : baseEnd_2912896 < baseStart_2912896 := by decide
  rcases family_descends (prefixWord ++ tailWord_2912896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2912899 : List Nat := [1, 1, 1, 3, 3, 1, 3, 2, 8]
def baseStart_2912899 : Nat := 118140960795 + 2912899 * 2 ^ 59
def prefixEnd_2912899 : Nat := 4983230072969 + 3 ^ 40 * 2912899 * 2
def baseEnd_2912899 : Nat := 166190809444567111440703

theorem tailTrace_2912899 : CollatzResearch.WordTrace tailWord_2912899 prefixEnd_2912899 166190809444567111440703 := by
  unfold tailWord_2912899
  simp only [CollatzResearch.WordTrace]
  refine ⟨106242154674071881387621751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70828103116047920925081167 106242154674071881387621751)
  ·
    refine ⟨159363232011107822081432627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106242154674071881387621751 159363232011107822081432627)
    ·
      refine ⟨239044848016661733122148941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159363232011107822081432627 239044848016661733122148941)
      ·
        refine ⟨89641818006248149920805853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 239044848016661733122148941 89641818006248149920805853)
        ·
          refine ⟨33615681752343056220302195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89641818006248149920805853 33615681752343056220302195)
          ·
            refine ⟨50423522628514584330453293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33615681752343056220302195 50423522628514584330453293)
            ·
              refine ⟨18908820985692969123919985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50423522628514584330453293 18908820985692969123919985)
              ·
                refine ⟨14181615739269726842939989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18908820985692969123919985 14181615739269726842939989)
                ·
                  refine ⟨166190809444567111440703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14181615739269726842939989 166190809444567111440703)
                  ·
                    rfl

theorem cell23_2912899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 2, 8].length) (baseStart_2912899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2912899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2912899 prefixEnd_2912899 := by exact prefixLift 2912899
  have htrace : WordTrace (prefixWord ++ tailWord_2912899) baseStart_2912899 baseEnd_2912899 := by
    simpa [prefixWord, tailWord_2912899, baseEnd_2912899] using wordTrace_append hprefix tailTrace_2912899
  have hstable : (prefixWord ++ tailWord_2912899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2912899).length < 2 ^ (prefixWord ++ tailWord_2912899).sum := by decide
  have hdescent : baseEnd_2912899 < baseStart_2912899 := by decide
  rcases family_descends (prefixWord ++ tailWord_2912899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2912970 : List Nat := [3, 1, 2, 1, 4, 1, 2, 2, 2, 3, 2]
def baseStart_2912970 : Nat := 118140960795 + 2912970 * 2 ^ 59
def prefixEnd_2912970 : Nat := 4983230072969 + 3 ^ 40 * 2912970 * 2
def baseEnd_2912970 : Nat := 1495753742127573225178501

theorem tailTrace_2912970 : CollatzResearch.WordTrace tailWord_2912970 prefixEnd_2912970 1495753742127573225178501 := by
  unfold tailWord_2912970
  simp only [CollatzResearch.WordTrace]
  refine ⟨26561186064203665128364091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70829829504543107008970909 26561186064203665128364091)
  ·
    refine ⟨39841779096305497692546137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26561186064203665128364091 39841779096305497692546137)
    ·
      refine ⟨29881334322229123269409603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39841779096305497692546137 29881334322229123269409603)
      ·
        refine ⟨44822001483343684904114405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29881334322229123269409603 44822001483343684904114405)
        ·
          refine ⟨8404125278126940919521451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44822001483343684904114405 8404125278126940919521451)
          ·
            refine ⟨12606187917190411379282177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8404125278126940919521451 12606187917190411379282177)
            ·
              refine ⟨9454640937892808534461633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12606187917190411379282177 9454640937892808534461633)
              ·
                refine ⟨7090980703419606400846225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9454640937892808534461633 7090980703419606400846225)
                ·
                  refine ⟨5318235527564704800634669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7090980703419606400846225 5318235527564704800634669)
                  ·
                    refine ⟨1994338322836764300238001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5318235527564704800634669 1994338322836764300238001)
                    ·
                      refine ⟨1495753742127573225178501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1994338322836764300238001 1495753742127573225178501)
                      ·
                        rfl

theorem cell23_2912970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 2, 2, 3, 2].length) (baseStart_2912970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2912970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2912970 prefixEnd_2912970 := by exact prefixLift 2912970
  have htrace : WordTrace (prefixWord ++ tailWord_2912970) baseStart_2912970 baseEnd_2912970 := by
    simpa [prefixWord, tailWord_2912970, baseEnd_2912970] using wordTrace_append hprefix tailTrace_2912970
  have hstable : (prefixWord ++ tailWord_2912970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2912970).length < 2 ^ (prefixWord ++ tailWord_2912970).sum := by decide
  have hdescent : baseEnd_2912970 < baseStart_2912970 := by decide
  rcases family_descends (prefixWord ++ tailWord_2912970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2912976 : List Nat := [2, 1, 1, 1, 1, 2, 1, 2, 8, 4]
def baseStart_2912976 : Nat := 118140960795 + 2912976 * 2 ^ 59
def prefixEnd_2912976 : Nat := 4983230072969 + 3 ^ 40 * 2912976 * 2
def baseEnd_2912976 : Nat := 498585607670500067234491

theorem tailTrace_2912976 : CollatzResearch.WordTrace tailWord_2912976 prefixEnd_2912976 498585607670500067234491 := by
  unfold tailWord_2912976
  simp only [CollatzResearch.WordTrace]
  refine ⟨53122481547396461769087391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70829975396528615692116521 53122481547396461769087391)
  ·
    refine ⟨79683722321094692653631087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53122481547396461769087391 79683722321094692653631087)
    ·
      refine ⟨119525583481642038980446631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79683722321094692653631087 119525583481642038980446631)
      ·
        refine ⟨179288375222463058470669947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119525583481642038980446631 179288375222463058470669947)
        ·
          refine ⟨268932562833694587706004921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179288375222463058470669947 268932562833694587706004921)
          ·
            refine ⟨201699422125270940779503691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 268932562833694587706004921 201699422125270940779503691)
            ·
              refine ⟨302549133187906411169255537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 201699422125270940779503691 302549133187906411169255537)
              ·
                refine ⟨226911849890929808376941653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 302549133187906411169255537 226911849890929808376941653)
                ·
                  refine ⟨2659123240909333691917285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 226911849890929808376941653 2659123240909333691917285)
                  ·
                    refine ⟨498585607670500067234491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2659123240909333691917285 498585607670500067234491)
                    ·
                      rfl

theorem cell23_2912976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 8, 4].length) (baseStart_2912976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2912976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2912976 prefixEnd_2912976 := by exact prefixLift 2912976
  have htrace : WordTrace (prefixWord ++ tailWord_2912976) baseStart_2912976 baseEnd_2912976 := by
    simpa [prefixWord, tailWord_2912976, baseEnd_2912976] using wordTrace_append hprefix tailTrace_2912976
  have hstable : (prefixWord ++ tailWord_2912976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2912976).length < 2 ^ (prefixWord ++ tailWord_2912976).sum := by decide
  have hdescent : baseEnd_2912976 < baseStart_2912976 := by decide
  rcases family_descends (prefixWord ++ tailWord_2912976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2912986 : List Nat := [3, 1, 1, 2, 2, 2, 2, 1, 3, 1, 5]
def baseStart_2912986 : Nat := 118140960795 + 2912986 * 2 ^ 59
def prefixEnd_2912986 : Nat := 4983230072969 + 3 ^ 40 * 2912986 * 2
def baseEnd_2912986 : Nat := 1495761957818045162578427

theorem tailTrace_2912986 : CollatzResearch.WordTrace tailWord_2912986 prefixEnd_2912986 1495761957818045162578427 := by
  unfold tailWord_2912986
  simp only [CollatzResearch.WordTrace]
  refine ⟨26561331956189173811509703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70830218549837796830692541 26561331956189173811509703)
  ·
    refine ⟨39841997934283760717264555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26561331956189173811509703 39841997934283760717264555)
    ·
      refine ⟨59762996901425641075896833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39841997934283760717264555 59762996901425641075896833)
      ·
        refine ⟨44822247676069230806922625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59762996901425641075896833 44822247676069230806922625)
        ·
          refine ⟨33616685757051923105191969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44822247676069230806922625 33616685757051923105191969)
          ·
            refine ⟨25212514317788942328893977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33616685757051923105191969 25212514317788942328893977)
            ·
              refine ⟨18909385738341706746670483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25212514317788942328893977 18909385738341706746670483)
              ·
                refine ⟨28364078607512560120005725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18909385738341706746670483 28364078607512560120005725)
                ·
                  refine ⟨10636529477817210045002147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28364078607512560120005725 10636529477817210045002147)
                  ·
                    refine ⟨15954794216725815067503221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10636529477817210045002147 15954794216725815067503221)
                    ·
                      refine ⟨1495761957818045162578427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15954794216725815067503221 1495761957818045162578427)
                      ·
                        rfl

theorem cell23_2912986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 1, 3, 1, 5].length) (baseStart_2912986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2912986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2912986 prefixEnd_2912986 := by exact prefixLift 2912986
  have htrace : WordTrace (prefixWord ++ tailWord_2912986) baseStart_2912986 baseEnd_2912986 := by
    simpa [prefixWord, tailWord_2912986, baseEnd_2912986] using wordTrace_append hprefix tailTrace_2912986
  have hstable : (prefixWord ++ tailWord_2912986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2912986).length < 2 ^ (prefixWord ++ tailWord_2912986).sum := by decide
  have hdescent : baseEnd_2912986 < baseStart_2912986 := by decide
  rcases family_descends (prefixWord ++ tailWord_2912986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2912993 : List Nat := [1, 2, 3, 1, 4, 2, 2, 1, 1, 6]
def baseStart_2912993 : Nat := 118140960795 + 2912993 * 2 ^ 59
def prefixEnd_2912993 : Nat := 4983230072969 + 3 ^ 40 * 2912993 * 2
def baseEnd_2912993 : Nat := 498588517394208878396965

theorem tailTrace_2912993 : CollatzResearch.WordTrace tailWord_2912993 prefixEnd_2912993 498588517394208878396965 := by
  unfold tailWord_2912993
  simp only [CollatzResearch.WordTrace]
  refine ⟨106245583135731335441543633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70830388757154223627695755 106245583135731335441543633)
  ·
    refine ⟨79684187351798501581157725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106245583135731335441543633 79684187351798501581157725)
    ·
      refine ⟨29881570256924438092934147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79684187351798501581157725 29881570256924438092934147)
      ·
        refine ⟨44822355385386657139401221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29881570256924438092934147 44822355385386657139401221)
        ·
          refine ⟨8404191634759998213637729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44822355385386657139401221 8404191634759998213637729)
          ·
            refine ⟨6303143726069998660228297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8404191634759998213637729 6303143726069998660228297)
            ·
              refine ⟨4727357794552498995171223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6303143726069998660228297 4727357794552498995171223)
              ·
                refine ⟨7091036691828748492756835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4727357794552498995171223 7091036691828748492756835)
                ·
                  refine ⟨10636555037743122739135253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7091036691828748492756835 10636555037743122739135253)
                  ·
                    refine ⟨498588517394208878396965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10636555037743122739135253 498588517394208878396965)
                    ·
                      rfl

theorem cell23_2912993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 2, 1, 1, 6].length) (baseStart_2912993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2912993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2912993 prefixEnd_2912993 := by exact prefixLift 2912993
  have htrace : WordTrace (prefixWord ++ tailWord_2912993) baseStart_2912993 baseEnd_2912993 := by
    simpa [prefixWord, tailWord_2912993, baseEnd_2912993] using wordTrace_append hprefix tailTrace_2912993
  have hstable : (prefixWord ++ tailWord_2912993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2912993).length < 2 ^ (prefixWord ++ tailWord_2912993).sum := by decide
  have hdescent : baseEnd_2912993 < baseStart_2912993 := by decide
  rcases family_descends (prefixWord ++ tailWord_2912993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2913003 : List Nat := [1, 1, 1, 1, 2, 4, 1, 6, 1, 2, 3]
def baseStart_2913003 : Nat := 118140960795 + 2913003 * 2 ^ 59
def prefixEnd_2913003 : Nat := 4983230072969 + 3 ^ 40 * 2913003 * 2
def baseEnd_2913003 : Nat := 1495770686989171596065849

theorem tailTrace_2913003 : CollatzResearch.WordTrace tailWord_2913003 prefixEnd_2913003 1495770686989171596065849 := by
  unfold tailWord_2913003
  simp only [CollatzResearch.WordTrace]
  refine ⟨106245947865695107149407663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70830631910463404766271775 106245947865695107149407663)
  ·
    refine ⟨159368921798542660724111495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106245947865695107149407663 159368921798542660724111495)
    ·
      refine ⟨239053382697813991086167243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159368921798542660724111495 239053382697813991086167243)
      ·
        refine ⟨358580074046720986629250865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239053382697813991086167243 358580074046720986629250865)
        ·
          refine ⟨268935055535040739971938149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 358580074046720986629250865 268935055535040739971938149)
          ·
            refine ⟨50425322912820138744738403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 268935055535040739971938149 50425322912820138744738403)
            ·
              refine ⟨75637984369230208117107605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50425322912820138744738403 75637984369230208117107605)
              ·
                refine ⟨3545530517307666005489419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 75637984369230208117107605 3545530517307666005489419)
                ·
                  refine ⟨5318295775961499008234129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3545530517307666005489419 5318295775961499008234129)
                  ·
                    refine ⟨3988721831971124256175597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5318295775961499008234129 3988721831971124256175597)
                    ·
                      refine ⟨1495770686989171596065849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3988721831971124256175597 1495770686989171596065849)
                      ·
                        rfl

theorem cell23_2913003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 6, 1, 2, 3].length) (baseStart_2913003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2913003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2913003 prefixEnd_2913003 := by exact prefixLift 2913003
  have htrace : WordTrace (prefixWord ++ tailWord_2913003) baseStart_2913003 baseEnd_2913003 := by
    simpa [prefixWord, tailWord_2913003, baseEnd_2913003] using wordTrace_append hprefix tailTrace_2913003
  have hstable : (prefixWord ++ tailWord_2913003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2913003).length < 2 ^ (prefixWord ++ tailWord_2913003).sum := by decide
  have hdescent : baseEnd_2913003 < baseStart_2913003 := by decide
  rcases family_descends (prefixWord ++ tailWord_2913003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2913020 : List Nat := [2, 2, 2, 1, 3, 3, 1, 3, 1, 2, 3]
def baseStart_2913020 : Nat := 118140960795 + 2913020 * 2 ^ 59
def prefixEnd_2913020 : Nat := 4983230072969 + 3 ^ 40 * 2913020 * 2
def baseEnd_2913020 : Nat := 1495779416160298029553271

theorem tailTrace_2913020 : CollatzResearch.WordTrace tailWord_2913020 prefixEnd_2913020 1495779416160298029553271 := by
  unfold tailWord_2913020
  simp only [CollatzResearch.WordTrace]
  refine ⟨53123283953316759526388257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70831045271089012701851009 53123283953316759526388257)
  ·
    refine ⟨39842462964987569644791193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53123283953316759526388257 39842462964987569644791193)
    ·
      refine ⟨29881847223740677233593395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39842462964987569644791193 29881847223740677233593395)
      ·
        refine ⟨44822770835611015850390093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29881847223740677233593395 44822770835611015850390093)
        ·
          refine ⟨16808539063354130943896285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44822770835611015850390093 16808539063354130943896285)
          ·
            refine ⟨6303202148757799103961107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16808539063354130943896285 6303202148757799103961107)
            ·
              refine ⟨9454803223136698655941661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6303202148757799103961107 9454803223136698655941661)
              ·
                refine ⟨3545551208676261995978123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9454803223136698655941661 3545551208676261995978123)
                ·
                  refine ⟨5318326813014392993967185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3545551208676261995978123 5318326813014392993967185)
                  ·
                    refine ⟨3988745109760794745475389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5318326813014392993967185 3988745109760794745475389)
                    ·
                      refine ⟨1495779416160298029553271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3988745109760794745475389 1495779416160298029553271)
                      ·
                        rfl

theorem cell23_2913020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 3, 1, 2, 3].length) (baseStart_2913020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2913020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2913020 prefixEnd_2913020 := by exact prefixLift 2913020
  have htrace : WordTrace (prefixWord ++ tailWord_2913020) baseStart_2913020 baseEnd_2913020 := by
    simpa [prefixWord, tailWord_2913020, baseEnd_2913020] using wordTrace_append hprefix tailTrace_2913020
  have hstable : (prefixWord ++ tailWord_2913020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2913020).length < 2 ^ (prefixWord ++ tailWord_2913020).sum := by decide
  have hdescent : baseEnd_2913020 < baseStart_2913020 := by decide
  rcases family_descends (prefixWord ++ tailWord_2913020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2913047 : List Nat := [1, 1, 3, 4, 4, 1, 1, 1, 1, 2, 4]
def baseStart_2913047 : Nat := 118140960795 + 2913047 * 2 ^ 59
def prefixEnd_2913047 : Nat := 4983230072969 + 3 ^ 40 * 2913047 * 2
def baseEnd_2913047 : Nat := 1495793280137969423915647

theorem tailTrace_2913047 : CollatzResearch.WordTrace tailWord_2913047 prefixEnd_2913047 1495793280137969423915647 := by
  unfold tailWord_2913047
  simp only [CollatzResearch.WordTrace]
  refine ⟨106247552677535702664009395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70831701785023801776006263 106247552677535702664009395)
  ·
    refine ⟨159371329016303553996014093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106247552677535702664009395 159371329016303553996014093)
    ·
      refine ⟨59764248381113832748505285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 159371329016303553996014093 59764248381113832748505285)
      ·
        refine ⟨11205796571458843640344741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59764248381113832748505285 11205796571458843640344741)
        ·
          refine ⟨2101086857148533182564639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11205796571458843640344741 2101086857148533182564639)
          ·
            refine ⟨3151630285722799773846959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2101086857148533182564639 3151630285722799773846959)
            ·
              refine ⟨4727445428584199660770439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3151630285722799773846959 4727445428584199660770439)
              ·
                refine ⟨7091168142876299491155659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4727445428584199660770439 7091168142876299491155659)
                ·
                  refine ⟨10636752214314449236733489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7091168142876299491155659 10636752214314449236733489)
                  ·
                    refine ⟨7977564160735836927550117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10636752214314449236733489 7977564160735836927550117)
                    ·
                      refine ⟨1495793280137969423915647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7977564160735836927550117 1495793280137969423915647)
                      ·
                        rfl

theorem cell23_2913047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 1, 1, 1, 2, 4].length) (baseStart_2913047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2913047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2913047 prefixEnd_2913047 := by exact prefixLift 2913047
  have htrace : WordTrace (prefixWord ++ tailWord_2913047) baseStart_2913047 baseEnd_2913047 := by
    simpa [prefixWord, tailWord_2913047, baseEnd_2913047] using wordTrace_append hprefix tailTrace_2913047
  have hstable : (prefixWord ++ tailWord_2913047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2913047).length < 2 ^ (prefixWord ++ tailWord_2913047).sum := by decide
  have hdescent : baseEnd_2913047 < baseStart_2913047 := by decide
  rcases family_descends (prefixWord ++ tailWord_2913047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2913077 : List Nat := [1, 3, 3, 1, 3, 1, 2, 3, 1, 3, 2]
def baseStart_2913077 : Nat := 118140960795 + 2913077 * 2 ^ 59
def prefixEnd_2913077 : Nat := 4983230072969 + 3 ^ 40 * 2913077 * 2
def baseEnd_2913077 : Nat := 1495808684557604306540509

theorem tailTrace_2913077 : CollatzResearch.WordTrace tailWord_2913077 prefixEnd_2913077 1495808684557604306540509 := by
  unfold tailWord_2913077
  simp only [CollatzResearch.WordTrace]
  refine ⟨106248646867427017787601485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70832431244951345191734323 106248646867427017787601485)
  ·
    refine ⟨39843242575285131670350557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106248646867427017787601485 39843242575285131670350557)
    ·
      refine ⟨14941215965731924376381459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39843242575285131670350557 14941215965731924376381459)
      ·
        refine ⟨22411823948597886564572189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14941215965731924376381459 22411823948597886564572189)
        ·
          refine ⟨8404433980724207461714571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22411823948597886564572189 8404433980724207461714571)
          ·
            refine ⟨12606650971086311192571857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8404433980724207461714571 12606650971086311192571857)
            ·
              refine ⟨9454988228314733394428893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12606650971086311192571857 9454988228314733394428893)
              ·
                refine ⟨3545620585618025022910835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9454988228314733394428893 3545620585618025022910835)
                ·
                  refine ⟨5318430878427037534366253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3545620585618025022910835 5318430878427037534366253)
                  ·
                    refine ⟨1994411579410139075387345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5318430878427037534366253 1994411579410139075387345)
                    ·
                      refine ⟨1495808684557604306540509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1994411579410139075387345 1495808684557604306540509)
                      ·
                        rfl

theorem cell23_2913077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 3, 1, 3, 2].length) (baseStart_2913077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2913077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2913077 prefixEnd_2913077 := by exact prefixLift 2913077
  have htrace : WordTrace (prefixWord ++ tailWord_2913077) baseStart_2913077 baseEnd_2913077 := by
    simpa [prefixWord, tailWord_2913077, baseEnd_2913077] using wordTrace_append hprefix tailTrace_2913077
  have hstable : (prefixWord ++ tailWord_2913077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2913077).length < 2 ^ (prefixWord ++ tailWord_2913077).sum := by decide
  have hdescent : baseEnd_2913077 < baseStart_2913077 := by decide
  rcases family_descends (prefixWord ++ tailWord_2913077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2913154 : List Nat := [3, 4, 2, 2, 1, 1, 1, 1, 2, 2, 4]
def baseStart_2913154 : Nat := 118140960795 + 2913154 * 2 ^ 59
def prefixEnd_2913154 : Nat := 4983230072969 + 3 ^ 40 * 2913154 * 2
def baseEnd_2913154 : Nat := 1495848222568000505277655

theorem tailTrace_2913154 : CollatzResearch.WordTrace tailWord_2913154 prefixEnd_2913154 1495848222568000505277655 := by
  unfold tailWord_2913154
  simp only [CollatzResearch.WordTrace]
  refine ⟨26562863822037014984538629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70834303525432039958769677 26562863822037014984538629)
  ·
    refine ⟨4980536966631940309600993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26562863822037014984538629 4980536966631940309600993)
    ·
      refine ⟨3735402724973955232200745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4980536966631940309600993 3735402724973955232200745)
      ·
        refine ⟨2801552043730466424150559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3735402724973955232200745 2801552043730466424150559)
        ·
          refine ⟨4202328065595699636225839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2801552043730466424150559 4202328065595699636225839)
          ·
            refine ⟨6303492098393549454338759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4202328065595699636225839 6303492098393549454338759)
            ·
              refine ⟨9455238147590324181508139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6303492098393549454338759 9455238147590324181508139)
              ·
                refine ⟨14182857221385486272262209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9455238147590324181508139 14182857221385486272262209)
                ·
                  refine ⟨10637142916039114704196657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14182857221385486272262209 10637142916039114704196657)
                  ·
                    refine ⟨7977857187029336028147493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10637142916039114704196657 7977857187029336028147493)
                    ·
                      refine ⟨1495848222568000505277655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7977857187029336028147493 1495848222568000505277655)
                      ·
                        rfl

theorem cell23_2913154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_2913154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2913154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2913154 prefixEnd_2913154 := by exact prefixLift 2913154
  have htrace : WordTrace (prefixWord ++ tailWord_2913154) baseStart_2913154 baseEnd_2913154 := by
    simpa [prefixWord, tailWord_2913154, baseEnd_2913154] using wordTrace_append hprefix tailTrace_2913154
  have hstable : (prefixWord ++ tailWord_2913154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2913154).length < 2 ^ (prefixWord ++ tailWord_2913154).sum := by decide
  have hdescent : baseEnd_2913154 < baseStart_2913154 := by decide
  rcases family_descends (prefixWord ++ tailWord_2913154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2913163 : List Nat := [1, 1, 1, 1, 4, 2, 2, 2, 4, 1, 4]
def baseStart_2913163 : Nat := 118140960795 + 2913163 * 2 ^ 59
def prefixEnd_2913163 : Nat := 4983230072969 + 3 ^ 40 * 2913163 * 2
def baseEnd_2913163 : Nat := 1495852843893890970065113

theorem tailTrace_2913163 : CollatzResearch.WordTrace tailWord_2913163 prefixEnd_2913163 1495852843893890970065113 := by
  unfold tailWord_2913163
  simp only [CollatzResearch.WordTrace]
  refine ⟨106251783545115454475232143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70834522363410302983488095 106251783545115454475232143)
  ·
    refine ⟨159377675317673181712848215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106251783545115454475232143 159377675317673181712848215)
    ·
      refine ⟨239066512976509772569272323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159377675317673181712848215 239066512976509772569272323)
      ·
        refine ⟨358599769464764658853908485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239066512976509772569272323 358599769464764658853908485)
        ·
          refine ⟨67237456774643373535107841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 358599769464764658853908485 67237456774643373535107841)
          ·
            refine ⟨50428092580982530151330881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67237456774643373535107841 50428092580982530151330881)
            ·
              refine ⟨37821069435736897613498161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50428092580982530151330881 37821069435736897613498161)
              ·
                refine ⟨28365802076802673210123621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37821069435736897613498161 28365802076802673210123621)
                ·
                  refine ⟨5318587889400501226898179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28365802076802673210123621 5318587889400501226898179)
                  ·
                    refine ⟨7977881834100751840347269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5318587889400501226898179 7977881834100751840347269)
                    ·
                      refine ⟨1495852843893890970065113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7977881834100751840347269 1495852843893890970065113)
                      ·
                        rfl

theorem cell23_2913163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 2, 4, 1, 4].length) (baseStart_2913163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2913163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2913163 prefixEnd_2913163 := by exact prefixLift 2913163
  have htrace : WordTrace (prefixWord ++ tailWord_2913163) baseStart_2913163 baseEnd_2913163 := by
    simpa [prefixWord, tailWord_2913163, baseEnd_2913163] using wordTrace_append hprefix tailTrace_2913163
  have hstable : (prefixWord ++ tailWord_2913163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2913163).length < 2 ^ (prefixWord ++ tailWord_2913163).sum := by decide
  have hdescent : baseEnd_2913163 < baseStart_2913163 := by decide
  rcases family_descends (prefixWord ++ tailWord_2913163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2913203 : List Nat := [1, 1, 1, 2, 3, 1, 2, 6, 6]
def baseStart_2913203 : Nat := 118140960795 + 2913203 * 2 ^ 59
def prefixEnd_2913203 : Nat := 4983230072969 + 3 ^ 40 * 2913203 * 2
def baseEnd_2913203 : Nat := 166208153680007868173881

theorem tailTrace_2913203 : CollatzResearch.WordTrace tailWord_2913203 prefixEnd_2913203 166208153680007868173881 := by
  unfold tailWord_2913203
  simp only [CollatzResearch.WordTrace]
  refine ⟨106253242464970541306688263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70835494976647027537792175 106253242464970541306688263)
  ·
    refine ⟨159379863697455811960032395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106253242464970541306688263 159379863697455811960032395)
    ·
      refine ⟨239069795546183717940048593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159379863697455811960032395 239069795546183717940048593)
      ·
        refine ⟨179302346659637788455036445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 239069795546183717940048593 179302346659637788455036445)
        ·
          refine ⟨67238379997364170670638667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 179302346659637788455036445 67238379997364170670638667)
          ·
            refine ⟨100857569996046256005958001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67238379997364170670638667 100857569996046256005958001)
            ·
              refine ⟨75643177497034692004468501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100857569996046256005958001 75643177497034692004468501)
              ·
                refine ⟨3545773945173501187709461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 75643177497034692004468501 3545773945173501187709461)
                ·
                  refine ⟨166208153680007868173881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3545773945173501187709461 166208153680007868173881)
                  ·
                    rfl

theorem cell23_2913203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 6, 6].length) (baseStart_2913203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2913203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2913203 prefixEnd_2913203 := by exact prefixLift 2913203
  have htrace : WordTrace (prefixWord ++ tailWord_2913203) baseStart_2913203 baseEnd_2913203 := by
    simpa [prefixWord, tailWord_2913203, baseEnd_2913203] using wordTrace_append hprefix tailTrace_2913203
  have hstable : (prefixWord ++ tailWord_2913203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2913203).length < 2 ^ (prefixWord ++ tailWord_2913203).sum := by decide
  have hdescent : baseEnd_2913203 < baseStart_2913203 := by decide
  rcases family_descends (prefixWord ++ tailWord_2913203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2913207 : List Nat := [1, 1, 3, 1, 3, 1, 4, 4, 1, 4]
def baseStart_2913207 : Nat := 118140960795 + 2913207 * 2 ^ 59
def prefixEnd_2913207 : Nat := 4983230072969 + 3 ^ 40 * 2913207 * 2
def baseEnd_2913207 : Nat := 498625145680896265971637

theorem tailTrace_2913207 : CollatzResearch.WordTrace tailWord_2913207 prefixEnd_2913207 498625145680896265971637 := by
  unfold tailWord_2913207
  simp only [CollatzResearch.WordTrace]
  refine ⟨106253388356956049989833875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70835592237970699993222583 106253388356956049989833875)
  ·
    refine ⟨159380082535434074984750813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106253388356956049989833875 159380082535434074984750813)
    ·
      refine ⟨59767530950787778119281555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 159380082535434074984750813 59767530950787778119281555)
      ·
        refine ⟨89651296426181667178922333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59767530950787778119281555 89651296426181667178922333)
        ·
          refine ⟨33619236159818125192095875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89651296426181667178922333 33619236159818125192095875)
          ·
            refine ⟨50428854239727187788143813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33619236159818125192095875 50428854239727187788143813)
            ·
              refine ⟨9455410169948847710276965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50428854239727187788143813 9455410169948847710276965)
              ·
                refine ⟨1772889406865408945676931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9455410169948847710276965 1772889406865408945676931)
                ·
                  refine ⟨2659334110298113418515397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1772889406865408945676931 2659334110298113418515397)
                  ·
                    refine ⟨498625145680896265971637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2659334110298113418515397 498625145680896265971637)
                    ·
                      rfl

theorem cell23_2913207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 4, 1, 4].length) (baseStart_2913207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2913207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2913207 prefixEnd_2913207 := by exact prefixLift 2913207
  have htrace : WordTrace (prefixWord ++ tailWord_2913207) baseStart_2913207 baseEnd_2913207 := by
    simpa [prefixWord, tailWord_2913207, baseEnd_2913207] using wordTrace_append hprefix tailTrace_2913207
  have hstable : (prefixWord ++ tailWord_2913207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2913207).length < 2 ^ (prefixWord ++ tailWord_2913207).sum := by decide
  have hdescent : baseEnd_2913207 < baseStart_2913207 := by decide
  rcases family_descends (prefixWord ++ tailWord_2913207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2913304 : List Nat := [2, 1, 2, 3, 2, 3, 3, 1, 1, 1, 4]
def baseStart_2913304 : Nat := 118140960795 + 2913304 * 2 ^ 59
def prefixEnd_2913304 : Nat := 4983230072969 + 3 ^ 40 * 2913304 * 2
def baseEnd_2913304 : Nat := 1495925244666174918401965

theorem tailTrace_2913304 : CollatzResearch.WordTrace tailWord_2913304 prefixEnd_2913304 1495925244666174918401965 := by
  unfold tailWord_2913304
  simp only [CollatzResearch.WordTrace]
  refine ⟨53128463118802317778057483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70837950825069757037409977 53128463118802317778057483)
  ·
    refine ⟨79692694678203476667086225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53128463118802317778057483 79692694678203476667086225)
    ·
      refine ⟨59769521008652607500314669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79692694678203476667086225 59769521008652607500314669)
      ·
        refine ⟨22413570378244727812618001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59769521008652607500314669 22413570378244727812618001)
        ·
          refine ⟨16810177783683545859463501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22413570378244727812618001 16810177783683545859463501)
          ·
            refine ⟨6303816668881329697298813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16810177783683545859463501 6303816668881329697298813)
            ·
              refine ⟨2363931250830498636487055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6303816668881329697298813 2363931250830498636487055)
              ·
                refine ⟨3545896876245747954730583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2363931250830498636487055 3545896876245747954730583)
                ·
                  refine ⟨5318845314368621932095875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3545896876245747954730583 5318845314368621932095875)
                  ·
                    refine ⟨7978267971552932898143813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5318845314368621932095875 7978267971552932898143813)
                    ·
                      refine ⟨1495925244666174918401965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7978267971552932898143813 1495925244666174918401965)
                      ·
                        rfl

theorem cell23_2913304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 3, 1, 1, 1, 4].length) (baseStart_2913304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2913304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2913304 prefixEnd_2913304 := by exact prefixLift 2913304
  have htrace : WordTrace (prefixWord ++ tailWord_2913304) baseStart_2913304 baseEnd_2913304 := by
    simpa [prefixWord, tailWord_2913304, baseEnd_2913304] using wordTrace_append hprefix tailTrace_2913304
  have hstable : (prefixWord ++ tailWord_2913304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2913304).length < 2 ^ (prefixWord ++ tailWord_2913304).sum := by decide
  have hdescent : baseEnd_2913304 < baseStart_2913304 := by decide
  rcases family_descends (prefixWord ++ tailWord_2913304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2913314 : List Nat := [3, 3, 1, 1, 1, 4, 2, 2, 2, 4]
def baseStart_2913314 : Nat := 118140960795 + 2913314 * 2 ^ 59
def prefixEnd_2913314 : Nat := 4983230072969 + 3 ^ 40 * 2913314 * 2
def baseEnd_2913314 : Nat := 498643459824239959758973

theorem tailTrace_2913314 : CollatzResearch.WordTrace tailWord_2913314 prefixEnd_2913314 498643459824239959758973 := by
  unfold tailWord_2913314
  simp only [CollatzResearch.WordTrace]
  refine ⟨26564322741892101815994749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70838193978378938175985997 26564322741892101815994749)
  ·
    refine ⟨9961621028209538180998031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26564322741892101815994749 9961621028209538180998031)
    ·
      refine ⟨14942431542314307271497047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9961621028209538180998031 14942431542314307271497047)
      ·
        refine ⟨22413647313471460907245571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14942431542314307271497047 22413647313471460907245571)
        ·
          refine ⟨33620470970207191360868357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22413647313471460907245571 33620470970207191360868357)
          ·
            refine ⟨6303838306913848380162817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33620470970207191360868357 6303838306913848380162817)
            ·
              refine ⟨4727878730185386285122113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6303838306913848380162817 4727878730185386285122113)
              ·
                refine ⟨3545909047639039713841585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4727878730185386285122113 3545909047639039713841585)
                ·
                  refine ⟨2659431785729279785381189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3545909047639039713841585 2659431785729279785381189)
                  ·
                    refine ⟨498643459824239959758973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2659431785729279785381189 498643459824239959758973)
                    ·
                      rfl

theorem cell23_2913314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 2, 2, 2, 4].length) (baseStart_2913314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2913314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2913314 prefixEnd_2913314 := by exact prefixLift 2913314
  have htrace : WordTrace (prefixWord ++ tailWord_2913314) baseStart_2913314 baseEnd_2913314 := by
    simpa [prefixWord, tailWord_2913314, baseEnd_2913314] using wordTrace_append hprefix tailTrace_2913314
  have hstable : (prefixWord ++ tailWord_2913314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2913314).length < 2 ^ (prefixWord ++ tailWord_2913314).sum := by decide
  have hdescent : baseEnd_2913314 < baseStart_2913314 := by decide
  rcases family_descends (prefixWord ++ tailWord_2913314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2913323 : List Nat := [1, 1, 1, 1, 2, 1, 5, 1, 1, 9]
def baseStart_2913323 : Nat := 118140960795 + 2913323 * 2 ^ 59
def prefixEnd_2913323 : Nat := 4983230072969 + 3 ^ 40 * 2913323 * 2
def baseEnd_2913323 : Nat := 498645000266203448021459

theorem tailTrace_2913323 : CollatzResearch.WordTrace tailWord_2913323 prefixEnd_2913323 498645000266203448021459 := by
  unfold tailWord_2913323
  simp only [CollatzResearch.WordTrace]
  refine ⟨106257619224535801801056623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70838412816357201200704415 106257619224535801801056623)
  ·
    refine ⟨159386428836803702701584935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106257619224535801801056623 159386428836803702701584935)
    ·
      refine ⟨239079643255205554052377403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159386428836803702701584935 239079643255205554052377403)
      ·
        refine ⟨358619464882808331078566105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239079643255205554052377403 358619464882808331078566105)
        ·
          refine ⟨268964598662106248308924579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 358619464882808331078566105 268964598662106248308924579)
          ·
            refine ⟨403446897993159372463386869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 268964598662106248308924579 403446897993159372463386869)
            ·
              refine ⟨37823146686858691168442519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 403446897993159372463386869 37823146686858691168442519)
              ·
                refine ⟨56734720030288036752663779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37823146686858691168442519 56734720030288036752663779)
                ·
                  refine ⟨85102080045432055128995669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56734720030288036752663779 85102080045432055128995669)
                  ·
                    refine ⟨498645000266203448021459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 85102080045432055128995669 498645000266203448021459)
                    ·
                      rfl

theorem cell23_2913323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 1, 1, 9].length) (baseStart_2913323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2913323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2913323 prefixEnd_2913323 := by exact prefixLift 2913323
  have htrace : WordTrace (prefixWord ++ tailWord_2913323) baseStart_2913323 baseEnd_2913323 := by
    simpa [prefixWord, tailWord_2913323, baseEnd_2913323] using wordTrace_append hprefix tailTrace_2913323
  have hstable : (prefixWord ++ tailWord_2913323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2913323).length < 2 ^ (prefixWord ++ tailWord_2913323).sum := by decide
  have hdescent : baseEnd_2913323 < baseStart_2913323 := by decide
  rcases family_descends (prefixWord ++ tailWord_2913323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2913334 : List Nat := [5, 1, 2, 1, 1, 3, 2, 1, 1, 2, 4]
def baseStart_2913334 : Nat := 118140960795 + 2913334 * 2 ^ 59
def prefixEnd_2913334 : Nat := 4983230072969 + 3 ^ 40 * 2913334 * 2
def baseEnd_2913334 : Nat := 1495940649085809801026827

theorem tailTrace_2913334 : CollatzResearch.WordTrace tailWord_2913334 prefixEnd_2913334 1495940649085809801026827 := by
  unfold tailWord_2913334
  simp only [CollatzResearch.WordTrace]
  refine ⟨6641126276718496917481691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 70838680284997300453138037 6641126276718496917481691)
  ·
    refine ⟨9961689415077745376222537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6641126276718496917481691 9961689415077745376222537)
    ·
      refine ⟨7471267061308309032166903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9961689415077745376222537 7471267061308309032166903)
      ·
        refine ⟨11206900591962463548250355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7471267061308309032166903 11206900591962463548250355)
        ·
          refine ⟨16810350887943695322375533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11206900591962463548250355 16810350887943695322375533)
          ·
            refine ⟨6303881582978885745890825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16810350887943695322375533 6303881582978885745890825)
            ·
              refine ⟨4727911187234164309418119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6303881582978885745890825 4727911187234164309418119)
              ·
                refine ⟨7091866780851246464127179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4727911187234164309418119 7091866780851246464127179)
                ·
                  refine ⟨10637800171276869696190769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7091866780851246464127179 10637800171276869696190769)
                  ·
                    refine ⟨7978350128457652272143077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10637800171276869696190769 7978350128457652272143077)
                    ·
                      refine ⟨1495940649085809801026827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7978350128457652272143077 1495940649085809801026827)
                      ·
                        rfl

theorem cell23_2913334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 2, 1, 1, 2, 4].length) (baseStart_2913334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2913334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2913334 prefixEnd_2913334 := by exact prefixLift 2913334
  have htrace : WordTrace (prefixWord ++ tailWord_2913334) baseStart_2913334 baseEnd_2913334 := by
    simpa [prefixWord, tailWord_2913334, baseEnd_2913334] using wordTrace_append hprefix tailTrace_2913334
  have hstable : (prefixWord ++ tailWord_2913334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2913334).length < 2 ^ (prefixWord ++ tailWord_2913334).sum := by decide
  have hdescent : baseEnd_2913334 < baseStart_2913334 := by decide
  rcases family_descends (prefixWord ++ tailWord_2913334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2913337 : List Nat := [1, 2, 1, 5, 2, 1, 1, 3, 1, 3, 3]
def baseStart_2913337 : Nat := 118140960795 + 2913337 * 2 ^ 59
def prefixEnd_2913337 : Nat := 4983230072969 + 3 ^ 40 * 2913337 * 2
def baseEnd_2913337 : Nat := 1495942189527773289289313

theorem tailTrace_2913337 : CollatzResearch.WordTrace tailWord_2913337 prefixEnd_2913337 1495942189527773289289313 := by
  unfold tailWord_2913337
  simp only [CollatzResearch.WordTrace]
  refine ⟨106258129846485082192066265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70838753230990054794710843 106258129846485082192066265)
  ·
    refine ⟨79693597384863811644049699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106258129846485082192066265 79693597384863811644049699)
    ·
      refine ⟨119540396077295717466074549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79693597384863811644049699 119540396077295717466074549)
      ·
        refine ⟨11206912132246473512444489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 119540396077295717466074549 11206912132246473512444489)
        ·
          refine ⟨8405184099184855134333367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11206912132246473512444489 8405184099184855134333367)
          ·
            refine ⟨12607776148777282701500051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8405184099184855134333367 12607776148777282701500051)
            ·
              refine ⟨18911664223165924052250077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12607776148777282701500051 18911664223165924052250077)
              ·
                refine ⟨7091874083687221519593779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18911664223165924052250077 7091874083687221519593779)
                ·
                  refine ⟨10637811125530832279390669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7091874083687221519593779 10637811125530832279390669)
                  ·
                    refine ⟨3989179172074062104771501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10637811125530832279390669 3989179172074062104771501)
                    ·
                      refine ⟨1495942189527773289289313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3989179172074062104771501 1495942189527773289289313)
                      ·
                        rfl

theorem cell23_2913337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 3, 1, 3, 3].length) (baseStart_2913337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2913337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2913337 prefixEnd_2913337 := by exact prefixLift 2913337
  have htrace : WordTrace (prefixWord ++ tailWord_2913337) baseStart_2913337 baseEnd_2913337 := by
    simpa [prefixWord, tailWord_2913337, baseEnd_2913337] using wordTrace_append hprefix tailTrace_2913337
  have hstable : (prefixWord ++ tailWord_2913337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2913337).length < 2 ^ (prefixWord ++ tailWord_2913337).sum := by decide
  have hdescent : baseEnd_2913337 < baseStart_2913337 := by decide
  rcases family_descends (prefixWord ++ tailWord_2913337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2913347 : List Nat := [1, 1, 1, 3, 1, 2, 3, 3, 3, 3, 2]
def baseStart_2913347 : Nat := 118140960795 + 2913347 * 2 ^ 59
def prefixEnd_2913347 : Nat := 4983230072969 + 3 ^ 40 * 2913347 * 2
def baseEnd_2913347 : Nat := 1495947324334318250164267

theorem tailTrace_2913347 : CollatzResearch.WordTrace tailWord_2913347 prefixEnd_2913347 1495947324334318250164267 := by
  unfold tailWord_2913347
  simp only [CollatzResearch.WordTrace]
  refine ⟨106258494576448853899930295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70838996384299235933286863 106258494576448853899930295)
  ·
    refine ⟨159387741864673280849895443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106258494576448853899930295 159387741864673280849895443)
    ·
      refine ⟨239081612797009921274843165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159387741864673280849895443 239081612797009921274843165)
      ·
        refine ⟨89655604798878720478066187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 239081612797009921274843165 89655604798878720478066187)
        ·
          refine ⟨134483407198318080717099281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89655604798878720478066187 134483407198318080717099281)
          ·
            refine ⟨100862555398738560537824461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134483407198318080717099281 100862555398738560537824461)
            ·
              refine ⟨37823458274526960201684173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 100862555398738560537824461 37823458274526960201684173)
              ·
                refine ⟨14183796852947610075631565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37823458274526960201684173 14183796852947610075631565)
                ·
                  refine ⟨5318923819855353778361837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14183796852947610075631565 5318923819855353778361837)
                  ·
                    refine ⟨1994596432445757666885689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5318923819855353778361837 1994596432445757666885689)
                    ·
                      refine ⟨1495947324334318250164267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1994596432445757666885689 1495947324334318250164267)
                      ·
                        rfl

theorem cell23_2913347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 3, 3, 3, 2].length) (baseStart_2913347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2913347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2913347 prefixEnd_2913347 := by exact prefixLift 2913347
  have htrace : WordTrace (prefixWord ++ tailWord_2913347) baseStart_2913347 baseEnd_2913347 := by
    simpa [prefixWord, tailWord_2913347, baseEnd_2913347] using wordTrace_append hprefix tailTrace_2913347
  have hstable : (prefixWord ++ tailWord_2913347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2913347).length < 2 ^ (prefixWord ++ tailWord_2913347).sum := by decide
  have hdescent : baseEnd_2913347 < baseStart_2913347 := by decide
  rcases family_descends (prefixWord ++ tailWord_2913347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2913377 : List Nat := [1, 2, 3, 1, 1, 2, 2, 2, 3, 4, 2]
def baseStart_2913377 : Nat := 118140960795 + 2913377 * 2 ^ 59
def prefixEnd_2913377 : Nat := 4983230072969 + 3 ^ 40 * 2913377 * 2
def baseEnd_2913377 : Nat := 1495962728753953132789129

theorem tailTrace_2913377 : CollatzResearch.WordTrace tailWord_2913377 prefixEnd_2913377 1495962728753953132789129 := by
  unfold tailWord_2913377
  simp only [CollatzResearch.WordTrace]
  refine ⟨106259588766340169023522385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70839725844226779349014923 106259588766340169023522385)
  ·
    refine ⟨79694691574755126767641789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106259588766340169023522385 79694691574755126767641789)
    ·
      refine ⟨29885509340533172537865671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79694691574755126767641789 29885509340533172537865671)
      ·
        refine ⟨44828264010799758806798507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29885509340533172537865671 44828264010799758806798507)
        ·
          refine ⟨67242396016199638210197761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44828264010799758806798507 67242396016199638210197761)
          ·
            refine ⟨50431797012149728657648321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67242396016199638210197761 50431797012149728657648321)
            ·
              refine ⟨37823847759112296493236241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50431797012149728657648321 37823847759112296493236241)
              ·
                refine ⟨28367885819334222369927181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37823847759112296493236241 28367885819334222369927181)
                ·
                  refine ⟨10637957182250333388722693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28367885819334222369927181 10637957182250333388722693)
                  ·
                    refine ⟨1994616971671937510385505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10637957182250333388722693 1994616971671937510385505)
                    ·
                      refine ⟨1495962728753953132789129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1994616971671937510385505 1495962728753953132789129)
                      ·
                        rfl

theorem cell23_2913377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 2, 3, 4, 2].length) (baseStart_2913377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2913377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2913377 prefixEnd_2913377 := by exact prefixLift 2913377
  have htrace : WordTrace (prefixWord ++ tailWord_2913377) baseStart_2913377 baseEnd_2913377 := by
    simpa [prefixWord, tailWord_2913377, baseEnd_2913377] using wordTrace_append hprefix tailTrace_2913377
  have hstable : (prefixWord ++ tailWord_2913377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2913377).length < 2 ^ (prefixWord ++ tailWord_2913377).sum := by decide
  have hdescent : baseEnd_2913377 < baseStart_2913377 := by decide
  rcases family_descends (prefixWord ++ tailWord_2913377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2913380 : List Nat := [2, 3, 1, 1, 2, 1, 1, 2, 4, 1, 5]
def baseStart_2913380 : Nat := 118140960795 + 2913380 * 2 ^ 59
def prefixEnd_2913380 : Nat := 4983230072969 + 3 ^ 40 * 2913380 * 2
def baseEnd_2913380 : Nat := 1495964269195916621051615

theorem tailTrace_2913380 : CollatzResearch.WordTrace tailWord_2913380 prefixEnd_2913380 1495964269195916621051615 := by
  unfold tailWord_2913380
  simp only [CollatzResearch.WordTrace]
  refine ⟨53129849092664650267940797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70839798790219533690587729 53129849092664650267940797)
  ·
    refine ⟨19923693409749243850477799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53129849092664650267940797 19923693409749243850477799)
    ·
      refine ⟨29885540114623865775716699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19923693409749243850477799 29885540114623865775716699)
      ·
        refine ⟨44828310171935798663575049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29885540114623865775716699 44828310171935798663575049)
        ·
          refine ⟨33621232628951848997681287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44828310171935798663575049 33621232628951848997681287)
          ·
            refine ⟨50431848943427773496521931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33621232628951848997681287 50431848943427773496521931)
            ·
              refine ⟨75647773415141660244782897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50431848943427773496521931 75647773415141660244782897)
              ·
                refine ⟨56735830061356245183587173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75647773415141660244782897 56735830061356245183587173)
                ·
                  refine ⟨10637968136504295971922595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56735830061356245183587173 10637968136504295971922595)
                  ·
                    refine ⟨15956952204756443957883893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10637968136504295971922595 15956952204756443957883893)
                    ·
                      refine ⟨1495964269195916621051615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15956952204756443957883893 1495964269195916621051615)
                      ·
                        rfl

theorem cell23_2913380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 2, 4, 1, 5].length) (baseStart_2913380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2913380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2913380 prefixEnd_2913380 := by exact prefixLift 2913380
  have htrace : WordTrace (prefixWord ++ tailWord_2913380) baseStart_2913380 baseEnd_2913380 := by
    simpa [prefixWord, tailWord_2913380, baseEnd_2913380] using wordTrace_append hprefix tailTrace_2913380
  have hstable : (prefixWord ++ tailWord_2913380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2913380).length < 2 ^ (prefixWord ++ tailWord_2913380).sum := by decide
  have hdescent : baseEnd_2913380 < baseStart_2913380 := by decide
  rcases family_descends (prefixWord ++ tailWord_2913380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2913400 : List Nat := [2, 1, 2, 1, 1, 1, 6, 2, 7]
def baseStart_2913400 : Nat := 118140960795 + 2913400 * 2 ^ 59
def prefixEnd_2913400 : Nat := 4983230072969 + 3 ^ 40 * 2913400 * 2
def baseEnd_2913400 : Nat := 166219393201000726977947

theorem tailTrace_2913400 : CollatzResearch.WordTrace tailWord_2913400 prefixEnd_2913400 166219393201000726977947 := by
  unfold tailWord_2913400
  simp only [CollatzResearch.WordTrace]
  refine ⟨53130213822628421975804827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70840285096837895967739769 53130213822628421975804827)
  ·
    refine ⟨79695320733942632963707241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53130213822628421975804827 79695320733942632963707241)
    ·
      refine ⟨59771490550456974722780431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79695320733942632963707241 59771490550456974722780431)
      ·
        refine ⟨89657235825685462084170647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59771490550456974722780431 89657235825685462084170647)
        ·
          refine ⟨134485853738528193126255971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89657235825685462084170647 134485853738528193126255971)
          ·
            refine ⟨201728780607792289689383957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134485853738528193126255971 201728780607792289689383957)
            ·
              refine ⟨9456036590990263579189873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 201728780607792289689383957 9456036590990263579189873)
              ·
                refine ⟨7092027443242697684392405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9456036590990263579189873 7092027443242697684392405)
                ·
                  refine ⟨166219393201000726977947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7092027443242697684392405 166219393201000726977947)
                  ·
                    rfl

theorem cell23_2913400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 2, 7].length) (baseStart_2913400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2913400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2913400 prefixEnd_2913400 := by exact prefixLift 2913400
  have htrace : WordTrace (prefixWord ++ tailWord_2913400) baseStart_2913400 baseEnd_2913400 := by
    simpa [prefixWord, tailWord_2913400, baseEnd_2913400] using wordTrace_append hprefix tailTrace_2913400
  have hstable : (prefixWord ++ tailWord_2913400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2913400).length < 2 ^ (prefixWord ++ tailWord_2913400).sum := by decide
  have hdescent : baseEnd_2913400 < baseStart_2913400 := by decide
  rcases family_descends (prefixWord ++ tailWord_2913400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2913406 : List Nat := [4, 2, 4, 1, 2, 1, 1, 3, 1, 2, 2]
def baseStart_2913406 : Nat := 118140960795 + 2913406 * 2 ^ 59
def prefixEnd_2913406 : Nat := 4983230072969 + 3 ^ 40 * 2913406 * 2
def baseEnd_2913406 : Nat := 1495977619692933519326497

theorem tailTrace_2913406 : CollatzResearch.WordTrace tailWord_2913406 prefixEnd_2913406 1495977619692933519326497 := by
  unfold tailWord_2913406
  simp only [CollatzResearch.WordTrace]
  refine ⟨13282580810404388372041009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70840430988823404650885381 13282580810404388372041009)
  ·
    refine ⟨9961935607803291279030757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13282580810404388372041009 9961935607803291279030757)
    ·
      refine ⟨1867862926463117114818267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9961935607803291279030757 1867862926463117114818267)
      ·
        refine ⟨2801794389694675672227401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1867862926463117114818267 2801794389694675672227401)
        ·
          refine ⟨2101345792271006754170551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2801794389694675672227401 2101345792271006754170551)
          ·
            refine ⟨3152018688406510131255827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2101345792271006754170551 3152018688406510131255827)
            ·
              refine ⟨4728028032609765196883741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3152018688406510131255827 4728028032609765196883741)
              ·
                refine ⟨1773010512228661948831403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4728028032609765196883741 1773010512228661948831403)
                ·
                  refine ⟨2659515768342992923247105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1773010512228661948831403 2659515768342992923247105)
                  ·
                    refine ⟨1994636826257244692435329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2659515768342992923247105 1994636826257244692435329)
                    ·
                      refine ⟨1495977619692933519326497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1994636826257244692435329 1495977619692933519326497)
                      ·
                        rfl

theorem cell23_2913406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 1, 3, 1, 2, 2].length) (baseStart_2913406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2913406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2913406 prefixEnd_2913406 := by exact prefixLift 2913406
  have htrace : WordTrace (prefixWord ++ tailWord_2913406) baseStart_2913406 baseEnd_2913406 := by
    simpa [prefixWord, tailWord_2913406, baseEnd_2913406] using wordTrace_append hprefix tailTrace_2913406
  have hstable : (prefixWord ++ tailWord_2913406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2913406).length < 2 ^ (prefixWord ++ tailWord_2913406).sum := by decide
  have hdescent : baseEnd_2913406 < baseStart_2913406 := by decide
  rcases family_descends (prefixWord ++ tailWord_2913406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2913434 : List Nat := [3, 1, 1, 5, 1, 3, 1, 1, 7]
def baseStart_2913434 : Nat := 118140960795 + 2913434 * 2 ^ 59
def prefixEnd_2913434 : Nat := 4983230072969 + 3 ^ 40 * 2913434 * 2
def baseEnd_2913434 : Nat := 166221333016806601086263

theorem tailTrace_2913434 : CollatzResearch.WordTrace tailWord_2913434 prefixEnd_2913434 166221333016806601086263 := by
  unfold tailWord_2913434
  simp only [CollatzResearch.WordTrace]
  refine ⟨26565416931783416939586839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70841111818089111838898237 26565416931783416939586839)
  ·
    refine ⟨39848125397675125409380259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26565416931783416939586839 39848125397675125409380259)
    ·
      refine ⟨59772188096512688114070389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39848125397675125409380259 59772188096512688114070389)
      ·
        refine ⟨5603642634048064510694099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 59772188096512688114070389 5603642634048064510694099)
        ·
          refine ⟨8405463951072096766041149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5603642634048064510694099 8405463951072096766041149)
          ·
            refine ⟨3152048981652036287265431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8405463951072096766041149 3152048981652036287265431)
            ·
              refine ⟨4728073472478054430898147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3152048981652036287265431 4728073472478054430898147)
              ·
                refine ⟨7092110208717081646347221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4728073472478054430898147 7092110208717081646347221)
                ·
                  refine ⟨166221333016806601086263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7092110208717081646347221 166221333016806601086263)
                  ·
                    rfl

theorem cell23_2913434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 1, 1, 7].length) (baseStart_2913434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2913434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2913434 prefixEnd_2913434 := by exact prefixLift 2913434
  have htrace : WordTrace (prefixWord ++ tailWord_2913434) baseStart_2913434 baseEnd_2913434 := by
    simpa [prefixWord, tailWord_2913434, baseEnd_2913434] using wordTrace_append hprefix tailTrace_2913434
  have hstable : (prefixWord ++ tailWord_2913434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2913434).length < 2 ^ (prefixWord ++ tailWord_2913434).sum := by decide
  have hdescent : baseEnd_2913434 < baseStart_2913434 := by decide
  rcases family_descends (prefixWord ++ tailWord_2913434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2913467 : List Nat := [1, 1, 1, 1, 1, 2, 4, 1, 3, 6, 2]
def baseStart_2913467 : Nat := 118140960795 + 2913467 * 2 ^ 59
def prefixEnd_2913467 : Nat := 4983230072969 + 3 ^ 40 * 2913467 * 2
def baseEnd_2913467 : Nat := 1496008942012857780663715

theorem tailTrace_2913467 : CollatzResearch.WordTrace tailWord_2913467 prefixEnd_2913467 1496008942012857780663715 := by
  unfold tailWord_2913467
  simp only [CollatzResearch.WordTrace]
  refine ⟨106262871336014114394298655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70841914224009409596199103 106262871336014114394298655)
  ·
    refine ⟨159394307004021171591447983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106262871336014114394298655 159394307004021171591447983)
    ·
      refine ⟨239091460506031757387171975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159394307004021171591447983 239091460506031757387171975)
      ·
        refine ⟨358637190759047636080757963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239091460506031757387171975 358637190759047636080757963)
        ·
          refine ⟨537955786138571454121136945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 358637190759047636080757963 537955786138571454121136945)
          ·
            refine ⟨403466839603928590590852709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 537955786138571454121136945 403466839603928590590852709)
            ·
              refine ⟨75650032425736610735784883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 403466839603928590590852709 75650032425736610735784883)
              ·
                refine ⟨113475048638604916103677325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75650032425736610735784883 113475048638604916103677325)
                ·
                  refine ⟨42553143239476843538878997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 113475048638604916103677325 42553143239476843538878997)
                  ·
                    refine ⟨1994678589350477040884953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 42553143239476843538878997 1994678589350477040884953)
                    ·
                      refine ⟨1496008942012857780663715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1994678589350477040884953 1496008942012857780663715)
                      ·
                        rfl

theorem cell23_2913467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 3, 6, 2].length) (baseStart_2913467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2913467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2913467 prefixEnd_2913467 := by exact prefixLift 2913467
  have htrace : WordTrace (prefixWord ++ tailWord_2913467) baseStart_2913467 baseEnd_2913467 := by
    simpa [prefixWord, tailWord_2913467, baseEnd_2913467] using wordTrace_append hprefix tailTrace_2913467
  have hstable : (prefixWord ++ tailWord_2913467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2913467).length < 2 ^ (prefixWord ++ tailWord_2913467).sum := by decide
  have hdescent : baseEnd_2913467 < baseStart_2913467 := by decide
  rcases family_descends (prefixWord ++ tailWord_2913467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2913487 : List Nat := [1, 1, 2, 1, 1, 3, 2, 3, 4, 2, 3]
def baseStart_2913487 : Nat := 118140960795 + 2913487 * 2 ^ 59
def prefixEnd_2913487 : Nat := 4983230072969 + 3 ^ 40 * 2913487 * 2
def baseEnd_2913487 : Nat := 1496019211625947702413623

theorem tailTrace_2913487 : CollatzResearch.WordTrace tailWord_2913487 prefixEnd_2913487 1496019211625947702413623 := by
  unfold tailWord_2913487
  simp only [CollatzResearch.WordTrace]
  refine ⟨106263600795941657810026715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70842400530627771873351143 106263600795941657810026715)
  ·
    refine ⟨159395401193912486715040073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106263600795941657810026715 159395401193912486715040073)
    ·
      refine ⟨119546550895434365036280055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159395401193912486715040073 119546550895434365036280055)
      ·
        refine ⟨179319826343151547554420083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119546550895434365036280055 179319826343151547554420083)
        ·
          refine ⟨268979739514727321331630125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179319826343151547554420083 268979739514727321331630125)
          ·
            refine ⟨100867402318022745499361297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 268979739514727321331630125 100867402318022745499361297)
            ·
              refine ⟨75650551738517059124520973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100867402318022745499361297 75650551738517059124520973)
              ·
                refine ⟨28368956901943897171695365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75650551738517059124520973 28368956901943897171695365)
                ·
                  refine ⟨5319179419114480719692881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28368956901943897171695365 5319179419114480719692881)
                  ·
                    refine ⟨3989384564335860539769661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5319179419114480719692881 3989384564335860539769661)
                    ·
                      refine ⟨1496019211625947702413623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3989384564335860539769661 1496019211625947702413623)
                      ·
                        rfl

theorem cell23_2913487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 3, 4, 2, 3].length) (baseStart_2913487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2913487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2913487 prefixEnd_2913487 := by exact prefixLift 2913487
  have htrace : WordTrace (prefixWord ++ tailWord_2913487) baseStart_2913487 baseEnd_2913487 := by
    simpa [prefixWord, tailWord_2913487, baseEnd_2913487] using wordTrace_append hprefix tailTrace_2913487
  have hstable : (prefixWord ++ tailWord_2913487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2913487).length < 2 ^ (prefixWord ++ tailWord_2913487).sum := by decide
  have hdescent : baseEnd_2913487 < baseStart_2913487 := by decide
  rcases family_descends (prefixWord ++ tailWord_2913487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2913511 : List Nat := [1, 1, 5, 3, 2, 1, 1, 2, 3, 4]
def baseStart_2913511 : Nat := 118140960795 + 2913511 * 2 ^ 59
def prefixEnd_2913511 : Nat := 4983230072969 + 3 ^ 40 * 2913511 * 2
def baseEnd_2913511 : Nat := 498677178387218536171171

theorem tailTrace_2913511 : CollatzResearch.WordTrace tailWord_2913511 prefixEnd_2913511 498677178387218536171171 := by
  unfold tailWord_2913511
  simp only [CollatzResearch.WordTrace]
  refine ⟨106264476147854709908900387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70842984098569806605933591 106264476147854709908900387)
  ·
    refine ⟨159396714221782064863350581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106264476147854709908900387 159396714221782064863350581)
    ·
      refine ⟨14943441958292068580939117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 159396714221782064863350581 14943441958292068580939117)
      ·
        refine ⟨5603790734359525717852169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14943441958292068580939117 5603790734359525717852169)
        ·
          refine ⟨4202843050769644288389127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5603790734359525717852169 4202843050769644288389127)
          ·
            refine ⟨6304264576154466432583691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4202843050769644288389127 6304264576154466432583691)
            ·
              refine ⟨9456396864231699648875537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6304264576154466432583691 9456396864231699648875537)
              ·
                refine ⟨7092297648173774736656653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9456396864231699648875537 7092297648173774736656653)
                ·
                  refine ⟨2659611618065165526246245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7092297648173774736656653 2659611618065165526246245)
                  ·
                    refine ⟨498677178387218536171171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2659611618065165526246245 498677178387218536171171)
                    ·
                      rfl

theorem cell23_2913511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 2, 3, 4].length) (baseStart_2913511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2913511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2913511 prefixEnd_2913511 := by exact prefixLift 2913511
  have htrace : WordTrace (prefixWord ++ tailWord_2913511) baseStart_2913511 baseEnd_2913511 := by
    simpa [prefixWord, tailWord_2913511, baseEnd_2913511] using wordTrace_append hprefix tailTrace_2913511
  have hstable : (prefixWord ++ tailWord_2913511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2913511).length < 2 ^ (prefixWord ++ tailWord_2913511).sum := by decide
  have hdescent : baseEnd_2913511 < baseStart_2913511 := by decide
  rcases family_descends (prefixWord ++ tailWord_2913511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2913585 : List Nat := [1, 2, 2, 3, 3, 3, 1, 3, 1, 1, 3]
def baseStart_2913585 : Nat := 118140960795 + 2913585 * 2 ^ 59
def prefixEnd_2913585 : Nat := 4983230072969 + 3 ^ 40 * 2913585 * 2
def baseEnd_2913585 : Nat := 1496069532730088318988173

theorem tailTrace_2913585 : CollatzResearch.WordTrace tailWord_2913585 prefixEnd_2913585 1496069532730088318988173 := by
  unfold tailWord_2913585
  simp only [CollatzResearch.WordTrace]
  refine ⟨106267175149586620547094209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70844783433057747031396139 106267175149586620547094209)
  ·
    refine ⟨79700381362189965410320657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106267175149586620547094209 79700381362189965410320657)
    ·
      refine ⟨59775286021642474057740493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79700381362189965410320657 59775286021642474057740493)
      ·
        refine ⟨22415732258115927771652685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59775286021642474057740493 22415732258115927771652685)
        ·
          refine ⟨8405899596793472914369757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22415732258115927771652685 8405899596793472914369757)
          ·
            refine ⟨3152212348797552342888659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8405899596793472914369757 3152212348797552342888659)
            ·
              refine ⟨4728318523196328514332989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3152212348797552342888659 4728318523196328514332989)
              ·
                refine ⟨1773119446198623192874871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4728318523196328514332989 1773119446198623192874871)
                ·
                  refine ⟨2659679169297934789312307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1773119446198623192874871 2659679169297934789312307)
                  ·
                    refine ⟨3989518753946902183968461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2659679169297934789312307 3989518753946902183968461)
                    ·
                      refine ⟨1496069532730088318988173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3989518753946902183968461 1496069532730088318988173)
                      ·
                        rfl

theorem cell23_2913585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 1, 3, 1, 1, 3].length) (baseStart_2913585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2913585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2913585 prefixEnd_2913585 := by exact prefixLift 2913585
  have htrace : WordTrace (prefixWord ++ tailWord_2913585) baseStart_2913585 baseEnd_2913585 := by
    simpa [prefixWord, tailWord_2913585, baseEnd_2913585] using wordTrace_append hprefix tailTrace_2913585
  have hstable : (prefixWord ++ tailWord_2913585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2913585).length < 2 ^ (prefixWord ++ tailWord_2913585).sum := by decide
  have hdescent : baseEnd_2913585 < baseStart_2913585 := by decide
  rcases family_descends (prefixWord ++ tailWord_2913585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2913594 : List Nat := [3, 1, 1, 1, 4, 1, 4, 1, 1, 1, 5]
def baseStart_2913594 : Nat := 118140960795 + 2913594 * 2 ^ 59
def prefixEnd_2913594 : Nat := 4983230072969 + 3 ^ 40 * 2913594 * 2
def baseEnd_2913594 : Nat := 1496074154055978783775631

theorem tailTrace_2913594 : CollatzResearch.WordTrace tailWord_2913594 prefixEnd_2913594 1496074154055978783775631 := by
  unfold tailWord_2913594
  simp only [CollatzResearch.WordTrace]
  refine ⟨26566875851638503771042959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70845002271036010056114557 26566875851638503771042959)
  ·
    refine ⟨39850313777457755656564439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26566875851638503771042959 39850313777457755656564439)
    ·
      refine ⟨59775470666186633484846659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39850313777457755656564439 59775470666186633484846659)
      ·
        refine ⟨89663205999279950227269989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59775470666186633484846659 89663205999279950227269989)
        ·
          refine ⟨16811851124864990667613123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 89663205999279950227269989 16811851124864990667613123)
          ·
            refine ⟨25217776687297486001419685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16811851124864990667613123 25217776687297486001419685)
            ·
              refine ⟨4728333128868278625266191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25217776687297486001419685 4728333128868278625266191)
              ·
                refine ⟨7092499693302417937899287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4728333128868278625266191 7092499693302417937899287)
                ·
                  refine ⟨10638749539953626906848931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7092499693302417937899287 10638749539953626906848931)
                  ·
                    refine ⟨15958124309930440360273397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10638749539953626906848931 15958124309930440360273397)
                    ·
                      refine ⟨1496074154055978783775631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15958124309930440360273397 1496074154055978783775631)
                      ·
                        rfl

theorem cell23_2913594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 4, 1, 1, 1, 5].length) (baseStart_2913594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2913594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2913594 prefixEnd_2913594 := by exact prefixLift 2913594
  have htrace : WordTrace (prefixWord ++ tailWord_2913594) baseStart_2913594 baseEnd_2913594 := by
    simpa [prefixWord, tailWord_2913594, baseEnd_2913594] using wordTrace_append hprefix tailTrace_2913594
  have hstable : (prefixWord ++ tailWord_2913594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2913594).length < 2 ^ (prefixWord ++ tailWord_2913594).sum := by decide
  have hdescent : baseEnd_2913594 < baseStart_2913594 := by decide
  rcases family_descends (prefixWord ++ tailWord_2913594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2913601 : List Nat := [1, 2, 5, 2, 1, 1, 2, 1, 4, 4]
def baseStart_2913601 : Nat := 118140960795 + 2913601 * 2 ^ 59
def prefixEnd_2913601 : Nat := 4983230072969 + 3 ^ 40 * 2913601 * 2
def baseEnd_2913601 : Nat := 498692582806853418796033

theorem tailTrace_2913601 : CollatzResearch.WordTrace tailWord_2913601 prefixEnd_2913601 498692582806853418796033 := by
  unfold tailWord_2913601
  simp only [CollatzResearch.WordTrace]
  refine ⟨106267758717528655279676657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70845172478352436853117771 106267758717528655279676657)
  ·
    refine ⟨79700819038146491459757493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106267758717528655279676657 79700819038146491459757493)
    ·
      refine ⟨7471951784826233574352265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 79700819038146491459757493 7471951784826233574352265)
      ·
        refine ⟨5603963838619675180764199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7471951784826233574352265 5603963838619675180764199)
        ·
          refine ⟨8405945757929512771146299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5603963838619675180764199 8405945757929512771146299)
          ·
            refine ⟨12608918636894269156719449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8405945757929512771146299 12608918636894269156719449)
            ·
              refine ⟨9456688977670701867539587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12608918636894269156719449 9456688977670701867539587)
              ·
                refine ⟨14185033466506052801309381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9456688977670701867539587 14185033466506052801309381)
                ·
                  refine ⟨2659693774969884900245509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14185033466506052801309381 2659693774969884900245509)
                  ·
                    refine ⟨498692582806853418796033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2659693774969884900245509 498692582806853418796033)
                    ·
                      rfl

theorem cell23_2913601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 1, 4, 4].length) (baseStart_2913601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2913601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2913601 prefixEnd_2913601 := by exact prefixLift 2913601
  have htrace : WordTrace (prefixWord ++ tailWord_2913601) baseStart_2913601 baseEnd_2913601 := by
    simpa [prefixWord, tailWord_2913601, baseEnd_2913601] using wordTrace_append hprefix tailTrace_2913601
  have hstable : (prefixWord ++ tailWord_2913601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2913601).length < 2 ^ (prefixWord ++ tailWord_2913601).sum := by decide
  have hdescent : baseEnd_2913601 < baseStart_2913601 := by decide
  rcases family_descends (prefixWord ++ tailWord_2913601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2913617 : List Nat := [1, 2, 2, 1, 4, 1, 1, 1, 2, 2, 6]
def baseStart_2913617 : Nat := 118140960795 + 2913617 * 2 ^ 59
def prefixEnd_2913617 : Nat := 4983230072969 + 3 ^ 40 * 2913617 * 2
def baseEnd_2913617 : Nat := 1496085964111032193788025

theorem tailTrace_2913617 : CollatzResearch.WordTrace tailWord_2913617 prefixEnd_2913617 1496085964111032193788025 := by
  unfold tailWord_2913617
  simp only [CollatzResearch.WordTrace]
  refine ⟨106268342285470690012259105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70845561523647126674839403 106268342285470690012259105)
  ·
    refine ⟨79701256714103017509194329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106268342285470690012259105 79701256714103017509194329)
    ·
      refine ⟨59775942535577263131895747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79701256714103017509194329 59775942535577263131895747)
      ·
        refine ⟨89663913803365894697843621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59775942535577263131895747 89663913803365894697843621)
        ·
          refine ⟨16811983838131105255845679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 89663913803365894697843621 16811983838131105255845679)
          ·
            refine ⟨25217975757196657883768519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16811983838131105255845679 25217975757196657883768519)
            ·
              refine ⟨37826963635794986825652779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25217975757196657883768519 37826963635794986825652779)
              ·
                refine ⟨56740445453692480238479169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37826963635794986825652779 56740445453692480238479169)
                ·
                  refine ⟨42555334090269360178859377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56740445453692480238479169 42555334090269360178859377)
                  ·
                    refine ⟨31916500567702020134144533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42555334090269360178859377 31916500567702020134144533)
                    ·
                      refine ⟨1496085964111032193788025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31916500567702020134144533 1496085964111032193788025)
                      ·
                        rfl

theorem cell23_2913617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 1, 2, 2, 6].length) (baseStart_2913617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2913617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2913617 prefixEnd_2913617 := by exact prefixLift 2913617
  have htrace : WordTrace (prefixWord ++ tailWord_2913617) baseStart_2913617 baseEnd_2913617 := by
    simpa [prefixWord, tailWord_2913617, baseEnd_2913617] using wordTrace_append hprefix tailTrace_2913617
  have hstable : (prefixWord ++ tailWord_2913617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2913617).length < 2 ^ (prefixWord ++ tailWord_2913617).sum := by decide
  have hdescent : baseEnd_2913617 < baseStart_2913617 := by decide
  rcases family_descends (prefixWord ++ tailWord_2913617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2913624 : List Nat := [2, 1, 2, 2, 1, 1, 4, 3, 1, 3, 3]
def baseStart_2913624 : Nat := 118140960795 + 2913624 * 2 ^ 59
def prefixEnd_2913624 : Nat := 4983230072969 + 3 ^ 40 * 2913624 * 2
def baseEnd_2913624 : Nat := 1496089558475613666400493

theorem tailTrace_2913624 : CollatzResearch.WordTrace tailWord_2913624 prefixEnd_2913624 1496089558475613666400493 := by
  unfold tailWord_2913624
  simp only [CollatzResearch.WordTrace]
  refine ⟨53134298798222665103881963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70845731730963553471842617 53134298798222665103881963)
  ·
    refine ⟨79701448197333997655822945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53134298798222665103881963 79701448197333997655822945)
    ·
      refine ⟨59776086148000498241867209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79701448197333997655822945 59776086148000498241867209)
      ·
        refine ⟨44832064611000373681400407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59776086148000498241867209 44832064611000373681400407)
        ·
          refine ⟨67248096916500560522100611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44832064611000373681400407 67248096916500560522100611)
          ·
            refine ⟨100872145374750840783150917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67248096916500560522100611 100872145374750840783150917)
            ·
              refine ⟨18913527257765782646840797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 100872145374750840783150917 18913527257765782646840797)
              ·
                refine ⟨7092572721662168492565299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18913527257765782646840797 7092572721662168492565299)
                ·
                  refine ⟨10638859082493252738847949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7092572721662168492565299 10638859082493252738847949)
                  ·
                    refine ⟨3989572155934969777067981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10638859082493252738847949 3989572155934969777067981)
                    ·
                      refine ⟨1496089558475613666400493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3989572155934969777067981 1496089558475613666400493)
                      ·
                        rfl

theorem cell23_2913624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 3, 1, 3, 3].length) (baseStart_2913624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2913624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2913624 prefixEnd_2913624 := by exact prefixLift 2913624
  have htrace : WordTrace (prefixWord ++ tailWord_2913624) baseStart_2913624 baseEnd_2913624 := by
    simpa [prefixWord, tailWord_2913624, baseEnd_2913624] using wordTrace_append hprefix tailTrace_2913624
  have hstable : (prefixWord ++ tailWord_2913624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2913624).length < 2 ^ (prefixWord ++ tailWord_2913624).sum := by decide
  have hdescent : baseEnd_2913624 < baseStart_2913624 := by decide
  rcases family_descends (prefixWord ++ tailWord_2913624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2913698 : List Nat := [3, 3, 1, 2, 1, 2, 2, 2, 1, 4, 2]
def baseStart_2913698 : Nat := 118140960795 + 2913698 * 2 ^ 59
def prefixEnd_2913698 : Nat := 4983230072969 + 3 ^ 40 * 2913698 * 2
def baseEnd_2913698 : Nat := 1496127556044046376875153

theorem tailTrace_2913698 : CollatzResearch.WordTrace tailWord_2913698 prefixEnd_2913698 1496127556044046376875153 := by
  unfold tailWord_2913698
  simp only [CollatzResearch.WordTrace]
  refine ⟨26567824149544310211489437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70847531065451493897305165 26567824149544310211489437)
  ·
    refine ⟨9962934056079116329308539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26567824149544310211489437 9962934056079116329308539)
    ·
      refine ⟨14944401084118674493962809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9962934056079116329308539 14944401084118674493962809)
      ·
        refine ⟨11208300813089005870472107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14944401084118674493962809 11208300813089005870472107)
        ·
          refine ⟨16812451219633508805708161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11208300813089005870472107 16812451219633508805708161)
          ·
            refine ⟨12609338414725131604281121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16812451219633508805708161 12609338414725131604281121)
            ·
              refine ⟨9457003811043848703210841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12609338414725131604281121 9457003811043848703210841)
              ·
                refine ⟨7092752858282886527408131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9457003811043848703210841 7092752858282886527408131)
                ·
                  refine ⟨10639129287424329791112197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7092752858282886527408131 10639129287424329791112197)
                  ·
                    refine ⟨1994836741392061835833537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10639129287424329791112197 1994836741392061835833537)
                    ·
                      refine ⟨1496127556044046376875153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1994836741392061835833537 1496127556044046376875153)
                      ·
                        rfl

theorem cell23_2913698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 2, 1, 4, 2].length) (baseStart_2913698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2913698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2913698 prefixEnd_2913698 := by exact prefixLift 2913698
  have htrace : WordTrace (prefixWord ++ tailWord_2913698) baseStart_2913698 baseEnd_2913698 := by
    simpa [prefixWord, tailWord_2913698, baseEnd_2913698] using wordTrace_append hprefix tailTrace_2913698
  have hstable : (prefixWord ++ tailWord_2913698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2913698).length < 2 ^ (prefixWord ++ tailWord_2913698).sum := by decide
  have hdescent : baseEnd_2913698 < baseStart_2913698 := by decide
  rcases family_descends (prefixWord ++ tailWord_2913698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2913707 : List Nat := [1, 1, 1, 1, 2, 1, 1, 2, 4, 1, 8]
def baseStart_2913707 : Nat := 118140960795 + 2913707 * 2 ^ 59
def prefixEnd_2913707 : Nat := 4983230072969 + 3 ^ 40 * 2913707 * 2
def baseEnd_2913707 : Nat := 1496132177369936841662611

theorem tailTrace_2913707 : CollatzResearch.WordTrace tailWord_2913707 prefixEnd_2913707 1496132177369936841662611 := by
  unfold tailWord_2913707
  simp only [CollatzResearch.WordTrace]
  refine ⟨106271624855144635383035375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70847749903429756922023583 106271624855144635383035375)
  ·
    refine ⟨159407437282716953074553063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106271624855144635383035375 159407437282716953074553063)
    ·
      refine ⟨239111155924075429611829595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159407437282716953074553063 239111155924075429611829595)
      ·
        refine ⟨358666733886113144417744393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239111155924075429611829595 358666733886113144417744393)
        ·
          refine ⟨269000050414584858313308295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 358666733886113144417744393 269000050414584858313308295)
          ·
            refine ⟨403500075621877287469962443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 269000050414584858313308295 403500075621877287469962443)
            ·
              refine ⟨605250113432815931204943665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 403500075621877287469962443 605250113432815931204943665)
              ·
                refine ⟨453937585074611948403707749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 605250113432815931204943665 453937585074611948403707749)
                ·
                  refine ⟨85113297201489740325695203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 453937585074611948403707749 85113297201489740325695203)
                  ·
                    refine ⟨127669945802234610488542805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 85113297201489740325695203 127669945802234610488542805)
                    ·
                      refine ⟨1496132177369936841662611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 127669945802234610488542805 1496132177369936841662611)
                      ·
                        rfl

theorem cell23_2913707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 4, 1, 8].length) (baseStart_2913707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2913707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2913707 prefixEnd_2913707 := by exact prefixLift 2913707
  have htrace : WordTrace (prefixWord ++ tailWord_2913707) baseStart_2913707 baseEnd_2913707 := by
    simpa [prefixWord, tailWord_2913707, baseEnd_2913707] using wordTrace_append hprefix tailTrace_2913707
  have hstable : (prefixWord ++ tailWord_2913707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2913707).length < 2 ^ (prefixWord ++ tailWord_2913707).sum := by decide
  have hdescent : baseEnd_2913707 < baseStart_2913707 := by decide
  rcases family_descends (prefixWord ++ tailWord_2913707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2913721 : List Nat := [1, 2, 1, 4, 4, 1, 2, 1, 7]
def baseStart_2913721 : Nat := 118140960795 + 2913721 * 2 ^ 59
def prefixEnd_2913721 : Nat := 4983230072969 + 3 ^ 40 * 2913721 * 2
def baseEnd_2913721 : Nat := 166237707344344420765283

theorem tailTrace_2913721 : CollatzResearch.WordTrace tailWord_2913721 prefixEnd_2913721 166237707344344420765283 := by
  unfold tailWord_2913721
  simp only [CollatzResearch.WordTrace]
  refine ⟨106272135477093915774045017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70848090318062610516030011 106272135477093915774045017)
  ·
    refine ⟨79704101607820436830533763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106272135477093915774045017 79704101607820436830533763)
    ·
      refine ⟨119556152411730655245800645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79704101607820436830533763 119556152411730655245800645)
      ·
        refine ⟨22416778577199497858587621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 119556152411730655245800645 22416778577199497858587621)
        ·
          refine ⟨4203145983224905848485179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22416778577199497858587621 4203145983224905848485179)
          ·
            refine ⟨6304718974837358772727769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4203145983224905848485179 6304718974837358772727769)
            ·
              refine ⟨4728539231128019079545827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6304718974837358772727769 4728539231128019079545827)
              ·
                refine ⟨7092808846692028619318741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4728539231128019079545827 7092808846692028619318741)
                ·
                  refine ⟨166237707344344420765283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7092808846692028619318741 166237707344344420765283)
                  ·
                    rfl

theorem cell23_2913721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 2, 1, 7].length) (baseStart_2913721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2913721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2913721 prefixEnd_2913721 := by exact prefixLift 2913721
  have htrace : WordTrace (prefixWord ++ tailWord_2913721) baseStart_2913721 baseEnd_2913721 := by
    simpa [prefixWord, tailWord_2913721, baseEnd_2913721] using wordTrace_append hprefix tailTrace_2913721
  have hstable : (prefixWord ++ tailWord_2913721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2913721).length < 2 ^ (prefixWord ++ tailWord_2913721).sum := by decide
  have hdescent : baseEnd_2913721 < baseStart_2913721 := by decide
  rcases family_descends (prefixWord ++ tailWord_2913721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2913771 : List Nat := [1, 1, 1, 1, 2, 3, 2, 4, 2, 4, 2]
def baseStart_2913771 : Nat := 118140960795 + 2913771 * 2 ^ 59
def prefixEnd_2913771 : Nat := 4983230072969 + 3 ^ 40 * 2913771 * 2
def baseEnd_2913771 : Nat := 1496165040131824591262317

theorem tailTrace_2913771 : CollatzResearch.WordTrace tailWord_2913771 prefixEnd_2913771 1496165040131824591262317 := by
  unfold tailWord_2913771
  simp only [CollatzResearch.WordTrace]
  refine ⟨106273959126912774313365167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70849306084608516208910111 106273959126912774313365167)
  ·
    refine ⟨159410938690369161470047751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106273959126912774313365167 159410938690369161470047751)
    ·
      refine ⟨239116408035553742205071627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159410938690369161470047751 239116408035553742205071627)
      ·
        refine ⟨358674612053330613307607441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239116408035553742205071627 358674612053330613307607441)
        ·
          refine ⟨269005959039997959980705581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 358674612053330613307607441 269005959039997959980705581)
          ·
            refine ⟨100877234639999234992764593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 269005959039997959980705581 100877234639999234992764593)
            ·
              refine ⟨75657925979999426244573445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100877234639999234992764593 75657925979999426244573445)
              ·
                refine ⟨14185861121249892420857521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 75657925979999426244573445 14185861121249892420857521)
                ·
                  refine ⟨10639395840937419315643141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14185861121249892420857521 10639395840937419315643141)
                  ·
                    refine ⟨1994886720175766121683089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10639395840937419315643141 1994886720175766121683089)
                    ·
                      refine ⟨1496165040131824591262317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1994886720175766121683089 1496165040131824591262317)
                      ·
                        rfl

theorem cell23_2913771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 4, 2, 4, 2].length) (baseStart_2913771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2913771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2913771 prefixEnd_2913771 := by exact prefixLift 2913771
  have htrace : WordTrace (prefixWord ++ tailWord_2913771) baseStart_2913771 baseEnd_2913771 := by
    simpa [prefixWord, tailWord_2913771, baseEnd_2913771] using wordTrace_append hprefix tailTrace_2913771
  have hstable : (prefixWord ++ tailWord_2913771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2913771).length < 2 ^ (prefixWord ++ tailWord_2913771).sum := by decide
  have hdescent : baseEnd_2913771 < baseStart_2913771 := by decide
  rcases family_descends (prefixWord ++ tailWord_2913771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2913832 : List Nat := [2, 1, 5, 2, 2, 1, 1, 4, 1, 4]
def baseStart_2913832 : Nat := 118140960795 + 2913832 * 2 ^ 59
def prefixEnd_2913832 : Nat := 4983230072969 + 3 ^ 40 * 2913832 * 2
def baseEnd_2913832 : Nat := 498732120817249617533179

theorem tailTrace_2913832 : CollatzResearch.WordTrace tailWord_2913832 prefixEnd_2913832 498732120817249617533179 := by
  unfold tailWord_2913832
  simp only [CollatzResearch.WordTrace]
  refine ⟨53138091989845890865667875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70850789319794521154223833 53138091989845890865667875)
  ·
    refine ⟨79707137984768836298501813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53138091989845890865667875 79707137984768836298501813)
    ·
      refine ⟨7472544186072078402984545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 79707137984768836298501813 7472544186072078402984545)
      ·
        refine ⟨5604408139554058802238409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7472544186072078402984545 5604408139554058802238409)
        ·
          refine ⟨4203306104665544101678807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5604408139554058802238409 4203306104665544101678807)
          ·
            refine ⟨6304959156998316152518211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4203306104665544101678807 6304959156998316152518211)
            ·
              refine ⟨9457438735497474228777317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6304959156998316152518211 9457438735497474228777317)
              ·
                refine ⟨1773269762905776417895747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9457438735497474228777317 1773269762905776417895747)
                ·
                  refine ⟨2659904644358664626843621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1773269762905776417895747 2659904644358664626843621)
                  ·
                    refine ⟨498732120817249617533179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2659904644358664626843621 498732120817249617533179)
                    ·
                      rfl

theorem cell23_2913832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 4, 1, 4].length) (baseStart_2913832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2913832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2913832 prefixEnd_2913832 := by exact prefixLift 2913832
  have htrace : WordTrace (prefixWord ++ tailWord_2913832) baseStart_2913832 baseEnd_2913832 := by
    simpa [prefixWord, tailWord_2913832, baseEnd_2913832] using wordTrace_append hprefix tailTrace_2913832
  have hstable : (prefixWord ++ tailWord_2913832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2913832).length < 2 ^ (prefixWord ++ tailWord_2913832).sum := by decide
  have hdescent : baseEnd_2913832 < baseStart_2913832 := by decide
  rcases family_descends (prefixWord ++ tailWord_2913832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2913861 : List Nat := [1, 3, 1, 1, 1, 4, 1, 3, 3, 1, 4]
def baseStart_2913861 : Nat := 118140960795 + 2913861 * 2 ^ 59
def prefixEnd_2913861 : Nat := 4983230072969 + 3 ^ 40 * 2913861 * 2
def baseEnd_2913861 : Nat := 1496211253390729239136903

theorem tailTrace_2913861 : CollatzResearch.WordTrace tailWord_2913861 prefixEnd_2913861 1496211253390729239136903 := by
  unfold tailWord_2913861
  simp only [CollatzResearch.WordTrace]
  refine ⟨106277241696586719684141437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70851494464391146456094291 106277241696586719684141437)
  ·
    refine ⟨39853965636220019881553039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106277241696586719684141437 39853965636220019881553039)
    ·
      refine ⟨59780948454330029822329559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39853965636220019881553039 59780948454330029822329559)
      ·
        refine ⟨89671422681495044733494339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59780948454330029822329559 89671422681495044733494339)
        ·
          refine ⟨134507134022242567100241509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89671422681495044733494339 134507134022242567100241509)
          ·
            refine ⟨25220087629170481331295283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 134507134022242567100241509 25220087629170481331295283)
            ·
              refine ⟨37830131443755721996942925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25220087629170481331295283 37830131443755721996942925)
              ·
                refine ⟨14186299291408395748853597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37830131443755721996942925 14186299291408395748853597)
                ·
                  refine ⟨5319862234278148405820099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14186299291408395748853597 5319862234278148405820099)
                  ·
                    refine ⟨7979793351417222608730149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5319862234278148405820099 7979793351417222608730149)
                    ·
                      refine ⟨1496211253390729239136903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7979793351417222608730149 1496211253390729239136903)
                      ·
                        rfl

theorem cell23_2913861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 3, 3, 1, 4].length) (baseStart_2913861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2913861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2913861 prefixEnd_2913861 := by exact prefixLift 2913861
  have htrace : WordTrace (prefixWord ++ tailWord_2913861) baseStart_2913861 baseEnd_2913861 := by
    simpa [prefixWord, tailWord_2913861, baseEnd_2913861] using wordTrace_append hprefix tailTrace_2913861
  have hstable : (prefixWord ++ tailWord_2913861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2913861).length < 2 ^ (prefixWord ++ tailWord_2913861).sum := by decide
  have hdescent : baseEnd_2913861 < baseStart_2913861 := by decide
  rcases family_descends (prefixWord ++ tailWord_2913861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2913871 : List Nat := [1, 1, 2, 1, 1, 2, 3, 4, 4, 4]
def baseStart_2913871 : Nat := 118140960795 + 2913871 * 2 ^ 59
def prefixEnd_2913871 : Nat := 4983230072969 + 3 ^ 40 * 2913871 * 2
def baseEnd_2913871 : Nat := 498738796065758066670619

theorem tailTrace_2913871 : CollatzResearch.WordTrace tailWord_2913871 prefixEnd_2913871 498738796065758066670619 := by
  unfold tailWord_2913871
  simp only [CollatzResearch.WordTrace]
  refine ⟨106277606426550491392005467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70851737617700327594670311 106277606426550491392005467)
  ·
    refine ⟨159416409639825737088008201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106277606426550491392005467 159416409639825737088008201)
    ·
      refine ⟨119562307229869302816006151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159416409639825737088008201 119562307229869302816006151)
      ·
        refine ⟨179343460844803954224009227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119562307229869302816006151 179343460844803954224009227)
        ·
          refine ⟨269015191267205931336013841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179343460844803954224009227 269015191267205931336013841)
          ·
            refine ⟨201761393450404448502010381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 269015191267205931336013841 201761393450404448502010381)
            ·
              refine ⟨75660522543901668188253893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 201761393450404448502010381 75660522543901668188253893)
              ·
                refine ⟨14186347976981562785297605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 75660522543901668188253893 14186347976981562785297605)
                ·
                  refine ⟨2659940245684043022243301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14186347976981562785297605 2659940245684043022243301)
                  ·
                    refine ⟨498738796065758066670619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2659940245684043022243301 498738796065758066670619)
                    ·
                      rfl

theorem cell23_2913871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 4, 4, 4].length) (baseStart_2913871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2913871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2913871 prefixEnd_2913871 := by exact prefixLift 2913871
  have htrace : WordTrace (prefixWord ++ tailWord_2913871) baseStart_2913871 baseEnd_2913871 := by
    simpa [prefixWord, tailWord_2913871, baseEnd_2913871] using wordTrace_append hprefix tailTrace_2913871
  have hstable : (prefixWord ++ tailWord_2913871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2913871).length < 2 ^ (prefixWord ++ tailWord_2913871).sum := by decide
  have hdescent : baseEnd_2913871 < baseStart_2913871 := by decide
  rcases family_descends (prefixWord ++ tailWord_2913871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2913895 : List Nat := [1, 1, 5, 1, 1, 1, 3, 3, 3, 2, 2]
def baseStart_2913895 : Nat := 118140960795 + 2913895 * 2 ^ 59
def prefixEnd_2913895 : Nat := 4983230072969 + 3 ^ 40 * 2913895 * 2
def baseEnd_2913895 : Nat := 1496228711732982106111747

theorem tailTrace_2913895 : CollatzResearch.WordTrace tailWord_2913895 prefixEnd_2913895 1496228711732982106111747 := by
  unfold tailWord_2913895
  simp only [CollatzResearch.WordTrace]
  refine ⟨106278481778463543490879139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70852321185642362327252759 106278481778463543490879139)
  ·
    refine ⟨159417722667695315236318709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106278481778463543490879139 159417722667695315236318709)
    ·
      refine ⟨14945411500096435803404879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 159417722667695315236318709 14945411500096435803404879)
      ·
        refine ⟨22418117250144653705107319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14945411500096435803404879 22418117250144653705107319)
        ·
          refine ⟨33627175875216980557660979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22418117250144653705107319 33627175875216980557660979)
          ·
            refine ⟨50440763812825470836491469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33627175875216980557660979 50440763812825470836491469)
            ·
              refine ⟨18915286429809551563684301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50440763812825470836491469 18915286429809551563684301)
              ·
                refine ⟨7093232411178581836381613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18915286429809551563684301 7093232411178581836381613)
                ·
                  refine ⟨2659962154191968188643105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7093232411178581836381613 2659962154191968188643105)
                  ·
                    refine ⟨1994971615643976141482329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2659962154191968188643105 1994971615643976141482329)
                    ·
                      refine ⟨1496228711732982106111747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1994971615643976141482329 1496228711732982106111747)
                      ·
                        rfl

theorem cell23_2913895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 3, 3, 2, 2].length) (baseStart_2913895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2913895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2913895 prefixEnd_2913895 := by exact prefixLift 2913895
  have htrace : WordTrace (prefixWord ++ tailWord_2913895) baseStart_2913895 baseEnd_2913895 := by
    simpa [prefixWord, tailWord_2913895, baseEnd_2913895] using wordTrace_append hprefix tailTrace_2913895
  have hstable : (prefixWord ++ tailWord_2913895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2913895).length < 2 ^ (prefixWord ++ tailWord_2913895).sum := by decide
  have hdescent : baseEnd_2913895 < baseStart_2913895 := by decide
  rcases family_descends (prefixWord ++ tailWord_2913895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2913898 : List Nat := [3, 1, 3, 2, 1, 3, 1, 2, 1, 1, 5]
def baseStart_2913898 : Nat := 118140960795 + 2913898 * 2 ^ 59
def prefixEnd_2913898 : Nat := 4983230072969 + 3 ^ 40 * 2913898 * 2
def baseEnd_2913898 : Nat := 1496230252174945594374233

theorem tailTrace_2913898 : CollatzResearch.WordTrace tailWord_2913898 prefixEnd_2913898 1496230252174945594374233 := by
  unfold tailWord_2913898
  simp only [CollatzResearch.WordTrace]
  refine ⟨26569647799363168750809587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70852394131635116668825565 26569647799363168750809587)
  ·
    refine ⟨39854471699044753126214381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26569647799363168750809587 39854471699044753126214381)
    ·
      refine ⟨14945426887141782422330393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39854471699044753126214381 14945426887141782422330393)
      ·
        refine ⟨11209070165356336816747795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14945426887141782422330393 11209070165356336816747795)
        ·
          refine ⟨16813605248034505225121693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11209070165356336816747795 16813605248034505225121693)
          ·
            refine ⟨6305101968012939459420635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16813605248034505225121693 6305101968012939459420635)
            ·
              refine ⟨9457652952019409189130953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6305101968012939459420635 9457652952019409189130953)
              ·
                refine ⟨7093239714014556891848215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9457652952019409189130953 7093239714014556891848215)
                ·
                  refine ⟨10639859571021835337772323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7093239714014556891848215 10639859571021835337772323)
                  ·
                    refine ⟨15959789356532753006658485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10639859571021835337772323 15959789356532753006658485)
                    ·
                      refine ⟨1496230252174945594374233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15959789356532753006658485 1496230252174945594374233)
                      ·
                        rfl

theorem cell23_2913898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_2913898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2913898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2913898 prefixEnd_2913898 := by exact prefixLift 2913898
  have htrace : WordTrace (prefixWord ++ tailWord_2913898) baseStart_2913898 baseEnd_2913898 := by
    simpa [prefixWord, tailWord_2913898, baseEnd_2913898] using wordTrace_append hprefix tailTrace_2913898
  have hstable : (prefixWord ++ tailWord_2913898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2913898).length < 2 ^ (prefixWord ++ tailWord_2913898).sum := by decide
  have hdescent : baseEnd_2913898 < baseStart_2913898 := by decide
  rcases family_descends (prefixWord ++ tailWord_2913898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2913966 : List Nat := [4, 1, 4, 1, 3, 1, 1, 2, 1, 2, 3]
def baseStart_2913966 : Nat := 118140960795 + 2913966 * 2 ^ 59
def prefixEnd_2913966 : Nat := 4983230072969 + 3 ^ 40 * 2913966 * 2
def baseEnd_2913966 : Nat := 1496265168859451328323921

theorem tailTrace_2913966 : CollatzResearch.WordTrace tailWord_2913966 prefixEnd_2913966 1496265168859451328323921 := by
  unfold tailWord_2913966
  simp only [CollatzResearch.WordTrace]
  refine ⟨13285133920150790327089219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70854047574137548411142501 13285133920150790327089219)
  ·
    refine ⟨19927700880226185490633829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13285133920150790327089219 19927700880226185490633829)
    ·
      refine ⟨3736443915042409779493843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19927700880226185490633829 3736443915042409779493843)
      ·
        refine ⟨5604665872563614669240765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3736443915042409779493843 5604665872563614669240765)
        ·
          refine ⟨2101749702211355500965287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5604665872563614669240765 2101749702211355500965287)
          ·
            refine ⟨3152624553317033251447931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2101749702211355500965287 3152624553317033251447931)
            ·
              refine ⟨4728936829975549877171897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3152624553317033251447931 4728936829975549877171897)
              ·
                refine ⟨3546702622481662407878923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4728936829975549877171897 3546702622481662407878923)
                ·
                  refine ⟨5320053933722493611818385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3546702622481662407878923 5320053933722493611818385)
                  ·
                    refine ⟨3990040450291870208863789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5320053933722493611818385 3990040450291870208863789)
                    ·
                      refine ⟨1496265168859451328323921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3990040450291870208863789 1496265168859451328323921)
                      ·
                        rfl

theorem cell23_2913966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 1, 2, 1, 2, 3].length) (baseStart_2913966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2913966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2913966 prefixEnd_2913966 := by exact prefixLift 2913966
  have htrace : WordTrace (prefixWord ++ tailWord_2913966) baseStart_2913966 baseEnd_2913966 := by
    simpa [prefixWord, tailWord_2913966, baseEnd_2913966] using wordTrace_append hprefix tailTrace_2913966
  have hstable : (prefixWord ++ tailWord_2913966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2913966).length < 2 ^ (prefixWord ++ tailWord_2913966).sum := by decide
  have hdescent : baseEnd_2913966 < baseStart_2913966 := by decide
  rcases family_descends (prefixWord ++ tailWord_2913966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2913971 : List Nat := [1, 1, 1, 2, 3, 3, 1, 1, 4, 1, 5]
def baseStart_2913971 : Nat := 118140960795 + 2913971 * 2 ^ 59
def prefixEnd_2913971 : Nat := 4983230072969 + 3 ^ 40 * 2913971 * 2
def baseEnd_2913971 : Nat := 1496267736262723808761397

theorem tailTrace_2913971 : CollatzResearch.WordTrace tailWord_2913971 prefixEnd_2913971 1496267736262723808761397 := by
  unfold tailWord_2913971
  simp only [CollatzResearch.WordTrace]
  refine ⟨106281253726188208470645767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70854169150792138980430511 106281253726188208470645767)
  ·
    refine ⟨159421880589282312705968651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106281253726188208470645767 159421880589282312705968651)
    ·
      refine ⟨239132820883923469058952977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159421880589282312705968651 239132820883923469058952977)
      ·
        refine ⟨179349615662942601794214733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 239132820883923469058952977 179349615662942601794214733)
        ·
          refine ⟨67256105873603475672830525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 179349615662942601794214733 67256105873603475672830525)
          ·
            refine ⟨25221039702601303377311447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67256105873603475672830525 25221039702601303377311447)
            ·
              refine ⟨37831559553901955065967171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25221039702601303377311447 37831559553901955065967171)
              ·
                refine ⟨56747339330852932598950757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37831559553901955065967171 56747339330852932598950757)
                ·
                  refine ⟨10640126124534924862303267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56747339330852932598950757 10640126124534924862303267)
                  ·
                    refine ⟨15960189186802387293454901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10640126124534924862303267 15960189186802387293454901)
                    ·
                      refine ⟨1496267736262723808761397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15960189186802387293454901 1496267736262723808761397)
                      ·
                        rfl

theorem cell23_2913971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 1, 4, 1, 5].length) (baseStart_2913971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2913971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2913971 prefixEnd_2913971 := by exact prefixLift 2913971
  have htrace : WordTrace (prefixWord ++ tailWord_2913971) baseStart_2913971 baseEnd_2913971 := by
    simpa [prefixWord, tailWord_2913971, baseEnd_2913971] using wordTrace_append hprefix tailTrace_2913971
  have hstable : (prefixWord ++ tailWord_2913971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2913971).length < 2 ^ (prefixWord ++ tailWord_2913971).sum := by decide
  have hdescent : baseEnd_2913971 < baseStart_2913971 := by decide
  rcases family_descends (prefixWord ++ tailWord_2913971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2913988 : List Nat := [2, 3, 3, 1, 1, 1, 1, 3, 2, 1, 5]
def baseStart_2913988 : Nat := 118140960795 + 2913988 * 2 ^ 59
def prefixEnd_2913988 : Nat := 4983230072969 + 3 ^ 40 * 2913988 * 2
def baseEnd_2913988 : Nat := 1496276465433850242248819

theorem tailTrace_2913988 : CollatzResearch.WordTrace tailWord_2913988 prefixEnd_2913988 1496276465433850242248819 := by
  unfold tailWord_2913988
  simp only [CollatzResearch.WordTrace]
  refine ⟨53140936883563310187007309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70854582511417746916009745 53140936883563310187007309)
  ·
    refine ⟨19927851331336241320127741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53140936883563310187007309 19927851331336241320127741)
    ·
      refine ⟨7472944249251090495047903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19927851331336241320127741 7472944249251090495047903)
      ·
        refine ⟨11209416373876635742571855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7472944249251090495047903 11209416373876635742571855)
        ·
          refine ⟨16814124560814953613857783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11209416373876635742571855 16814124560814953613857783)
          ·
            refine ⟨25221186841222430420786675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16814124560814953613857783 25221186841222430420786675)
            ·
              refine ⟨37831780261833645631180013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25221186841222430420786675 37831780261833645631180013)
              ·
                refine ⟨14186917598187617111692505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37831780261833645631180013 14186917598187617111692505)
                ·
                  refine ⟨10640188198640712833769379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14186917598187617111692505 10640188198640712833769379)
                  ·
                    refine ⟨15960282297961069250654069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10640188198640712833769379 15960282297961069250654069)
                    ·
                      refine ⟨1496276465433850242248819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15960282297961069250654069 1496276465433850242248819)
                      ·
                        rfl

theorem cell23_2913988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_2913988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2913988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2913988 prefixEnd_2913988 := by exact prefixLift 2913988
  have htrace : WordTrace (prefixWord ++ tailWord_2913988) baseStart_2913988 baseEnd_2913988 := by
    simpa [prefixWord, tailWord_2913988, baseEnd_2913988] using wordTrace_append hprefix tailTrace_2913988
  have hstable : (prefixWord ++ tailWord_2913988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2913988).length < 2 ^ (prefixWord ++ tailWord_2913988).sum := by decide
  have hdescent : baseEnd_2913988 < baseStart_2913988 := by decide
  rcases family_descends (prefixWord ++ tailWord_2913988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2913998 : List Nat := [4, 1, 1, 1, 3, 1, 2, 2, 2, 2, 4]
def baseStart_2913998 : Nat := 118140960795 + 2913998 * 2 ^ 59
def prefixEnd_2913998 : Nat := 4983230072969 + 3 ^ 40 * 2913998 * 2
def baseEnd_2913998 : Nat := 1496281600240395203123773

theorem tailTrace_2913998 : CollatzResearch.WordTrace tailWord_2913998 prefixEnd_2913998 1496281600240395203123773 := by
  unfold tailWord_2913998
  simp only [CollatzResearch.WordTrace]
  refine ⟨13285279812136299010234831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70854825664726928054585765 13285279812136299010234831)
  ·
    refine ⟨19927919718204448515352247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13285279812136299010234831 19927919718204448515352247)
    ·
      refine ⟨29891879577306672773028371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19927919718204448515352247 29891879577306672773028371)
      ·
        refine ⟨44837819365960009159542557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29891879577306672773028371 44837819365960009159542557)
        ·
          refine ⟨16814182262235003434828459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44837819365960009159542557 16814182262235003434828459)
          ·
            refine ⟨25221273393352505152242689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16814182262235003434828459 25221273393352505152242689)
            ·
              refine ⟨18915955045014378864182017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25221273393352505152242689 18915955045014378864182017)
              ·
                refine ⟨14186966283760784148136513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18915955045014378864182017 14186966283760784148136513)
                ·
                  refine ⟨10640224712820588111102385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14186966283760784148136513 10640224712820588111102385)
                  ·
                    refine ⟨7980168534615441083326789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10640224712820588111102385 7980168534615441083326789)
                    ·
                      refine ⟨1496281600240395203123773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7980168534615441083326789 1496281600240395203123773)
                      ·
                        rfl

theorem cell23_2913998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 2, 2, 2, 4].length) (baseStart_2913998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2913998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2913998 prefixEnd_2913998 := by exact prefixLift 2913998
  have htrace : WordTrace (prefixWord ++ tailWord_2913998) baseStart_2913998 baseEnd_2913998 := by
    simpa [prefixWord, tailWord_2913998, baseEnd_2913998] using wordTrace_append hprefix tailTrace_2913998
  have hstable : (prefixWord ++ tailWord_2913998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2913998).length < 2 ^ (prefixWord ++ tailWord_2913998).sum := by decide
  have hdescent : baseEnd_2913998 < baseStart_2913998 := by decide
  rcases family_descends (prefixWord ++ tailWord_2913998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2914085 : List Nat := [1, 3, 1, 2, 3, 2, 2, 2, 3, 4]
def baseStart_2914085 : Nat := 118140960795 + 2914085 * 2 ^ 59
def prefixEnd_2914085 : Nat := 4983230072969 + 3 ^ 40 * 2914085 * 2
def baseEnd_2914085 : Nat := 498775424352445454245291

theorem tailTrace_2914085 : CollatzResearch.WordTrace tailWord_2914085 prefixEnd_2914085 498775424352445454245291 := by
  unfold tailWord_2914085
  simp only [CollatzResearch.WordTrace]
  refine ⟨106285411647775205940295709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70856941098516803960197139 106285411647775205940295709)
  ·
    refine ⟨39857029367915702227610891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106285411647775205940295709 39857029367915702227610891)
    ·
      refine ⟨59785544051873553341416337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39857029367915702227610891 59785544051873553341416337)
      ·
        refine ⟨44839158038905165006062253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59785544051873553341416337 44839158038905165006062253)
        ·
          refine ⟨16814684264589436877273345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44839158038905165006062253 16814684264589436877273345)
          ·
            refine ⟨12611013198442077657955009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16814684264589436877273345 12611013198442077657955009)
            ·
              refine ⟨9458259898831558243466257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12611013198442077657955009 9458259898831558243466257)
              ·
                refine ⟨7093694924123668682599693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9458259898831558243466257 7093694924123668682599693)
                ·
                  refine ⟨2660135596546375755974885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7093694924123668682599693 2660135596546375755974885)
                  ·
                    refine ⟨498775424352445454245291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2660135596546375755974885 498775424352445454245291)
                    ·
                      rfl

theorem cell23_2914085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 2, 3, 4].length) (baseStart_2914085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2914085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2914085 prefixEnd_2914085 := by exact prefixLift 2914085
  have htrace : WordTrace (prefixWord ++ tailWord_2914085) baseStart_2914085 baseEnd_2914085 := by
    simpa [prefixWord, tailWord_2914085, baseEnd_2914085] using wordTrace_append hprefix tailTrace_2914085
  have hstable : (prefixWord ++ tailWord_2914085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2914085).length < 2 ^ (prefixWord ++ tailWord_2914085).sum := by decide
  have hdescent : baseEnd_2914085 < baseStart_2914085 := by decide
  rcases family_descends (prefixWord ++ tailWord_2914085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2914098 : List Nat := [3, 2, 1, 1, 3, 2, 1, 2, 8]
def baseStart_2914098 : Nat := 118140960795 + 2914098 * 2 ^ 59
def prefixEnd_2914098 : Nat := 4983230072969 + 3 ^ 40 * 2914098 * 2
def baseEnd_2914098 : Nat := 166259216478427201319257

theorem tailTrace_2914098 : CollatzResearch.WordTrace tailWord_2914098 prefixEnd_2914098 166259216478427201319257 := by
  unfold tailWord_2914098
  simp only [CollatzResearch.WordTrace]
  refine ⟨26571471449182027290129737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70857257197818739440345965 26571471449182027290129737)
  ·
    refine ⟨19928603586886520467597303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26571471449182027290129737 19928603586886520467597303)
    ·
      refine ⟨29892905380329780701395955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19928603586886520467597303 29892905380329780701395955)
      ·
        refine ⟨44839358070494671052093933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29892905380329780701395955 44839358070494671052093933)
        ·
          refine ⟨16814759276435501644535225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44839358070494671052093933 16814759276435501644535225)
          ·
            refine ⟨12611069457326626233401419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16814759276435501644535225 12611069457326626233401419)
            ·
              refine ⟨18916604185989939350102129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12611069457326626233401419 18916604185989939350102129)
              ·
                refine ⟨14187453139492454512576597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18916604185989939350102129 14187453139492454512576597)
                ·
                  refine ⟨166259216478427201319257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14187453139492454512576597 166259216478427201319257)
                  ·
                    rfl

theorem cell23_2914098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 2, 8].length) (baseStart_2914098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2914098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2914098 prefixEnd_2914098 := by exact prefixLift 2914098
  have htrace : WordTrace (prefixWord ++ tailWord_2914098) baseStart_2914098 baseEnd_2914098 := by
    simpa [prefixWord, tailWord_2914098, baseEnd_2914098] using wordTrace_append hprefix tailTrace_2914098
  have hstable : (prefixWord ++ tailWord_2914098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2914098).length < 2 ^ (prefixWord ++ tailWord_2914098).sum := by decide
  have hdescent : baseEnd_2914098 < baseStart_2914098 := by decide
  rcases family_descends (prefixWord ++ tailWord_2914098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2914128 : List Nat := [2, 1, 1, 1, 1, 4, 1, 4, 3, 5]
def baseStart_2914128 : Nat := 118140960795 + 2914128 * 2 ^ 59
def prefixEnd_2914128 : Nat := 4983230072969 + 3 ^ 40 * 2914128 * 2
def baseEnd_2914128 : Nat := 498782784241826564832725

theorem tailTrace_2914128 : CollatzResearch.WordTrace tailWord_2914128 prefixEnd_2914128 498782784241826564832725 := by
  unfold tailWord_2914128
  simp only [CollatzResearch.WordTrace]
  refine ⟨53143489993309712142055519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70857986657746282856074025 53143489993309712142055519)
  ·
    refine ⟨79715234989964568213083279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53143489993309712142055519 79715234989964568213083279)
    ·
      refine ⟨119572852484946852319624919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79715234989964568213083279 119572852484946852319624919)
      ·
        refine ⟨179359278727420278479437379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119572852484946852319624919 179359278727420278479437379)
        ·
          refine ⟨269038918091130417719156069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179359278727420278479437379 269038918091130417719156069)
          ·
            refine ⟨50444797142086953322341763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 269038918091130417719156069 50444797142086953322341763)
            ·
              refine ⟨75667195713130429983512645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50444797142086953322341763 75667195713130429983512645)
              ·
                refine ⟨14187599196211955621908621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 75667195713130429983512645 14187599196211955621908621)
                ·
                  refine ⟨5320349698579483358215733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14187599196211955621908621 5320349698579483358215733)
                  ·
                    refine ⟨498782784241826564832725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5320349698579483358215733 498782784241826564832725)
                    ·
                      rfl

theorem cell23_2914128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 4, 3, 5].length) (baseStart_2914128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2914128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2914128 prefixEnd_2914128 := by exact prefixLift 2914128
  have htrace : WordTrace (prefixWord ++ tailWord_2914128) baseStart_2914128 baseEnd_2914128 := by
    simpa [prefixWord, tailWord_2914128, baseEnd_2914128] using wordTrace_append hprefix tailTrace_2914128
  have hstable : (prefixWord ++ tailWord_2914128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2914128).length < 2 ^ (prefixWord ++ tailWord_2914128).sum := by decide
  have hdescent : baseEnd_2914128 < baseStart_2914128 := by decide
  rcases family_descends (prefixWord ++ tailWord_2914128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2914132 : List Nat := [2, 4, 1, 1, 3, 1, 4, 1, 6]
def baseStart_2914132 : Nat := 118140960795 + 2914132 * 2 ^ 59
def prefixEnd_2914132 : Nat := 4983230072969 + 3 ^ 40 * 2914132 * 2
def baseEnd_2914132 : Nat := 166261156294233075427573

theorem tailTrace_2914132 : CollatzResearch.WordTrace tailWord_2914132 prefixEnd_2914132 166261156294233075427573 := by
  unfold tailWord_2914132
  simp only [CollatzResearch.WordTrace]
  refine ⟨53143562939302466483628325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70858083919069955311504433 53143562939302466483628325)
  ·
    refine ⟨9964418051119212465680311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53143562939302466483628325 9964418051119212465680311)
    ·
      refine ⟨14946627076678818698520467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9964418051119212465680311 14946627076678818698520467)
      ·
        refine ⟨22419940615018228047780701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14946627076678818698520467 22419940615018228047780701)
        ·
          refine ⟨8407477730631835517917763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22419940615018228047780701 8407477730631835517917763)
          ·
            refine ⟨12611216595947753276876645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8407477730631835517917763 12611216595947753276876645)
            ·
              refine ⟨2364603111740203739414371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12611216595947753276876645 2364603111740203739414371)
              ·
                refine ⟨3546904667610305609121557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2364603111740203739414371 3546904667610305609121557)
                ·
                  refine ⟨166261156294233075427573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3546904667610305609121557 166261156294233075427573)
                  ·
                    rfl

theorem cell23_2914132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 4, 1, 6].length) (baseStart_2914132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2914132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2914132 prefixEnd_2914132 := by exact prefixLift 2914132
  have htrace : WordTrace (prefixWord ++ tailWord_2914132) baseStart_2914132 baseEnd_2914132 := by
    simpa [prefixWord, tailWord_2914132, baseEnd_2914132] using wordTrace_append hprefix tailTrace_2914132
  have hstable : (prefixWord ++ tailWord_2914132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2914132).length < 2 ^ (prefixWord ++ tailWord_2914132).sum := by decide
  have hdescent : baseEnd_2914132 < baseStart_2914132 := by decide
  rcases family_descends (prefixWord ++ tailWord_2914132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2914185 : List Nat := [1, 2, 1, 1, 5, 1, 1, 1, 5, 2, 3]
def baseStart_2914185 : Nat := 118140960795 + 2914185 * 2 ^ 59
def prefixEnd_2914185 : Nat := 4983230072969 + 3 ^ 40 * 2914185 * 2
def baseEnd_2914185 : Nat := 1496377621122785971485413

theorem tailTrace_2914185 : CollatzResearch.WordTrace tailWord_2914185 prefixEnd_2914185 1496377621122785971485413 := by
  unfold tailWord_2914185
  simp only [CollatzResearch.WordTrace]
  refine ⟨106289058947412923018936009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70859372631608615345957339 106289058947412923018936009)
  ·
    refine ⟨79716794210559692264202007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106289058947412923018936009 79716794210559692264202007)
    ·
      refine ⟨119575191315839538396303011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79716794210559692264202007 119575191315839538396303011)
      ·
        refine ⟨179362786973759307594454517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119575191315839538396303011 179362786973759307594454517)
        ·
          refine ⟨16815261278789935086980111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 179362786973759307594454517 16815261278789935086980111)
          ·
            refine ⟨25222891918184902630470167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16815261278789935086980111 25222891918184902630470167)
            ·
              refine ⟨37834337877277353945705251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25222891918184902630470167 37834337877277353945705251)
              ·
                refine ⟨56751506815916030918557877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37834337877277353945705251 56751506815916030918557877)
                ·
                  refine ⟨5320453763992127898614801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 56751506815916030918557877 5320453763992127898614801)
                  ·
                    refine ⟨3990340322994095923961101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5320453763992127898614801 3990340322994095923961101)
                    ·
                      refine ⟨1496377621122785971485413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3990340322994095923961101 1496377621122785971485413)
                      ·
                        rfl

theorem cell23_2914185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 1, 5, 2, 3].length) (baseStart_2914185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2914185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2914185 prefixEnd_2914185 := by exact prefixLift 2914185
  have htrace : WordTrace (prefixWord ++ tailWord_2914185) baseStart_2914185 baseEnd_2914185 := by
    simpa [prefixWord, tailWord_2914185, baseEnd_2914185] using wordTrace_append hprefix tailTrace_2914185
  have hstable : (prefixWord ++ tailWord_2914185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2914185).length < 2 ^ (prefixWord ++ tailWord_2914185).sum := by decide
  have hdescent : baseEnd_2914185 < baseStart_2914185 := by decide
  rcases family_descends (prefixWord ++ tailWord_2914185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2914199 : List Nat := [1, 1, 3, 3, 1, 4, 1, 2, 3, 2, 2]
def baseStart_2914199 : Nat := 118140960795 + 2914199 * 2 ^ 59
def prefixEnd_2914199 : Nat := 4983230072969 + 3 ^ 40 * 2914199 * 2
def baseEnd_2914199 : Nat := 1496384809851948916710349

theorem tailTrace_2914199 : CollatzResearch.WordTrace tailWord_2914199 prefixEnd_2914199 1496384809851948916710349 := by
  unfold tailWord_2914199
  simp only [CollatzResearch.WordTrace]
  refine ⟨106289569569362203409945651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70859713046241468939963767 106289569569362203409945651)
  ·
    refine ⟨159434354354043305114918477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106289569569362203409945651 159434354354043305114918477)
    ·
      refine ⟨59787882882766239418094429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 159434354354043305114918477 59787882882766239418094429)
      ·
        refine ⟨22420456081037339781785411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59787882882766239418094429 22420456081037339781785411)
        ·
          refine ⟨33630684121556009672678117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22420456081037339781785411 33630684121556009672678117)
          ·
            refine ⟨6305753272791751813627147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33630684121556009672678117 6305753272791751813627147)
            ·
              refine ⟨9458629909187627720440721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6305753272791751813627147 9458629909187627720440721)
              ·
                refine ⟨7093972431890720790330541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9458629909187627720440721 7093972431890720790330541)
                ·
                  refine ⟨2660239661959020296373953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7093972431890720790330541 2660239661959020296373953)
                  ·
                    refine ⟨1995179746469265222280465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2660239661959020296373953 1995179746469265222280465)
                    ·
                      refine ⟨1496384809851948916710349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1995179746469265222280465 1496384809851948916710349)
                      ·
                        rfl

theorem cell23_2914199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 2, 3, 2, 2].length) (baseStart_2914199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2914199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2914199 prefixEnd_2914199 := by exact prefixLift 2914199
  have htrace : WordTrace (prefixWord ++ tailWord_2914199) baseStart_2914199 baseEnd_2914199 := by
    simpa [prefixWord, tailWord_2914199, baseEnd_2914199] using wordTrace_append hprefix tailTrace_2914199
  have hstable : (prefixWord ++ tailWord_2914199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2914199).length < 2 ^ (prefixWord ++ tailWord_2914199).sum := by decide
  have hdescent : baseEnd_2914199 < baseStart_2914199 := by decide
  rcases family_descends (prefixWord ++ tailWord_2914199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2914202 : List Nat := [3, 1, 1, 4, 2, 1, 2, 1, 3, 2, 3]
def baseStart_2914202 : Nat := 118140960795 + 2914202 * 2 ^ 59
def prefixEnd_2914202 : Nat := 4983230072969 + 3 ^ 40 * 2914202 * 2
def baseEnd_2914202 : Nat := 1496386350293912404972835

theorem tailTrace_2914202 : CollatzResearch.WordTrace tailWord_2914202 prefixEnd_2914202 1496386350293912404972835 := by
  unfold tailWord_2914202
  simp only [CollatzResearch.WordTrace]
  refine ⟨26572419747087833730576215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70859785992234223281536573 26572419747087833730576215)
  ·
    refine ⟨39858629620631750595864323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26572419747087833730576215 39858629620631750595864323)
    ·
      refine ⟨59787944430947625893796485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39858629620631750595864323 59787944430947625893796485)
      ·
        refine ⟨11210239580802679855086841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59787944430947625893796485 11210239580802679855086841)
        ·
          refine ⟨8407679685602009891315131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11210239580802679855086841 8407679685602009891315131)
          ·
            refine ⟨12611519528403014836972697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8407679685602009891315131 12611519528403014836972697)
            ·
              refine ⟨9458639646302261127729523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12611519528403014836972697 9458639646302261127729523)
              ·
                refine ⟨14187959469453391691594285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9458639646302261127729523 14187959469453391691594285)
                ·
                  refine ⟨5320484801045021884347857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14187959469453391691594285 5320484801045021884347857)
                  ·
                    refine ⟨3990363600783766413260893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5320484801045021884347857 3990363600783766413260893)
                    ·
                      refine ⟨1496386350293912404972835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3990363600783766413260893 1496386350293912404972835)
                      ·
                        rfl

theorem cell23_2914202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 1, 3, 2, 3].length) (baseStart_2914202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2914202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2914202 prefixEnd_2914202 := by exact prefixLift 2914202
  have htrace : WordTrace (prefixWord ++ tailWord_2914202) baseStart_2914202 baseEnd_2914202 := by
    simpa [prefixWord, tailWord_2914202, baseEnd_2914202] using wordTrace_append hprefix tailTrace_2914202
  have hstable : (prefixWord ++ tailWord_2914202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2914202).length < 2 ^ (prefixWord ++ tailWord_2914202).sum := by decide
  have hdescent : baseEnd_2914202 < baseStart_2914202 := by decide
  rcases family_descends (prefixWord ++ tailWord_2914202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2914216 : List Nat := [2, 1, 6, 2, 1, 1, 1, 3, 1, 1, 4]
def baseStart_2914216 : Nat := 118140960795 + 2914216 * 2 ^ 59
def prefixEnd_2914216 : Nat := 4983230072969 + 3 ^ 40 * 2914216 * 2
def baseEnd_2914216 : Nat := 1496393539023075350197771

theorem tailTrace_2914216 : CollatzResearch.WordTrace tailWord_2914216 prefixEnd_2914216 1496393539023075350197771 := by
  unfold tailWord_2914216
  simp only [CollatzResearch.WordTrace]
  refine ⟨53145094805150307656657251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70860126406867076875543001 53145094805150307656657251)
  ·
    refine ⟨79717642207725461484985877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53145094805150307656657251 79717642207725461484985877)
    ·
      refine ⟨3736764478487131007108713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 79717642207725461484985877 3736764478487131007108713)
      ·
        refine ⟨2802573358865348255331535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3736764478487131007108713 2802573358865348255331535)
        ·
          refine ⟨4203860038298022382997303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2802573358865348255331535 4203860038298022382997303)
          ·
            refine ⟨6305790057447033574495955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4203860038298022382997303 6305790057447033574495955)
            ·
              refine ⟨9458685086170550361743933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6305790057447033574495955 9458685086170550361743933)
              ·
                refine ⟨3547006907313956385653975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9458685086170550361743933 3547006907313956385653975)
                ·
                  refine ⟨5320510360970934578480963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3547006907313956385653975 5320510360970934578480963)
                  ·
                    refine ⟨7980765541456401867721445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5320510360970934578480963 7980765541456401867721445)
                    ·
                      refine ⟨1496393539023075350197771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7980765541456401867721445 1496393539023075350197771)
                      ·
                        rfl

theorem cell23_2914216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_2914216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2914216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2914216 prefixEnd_2914216 := by exact prefixLift 2914216
  have htrace : WordTrace (prefixWord ++ tailWord_2914216) baseStart_2914216 baseEnd_2914216 := by
    simpa [prefixWord, tailWord_2914216, baseEnd_2914216] using wordTrace_append hprefix tailTrace_2914216
  have hstable : (prefixWord ++ tailWord_2914216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2914216).length < 2 ^ (prefixWord ++ tailWord_2914216).sum := by decide
  have hdescent : baseEnd_2914216 < baseStart_2914216 := by decide
  rcases family_descends (prefixWord ++ tailWord_2914216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2914232 : List Nat := [2, 1, 2, 1, 2, 3, 3, 1, 4, 1, 3]
def baseStart_2914232 : Nat := 118140960795 + 2914232 * 2 ^ 59
def prefixEnd_2914232 : Nat := 4983230072969 + 3 ^ 40 * 2914232 * 2
def baseEnd_2914232 : Nat := 1496401754713547287597697

theorem tailTrace_2914232 : CollatzResearch.WordTrace tailWord_2914232 prefixEnd_2914232 1496401754713547287597697 := by
  unfold tailWord_2914232
  simp only [CollatzResearch.WordTrace]
  refine ⟨53145386589121325022948475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70860515452161766697264633 53145386589121325022948475)
  ·
    refine ⟨79718079883681987534422713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53145386589121325022948475 79718079883681987534422713)
    ·
      refine ⟨59788559912761490650817035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79718079883681987534422713 59788559912761490650817035)
      ·
        refine ⟨89682839869142235976225553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59788559912761490650817035 89682839869142235976225553)
        ·
          refine ⟨67262129901856676982169165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89682839869142235976225553 67262129901856676982169165)
          ·
            refine ⟨25223298713196253868313437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67262129901856676982169165 25223298713196253868313437)
            ·
              refine ⟨9458737017448595200617539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25223298713196253868313437 9458737017448595200617539)
              ·
                refine ⟨14188105526172892800926309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9458737017448595200617539 14188105526172892800926309)
                ·
                  refine ⟨2660269786157417400173683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14188105526172892800926309 2660269786157417400173683)
                  ·
                    refine ⟨3990404679236126100260525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2660269786157417400173683 3990404679236126100260525)
                    ·
                      refine ⟨1496401754713547287597697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3990404679236126100260525 1496401754713547287597697)
                      ·
                        rfl

theorem cell23_2914232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 1, 4, 1, 3].length) (baseStart_2914232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2914232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2914232 prefixEnd_2914232 := by exact prefixLift 2914232
  have htrace : WordTrace (prefixWord ++ tailWord_2914232) baseStart_2914232 baseEnd_2914232 := by
    simpa [prefixWord, tailWord_2914232, baseEnd_2914232] using wordTrace_append hprefix tailTrace_2914232
  have hstable : (prefixWord ++ tailWord_2914232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2914232).length < 2 ^ (prefixWord ++ tailWord_2914232).sum := by decide
  have hdescent : baseEnd_2914232 < baseStart_2914232 := by decide
  rcases family_descends (prefixWord ++ tailWord_2914232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2914272 : List Nat := [2, 1, 1, 3, 1, 1, 1, 6, 1, 4, 2]
def baseStart_2914272 : Nat := 118140960795 + 2914272 * 2 ^ 59
def prefixEnd_2914272 : Nat := 4983230072969 + 3 ^ 40 * 2914272 * 2
def baseEnd_2914272 : Nat := 1496422293939727131097513

theorem tailTrace_2914272 : CollatzResearch.WordTrace tailWord_2914272 prefixEnd_2914272 1496422293939727131097513 := by
  unfold tailWord_2914272
  simp only [CollatzResearch.WordTrace]
  refine ⟨53146116049048868438676535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70861488065398491251568713 53146116049048868438676535)
  ·
    refine ⟨79719174073573302658014803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53146116049048868438676535 79719174073573302658014803)
    ·
      refine ⟨119578761110359953987022205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79719174073573302658014803 119578761110359953987022205)
      ·
        refine ⟨44842035416384982745133327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119578761110359953987022205 44842035416384982745133327)
        ·
          refine ⟨67263053124577474117699991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44842035416384982745133327 67263053124577474117699991)
          ·
            refine ⟨100894579686866211176549987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67263053124577474117699991 100894579686866211176549987)
            ·
              refine ⟨151341869530299316764824981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100894579686866211176549987 151341869530299316764824981)
              ·
                refine ⟨7094150134232780473351171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 151341869530299316764824981 7094150134232780473351171)
                ·
                  refine ⟨10641225201349170710026757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7094150134232780473351171 10641225201349170710026757)
                  ·
                    refine ⟨1995229725252969508130017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10641225201349170710026757 1995229725252969508130017)
                    ·
                      refine ⟨1496422293939727131097513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1995229725252969508130017 1496422293939727131097513)
                      ·
                        rfl

theorem cell23_2914272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 6, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 6, 1, 4, 2].length) (baseStart_2914272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2914272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2914272 prefixEnd_2914272 := by exact prefixLift 2914272
  have htrace : WordTrace (prefixWord ++ tailWord_2914272) baseStart_2914272 baseEnd_2914272 := by
    simpa [prefixWord, tailWord_2914272, baseEnd_2914272] using wordTrace_append hprefix tailTrace_2914272
  have hstable : (prefixWord ++ tailWord_2914272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2914272).length < 2 ^ (prefixWord ++ tailWord_2914272).sum := by decide
  have hdescent : baseEnd_2914272 < baseStart_2914272 := by decide
  rcases family_descends (prefixWord ++ tailWord_2914272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2914275 : List Nat := [1, 1, 1, 6, 1, 2, 1, 1, 1, 3, 5]
def baseStart_2914275 : Nat := 118140960795 + 2914275 * 2 ^ 59
def prefixEnd_2914275 : Nat := 4983230072969 + 3 ^ 40 * 2914275 * 2
def baseEnd_2914275 : Nat := 1496423834381690619359999

theorem tailTrace_2914275 : CollatzResearch.WordTrace tailWord_2914275 prefixEnd_2914275 1496423834381690619359999 := by
  unfold tailWord_2914275
  simp only [CollatzResearch.WordTrace]
  refine ⟨106292341517086868389712279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70861561011391245593141519 106292341517086868389712279)
  ·
    refine ⟨159438512275630302584568419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106292341517086868389712279 159438512275630302584568419)
    ·
      refine ⟨239157768413445453876852629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159438512275630302584568419 239157768413445453876852629)
      ·
        refine ⟨11210520394380255650477467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 239157768413445453876852629 11210520394380255650477467)
        ·
          refine ⟨16815780591570383475716201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11210520394380255650477467 16815780591570383475716201)
          ·
            refine ⟨12611835443677787606787151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16815780591570383475716201 12611835443677787606787151)
            ·
              refine ⟨18917753165516681410180727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12611835443677787606787151 18917753165516681410180727)
              ·
                refine ⟨28376629748275022115271091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18917753165516681410180727 28376629748275022115271091)
                ·
                  refine ⟨42564944622412533172906637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28376629748275022115271091 42564944622412533172906637)
                  ·
                    refine ⟨15961854233404699939839989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42564944622412533172906637 15961854233404699939839989)
                    ·
                      refine ⟨1496423834381690619359999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15961854233404699939839989 1496423834381690619359999)
                      ·
                        rfl

theorem cell23_2914275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_2914275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2914275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2914275 prefixEnd_2914275 := by exact prefixLift 2914275
  have htrace : WordTrace (prefixWord ++ tailWord_2914275) baseStart_2914275 baseEnd_2914275 := by
    simpa [prefixWord, tailWord_2914275, baseEnd_2914275] using wordTrace_append hprefix tailTrace_2914275
  have hstable : (prefixWord ++ tailWord_2914275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2914275).length < 2 ^ (prefixWord ++ tailWord_2914275).sum := by decide
  have hdescent : baseEnd_2914275 < baseStart_2914275 := by decide
  rcases family_descends (prefixWord ++ tailWord_2914275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2914335 : List Nat := [1, 1, 2, 4, 1, 2, 1, 1, 3, 2, 5]
def baseStart_2914335 : Nat := 118140960795 + 2914335 * 2 ^ 59
def prefixEnd_2914335 : Nat := 4983230072969 + 3 ^ 40 * 2914335 * 2
def baseEnd_2914335 : Nat := 1496454643220960384609723

theorem tailTrace_2914335 : CollatzResearch.WordTrace tailWord_2914335 prefixEnd_2914335 1496454643220960384609723 := by
  unfold tailWord_2914335
  simp only [CollatzResearch.WordTrace]
  refine ⟨106294529896869498636896459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70863019931246332424597639 106294529896869498636896459)
  ·
    refine ⟨159441794845304247955344689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106294529896869498636896459 159441794845304247955344689)
    ·
      refine ⟨119581346133978185966508517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159441794845304247955344689 119581346133978185966508517)
      ·
        refine ⟨22421502400120909868720347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 119581346133978185966508517 22421502400120909868720347)
        ·
          refine ⟨33632253600181364803080521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22421502400120909868720347 33632253600181364803080521)
          ·
            refine ⟨25224190200136023602310391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33632253600181364803080521 25224190200136023602310391)
            ·
              refine ⟨37836285300204035403465587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25224190200136023602310391 37836285300204035403465587)
              ·
                refine ⟨56754427950306053105198381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37836285300204035403465587 56754427950306053105198381)
                ·
                  refine ⟨21282910481364769914449393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56754427950306053105198381 21282910481364769914449393)
                  ·
                    refine ⟨15962182861023577435837045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21282910481364769914449393 15962182861023577435837045)
                    ·
                      refine ⟨1496454643220960384609723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15962182861023577435837045 1496454643220960384609723)
                      ·
                        rfl

theorem cell23_2914335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 1, 3, 2, 5].length) (baseStart_2914335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2914335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2914335 prefixEnd_2914335 := by exact prefixLift 2914335
  have htrace : WordTrace (prefixWord ++ tailWord_2914335) baseStart_2914335 baseEnd_2914335 := by
    simpa [prefixWord, tailWord_2914335, baseEnd_2914335] using wordTrace_append hprefix tailTrace_2914335
  have hstable : (prefixWord ++ tailWord_2914335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2914335).length < 2 ^ (prefixWord ++ tailWord_2914335).sum := by decide
  have hdescent : baseEnd_2914335 < baseStart_2914335 := by decide
  rcases family_descends (prefixWord ++ tailWord_2914335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2914346 : List Nat := [3, 1, 4, 1, 2, 1, 4, 2, 5]
def baseStart_2914346 : Nat := 118140960795 + 2914346 * 2 ^ 59
def prefixEnd_2914346 : Nat := 4983230072969 + 3 ^ 40 * 2914346 * 2
def baseEnd_2914346 : Nat := 166273365723128871285797

theorem tailTrace_2914346 : CollatzResearch.WordTrace tailWord_2914346 prefixEnd_2914346 166273365723128871285797 := by
  unfold tailWord_2914346
  simp only [CollatzResearch.WordTrace]
  refine ⟨26573732774957411878886723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70863287399886431677031261 26573732774957411878886723)
  ·
    refine ⟨39860599162436117818330085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26573732774957411878886723 39860599162436117818330085)
    ·
      refine ⟨7473862342956772090936891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39860599162436117818330085 7473862342956772090936891)
      ·
        refine ⟨11210793514435158136405337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7473862342956772090936891 11210793514435158136405337)
        ·
          refine ⟨8408095135826368602304003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11210793514435158136405337 8408095135826368602304003)
          ·
            refine ⟨12612142703739552903456005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8408095135826368602304003 12612142703739552903456005)
            ·
              refine ⟨2364776756951166169398001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12612142703739552903456005 2364776756951166169398001)
              ·
                refine ⟨1773582567713374627048501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2364776756951166169398001 1773582567713374627048501)
                ·
                  refine ⟨166273365723128871285797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1773582567713374627048501 166273365723128871285797)
                  ·
                    rfl

theorem cell23_2914346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 4, 2, 5].length) (baseStart_2914346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2914346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2914346 prefixEnd_2914346 := by exact prefixLift 2914346
  have htrace : WordTrace (prefixWord ++ tailWord_2914346) baseStart_2914346 baseEnd_2914346 := by
    simpa [prefixWord, tailWord_2914346, baseEnd_2914346] using wordTrace_append hprefix tailTrace_2914346
  have hstable : (prefixWord ++ tailWord_2914346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2914346).length < 2 ^ (prefixWord ++ tailWord_2914346).sum := by decide
  have hdescent : baseEnd_2914346 < baseStart_2914346 := by decide
  rcases family_descends (prefixWord ++ tailWord_2914346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2914356 : List Nat := [2, 5, 1, 2, 2, 1, 1, 1, 2, 3, 3]
def baseStart_2914356 : Nat := 118140960795 + 2914356 * 2 ^ 59
def prefixEnd_2914356 : Nat := 4983230072969 + 3 ^ 40 * 2914356 * 2
def baseEnd_2914356 : Nat := 1496465426314704802447127

theorem tailTrace_2914356 : CollatzResearch.WordTrace tailWord_2914356 prefixEnd_2914356 1496465426314704802447127 := by
  unfold tailWord_2914356
  simp only [CollatzResearch.WordTrace]
  refine ⟨53147647914896709611705461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70863530553195612815607281 53147647914896709611705461)
  ·
    refine ⟨4982591992021566526097387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 53147647914896709611705461 4982591992021566526097387)
    ·
      refine ⟨7473887988032349789146081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4982591992021566526097387 7473887988032349789146081)
      ·
        refine ⟨5605415991024262341859561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7473887988032349789146081 5605415991024262341859561)
        ·
          refine ⟨4204061993268196756394671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5605415991024262341859561 4204061993268196756394671)
          ·
            refine ⟨6306092989902295134592007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4204061993268196756394671 6306092989902295134592007)
            ·
              refine ⟨9459139484853442701888011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6306092989902295134592007 9459139484853442701888011)
              ·
                refine ⟨14188709227280164052832017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9459139484853442701888011 14188709227280164052832017)
                ·
                  refine ⟨10641531920460123039624013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14188709227280164052832017 10641531920460123039624013)
                  ·
                    refine ⟨3990574470172546139859005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10641531920460123039624013 3990574470172546139859005)
                    ·
                      refine ⟨1496465426314704802447127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3990574470172546139859005 1496465426314704802447127)
                      ·
                        rfl

theorem cell23_2914356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_2914356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2914356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2914356 prefixEnd_2914356 := by exact prefixLift 2914356
  have htrace : WordTrace (prefixWord ++ tailWord_2914356) baseStart_2914356 baseEnd_2914356 := by
    simpa [prefixWord, tailWord_2914356, baseEnd_2914356] using wordTrace_append hprefix tailTrace_2914356
  have hstable : (prefixWord ++ tailWord_2914356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2914356).length < 2 ^ (prefixWord ++ tailWord_2914356).sum := by decide
  have hdescent : baseEnd_2914356 < baseStart_2914356 := by decide
  rcases family_descends (prefixWord ++ tailWord_2914356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2914385 : List Nat := [1, 2, 2, 1, 3, 1, 1, 4, 8]
def baseStart_2914385 : Nat := 118140960795 + 2914385 * 2 ^ 59
def prefixEnd_2914385 : Nat := 4983230072969 + 3 ^ 40 * 2914385 * 2
def baseEnd_2914385 : Nat := 166275590805965020998277

theorem tailTrace_2914385 : CollatzResearch.WordTrace tailWord_2914385 prefixEnd_2914385 166275590805965020998277 := by
  unfold tailWord_2914385
  simp only [CollatzResearch.WordTrace]
  refine ⟨106296353546688357176216609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70864235697792238117477739 106296353546688357176216609)
  ·
    refine ⟨79722265160016267882162457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106296353546688357176216609 79722265160016267882162457)
    ·
      refine ⟨59791698870012200911621843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79722265160016267882162457 59791698870012200911621843)
      ·
        refine ⟨89687548305018301367432765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59791698870012200911621843 89687548305018301367432765)
        ·
          refine ⟨33632830614381863012787287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89687548305018301367432765 33632830614381863012787287)
          ·
            refine ⟨50449245921572794519180931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33632830614381863012787287 50449245921572794519180931)
            ·
              refine ⟨75673868882359191778771397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50449245921572794519180931 75673868882359191778771397)
              ·
                refine ⟨14188850415442348458519637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 75673868882359191778771397 14188850415442348458519637)
                ·
                  refine ⟨166275590805965020998277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14188850415442348458519637 166275590805965020998277)
                  ·
                    rfl

theorem cell23_2914385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 4, 8].length) (baseStart_2914385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2914385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2914385 prefixEnd_2914385 := by exact prefixLift 2914385
  have htrace : WordTrace (prefixWord ++ tailWord_2914385) baseStart_2914385 baseEnd_2914385 := by
    simpa [prefixWord, tailWord_2914385, baseEnd_2914385] using wordTrace_append hprefix tailTrace_2914385
  have hstable : (prefixWord ++ tailWord_2914385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2914385).length < 2 ^ (prefixWord ++ tailWord_2914385).sum := by decide
  have hdescent : baseEnd_2914385 < baseStart_2914385 := by decide
  rcases family_descends (prefixWord ++ tailWord_2914385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2914439 : List Nat := [1, 1, 4, 2, 1, 1, 4, 1, 1, 5, 2]
def baseStart_2914439 : Nat := 118140960795 + 2914439 * 2 ^ 59
def prefixEnd_2914439 : Nat := 4983230072969 + 3 ^ 40 * 2914439 * 2
def baseEnd_2914439 : Nat := 1496508045209027977709245

theorem tailTrace_2914439 : CollatzResearch.WordTrace tailWord_2914439 prefixEnd_2914439 1496508045209027977709245 := by
  unfold tailWord_2914439
  simp only [CollatzResearch.WordTrace]
  refine ⟨106298323088492724398682371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70865548725661816265788247 106298323088492724398682371)
  ·
    refine ⟨159447484632739086598023557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106298323088492724398682371 159447484632739086598023557)
    ·
      refine ⟨29896403368638578737129417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 159447484632739086598023557 29896403368638578737129417)
      ·
        refine ⟨22422302526478934052847063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29896403368638578737129417 22422302526478934052847063)
        ·
          refine ⟨33633453789718401079270595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22422302526478934052847063 33633453789718401079270595)
          ·
            refine ⟨50450180684577601618905893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33633453789718401079270595 50450180684577601618905893)
            ·
              refine ⟨9459408878358300303544855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50450180684577601618905893 9459408878358300303544855)
              ·
                refine ⟨14189113317537450455317283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9459408878358300303544855 14189113317537450455317283)
                ·
                  refine ⟨21283669976306175682975925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14189113317537450455317283 21283669976306175682975925)
                  ·
                    refine ⟨1995344060278703970278993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21283669976306175682975925 1995344060278703970278993)
                    ·
                      refine ⟨1496508045209027977709245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1995344060278703970278993 1496508045209027977709245)
                      ·
                        rfl

theorem cell23_2914439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 1, 1, 5, 2].length) (baseStart_2914439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2914439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2914439 prefixEnd_2914439 := by exact prefixLift 2914439
  have htrace : WordTrace (prefixWord ++ tailWord_2914439) baseStart_2914439 baseEnd_2914439 := by
    simpa [prefixWord, tailWord_2914439, baseEnd_2914439] using wordTrace_append hprefix tailTrace_2914439
  have hstable : (prefixWord ++ tailWord_2914439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2914439).length < 2 ^ (prefixWord ++ tailWord_2914439).sum := by decide
  have hdescent : baseEnd_2914439 < baseStart_2914439 := by decide
  rcases family_descends (prefixWord ++ tailWord_2914439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2914463 : List Nat := [1, 1, 2, 6, 1, 3, 1, 1, 3, 1, 3]
def baseStart_2914463 : Nat := 118140960795 + 2914463 * 2 ^ 59
def prefixEnd_2914463 : Nat := 4983230072969 + 3 ^ 40 * 2914463 * 2
def baseEnd_2914463 : Nat := 1496520368744735883809135

theorem tailTrace_2914463 : CollatzResearch.WordTrace tailWord_2914463 prefixEnd_2914463 1496520368744735883809135 := by
  unfold tailWord_2914463
  simp only [CollatzResearch.WordTrace]
  refine ⟨106299198440405776497556043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70866132293603850998370695 106299198440405776497556043)
  ·
    refine ⟨159448797660608664746334065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106299198440405776497556043 159448797660608664746334065)
    ·
      refine ⟨119586598245456498559750549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159448797660608664746334065 119586598245456498559750549)
      ·
        refine ⟨5605621792755773369988307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 119586598245456498559750549 5605621792755773369988307)
        ·
          refine ⟨8408432689133660054982461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5605621792755773369988307 8408432689133660054982461)
          ·
            refine ⟨3153162258425122520618423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8408432689133660054982461 3153162258425122520618423)
            ·
              refine ⟨4729743387637683780927635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3153162258425122520618423 4729743387637683780927635)
              ·
                refine ⟨7094615081456525671391453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4729743387637683780927635 7094615081456525671391453)
                ·
                  refine ⟨2660480655546197126771795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7094615081456525671391453 2660480655546197126771795)
                  ·
                    refine ⟨3990720983319295690157693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2660480655546197126771795 3990720983319295690157693)
                    ·
                      refine ⟨1496520368744735883809135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3990720983319295690157693 1496520368744735883809135)
                      ·
                        rfl

theorem cell23_2914463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_2914463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2914463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2914463 prefixEnd_2914463 := by exact prefixLift 2914463
  have htrace : WordTrace (prefixWord ++ tailWord_2914463) baseStart_2914463 baseEnd_2914463 := by
    simpa [prefixWord, tailWord_2914463, baseEnd_2914463] using wordTrace_append hprefix tailTrace_2914463
  have hstable : (prefixWord ++ tailWord_2914463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2914463).length < 2 ^ (prefixWord ++ tailWord_2914463).sum := by decide
  have hdescent : baseEnd_2914463 < baseStart_2914463 := by decide
  rcases family_descends (prefixWord ++ tailWord_2914463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2914482 : List Nat := [3, 2, 1, 1, 1, 3, 1, 3, 1, 1, 6]
def baseStart_2914482 : Nat := 118140960795 + 2914482 * 2 ^ 59
def prefixEnd_2914482 : Nat := 4983230072969 + 3 ^ 40 * 2914482 * 2
def baseEnd_2914482 : Nat := 1496530124877171309471547

theorem tailTrace_2914482 : CollatzResearch.WordTrace tailWord_2914482 prefixEnd_2914482 1496530124877171309471547 := by
  unfold tailWord_2914482
  simp only [CollatzResearch.WordTrace]
  refine ⟨26574972856834235685624425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70866594284891295161665133 26574972856834235685624425)
  ·
    refine ⟨19931229642625676764218319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26574972856834235685624425 19931229642625676764218319)
    ·
      refine ⟨29896844463938515146327479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19931229642625676764218319 29896844463938515146327479)
      ·
        refine ⟨44845266695907772719491219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29896844463938515146327479 44845266695907772719491219)
        ·
          refine ⟨67267900043861659079236829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44845266695907772719491219 67267900043861659079236829)
          ·
            refine ⟨25225462516448122154713811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67267900043861659079236829 25225462516448122154713811)
            ·
              refine ⟨37838193774672183232070717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25225462516448122154713811 37838193774672183232070717)
              ·
                refine ⟨14189322665502068712026519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37838193774672183232070717 14189322665502068712026519)
                ·
                  refine ⟨21283983998253103068039779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14189322665502068712026519 21283983998253103068039779)
                  ·
                    refine ⟨31925975997379654602059669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21283983998253103068039779 31925975997379654602059669)
                    ·
                      refine ⟨1496530124877171309471547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31925975997379654602059669 1496530124877171309471547)
                      ·
                        rfl

theorem cell23_2914482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 3, 1, 1, 6].length) (baseStart_2914482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2914482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2914482 prefixEnd_2914482 := by exact prefixLift 2914482
  have htrace : WordTrace (prefixWord ++ tailWord_2914482) baseStart_2914482 baseEnd_2914482 := by
    simpa [prefixWord, tailWord_2914482, baseEnd_2914482] using wordTrace_append hprefix tailTrace_2914482
  have hstable : (prefixWord ++ tailWord_2914482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2914482).length < 2 ^ (prefixWord ++ tailWord_2914482).sum := by decide
  have hdescent : baseEnd_2914482 < baseStart_2914482 := by decide
  rcases family_descends (prefixWord ++ tailWord_2914482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2914489 : List Nat := [1, 2, 1, 4, 1, 2, 3, 1, 3, 2, 3]
def baseStart_2914489 : Nat := 118140960795 + 2914489 * 2 ^ 59
def prefixEnd_2914489 : Nat := 4983230072969 + 3 ^ 40 * 2914489 * 2
def baseEnd_2914489 : Nat := 1496533719241752782084015

theorem tailTrace_2914489 : CollatzResearch.WordTrace tailWord_2914489 prefixEnd_2914489 1496533719241752782084015 := by
  unfold tailWord_2914489
  simp only [CollatzResearch.WordTrace]
  refine ⟨106300146738311582938002521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70866764492207721958668347 106300146738311582938002521)
  ·
    refine ⟨79725110053733687203501891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106300146738311582938002521 79725110053733687203501891)
    ·
      refine ⟨119587665080600530805252837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79725110053733687203501891 119587665080600530805252837)
      ·
        refine ⟨22422687202612599525984907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 119587665080600530805252837 22422687202612599525984907)
        ·
          refine ⟨33634030803918899288977361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22422687202612599525984907 33634030803918899288977361)
          ·
            refine ⟨25225523102939174466733021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33634030803918899288977361 25225523102939174466733021)
            ·
              refine ⟨9459571163602190425024883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25225523102939174466733021 9459571163602190425024883)
              ·
                refine ⟨14189356745403285637537325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9459571163602190425024883 14189356745403285637537325)
                ·
                  refine ⟨5321008779526232114076497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14189356745403285637537325 5321008779526232114076497)
                  ·
                    refine ⟨3990756584644674085557373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5321008779526232114076497 3990756584644674085557373)
                    ·
                      refine ⟨1496533719241752782084015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3990756584644674085557373 1496533719241752782084015)
                      ·
                        rfl

theorem cell23_2914489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 1, 3, 2, 3].length) (baseStart_2914489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2914489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2914489 prefixEnd_2914489 := by exact prefixLift 2914489
  have htrace : WordTrace (prefixWord ++ tailWord_2914489) baseStart_2914489 baseEnd_2914489 := by
    simpa [prefixWord, tailWord_2914489, baseEnd_2914489] using wordTrace_append hprefix tailTrace_2914489
  have hstable : (prefixWord ++ tailWord_2914489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2914489).length < 2 ^ (prefixWord ++ tailWord_2914489).sum := by decide
  have hdescent : baseEnd_2914489 < baseStart_2914489 := by decide
  rcases family_descends (prefixWord ++ tailWord_2914489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2914520 : List Nat := [2, 1, 2, 2, 4, 2, 1, 4, 1, 2, 2]
def baseStart_2914520 : Nat := 118140960795 + 2914520 * 2 ^ 59
def prefixEnd_2914520 : Nat := 4983230072969 + 3 ^ 40 * 2914520 * 2
def baseEnd_2914520 : Nat := 1496549637142042160796373

theorem tailTrace_2914520 : CollatzResearch.WordTrace tailWord_2914520 prefixEnd_2914520 1496549637142042160796373 := by
  unfold tailWord_2914520
  simp only [CollatzResearch.WordTrace]
  refine ⟨53150638700599637616190507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70867518267466183488254009 53150638700599637616190507)
  ·
    refine ⟨79725958050899456424285761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53150638700599637616190507 79725958050899456424285761)
    ·
      refine ⟨59794468538174592318214321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79725958050899456424285761 59794468538174592318214321)
      ·
        refine ⟨44845851403630944238660741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59794468538174592318214321 44845851403630944238660741)
        ·
          refine ⟨8408597138180802044748889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44845851403630944238660741 8408597138180802044748889)
          ·
            refine ⟨6306447853635601533561667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8408597138180802044748889 6306447853635601533561667)
            ·
              refine ⟨9459671780453402300342501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6306447853635601533561667 9459671780453402300342501)
              ·
                refine ⟨1773688458835012931314219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9459671780453402300342501 1773688458835012931314219)
                ·
                  refine ⟨2660532688252519396971329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1773688458835012931314219 2660532688252519396971329)
                  ·
                    refine ⟨1995399516189389547728497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2660532688252519396971329 1995399516189389547728497)
                    ·
                      refine ⟨1496549637142042160796373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1995399516189389547728497 1496549637142042160796373)
                      ·
                        rfl

theorem cell23_2914520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 4, 1, 2, 2].length) (baseStart_2914520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2914520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2914520 prefixEnd_2914520 := by exact prefixLift 2914520
  have htrace : WordTrace (prefixWord ++ tailWord_2914520) baseStart_2914520 baseEnd_2914520 := by
    simpa [prefixWord, tailWord_2914520, baseEnd_2914520] using wordTrace_append hprefix tailTrace_2914520
  have hstable : (prefixWord ++ tailWord_2914520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2914520).length < 2 ^ (prefixWord ++ tailWord_2914520).sum := by decide
  have hdescent : baseEnd_2914520 < baseStart_2914520 := by decide
  rcases family_descends (prefixWord ++ tailWord_2914520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2914522 : List Nat := [3, 1, 1, 2, 2, 1, 3, 1, 2, 7]
def baseStart_2914522 : Nat := 118140960795 + 2914522 * 2 ^ 59
def prefixEnd_2914522 : Nat := 4983230072969 + 3 ^ 40 * 2914522 * 2
def baseEnd_2914522 : Nat := 498850221367783717657121

theorem tailTrace_2914522 : CollatzResearch.WordTrace tailWord_2914522 prefixEnd_2914522 498850221367783717657121 := by
  unfold tailWord_2914522
  simp only [CollatzResearch.WordTrace]
  refine ⟨26575337586798007393488455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70867566898128019715969213 26575337586798007393488455)
  ·
    refine ⟨39863006380197011090232683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26575337586798007393488455 39863006380197011090232683)
    ·
      refine ⟨59794509570295516635349025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39863006380197011090232683 59794509570295516635349025)
      ·
        refine ⟨44845882177721637476511769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59794509570295516635349025 44845882177721637476511769)
        ·
          refine ⟨33634411633291228107383827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44845882177721637476511769 33634411633291228107383827)
          ·
            refine ⟨50451617449936842161075741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33634411633291228107383827 50451617449936842161075741)
            ·
              refine ⟨18919356543726315810403403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50451617449936842161075741 18919356543726315810403403)
              ·
                refine ⟨28379034815589473715605105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18919356543726315810403403 28379034815589473715605105)
                ·
                  refine ⟨21284276111692105286703829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28379034815589473715605105 21284276111692105286703829)
                  ·
                    refine ⟨498850221367783717657121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21284276111692105286703829 498850221367783717657121)
                    ·
                      rfl

theorem cell23_2914522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 1, 2, 7].length) (baseStart_2914522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2914522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2914522 prefixEnd_2914522 := by exact prefixLift 2914522
  have htrace : WordTrace (prefixWord ++ tailWord_2914522) baseStart_2914522 baseEnd_2914522 := by
    simpa [prefixWord, tailWord_2914522, baseEnd_2914522] using wordTrace_append hprefix tailTrace_2914522
  have hstable : (prefixWord ++ tailWord_2914522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2914522).length < 2 ^ (prefixWord ++ tailWord_2914522).sum := by decide
  have hdescent : baseEnd_2914522 < baseStart_2914522 := by decide
  rcases family_descends (prefixWord ++ tailWord_2914522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2914530 : List Nat := [3, 3, 4, 1, 1, 1, 2, 1, 1, 6]
def baseStart_2914530 : Nat := 118140960795 + 2914530 * 2 ^ 59
def prefixEnd_2914530 : Nat := 4983230072969 + 3 ^ 40 * 2914530 * 2
def baseEnd_2914530 : Nat := 498851590649529040557109

theorem tailTrace_2914530 : CollatzResearch.WordTrace tailWord_2914530 prefixEnd_2914530 498851590649529040557109 := by
  unfold tailWord_2914530
  simp only [CollatzResearch.WordTrace]
  refine ⟨26575410532790761735061261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70867761420775364626830029 26575410532790761735061261)
  ·
    refine ⟨9965778949796535650647973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26575410532790761735061261 9965778949796535650647973)
    ·
      refine ⟨1868583553086850434496495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9965778949796535650647973 1868583553086850434496495)
      ·
        refine ⟨2802875329630275651744743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1868583553086850434496495 2802875329630275651744743)
        ·
          refine ⟨4204312994445413477617115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2802875329630275651744743 4204312994445413477617115)
          ·
            refine ⟨6306469491668120216425673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4204312994445413477617115 6306469491668120216425673)
            ·
              refine ⟨4729852118751090162319255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6306469491668120216425673 4729852118751090162319255)
              ·
                refine ⟨7094778178126635243478883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4729852118751090162319255 7094778178126635243478883)
                ·
                  refine ⟨10642167267189952865218325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7094778178126635243478883 10642167267189952865218325)
                  ·
                    refine ⟨498851590649529040557109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10642167267189952865218325 498851590649529040557109)
                    ·
                      rfl

theorem cell23_2914530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_2914530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2914530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2914530 prefixEnd_2914530 := by exact prefixLift 2914530
  have htrace : WordTrace (prefixWord ++ tailWord_2914530) baseStart_2914530 baseEnd_2914530 := by
    simpa [prefixWord, tailWord_2914530, baseEnd_2914530] using wordTrace_append hprefix tailTrace_2914530
  have hstable : (prefixWord ++ tailWord_2914530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2914530).length < 2 ^ (prefixWord ++ tailWord_2914530).sum := by decide
  have hdescent : baseEnd_2914530 < baseStart_2914530 := by decide
  rcases family_descends (prefixWord ++ tailWord_2914530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2914532 : List Nat := [2, 3, 1, 1, 1, 2, 1, 2, 1, 4, 5]
def baseStart_2914532 : Nat := 118140960795 + 2914532 * 2 ^ 59
def prefixEnd_2914532 : Nat := 4983230072969 + 3 ^ 40 * 2914532 * 2
def baseEnd_2914532 : Nat := 1496555798909896113846317

theorem tailTrace_2914532 : CollatzResearch.WordTrace tailWord_2914532 prefixEnd_2914532 1496555798909896113846317 := by
  unfold tailWord_2914532
  simp only [CollatzResearch.WordTrace]
  refine ⟨53150857538577900640908925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70867810051437200854545233 53150857538577900640908925)
  ·
    refine ⟨19931571576966712740340847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53150857538577900640908925 19931571576966712740340847)
    ·
      refine ⟨29897357365450069110511271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19931571576966712740340847 29897357365450069110511271)
      ·
        refine ⟨44846036048175103665766907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29897357365450069110511271 44846036048175103665766907)
        ·
          refine ⟨67269054072262655498650361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44846036048175103665766907 67269054072262655498650361)
          ·
            refine ⟨50451790554196991623987771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67269054072262655498650361 50451790554196991623987771)
            ·
              refine ⟨75677685831295487435981657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50451790554196991623987771 75677685831295487435981657)
              ·
                refine ⟨56758264373471615576986243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75677685831295487435981657 56758264373471615576986243)
                ·
                  refine ⟨85137396560207423365479365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56758264373471615576986243 85137396560207423365479365)
                  ·
                    refine ⟨15963261855038891881027381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 85137396560207423365479365 15963261855038891881027381)
                    ·
                      refine ⟨1496555798909896113846317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15963261855038891881027381 1496555798909896113846317)
                      ·
                        rfl

theorem cell23_2914532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 2, 1, 4, 5].length) (baseStart_2914532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2914532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2914532 prefixEnd_2914532 := by exact prefixLift 2914532
  have htrace : WordTrace (prefixWord ++ tailWord_2914532) baseStart_2914532 baseEnd_2914532 := by
    simpa [prefixWord, tailWord_2914532, baseEnd_2914532] using wordTrace_append hprefix tailTrace_2914532
  have hstable : (prefixWord ++ tailWord_2914532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2914532).length < 2 ^ (prefixWord ++ tailWord_2914532).sum := by decide
  have hdescent : baseEnd_2914532 < baseStart_2914532 := by decide
  rcases family_descends (prefixWord ++ tailWord_2914532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2914536 : List Nat := [2, 1, 4, 1, 2, 3, 2, 1, 1, 3, 3]
def baseStart_2914536 : Nat := 118140960795 + 2914536 * 2 ^ 59
def prefixEnd_2914536 : Nat := 4983230072969 + 3 ^ 40 * 2914536 * 2
def baseEnd_2914536 : Nat := 1496557852832514098196299

theorem tailTrace_2914536 : CollatzResearch.WordTrace tailWord_2914536 prefixEnd_2914536 1496557852832514098196299 := by
  unfold tailWord_2914536
  simp only [CollatzResearch.WordTrace]
  refine ⟨53150930484570654982481731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70867907312760873309975641 53150930484570654982481731)
  ·
    refine ⟨79726395726855982473722597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53150930484570654982481731 79726395726855982473722597)
    ·
      refine ⟨14948699198785496713822987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79726395726855982473722597 14948699198785496713822987)
      ·
        refine ⟨22423048798178245070734481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14948699198785496713822987 22423048798178245070734481)
        ·
          refine ⟨16817286598633683803050861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22423048798178245070734481 16817286598633683803050861)
          ·
            refine ⟨6306482474487631426144073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16817286598633683803050861 6306482474487631426144073)
            ·
              refine ⟨4729861855865723569608055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6306482474487631426144073 4729861855865723569608055)
              ·
                refine ⟨7094792783798585354412083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4729861855865723569608055 7094792783798585354412083)
                ·
                  refine ⟨10642189175697878031618125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7094792783798585354412083 10642189175697878031618125)
                  ·
                    refine ⟨3990820940886704261856797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10642189175697878031618125 3990820940886704261856797)
                    ·
                      refine ⟨1496557852832514098196299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3990820940886704261856797 1496557852832514098196299)
                      ·
                        rfl

theorem cell23_2914536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 2, 1, 1, 3, 3].length) (baseStart_2914536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2914536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2914536 prefixEnd_2914536 := by exact prefixLift 2914536
  have htrace : WordTrace (prefixWord ++ tailWord_2914536) baseStart_2914536 baseEnd_2914536 := by
    simpa [prefixWord, tailWord_2914536, baseEnd_2914536] using wordTrace_append hprefix tailTrace_2914536
  have hstable : (prefixWord ++ tailWord_2914536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2914536).length < 2 ^ (prefixWord ++ tailWord_2914536).sum := by decide
  have hdescent : baseEnd_2914536 < baseStart_2914536 := by decide
  rcases family_descends (prefixWord ++ tailWord_2914536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2914593 : List Nat := [1, 2, 3, 2, 1, 1, 2, 5, 2, 2, 2]
def baseStart_2914593 : Nat := 118140960795 + 2914593 * 2 ^ 59
def prefixEnd_2914593 : Nat := 4983230072969 + 3 ^ 40 * 2914593 * 2
def baseEnd_2914593 : Nat := 1496587121229820375183537

theorem tailTrace_2914593 : CollatzResearch.WordTrace tailWord_2914593 prefixEnd_2914593 1496587121229820375183537 := by
  unfold tailWord_2914593
  simp only [CollatzResearch.WordTrace]
  refine ⟨106303939929934808699788433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70869293286623205799858955 106303939929934808699788433)
  ·
    refine ⟨79727954947451106524841325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106303939929934808699788433 79727954947451106524841325)
    ·
      refine ⟨29897983105294164946815497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79727954947451106524841325 29897983105294164946815497)
      ·
        refine ⟨22423487328970623710111623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29897983105294164946815497 22423487328970623710111623)
        ·
          refine ⟨33635230993455935565167435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22423487328970623710111623 33635230993455935565167435)
          ·
            refine ⟨50452846490183903347751153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33635230993455935565167435 50452846490183903347751153)
            ·
              refine ⟨37839634867637927510813365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50452846490183903347751153 37839634867637927510813365)
              ·
                refine ⟨3547465768841055704138753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37839634867637927510813365 3547465768841055704138753)
                ·
                  refine ⟨2660599326630791778104065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3547465768841055704138753 2660599326630791778104065)
                  ·
                    refine ⟨1995449494973093833578049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2660599326630791778104065 1995449494973093833578049)
                    ·
                      refine ⟨1496587121229820375183537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1995449494973093833578049 1496587121229820375183537)
                      ·
                        rfl

theorem cell23_2914593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 5, 2, 2, 2].length) (baseStart_2914593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2914593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2914593 prefixEnd_2914593 := by exact prefixLift 2914593
  have htrace : WordTrace (prefixWord ++ tailWord_2914593) baseStart_2914593 baseEnd_2914593 := by
    simpa [prefixWord, tailWord_2914593, baseEnd_2914593] using wordTrace_append hprefix tailTrace_2914593
  have hstable : (prefixWord ++ tailWord_2914593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2914593).length < 2 ^ (prefixWord ++ tailWord_2914593).sum := by decide
  have hdescent : baseEnd_2914593 < baseStart_2914593 := by decide
  rcases family_descends (prefixWord ++ tailWord_2914593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2914616 : List Nat := [2, 1, 2, 1, 3, 1, 5, 3, 5]
def baseStart_2914616 : Nat := 118140960795 + 2914616 * 2 ^ 59
def prefixEnd_2914616 : Nat := 4983230072969 + 3 ^ 40 * 2914616 * 2
def baseEnd_2914616 : Nat := 166288770142763753910659

theorem tailTrace_2914616 : CollatzResearch.WordTrace tailWord_2914616 prefixEnd_2914616 166288770142763753910659 := by
  unfold tailWord_2914616
  simp only [CollatzResearch.WordTrace]
  refine ⟨53152389404425741813937851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70869852539234322418583801 53152389404425741813937851)
  ·
    refine ⟨79728584106638612720906777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53152389404425741813937851 79728584106638612720906777)
    ·
      refine ⟨59796438079978959540680083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79728584106638612720906777 59796438079978959540680083)
      ·
        refine ⟨89694657119968439311020125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59796438079978959540680083 89694657119968439311020125)
        ·
          refine ⟨33635496419988164741632547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89694657119968439311020125 33635496419988164741632547)
          ·
            refine ⟨50453244629982247112448821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33635496419988164741632547 50453244629982247112448821)
            ·
              refine ⟨4729991684060835666792077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50453244629982247112448821 4729991684060835666792077)
              ·
                refine ⟨1773746881522813375047029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4729991684060835666792077 1773746881522813375047029)
                ·
                  refine ⟨166288770142763753910659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1773746881522813375047029 166288770142763753910659)
                  ·
                    rfl

theorem cell23_2914616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 5, 3, 5].length) (baseStart_2914616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2914616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2914616 prefixEnd_2914616 := by exact prefixLift 2914616
  have htrace : WordTrace (prefixWord ++ tailWord_2914616) baseStart_2914616 baseEnd_2914616 := by
    simpa [prefixWord, tailWord_2914616, baseEnd_2914616] using wordTrace_append hprefix tailTrace_2914616
  have hstable : (prefixWord ++ tailWord_2914616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2914616).length < 2 ^ (prefixWord ++ tailWord_2914616).sum := by decide
  have hdescent : baseEnd_2914616 < baseStart_2914616 := by decide
  rcases family_descends (prefixWord ++ tailWord_2914616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2914636 : List Nat := [2, 2, 1, 3, 2, 1, 2, 1, 2, 5, 2]
def baseStart_2914636 : Nat := 118140960795 + 2914636 * 2 ^ 59
def prefixEnd_2914636 : Nat := 4983230072969 + 3 ^ 40 * 2914636 * 2
def baseEnd_2914636 : Nat := 1496609200897963706945839

theorem tailTrace_2914636 : CollatzResearch.WordTrace tailWord_2914636 prefixEnd_2914636 1496609200897963706945839 := by
  unfold tailWord_2914636
  simp only [CollatzResearch.WordTrace]
  refine ⟨53152754134389513521801881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70870338845852684695735841 53152754134389513521801881)
  ·
    refine ⟨39864565600792135141351411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53152754134389513521801881 39864565600792135141351411)
    ·
      refine ⟨59796848401188202712027117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39864565600792135141351411 59796848401188202712027117)
      ·
        refine ⟨22423818150445576017010169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59796848401188202712027117 22423818150445576017010169)
        ·
          refine ⟨16817863612834182012757627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22423818150445576017010169 16817863612834182012757627)
          ·
            refine ⟨25226795419251273019136441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16817863612834182012757627 25226795419251273019136441)
            ·
              refine ⟨18920096564438454764352331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25226795419251273019136441 18920096564438454764352331)
              ·
                refine ⟨28380144846657682146528497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18920096564438454764352331 28380144846657682146528497)
                ·
                  refine ⟨21285108634993261609896373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28380144846657682146528497 21285108634993261609896373)
                  ·
                    refine ⟨1995478934530618275927785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21285108634993261609896373 1995478934530618275927785)
                    ·
                      refine ⟨1496609200897963706945839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1995478934530618275927785 1496609200897963706945839)
                      ·
                        rfl

theorem cell23_2914636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 1, 2, 5, 2].length) (baseStart_2914636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2914636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2914636 prefixEnd_2914636 := by exact prefixLift 2914636
  have htrace : WordTrace (prefixWord ++ tailWord_2914636) baseStart_2914636 baseEnd_2914636 := by
    simpa [prefixWord, tailWord_2914636, baseEnd_2914636] using wordTrace_append hprefix tailTrace_2914636
  have hstable : (prefixWord ++ tailWord_2914636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2914636).length < 2 ^ (prefixWord ++ tailWord_2914636).sum := by decide
  have hdescent : baseEnd_2914636 < baseStart_2914636 := by decide
  rcases family_descends (prefixWord ++ tailWord_2914636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2914649 : List Nat := [1, 2, 1, 2, 2, 2, 1, 1, 6, 1, 4]
def baseStart_2914649 : Nat := 118140960795 + 2914649 * 2 ^ 59
def prefixEnd_2914649 : Nat := 4983230072969 + 3 ^ 40 * 2914649 * 2
def baseEnd_2914649 : Nat := 1496615876146472156083279

theorem tailTrace_2914649 : CollatzResearch.WordTrace tailWord_2914649 prefixEnd_2914649 1496615876146472156083279 := by
  unfold tailWord_2914649
  simp only [CollatzResearch.WordTrace]
  refine ⟨106305982417731930263827001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70870654945154620175884667 106305982417731930263827001)
  ·
    refine ⟨79729486813298947697870251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106305982417731930263827001 79729486813298947697870251)
    ·
      refine ⟨119594230219948421546805377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79729486813298947697870251 119594230219948421546805377)
      ·
        refine ⟨89695672664961316160104033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119594230219948421546805377 89695672664961316160104033)
        ·
          refine ⟨67271754498720987120078025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89695672664961316160104033 67271754498720987120078025)
          ·
            refine ⟨50453815874040740340058519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67271754498720987120078025 50453815874040740340058519)
            ·
              refine ⟨75680723811061110510087779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50453815874040740340058519 75680723811061110510087779)
              ·
                refine ⟨113521085716591665765131669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75680723811061110510087779 113521085716591665765131669)
                ·
                  refine ⟨5321300892965234332740547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 113521085716591665765131669 5321300892965234332740547)
                  ·
                    refine ⟨7981951339447851499110821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5321300892965234332740547 7981951339447851499110821)
                    ·
                      refine ⟨1496615876146472156083279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7981951339447851499110821 1496615876146472156083279)
                      ·
                        rfl

theorem cell23_2914649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 6, 1, 4].length) (baseStart_2914649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2914649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2914649 prefixEnd_2914649 := by exact prefixLift 2914649
  have htrace : WordTrace (prefixWord ++ tailWord_2914649) baseStart_2914649 baseEnd_2914649 := by
    simpa [prefixWord, tailWord_2914649, baseEnd_2914649] using wordTrace_append hprefix tailTrace_2914649
  have hstable : (prefixWord ++ tailWord_2914649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2914649).length < 2 ^ (prefixWord ++ tailWord_2914649).sum := by decide
  have hdescent : baseEnd_2914649 < baseStart_2914649 := by decide
  rcases family_descends (prefixWord ++ tailWord_2914649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2914740 : List Nat := [2, 5, 2, 2, 1, 1, 1, 1, 8]
def baseStart_2914740 : Nat := 118140960795 + 2914740 * 2 ^ 59
def prefixEnd_2914740 : Nat := 4983230072969 + 3 ^ 40 * 2914740 * 2
def baseEnd_2914740 : Nat := 166295844765114588893929

theorem tailTrace_2914740 : CollatzResearch.WordTrace tailWord_2914740 prefixEnd_2914740 166295844765114588893929 := by
  unfold tailWord_2914740
  simp only [CollatzResearch.WordTrace]
  refine ⟨53154650730201126402694837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70872867640268168536926449 53154650730201126402694837)
  ·
    refine ⟨4983248505956355600252641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 53154650730201126402694837 4983248505956355600252641)
    ·
      refine ⟨3737436379467266700189481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4983248505956355600252641 3737436379467266700189481)
      ·
        refine ⟨2803077284600450025142111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3737436379467266700189481 2803077284600450025142111)
        ·
          refine ⟨4204615926900675037713167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2803077284600450025142111 4204615926900675037713167)
          ·
            refine ⟨6306923890351012556569751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4204615926900675037713167 6306923890351012556569751)
            ·
              refine ⟨9460385835526518834854627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6306923890351012556569751 9460385835526518834854627)
              ·
                refine ⟨14190578753289778252281941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9460385835526518834854627 14190578753289778252281941)
                ·
                  refine ⟨166295844765114588893929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14190578753289778252281941 166295844765114588893929)
                  ·
                    rfl

theorem cell23_2914740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 1, 8].length) (baseStart_2914740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2914740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2914740 prefixEnd_2914740 := by exact prefixLift 2914740
  have htrace : WordTrace (prefixWord ++ tailWord_2914740) baseStart_2914740 baseEnd_2914740 := by
    simpa [prefixWord, tailWord_2914740, baseEnd_2914740] using wordTrace_append hprefix tailTrace_2914740
  have hstable : (prefixWord ++ tailWord_2914740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2914740).length < 2 ^ (prefixWord ++ tailWord_2914740).sum := by decide
  have hdescent : baseEnd_2914740 < baseStart_2914740 := by decide
  rcases family_descends (prefixWord ++ tailWord_2914740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2914773 : List Nat := [1, 3, 2, 3, 1, 2, 1, 4, 1, 1, 4]
def baseStart_2914773 : Nat := 118140960795 + 2914773 * 2 ^ 59
def prefixEnd_2914773 : Nat := 4983230072969 + 3 ^ 40 * 2914773 * 2
def baseEnd_2914773 : Nat := 1496679547747629670932709

theorem tailTrace_2914773 : CollatzResearch.WordTrace tailWord_2914773 prefixEnd_2914773 1496679547747629670932709 := by
  unfold tailWord_2914773
  simp only [CollatzResearch.WordTrace]
  refine ⟨106310505069282699441340973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70873670046188466294227315 106310505069282699441340973)
  ·
    refine ⟨39866439400981012290502865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106310505069282699441340973 39866439400981012290502865)
    ·
      refine ⟨29899829550735759217877149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39866439400981012290502865 29899829550735759217877149)
      ·
        refine ⟨11212436081525909706703931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29899829550735759217877149 11212436081525909706703931)
        ·
          refine ⟨16818654122288864560055897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11212436081525909706703931 16818654122288864560055897)
          ·
            refine ⟨12613990591716648420041923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16818654122288864560055897 12613990591716648420041923)
            ·
              refine ⟨18920985887574972630062885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12613990591716648420041923 18920985887574972630062885)
              ·
                refine ⟨3547684853920307368136791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18920985887574972630062885 3547684853920307368136791)
                ·
                  refine ⟨5321527280880461052205187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3547684853920307368136791 5321527280880461052205187)
                  ·
                    refine ⟨7982290921320691578307781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5321527280880461052205187 7982290921320691578307781)
                    ·
                      refine ⟨1496679547747629670932709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7982290921320691578307781 1496679547747629670932709)
                      ·
                        rfl

theorem cell23_2914773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 4, 1, 1, 4].length) (baseStart_2914773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2914773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2914773 prefixEnd_2914773 := by exact prefixLift 2914773
  have htrace : WordTrace (prefixWord ++ tailWord_2914773) baseStart_2914773 baseEnd_2914773 := by
    simpa [prefixWord, tailWord_2914773, baseEnd_2914773] using wordTrace_append hprefix tailTrace_2914773
  have hstable : (prefixWord ++ tailWord_2914773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2914773).length < 2 ^ (prefixWord ++ tailWord_2914773).sum := by decide
  have hdescent : baseEnd_2914773 < baseStart_2914773 := by decide
  rcases family_descends (prefixWord ++ tailWord_2914773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2914817 : List Nat := [1, 2, 4, 1, 3, 3, 2, 1, 2, 4]
def baseStart_2914817 : Nat := 118140960795 + 2914817 * 2 ^ 59
def prefixEnd_2914817 : Nat := 4983230072969 + 3 ^ 40 * 2914817 * 2
def baseEnd_2914817 : Nat := 498900713632142499594169

theorem tailTrace_2914817 : CollatzResearch.WordTrace tailWord_2914817 prefixEnd_2914817 498900713632142499594169 := by
  unfold tailWord_2914817
  simp only [CollatzResearch.WordTrace]
  refine ⟨106312109881123294955942705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70874739920748863303961803 106312109881123294955942705)
  ·
    refine ⟨79734082410842471216957029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106312109881123294955942705 79734082410842471216957029)
    ·
      refine ⟨14950140452032963353179443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79734082410842471216957029 14950140452032963353179443)
      ·
        refine ⟨22425210678049445029769165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14950140452032963353179443 22425210678049445029769165)
        ·
          refine ⟨8409454004268541886163437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22425210678049445029769165 8409454004268541886163437)
          ·
            refine ⟨3153545251600703207311289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8409454004268541886163437 3153545251600703207311289)
            ·
              refine ⟨2365158938700527405483467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3153545251600703207311289 2365158938700527405483467)
              ·
                refine ⟨3547738408050791108225201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2365158938700527405483467 3547738408050791108225201)
                ·
                  refine ⟨2660803806038093331168901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3547738408050791108225201 2660803806038093331168901)
                  ·
                    refine ⟨498900713632142499594169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2660803806038093331168901 498900713632142499594169)
                    ·
                      rfl

theorem cell23_2914817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 2, 1, 2, 4].length) (baseStart_2914817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2914817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2914817 prefixEnd_2914817 := by exact prefixLift 2914817
  have htrace : WordTrace (prefixWord ++ tailWord_2914817) baseStart_2914817 baseEnd_2914817 := by
    simpa [prefixWord, tailWord_2914817, baseEnd_2914817] using wordTrace_append hprefix tailTrace_2914817
  have hstable : (prefixWord ++ tailWord_2914817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2914817).length < 2 ^ (prefixWord ++ tailWord_2914817).sum := by decide
  have hdescent : baseEnd_2914817 < baseStart_2914817 := by decide
  rcases family_descends (prefixWord ++ tailWord_2914817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2914866 : List Nat := [3, 2, 1, 1, 2, 1, 2, 2, 1, 3, 5]
def baseStart_2914866 : Nat := 118140960795 + 2914866 * 2 ^ 59
def prefixEnd_2914866 : Nat := 4983230072969 + 3 ^ 40 * 2914866 * 2
def baseEnd_2914866 : Nat := 1496727301448497807069781

theorem tailTrace_2914866 : CollatzResearch.WordTrace tailWord_2914866 prefixEnd_2914866 1496727301448497807069781 := by
  unfold tailWord_2914866
  simp only [CollatzResearch.WordTrace]
  refine ⟨26578474264486444081119113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70875931371963850882984301 26578474264486444081119113)
  ·
    refine ⟨19933855698364833060839335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26578474264486444081119113 19933855698364833060839335)
    ·
      refine ⟨29900783547547249591259003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19933855698364833060839335 29900783547547249591259003)
      ·
        refine ⟨44851175321320874386888505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29900783547547249591259003 44851175321320874386888505)
        ·
          refine ⟨33638381490990655790166379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44851175321320874386888505 33638381490990655790166379)
          ·
            refine ⟨50457572236485983685249569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33638381490990655790166379 50457572236485983685249569)
            ·
              refine ⟨37843179177364487763937177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50457572236485983685249569 37843179177364487763937177)
              ·
                refine ⟨28382384383023365822952883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37843179177364487763937177 28382384383023365822952883)
                ·
                  refine ⟨42573576574535048734429325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28382384383023365822952883 42573576574535048734429325)
                  ·
                    refine ⟨15965091215450643275410997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42573576574535048734429325 15965091215450643275410997)
                    ·
                      refine ⟨1496727301448497807069781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15965091215450643275410997 1496727301448497807069781)
                      ·
                        rfl

theorem cell23_2914866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 2, 1, 3, 5].length) (baseStart_2914866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2914866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2914866 prefixEnd_2914866 := by exact prefixLift 2914866
  have htrace : WordTrace (prefixWord ++ tailWord_2914866) baseStart_2914866 baseEnd_2914866 := by
    simpa [prefixWord, tailWord_2914866, baseEnd_2914866] using wordTrace_append hprefix tailTrace_2914866
  have hstable : (prefixWord ++ tailWord_2914866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2914866).length < 2 ^ (prefixWord ++ tailWord_2914866).sum := by decide
  have hdescent : baseEnd_2914866 < baseStart_2914866 := by decide
  rcases family_descends (prefixWord ++ tailWord_2914866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2914913 : List Nat := [1, 2, 3, 1, 1, 4, 1, 2, 2, 3, 3]
def baseStart_2914913 : Nat := 118140960795 + 2914913 * 2 ^ 59
def prefixEnd_2914913 : Nat := 4983230072969 + 3 ^ 40 * 2914913 * 2
def baseEnd_2914913 : Nat := 1496751435039259123182065

theorem tailTrace_2914913 : CollatzResearch.WordTrace tailWord_2914913 prefixEnd_2914913 1496751435039259123182065 := by
  unfold tailWord_2914913
  simp only [CollatzResearch.WordTrace]
  refine ⟨106315611288775503351437393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70877074192517002234291595 106315611288775503351437393)
  ·
    refine ⟨79736708466581627513578045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106315611288775503351437393 79736708466581627513578045)
    ·
      refine ⟨29901265674968110317591767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79736708466581627513578045 29901265674968110317591767)
      ·
        refine ⟨44851898512452165476387651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29901265674968110317591767 44851898512452165476387651)
        ·
          refine ⟨67277847768678248214581477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44851898512452165476387651 67277847768678248214581477)
          ·
            refine ⟨12614596456627171540234027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67277847768678248214581477 12614596456627171540234027)
            ·
              refine ⟨18921894684940757310351041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12614596456627171540234027 18921894684940757310351041)
              ·
                refine ⟨14191421013705567982763281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18921894684940757310351041 14191421013705567982763281)
                ·
                  refine ⟨10643565760279175987072461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14191421013705567982763281 10643565760279175987072461)
                  ·
                    refine ⟨3991337160104690995152173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10643565760279175987072461 3991337160104690995152173)
                    ·
                      refine ⟨1496751435039259123182065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3991337160104690995152173 1496751435039259123182065)
                      ·
                        rfl

theorem cell23_2914913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 2, 2, 3, 3].length) (baseStart_2914913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2914913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2914913 prefixEnd_2914913 := by exact prefixLift 2914913
  have htrace : WordTrace (prefixWord ++ tailWord_2914913) baseStart_2914913 baseEnd_2914913 := by
    simpa [prefixWord, tailWord_2914913, baseEnd_2914913] using wordTrace_append hprefix tailTrace_2914913
  have hstable : (prefixWord ++ tailWord_2914913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2914913).length < 2 ^ (prefixWord ++ tailWord_2914913).sum := by decide
  have hdescent : baseEnd_2914913 < baseStart_2914913 := by decide
  rcases family_descends (prefixWord ++ tailWord_2914913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2914920 : List Nat := [2, 1, 4, 3, 2, 1, 2, 1, 7]
def baseStart_2914920 : Nat := 118140960795 + 2914920 * 2 ^ 59
def prefixEnd_2914920 : Nat := 4983230072969 + 3 ^ 40 * 2914920 * 2
def baseEnd_2914920 : Nat := 166306114378204510643837

theorem tailTrace_2914920 : CollatzResearch.WordTrace tailWord_2914920 prefixEnd_2914920 166306114378204510643837 := by
  unfold tailWord_2914920
  simp only [CollatzResearch.WordTrace]
  refine ⟨53157933299875071773471107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70877244399833429031294809 53157933299875071773471107)
  ·
    refine ⟨79736899949812607660206661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53157933299875071773471107 79736899949812607660206661)
    ·
      refine ⟨14950668740589863936288749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79736899949812607660206661 14950668740589863936288749)
      ·
        refine ⟨5606500777721198976108281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14950668740589863936288749 5606500777721198976108281)
        ·
          refine ⟨4204875583290899232081211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5606500777721198976108281 4204875583290899232081211)
          ·
            refine ⟨6307313374936348848121817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4204875583290899232081211 6307313374936348848121817)
            ·
              refine ⟨4730485031202261636091363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6307313374936348848121817 4730485031202261636091363)
              ·
                refine ⟨7095727546803392454137045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4730485031202261636091363 7095727546803392454137045)
                ·
                  refine ⟨166306114378204510643837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7095727546803392454137045 166306114378204510643837)
                  ·
                    rfl

theorem cell23_2914920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 2, 1, 7].length) (baseStart_2914920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2914920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2914920 prefixEnd_2914920 := by exact prefixLift 2914920
  have htrace : WordTrace (prefixWord ++ tailWord_2914920) baseStart_2914920 baseEnd_2914920 := by
    simpa [prefixWord, tailWord_2914920, baseEnd_2914920] using wordTrace_append hprefix tailTrace_2914920
  have hstable : (prefixWord ++ tailWord_2914920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2914920).length < 2 ^ (prefixWord ++ tailWord_2914920).sum := by decide
  have hdescent : baseEnd_2914920 < baseStart_2914920 := by decide
  rcases family_descends (prefixWord ++ tailWord_2914920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2914923 : List Nat := [1, 1, 1, 1, 2, 2, 1, 5, 2, 5, 2]
def baseStart_2914923 : Nat := 118140960795 + 2914923 * 2 ^ 59
def prefixEnd_2914923 : Nat := 4983230072969 + 3 ^ 40 * 2914923 * 2
def baseEnd_2914923 : Nat := 1496756569845804084057019

theorem tailTrace_2914923 : CollatzResearch.WordTrace tailWord_2914923 prefixEnd_2914923 1496756569845804084057019 := by
  unfold tailWord_2914923
  simp only [CollatzResearch.WordTrace]
  refine ⟨106315976018739275059301423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70877317345826183372867615 106315976018739275059301423)
  ·
    refine ⟨159473964028108912588952135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106315976018739275059301423 159473964028108912588952135)
    ·
      refine ⟨239210946042163368883428203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159473964028108912588952135 239210946042163368883428203)
      ·
        refine ⟨358816419063245053325142305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239210946042163368883428203 358816419063245053325142305)
        ·
          refine ⟨269112314297433789993856729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 358816419063245053325142305 269112314297433789993856729)
          ·
            refine ⟨201834235723075342495392547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 269112314297433789993856729 201834235723075342495392547)
            ·
              refine ⟨302751353584613013743088821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 201834235723075342495392547 302751353584613013743088821)
              ·
                refine ⟨28382939398557470038414577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 302751353584613013743088821 28382939398557470038414577)
                ·
                  refine ⟨21287204548918102528810933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28382939398557470038414577 21287204548918102528810933)
                  ·
                    refine ⟨1995675426461072112076025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21287204548918102528810933 1995675426461072112076025)
                    ·
                      refine ⟨1496756569845804084057019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1995675426461072112076025 1496756569845804084057019)
                      ·
                        rfl

theorem cell23_2914923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 5, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 5, 2, 5, 2].length) (baseStart_2914923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2914923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2914923 prefixEnd_2914923 := by exact prefixLift 2914923
  have htrace : WordTrace (prefixWord ++ tailWord_2914923) baseStart_2914923 baseEnd_2914923 := by
    simpa [prefixWord, tailWord_2914923, baseEnd_2914923] using wordTrace_append hprefix tailTrace_2914923
  have hstable : (prefixWord ++ tailWord_2914923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2914923).length < 2 ^ (prefixWord ++ tailWord_2914923).sum := by decide
  have hdescent : baseEnd_2914923 < baseStart_2914923 := by decide
  rcases family_descends (prefixWord ++ tailWord_2914923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2914953 : List Nat := [1, 2, 1, 1, 4, 1, 1, 5, 2, 1, 4]
def baseStart_2914953 : Nat := 118140960795 + 2914953 * 2 ^ 59
def prefixEnd_2914953 : Nat := 4983230072969 + 3 ^ 40 * 2914953 * 2
def baseEnd_2914953 : Nat := 1496771974265438966681881

theorem tailTrace_2914953 : CollatzResearch.WordTrace tailWord_2914953 prefixEnd_2914953 1496771974265438966681881 := by
  unfold tailWord_2914953
  simp only [CollatzResearch.WordTrace]
  refine ⟨106317070208630590182893513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70878046805753726788595675 106317070208630590182893513)
  ·
    refine ⟨79737802656472942637170135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106317070208630590182893513 79737802656472942637170135)
    ·
      refine ⟨119606703984709413955755203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79737802656472942637170135 119606703984709413955755203)
      ·
        refine ⟨179410055977064120933632805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119606703984709413955755203 179410055977064120933632805)
        ·
          refine ⟨33639385495699522675056151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 179410055977064120933632805 33639385495699522675056151)
          ·
            refine ⟨50459078243549284012584227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33639385495699522675056151 50459078243549284012584227)
            ·
              refine ⟨75688617365323926018876341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50459078243549284012584227 75688617365323926018876341)
              ·
                refine ⟨7095807877999118064269657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 75688617365323926018876341 7095807877999118064269657)
                ·
                  refine ⟨5321855908499338548202243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7095807877999118064269657 5321855908499338548202243)
                  ·
                    refine ⟨7982783862749007822303365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5321855908499338548202243 7982783862749007822303365)
                    ·
                      refine ⟨1496771974265438966681881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7982783862749007822303365 1496771974265438966681881)
                      ·
                        rfl

theorem cell23_2914953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 5, 2, 1, 4].length) (baseStart_2914953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2914953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2914953 prefixEnd_2914953 := by exact prefixLift 2914953
  have htrace : WordTrace (prefixWord ++ tailWord_2914953) baseStart_2914953 baseEnd_2914953 := by
    simpa [prefixWord, tailWord_2914953, baseEnd_2914953] using wordTrace_append hprefix tailTrace_2914953
  have hstable : (prefixWord ++ tailWord_2914953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2914953).length < 2 ^ (prefixWord ++ tailWord_2914953).sum := by decide
  have hdescent : baseEnd_2914953 < baseStart_2914953 := by decide
  rcases family_descends (prefixWord ++ tailWord_2914953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2914954 : List Nat := [3, 1, 2, 3, 4, 1, 1, 3, 5]
def baseStart_2914954 : Nat := 118140960795 + 2914954 * 2 ^ 59
def prefixEnd_2914954 : Nat := 4983230072969 + 3 ^ 40 * 2914954 * 2
def baseEnd_2914954 : Nat := 166308054194010384752153

theorem tailTrace_2914954 : CollatzResearch.WordTrace tailWord_2914954 prefixEnd_2914954 166308054194010384752153 := by
  unfold tailWord_2914954
  simp only [CollatzResearch.WordTrace]
  refine ⟨26579276670406741838419979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70878071121084644902453277 26579276670406741838419979)
  ·
    refine ⟨39868915005610112757629969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26579276670406741838419979 39868915005610112757629969)
    ·
      refine ⟨29901686254207584568222477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39868915005610112757629969 29901686254207584568222477)
      ·
        refine ⟨11213132345327844213083429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29901686254207584568222477 11213132345327844213083429)
        ·
          refine ⟨2102462314748970789953143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11213132345327844213083429 2102462314748970789953143)
          ·
            refine ⟨3153693472123456184929715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2102462314748970789953143 3153693472123456184929715)
            ·
              refine ⟨4730540208185184277394573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3153693472123456184929715 4730540208185184277394573)
              ·
                refine ⟨1773952578069444104022965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4730540208185184277394573 1773952578069444104022965)
                ·
                  refine ⟨166308054194010384752153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1773952578069444104022965 166308054194010384752153)
                  ·
                    rfl

theorem cell23_2914954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 1, 3, 5].length) (baseStart_2914954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2914954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2914954 prefixEnd_2914954 := by exact prefixLift 2914954
  have htrace : WordTrace (prefixWord ++ tailWord_2914954) baseStart_2914954 baseEnd_2914954 := by
    simpa [prefixWord, tailWord_2914954, baseEnd_2914954] using wordTrace_append hprefix tailTrace_2914954
  have hstable : (prefixWord ++ tailWord_2914954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2914954).length < 2 ^ (prefixWord ++ tailWord_2914954).sum := by decide
  have hdescent : baseEnd_2914954 < baseStart_2914954 := by decide
  rcases family_descends (prefixWord ++ tailWord_2914954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2915073 : List Nat := [1, 2, 4, 1, 1, 1, 1, 2, 3, 1, 6]
def baseStart_2915073 : Nat := 118140960795 + 2915073 * 2 ^ 59
def prefixEnd_2915073 : Nat := 4983230072969 + 3 ^ 40 * 2915073 * 2
def baseEnd_2915073 : Nat := 1496833591943978497181329

theorem tailTrace_2915073 : CollatzResearch.WordTrace tailWord_2915073 prefixEnd_2915073 1496833591943978497181329 := by
  unfold tailWord_2915073
  simp only [CollatzResearch.WordTrace]
  refine ⟨106321446968195850677261873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70880964645463900451507915 106321446968195850677261873)
  ·
    refine ⟨79741085226146888007946405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106321446968195850677261873 79741085226146888007946405)
    ·
      refine ⟨14951453479902541501489951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79741085226146888007946405 14951453479902541501489951)
      ·
        refine ⟨22427180219853812252234927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14951453479902541501489951 22427180219853812252234927)
        ·
          refine ⟨33640770329780718378352391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22427180219853812252234927 33640770329780718378352391)
          ·
            refine ⟨50461155494671077567528587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33640770329780718378352391 50461155494671077567528587)
            ·
              refine ⟨75691733242006616351292881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50461155494671077567528587 75691733242006616351292881)
              ·
                refine ⟨56768799931504962263469661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75691733242006616351292881 56768799931504962263469661)
                ·
                  refine ⟨21288299974314360848801123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56768799931504962263469661 21288299974314360848801123)
                  ·
                    refine ⟨31932449961471541273201685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21288299974314360848801123 31932449961471541273201685)
                    ·
                      refine ⟨1496833591943978497181329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31932449961471541273201685 1496833591943978497181329)
                      ·
                        rfl

theorem cell23_2915073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 2, 3, 1, 6].length) (baseStart_2915073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2915073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2915073 prefixEnd_2915073 := by exact prefixLift 2915073
  have htrace : WordTrace (prefixWord ++ tailWord_2915073) baseStart_2915073 baseEnd_2915073 := by
    simpa [prefixWord, tailWord_2915073, baseEnd_2915073] using wordTrace_append hprefix tailTrace_2915073
  have hstable : (prefixWord ++ tailWord_2915073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2915073).length < 2 ^ (prefixWord ++ tailWord_2915073).sum := by decide
  have hdescent : baseEnd_2915073 < baseStart_2915073 := by decide
  rcases family_descends (prefixWord ++ tailWord_2915073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2915074 : List Nat := [3, 4, 1, 1, 1, 2, 4, 1, 1, 5]
def baseStart_2915074 : Nat := 118140960795 + 2915074 * 2 ^ 59
def prefixEnd_2915074 : Nat := 4983230072969 + 3 ^ 40 * 2915074 * 2
def baseEnd_2915074 : Nat := 498944701808210997756275

theorem tailTrace_2915074 : CollatzResearch.WordTrace tailWord_2915074 prefixEnd_2915074 498944701808210997756275 := by
  unfold tailWord_2915074
  simp only [CollatzResearch.WordTrace]
  refine ⟨26580370860298056962012069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70880988960794818565365517 26580370860298056962012069)
  ·
    refine ⟨4983819536305885680377263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26580370860298056962012069 4983819536305885680377263)
    ·
      refine ⟨7475729304458828520565895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4983819536305885680377263 7475729304458828520565895)
      ·
        refine ⟨11213593956688242780848843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7475729304458828520565895 11213593956688242780848843)
        ·
          refine ⟨16820390935032364171273265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11213593956688242780848843 16820390935032364171273265)
          ·
            refine ⟨12615293201274273128454949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16820390935032364171273265 12615293201274273128454949)
            ·
              refine ⟨2365367475238926211585303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12615293201274273128454949 2365367475238926211585303)
              ·
                refine ⟨3548051212858389317377955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2365367475238926211585303 3548051212858389317377955)
                ·
                  refine ⟨5322076819287583976066933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3548051212858389317377955 5322076819287583976066933)
                  ·
                    refine ⟨498944701808210997756275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5322076819287583976066933 498944701808210997756275)
                    ·
                      rfl

theorem cell23_2915074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 4, 1, 1, 5].length) (baseStart_2915074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2915074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2915074 prefixEnd_2915074 := by exact prefixLift 2915074
  have htrace : WordTrace (prefixWord ++ tailWord_2915074) baseStart_2915074 baseEnd_2915074 := by
    simpa [prefixWord, tailWord_2915074, baseEnd_2915074] using wordTrace_append hprefix tailTrace_2915074
  have hstable : (prefixWord ++ tailWord_2915074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2915074).length < 2 ^ (prefixWord ++ tailWord_2915074).sum := by decide
  have hdescent : baseEnd_2915074 < baseStart_2915074 := by decide
  rcases family_descends (prefixWord ++ tailWord_2915074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2915104 : List Nat := [2, 1, 1, 5, 1, 3, 3, 1, 2, 4]
def baseStart_2915104 : Nat := 118140960795 + 2915104 * 2 ^ 59
def prefixEnd_2915104 : Nat := 4983230072969 + 3 ^ 40 * 2915104 * 2
def baseEnd_2915104 : Nat := 498949836614755958631229

theorem tailTrace_2915104 : CollatzResearch.WordTrace tailWord_2915104 prefixEnd_2915104 498949836614755958631229 := by
  unfold tailWord_2915104
  simp only [CollatzResearch.WordTrace]
  refine ⟨53161288815541771485820183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70881718420722361981093577 53161288815541771485820183)
  ·
    refine ⟨79741933223312657228730275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53161288815541771485820183 79741933223312657228730275)
    ·
      refine ⟨119612899834968985843095413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79741933223312657228730275 119612899834968985843095413)
      ·
        refine ⟨11213709359528342422790195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 119612899834968985843095413 11213709359528342422790195)
        ·
          refine ⟨16820564039292513634185293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11213709359528342422790195 16820564039292513634185293)
          ·
            refine ⟨6307711514734692612819485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16820564039292513634185293 6307711514734692612819485)
            ·
              refine ⟨2365391818025509729807307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6307711514734692612819485 2365391818025509729807307)
              ·
                refine ⟨3548087727038264594710961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2365391818025509729807307 3548087727038264594710961)
                ·
                  refine ⟨2661065795278698446033221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3548087727038264594710961 2661065795278698446033221)
                  ·
                    refine ⟨498949836614755958631229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2661065795278698446033221 498949836614755958631229)
                    ·
                      rfl

theorem cell23_2915104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 3, 1, 2, 4].length) (baseStart_2915104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2915104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2915104 prefixEnd_2915104 := by exact prefixLift 2915104
  have htrace : WordTrace (prefixWord ++ tailWord_2915104) baseStart_2915104 baseEnd_2915104 := by
    simpa [prefixWord, tailWord_2915104, baseEnd_2915104] using wordTrace_append hprefix tailTrace_2915104
  have hstable : (prefixWord ++ tailWord_2915104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2915104).length < 2 ^ (prefixWord ++ tailWord_2915104).sum := by decide
  have hdescent : baseEnd_2915104 < baseStart_2915104 := by decide
  rcases family_descends (prefixWord ++ tailWord_2915104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2915120 : List Nat := [2, 1, 1, 1, 2, 2, 1, 2, 2, 7, 2]
def baseStart_2915120 : Nat := 118140960795 + 2915120 * 2 ^ 59
def prefixEnd_2915120 : Nat := 4983230072969 + 3 ^ 40 * 2915120 * 2
def baseEnd_2915120 : Nat := 1496857725534739813293613

theorem tailTrace_2915120 : CollatzResearch.WordTrace tailWord_2915120 prefixEnd_2915120 1496857725534739813293613 := by
  unfold tailWord_2915120
  simp only [CollatzResearch.WordTrace]
  refine ⟨53161580599512788852111407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70882107466017051802815209 53161580599512788852111407)
  ·
    refine ⟨79742370899269183278167111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53161580599512788852111407 79742370899269183278167111)
    ·
      refine ⟨119613556348903774917250667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79742370899269183278167111 119613556348903774917250667)
      ·
        refine ⟨179420334523355662375876001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119613556348903774917250667 179420334523355662375876001)
        ·
          refine ⟨134565250892516746781907001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179420334523355662375876001 134565250892516746781907001)
          ·
            refine ⟨100923938169387560086430251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134565250892516746781907001 100923938169387560086430251)
            ·
              refine ⟨151385907254081340129645377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100923938169387560086430251 151385907254081340129645377)
              ·
                refine ⟨113539430440561005097234033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 151385907254081340129645377 113539430440561005097234033)
                ·
                  refine ⟨85154572830420753822925525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 113539430440561005097234033 85154572830420753822925525)
                  ·
                    refine ⟨1995810300712986417724817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 85154572830420753822925525 1995810300712986417724817)
                    ·
                      refine ⟨1496857725534739813293613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1995810300712986417724817 1496857725534739813293613)
                      ·
                        rfl

theorem cell23_2915120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 2, 7, 2].length) (baseStart_2915120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2915120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2915120 prefixEnd_2915120 := by exact prefixLift 2915120
  have htrace : WordTrace (prefixWord ++ tailWord_2915120) baseStart_2915120 baseEnd_2915120 := by
    simpa [prefixWord, tailWord_2915120, baseEnd_2915120] using wordTrace_append hprefix tailTrace_2915120
  have hstable : (prefixWord ++ tailWord_2915120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2915120).length < 2 ^ (prefixWord ++ tailWord_2915120).sum := by decide
  have hdescent : baseEnd_2915120 < baseStart_2915120 := by decide
  rcases family_descends (prefixWord ++ tailWord_2915120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2915161 : List Nat := [1, 2, 1, 2, 2, 6, 2, 1, 2, 1, 3]
def baseStart_2915161 : Nat := 118140960795 + 2915161 * 2 ^ 59
def prefixEnd_2915161 : Nat := 4983230072969 + 3 ^ 40 * 2915161 * 2
def baseEnd_2915161 : Nat := 1496878778241574152880925

theorem tailTrace_2915161 : CollatzResearch.WordTrace tailWord_2915161 prefixEnd_2915161 1496878778241574152880925 := by
  unfold tailWord_2915161
  simp only [CollatzResearch.WordTrace]
  refine ⟨106324656591877041706465337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70883104394584694470976891 106324656591877041706465337)
  ·
    refine ⟨79743492443907781279849003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106324656591877041706465337 79743492443907781279849003)
    ·
      refine ⟨119615238665861671919773505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79743492443907781279849003 119615238665861671919773505)
      ·
        refine ⟨89711428999396253939830129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119615238665861671919773505 89711428999396253939830129)
        ·
          refine ⟨67283571749547190454872597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89711428999396253939830129 67283571749547190454872597)
          ·
            refine ⟨3153917425760024552572153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 67283571749547190454872597 3153917425760024552572153)
            ·
              refine ⟨2365438069320018414429115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3153917425760024552572153 2365438069320018414429115)
              ·
                refine ⟨3548157103980027621643673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2365438069320018414429115 3548157103980027621643673)
                ·
                  refine ⟨2661117827985020716232755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3548157103980027621643673 2661117827985020716232755)
                  ·
                    refine ⟨3991676741977531074349133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2661117827985020716232755 3991676741977531074349133)
                    ·
                      refine ⟨1496878778241574152880925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3991676741977531074349133 1496878778241574152880925)
                      ·
                        rfl

theorem cell23_2915161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 2, 1, 2, 1, 3].length) (baseStart_2915161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2915161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2915161 prefixEnd_2915161 := by exact prefixLift 2915161
  have htrace : WordTrace (prefixWord ++ tailWord_2915161) baseStart_2915161 baseEnd_2915161 := by
    simpa [prefixWord, tailWord_2915161, baseEnd_2915161] using wordTrace_append hprefix tailTrace_2915161
  have hstable : (prefixWord ++ tailWord_2915161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2915161).length < 2 ^ (prefixWord ++ tailWord_2915161).sum := by decide
  have hdescent : baseEnd_2915161 < baseStart_2915161 := by decide
  rcases family_descends (prefixWord ++ tailWord_2915161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2915167 : List Nat := [1, 1, 2, 3, 1, 3, 2, 3, 1, 4, 2]
def baseStart_2915167 : Nat := 118140960795 + 2915167 * 2 ^ 59
def prefixEnd_2915167 : Nat := 4983230072969 + 3 ^ 40 * 2915167 * 2
def baseEnd_2915167 : Nat := 1496881859125501129405897

theorem tailTrace_2915167 : CollatzResearch.WordTrace tailWord_2915167 prefixEnd_2915167 1496881859125501129405897 := by
  unfold tailWord_2915167
  simp only [CollatzResearch.WordTrace]
  refine ⟨106324875429855304731183755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70883250286570203154122503 106324875429855304731183755)
  ·
    refine ⟨159487313144782957096775633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106324875429855304731183755 159487313144782957096775633)
    ·
      refine ⟨119615484858587217822581725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159487313144782957096775633 119615484858587217822581725)
      ·
        refine ⟨44855806821970206683468147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119615484858587217822581725 44855806821970206683468147)
        ·
          refine ⟨67283710232955310025202221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44855806821970206683468147 67283710232955310025202221)
          ·
            refine ⟨25231391337358241259450833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67283710232955310025202221 25231391337358241259450833)
            ·
              refine ⟨18923543503018680944588125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25231391337358241259450833 18923543503018680944588125)
              ·
                refine ⟨7096328813632005354220547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18923543503018680944588125 7096328813632005354220547)
                ·
                  refine ⟨10644493220448008031330821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7096328813632005354220547 10644493220448008031330821)
                  ·
                    refine ⟨1995842478834001505874529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10644493220448008031330821 1995842478834001505874529)
                    ·
                      refine ⟨1496881859125501129405897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1995842478834001505874529 1496881859125501129405897)
                      ·
                        rfl

theorem cell23_2915167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 3, 1, 4, 2].length) (baseStart_2915167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2915167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2915167 prefixEnd_2915167 := by exact prefixLift 2915167
  have htrace : WordTrace (prefixWord ++ tailWord_2915167) baseStart_2915167 baseEnd_2915167 := by
    simpa [prefixWord, tailWord_2915167, baseEnd_2915167] using wordTrace_append hprefix tailTrace_2915167
  have hstable : (prefixWord ++ tailWord_2915167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2915167).length < 2 ^ (prefixWord ++ tailWord_2915167).sum := by decide
  have hdescent : baseEnd_2915167 < baseStart_2915167 := by decide
  rcases family_descends (prefixWord ++ tailWord_2915167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2915171 : List Nat := [1, 1, 1, 5, 3, 3, 1, 2, 1, 3, 2]
def baseStart_2915171 : Nat := 118140960795 + 2915171 * 2 ^ 59
def prefixEnd_2915171 : Nat := 4983230072969 + 3 ^ 40 * 2915171 * 2
def baseEnd_2915171 : Nat := 1496883913048119113755879

theorem tailTrace_2915171 : CollatzResearch.WordTrace tailWord_2915171 prefixEnd_2915171 1496883913048119113755879 := by
  unfold tailWord_2915171
  simp only [CollatzResearch.WordTrace]
  refine ⟨106325021321840813414329367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70883347547893875609552911 106325021321840813414329367)
  ·
    refine ⟨159487531982761220121494051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106325021321840813414329367 159487531982761220121494051)
    ·
      refine ⟨239231297974141830182241077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159487531982761220121494051 239231297974141830182241077)
      ·
        refine ⟨22427934185075796579585101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 239231297974141830182241077 22427934185075796579585101)
        ·
          refine ⟨8410475319403423717344413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22427934185075796579585101 8410475319403423717344413)
          ·
            refine ⟨3153928244776283894004155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8410475319403423717344413 3153928244776283894004155)
            ·
              refine ⟨4730892367164425841006233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3153928244776283894004155 4730892367164425841006233)
              ·
                refine ⟨3548169275373319380754675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4730892367164425841006233 3548169275373319380754675)
                ·
                  refine ⟨5322253913059979071132013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3548169275373319380754675 5322253913059979071132013)
                  ·
                    refine ⟨1995845217397492151674505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5322253913059979071132013 1995845217397492151674505)
                    ·
                      refine ⟨1496883913048119113755879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1995845217397492151674505 1496883913048119113755879)
                      ·
                        rfl

theorem cell23_2915171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 1, 2, 1, 3, 2].length) (baseStart_2915171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2915171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2915171 prefixEnd_2915171 := by exact prefixLift 2915171
  have htrace : WordTrace (prefixWord ++ tailWord_2915171) baseStart_2915171 baseEnd_2915171 := by
    simpa [prefixWord, tailWord_2915171, baseEnd_2915171] using wordTrace_append hprefix tailTrace_2915171
  have hstable : (prefixWord ++ tailWord_2915171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2915171).length < 2 ^ (prefixWord ++ tailWord_2915171).sum := by decide
  have hdescent : baseEnd_2915171 < baseStart_2915171 := by decide
  rcases family_descends (prefixWord ++ tailWord_2915171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2915284 : List Nat := [2, 4, 1, 2, 1, 2, 2, 2, 3, 4]
def baseStart_2915284 : Nat := 118140960795 + 2915284 * 2 ^ 59
def prefixEnd_2915284 : Nat := 4983230072969 + 3 ^ 40 * 2915284 * 2
def baseEnd_2915284 : Nat := 498980645454025723880953

theorem tailTrace_2915284 : CollatzResearch.WordTrace tailWord_2915284 prefixEnd_2915284 498980645454025723880953 := by
  unfold tailWord_2915284
  simp only [CollatzResearch.WordTrace]
  refine ⟨53164571385215716856596453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70886095180287622475461937 53164571385215716856596453)
  ·
    refine ⟨9968357134727946910611835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53164571385215716856596453 9968357134727946910611835)
    ·
      refine ⟨14952535702091920365917753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9968357134727946910611835 14952535702091920365917753)
      ·
        refine ⟨11214401776568940274438315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14952535702091920365917753 11214401776568940274438315)
        ·
          refine ⟨16821602664853410411657473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11214401776568940274438315 16821602664853410411657473)
          ·
            refine ⟨12616201998640057808743105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16821602664853410411657473 12616201998640057808743105)
            ·
              refine ⟨9462151498980043356557329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12616201998640057808743105 9462151498980043356557329)
              ·
                refine ⟨7096613624235032517417997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9462151498980043356557329 7096613624235032517417997)
                ·
                  refine ⟨2661230109088137194031749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7096613624235032517417997 2661230109088137194031749)
                  ·
                    refine ⟨498980645454025723880953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2661230109088137194031749 498980645454025723880953)
                    ·
                      rfl

theorem cell23_2915284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 2, 3, 4].length) (baseStart_2915284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2915284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2915284 prefixEnd_2915284 := by exact prefixLift 2915284
  have htrace : WordTrace (prefixWord ++ tailWord_2915284) baseStart_2915284 baseEnd_2915284 := by
    simpa [prefixWord, tailWord_2915284, baseEnd_2915284] using wordTrace_append hprefix tailTrace_2915284
  have hstable : (prefixWord ++ tailWord_2915284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2915284).length < 2 ^ (prefixWord ++ tailWord_2915284).sum := by decide
  have hdescent : baseEnd_2915284 < baseStart_2915284 := by decide
  rcases family_descends (prefixWord ++ tailWord_2915284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2915300 : List Nat := [2, 3, 1, 1, 1, 1, 2, 2, 1, 1, 8]
def baseStart_2915300 : Nat := 118140960795 + 2915300 * 2 ^ 59
def prefixEnd_2915300 : Nat := 4983230072969 + 3 ^ 40 * 2915300 * 2
def baseEnd_2915300 : Nat := 1496950152052549109042785

theorem tailTrace_2915300 : CollatzResearch.WordTrace tailWord_2915300 prefixEnd_2915300 1496950152052549109042785 := by
  unfold tailWord_2915300
  simp only [CollatzResearch.WordTrace]
  refine ⟨53164863169186734222887677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70886484225582312297183569 53164863169186734222887677)
  ·
    refine ⟨19936823688445025333582879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53164863169186734222887677 19936823688445025333582879)
    ·
      refine ⟨29905235532667538000374319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19936823688445025333582879 29905235532667538000374319)
      ·
        refine ⟨44857853299001307000561479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29905235532667538000374319 44857853299001307000561479)
        ·
          refine ⟨67286779948501960500842219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44857853299001307000561479 67286779948501960500842219)
          ·
            refine ⟨100930169922752940751263329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67286779948501960500842219 100930169922752940751263329)
            ·
              refine ⟨75697627442064705563447497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100930169922752940751263329 75697627442064705563447497)
              ·
                refine ⟨56773220581548529172585623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75697627442064705563447497 56773220581548529172585623)
                ·
                  refine ⟨85159830872322793758878435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56773220581548529172585623 85159830872322793758878435)
                  ·
                    refine ⟨127739746308484190638317653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 85159830872322793758878435 127739746308484190638317653)
                    ·
                      refine ⟨1496950152052549109042785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 127739746308484190638317653 1496950152052549109042785)
                      ·
                        rfl

theorem cell23_2915300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 1, 1, 8].length) (baseStart_2915300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2915300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2915300 prefixEnd_2915300 := by exact prefixLift 2915300
  have htrace : WordTrace (prefixWord ++ tailWord_2915300) baseStart_2915300 baseEnd_2915300 := by
    simpa [prefixWord, tailWord_2915300, baseEnd_2915300] using wordTrace_append hprefix tailTrace_2915300
  have hstable : (prefixWord ++ tailWord_2915300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2915300).length < 2 ^ (prefixWord ++ tailWord_2915300).sum := by decide
  have hdescent : baseEnd_2915300 < baseStart_2915300 := by decide
  rcases family_descends (prefixWord ++ tailWord_2915300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2915320 : List Nat := [2, 1, 2, 1, 1, 3, 1, 2, 2, 1, 7]
def baseStart_2915320 : Nat := 118140960795 + 2915320 * 2 ^ 59
def prefixEnd_2915320 : Nat := 4983230072969 + 3 ^ 40 * 2915320 * 2
def baseEnd_2915320 : Nat := 1496960421665639030792693

theorem tailTrace_2915320 : CollatzResearch.WordTrace tailWord_2915320 prefixEnd_2915320 1496960421665639030792693 := by
  unfold tailWord_2915320
  simp only [CollatzResearch.WordTrace]
  refine ⟨53165227899150505930751707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70886970532200674574335609 53165227899150505930751707)
  ·
    refine ⟨79747841848725758896127561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53165227899150505930751707 79747841848725758896127561)
    ·
      refine ⟨59810881386544319172095671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79747841848725758896127561 59810881386544319172095671)
      ·
        refine ⟨89716322079816478758143507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59810881386544319172095671 89716322079816478758143507)
        ·
          refine ⟨134574483119724718137215261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89716322079816478758143507 134574483119724718137215261)
          ·
            refine ⟨50465431169896769301455723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 134574483119724718137215261 50465431169896769301455723)
            ·
              refine ⟨75698146754845153952183585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50465431169896769301455723 75698146754845153952183585)
              ·
                refine ⟨56773610066133865464137689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75698146754845153952183585 56773610066133865464137689)
                ·
                  refine ⟨42580207549600399098103267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56773610066133865464137689 42580207549600399098103267)
                  ·
                    refine ⟨63870311324400598647154901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42580207549600399098103267 63870311324400598647154901)
                    ·
                      refine ⟨1496960421665639030792693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 63870311324400598647154901 1496960421665639030792693)
                      ·
                        rfl

theorem cell23_2915320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 2, 1, 7].length) (baseStart_2915320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2915320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2915320 prefixEnd_2915320 := by exact prefixLift 2915320
  have htrace : WordTrace (prefixWord ++ tailWord_2915320) baseStart_2915320 baseEnd_2915320 := by
    simpa [prefixWord, tailWord_2915320, baseEnd_2915320] using wordTrace_append hprefix tailTrace_2915320
  have hstable : (prefixWord ++ tailWord_2915320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2915320).length < 2 ^ (prefixWord ++ tailWord_2915320).sum := by decide
  have hdescent : baseEnd_2915320 < baseStart_2915320 := by decide
  rcases family_descends (prefixWord ++ tailWord_2915320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2915351 : List Nat := [1, 1, 3, 5, 1, 1, 1, 3, 2, 3, 2]
def baseStart_2915351 : Nat := 118140960795 + 2915351 * 2 ^ 59
def prefixEnd_2915351 : Nat := 4983230072969 + 3 ^ 40 * 2915351 * 2
def baseEnd_2915351 : Nat := 1496976339565928409505051

theorem tailTrace_2915351 : CollatzResearch.WordTrace tailWord_2915351 prefixEnd_2915351 1496976339565928409505051 := by
  unfold tailWord_2915351
  simp only [CollatzResearch.WordTrace]
  refine ⟨106331586461188704155881907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70887724307459136103921271 106331586461188704155881907)
  ·
    refine ⟨159497379691783056233822861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106331586461188704155881907 159497379691783056233822861)
    ·
      refine ⟨59811517384418646087683573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 159497379691783056233822861 59811517384418646087683573)
      ·
        refine ⟨5607329754789248070720335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 59811517384418646087683573 5607329754789248070720335)
        ·
          refine ⟨8410994632183872106080503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5607329754789248070720335 8410994632183872106080503)
          ·
            refine ⟨12616491948275808159120755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8410994632183872106080503 12616491948275808159120755)
            ·
              refine ⟨18924737922413712238681133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12616491948275808159120755 18924737922413712238681133)
              ·
                refine ⟨7096776720905142089505425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18924737922413712238681133 7096776720905142089505425)
                ·
                  refine ⟨5322582540678856567129069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7096776720905142089505425 5322582540678856567129069)
                  ·
                    refine ⟨1995968452754571212673401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5322582540678856567129069 1995968452754571212673401)
                    ·
                      refine ⟨1496976339565928409505051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1995968452754571212673401 1496976339565928409505051)
                      ·
                        rfl

theorem cell23_2915351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 3, 2, 3, 2].length) (baseStart_2915351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2915351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2915351 prefixEnd_2915351 := by exact prefixLift 2915351
  have htrace : WordTrace (prefixWord ++ tailWord_2915351) baseStart_2915351 baseEnd_2915351 := by
    simpa [prefixWord, tailWord_2915351, baseEnd_2915351] using wordTrace_append hprefix tailTrace_2915351
  have hstable : (prefixWord ++ tailWord_2915351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2915351).length < 2 ^ (prefixWord ++ tailWord_2915351).sum := by decide
  have hdescent : baseEnd_2915351 < baseStart_2915351 := by decide
  rcases family_descends (prefixWord ++ tailWord_2915351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2915361 : List Nat := [1, 2, 3, 2, 3, 2, 3, 1, 1, 5]
def baseStart_2915361 : Nat := 118140960795 + 2915361 * 2 ^ 59
def prefixEnd_2915361 : Nat := 4983230072969 + 3 ^ 40 * 2915361 * 2
def baseEnd_2915361 : Nat := 498993824790824456793335

theorem tailTrace_2915361 : CollatzResearch.WordTrace tailWord_2915361 prefixEnd_2915361 498993824790824456793335 := by
  unfold tailWord_2915361
  simp only [CollatzResearch.WordTrace]
  refine ⟨106331951191152475863745937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70887967460768317242497291 106331951191152475863745937)
  ·
    refine ⟨79748963393364356897809453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106331951191152475863745937 79748963393364356897809453)
    ·
      refine ⟨29905861272511633836678545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79748963393364356897809453 29905861272511633836678545)
      ·
        refine ⟨22429395954383725377508909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29905861272511633836678545 22429395954383725377508909)
        ·
          refine ⟨8411023482893897016565841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22429395954383725377508909 8411023482893897016565841)
          ·
            refine ⟨6308267612170422762424381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8411023482893897016565841 6308267612170422762424381)
            ·
              refine ⟨2365600354563908535909143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6308267612170422762424381 2365600354563908535909143)
              ·
                refine ⟨3548400531845862803863715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2365600354563908535909143 3548400531845862803863715)
                ·
                  refine ⟨5322600797768794205795573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3548400531845862803863715 5322600797768794205795573)
                  ·
                    refine ⟨498993824790824456793335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5322600797768794205795573 498993824790824456793335)
                    ·
                      rfl

theorem cell23_2915361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 3, 1, 1, 5].length) (baseStart_2915361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2915361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2915361 prefixEnd_2915361 := by exact prefixLift 2915361
  have htrace : WordTrace (prefixWord ++ tailWord_2915361) baseStart_2915361 baseEnd_2915361 := by
    simpa [prefixWord, tailWord_2915361, baseEnd_2915361] using wordTrace_append hprefix tailTrace_2915361
  have hstable : (prefixWord ++ tailWord_2915361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2915361).length < 2 ^ (prefixWord ++ tailWord_2915361).sum := by decide
  have hdescent : baseEnd_2915361 < baseStart_2915361 := by decide
  rcases family_descends (prefixWord ++ tailWord_2915361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2915377 : List Nat := [1, 2, 2, 3, 1, 2, 1, 2, 3, 2, 4]
def baseStart_2915377 : Nat := 118140960795 + 2915377 * 2 ^ 59
def prefixEnd_2915377 : Nat := 4983230072969 + 3 ^ 40 * 2915377 * 2
def baseEnd_2915377 : Nat := 1496989690062945307779931

theorem tailTrace_2915377 : CollatzResearch.WordTrace tailWord_2915377 prefixEnd_2915377 1496989690062945307779931 := by
  unfold tailWord_2915377
  simp only [CollatzResearch.WordTrace]
  refine ⟨106332534759094510596328385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70888356506063007064218923 106332534759094510596328385)
  ·
    refine ⟨79749401069320882947246289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106332534759094510596328385 79749401069320882947246289)
    ·
      refine ⟨59812050801990662210434717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79749401069320882947246289 59812050801990662210434717)
      ·
        refine ⟨22429519050746498328913019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59812050801990662210434717 22429519050746498328913019)
        ·
          refine ⟨33644278576119747493369529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22429519050746498328913019 33644278576119747493369529)
          ·
            refine ⟨25233208932089810620027147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33644278576119747493369529 25233208932089810620027147)
            ·
              refine ⟨37849813398134715930040721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25233208932089810620027147 37849813398134715930040721)
              ·
                refine ⟨28387360048601036947530541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37849813398134715930040721 28387360048601036947530541)
                ·
                  refine ⟨10645260018225388855323953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28387360048601036947530541 10645260018225388855323953)
                  ·
                    refine ⟨7983945013669041641492965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10645260018225388855323953 7983945013669041641492965)
                    ·
                      refine ⟨1496989690062945307779931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7983945013669041641492965 1496989690062945307779931)
                      ·
                        rfl

theorem cell23_2915377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 2, 3, 2, 4].length) (baseStart_2915377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2915377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2915377 prefixEnd_2915377 := by exact prefixLift 2915377
  have htrace : WordTrace (prefixWord ++ tailWord_2915377) baseStart_2915377 baseEnd_2915377 := by
    simpa [prefixWord, tailWord_2915377, baseEnd_2915377] using wordTrace_append hprefix tailTrace_2915377
  have hstable : (prefixWord ++ tailWord_2915377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2915377).length < 2 ^ (prefixWord ++ tailWord_2915377).sum := by decide
  have hdescent : baseEnd_2915377 < baseStart_2915377 := by decide
  rcases family_descends (prefixWord ++ tailWord_2915377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2915381 : List Nat := [1, 3, 3, 1, 1, 1, 1, 5, 3, 2, 2]
def baseStart_2915381 : Nat := 118140960795 + 2915381 * 2 ^ 59
def prefixEnd_2915381 : Nat := 4983230072969 + 3 ^ 40 * 2915381 * 2
def baseEnd_2915381 : Nat := 1496991743985563292129913

theorem tailTrace_2915381 : CollatzResearch.WordTrace tailWord_2915381 prefixEnd_2915381 1496991743985563292129913 := by
  unfold tailWord_2915381
  simp only [CollatzResearch.WordTrace]
  refine ⟨106332680651080019279473997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70888453767386679519649331 106332680651080019279473997)
  ·
    refine ⟨39874755244155007229802749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106332680651080019279473997 39874755244155007229802749)
    ·
      refine ⟨14953033216558127711176031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39874755244155007229802749 14953033216558127711176031)
      ·
        refine ⟨22429549824837191566764047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14953033216558127711176031 22429549824837191566764047)
        ·
          refine ⟨33644324737255787350146071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22429549824837191566764047 33644324737255787350146071)
          ·
            refine ⟨50466487105883681025219107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33644324737255787350146071 50466487105883681025219107)
            ·
              refine ⟨75699730658825521537828661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50466487105883681025219107 75699730658825521537828661)
              ·
                refine ⟨7096849749264892644171437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 75699730658825521537828661 7096849749264892644171437)
                ·
                  refine ⟨2661318655974334741564289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7096849749264892644171437 2661318655974334741564289)
                  ·
                    refine ⟨1995988991980751056173217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2661318655974334741564289 1995988991980751056173217)
                    ·
                      refine ⟨1496991743985563292129913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1995988991980751056173217 1496991743985563292129913)
                      ·
                        rfl

theorem cell23_2915381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 5, 3, 2, 2].length) (baseStart_2915381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2915381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2915381 prefixEnd_2915381 := by exact prefixLift 2915381
  have htrace : WordTrace (prefixWord ++ tailWord_2915381) baseStart_2915381 baseEnd_2915381 := by
    simpa [prefixWord, tailWord_2915381, baseEnd_2915381] using wordTrace_append hprefix tailTrace_2915381
  have hstable : (prefixWord ++ tailWord_2915381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2915381).length < 2 ^ (prefixWord ++ tailWord_2915381).sum := by decide
  have hdescent : baseEnd_2915381 < baseStart_2915381 := by decide
  rcases family_descends (prefixWord ++ tailWord_2915381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2915384 : List Nat := [2, 1, 2, 1, 5, 1, 1, 2, 3, 2, 3]
def baseStart_2915384 : Nat := 118140960795 + 2915384 * 2 ^ 59
def prefixEnd_2915384 : Nat := 4983230072969 + 3 ^ 40 * 2915384 * 2
def baseEnd_2915384 : Nat := 1496993284427526780392399

theorem tailTrace_2915384 : CollatzResearch.WordTrace tailWord_2915384 prefixEnd_2915384 1496993284427526780392399 := by
  unfold tailWord_2915384
  simp only [CollatzResearch.WordTrace]
  refine ⟨53166395035034575395916603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70888526713379433861222137 53166395035034575395916603)
  ·
    refine ⟨79749592552551863093874905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53166395035034575395916603 79749592552551863093874905)
    ·
      refine ⟨59812194414413897320406179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79749592552551863093874905 59812194414413897320406179)
      ·
        refine ⟨89718291621620845980609269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59812194414413897320406179 89718291621620845980609269)
        ·
          refine ⟨8411089839526954310682119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 89718291621620845980609269 8411089839526954310682119)
          ·
            refine ⟨12616634759290431466023179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8411089839526954310682119 12616634759290431466023179)
            ·
              refine ⟨18924952138935647199034769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12616634759290431466023179 18924952138935647199034769)
              ·
                refine ⟨14193714104201735399276077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18924952138935647199034769 14193714104201735399276077)
                ·
                  refine ⟨5322642789075650774728529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14193714104201735399276077 5322642789075650774728529)
                  ·
                    refine ⟨3991982091806738081046397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5322642789075650774728529 3991982091806738081046397)
                    ·
                      refine ⟨1496993284427526780392399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3991982091806738081046397 1496993284427526780392399)
                      ·
                        rfl

theorem cell23_2915384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 2, 3, 2, 3].length) (baseStart_2915384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2915384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2915384 prefixEnd_2915384 := by exact prefixLift 2915384
  have htrace : WordTrace (prefixWord ++ tailWord_2915384) baseStart_2915384 baseEnd_2915384 := by
    simpa [prefixWord, tailWord_2915384, baseEnd_2915384] using wordTrace_append hprefix tailTrace_2915384
  have hstable : (prefixWord ++ tailWord_2915384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2915384).length < 2 ^ (prefixWord ++ tailWord_2915384).sum := by decide
  have hdescent : baseEnd_2915384 < baseStart_2915384 := by decide
  rcases family_descends (prefixWord ++ tailWord_2915384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2915431 : List Nat := [1, 1, 5, 1, 1, 4, 1, 1, 4, 1, 3]
def baseStart_2915431 : Nat := 118140960795 + 2915431 * 2 ^ 59
def prefixEnd_2915431 : Nat := 4983230072969 + 3 ^ 40 * 2915431 * 2
def baseEnd_2915431 : Nat := 1497017418018288096504683

theorem tailTrace_2915431 : CollatzResearch.WordTrace tailWord_2915431 prefixEnd_2915431 1497017418018288096504683 := by
  unfold tailWord_2915431
  simp only [CollatzResearch.WordTrace]
  refine ⟨106334504300898877818794147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70889669533932585212529431 106334504300898877818794147)
  ·
    refine ⟨159501756451348316728191221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106334504300898877818794147 159501756451348316728191221)
    ·
      refine ⟨14953289667313904693267927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 159501756451348316728191221 14953289667313904693267927)
      ·
        refine ⟨22429934500970857039901891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14953289667313904693267927 22429934500970857039901891)
        ·
          refine ⟨33644901751456285559852837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22429934500970857039901891 33644901751456285559852837)
          ·
            refine ⟨6308419078398053542472407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33644901751456285559852837 6308419078398053542472407)
            ·
              refine ⟨9462628617597080313708611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6308419078398053542472407 9462628617597080313708611)
              ·
                refine ⟨14193942926395620470562917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9462628617597080313708611 14193942926395620470562917)
                ·
                  refine ⟨2661364298699178838230547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14193942926395620470562917 2661364298699178838230547)
                  ·
                    refine ⟨3992046448048768257345821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2661364298699178838230547 3992046448048768257345821)
                    ·
                      refine ⟨1497017418018288096504683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3992046448048768257345821 1497017418018288096504683)
                      ·
                        rfl

theorem cell23_2915431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 1, 4, 1, 3].length) (baseStart_2915431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2915431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2915431 prefixEnd_2915431 := by exact prefixLift 2915431
  have htrace : WordTrace (prefixWord ++ tailWord_2915431) baseStart_2915431 baseEnd_2915431 := by
    simpa [prefixWord, tailWord_2915431, baseEnd_2915431] using wordTrace_append hprefix tailTrace_2915431
  have hstable : (prefixWord ++ tailWord_2915431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2915431).length < 2 ^ (prefixWord ++ tailWord_2915431).sum := by decide
  have hdescent : baseEnd_2915431 < baseStart_2915431 := by decide
  rcases family_descends (prefixWord ++ tailWord_2915431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2915445 : List Nat := [1, 3, 4, 3, 2, 1, 1, 1, 1, 2, 4]
def baseStart_2915445 : Nat := 118140960795 + 2915445 * 2 ^ 59
def prefixEnd_2915445 : Nat := 4983230072969 + 3 ^ 40 * 2915445 * 2
def baseEnd_2915445 : Nat := 1497024606747451041729619

theorem tailTrace_2915445 : CollatzResearch.WordTrace tailWord_2915445 prefixEnd_2915445 1497024606747451041729619 := by
  unfold tailWord_2915445
  simp only [CollatzResearch.WordTrace]
  refine ⟨106335014922848158209803789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70890009948565438806535859 106335014922848158209803789)
  ·
    refine ⟨39875630596068059328676421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106335014922848158209803789 39875630596068059328676421)
    ·
      refine ⟨7476680736762761124126829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39875630596068059328676421 7476680736762761124126829)
      ·
        refine ⟨2803755276286035421547561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7476680736762761124126829 2803755276286035421547561)
        ·
          refine ⟨2102816457214526566160671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2803755276286035421547561 2102816457214526566160671)
          ·
            refine ⟨3154224685821789849241007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2102816457214526566160671 3154224685821789849241007)
            ·
              refine ⟨4731337028732684773861511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3154224685821789849241007 4731337028732684773861511)
              ·
                refine ⟨7097005543099027160792267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4731337028732684773861511 7097005543099027160792267)
                ·
                  refine ⟨10645508314648540741188401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7097005543099027160792267 10645508314648540741188401)
                  ·
                    refine ⟨7984131235986405555891301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10645508314648540741188401 7984131235986405555891301)
                    ·
                      refine ⟨1497024606747451041729619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7984131235986405555891301 1497024606747451041729619)
                      ·
                        rfl

theorem cell23_2915445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_2915445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2915445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2915445 prefixEnd_2915445 := by exact prefixLift 2915445
  have htrace : WordTrace (prefixWord ++ tailWord_2915445) baseStart_2915445 baseEnd_2915445 := by
    simpa [prefixWord, tailWord_2915445, baseEnd_2915445] using wordTrace_append hprefix tailTrace_2915445
  have hstable : (prefixWord ++ tailWord_2915445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2915445).length < 2 ^ (prefixWord ++ tailWord_2915445).sum := by decide
  have hdescent : baseEnd_2915445 < baseStart_2915445 := by decide
  rcases family_descends (prefixWord ++ tailWord_2915445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2915447 : List Nat := [1, 1, 3, 1, 1, 4, 1, 3, 2, 6]
def baseStart_2915447 : Nat := 118140960795 + 2915447 * 2 ^ 59
def prefixEnd_2915447 : Nat := 4983230072969 + 3 ^ 40 * 2915447 * 2
def baseEnd_2915447 : Nat := 499008544569586677968203

theorem tailTrace_2915447 : CollatzResearch.WordTrace tailWord_2915447 prefixEnd_2915447 499008544569586677968203 := by
  unfold tailWord_2915447
  simp only [CollatzResearch.WordTrace]
  refine ⟨106335087868840912551376595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70890058579227275034251063 106335087868840912551376595)
  ·
    refine ⟨159502631803261368827064893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106335087868840912551376595 159502631803261368827064893)
    ·
      refine ⟨59813486926223013310149335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 159502631803261368827064893 59813486926223013310149335)
      ·
        refine ⟨89720230389334519965224003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59813486926223013310149335 89720230389334519965224003)
        ·
          refine ⟨134580345584001779947836005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89720230389334519965224003 134580345584001779947836005)
          ·
            refine ⟨25233814797000333740219251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 134580345584001779947836005 25233814797000333740219251)
            ·
              refine ⟨37850722195500500610328877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25233814797000333740219251 37850722195500500610328877)
              ·
                refine ⟨14194020823312687728873329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37850722195500500610328877 14194020823312687728873329)
                ·
                  refine ⟨10645515617484515796654997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14194020823312687728873329 10645515617484515796654997)
                  ·
                    refine ⟨499008544569586677968203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10645515617484515796654997 499008544569586677968203)
                    ·
                      rfl

theorem cell23_2915447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 3, 2, 6].length) (baseStart_2915447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2915447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2915447 prefixEnd_2915447 := by exact prefixLift 2915447
  have htrace : WordTrace (prefixWord ++ tailWord_2915447) baseStart_2915447 baseEnd_2915447 := by
    simpa [prefixWord, tailWord_2915447, baseEnd_2915447] using wordTrace_append hprefix tailTrace_2915447
  have hstable : (prefixWord ++ tailWord_2915447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2915447).length < 2 ^ (prefixWord ++ tailWord_2915447).sum := by decide
  have hdescent : baseEnd_2915447 < baseStart_2915447 := by decide
  rcases family_descends (prefixWord ++ tailWord_2915447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2915467 : List Nat := [1, 1, 1, 1, 4, 1, 1, 4, 1, 4, 4]
def baseStart_2915467 : Nat := 118140960795 + 2915467 * 2 ^ 59
def prefixEnd_2915467 : Nat := 4983230072969 + 3 ^ 40 * 2915467 * 2
def baseEnd_2915467 : Nat := 1497035903321849955654517

theorem tailTrace_2915467 : CollatzResearch.WordTrace tailWord_2915467 prefixEnd_2915467 1497035903321849955654517 := by
  unfold tailWord_2915467
  simp only [CollatzResearch.WordTrace]
  refine ⟨106335817328768455967104655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70890544885845637311403103 106335817328768455967104655)
  ·
    refine ⟨159503725993152683950656983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106335817328768455967104655 159503725993152683950656983)
    ·
      refine ⟨239255588989729025925985475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159503725993152683950656983 239255588989729025925985475)
      ·
        refine ⟨358883383484593538888978213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239255588989729025925985475 358883383484593538888978213)
        ·
          refine ⟨67290634403361288541683415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 358883383484593538888978213 67290634403361288541683415)
          ·
            refine ⟨100935951605041932812525123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67290634403361288541683415 100935951605041932812525123)
            ·
              refine ⟨151403927407562899218787685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100935951605041932812525123 151403927407562899218787685)
              ·
                refine ⟨28388236388918043603522691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 151403927407562899218787685 28388236388918043603522691)
                ·
                  refine ⟨42582354583377065405284037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28388236388918043603522691 42582354583377065405284037)
                  ·
                    refine ⟨7984191484383199763490757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42582354583377065405284037 7984191484383199763490757)
                    ·
                      refine ⟨1497035903321849955654517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7984191484383199763490757 1497035903321849955654517)
                      ·
                        rfl

theorem cell23_2915467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 4, 1, 4, 4].length) (baseStart_2915467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2915467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2915467 prefixEnd_2915467 := by exact prefixLift 2915467
  have htrace : WordTrace (prefixWord ++ tailWord_2915467) baseStart_2915467 baseEnd_2915467 := by
    simpa [prefixWord, tailWord_2915467, baseEnd_2915467] using wordTrace_append hprefix tailTrace_2915467
  have hstable : (prefixWord ++ tailWord_2915467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2915467).length < 2 ^ (prefixWord ++ tailWord_2915467).sum := by decide
  have hdescent : baseEnd_2915467 < baseStart_2915467 := by decide
  rcases family_descends (prefixWord ++ tailWord_2915467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2915474 : List Nat := [3, 2, 3, 1, 1, 2, 1, 1, 1, 3, 5]
def baseStart_2915474 : Nat := 118140960795 + 2915474 * 2 ^ 59
def prefixEnd_2915474 : Nat := 4983230072969 + 3 ^ 40 * 2915474 * 2
def baseEnd_2915474 : Nat := 1497039497686431428266985

theorem tailTrace_2915474 : CollatzResearch.WordTrace tailWord_2915474 prefixEnd_2915474 1497039497686431428266985 := by
  unfold tailWord_2915474
  simp only [CollatzResearch.WordTrace]
  refine ⟨26584018159935774040652369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70890715093162064108406317 26584018159935774040652369)
  ·
    refine ⟨19938013619951830530489277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26584018159935774040652369 19938013619951830530489277)
    ·
      refine ⟨7476755107481936448933479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19938013619951830530489277 7476755107481936448933479)
      ·
        refine ⟨11215132661222904673400219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7476755107481936448933479 11215132661222904673400219)
        ·
          refine ⟨16822698991834357010100329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11215132661222904673400219 16822698991834357010100329)
          ·
            refine ⟨12617024243875767757575247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16822698991834357010100329 12617024243875767757575247)
            ·
              refine ⟨18925536365813651636362871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12617024243875767757575247 18925536365813651636362871)
              ·
                refine ⟨28388304548720477454544307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18925536365813651636362871 28388304548720477454544307)
                ·
                  refine ⟨42582456823080716181816461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28388304548720477454544307 42582456823080716181816461)
                  ·
                    refine ⟨15968421308655268568181173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42582456823080716181816461 15968421308655268568181173)
                    ·
                      refine ⟨1497039497686431428266985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15968421308655268568181173 1497039497686431428266985)
                      ·
                        rfl

theorem cell23_2915474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_2915474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2915474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2915474 prefixEnd_2915474 := by exact prefixLift 2915474
  have htrace : WordTrace (prefixWord ++ tailWord_2915474) baseStart_2915474 baseEnd_2915474 := by
    simpa [prefixWord, tailWord_2915474, baseEnd_2915474] using wordTrace_append hprefix tailTrace_2915474
  have hstable : (prefixWord ++ tailWord_2915474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2915474).length < 2 ^ (prefixWord ++ tailWord_2915474).sum := by decide
  have hdescent : baseEnd_2915474 < baseStart_2915474 := by decide
  rcases family_descends (prefixWord ++ tailWord_2915474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2915488 : List Nat := [2, 1, 1, 4, 2, 1, 2, 4, 2, 2, 2]
def baseStart_2915488 : Nat := 118140960795 + 2915488 * 2 ^ 59
def prefixEnd_2915488 : Nat := 4983230072969 + 3 ^ 40 * 2915488 * 2
def baseEnd_2915488 : Nat := 1497046686415594373491921

theorem tailTrace_2915488 : CollatzResearch.WordTrace tailWord_2915488 prefixEnd_2915488 1497046686415594373491921 := by
  unfold tailWord_2915488
  simp only [CollatzResearch.WordTrace]
  refine ⟨53168291630846188276809559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70891055507794917702412745 53168291630846188276809559)
  ·
    refine ⟨79752437446269282415214339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53168291630846188276809559 79752437446269282415214339)
    ·
      refine ⟨119628656169403923622821509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79752437446269282415214339 119628656169403923622821509)
      ·
        refine ⟨22430373031763235679279033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 119628656169403923622821509 22430373031763235679279033)
        ·
          refine ⟨16822779773822426759459275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22430373031763235679279033 16822779773822426759459275)
          ·
            refine ⟨25234169660733640139188913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16822779773822426759459275 25234169660733640139188913)
            ·
              refine ⟨18925627245550230104391685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25234169660733640139188913 18925627245550230104391685)
              ·
                refine ⟨3548555108540668144573441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18925627245550230104391685 3548555108540668144573441)
                ·
                  refine ⟨2661416331405501108430081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3548555108540668144573441 2661416331405501108430081)
                  ·
                    refine ⟨1996062248554125831322561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2661416331405501108430081 1996062248554125831322561)
                    ·
                      refine ⟨1497046686415594373491921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1996062248554125831322561 1497046686415594373491921)
                      ·
                        rfl

theorem cell23_2915488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 4, 2, 2, 2].length) (baseStart_2915488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2915488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2915488 prefixEnd_2915488 := by exact prefixLift 2915488
  have htrace : WordTrace (prefixWord ++ tailWord_2915488) baseStart_2915488 baseEnd_2915488 := by
    simpa [prefixWord, tailWord_2915488, baseEnd_2915488] using wordTrace_append hprefix tailTrace_2915488
  have hstable : (prefixWord ++ tailWord_2915488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2915488).length < 2 ^ (prefixWord ++ tailWord_2915488).sum := by decide
  have hdescent : baseEnd_2915488 < baseStart_2915488 := by decide
  rcases family_descends (prefixWord ++ tailWord_2915488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2915505 : List Nat := [1, 2, 2, 5, 1, 2, 1, 3, 2, 2, 2]
def baseStart_2915505 : Nat := 118140960795 + 2915505 * 2 ^ 59
def prefixEnd_2915505 : Nat := 4983230072969 + 3 ^ 40 * 2915505 * 2
def baseEnd_2915505 : Nat := 1497055415586720806979343

theorem tailTrace_2915505 : CollatzResearch.WordTrace tailWord_2915505 prefixEnd_2915505 1497055415586720806979343 := by
  unfold tailWord_2915505
  simp only [CollatzResearch.WordTrace]
  refine ⟨106337203302630788456987969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70891468868420525637991979 106337203302630788456987969)
  ·
    refine ⟨79752902476973091342740977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106337203302630788456987969 79752902476973091342740977)
    ·
      refine ⟨59814676857729818507055733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79752902476973091342740977 59814676857729818507055733)
      ·
        refine ⟨5607625955412170485036475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 59814676857729818507055733 5607625955412170485036475)
        ·
          refine ⟨8411438933118255727554713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5607625955412170485036475 8411438933118255727554713)
          ·
            refine ⟨6308579199838691795666035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8411438933118255727554713 6308579199838691795666035)
            ·
              refine ⟨9462868799758037693499053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6308579199838691795666035 9462868799758037693499053)
              ·
                refine ⟨3548575799909264135062145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9462868799758037693499053 3548575799909264135062145)
                ·
                  refine ⟨2661431849931948101296609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3548575799909264135062145 2661431849931948101296609)
                  ·
                    refine ⟨1996073887448961075972457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2661431849931948101296609 1996073887448961075972457)
                    ·
                      refine ⟨1497055415586720806979343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1996073887448961075972457 1497055415586720806979343)
                      ·
                        rfl

theorem cell23_2915505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 3, 2, 2, 2].length) (baseStart_2915505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2915505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2915505 prefixEnd_2915505 := by exact prefixLift 2915505
  have htrace : WordTrace (prefixWord ++ tailWord_2915505) baseStart_2915505 baseEnd_2915505 := by
    simpa [prefixWord, tailWord_2915505, baseEnd_2915505] using wordTrace_append hprefix tailTrace_2915505
  have hstable : (prefixWord ++ tailWord_2915505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2915505).length < 2 ^ (prefixWord ++ tailWord_2915505).sum := by decide
  have hdescent : baseEnd_2915505 < baseStart_2915505 := by decide
  rcases family_descends (prefixWord ++ tailWord_2915505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2915507 : List Nat := [1, 1, 1, 2, 3, 2, 2, 1, 3, 7]
def baseStart_2915507 : Nat := 118140960795 + 2915507 * 2 ^ 59
def prefixEnd_2915507 : Nat := 4983230072969 + 3 ^ 40 * 2915507 * 2
def baseEnd_2915507 : Nat := 499018814182676599718111

theorem tailTrace_2915507 : CollatzResearch.WordTrace tailWord_2915507 prefixEnd_2915507 499018814182676599718111 := by
  unfold tailWord_2915507
  simp only [CollatzResearch.WordTrace]
  refine ⟨106337276248623542798560775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70891517499082361865707183 106337276248623542798560775)
  ·
    refine ⟨159505914372935314197841163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106337276248623542798560775 159505914372935314197841163)
    ·
      refine ⟨239258871559402971296761745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159505914372935314197841163 239258871559402971296761745)
      ·
        refine ⟨179444153669552228472571309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 239258871559402971296761745 179444153669552228472571309)
        ·
          refine ⟨67291557626082085677214241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 179444153669552228472571309 67291557626082085677214241)
          ·
            refine ⟨50468668219561564257910681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67291557626082085677214241 50468668219561564257910681)
            ·
              refine ⟨37851501164671173193433011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50468668219561564257910681 37851501164671173193433011)
              ·
                refine ⟨56777251747006759790149517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37851501164671173193433011 56777251747006759790149517)
                ·
                  refine ⟨21291469405127534921306069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56777251747006759790149517 21291469405127534921306069)
                  ·
                    refine ⟨499018814182676599718111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21291469405127534921306069 499018814182676599718111)
                    ·
                      rfl

theorem cell23_2915507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 1, 3, 7].length) (baseStart_2915507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2915507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2915507 prefixEnd_2915507 := by exact prefixLift 2915507
  have htrace : WordTrace (prefixWord ++ tailWord_2915507) baseStart_2915507 baseEnd_2915507 := by
    simpa [prefixWord, tailWord_2915507, baseEnd_2915507] using wordTrace_append hprefix tailTrace_2915507
  have hstable : (prefixWord ++ tailWord_2915507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2915507).length < 2 ^ (prefixWord ++ tailWord_2915507).sum := by decide
  have hdescent : baseEnd_2915507 < baseStart_2915507 := by decide
  rcases family_descends (prefixWord ++ tailWord_2915507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2915522 : List Nat := [3, 5, 1, 1, 2, 1, 1, 2, 1, 4, 2]
def baseStart_2915522 : Nat := 118140960795 + 2915522 * 2 ^ 59
def prefixEnd_2915522 : Nat := 4983230072969 + 3 ^ 40 * 2915522 * 2
def baseEnd_2915522 : Nat := 1497064144757847240466765

theorem tailTrace_2915522 : CollatzResearch.WordTrace tailWord_2915522 prefixEnd_2915522 1497064144757847240466765 := by
  unfold tailWord_2915522
  simp only [CollatzResearch.WordTrace]
  refine ⟨26584455835892300090089205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70891882229046133573571213 26584455835892300090089205)
  ·
    refine ⟨2492292734614903133445863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26584455835892300090089205 2492292734614903133445863)
    ·
      refine ⟨3738439101922354700168795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2492292734614903133445863 3738439101922354700168795)
      ·
        refine ⟨5607658652883532050253193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3738439101922354700168795 5607658652883532050253193)
        ·
          refine ⟨4205743989662649037689895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5607658652883532050253193 4205743989662649037689895)
          ·
            refine ⟨6308615984493973556534843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4205743989662649037689895 6308615984493973556534843)
            ·
              refine ⟨9462923976740960334802265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6308615984493973556534843 9462923976740960334802265)
              ·
                refine ⟨7097192982555720251101699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9462923976740960334802265 7097192982555720251101699)
                ·
                  refine ⟨10645789473833580376652549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7097192982555720251101699 10645789473833580376652549)
                  ·
                    refine ⟨1996085526343796320622353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10645789473833580376652549 1996085526343796320622353)
                    ·
                      refine ⟨1497064144757847240466765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1996085526343796320622353 1497064144757847240466765)
                      ·
                        rfl

theorem cell23_2915522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 2, 1, 4, 2].length) (baseStart_2915522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2915522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2915522 prefixEnd_2915522 := by exact prefixLift 2915522
  have htrace : WordTrace (prefixWord ++ tailWord_2915522) baseStart_2915522 baseEnd_2915522 := by
    simpa [prefixWord, tailWord_2915522, baseEnd_2915522] using wordTrace_append hprefix tailTrace_2915522
  have hstable : (prefixWord ++ tailWord_2915522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2915522).length < 2 ^ (prefixWord ++ tailWord_2915522).sum := by decide
  have hdescent : baseEnd_2915522 < baseStart_2915522 := by decide
  rcases family_descends (prefixWord ++ tailWord_2915522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2915526 : List Nat := [6, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2]
def baseStart_2915526 : Nat := 118140960795 + 2915526 * 2 ^ 59
def prefixEnd_2915526 : Nat := 4983230072969 + 3 ^ 40 * 2915526 * 2
def baseEnd_2915526 : Nat := 1497066198680465224816747

theorem tailTrace_2915526 : CollatzResearch.WordTrace tailWord_2915526 prefixEnd_2915526 1497066198680465224816747 := by
  unfold tailWord_2915526
  simp only [CollatzResearch.WordTrace]
  refine ⟨3323061538611084657609451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 70891979490369806029001621 3323061538611084657609451)
  ·
    refine ⟨4984592307916626986414177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3323061538611084657609451 4984592307916626986414177)
    ·
      refine ⟨3738444230937470239810633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4984592307916626986414177 3738444230937470239810633)
      ·
        refine ⟨2803833173203102679857975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3738444230937470239810633 2803833173203102679857975)
        ·
          refine ⟨4205749759804654019786963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2803833173203102679857975 4205749759804654019786963)
          ·
            refine ⟨6308624639706981029680445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4205749759804654019786963 6308624639706981029680445)
            ·
              refine ⟨2365734239890117886130167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6308624639706981029680445 2365734239890117886130167)
              ·
                refine ⟨3548601359835176829195251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2365734239890117886130167 3548601359835176829195251)
                ·
                  refine ⟨5322902039752765243792877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3548601359835176829195251 5322902039752765243792877)
                  ·
                    refine ⟨1996088264907286966422329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5322902039752765243792877 1996088264907286966422329)
                    ·
                      refine ⟨1497066198680465224816747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1996088264907286966422329 1497066198680465224816747)
                      ·
                        rfl

theorem cell23_2915526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_2915526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2915526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2915526 prefixEnd_2915526 := by exact prefixLift 2915526
  have htrace : WordTrace (prefixWord ++ tailWord_2915526) baseStart_2915526 baseEnd_2915526 := by
    simpa [prefixWord, tailWord_2915526, baseEnd_2915526] using wordTrace_append hprefix tailTrace_2915526
  have hstable : (prefixWord ++ tailWord_2915526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2915526).length < 2 ^ (prefixWord ++ tailWord_2915526).sum := by decide
  have hdescent : baseEnd_2915526 < baseStart_2915526 := by decide
  rcases family_descends (prefixWord ++ tailWord_2915526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2915541 : List Nat := [1, 3, 2, 4, 1, 1, 2, 2, 2, 5]
def baseStart_2915541 : Nat := 118140960795 + 2915541 * 2 ^ 59
def prefixEnd_2915541 : Nat := 4983230072969 + 3 ^ 40 * 2915541 * 2
def baseEnd_2915541 : Nat := 499024633630094222043059

theorem tailTrace_2915541 : CollatzResearch.WordTrace tailWord_2915541 prefixEnd_2915541 499024633630094222043059 := by
  unfold tailWord_2915541
  simp only [CollatzResearch.WordTrace]
  refine ⟨106338516330500366605298477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70892344220333577736865651 106338516330500366605298477)
  ·
    refine ⟨39876943623937637476986929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106338516330500366605298477 39876943623937637476986929)
    ·
      refine ⟨29907707717953228107740197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39876943623937637476986929 29907707717953228107740197)
      ·
        refine ⟨5607695197116230270201287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29907707717953228107740197 5607695197116230270201287)
        ·
          refine ⟨8411542795674345405301931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5607695197116230270201287 8411542795674345405301931)
          ·
            refine ⟨12617314193511518107952897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8411542795674345405301931 12617314193511518107952897)
            ·
              refine ⟨9462985645133638580964673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12617314193511518107952897 9462985645133638580964673)
              ·
                refine ⟨7097239233850228935723505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9462985645133638580964673 7097239233850228935723505)
                ·
                  refine ⟨5322929425387671701792629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7097239233850228935723505 5322929425387671701792629)
                  ·
                    refine ⟨499024633630094222043059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5322929425387671701792629 499024633630094222043059)
                    ·
                      rfl

theorem cell23_2915541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 2, 2, 5].length) (baseStart_2915541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2915541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2915541 prefixEnd_2915541 := by exact prefixLift 2915541
  have htrace : WordTrace (prefixWord ++ tailWord_2915541) baseStart_2915541 baseEnd_2915541 := by
    simpa [prefixWord, tailWord_2915541, baseEnd_2915541] using wordTrace_append hprefix tailTrace_2915541
  have hstable : (prefixWord ++ tailWord_2915541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2915541).length < 2 ^ (prefixWord ++ tailWord_2915541).sum := by decide
  have hdescent : baseEnd_2915541 < baseStart_2915541 := by decide
  rcases family_descends (prefixWord ++ tailWord_2915541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2915571 : List Nat := [1, 1, 1, 2, 2, 6, 1, 2, 3, 4]
def baseStart_2915571 : Nat := 118140960795 + 2915571 * 2 ^ 59
def prefixEnd_2915571 : Nat := 4983230072969 + 3 ^ 40 * 2915571 * 2
def baseEnd_2915571 : Nat := 499029768436639182918013

theorem tailTrace_2915571 : CollatzResearch.WordTrace tailWord_2915571 prefixEnd_2915571 499029768436639182918013 := by
  unfold tailWord_2915571
  simp only [CollatzResearch.WordTrace]
  refine ⟨106339610520391681728890567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70893073680261121152593711 106339610520391681728890567)
  ·
    refine ⟨159509415780587522593335851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106339610520391681728890567 159509415780587522593335851)
    ·
      refine ⟨239264123670881283890003777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159509415780587522593335851 239264123670881283890003777)
      ·
        refine ⟨179448092753160962917502833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 239264123670881283890003777 179448092753160962917502833)
        ·
          refine ⟨134586069564870722188127125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179448092753160962917502833 134586069564870722188127125)
          ·
            refine ⟨6308722010853315102568459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 134586069564870722188127125 6308722010853315102568459)
            ·
              refine ⟨9463083016279972653852689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6308722010853315102568459 9463083016279972653852689)
              ·
                refine ⟨7097312262209979490389517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9463083016279972653852689 7097312262209979490389517)
                ·
                  refine ⟨2661492098328742308896069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7097312262209979490389517 2661492098328742308896069)
                  ·
                    refine ⟨499029768436639182918013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2661492098328742308896069 499029768436639182918013)
                    ·
                      rfl

theorem cell23_2915571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 2, 3, 4].length) (baseStart_2915571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2915571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2915571 prefixEnd_2915571 := by exact prefixLift 2915571
  have htrace : WordTrace (prefixWord ++ tailWord_2915571) baseStart_2915571 baseEnd_2915571 := by
    simpa [prefixWord, tailWord_2915571, baseEnd_2915571] using wordTrace_append hprefix tailTrace_2915571
  have hstable : (prefixWord ++ tailWord_2915571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2915571).length < 2 ^ (prefixWord ++ tailWord_2915571).sum := by decide
  have hdescent : baseEnd_2915571 < baseStart_2915571 := by decide
  rcases family_descends (prefixWord ++ tailWord_2915571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2915662 : List Nat := [4, 1, 1, 1, 1, 1, 7, 2, 1, 1, 3]
def baseStart_2915662 : Nat := 118140960795 + 2915662 * 2 ^ 59
def prefixEnd_2915662 : Nat := 4983230072969 + 3 ^ 40 * 2915662 * 2
def baseEnd_2915662 : Nat := 1497136032049476692716121

theorem tailTrace_2915662 : CollatzResearch.WordTrace tailWord_2915662 prefixEnd_2915662 1497136032049476692716121 := by
  unfold tailWord_2915662
  simp only [CollatzResearch.WordTrace]
  refine ⟨13292866195382750533806655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70895286375374669513635493 13292866195382750533806655)
  ·
    refine ⟨19939299293074125800709983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13292866195382750533806655 19939299293074125800709983)
    ·
      refine ⟨29908948939611188701064975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19939299293074125800709983 29908948939611188701064975)
      ·
        refine ⟨44863423409416783051597463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29908948939611188701064975 44863423409416783051597463)
        ·
          refine ⟨67295135114125174577396195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44863423409416783051597463 67295135114125174577396195)
          ·
            refine ⟨100942702671187761866094293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67295135114125174577396195 100942702671187761866094293)
            ·
              refine ⟨2365844593855963168736585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 100942702671187761866094293 2365844593855963168736585)
              ·
                refine ⟨1774383445391972376552439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2365844593855963168736585 1774383445391972376552439)
                ·
                  refine ⟨2661575168087958564828659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1774383445391972376552439 2661575168087958564828659)
                  ·
                    refine ⟨3992362752131937847242989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2661575168087958564828659 3992362752131937847242989)
                    ·
                      refine ⟨1497136032049476692716121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3992362752131937847242989 1497136032049476692716121)
                      ·
                        rfl

theorem cell23_2915662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 7, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 7, 2, 1, 1, 3].length) (baseStart_2915662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2915662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2915662 prefixEnd_2915662 := by exact prefixLift 2915662
  have htrace : WordTrace (prefixWord ++ tailWord_2915662) baseStart_2915662 baseEnd_2915662 := by
    simpa [prefixWord, tailWord_2915662, baseEnd_2915662] using wordTrace_append hprefix tailTrace_2915662
  have hstable : (prefixWord ++ tailWord_2915662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2915662).length < 2 ^ (prefixWord ++ tailWord_2915662).sum := by decide
  have hdescent : baseEnd_2915662 < baseStart_2915662 := by decide
  rcases family_descends (prefixWord ++ tailWord_2915662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2915664 : List Nat := [2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 6]
def baseStart_2915664 : Nat := 118140960795 + 2915664 * 2 ^ 59
def prefixEnd_2915664 : Nat := 4983230072969 + 3 ^ 40 * 2915664 * 2
def baseEnd_2915664 : Nat := 1497137059010785684891111

theorem tailTrace_2915664 : CollatzResearch.WordTrace tailWord_2915664 prefixEnd_2915664 1497137059010785684891111 := by
  unfold tailWord_2915664
  simp only [CollatzResearch.WordTrace]
  refine ⟨53171501254527379306013023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70895335006036505741350697 53171501254527379306013023)
  ·
    refine ⟨79757251881791068959019535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53171501254527379306013023 79757251881791068959019535)
    ·
      refine ⟨119635877822686603438529303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79757251881791068959019535 119635877822686603438529303)
      ·
        refine ⟨179453816734029905157793955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119635877822686603438529303 179453816734029905157793955)
        ·
          refine ⟨269180725101044857736690933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179453816734029905157793955 269180725101044857736690933)
          ·
            refine ⟨25235692978222955412814775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 269180725101044857736690933 25235692978222955412814775)
            ·
              refine ⟨37853539467334433119222163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25235692978222955412814775 37853539467334433119222163)
              ·
                refine ⟨56780309201001649678833245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37853539467334433119222163 56780309201001649678833245)
                ·
                  refine ⟨21292615950375618629562467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56780309201001649678833245 21292615950375618629562467)
                  ·
                    refine ⟨31938923925563427944343701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21292615950375618629562467 31938923925563427944343701)
                    ·
                      refine ⟨1497137059010785684891111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31938923925563427944343701 1497137059010785684891111)
                      ·
                        rfl

theorem cell23_2915664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 6].length) (baseStart_2915664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2915664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2915664 prefixEnd_2915664 := by exact prefixLift 2915664
  have htrace : WordTrace (prefixWord ++ tailWord_2915664) baseStart_2915664 baseEnd_2915664 := by
    simpa [prefixWord, tailWord_2915664, baseEnd_2915664] using wordTrace_append hprefix tailTrace_2915664
  have hstable : (prefixWord ++ tailWord_2915664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2915664).length < 2 ^ (prefixWord ++ tailWord_2915664).sum := by decide
  have hdescent : baseEnd_2915664 < baseStart_2915664 := by decide
  rcases family_descends (prefixWord ++ tailWord_2915664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2915671 : List Nat := [1, 1, 3, 2, 3, 2, 2, 2, 1, 1, 5]
def baseStart_2915671 : Nat := 118140960795 + 2915671 * 2 ^ 59
def prefixEnd_2915671 : Nat := 4983230072969 + 3 ^ 40 * 2915671 * 2
def baseEnd_2915671 : Nat := 1497140653375367157503579

theorem tailTrace_2915671 : CollatzResearch.WordTrace tailWord_2915671 prefixEnd_2915671 1497140653375367157503579 := by
  unfold tailWord_2915671
  simp only [CollatzResearch.WordTrace]
  refine ⟨106343257820029398807530867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70895505213352932538353911 106343257820029398807530867)
  ·
    refine ⟨159514886730044098211296301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106343257820029398807530867 159514886730044098211296301)
    ·
      refine ⟨59818082523766536829236113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 159514886730044098211296301 59818082523766536829236113)
      ·
        refine ⟨44863561892824902621927085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59818082523766536829236113 44863561892824902621927085)
        ·
          refine ⟨16823835709809338483222657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44863561892824902621927085 16823835709809338483222657)
          ·
            refine ⟨12617876782357003862416993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16823835709809338483222657 12617876782357003862416993)
            ·
              refine ⟨9463407586767752896812745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12617876782357003862416993 9463407586767752896812745)
              ·
                refine ⟨7097555690075814672609559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9463407586767752896812745 7097555690075814672609559)
                ·
                  refine ⟨10646333535113722008914339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7097555690075814672609559 10646333535113722008914339)
                  ·
                    refine ⟨15969500302670583013371509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10646333535113722008914339 15969500302670583013371509)
                    ·
                      refine ⟨1497140653375367157503579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15969500302670583013371509 1497140653375367157503579)
                      ·
                        rfl

theorem cell23_2915671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 2, 1, 1, 5].length) (baseStart_2915671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2915671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2915671 prefixEnd_2915671 := by exact prefixLift 2915671
  have htrace : WordTrace (prefixWord ++ tailWord_2915671) baseStart_2915671 baseEnd_2915671 := by
    simpa [prefixWord, tailWord_2915671, baseEnd_2915671] using wordTrace_append hprefix tailTrace_2915671
  have hstable : (prefixWord ++ tailWord_2915671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2915671).length < 2 ^ (prefixWord ++ tailWord_2915671).sum := by decide
  have hdescent : baseEnd_2915671 < baseStart_2915671 := by decide
  rcases family_descends (prefixWord ++ tailWord_2915671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2915674 : List Nat := [3, 1, 1, 2, 1, 2, 3, 10]
def baseStart_2915674 : Nat := 118140960795 + 2915674 * 2 ^ 59
def prefixEnd_2915674 : Nat := 4983230072969 + 3 ^ 40 * 2915674 * 2
def baseEnd_2915674 : Nat := 55449710882123357250595

theorem tailTrace_2915674 : CollatzResearch.WordTrace tailWord_2915674 prefixEnd_2915674 55449710882123357250595 := by
  unfold tailWord_2915674
  simp only [CollatzResearch.WordTrace]
  refine ⟨26585841809754632579972519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70895578159345686879926717 26585841809754632579972519)
  ·
    refine ⟨39878762714631948869958779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26585841809754632579972519 39878762714631948869958779)
    ·
      refine ⟨59818144071947923304938169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39878762714631948869958779 59818144071947923304938169)
      ·
        refine ⟨44863608053960942478703627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59818144071947923304938169 44863608053960942478703627)
        ·
          refine ⟨67295412080941413718055441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44863608053960942478703627 67295412080941413718055441)
          ·
            refine ⟨50471559060706060288541581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67295412080941413718055441 50471559060706060288541581)
            ·
              refine ⟨18926834647764772608203093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50471559060706060288541581 18926834647764772608203093)
              ·
                refine ⟨55449710882123357250595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 18926834647764772608203093 55449710882123357250595)
                ·
                  rfl

theorem cell23_2915674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 10].length) (baseStart_2915674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2915674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2915674 prefixEnd_2915674 := by exact prefixLift 2915674
  have htrace : WordTrace (prefixWord ++ tailWord_2915674) baseStart_2915674 baseEnd_2915674 := by
    simpa [prefixWord, tailWord_2915674, baseEnd_2915674] using wordTrace_append hprefix tailTrace_2915674
  have hstable : (prefixWord ++ tailWord_2915674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2915674).length < 2 ^ (prefixWord ++ tailWord_2915674).sum := by decide
  have hdescent : baseEnd_2915674 < baseStart_2915674 := by decide
  rcases family_descends (prefixWord ++ tailWord_2915674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2915704 : List Nat := [2, 1, 2, 1, 1, 1, 1, 1, 6, 7]
def baseStart_2915704 : Nat := 118140960795 + 2915704 * 2 ^ 59
def prefixEnd_2915704 : Nat := 4983230072969 + 3 ^ 40 * 2915704 * 2
def baseEnd_2915704 : Nat := 499052532745655176130309

theorem tailTrace_2915704 : CollatzResearch.WordTrace tailWord_2915704 prefixEnd_2915704 499052532745655176130309 := by
  unfold tailWord_2915704
  simp only [CollatzResearch.WordTrace]
  refine ⟨53172230714454922721741083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70896307619273230295654777 53172230714454922721741083)
  ·
    refine ⟨79758346071682384082611625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53172230714454922721741083 79758346071682384082611625)
    ·
      refine ⟨59818759553761788061958719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79758346071682384082611625 59818759553761788061958719)
      ·
        refine ⟨89728139330642682092938079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59818759553761788061958719 89728139330642682092938079)
        ·
          refine ⟨134592208995964023139407119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89728139330642682092938079 134592208995964023139407119)
          ·
            refine ⟨201888313493946034709110679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134592208995964023139407119 201888313493946034709110679)
            ·
              refine ⟨302832470240919052063666019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 201888313493946034709110679 302832470240919052063666019)
              ·
                refine ⟨454248705361378578095499029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 302832470240919052063666019 454248705361378578095499029)
                ·
                  refine ⟨21292908063814620848226517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 454248705361378578095499029 21292908063814620848226517)
                  ·
                    refine ⟨499052532745655176130309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21292908063814620848226517 499052532745655176130309)
                    ·
                      rfl

theorem cell23_2915704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 6, 7].length) (baseStart_2915704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2915704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2915704 prefixEnd_2915704 := by exact prefixLift 2915704
  have htrace : WordTrace (prefixWord ++ tailWord_2915704) baseStart_2915704 baseEnd_2915704 := by
    simpa [prefixWord, tailWord_2915704, baseEnd_2915704] using wordTrace_append hprefix tailTrace_2915704
  have hstable : (prefixWord ++ tailWord_2915704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2915704).length < 2 ^ (prefixWord ++ tailWord_2915704).sum := by decide
  have hdescent : baseEnd_2915704 < baseStart_2915704 := by decide
  rcases family_descends (prefixWord ++ tailWord_2915704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2915719 : List Nat := [1, 1, 4, 2, 2, 2, 4, 2, 1, 2, 2]
def baseStart_2915719 : Nat := 118140960795 + 2915719 * 2 ^ 59
def prefixEnd_2915719 : Nat := 4983230072969 + 3 ^ 40 * 2915719 * 2
def baseEnd_2915719 : Nat := 1497165300446782969703359

theorem tailTrace_2915719 : CollatzResearch.WordTrace tailWord_2915719 prefixEnd_2915719 1497165300446782969703359 := by
  unfold tailWord_2915719
  simp only [CollatzResearch.WordTrace]
  refine ⟨106345008523855503005278211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70896672349237002003518807 106345008523855503005278211)
  ·
    refine ⟨159517512785783254507917317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106345008523855503005278211 159517512785783254507917317)
    ·
      refine ⟨29909533647334360220234497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 159517512785783254507917317 29909533647334360220234497)
      ·
        refine ⟨22432150235500770165175873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29909533647334360220234497 22432150235500770165175873)
        ·
          refine ⟨16824112676625577623881905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22432150235500770165175873 16824112676625577623881905)
          ·
            refine ⟨12618084507469183217911429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16824112676625577623881905 12618084507469183217911429)
            ·
              refine ⟨2365890845150471853358393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12618084507469183217911429 2365890845150471853358393)
              ·
                refine ⟨1774418133862853890018795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2365890845150471853358393 1774418133862853890018795)
                ·
                  refine ⟨2661627200794280835028193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1774418133862853890018795 2661627200794280835028193)
                  ·
                    refine ⟨1996220400595710626271145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2661627200794280835028193 1996220400595710626271145)
                    ·
                      refine ⟨1497165300446782969703359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1996220400595710626271145 1497165300446782969703359)
                      ·
                        rfl

theorem cell23_2915719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 4, 2, 1, 2, 2].length) (baseStart_2915719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2915719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2915719 prefixEnd_2915719 := by exact prefixLift 2915719
  have htrace : WordTrace (prefixWord ++ tailWord_2915719) baseStart_2915719 baseEnd_2915719 := by
    simpa [prefixWord, tailWord_2915719, baseEnd_2915719] using wordTrace_append hprefix tailTrace_2915719
  have hstable : (prefixWord ++ tailWord_2915719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2915719).length < 2 ^ (prefixWord ++ tailWord_2915719).sum := by decide
  have hdescent : baseEnd_2915719 < baseStart_2915719 := by decide
  rcases family_descends (prefixWord ++ tailWord_2915719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2915751 : List Nat := [1, 1, 6, 1, 1, 1, 1, 2, 1, 8]
def baseStart_2915751 : Nat := 118140960795 + 2915751 * 2 ^ 59
def prefixEnd_2915751 : Nat := 4983230072969 + 3 ^ 40 * 2915751 * 2
def baseEnd_2915751 : Nat := 499060577275908948167737

theorem tailTrace_2915751 : CollatzResearch.WordTrace tailWord_2915751 prefixEnd_2915751 499060577275908948167737 := by
  unfold tailWord_2915751
  simp only [CollatzResearch.WordTrace]
  refine ⟨106346175659739572470443107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70897450439826381646962071 106346175659739572470443107)
  ·
    refine ⟨159519263489609358705664661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106346175659739572470443107 159519263489609358705664661)
    ·
      refine ⟨7477465476075438689328031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 159519263489609358705664661 7477465476075438689328031)
      ·
        refine ⟨11216198214113158033992047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7477465476075438689328031 11216198214113158033992047)
        ·
          refine ⟨16824297321169737050988071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11216198214113158033992047 16824297321169737050988071)
          ·
            refine ⟨25236445981754605576482107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16824297321169737050988071 25236445981754605576482107)
            ·
              refine ⟨37854668972631908364723161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25236445981754605576482107 37854668972631908364723161)
              ·
                refine ⟨28391001729473931273542371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37854668972631908364723161 28391001729473931273542371)
                ·
                  refine ⟨42586502594210896910313557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28391001729473931273542371 42586502594210896910313557)
                  ·
                    refine ⟨499060577275908948167737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 42586502594210896910313557 499060577275908948167737)
                    ·
                      rfl

theorem cell23_2915751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 2, 1, 8].length) (baseStart_2915751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2915751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2915751 prefixEnd_2915751 := by exact prefixLift 2915751
  have htrace : WordTrace (prefixWord ++ tailWord_2915751) baseStart_2915751 baseEnd_2915751 := by
    simpa [prefixWord, tailWord_2915751, baseEnd_2915751] using wordTrace_append hprefix tailTrace_2915751
  have hstable : (prefixWord ++ tailWord_2915751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2915751).length < 2 ^ (prefixWord ++ tailWord_2915751).sum := by decide
  have hdescent : baseEnd_2915751 < baseStart_2915751 := by decide
  rcases family_descends (prefixWord ++ tailWord_2915751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2915761 : List Nat := [1, 2, 2, 4, 1, 1, 2, 1, 1, 3, 5]
def baseStart_2915761 : Nat := 118140960795 + 2915761 * 2 ^ 59
def prefixEnd_2915761 : Nat := 4983230072969 + 3 ^ 40 * 2915761 * 2
def baseEnd_2915761 : Nat := 1497186866634271805378165

theorem tailTrace_2915761 : CollatzResearch.WordTrace tailWord_2915761 prefixEnd_2915761 1497186866634271805378165 := by
  unfold tailWord_2915761
  simp only [CollatzResearch.WordTrace]
  refine ⟨106346540389703344178307137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70897693593135562785538091 106346540389703344178307137)
  ·
    refine ⟨79759905292277508133730353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106346540389703344178307137 79759905292277508133730353)
    ·
      refine ⟨59819928969208131100297765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79759905292277508133730353 59819928969208131100297765)
      ·
        refine ⟨11216236681726524581305831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59819928969208131100297765 11216236681726524581305831)
        ·
          refine ⟨16824355022589786871958747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11216236681726524581305831 16824355022589786871958747)
          ·
            refine ⟨25236532533884680307938121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16824355022589786871958747 25236532533884680307938121)
            ·
              refine ⟨18927399400413510230953591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25236532533884680307938121 18927399400413510230953591)
              ·
                refine ⟨28391099100620265346430387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18927399400413510230953591 28391099100620265346430387)
                ·
                  refine ⟨42586648650930398019645581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28391099100620265346430387 42586648650930398019645581)
                  ·
                    refine ⟨15969993244098899257367093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42586648650930398019645581 15969993244098899257367093)
                    ·
                      refine ⟨1497186866634271805378165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15969993244098899257367093 1497186866634271805378165)
                      ·
                        rfl

theorem cell23_2915761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_2915761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2915761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2915761 prefixEnd_2915761 := by exact prefixLift 2915761
  have htrace : WordTrace (prefixWord ++ tailWord_2915761) baseStart_2915761 baseEnd_2915761 := by
    simpa [prefixWord, tailWord_2915761, baseEnd_2915761] using wordTrace_append hprefix tailTrace_2915761
  have hstable : (prefixWord ++ tailWord_2915761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2915761).length < 2 ^ (prefixWord ++ tailWord_2915761).sum := by decide
  have hdescent : baseEnd_2915761 < baseStart_2915761 := by decide
  rcases family_descends (prefixWord ++ tailWord_2915761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2915769 : List Nat := [1, 2, 1, 4, 5, 1, 1, 2, 2, 1, 3]
def baseStart_2915769 : Nat := 118140960795 + 2915769 * 2 ^ 59
def prefixEnd_2915769 : Nat := 4983230072969 + 3 ^ 40 * 2915769 * 2
def baseEnd_2915769 : Nat := 1497190974479507774078129

theorem tailTrace_2915769 : CollatzResearch.WordTrace tailWord_2915769 prefixEnd_2915769 1497190974479507774078129 := by
  unfold tailWord_2915769
  simp only [CollatzResearch.WordTrace]
  refine ⟨106346832173674361544598361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70897888115782907696398907 106346832173674361544598361)
  ·
    refine ⟨79760124130255771158448771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106346832173674361544598361 79760124130255771158448771)
    ·
      refine ⟨119640186195383656737673157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79760124130255771158448771 119640186195383656737673157)
      ·
        refine ⟨22432534911634435638313717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 119640186195383656737673157 22432534911634435638313717)
        ·
          refine ⟨2103050147965728341091911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22432534911634435638313717 2103050147965728341091911)
          ·
            refine ⟨3154575221948592511637867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2103050147965728341091911 3154575221948592511637867)
            ·
              refine ⟨4731862832922888767456801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3154575221948592511637867 4731862832922888767456801)
              ·
                refine ⟨3548897124692166575592601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4731862832922888767456801 3548897124692166575592601)
                ·
                  refine ⟨2661672843519124931694451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3548897124692166575592601 2661672843519124931694451)
                  ·
                    refine ⟨3992509265278687397541677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2661672843519124931694451 3992509265278687397541677)
                    ·
                      refine ⟨1497190974479507774078129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3992509265278687397541677 1497190974479507774078129)
                      ·
                        rfl

theorem cell23_2915769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 1, 2, 2, 1, 3].length) (baseStart_2915769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2915769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2915769 prefixEnd_2915769 := by exact prefixLift 2915769
  have htrace : WordTrace (prefixWord ++ tailWord_2915769) baseStart_2915769 baseEnd_2915769 := by
    simpa [prefixWord, tailWord_2915769, baseEnd_2915769] using wordTrace_append hprefix tailTrace_2915769
  have hstable : (prefixWord ++ tailWord_2915769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2915769).length < 2 ^ (prefixWord ++ tailWord_2915769).sum := by decide
  have hdescent : baseEnd_2915769 < baseStart_2915769 := by decide
  rcases family_descends (prefixWord ++ tailWord_2915769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2915788 : List Nat := [2, 2, 1, 4, 2, 1, 2, 1, 2, 2, 4]
def baseStart_2915788 : Nat := 118140960795 + 2915788 * 2 ^ 59
def prefixEnd_2915788 : Nat := 4983230072969 + 3 ^ 40 * 2915788 * 2
def baseEnd_2915788 : Nat := 1497200730611943199740541

theorem tailTrace_2915788 : CollatzResearch.WordTrace tailWord_2915788 prefixEnd_2915788 1497200730611943199740541 := by
  unfold tailWord_2915788
  simp only [CollatzResearch.WordTrace]
  refine ⟨53173762580302763894770009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70898350107070351859693345 53173762580302763894770009)
  ·
    refine ⟨39880321935227072921077507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53173762580302763894770009 39880321935227072921077507)
    ·
      refine ⟨59820482902840609381616261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39880321935227072921077507 59820482902840609381616261)
      ·
        refine ⟨11216340544282614259053049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59820482902840609381616261 11216340544282614259053049)
        ·
          refine ⟨8412255408211960694289787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11216340544282614259053049 8412255408211960694289787)
          ·
            refine ⟨12618383112317941041434681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8412255408211960694289787 12618383112317941041434681)
            ·
              refine ⟨9463787334238455781076011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12618383112317941041434681 9463787334238455781076011)
              ·
                refine ⟨14195681001357683671614017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9463787334238455781076011 14195681001357683671614017)
                ·
                  refine ⟨10646760751018262753710513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14195681001357683671614017 10646760751018262753710513)
                  ·
                    refine ⟨7985070563263697065282885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10646760751018262753710513 7985070563263697065282885)
                    ·
                      refine ⟨1497200730611943199740541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7985070563263697065282885 1497200730611943199740541)
                      ·
                        rfl

theorem cell23_2915788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_2915788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2915788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2915788 prefixEnd_2915788 := by exact prefixLift 2915788
  have htrace : WordTrace (prefixWord ++ tailWord_2915788) baseStart_2915788 baseEnd_2915788 := by
    simpa [prefixWord, tailWord_2915788, baseEnd_2915788] using wordTrace_append hprefix tailTrace_2915788
  have hstable : (prefixWord ++ tailWord_2915788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2915788).length < 2 ^ (prefixWord ++ tailWord_2915788).sum := by decide
  have hdescent : baseEnd_2915788 < baseStart_2915788 := by decide
  rcases family_descends (prefixWord ++ tailWord_2915788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2915815 : List Nat := [1, 1, 5, 2, 1, 2, 3, 3, 5]
def baseStart_2915815 : Nat := 118140960795 + 2915815 * 2 ^ 59
def prefixEnd_2915815 : Nat := 4983230072969 + 3 ^ 40 * 2915815 * 2
def baseEnd_2915815 : Nat := 166357177176623843789213

theorem tailTrace_2915815 : CollatzResearch.WordTrace tailWord_2915815 prefixEnd_2915815 166357177176623843789213 := by
  unfold tailWord_2915815
  simp only [CollatzResearch.WordTrace]
  refine ⟨106348509931507711400772899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70899006621005140933848599 106348509931507711400772899)
  ·
    refine ⟨159522764897261567101159349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106348509931507711400772899 159522764897261567101159349)
    ·
      refine ⟨14955259209118271915733689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 159522764897261567101159349 14955259209118271915733689)
      ·
        refine ⟨11216444406838703936800267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14955259209118271915733689 11216444406838703936800267)
        ·
          refine ⟨16824666610258055905200401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11216444406838703936800267 16824666610258055905200401)
          ·
            refine ⟨12618499957693541928900301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16824666610258055905200401 12618499957693541928900301)
            ·
              refine ⟨4731937484135078223337613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12618499957693541928900301 4731937484135078223337613)
              ·
                refine ⟨1774476556550654333751605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4731937484135078223337613 1774476556550654333751605)
                ·
                  refine ⟨166357177176623843789213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1774476556550654333751605 166357177176623843789213)
                  ·
                    rfl

theorem cell23_2915815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 3, 3, 5].length) (baseStart_2915815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2915815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2915815 prefixEnd_2915815 := by exact prefixLift 2915815
  have htrace : WordTrace (prefixWord ++ tailWord_2915815) baseStart_2915815 baseEnd_2915815 := by
    simpa [prefixWord, tailWord_2915815, baseEnd_2915815] using wordTrace_append hprefix tailTrace_2915815
  have hstable : (prefixWord ++ tailWord_2915815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2915815).length < 2 ^ (prefixWord ++ tailWord_2915815).sum := by decide
  have hdescent : baseEnd_2915815 < baseStart_2915815 := by decide
  rcases family_descends (prefixWord ++ tailWord_2915815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2915831 : List Nat := [1, 1, 3, 1, 1, 1, 1, 4, 3, 3, 4]
def baseStart_2915831 : Nat := 118140960795 + 2915831 * 2 ^ 59
def prefixEnd_2915831 : Nat := 4983230072969 + 3 ^ 40 * 2915831 * 2
def baseEnd_2915831 : Nat := 1497222810280086531502843

theorem tailTrace_2915831 : CollatzResearch.WordTrace tailWord_2915831 prefixEnd_2915831 1497222810280086531502843 := by
  unfold tailWord_2915831
  simp only [CollatzResearch.WordTrace]
  refine ⟨106349093499449746133355347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70899395666299830755570231 106349093499449746133355347)
  ·
    refine ⟨159523640249174619200033021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106349093499449746133355347 159523640249174619200033021)
    ·
      refine ⟨59821365093440482200012383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 159523640249174619200033021 59821365093440482200012383)
      ·
        refine ⟨89732047640160723300018575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59821365093440482200012383 89732047640160723300018575)
        ·
          refine ⟨134598071460241084950027863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89732047640160723300018575 134598071460241084950027863)
          ·
            refine ⟨201897107190361627425041795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134598071460241084950027863 201897107190361627425041795)
            ·
              refine ⟨302845660785542441137562693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 201897107190361627425041795 302845660785542441137562693)
              ·
                refine ⟨56783561397289207713293005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 302845660785542441137562693 56783561397289207713293005)
                ·
                  refine ⟨21293835523983452892484877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56783561397289207713293005 21293835523983452892484877)
                  ·
                    refine ⟨7985188321493794834681829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21293835523983452892484877 7985188321493794834681829)
                    ·
                      refine ⟨1497222810280086531502843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7985188321493794834681829 1497222810280086531502843)
                      ·
                        rfl

theorem cell23_2915831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 3, 3, 4].length) (baseStart_2915831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2915831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2915831 prefixEnd_2915831 := by exact prefixLift 2915831
  have htrace : WordTrace (prefixWord ++ tailWord_2915831) baseStart_2915831 baseEnd_2915831 := by
    simpa [prefixWord, tailWord_2915831, baseEnd_2915831] using wordTrace_append hprefix tailTrace_2915831
  have hstable : (prefixWord ++ tailWord_2915831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2915831).length < 2 ^ (prefixWord ++ tailWord_2915831).sum := by decide
  have hdescent : baseEnd_2915831 < baseStart_2915831 := by decide
  rcases family_descends (prefixWord ++ tailWord_2915831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2915871 : List Nat := [1, 1, 2, 4, 1, 1, 2, 1, 10]
def baseStart_2915871 : Nat := 118140960795 + 2915871 * 2 ^ 59
def prefixEnd_2915871 : Nat := 4983230072969 + 3 ^ 40 * 2915871 * 2
def baseEnd_2915871 : Nat := 166360372167362930555851

theorem tailTrace_2915871 : CollatzResearch.WordTrace tailWord_2915871 prefixEnd_2915871 166360372167362930555851 := by
  unfold tailWord_2915871
  simp only [CollatzResearch.WordTrace]
  refine ⟨106350552419304832964811467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70900368279536555309874311 106350552419304832964811467)
  ·
    refine ⟨159525828628957249447217201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106350552419304832964811467 159525828628957249447217201)
    ·
      refine ⟨119644371471717937085412901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159525828628957249447217201 119644371471717937085412901)
      ·
        refine ⟨22433319650947113203514919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 119644371471717937085412901 22433319650947113203514919)
        ·
          refine ⟨33649979476420669805272379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22433319650947113203514919 33649979476420669805272379)
          ·
            refine ⟨50474969214631004707908569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33649979476420669805272379 50474969214631004707908569)
            ·
              refine ⟨37856226910973253530931427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50474969214631004707908569 37856226910973253530931427)
              ·
                refine ⟨56784340366459880296397141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37856226910973253530931427 56784340366459880296397141)
                ·
                  refine ⟨166360372167362930555851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 56784340366459880296397141 166360372167362930555851)
                  ·
                    rfl

theorem cell23_2915871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 1, 10].length) (baseStart_2915871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2915871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2915871 prefixEnd_2915871 := by exact prefixLift 2915871
  have htrace : WordTrace (prefixWord ++ tailWord_2915871) baseStart_2915871 baseEnd_2915871 := by
    simpa [prefixWord, tailWord_2915871, baseEnd_2915871] using wordTrace_append hprefix tailTrace_2915871
  have hstable : (prefixWord ++ tailWord_2915871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2915871).length < 2 ^ (prefixWord ++ tailWord_2915871).sum := by decide
  have hdescent : baseEnd_2915871 < baseStart_2915871 := by decide
  rcases family_descends (prefixWord ++ tailWord_2915871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2915949 : List Nat := [1, 5, 1, 1, 4, 1, 2, 1, 3, 1, 3]
def baseStart_2915949 : Nat := 118140960795 + 2915949 * 2 ^ 59
def prefixEnd_2915949 : Nat := 4983230072969 + 3 ^ 40 * 2915949 * 2
def baseEnd_2915949 : Nat := 1497283400997317069827301

theorem tailTrace_2915949 : CollatzResearch.WordTrace tailWord_2915949 prefixEnd_2915949 1497283400997317069827301 := by
  unfold tailWord_2915949
  simp only [CollatzResearch.WordTrace]
  refine ⟨106353397313022252286150901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70902264875348168190767267 106353397313022252286150901)
  ·
    refine ⟨9970630998095836151826647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 106353397313022252286150901 9970630998095836151826647)
    ·
      refine ⟨14955946497143754227739971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9970630998095836151826647 14955946497143754227739971)
      ·
        refine ⟨22433919745715631341609957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14955946497143754227739971 22433919745715631341609957)
        ·
          refine ⟨4206359952321680876551867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22433919745715631341609957 4206359952321680876551867)
          ·
            refine ⟨6309539928482521314827801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4206359952321680876551867 6309539928482521314827801)
            ·
              refine ⟨4732154946361890986120851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6309539928482521314827801 4732154946361890986120851)
              ·
                refine ⟨7098232419542836479181277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4732154946361890986120851 7098232419542836479181277)
                ·
                  refine ⟨2661837157328563679692979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7098232419542836479181277 2661837157328563679692979)
                  ·
                    refine ⟨3992755735992845519539469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2661837157328563679692979 3992755735992845519539469)
                    ·
                      refine ⟨1497283400997317069827301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3992755735992845519539469 1497283400997317069827301)
                      ·
                        rfl

theorem cell23_2915949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 2, 1, 3, 1, 3].length) (baseStart_2915949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2915949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2915949 prefixEnd_2915949 := by exact prefixLift 2915949
  have htrace : WordTrace (prefixWord ++ tailWord_2915949) baseStart_2915949 baseEnd_2915949 := by
    simpa [prefixWord, tailWord_2915949, baseEnd_2915949] using wordTrace_append hprefix tailTrace_2915949
  have hstable : (prefixWord ++ tailWord_2915949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2915949).length < 2 ^ (prefixWord ++ tailWord_2915949).sum := by decide
  have hdescent : baseEnd_2915949 < baseStart_2915949 := by decide
  rcases family_descends (prefixWord ++ tailWord_2915949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2915965 : List Nat := [1, 4, 1, 1, 4, 1, 3, 1, 1, 6]
def baseStart_2915965 : Nat := 118140960795 + 2915965 * 2 ^ 59
def prefixEnd_2915965 : Nat := 4983230072969 + 3 ^ 40 * 2915965 * 2
def baseEnd_2915965 : Nat := 499097205562596335742409

theorem tailTrace_2915965 : CollatzResearch.WordTrace tailWord_2915965 prefixEnd_2915965 499097205562596335742409 := by
  unfold tailWord_2915965
  simp only [CollatzResearch.WordTrace]
  refine ⟨106353980880964287018733349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70902653920642858012488899 106353980880964287018733349)
  ·
    refine ⟨19941371415180803816012503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 106353980880964287018733349 19941371415180803816012503)
    ·
      refine ⟨29912057122771205724018755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19941371415180803816012503 29912057122771205724018755)
      ·
        refine ⟨44868085684156808586028133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29912057122771205724018755 44868085684156808586028133)
        ·
          refine ⟨8412766065779401609880275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44868085684156808586028133 8412766065779401609880275)
          ·
            refine ⟨12619149098669102414820413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8412766065779401609880275 12619149098669102414820413)
            ·
              refine ⟨4732180912000913405557655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12619149098669102414820413 4732180912000913405557655)
              ·
                refine ⟨7098271368001370108336483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4732180912000913405557655 7098271368001370108336483)
                ·
                  refine ⟨10647407052002055162504725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7098271368001370108336483 10647407052002055162504725)
                  ·
                    refine ⟨499097205562596335742409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10647407052002055162504725 499097205562596335742409)
                    ·
                      rfl

theorem cell23_2915965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 3, 1, 1, 6].length) (baseStart_2915965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2915965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2915965 prefixEnd_2915965 := by exact prefixLift 2915965
  have htrace : WordTrace (prefixWord ++ tailWord_2915965) baseStart_2915965 baseEnd_2915965 := by
    simpa [prefixWord, tailWord_2915965, baseEnd_2915965] using wordTrace_append hprefix tailTrace_2915965
  have hstable : (prefixWord ++ tailWord_2915965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2915965).length < 2 ^ (prefixWord ++ tailWord_2915965).sum := by decide
  have hdescent : baseEnd_2915965 < baseStart_2915965 := by decide
  rcases family_descends (prefixWord ++ tailWord_2915965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2915968 : List Nat := [2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 6]
def baseStart_2915968 : Nat := 118140960795 + 2915968 * 2 ^ 59
def prefixEnd_2915968 : Nat := 4983230072969 + 3 ^ 40 * 2915968 * 2
def baseEnd_2915968 : Nat := 1497293157129752495489713

theorem tailTrace_2915968 : CollatzResearch.WordTrace tailWord_2915968 prefixEnd_2915968 1497293157129752495489713 := by
  unfold tailWord_2915968
  simp only [CollatzResearch.WordTrace]
  refine ⟨53177045149976709265546279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70902726866635612354061705 53177045149976709265546279)
  ·
    refine ⟨79765567724965063898319419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53177045149976709265546279 79765567724965063898319419)
    ·
      refine ⟨119648351587447595847479129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79765567724965063898319419 119648351587447595847479129)
      ·
        refine ⟨89736263690585696885609347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119648351587447595847479129 89736263690585696885609347)
        ·
          refine ⟨134604395535878545328414021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89736263690585696885609347 134604395535878545328414021)
          ·
            refine ⟨25238324162977227249077629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 134604395535878545328414021 25238324162977227249077629)
            ·
              refine ⟨9464371561116460218404111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25238324162977227249077629 9464371561116460218404111)
              ·
                refine ⟨14196557341674690327606167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9464371561116460218404111 14196557341674690327606167)
                ·
                  refine ⟨21294836012512035491409251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14196557341674690327606167 21294836012512035491409251)
                  ·
                    refine ⟨31942254018768053237113877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21294836012512035491409251 31942254018768053237113877)
                    ·
                      refine ⟨1497293157129752495489713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31942254018768053237113877 1497293157129752495489713)
                      ·
                        rfl

theorem cell23_2915968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 6].length) (baseStart_2915968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2915968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2915968 prefixEnd_2915968 := by exact prefixLift 2915968
  have htrace : WordTrace (prefixWord ++ tailWord_2915968) baseStart_2915968 baseEnd_2915968 := by
    simpa [prefixWord, tailWord_2915968, baseEnd_2915968] using wordTrace_append hprefix tailTrace_2915968
  have hstable : (prefixWord ++ tailWord_2915968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2915968).length < 2 ^ (prefixWord ++ tailWord_2915968).sum := by decide
  have hdescent : baseEnd_2915968 < baseStart_2915968 := by decide
  rcases family_descends (prefixWord ++ tailWord_2915968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2915992 : List Nat := [2, 1, 2, 4, 1, 2, 2, 3, 1, 2, 3]
def baseStart_2915992 : Nat := 118140960795 + 2915992 * 2 ^ 59
def prefixEnd_2915992 : Nat := 4983230072969 + 3 ^ 40 * 2915992 * 2
def baseEnd_2915992 : Nat := 1497305480665460401589603

theorem tailTrace_2915992 : CollatzResearch.WordTrace tailWord_2915992 prefixEnd_2915992 1497305480665460401589603 := by
  unfold tailWord_2915992
  simp only [CollatzResearch.WordTrace]
  refine ⟨53177482825933235314983115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70903310434577647086644153 53177482825933235314983115)
  ·
    refine ⟨79766224238899852972474673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53177482825933235314983115 79766224238899852972474673)
    ·
      refine ⟨59824668179174889729356005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79766224238899852972474673 59824668179174889729356005)
      ·
        refine ⟨11217125283595291824254251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59824668179174889729356005 11217125283595291824254251)
        ·
          refine ⟨16825687925392937736381377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11217125283595291824254251 16825687925392937736381377)
          ·
            refine ⟨12619265944044703302286033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16825687925392937736381377 12619265944044703302286033)
            ·
              refine ⟨9464449458033527476714525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12619265944044703302286033 9464449458033527476714525)
              ·
                refine ⟨3549168546762572803767947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9464449458033527476714525 3549168546762572803767947)
                ·
                  refine ⟨5323752820143859205651921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3549168546762572803767947 5323752820143859205651921)
                  ·
                    refine ⟨3992814615107894404238941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5323752820143859205651921 3992814615107894404238941)
                    ·
                      refine ⟨1497305480665460401589603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3992814615107894404238941 1497305480665460401589603)
                      ·
                        rfl

theorem cell23_2915992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 3, 1, 2, 3].length) (baseStart_2915992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2915992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2915992 prefixEnd_2915992 := by exact prefixLift 2915992
  have htrace : WordTrace (prefixWord ++ tailWord_2915992) baseStart_2915992 baseEnd_2915992 := by
    simpa [prefixWord, tailWord_2915992, baseEnd_2915992] using wordTrace_append hprefix tailTrace_2915992
  have hstable : (prefixWord ++ tailWord_2915992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2915992).length < 2 ^ (prefixWord ++ tailWord_2915992).sum := by decide
  have hdescent : baseEnd_2915992 < baseStart_2915992 := by decide
  rcases family_descends (prefixWord ++ tailWord_2915992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2916032 : List Nat := [2, 1, 1, 2, 4, 1, 3, 1, 3, 3, 2]
def baseStart_2916032 : Nat := 118140960795 + 2916032 * 2 ^ 59
def prefixEnd_2916032 : Nat := 4983230072969 + 3 ^ 40 * 2916032 * 2
def baseEnd_2916032 : Nat := 1497326019891640245089419

theorem tailTrace_2916032 : CollatzResearch.WordTrace tailWord_2916032 prefixEnd_2916032 1497326019891640245089419 := by
  unfold tailWord_2916032
  simp only [CollatzResearch.WordTrace]
  refine ⟨53178212285860778730711175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70904283047814371640948233 53178212285860778730711175)
  ·
    refine ⟨79767318428791168096066763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53178212285860778730711175 79767318428791168096066763)
    ·
      refine ⟨119650977643186752144100145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79767318428791168096066763 119650977643186752144100145)
      ·
        refine ⟨89738233232390064108075109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119650977643186752144100145 89738233232390064108075109)
        ·
          refine ⟨16825918731073137020264083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 89738233232390064108075109 16825918731073137020264083)
          ·
            refine ⟨25238878096609705530396125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16825918731073137020264083 25238878096609705530396125)
            ·
              refine ⟨9464579286228639573898547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25238878096609705530396125 9464579286228639573898547)
              ·
                refine ⟨14196868929342959360847821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9464579286228639573898547 14196868929342959360847821)
                ·
                  refine ⟨5323825848503609760317933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14196868929342959360847821 5323825848503609760317933)
                  ·
                    refine ⟨1996434693188853660119225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5323825848503609760317933 1996434693188853660119225)
                    ·
                      refine ⟨1497326019891640245089419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1996434693188853660119225 1497326019891640245089419)
                      ·
                        rfl

theorem cell23_2916032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 1, 3, 3, 2].length) (baseStart_2916032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2916032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2916032 prefixEnd_2916032 := by exact prefixLift 2916032
  have htrace : WordTrace (prefixWord ++ tailWord_2916032) baseStart_2916032 baseEnd_2916032 := by
    simpa [prefixWord, tailWord_2916032, baseEnd_2916032] using wordTrace_append hprefix tailTrace_2916032
  have hstable : (prefixWord ++ tailWord_2916032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2916032).length < 2 ^ (prefixWord ++ tailWord_2916032).sum := by decide
  have hdescent : baseEnd_2916032 < baseStart_2916032 := by decide
  rcases family_descends (prefixWord ++ tailWord_2916032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2916048 : List Nat := [2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 5]
def baseStart_2916048 : Nat := 118140960795 + 2916048 * 2 ^ 59
def prefixEnd_2916048 : Nat := 4983230072969 + 3 ^ 40 * 2916048 * 2
def baseEnd_2916048 : Nat := 1497334235582112182489345

theorem tailTrace_2916048 : CollatzResearch.WordTrace tailWord_2916048 prefixEnd_2916048 1497334235582112182489345 := by
  unfold tailWord_2916048
  simp only [CollatzResearch.WordTrace]
  refine ⟨53178504069831796097002399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70904672093109061462669865 53178504069831796097002399)
  ·
    refine ⟨79767756104747694145503599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53178504069831796097002399 79767756104747694145503599)
    ·
      refine ⟨119651634157121541218255399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79767756104747694145503599 119651634157121541218255399)
      ·
        refine ⟨179477451235682311827383099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119651634157121541218255399 179477451235682311827383099)
        ·
          refine ⟨269216176853523467741074649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179477451235682311827383099 269216176853523467741074649)
          ·
            refine ⟨201912132640142600805805987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 269216176853523467741074649 201912132640142600805805987)
            ·
              refine ⟨302868198960213901208708981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 201912132640142600805805987 302868198960213901208708981)
              ·
                refine ⟨28393893652520053238316467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 302868198960213901208708981 28393893652520053238316467)
                ·
                  refine ⟨42590840478780079857474701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28393893652520053238316467 42590840478780079857474701)
                  ·
                    refine ⟨15971565179542529946553013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42590840478780079857474701 15971565179542529946553013)
                    ·
                      refine ⟨1497334235582112182489345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15971565179542529946553013 1497334235582112182489345)
                      ·
                        rfl

theorem cell23_2916048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 5].length) (baseStart_2916048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2916048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2916048 prefixEnd_2916048 := by exact prefixLift 2916048
  have htrace : WordTrace (prefixWord ++ tailWord_2916048) baseStart_2916048 baseEnd_2916048 := by
    simpa [prefixWord, tailWord_2916048, baseEnd_2916048] using wordTrace_append hprefix tailTrace_2916048
  have hstable : (prefixWord ++ tailWord_2916048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2916048).length < 2 ^ (prefixWord ++ tailWord_2916048).sum := by decide
  have hdescent : baseEnd_2916048 < baseStart_2916048 := by decide
  rcases family_descends (prefixWord ++ tailWord_2916048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2916079 : List Nat := [1, 1, 2, 1, 5, 1, 1, 5, 2, 2, 2]
def baseStart_2916079 : Nat := 118140960795 + 2916079 * 2 ^ 59
def prefixEnd_2916079 : Nat := 4983230072969 + 3 ^ 40 * 2916079 * 2
def baseEnd_2916079 : Nat := 1497350153482401561201703

theorem tailTrace_2916079 : CollatzResearch.WordTrace tailWord_2916079 prefixEnd_2916079 1497350153482401561201703 := by
  unfold tailWord_2916079
  simp only [CollatzResearch.WordTrace]
  refine ⟨106358138802551284488383291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70905425868367522992255527 106358138802551284488383291)
  ·
    refine ⟨159537208203826926732574937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106358138802551284488383291 159537208203826926732574937)
    ·
      refine ⟨119652906152870195049431203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159537208203826926732574937 119652906152870195049431203)
      ·
        refine ⟨179479359229305292574146805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119652906152870195049431203 179479359229305292574146805)
        ·
          refine ⟨16826189927747371178826263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 179479359229305292574146805 16826189927747371178826263)
          ·
            refine ⟨25239284891621056768239395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16826189927747371178826263 25239284891621056768239395)
            ·
              refine ⟨37858927337431585152359093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25239284891621056768239395 37858927337431585152359093)
              ·
                refine ⟨3549274437884211108033665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37858927337431585152359093 3549274437884211108033665)
                ·
                  refine ⟨2661955828413158331025249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3549274437884211108033665 2661955828413158331025249)
                  ·
                    refine ⟨1996466871309868748268937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2661955828413158331025249 1996466871309868748268937)
                    ·
                      refine ⟨1497350153482401561201703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1996466871309868748268937 1497350153482401561201703)
                      ·
                        rfl

theorem cell23_2916079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 5, 2, 2, 2].length) (baseStart_2916079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2916079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2916079 prefixEnd_2916079 := by exact prefixLift 2916079
  have htrace : WordTrace (prefixWord ++ tailWord_2916079) baseStart_2916079 baseEnd_2916079 := by
    simpa [prefixWord, tailWord_2916079, baseEnd_2916079] using wordTrace_append hprefix tailTrace_2916079
  have hstable : (prefixWord ++ tailWord_2916079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2916079).length < 2 ^ (prefixWord ++ tailWord_2916079).sum := by decide
  have hdescent : baseEnd_2916079 < baseStart_2916079 := by decide
  rcases family_descends (prefixWord ++ tailWord_2916079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2916153 : List Nat := [1, 2, 1, 7, 2, 1, 1, 3, 5]
def baseStart_2916153 : Nat := 118140960795 + 2916153 * 2 ^ 59
def prefixEnd_2916153 : Nat := 4983230072969 + 3 ^ 40 * 2916153 * 2
def baseEnd_2916153 : Nat := 166376461227870474630707

theorem tailTrace_2916153 : CollatzResearch.WordTrace tailWord_2916153 prefixEnd_2916153 166376461227870474630707 := by
  unfold tailWord_2916153
  simp only [CollatzResearch.WordTrace]
  refine ⟨106360837804283195126577113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70907225202855463417718075 106360837804283195126577113)
  ·
    refine ⟨79770628353212396344932835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106360837804283195126577113 79770628353212396344932835)
    ·
      refine ⟨119655942529818594517399253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79770628353212396344932835 119655942529818594517399253)
      ·
        refine ⟨2804436153042623309001545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 119655942529818594517399253 2804436153042623309001545)
        ·
          refine ⟨2103327114781967481751159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2804436153042623309001545 2103327114781967481751159)
          ·
            refine ⟨3154990672172951222626739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2103327114781967481751159 3154990672172951222626739)
            ·
              refine ⟨4732486008259426833940109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3154990672172951222626739 4732486008259426833940109)
              ·
                refine ⟨1774682253097285062727541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4732486008259426833940109 1774682253097285062727541)
                ·
                  refine ⟨166376461227870474630707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1774682253097285062727541 166376461227870474630707)
                  ·
                    rfl

theorem cell23_2916153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 1, 3, 5].length) (baseStart_2916153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2916153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2916153 prefixEnd_2916153 := by exact prefixLift 2916153
  have htrace : WordTrace (prefixWord ++ tailWord_2916153) baseStart_2916153 baseEnd_2916153 := by
    simpa [prefixWord, tailWord_2916153, baseEnd_2916153] using wordTrace_append hprefix tailTrace_2916153
  have hstable : (prefixWord ++ tailWord_2916153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2916153).length < 2 ^ (prefixWord ++ tailWord_2916153).sum := by decide
  have hdescent : baseEnd_2916153 < baseStart_2916153 := by decide
  rcases family_descends (prefixWord ++ tailWord_2916153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2916166 : List Nat := [6, 1, 1, 2, 1, 2, 1, 2, 2, 5]
def baseStart_2916166 : Nat := 118140960795 + 2916166 * 2 ^ 59
def prefixEnd_2916166 : Nat := 4983230072969 + 3 ^ 40 * 2916166 * 2
def baseEnd_2916166 : Nat := 499131608766447573604601

theorem tailTrace_2916166 : CollatzResearch.WordTrace tailWord_2916166 prefixEnd_2916166 499131608766447573604601 := by
  unfold tailWord_2916166
  simp only [CollatzResearch.WordTrace]
  refine ⟨3323790998538628073337511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 70907541302157398897866901 3323790998538628073337511)
  ·
    refine ⟨4985686497807942110006267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3323790998538628073337511 4985686497807942110006267)
    ·
      refine ⟨7478529746711913165009401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4985686497807942110006267 7478529746711913165009401)
      ·
        refine ⟨5608897310033934873757051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7478529746711913165009401 5608897310033934873757051)
        ·
          refine ⟨8413345965050902310635577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5608897310033934873757051 8413345965050902310635577)
          ·
            refine ⟨6310009473788176732976683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8413345965050902310635577 6310009473788176732976683)
            ·
              refine ⟨9465014210682265099465025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6310009473788176732976683 9465014210682265099465025)
              ·
                refine ⟨7098760658011698824598769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9465014210682265099465025 7098760658011698824598769)
                ·
                  refine ⟨5324070493508774118449077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7098760658011698824598769 5324070493508774118449077)
                  ·
                    refine ⟨499131608766447573604601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5324070493508774118449077 499131608766447573604601)
                    ·
                      rfl

theorem cell23_2916166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 2, 2, 5].length) (baseStart_2916166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2916166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2916166 prefixEnd_2916166 := by exact prefixLift 2916166
  have htrace : WordTrace (prefixWord ++ tailWord_2916166) baseStart_2916166 baseEnd_2916166 := by
    simpa [prefixWord, tailWord_2916166, baseEnd_2916166] using wordTrace_append hprefix tailTrace_2916166
  have hstable : (prefixWord ++ tailWord_2916166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2916166).length < 2 ^ (prefixWord ++ tailWord_2916166).sum := by decide
  have hdescent : baseEnd_2916166 < baseStart_2916166 := by decide
  rcases family_descends (prefixWord ++ tailWord_2916166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2916192 : List Nat := [2, 1, 1, 3, 3, 3, 1, 3, 6]
def baseStart_2916192 : Nat := 118140960795 + 2916192 * 2 ^ 59
def prefixEnd_2916192 : Nat := 4983230072969 + 3 ^ 40 * 2916192 * 2
def baseEnd_2916192 : Nat := 166378686310706624343187

theorem tailTrace_2916192 : CollatzResearch.WordTrace tailWord_2916192 prefixEnd_2916192 166378686310706624343187 := by
  unfold tailWord_2916192
  simp only [CollatzResearch.WordTrace]
  refine ⟨53181130125570952393623415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70908173500761269858164553 53181130125570952393623415)
  ·
    refine ⟨79771695188356428590435123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53181130125570952393623415 79771695188356428590435123)
    ·
      refine ⟨119657542782534642885652685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79771695188356428590435123 119657542782534642885652685)
      ·
        refine ⟨44871578543450491082119757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119657542782534642885652685 44871578543450491082119757)
        ·
          refine ⟨16826841953793934155794909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44871578543450491082119757 16826841953793934155794909)
          ·
            refine ⟨6310065732672725308423091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16826841953793934155794909 6310065732672725308423091)
            ·
              refine ⟨9465098599009087962634637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6310065732672725308423091 9465098599009087962634637)
              ·
                refine ⟨3549411974628407985987989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9465098599009087962634637 3549411974628407985987989)
                ·
                  refine ⟨166378686310706624343187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3549411974628407985987989 166378686310706624343187)
                  ·
                    rfl

theorem cell23_2916192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 3, 6].length) (baseStart_2916192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2916192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2916192 prefixEnd_2916192 := by exact prefixLift 2916192
  have htrace : WordTrace (prefixWord ++ tailWord_2916192) baseStart_2916192 baseEnd_2916192 := by
    simpa [prefixWord, tailWord_2916192, baseEnd_2916192] using wordTrace_append hprefix tailTrace_2916192
  have hstable : (prefixWord ++ tailWord_2916192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2916192).length < 2 ^ (prefixWord ++ tailWord_2916192).sum := by decide
  have hdescent : baseEnd_2916192 < baseStart_2916192 := by decide
  rcases family_descends (prefixWord ++ tailWord_2916192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2916206 : List Nat := [4, 1, 2, 3, 1, 2, 2, 1, 2, 2, 3]
def baseStart_2916206 : Nat := 118140960795 + 2916206 * 2 ^ 59
def prefixEnd_2916206 : Nat := 4983230072969 + 3 ^ 40 * 2916206 * 2
def baseEnd_2916206 : Nat := 1497415365525522564313619

theorem tailTrace_2916206 : CollatzResearch.WordTrace tailWord_2916206 prefixEnd_2916206 1497415365525522564313619 := by
  unfold tailWord_2916206
  simp only [CollatzResearch.WordTrace]
  refine ⟨13295346359136398147282059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70908513915394123452170981 13295346359136398147282059)
  ·
    refine ⟨19943019538704597220923089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13295346359136398147282059 19943019538704597220923089)
    ·
      refine ⟨14957264654028447915692317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19943019538704597220923089 14957264654028447915692317)
      ·
        refine ⟨5608974245260667968384619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14957264654028447915692317 5608974245260667968384619)
        ·
          refine ⟨8413461367891001952576929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5608974245260667968384619 8413461367891001952576929)
          ·
            refine ⟨6310096025918251464432697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8413461367891001952576929 6310096025918251464432697)
            ·
              refine ⟨4732572019438688598324523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6310096025918251464432697 4732572019438688598324523)
              ·
                refine ⟨7098858029158032897486785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4732572019438688598324523 7098858029158032897486785)
                ·
                  refine ⟨5324143521868524673115089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7098858029158032897486785 5324143521868524673115089)
                  ·
                    refine ⟨3993107641401393504836317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5324143521868524673115089 3993107641401393504836317)
                    ·
                      refine ⟨1497415365525522564313619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3993107641401393504836317 1497415365525522564313619)
                      ·
                        rfl

theorem cell23_2916206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_2916206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2916206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2916206 prefixEnd_2916206 := by exact prefixLift 2916206
  have htrace : WordTrace (prefixWord ++ tailWord_2916206) baseStart_2916206 baseEnd_2916206 := by
    simpa [prefixWord, tailWord_2916206, baseEnd_2916206] using wordTrace_append hprefix tailTrace_2916206
  have hstable : (prefixWord ++ tailWord_2916206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2916206).length < 2 ^ (prefixWord ++ tailWord_2916206).sum := by decide
  have hdescent : baseEnd_2916206 < baseStart_2916206 := by decide
  rcases family_descends (prefixWord ++ tailWord_2916206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2916229 : List Nat := [1, 3, 1, 1, 3, 2, 1, 4, 2, 3, 2]
def baseStart_2916229 : Nat := 118140960795 + 2916229 * 2 ^ 59
def prefixEnd_2916229 : Nat := 4983230072969 + 3 ^ 40 * 2916229 * 2
def baseEnd_2916229 : Nat := 1497427175580575974326013

theorem tailTrace_2916229 : CollatzResearch.WordTrace tailWord_2916229 prefixEnd_2916229 1497427175580575974326013 := by
  unfold tailWord_2916229
  simp only [CollatzResearch.WordTrace]
  refine ⟨106363609752007860106343741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70909073168005240070895827 106363609752007860106343741)
  ·
    refine ⟨39886353657002947539878903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106363609752007860106343741 39886353657002947539878903)
    ·
      refine ⟨59829530485504421309818355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39886353657002947539878903 59829530485504421309818355)
      ·
        refine ⟨89744295728256631964727533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59829530485504421309818355 89744295728256631964727533)
        ·
          refine ⟨33654110898096236986772825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89744295728256631964727533 33654110898096236986772825)
          ·
            refine ⟨25240583173572177740079619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33654110898096236986772825 25240583173572177740079619)
            ·
              refine ⟨37860874760358266610119429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25240583173572177740079619 37860874760358266610119429)
              ·
                refine ⟨7098914017567174989397393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37860874760358266610119429 7098914017567174989397393)
                ·
                  refine ⟨5324185513175381242048045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7098914017567174989397393 5324185513175381242048045)
                  ·
                    refine ⟨1996569567440767965768017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5324185513175381242048045 1996569567440767965768017)
                    ·
                      refine ⟨1497427175580575974326013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1996569567440767965768017 1497427175580575974326013)
                      ·
                        rfl

theorem cell23_2916229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 4, 2, 3, 2].length) (baseStart_2916229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2916229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2916229 prefixEnd_2916229 := by exact prefixLift 2916229
  have htrace : WordTrace (prefixWord ++ tailWord_2916229) baseStart_2916229 baseEnd_2916229 := by
    simpa [prefixWord, tailWord_2916229, baseEnd_2916229] using wordTrace_append hprefix tailTrace_2916229
  have hstable : (prefixWord ++ tailWord_2916229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2916229).length < 2 ^ (prefixWord ++ tailWord_2916229).sum := by decide
  have hdescent : baseEnd_2916229 < baseStart_2916229 := by decide
  rcases family_descends (prefixWord ++ tailWord_2916229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2916235 : List Nat := [1, 1, 1, 1, 4, 2, 1, 1, 5, 6]
def baseStart_2916235 : Nat := 118140960795 + 2916235 * 2 ^ 59
def prefixEnd_2916235 : Nat := 4983230072969 + 3 ^ 40 * 2916235 * 2
def baseEnd_2916235 : Nat := 499143418821500983616995

theorem tailTrace_2916235 : CollatzResearch.WordTrace tailWord_2916235 prefixEnd_2916235 499143418821500983616995 := by
  unfold tailWord_2916235
  simp only [CollatzResearch.WordTrace]
  refine ⟨106363828589986123131062159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70909219059990748754041439 106363828589986123131062159)
  ·
    refine ⟨159545742884979184696593239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106363828589986123131062159 159545742884979184696593239)
    ·
      refine ⟨239318614327468777044889859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159545742884979184696593239 239318614327468777044889859)
      ·
        refine ⟨358977921491203165567334789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239318614327468777044889859 358977921491203165567334789)
        ·
          refine ⟨67308360279600593543875273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 358977921491203165567334789 67308360279600593543875273)
          ·
            refine ⟨50481270209700445157906455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67308360279600593543875273 50481270209700445157906455)
            ·
              refine ⟨75721905314550667736859683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50481270209700445157906455 75721905314550667736859683)
              ·
                refine ⟨113582857971826001605289525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75721905314550667736859683 113582857971826001605289525)
                ·
                  refine ⟨10648392934858687650495893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 113582857971826001605289525 10648392934858687650495893)
                  ·
                    refine ⟨499143418821500983616995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10648392934858687650495893 499143418821500983616995)
                    ·
                      rfl

theorem cell23_2916235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 5, 6].length) (baseStart_2916235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2916235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2916235 prefixEnd_2916235 := by exact prefixLift 2916235
  have htrace : WordTrace (prefixWord ++ tailWord_2916235) baseStart_2916235 baseEnd_2916235 := by
    simpa [prefixWord, tailWord_2916235, baseEnd_2916235] using wordTrace_append hprefix tailTrace_2916235
  have hstable : (prefixWord ++ tailWord_2916235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2916235).length < 2 ^ (prefixWord ++ tailWord_2916235).sum := by decide
  have hdescent : baseEnd_2916235 < baseStart_2916235 := by decide
  rcases family_descends (prefixWord ++ tailWord_2916235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2916263 : List Nat := [1, 1, 6, 1, 2, 3, 1, 1, 2, 3, 2]
def baseStart_2916263 : Nat := 118140960795 + 2916263 * 2 ^ 59
def prefixEnd_2916263 : Nat := 4983230072969 + 3 ^ 40 * 2916263 * 2
def baseEnd_2916263 : Nat := 1497444633922828841300857

theorem tailTrace_2916263 : CollatzResearch.WordTrace tailWord_2916263 prefixEnd_2916263 1497444633922828841300857 := by
  unfold tailWord_2916263
  simp only [CollatzResearch.WordTrace]
  refine ⟨106364849833884683913081443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70909899889256455942054295 106364849833884683913081443)
  ·
    refine ⟨159547274750827025869622165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106364849833884683913081443 159547274750827025869622165)
    ·
      refine ⟨7478778503945016837638539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 159547274750827025869622165 7478778503945016837638539)
      ·
        refine ⟨11218167755917525256457809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7478778503945016837638539 11218167755917525256457809)
        ·
          refine ⟨8413625816938143942343357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11218167755917525256457809 8413625816938143942343357)
          ·
            refine ⟨3155109681351803978378759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8413625816938143942343357 3155109681351803978378759)
            ·
              refine ⟨4732664522027705967568139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3155109681351803978378759 4732664522027705967568139)
              ·
                refine ⟨7098996783041558951352209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4732664522027705967568139 7098996783041558951352209)
                ·
                  refine ⟨5324247587281169213514157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7098996783041558951352209 5324247587281169213514157)
                  ·
                    refine ⟨1996592845230438455067809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5324247587281169213514157 1996592845230438455067809)
                    ·
                      refine ⟨1497444633922828841300857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1996592845230438455067809 1497444633922828841300857)
                      ·
                        rfl

theorem cell23_2916263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 1, 1, 2, 3, 2].length) (baseStart_2916263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2916263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2916263 prefixEnd_2916263 := by exact prefixLift 2916263
  have htrace : WordTrace (prefixWord ++ tailWord_2916263) baseStart_2916263 baseEnd_2916263 := by
    simpa [prefixWord, tailWord_2916263, baseEnd_2916263] using wordTrace_append hprefix tailTrace_2916263
  have hstable : (prefixWord ++ tailWord_2916263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2916263).length < 2 ^ (prefixWord ++ tailWord_2916263).sum := by decide
  have hdescent : baseEnd_2916263 < baseStart_2916263 := by decide
  rcases family_descends (prefixWord ++ tailWord_2916263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2916286 : List Nat := [4, 2, 1, 1, 1, 3, 3, 2, 2, 4]
def baseStart_2916286 : Nat := 118140960795 + 2916286 * 2 ^ 59
def prefixEnd_2916286 : Nat := 4983230072969 + 3 ^ 40 * 2916286 * 2
def baseEnd_2916286 : Nat := 499152147992627417104417

theorem tailTrace_2916286 : CollatzResearch.WordTrace tailWord_2916286 prefixEnd_2916286 499152147992627417104417 := by
  unfold tailWord_2916286
  simp only [CollatzResearch.WordTrace]
  refine ⟨13295711089100169855146089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70910459141867572560779141 13295711089100169855146089)
  ·
    refine ⟨9971783316825127391359567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13295711089100169855146089 9971783316825127391359567)
    ·
      refine ⟨14957674975237691087039351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9971783316825127391359567 14957674975237691087039351)
      ·
        refine ⟨22436512462856536630559027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14957674975237691087039351 22436512462856536630559027)
        ·
          refine ⟨33654768694284804945838541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22436512462856536630559027 33654768694284804945838541)
          ·
            refine ⟨12620538260356801854689453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33654768694284804945838541 12620538260356801854689453)
            ·
              refine ⟨4732701847633800695508545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12620538260356801854689453 4732701847633800695508545)
              ·
                refine ⟨3549526385725350521631409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4732701847633800695508545 3549526385725350521631409)
                ·
                  refine ⟨2662144789294012891223557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3549526385725350521631409 2662144789294012891223557)
                  ·
                    refine ⟨499152147992627417104417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2662144789294012891223557 499152147992627417104417)
                    ·
                      rfl

theorem cell23_2916286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 3, 2, 2, 4].length) (baseStart_2916286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2916286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2916286 prefixEnd_2916286 := by exact prefixLift 2916286
  have htrace : WordTrace (prefixWord ++ tailWord_2916286) baseStart_2916286 baseEnd_2916286 := by
    simpa [prefixWord, tailWord_2916286, baseEnd_2916286] using wordTrace_append hprefix tailTrace_2916286
  have hstable : (prefixWord ++ tailWord_2916286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2916286).length < 2 ^ (prefixWord ++ tailWord_2916286).sum := by decide
  have hdescent : baseEnd_2916286 < baseStart_2916286 := by decide
  rcases family_descends (prefixWord ++ tailWord_2916286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2916327 : List Nat := [1, 1, 5, 2, 3, 2, 1, 3, 1, 2, 2]
def baseStart_2916327 : Nat := 118140960795 + 2916327 * 2 ^ 59
def prefixEnd_2916327 : Nat := 4983230072969 + 3 ^ 40 * 2916327 * 2
def baseEnd_2916327 : Nat := 1497477496684716590900563

theorem tailTrace_2916327 : CollatzResearch.WordTrace tailWord_2916327 prefixEnd_2916327 1497477496684716590900563 := by
  unfold tailWord_2916327
  simp only [CollatzResearch.WordTrace]
  refine ⟨106367184105652822843411235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70911456070435215228940823 106367184105652822843411235)
  ·
    refine ⟨159550776158479234265116853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106367184105652822843411235 159550776158479234265116853)
    ·
      refine ⟨14957885264857428212354705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 159550776158479234265116853 14957885264857428212354705)
      ·
        refine ⟨11218413948643071159266029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14957885264857428212354705 11218413948643071159266029)
        ·
          refine ⟨4206905230741151684724761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11218413948643071159266029 4206905230741151684724761)
          ·
            refine ⟨3155178923055863763543571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4206905230741151684724761 3155178923055863763543571)
            ·
              refine ⟨4732768384583795645315357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3155178923055863763543571 4732768384583795645315357)
              ·
                refine ⟨1774788144218923366993259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4732768384583795645315357 1774788144218923366993259)
                ·
                  refine ⟨2662182216328385050489889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1774788144218923366993259 2662182216328385050489889)
                  ·
                    refine ⟨1996636662246288787867417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2662182216328385050489889 1996636662246288787867417)
                    ·
                      refine ⟨1497477496684716590900563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1996636662246288787867417 1497477496684716590900563)
                      ·
                        rfl

theorem cell23_2916327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 1, 3, 1, 2, 2].length) (baseStart_2916327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2916327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2916327 prefixEnd_2916327 := by exact prefixLift 2916327
  have htrace : WordTrace (prefixWord ++ tailWord_2916327) baseStart_2916327 baseEnd_2916327 := by
    simpa [prefixWord, tailWord_2916327, baseEnd_2916327] using wordTrace_append hprefix tailTrace_2916327
  have hstable : (prefixWord ++ tailWord_2916327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2916327).length < 2 ^ (prefixWord ++ tailWord_2916327).sum := by decide
  have hdescent : baseEnd_2916327 < baseStart_2916327 := by decide
  rcases family_descends (prefixWord ++ tailWord_2916327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2916336 : List Nat := [2, 1, 1, 1, 3, 2, 4, 3, 1, 3, 2]
def baseStart_2916336 : Nat := 118140960795 + 2916336 * 2 ^ 59
def prefixEnd_2916336 : Nat := 4983230072969 + 3 ^ 40 * 2916336 * 2
def baseEnd_2916336 : Nat := 1497482118010607055688021

theorem tailTrace_2916336 : CollatzResearch.WordTrace tailWord_2916336 prefixEnd_2916336 1497482118010607055688021 := by
  unfold tailWord_2916336
  simp only [CollatzResearch.WordTrace]
  refine ⟨53183756181310108690244431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70911674908413478253659241 53183756181310108690244431)
  ·
    refine ⟨79775634271965163035366647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53183756181310108690244431 79775634271965163035366647)
    ·
      refine ⟨119663451407947744553049971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79775634271965163035366647 119663451407947744553049971)
      ·
        refine ⟨179495177111921616829574957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119663451407947744553049971 179495177111921616829574957)
        ·
          refine ⟨67310691416970606311090609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 179495177111921616829574957 67310691416970606311090609)
          ·
            refine ⟨50483018562727954733317957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67310691416970606311090609 50483018562727954733317957)
            ·
              refine ⟨9465565980511491512497117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50483018562727954733317957 9465565980511491512497117)
              ·
                refine ⟨3549587242691809317186419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9465565980511491512497117 3549587242691809317186419)
                ·
                  refine ⟨5324380864037713975779629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3549587242691809317186419 5324380864037713975779629)
                  ·
                    refine ⟨1996642824014142740917361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5324380864037713975779629 1996642824014142740917361)
                    ·
                      refine ⟨1497482118010607055688021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1996642824014142740917361 1497482118010607055688021)
                      ·
                        rfl

theorem cell23_2916336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 3, 1, 3, 2].length) (baseStart_2916336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2916336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2916336 prefixEnd_2916336 := by exact prefixLift 2916336
  have htrace : WordTrace (prefixWord ++ tailWord_2916336) baseStart_2916336 baseEnd_2916336 := by
    simpa [prefixWord, tailWord_2916336, baseEnd_2916336] using wordTrace_append hprefix tailTrace_2916336
  have hstable : (prefixWord ++ tailWord_2916336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2916336).length < 2 ^ (prefixWord ++ tailWord_2916336).sum := by decide
  have hdescent : baseEnd_2916336 < baseStart_2916336 := by decide
  rcases family_descends (prefixWord ++ tailWord_2916336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2916366 : List Nat := [4, 1, 1, 2, 2, 1, 2, 3, 1, 4, 2]
def baseStart_2916366 : Nat := 118140960795 + 2916366 * 2 ^ 59
def prefixEnd_2916366 : Nat := 4983230072969 + 3 ^ 40 * 2916366 * 2
def baseEnd_2916366 : Nat := 1497497522430241938312883

theorem tailTrace_2916366 : CollatzResearch.WordTrace tailWord_2916366 prefixEnd_2916366 1497497522430241938312883 := by
  unfold tailWord_2916366
  simp only [CollatzResearch.WordTrace]
  refine ⟨13296075819063941563010119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70912404368341021669387301 13296075819063941563010119)
  ·
    refine ⟨19944113728595912344515179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13296075819063941563010119 19944113728595912344515179)
    ·
      refine ⟨29916170592893868516772769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19944113728595912344515179 29916170592893868516772769)
      ·
        refine ⟨22437127944670401387579577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29916170592893868516772769 22437127944670401387579577)
        ·
          refine ⟨16827845958502801040684683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22437127944670401387579577 16827845958502801040684683)
          ·
            refine ⟨25241768937754201561027025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16827845958502801040684683 25241768937754201561027025)
            ·
              refine ⟨18931326703315651170770269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25241768937754201561027025 18931326703315651170770269)
              ·
                refine ⟨7099247513743369189038851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18931326703315651170770269 7099247513743369189038851)
                ·
                  refine ⟨10648871270615053783558277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7099247513743369189038851 10648871270615053783558277)
                  ·
                    refine ⟨1996663363240322584417177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10648871270615053783558277 1996663363240322584417177)
                    ·
                      refine ⟨1497497522430241938312883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1996663363240322584417177 1497497522430241938312883)
                      ·
                        rfl

theorem cell23_2916366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 3, 1, 4, 2].length) (baseStart_2916366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2916366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2916366 prefixEnd_2916366 := by exact prefixLift 2916366
  have htrace : WordTrace (prefixWord ++ tailWord_2916366) baseStart_2916366 baseEnd_2916366 := by
    simpa [prefixWord, tailWord_2916366, baseEnd_2916366] using wordTrace_append hprefix tailTrace_2916366
  have hstable : (prefixWord ++ tailWord_2916366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2916366).length < 2 ^ (prefixWord ++ tailWord_2916366).sum := by decide
  have hdescent : baseEnd_2916366 < baseStart_2916366 := by decide
  rcases family_descends (prefixWord ++ tailWord_2916366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2916449 : List Nat := [1, 2, 3, 1, 1, 2, 1, 1, 7, 4]
def baseStart_2916449 : Nat := 118140960795 + 2916449 * 2 ^ 59
def prefixEnd_2916449 : Nat := 4983230072969 + 3 ^ 40 * 2916449 * 2
def baseEnd_2916449 : Nat := 499180047108188371191667

theorem tailTrace_2916449 : CollatzResearch.WordTrace tailWord_2916449 prefixEnd_2916449 499180047108188371191667 := by
  unfold tailWord_2916449
  simp only [CollatzResearch.WordTrace]
  refine ⟨106371633811210837679352401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70914422540807225119568267 106371633811210837679352401)
  ·
    refine ⟨79778725358408128259514301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106371633811210837679352401 79778725358408128259514301)
    ·
      refine ⟨29917022009403048097317863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79778725358408128259514301 29917022009403048097317863)
      ·
        refine ⟨44875533014104572145976795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29917022009403048097317863 44875533014104572145976795)
        ·
          refine ⟨67313299521156858218965193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44875533014104572145976795 67313299521156858218965193)
          ·
            refine ⟨50484974640867643664223895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67313299521156858218965193 50484974640867643664223895)
            ·
              refine ⟨75727461961301465496335843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50484974640867643664223895 75727461961301465496335843)
              ·
                refine ⟨113591192941952198244503765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75727461961301465496335843 113591192941952198244503765)
                ·
                  refine ⟨2662293584577004646355557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 113591192941952198244503765 2662293584577004646355557)
                  ·
                    refine ⟨499180047108188371191667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2662293584577004646355557 499180047108188371191667)
                    ·
                      rfl

theorem cell23_2916449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 7, 4].length) (baseStart_2916449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2916449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2916449 prefixEnd_2916449 := by exact prefixLift 2916449
  have htrace : WordTrace (prefixWord ++ tailWord_2916449) baseStart_2916449 baseEnd_2916449 := by
    simpa [prefixWord, tailWord_2916449, baseEnd_2916449] using wordTrace_append hprefix tailTrace_2916449
  have hstable : (prefixWord ++ tailWord_2916449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2916449).length < 2 ^ (prefixWord ++ tailWord_2916449).sum := by decide
  have hdescent : baseEnd_2916449 < baseStart_2916449 := by decide
  rcases family_descends (prefixWord ++ tailWord_2916449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2916466 : List Nat := [3, 2, 1, 2, 2, 2, 1, 3, 3, 4]
def baseStart_2916466 : Nat := 118140960795 + 2916466 * 2 ^ 59
def prefixEnd_2916466 : Nat := 4983230072969 + 3 ^ 40 * 2916466 * 2
def baseEnd_2916466 : Nat := 499182956831897182354141

theorem tailTrace_2916466 : CollatzResearch.WordTrace tailWord_2916466 prefixEnd_2916466 499182956831897182354141 := by
  unfold tailWord_2916466
  simp only [CollatzResearch.WordTrace]
  refine ⟨26593063463037312395680313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70914835901432833055147501 26593063463037312395680313)
  ·
    refine ⟨19944797597277984296760235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26593063463037312395680313 19944797597277984296760235)
    ·
      refine ⟨29917196395916976445140353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19944797597277984296760235 29917196395916976445140353)
      ·
        refine ⟨22437897296937732333855265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29917196395916976445140353 22437897296937732333855265)
        ·
          refine ⟨16828422972703299250391449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22437897296937732333855265 16828422972703299250391449)
          ·
            refine ⟨12621317229527474437793587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16828422972703299250391449 12621317229527474437793587)
            ·
              refine ⟨18931975844291211656690381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12621317229527474437793587 18931975844291211656690381)
              ·
                refine ⟨7099490941609204371258893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18931975844291211656690381 7099490941609204371258893)
                ·
                  refine ⟨2662309103103451639222085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7099490941609204371258893 2662309103103451639222085)
                  ·
                    refine ⟨499182956831897182354141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2662309103103451639222085 499182956831897182354141)
                    ·
                      rfl

theorem cell23_2916466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 3, 3, 4].length) (baseStart_2916466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2916466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2916466 prefixEnd_2916466 := by exact prefixLift 2916466
  have htrace : WordTrace (prefixWord ++ tailWord_2916466) baseStart_2916466 baseEnd_2916466 := by
    simpa [prefixWord, tailWord_2916466, baseEnd_2916466] using wordTrace_append hprefix tailTrace_2916466
  have hstable : (prefixWord ++ tailWord_2916466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2916466).length < 2 ^ (prefixWord ++ tailWord_2916466).sum := by decide
  have hdescent : baseEnd_2916466 < baseStart_2916466 := by decide
  rcases family_descends (prefixWord ++ tailWord_2916466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2916489 : List Nat := [1, 2, 1, 1, 4, 2, 1, 1, 2, 5, 3]
def baseStart_2916489 : Nat := 118140960795 + 2916489 * 2 ^ 59
def prefixEnd_2916489 : Nat := 4983230072969 + 3 ^ 40 * 2916489 * 2
def baseEnd_2916489 : Nat := 1497560680550744957074817

theorem tailTrace_2916489 : CollatzResearch.WordTrace tailWord_2916489 prefixEnd_2916489 1497560680550744957074817 := by
  unfold tailWord_2916489
  simp only [CollatzResearch.WordTrace]
  refine ⟨106373092731065924510808521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70915395154043949673872347 106373092731065924510808521)
  ·
    refine ⟨79779819548299443383106391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106373092731065924510808521 79779819548299443383106391)
    ·
      refine ⟨119669729322449165074659587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79779819548299443383106391 119669729322449165074659587)
      ·
        refine ⟨179504593983673747611989381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119669729322449165074659587 179504593983673747611989381)
        ·
          refine ⟨33657111371938827677248009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 179504593983673747611989381 33657111371938827677248009)
          ·
            refine ⟨25242833528954120757936007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33657111371938827677248009 25242833528954120757936007)
            ·
              refine ⟨37864250293431181136904011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25242833528954120757936007 37864250293431181136904011)
              ·
                refine ⟨56796375440146771705356017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37864250293431181136904011 56796375440146771705356017)
                ·
                  refine ⟨42597281580110078779017013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56796375440146771705356017 42597281580110078779017013)
                  ·
                    refine ⟨3993495148135319885532845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42597281580110078779017013 3993495148135319885532845)
                    ·
                      refine ⟨1497560680550744957074817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3993495148135319885532845 1497560680550744957074817)
                      ·
                        rfl

theorem cell23_2916489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 1, 2, 5, 3].length) (baseStart_2916489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2916489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2916489 prefixEnd_2916489 := by exact prefixLift 2916489
  have htrace : WordTrace (prefixWord ++ tailWord_2916489) baseStart_2916489 baseEnd_2916489 := by
    simpa [prefixWord, tailWord_2916489, baseEnd_2916489] using wordTrace_append hprefix tailTrace_2916489
  have hstable : (prefixWord ++ tailWord_2916489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2916489).length < 2 ^ (prefixWord ++ tailWord_2916489).sum := by decide
  have hdescent : baseEnd_2916489 < baseStart_2916489 := by decide
  rcases family_descends (prefixWord ++ tailWord_2916489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2916510 : List Nat := [4, 3, 1, 1, 3, 1, 1, 2, 2, 2, 3]
def baseStart_2916510 : Nat := 118140960795 + 2916510 * 2 ^ 59
def prefixEnd_2916510 : Nat := 4983230072969 + 3 ^ 40 * 2916510 * 2
def baseEnd_2916510 : Nat := 1497571463644489374912221

theorem tailTrace_2916510 : CollatzResearch.WordTrace tailWord_2916510 prefixEnd_2916510 1497571463644489374912221 := by
  unfold tailWord_2916510
  simp only [CollatzResearch.WordTrace]
  refine ⟨13296732332998730637165373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70915905775993230064881989 13296732332998730637165373)
  ·
    refine ⟨4986274624874523988937015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13296732332998730637165373 4986274624874523988937015)
    ·
      refine ⟨7479411937311785983405523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4986274624874523988937015 7479411937311785983405523)
      ·
        refine ⟨11219117905967678975108285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7479411937311785983405523 11219117905967678975108285)
        ·
          refine ⟨4207169214737879615665607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11219117905967678975108285 4207169214737879615665607)
          ·
            refine ⟨6310753822106819423498411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4207169214737879615665607 6310753822106819423498411)
            ·
              refine ⟨9466130733160229135247617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6310753822106819423498411 9466130733160229135247617)
              ·
                refine ⟨7099598049870171851435713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9466130733160229135247617 7099598049870171851435713)
                ·
                  refine ⟨5324698537402628888576785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7099598049870171851435713 5324698537402628888576785)
                  ·
                    refine ⟨3993523903051971666432589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5324698537402628888576785 3993523903051971666432589)
                    ·
                      refine ⟨1497571463644489374912221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3993523903051971666432589 1497571463644489374912221)
                      ·
                        rfl

theorem cell23_2916510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 2, 2, 2, 3].length) (baseStart_2916510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2916510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2916510 prefixEnd_2916510 := by exact prefixLift 2916510
  have htrace : WordTrace (prefixWord ++ tailWord_2916510) baseStart_2916510 baseEnd_2916510 := by
    simpa [prefixWord, tailWord_2916510, baseEnd_2916510] using wordTrace_append hprefix tailTrace_2916510
  have hstable : (prefixWord ++ tailWord_2916510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2916510).length < 2 ^ (prefixWord ++ tailWord_2916510).sum := by decide
  have hdescent : baseEnd_2916510 < baseStart_2916510 := by decide
  rcases family_descends (prefixWord ++ tailWord_2916510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2916539 : List Nat := [1, 1, 1, 1, 1, 2, 6, 3, 1, 6]
def baseStart_2916539 : Nat := 118140960795 + 2916539 * 2 ^ 59
def prefixEnd_2916539 : Nat := 4983230072969 + 3 ^ 40 * 2916539 * 2
def baseEnd_2916539 : Nat := 499195451527823253816529

theorem tailTrace_2916539 : CollatzResearch.WordTrace tailWord_2916539 prefixEnd_2916539 499195451527823253816529 := by
  unfold tailWord_2916539
  simp only [CollatzResearch.WordTrace]
  refine ⟨106374916380884783050128671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70916610920589855366752447 106374916380884783050128671)
  ·
    refine ⟨159562374571327174575193007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106374916380884783050128671 159562374571327174575193007)
    ·
      refine ⟨239343561856990761862789511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159562374571327174575193007 239343561856990761862789511)
      ·
        refine ⟨359015342785486142794184267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239343561856990761862789511 359015342785486142794184267)
        ·
          refine ⟨538523014178229214191276401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 359015342785486142794184267 538523014178229214191276401)
          ·
            refine ⟨403892260633671910643457301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 538523014178229214191276401 403892260633671910643457301)
            ·
              refine ⟨18932449717203370811412061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 403892260633671910643457301 18932449717203370811412061)
              ·
                refine ⟨7099668643951264054279523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18932449717203370811412061 7099668643951264054279523)
                ·
                  refine ⟨10649502965926896081419285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7099668643951264054279523 10649502965926896081419285)
                  ·
                    refine ⟨499195451527823253816529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10649502965926896081419285 499195451527823253816529)
                    ·
                      rfl

theorem cell23_2916539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 3, 1, 6].length) (baseStart_2916539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2916539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2916539 prefixEnd_2916539 := by exact prefixLift 2916539
  have htrace : WordTrace (prefixWord ++ tailWord_2916539) baseStart_2916539 baseEnd_2916539 := by
    simpa [prefixWord, tailWord_2916539, baseEnd_2916539] using wordTrace_append hprefix tailTrace_2916539
  have hstable : (prefixWord ++ tailWord_2916539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2916539).length < 2 ^ (prefixWord ++ tailWord_2916539).sum := by decide
  have hdescent : baseEnd_2916539 < baseStart_2916539 := by decide
  rcases family_descends (prefixWord ++ tailWord_2916539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2916549 : List Nat := [1, 3, 1, 1, 1, 1, 4, 2, 3, 1, 5]
def baseStart_2916549 : Nat := 118140960795 + 2916549 * 2 ^ 59
def prefixEnd_2916549 : Nat := 4983230072969 + 3 ^ 40 * 2916549 * 2
def baseEnd_2916549 : Nat := 1497591489390014722324541

theorem tailTrace_2916549 : CollatzResearch.WordTrace tailWord_2916549 prefixEnd_2916549 1497591489390014722324541 := by
  unfold tailWord_2916549
  simp only [CollatzResearch.WordTrace]
  refine ⟨106375281110848554757992701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70916854073899036505328467 106375281110848554757992701)
  ·
    refine ⟨39890730416568208034247263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106375281110848554757992701 39890730416568208034247263)
    ·
      refine ⟨59836095624852312051370895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39890730416568208034247263 59836095624852312051370895)
      ·
        refine ⟨89754143437278468077056343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59836095624852312051370895 89754143437278468077056343)
        ·
          refine ⟨134631215155917702115584515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89754143437278468077056343 134631215155917702115584515)
          ·
            refine ⟨201946822733876553173376773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134631215155917702115584515 201946822733876553173376773)
            ·
              refine ⟨37865029262601853720008145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 201946822733876553173376773 37865029262601853720008145)
              ·
                refine ⟨28398771946951390290006109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37865029262601853720008145 28398771946951390290006109)
                ·
                  refine ⟨10649539480106771358752291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28398771946951390290006109 10649539480106771358752291)
                  ·
                    refine ⟨15974309220160157038128437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10649539480106771358752291 15974309220160157038128437)
                    ·
                      refine ⟨1497591489390014722324541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15974309220160157038128437 1497591489390014722324541)
                      ·
                        rfl

theorem cell23_2916549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 2, 3, 1, 5].length) (baseStart_2916549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2916549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2916549 prefixEnd_2916549 := by exact prefixLift 2916549
  have htrace : WordTrace (prefixWord ++ tailWord_2916549) baseStart_2916549 baseEnd_2916549 := by
    simpa [prefixWord, tailWord_2916549, baseEnd_2916549] using wordTrace_append hprefix tailTrace_2916549
  have hstable : (prefixWord ++ tailWord_2916549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2916549).length < 2 ^ (prefixWord ++ tailWord_2916549).sum := by decide
  have hdescent : baseEnd_2916549 < baseStart_2916549 := by decide
  rcases family_descends (prefixWord ++ tailWord_2916549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2916583 : List Nat := [1, 1, 5, 3, 1, 1, 1, 2, 3, 2, 3]
def baseStart_2916583 : Nat := 118140960795 + 2916583 * 2 ^ 59
def prefixEnd_2916583 : Nat := 4983230072969 + 3 ^ 40 * 2916583 * 2
def baseEnd_2916583 : Nat := 1497608947732267589299385

theorem tailTrace_2916583 : CollatzResearch.WordTrace tailWord_2916583 prefixEnd_2916583 1497608947732267589299385 := by
  unfold tailWord_2916583
  simp only [CollatzResearch.WordTrace]
  refine ⟨106376521192725378564730403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70917680795150252376486935 106376521192725378564730403)
  ·
    refine ⟨159564781789088067847095605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106376521192725378564730403 159564781789088067847095605)
    ·
      refine ⟨14959198292727006360665213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 159564781789088067847095605 14959198292727006360665213)
      ·
        refine ⟨5609699359772627385249455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14959198292727006360665213 5609699359772627385249455)
        ·
          refine ⟨8414549039658941077874183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5609699359772627385249455 8414549039658941077874183)
          ·
            refine ⟨12621823559488411616811275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8414549039658941077874183 12621823559488411616811275)
            ·
              refine ⟨18932735339232617425216913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12621823559488411616811275 18932735339232617425216913)
              ·
                refine ⟨14199551504424463068912685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18932735339232617425216913 14199551504424463068912685)
                ·
                  refine ⟨5324831814159173650842257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14199551504424463068912685 5324831814159173650842257)
                  ·
                    refine ⟨3993623860619380238131693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5324831814159173650842257 3993623860619380238131693)
                    ·
                      refine ⟨1497608947732267589299385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3993623860619380238131693 1497608947732267589299385)
                      ·
                        rfl

theorem cell23_2916583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_2916583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2916583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2916583 prefixEnd_2916583 := by exact prefixLift 2916583
  have htrace : WordTrace (prefixWord ++ tailWord_2916583) baseStart_2916583 baseEnd_2916583 := by
    simpa [prefixWord, tailWord_2916583, baseEnd_2916583] using wordTrace_append hprefix tailTrace_2916583
  have hstable : (prefixWord ++ tailWord_2916583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2916583).length < 2 ^ (prefixWord ++ tailWord_2916583).sum := by decide
  have hdescent : baseEnd_2916583 < baseStart_2916583 := by decide
  rcases family_descends (prefixWord ++ tailWord_2916583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2916657 : List Nat := [1, 2, 2, 3, 4, 1, 2, 2, 1, 3, 2]
def baseStart_2916657 : Nat := 118140960795 + 2916657 * 2 ^ 59
def prefixEnd_2916657 : Nat := 4983230072969 + 3 ^ 40 * 2916657 * 2
def baseEnd_2916657 : Nat := 1497646945300700299774045

theorem tailTrace_2916657 : CollatzResearch.WordTrace tailWord_2916657 prefixEnd_2916657 1497646945300700299774045 := by
  unfold tailWord_2916657
  simp only [CollatzResearch.WordTrace]
  refine ⟨106379220194457289202924225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70919480129638192801949483 106379220194457289202924225)
  ·
    refine ⟨79784415145842966902193169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106379220194457289202924225 79784415145842966902193169)
    ·
      refine ⟨59838311359382225176644877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79784415145842966902193169 59838311359382225176644877)
      ·
        refine ⟨22439366759768334441241829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59838311359382225176644877 22439366759768334441241829)
        ·
          refine ⟨4207381267456562707732843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22439366759768334441241829 4207381267456562707732843)
          ·
            refine ⟨6311071901184844061599265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4207381267456562707732843 6311071901184844061599265)
            ·
              refine ⟨4733303925888633046199449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6311071901184844061599265 4733303925888633046199449)
              ·
                refine ⟨3549977944416474784649587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4733303925888633046199449 3549977944416474784649587)
                ·
                  refine ⟨5324966916624712176974381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3549977944416474784649587 5324966916624712176974381)
                  ·
                    refine ⟨1996862593734267066365393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5324966916624712176974381 1996862593734267066365393)
                    ·
                      refine ⟨1497646945300700299774045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1996862593734267066365393 1497646945300700299774045)
                      ·
                        rfl

theorem cell23_2916657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 2, 2, 1, 3, 2].length) (baseStart_2916657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2916657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2916657 prefixEnd_2916657 := by exact prefixLift 2916657
  have htrace : WordTrace (prefixWord ++ tailWord_2916657) baseStart_2916657 baseEnd_2916657 := by
    simpa [prefixWord, tailWord_2916657, baseEnd_2916657] using wordTrace_append hprefix tailTrace_2916657
  have hstable : (prefixWord ++ tailWord_2916657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2916657).length < 2 ^ (prefixWord ++ tailWord_2916657).sum := by decide
  have hdescent : baseEnd_2916657 < baseStart_2916657 := by decide
  rcases family_descends (prefixWord ++ tailWord_2916657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2916743 : List Nat := [1, 1, 4, 2, 2, 1, 1, 4, 2, 1, 4]
def baseStart_2916743 : Nat := 118140960795 + 2916743 * 2 ^ 59
def prefixEnd_2916743 : Nat := 4983230072969 + 3 ^ 40 * 2916743 * 2
def baseEnd_2916743 : Nat := 1497691104636986963298649

theorem tailTrace_2916743 : CollatzResearch.WordTrace tailWord_2916743 prefixEnd_2916743 1497691104636986963298649 := by
  unfold tailWord_2916743
  simp only [CollatzResearch.WordTrace]
  refine ⟨106382356872145725890554883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70921571248097150593703255 106382356872145725890554883)
  ·
    refine ⟨159573535308218588835832325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106382356872145725890554883 159573535308218588835832325)
    ·
      refine ⟨29920037870290985406718561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 159573535308218588835832325 29920037870290985406718561)
      ·
        refine ⟨22440028402718239055038921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29920037870290985406718561 22440028402718239055038921)
        ·
          refine ⟨16830021302038679291279191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22440028402718239055038921 16830021302038679291279191)
          ·
            refine ⟨25245031953058018936918787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16830021302038679291279191 25245031953058018936918787)
            ·
              refine ⟨37867547929587028405378181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25245031953058018936918787 37867547929587028405378181)
              ·
                refine ⟨7100165236797567826008409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37867547929587028405378181 7100165236797567826008409)
                ·
                  refine ⟨5325123927598175869506307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7100165236797567826008409 5325123927598175869506307)
                  ·
                    refine ⟨7987685891397263804259461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5325123927598175869506307 7987685891397263804259461)
                    ·
                      refine ⟨1497691104636986963298649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7987685891397263804259461 1497691104636986963298649)
                      ·
                        rfl

theorem cell23_2916743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 4, 2, 1, 4].length) (baseStart_2916743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2916743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2916743 prefixEnd_2916743 := by exact prefixLift 2916743
  have htrace : WordTrace (prefixWord ++ tailWord_2916743) baseStart_2916743 baseEnd_2916743 := by
    simpa [prefixWord, tailWord_2916743, baseEnd_2916743] using wordTrace_append hprefix tailTrace_2916743
  have hstable : (prefixWord ++ tailWord_2916743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2916743).length < 2 ^ (prefixWord ++ tailWord_2916743).sum := by decide
  have hdescent : baseEnd_2916743 < baseStart_2916743 := by decide
  rcases family_descends (prefixWord ++ tailWord_2916743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2916760 : List Nat := [2, 1, 2, 5, 1, 1, 1, 1, 1, 6, 2]
def baseStart_2916760 : Nat := 118140960795 + 2916760 * 2 ^ 59
def prefixEnd_2916760 : Nat := 4983230072969 + 3 ^ 40 * 2916760 * 2
def baseEnd_2916760 : Nat := 1497699833808113396786071

theorem tailTrace_2916760 : CollatzResearch.WordTrace tailWord_2916760 prefixEnd_2916760 1497699833808113396786071 := by
  unfold tailWord_2916760
  simp only [CollatzResearch.WordTrace]
  refine ⟨53191488456542068896961867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70921984608722758529282489 53191488456542068896961867)
  ·
    refine ⟨79787232684813103345442801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53191488456542068896961867 79787232684813103345442801)
    ·
      refine ⟨59840424513609827509082101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79787232684813103345442801 59840424513609827509082101)
      ·
        refine ⟨5610039798150921328976447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 59840424513609827509082101 5610039798150921328976447)
        ·
          refine ⟨8415059697226381993464671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5610039798150921328976447 8415059697226381993464671)
          ·
            refine ⟨12622589545839572990197007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8415059697226381993464671 12622589545839572990197007)
            ·
              refine ⟨18933884318759359485295511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12622589545839572990197007 18933884318759359485295511)
              ·
                refine ⟨28400826478139039227943267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18933884318759359485295511 28400826478139039227943267)
                ·
                  refine ⟨42601239717208558841914901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28400826478139039227943267 42601239717208558841914901)
                  ·
                    refine ⟨1996933111744151195714761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 42601239717208558841914901 1996933111744151195714761)
                    ·
                      refine ⟨1497699833808113396786071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1996933111744151195714761 1497699833808113396786071)
                      ·
                        rfl

theorem cell23_2916760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 1, 1, 6, 2].length) (baseStart_2916760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2916760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2916760 prefixEnd_2916760 := by exact prefixLift 2916760
  have htrace : WordTrace (prefixWord ++ tailWord_2916760) baseStart_2916760 baseEnd_2916760 := by
    simpa [prefixWord, tailWord_2916760, baseEnd_2916760] using wordTrace_append hprefix tailTrace_2916760
  have hstable : (prefixWord ++ tailWord_2916760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2916760).length < 2 ^ (prefixWord ++ tailWord_2916760).sum := by decide
  have hdescent : baseEnd_2916760 < baseStart_2916760 := by decide
  rcases family_descends (prefixWord ++ tailWord_2916760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2916770 : List Nat := [3, 3, 1, 2, 1, 1, 3, 2, 3, 4]
def baseStart_2916770 : Nat := 118140960795 + 2916770 * 2 ^ 59
def prefixEnd_2916770 : Nat := 4983230072969 + 3 ^ 40 * 2916770 * 2
def baseEnd_2916770 : Nat := 499234989538219452553675

theorem tailTrace_2916770 : CollatzResearch.WordTrace tailWord_2916770 prefixEnd_2916770 499234989538219452553675 := by
  unfold tailWord_2916770
  simp only [CollatzResearch.WordTrace]
  refine ⟨26595835410761977375446941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70922227762031939667858509 26595835410761977375446941)
  ·
    refine ⟨9973438279035741515792603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26595835410761977375446941 9973438279035741515792603)
    ·
      refine ⟨14960157418553612273688905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9973438279035741515792603 14960157418553612273688905)
      ·
        refine ⟨11220118063915209205266679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14960157418553612273688905 11220118063915209205266679)
        ·
          refine ⟨16830177095872813807900019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11220118063915209205266679 16830177095872813807900019)
          ·
            refine ⟨25245265643809220711850029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16830177095872813807900019 25245265643809220711850029)
            ·
              refine ⟨9466974616428457766943761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25245265643809220711850029 9466974616428457766943761)
              ·
                refine ⟨7100230962321343325207821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9466974616428457766943761 7100230962321343325207821)
                ·
                  refine ⟨2662586610870503746952933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7100230962321343325207821 2662586610870503746952933)
                  ·
                    refine ⟨499234989538219452553675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2662586610870503746952933 499234989538219452553675)
                    ·
                      rfl

theorem cell23_2916770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 2, 3, 4].length) (baseStart_2916770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2916770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2916770 prefixEnd_2916770 := by exact prefixLift 2916770
  have htrace : WordTrace (prefixWord ++ tailWord_2916770) baseStart_2916770 baseEnd_2916770 := by
    simpa [prefixWord, tailWord_2916770, baseEnd_2916770] using wordTrace_append hprefix tailTrace_2916770
  have hstable : (prefixWord ++ tailWord_2916770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2916770).length < 2 ^ (prefixWord ++ tailWord_2916770).sum := by decide
  have hdescent : baseEnd_2916770 < baseStart_2916770 := by decide
  rcases family_descends (prefixWord ++ tailWord_2916770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2916843 : List Nat := [1, 1, 1, 1, 2, 3, 3, 1, 6, 4]
def baseStart_2916843 : Nat := 118140960795 + 2916843 * 2 ^ 59
def prefixEnd_2916843 : Nat := 4983230072969 + 3 ^ 40 * 2916843 * 2
def baseEnd_2916843 : Nat := 499247484234145524016063

theorem tailTrace_2916843 : CollatzResearch.WordTrace tailWord_2916843 prefixEnd_2916843 499247484234145524016063 := by
  unfold tailWord_2916843
  simp only [CollatzResearch.WordTrace]
  refine ⟨106386004171783442969195183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70924002781188961979463455 106386004171783442969195183)
  ·
    refine ⟨159579006257675164453792775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106386004171783442969195183 159579006257675164453792775)
    ·
      refine ⟨239368509386512746680689163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159579006257675164453792775 239368509386512746680689163)
      ·
        refine ⟨359052764079769120021033745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239368509386512746680689163 359052764079769120021033745)
        ·
          refine ⟨269289573059826840015775309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 359052764079769120021033745 269289573059826840015775309)
          ·
            refine ⟨100983589897435065005915741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 269289573059826840015775309 100983589897435065005915741)
            ·
              refine ⟨37868846211538149377218403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 100983589897435065005915741 37868846211538149377218403)
              ·
                refine ⟨56803269317307224065827605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37868846211538149377218403 56803269317307224065827605)
                ·
                  refine ⟨2662653249248776128085669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 56803269317307224065827605 2662653249248776128085669)
                  ·
                    refine ⟨499247484234145524016063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2662653249248776128085669 499247484234145524016063)
                    ·
                      rfl

theorem cell23_2916843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 6, 4].length) (baseStart_2916843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2916843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2916843 prefixEnd_2916843 := by exact prefixLift 2916843
  have htrace : WordTrace (prefixWord ++ tailWord_2916843) baseStart_2916843 baseEnd_2916843 := by
    simpa [prefixWord, tailWord_2916843, baseEnd_2916843] using wordTrace_append hprefix tailTrace_2916843
  have hstable : (prefixWord ++ tailWord_2916843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2916843).length < 2 ^ (prefixWord ++ tailWord_2916843).sum := by decide
  have hdescent : baseEnd_2916843 < baseStart_2916843 := by decide
  rcases family_descends (prefixWord ++ tailWord_2916843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2916860 : List Nat := [2, 2, 2, 1, 2, 1, 1, 6, 2, 4]
def baseStart_2916860 : Nat := 118140960795 + 2916860 * 2 ^ 59
def prefixEnd_2916860 : Nat := 4983230072969 + 3 ^ 40 * 2916860 * 2
def baseEnd_2916860 : Nat := 499250393957854335178537

theorem tailTrace_2916860 : CollatzResearch.WordTrace tailWord_2916860 prefixEnd_2916860 499250393957854335178537 := by
  unfold tailWord_2916860
  simp only [CollatzResearch.WordTrace]
  refine ⟨53193312106360927436282017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70924416141814569915042689 53193312106360927436282017)
  ·
    refine ⟨39894984079770695577211513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53193312106360927436282017 39894984079770695577211513)
    ·
      refine ⟨29921238059828021682908635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39894984079770695577211513 29921238059828021682908635)
      ·
        refine ⟨44881857089742032524362953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29921238059828021682908635 44881857089742032524362953)
        ·
          refine ⟨33661392817306524393272215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44881857089742032524362953 33661392817306524393272215)
          ·
            refine ⟨50492089225959786589908323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33661392817306524393272215 50492089225959786589908323)
            ·
              refine ⟨75738133838939679884862485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50492089225959786589908323 75738133838939679884862485)
              ·
                refine ⟨3550225023700297494602929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 75738133838939679884862485 3550225023700297494602929)
                ·
                  refine ⟨2662668767775223120952197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3550225023700297494602929 2662668767775223120952197)
                  ·
                    refine ⟨499250393957854335178537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2662668767775223120952197 499250393957854335178537)
                    ·
                      rfl

theorem cell23_2916860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 6, 2, 4].length) (baseStart_2916860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2916860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2916860 prefixEnd_2916860 := by exact prefixLift 2916860
  have htrace : WordTrace (prefixWord ++ tailWord_2916860) baseStart_2916860 baseEnd_2916860 := by
    simpa [prefixWord, tailWord_2916860, baseEnd_2916860] using wordTrace_append hprefix tailTrace_2916860
  have hstable : (prefixWord ++ tailWord_2916860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2916860).length < 2 ^ (prefixWord ++ tailWord_2916860).sum := by decide
  have hdescent : baseEnd_2916860 < baseStart_2916860 := by decide
  rcases family_descends (prefixWord ++ tailWord_2916860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2916884 : List Nat := [2, 4, 3, 1, 1, 1, 3, 2, 1, 1, 4]
def baseStart_2916884 : Nat := 118140960795 + 2916884 * 2 ^ 59
def prefixEnd_2916884 : Nat := 4983230072969 + 3 ^ 40 * 2916884 * 2
def baseEnd_2916884 : Nat := 1497763505409270911635501

theorem tailTrace_2916884 : CollatzResearch.WordTrace tailWord_2916884 prefixEnd_2916884 1497763505409270911635501 := by
  unfold tailWord_2916884
  simp only [CollatzResearch.WordTrace]
  refine ⟨53193749782317453485718853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70924999709756604647625137 53193749782317453485718853)
  ·
    refine ⟨9973828084184522528572285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53193749782317453485718853 9973828084184522528572285)
    ·
      refine ⟨3740185531569195948214607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9973828084184522528572285 3740185531569195948214607)
      ·
        refine ⟨5610278297353793922321911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3740185531569195948214607 5610278297353793922321911)
        ·
          refine ⟨8415417446030690883482867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5610278297353793922321911 8415417446030690883482867)
          ·
            refine ⟨12623126169046036325224301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8415417446030690883482867 12623126169046036325224301)
            ·
              refine ⟨4733672313392263621959113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12623126169046036325224301 4733672313392263621959113)
              ·
                refine ⟨3550254235044197716469335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4733672313392263621959113 3550254235044197716469335)
                ·
                  refine ⟨5325381352566296574704003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3550254235044197716469335 5325381352566296574704003)
                  ·
                    refine ⟨7988072028849444862056005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5325381352566296574704003 7988072028849444862056005)
                    ·
                      refine ⟨1497763505409270911635501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7988072028849444862056005 1497763505409270911635501)
                      ·
                        rfl

theorem cell23_2916884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_2916884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2916884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2916884 prefixEnd_2916884 := by exact prefixLift 2916884
  have htrace : WordTrace (prefixWord ++ tailWord_2916884) baseStart_2916884 baseEnd_2916884 := by
    simpa [prefixWord, tailWord_2916884, baseEnd_2916884] using wordTrace_append hprefix tailTrace_2916884
  have hstable : (prefixWord ++ tailWord_2916884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2916884).length < 2 ^ (prefixWord ++ tailWord_2916884).sum := by decide
  have hdescent : baseEnd_2916884 < baseStart_2916884 := by decide
  rcases family_descends (prefixWord ++ tailWord_2916884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2916913 : List Nat := [1, 2, 2, 3, 1, 1, 2, 2, 2, 2, 5]
def baseStart_2916913 : Nat := 118140960795 + 2916913 * 2 ^ 59
def prefixEnd_2916913 : Nat := 4983230072969 + 3 ^ 40 * 2916913 * 2
def baseEnd_2916913 : Nat := 1497778396348251298172867

theorem tailTrace_2916913 : CollatzResearch.WordTrace tailWord_2916913 prefixEnd_2916913 1497778396348251298172867 := by
  unfold tailWord_2916913
  simp only [CollatzResearch.WordTrace]
  refine ⟨106388557281529844924243393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70925704854353229949495595 106388557281529844924243393)
  ·
    refine ⟨79791417961147383693182545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106388557281529844924243393 79791417961147383693182545)
    ·
      refine ⟨59843563470860537769886909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79791417961147383693182545 59843563470860537769886909)
      ·
        refine ⟨22441336301572701663707591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59843563470860537769886909 22441336301572701663707591)
        ·
          refine ⟨33662004452359052495561387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22441336301572701663707591 33662004452359052495561387)
          ·
            refine ⟨50493006678538578743342081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33662004452359052495561387 50493006678538578743342081)
            ·
              refine ⟨37869755008903934057506561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50493006678538578743342081 37869755008903934057506561)
              ·
                refine ⟨28402316256677950543129921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37869755008903934057506561 28402316256677950543129921)
                ·
                  refine ⟨21301737192508462907347441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28402316256677950543129921 21301737192508462907347441)
                  ·
                    refine ⟨15976302894381347180510581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21301737192508462907347441 15976302894381347180510581)
                    ·
                      refine ⟨1497778396348251298172867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15976302894381347180510581 1497778396348251298172867)
                      ·
                        rfl

theorem cell23_2916913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 2, 2, 2, 5].length) (baseStart_2916913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2916913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2916913 prefixEnd_2916913 := by exact prefixLift 2916913
  have htrace : WordTrace (prefixWord ++ tailWord_2916913) baseStart_2916913 baseEnd_2916913 := by
    simpa [prefixWord, tailWord_2916913, baseEnd_2916913] using wordTrace_append hprefix tailTrace_2916913
  have hstable : (prefixWord ++ tailWord_2916913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2916913).length < 2 ^ (prefixWord ++ tailWord_2916913).sum := by decide
  have hdescent : baseEnd_2916913 < baseStart_2916913 := by decide
  rcases family_descends (prefixWord ++ tailWord_2916913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2916918 : List Nat := [5, 1, 2, 1, 2, 2, 1, 4, 1, 2, 2]
def baseStart_2916918 : Nat := 118140960795 + 2916918 * 2 ^ 59
def prefixEnd_2916918 : Nat := 4983230072969 + 3 ^ 40 * 2916918 * 2
def baseEnd_2916918 : Nat := 1497780963751523778610345

theorem tailTrace_2916918 : CollatzResearch.WordTrace tailWord_2916918 prefixEnd_2916918 1497780963751523778610345 := by
  unfold tailWord_2916918
  simp only [CollatzResearch.WordTrace]
  refine ⟨6649296227906983173635963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 70925826431007820518783605 6649296227906983173635963)
  ·
    refine ⟨9973944341860474760453945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6649296227906983173635963 9973944341860474760453945)
    ·
      refine ⟨7480458256395356070340459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9973944341860474760453945 7480458256395356070340459)
      ·
        refine ⟨11220687384593034105510689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7480458256395356070340459 11220687384593034105510689)
        ·
          refine ⟨8415515538444775579133017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11220687384593034105510689 8415515538444775579133017)
          ·
            refine ⟨6311636653833581684349763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8415515538444775579133017 6311636653833581684349763)
            ·
              refine ⟨9467454980750372526524645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6311636653833581684349763 9467454980750372526524645)
              ·
                refine ⟨1775147808890694848723371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9467454980750372526524645 1775147808890694848723371)
                ·
                  refine ⟨2662721713336042273085057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1775147808890694848723371 2662721713336042273085057)
                  ·
                    refine ⟨1997041285002031704813793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2662721713336042273085057 1997041285002031704813793)
                    ·
                      refine ⟨1497780963751523778610345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1997041285002031704813793 1497780963751523778610345)
                      ·
                        rfl

theorem cell23_2916918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 4, 1, 2, 2].length) (baseStart_2916918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2916918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2916918 prefixEnd_2916918 := by exact prefixLift 2916918
  have htrace : WordTrace (prefixWord ++ tailWord_2916918) baseStart_2916918 baseEnd_2916918 := by
    simpa [prefixWord, tailWord_2916918, baseEnd_2916918] using wordTrace_append hprefix tailTrace_2916918
  have hstable : (prefixWord ++ tailWord_2916918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2916918).length < 2 ^ (prefixWord ++ tailWord_2916918).sum := by decide
  have hdescent : baseEnd_2916918 < baseStart_2916918 := by decide
  rcases family_descends (prefixWord ++ tailWord_2916918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2916933 : List Nat := [1, 3, 1, 1, 1, 5, 1, 1, 1, 8]
def baseStart_2916933 : Nat := 118140960795 + 2916933 * 2 ^ 59
def prefixEnd_2916933 : Nat := 4983230072969 + 3 ^ 40 * 2916933 * 2
def baseEnd_2916933 : Nat := 499262888653780406640925

theorem tailTrace_2916933 : CollatzResearch.WordTrace tailWord_2916933 prefixEnd_2916933 499262888653780406640925 := by
  unfold tailWord_2916933
  simp only [CollatzResearch.WordTrace]
  refine ⟨106389286741457388339971453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70926191160971592226647635 106389286741457388339971453)
  ·
    refine ⟨39895982528046520627489295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106389286741457388339971453 39895982528046520627489295)
    ·
      refine ⟨59843973792069780941233943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39895982528046520627489295 59843973792069780941233943)
      ·
        refine ⟨89765960688104671411850915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59843973792069780941233943 89765960688104671411850915)
        ·
          refine ⟨134648941032157007117776373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89765960688104671411850915 134648941032157007117776373)
          ·
            refine ⟨12623338221764719417291535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 134648941032157007117776373 12623338221764719417291535)
            ·
              refine ⟨18935007332647079125937303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12623338221764719417291535 18935007332647079125937303)
              ·
                refine ⟨28402510998970618688905955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18935007332647079125937303 28402510998970618688905955)
                ·
                  refine ⟨42603766498455928033358933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28402510998970618688905955 42603766498455928033358933)
                  ·
                    refine ⟨499262888653780406640925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 42603766498455928033358933 499262888653780406640925)
                    ·
                      rfl

theorem cell23_2916933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 1, 1, 8].length) (baseStart_2916933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2916933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2916933 prefixEnd_2916933 := by exact prefixLift 2916933
  have htrace : WordTrace (prefixWord ++ tailWord_2916933) baseStart_2916933 baseEnd_2916933 := by
    simpa [prefixWord, tailWord_2916933, baseEnd_2916933] using wordTrace_append hprefix tailTrace_2916933
  have hstable : (prefixWord ++ tailWord_2916933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2916933).length < 2 ^ (prefixWord ++ tailWord_2916933).sum := by decide
  have hdescent : baseEnd_2916933 < baseStart_2916933 := by decide
  rcases family_descends (prefixWord ++ tailWord_2916933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2916934 : List Nat := [6, 1, 1, 1, 2, 1, 1, 3, 1, 3, 3]
def baseStart_2916934 : Nat := 118140960795 + 2916934 * 2 ^ 59
def prefixEnd_2916934 : Nat := 4983230072969 + 3 ^ 40 * 2916934 * 2
def baseEnd_2916934 : Nat := 1497789179441995716010271

theorem tailTrace_2916934 : CollatzResearch.WordTrace tailWord_2916934 prefixEnd_2916934 1497789179441995716010271 := by
  unfold tailWord_2916934
  simp only [CollatzResearch.WordTrace]
  refine ⟨3324666350451680172211183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 70926215476302510340505237 3324666350451680172211183)
  ·
    refine ⟨4986999525677520258316775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3324666350451680172211183 4986999525677520258316775)
    ·
      refine ⟨7480499288516280387475163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4986999525677520258316775 7480499288516280387475163)
      ·
        refine ⟨11220748932774420581212745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7480499288516280387475163 11220748932774420581212745)
        ·
          refine ⟨8415561699580815435909559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11220748932774420581212745 8415561699580815435909559)
          ·
            refine ⟨12623342549371223153864339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8415561699580815435909559 12623342549371223153864339)
            ·
              refine ⟨18935013824056834730796509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12623342549371223153864339 18935013824056834730796509)
              ·
                refine ⟨7100630184021313024048691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18935013824056834730796509 7100630184021313024048691)
                ·
                  refine ⟨10650945276031969536073037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7100630184021313024048691 10650945276031969536073037)
                  ·
                    refine ⟨3994104478511988576027389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10650945276031969536073037 3994104478511988576027389)
                    ·
                      refine ⟨1497789179441995716010271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3994104478511988576027389 1497789179441995716010271)
                      ·
                        rfl

theorem cell23_2916934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 3, 1, 3, 3].length) (baseStart_2916934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2916934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2916934 prefixEnd_2916934 := by exact prefixLift 2916934
  have htrace : WordTrace (prefixWord ++ tailWord_2916934) baseStart_2916934 baseEnd_2916934 := by
    simpa [prefixWord, tailWord_2916934, baseEnd_2916934] using wordTrace_append hprefix tailTrace_2916934
  have hstable : (prefixWord ++ tailWord_2916934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2916934).length < 2 ^ (prefixWord ++ tailWord_2916934).sum := by decide
  have hdescent : baseEnd_2916934 < baseStart_2916934 := by decide
  rcases family_descends (prefixWord ++ tailWord_2916934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2916943 : List Nat := [1, 1, 2, 1, 1, 2, 4, 1, 4, 1, 5]
def baseStart_2916943 : Nat := 118140960795 + 2916943 * 2 ^ 59
def prefixEnd_2916943 : Nat := 4983230072969 + 3 ^ 40 * 2916943 * 2
def baseEnd_2916943 : Nat := 1497793800767886180797729

theorem tailTrace_2916943 : CollatzResearch.WordTrace tailWord_2916943 prefixEnd_2916943 1497793800767886180797729 := by
  unfold tailWord_2916943
  simp only [CollatzResearch.WordTrace]
  refine ⟨106389651471421160047835483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70926434314280773365223655 106389651471421160047835483)
  ·
    refine ⟨159584477207131740071753225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106389651471421160047835483 159584477207131740071753225)
    ·
      refine ⟨119688357905348805053814919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159584477207131740071753225 119688357905348805053814919)
      ·
        refine ⟨179532536858023207580722379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119688357905348805053814919 179532536858023207580722379)
        ·
          refine ⟨269298805287034811371083569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179532536858023207580722379 269298805287034811371083569)
          ·
            refine ⟨201974103965276108528312677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 269298805287034811371083569 201974103965276108528312677)
            ·
              refine ⟨37870144493489270349058627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 201974103965276108528312677 37870144493489270349058627)
              ·
                refine ⟨56805216740233905523587941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37870144493489270349058627 56805216740233905523587941)
                ·
                  refine ⟨10650978138793857285672739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56805216740233905523587941 10650978138793857285672739)
                  ·
                    refine ⟨15976467208190785928509109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10650978138793857285672739 15976467208190785928509109)
                    ·
                      refine ⟨1497793800767886180797729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15976467208190785928509109 1497793800767886180797729)
                      ·
                        rfl

theorem cell23_2916943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 1, 4, 1, 5].length) (baseStart_2916943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2916943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2916943 prefixEnd_2916943 := by exact prefixLift 2916943
  have htrace : WordTrace (prefixWord ++ tailWord_2916943) baseStart_2916943 baseEnd_2916943 := by
    simpa [prefixWord, tailWord_2916943, baseEnd_2916943] using wordTrace_append hprefix tailTrace_2916943
  have hstable : (prefixWord ++ tailWord_2916943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2916943).length < 2 ^ (prefixWord ++ tailWord_2916943).sum := by decide
  have hdescent : baseEnd_2916943 < baseStart_2916943 := by decide
  rcases family_descends (prefixWord ++ tailWord_2916943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2916961 : List Nat := [1, 2, 3, 1, 1, 6, 2, 1, 1, 3, 2]
def baseStart_2916961 : Nat := 118140960795 + 2916961 * 2 ^ 59
def prefixEnd_2916961 : Nat := 4983230072969 + 3 ^ 40 * 2916961 * 2
def baseEnd_2916961 : Nat := 1497803043419667110372647

theorem tailTrace_2916961 : CollatzResearch.WordTrace tailWord_2916961 prefixEnd_2916961 1497803043419667110372647 := by
  unfold tailWord_2916961
  simp only [CollatzResearch.WordTrace]
  refine ⟨106390307985355949121990737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70926871990237299414660491 106390307985355949121990737)
  ·
    refine ⟨79792730989016961841493053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106390307985355949121990737 79792730989016961841493053)
    ·
      refine ⟨29922274120881360690559895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79792730989016961841493053 29922274120881360690559895)
      ·
        refine ⟨44883411181322041035839843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29922274120881360690559895 44883411181322041035839843)
        ·
          refine ⟨67325116771983061553759765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44883411181322041035839843 67325116771983061553759765)
          ·
            refine ⟨3155864848686706010332489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 67325116771983061553759765 3155864848686706010332489)
            ·
              refine ⟨2366898636515029507749367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3155864848686706010332489 2366898636515029507749367)
              ·
                refine ⟨3550347954772544261624051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2366898636515029507749367 3550347954772544261624051)
                ·
                  refine ⟨5325521932158816392436077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3550347954772544261624051 5325521932158816392436077)
                  ·
                    refine ⟨1997070724559556147163529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5325521932158816392436077 1997070724559556147163529)
                    ·
                      refine ⟨1497803043419667110372647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1997070724559556147163529 1497803043419667110372647)
                      ·
                        rfl

theorem cell23_2916961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 2, 1, 1, 3, 2].length) (baseStart_2916961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2916961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2916961 prefixEnd_2916961 := by exact prefixLift 2916961
  have htrace : WordTrace (prefixWord ++ tailWord_2916961) baseStart_2916961 baseEnd_2916961 := by
    simpa [prefixWord, tailWord_2916961, baseEnd_2916961] using wordTrace_append hprefix tailTrace_2916961
  have hstable : (prefixWord ++ tailWord_2916961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2916961).length < 2 ^ (prefixWord ++ tailWord_2916961).sum := by decide
  have hdescent : baseEnd_2916961 < baseStart_2916961 := by decide
  rcases family_descends (prefixWord ++ tailWord_2916961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2916963 : List Nat := [1, 1, 1, 5, 1, 2, 1, 2, 9]
def baseStart_2916963 : Nat := 118140960795 + 2916963 * 2 ^ 59
def prefixEnd_2916963 : Nat := 4983230072969 + 3 ^ 40 * 2916963 * 2
def baseEnd_2916963 : Nat := 166422674486775122505293

theorem tailTrace_2916963 : CollatzResearch.WordTrace tailWord_2916963 prefixEnd_2916963 166422674486775122505293 := by
  unfold tailWord_2916963
  simp only [CollatzResearch.WordTrace]
  refine ⟨106390380931348703463563543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70926920620899135642375695 106390380931348703463563543)
  ·
    refine ⟨159585571397023055195345315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106390380931348703463563543 159585571397023055195345315)
    ·
      refine ⟨239378357095534582793017973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159585571397023055195345315 239378357095534582793017973)
      ·
        refine ⟨22441720977706367136845435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 239378357095534582793017973 22441720977706367136845435)
        ·
          refine ⟨33662581466559550705268153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22441720977706367136845435 33662581466559550705268153)
          ·
            refine ⟨25246936099919663028951115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33662581466559550705268153 25246936099919663028951115)
            ·
              refine ⟨37870404149879494543426673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25246936099919663028951115 37870404149879494543426673)
              ·
                refine ⟨28402803112409620907570005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37870404149879494543426673 28402803112409620907570005)
                ·
                  refine ⟨166422674486775122505293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 28402803112409620907570005 166422674486775122505293)
                  ·
                    rfl

theorem cell23_2916963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 2, 9].length) (baseStart_2916963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2916963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2916963 prefixEnd_2916963 := by exact prefixLift 2916963
  have htrace : WordTrace (prefixWord ++ tailWord_2916963) baseStart_2916963 baseEnd_2916963 := by
    simpa [prefixWord, tailWord_2916963, baseEnd_2916963] using wordTrace_append hprefix tailTrace_2916963
  have hstable : (prefixWord ++ tailWord_2916963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2916963).length < 2 ^ (prefixWord ++ tailWord_2916963).sum := by decide
  have hdescent : baseEnd_2916963 < baseStart_2916963 := by decide
  rcases family_descends (prefixWord ++ tailWord_2916963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2916968 : List Nat := [2, 1, 4, 3, 3, 1, 1, 2, 2, 1, 3]
def baseStart_2916968 : Nat := 118140960795 + 2916968 * 2 ^ 59
def prefixEnd_2916968 : Nat := 4983230072969 + 3 ^ 40 * 2916968 * 2
def baseEnd_2916968 : Nat := 1497806637784248582985115

theorem tailTrace_2916968 : CollatzResearch.WordTrace tailWord_2916968 prefixEnd_2916968 1497806637784248582985115 := by
  unfold tailWord_2916968
  simp only [CollatzResearch.WordTrace]
  refine ⟨53195281648165294658747779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70927042197553726211663705 53195281648165294658747779)
  ·
    refine ⟨79792922472247941988121669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53195281648165294658747779 79792922472247941988121669)
    ·
      refine ⟨14961172963546489122772813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79792922472247941988121669 14961172963546489122772813)
      ·
        refine ⟨5610439861329933421039805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14961172963546489122772813 5610439861329933421039805)
        ·
          refine ⟨2103914947998725032889927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5610439861329933421039805 2103914947998725032889927)
          ·
            refine ⟨3155872421998087549334891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2103914947998725032889927 3155872421998087549334891)
            ·
              refine ⟨4733808632997131324002337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3155872421998087549334891 4733808632997131324002337)
              ·
                refine ⟨3550356474747848493001753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4733808632997131324002337 3550356474747848493001753)
                ·
                  refine ⟨2662767356060886369751315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3550356474747848493001753 2662767356060886369751315)
                  ·
                    refine ⟨3994151034091329554626973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2662767356060886369751315 3994151034091329554626973)
                    ·
                      refine ⟨1497806637784248582985115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3994151034091329554626973 1497806637784248582985115)
                      ·
                        rfl

theorem cell23_2916968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 1, 2, 2, 1, 3].length) (baseStart_2916968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2916968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2916968 prefixEnd_2916968 := by exact prefixLift 2916968
  have htrace : WordTrace (prefixWord ++ tailWord_2916968) baseStart_2916968 baseEnd_2916968 := by
    simpa [prefixWord, tailWord_2916968, baseEnd_2916968] using wordTrace_append hprefix tailTrace_2916968
  have hstable : (prefixWord ++ tailWord_2916968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2916968).length < 2 ^ (prefixWord ++ tailWord_2916968).sum := by decide
  have hdescent : baseEnd_2916968 < baseStart_2916968 := by decide
  rcases family_descends (prefixWord ++ tailWord_2916968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2916970 : List Nat := [3, 1, 3, 2, 1, 1, 1, 1, 4, 2, 4]
def baseStart_2916970 : Nat := 118140960795 + 2916970 * 2 ^ 59
def prefixEnd_2916970 : Nat := 4983230072969 + 3 ^ 40 * 2916970 * 2
def baseEnd_2916970 : Nat := 1497807664745557575160105

theorem tailTrace_2916970 : CollatzResearch.WordTrace tailWord_2916970 prefixEnd_2916970 1497807664745557575160105 := by
  unfold tailWord_2916970
  simp only [CollatzResearch.WordTrace]
  refine ⟨26597659060580835914767091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70927090828215562439378909 26597659060580835914767091)
  ·
    refine ⟨39896488590871253872150637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26597659060580835914767091 39896488590871253872150637)
    ·
      refine ⟨14961183221576720202056489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39896488590871253872150637 14961183221576720202056489)
      ·
        refine ⟨11220887416182540151542367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14961183221576720202056489 11220887416182540151542367)
        ·
          refine ⟨16831331124273810227313551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11220887416182540151542367 16831331124273810227313551)
          ·
            refine ⟨25246996686410715340970327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16831331124273810227313551 25246996686410715340970327)
            ·
              refine ⟨37870495029616073011455491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25246996686410715340970327 37870495029616073011455491)
              ·
                refine ⟨56805742544424109517183237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37870495029616073011455491 56805742544424109517183237)
                ·
                  refine ⟨10651076727079520534471857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56805742544424109517183237 10651076727079520534471857)
                  ·
                    refine ⟨7988307545309640400853893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10651076727079520534471857 7988307545309640400853893)
                    ·
                      refine ⟨1497807664745557575160105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7988307545309640400853893 1497807664745557575160105)
                      ·
                        rfl

theorem cell23_2916970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_2916970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2916970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2916970 prefixEnd_2916970 := by exact prefixLift 2916970
  have htrace : WordTrace (prefixWord ++ tailWord_2916970) baseStart_2916970 baseEnd_2916970 := by
    simpa [prefixWord, tailWord_2916970, baseEnd_2916970] using wordTrace_append hprefix tailTrace_2916970
  have hstable : (prefixWord ++ tailWord_2916970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2916970).length < 2 ^ (prefixWord ++ tailWord_2916970).sum := by decide
  have hdescent : baseEnd_2916970 < baseStart_2916970 := by decide
  rcases family_descends (prefixWord ++ tailWord_2916970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2917003 : List Nat := [1, 1, 1, 1, 4, 1, 2, 1, 3, 1, 7]
def baseStart_2917003 : Nat := 118140960795 + 2917003 * 2 ^ 59
def prefixEnd_2917003 : Nat := 4983230072969 + 3 ^ 40 * 2917003 * 2
def baseEnd_2917003 : Nat := 1497824609607155946047453

theorem tailTrace_2917003 : CollatzResearch.WordTrace tailWord_2917003 prefixEnd_2917003 1497824609607155946047453 := by
  unfold tailWord_2917003
  simp only [CollatzResearch.WordTrace]
  refine ⟨106391839851203790295019663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70927893234135860196679775 106391839851203790295019663)
  ·
    refine ⟨159587759776805685442529495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106391839851203790295019663 159587759776805685442529495)
    ·
      refine ⟨239381639665208528163794243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159587759776805685442529495 239381639665208528163794243)
      ·
        refine ⟨359072459497812792245691365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239381639665208528163794243 359072459497812792245691365)
        ·
          refine ⟨67326086155839898546067131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 359072459497812792245691365 67326086155839898546067131)
          ·
            refine ⟨100989129233759847819100697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67326086155839898546067131 100989129233759847819100697)
            ·
              refine ⟨75741846925319885864325523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100989129233759847819100697 75741846925319885864325523)
              ·
                refine ⟨113612770387979828796488285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75741846925319885864325523 113612770387979828796488285)
                ·
                  refine ⟨42604788895492435798683107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 113612770387979828796488285 42604788895492435798683107)
                  ·
                    refine ⟨63907183343238653698024661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42604788895492435798683107 63907183343238653698024661)
                    ·
                      refine ⟨1497824609607155946047453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 63907183343238653698024661 1497824609607155946047453)
                      ·
                        rfl

theorem cell23_2917003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 3, 1, 7].length) (baseStart_2917003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2917003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2917003 prefixEnd_2917003 := by exact prefixLift 2917003
  have htrace : WordTrace (prefixWord ++ tailWord_2917003) baseStart_2917003 baseEnd_2917003 := by
    simpa [prefixWord, tailWord_2917003, baseEnd_2917003] using wordTrace_append hprefix tailTrace_2917003
  have hstable : (prefixWord ++ tailWord_2917003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2917003).length < 2 ^ (prefixWord ++ tailWord_2917003).sum := by decide
  have hdescent : baseEnd_2917003 < baseStart_2917003 := by decide
  rcases family_descends (prefixWord ++ tailWord_2917003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2917031 : List Nat := [1, 1, 6, 3, 2, 1, 1, 1, 7]
def baseStart_2917031 : Nat := 118140960795 + 2917031 * 2 ^ 59
def prefixEnd_2917031 : Nat := 4983230072969 + 3 ^ 40 * 2917031 * 2
def baseEnd_2917031 : Nat := 166426554118386870721925

theorem tailTrace_2917031 : CollatzResearch.WordTrace tailWord_2917031 prefixEnd_2917031 166426554118386870721925 := by
  unfold tailWord_2917031
  simp only [CollatzResearch.WordTrace]
  refine ⟨106392861095102351077038947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70928574063401567384692631 106392861095102351077038947)
  ·
    refine ⟨159589291642653526615558421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106392861095102351077038947 159589291642653526615558421)
    ·
      refine ⟨7480748045749384060104301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 159589291642653526615558421 7480748045749384060104301)
      ·
        refine ⟨2805280517156019022539113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7480748045749384060104301 2805280517156019022539113)
        ·
          refine ⟨2103960387867014266904335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2805280517156019022539113 2103960387867014266904335)
          ·
            refine ⟨3155940581800521400356503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2103960387867014266904335 3155940581800521400356503)
            ·
              refine ⟨4733910872700782100534755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3155940581800521400356503 4733910872700782100534755)
              ·
                refine ⟨7100866309051173150802133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4733910872700782100534755 7100866309051173150802133)
                ·
                  refine ⟨166426554118386870721925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7100866309051173150802133 166426554118386870721925)
                  ·
                    rfl

theorem cell23_2917031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 1, 1, 7].length) (baseStart_2917031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2917031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2917031 prefixEnd_2917031 := by exact prefixLift 2917031
  have htrace : WordTrace (prefixWord ++ tailWord_2917031) baseStart_2917031 baseEnd_2917031 := by
    simpa [prefixWord, tailWord_2917031, baseEnd_2917031] using wordTrace_append hprefix tailTrace_2917031
  have hstable : (prefixWord ++ tailWord_2917031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2917031).length < 2 ^ (prefixWord ++ tailWord_2917031).sum := by decide
  have hdescent : baseEnd_2917031 < baseStart_2917031 := by decide
  rcases family_descends (prefixWord ++ tailWord_2917031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2917037 : List Nat := [1, 5, 2, 1, 1, 3, 1, 1, 1, 2, 5]
def baseStart_2917037 : Nat := 118140960795 + 2917037 * 2 ^ 59
def prefixEnd_2917037 : Nat := 4983230072969 + 3 ^ 40 * 2917037 * 2
def baseEnd_2917037 : Nat := 1497842067949408813022297

theorem tailTrace_2917037 : CollatzResearch.WordTrace tailWord_2917037 prefixEnd_2917037 1497842067949408813022297 := by
  unfold tailWord_2917037
  simp only [CollatzResearch.WordTrace]
  refine ⟨106393079933080614101757365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70928719955387076067838243 106393079933080614101757365)
  ·
    refine ⟨9974351243726307572039753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 106393079933080614101757365 9974351243726307572039753)
    ·
      refine ⟨7480763432794730679029815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9974351243726307572039753 7480763432794730679029815)
      ·
        refine ⟨11221145149192096018544723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7480763432794730679029815 11221145149192096018544723)
        ·
          refine ⟨16831717723788144027817085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11221145149192096018544723 16831717723788144027817085)
          ·
            refine ⟨6311894146420554010431407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16831717723788144027817085 6311894146420554010431407)
            ·
              refine ⟨9467841219630831015647111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6311894146420554010431407 9467841219630831015647111)
              ·
                refine ⟨14201761829446246523470667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9467841219630831015647111 14201761829446246523470667)
                ·
                  refine ⟨21302642744169369785206001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14201761829446246523470667 21302642744169369785206001)
                  ·
                    refine ⟨15976982058127027338904501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21302642744169369785206001 15976982058127027338904501)
                    ·
                      refine ⟨1497842067949408813022297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15976982058127027338904501 1497842067949408813022297)
                      ·
                        rfl

theorem cell23_2917037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_2917037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2917037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2917037 prefixEnd_2917037 := by exact prefixLift 2917037
  have htrace : WordTrace (prefixWord ++ tailWord_2917037) baseStart_2917037 baseEnd_2917037 := by
    simpa [prefixWord, tailWord_2917037, baseEnd_2917037] using wordTrace_append hprefix tailTrace_2917037
  have hstable : (prefixWord ++ tailWord_2917037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2917037).length < 2 ^ (prefixWord ++ tailWord_2917037).sum := by decide
  have hdescent : baseEnd_2917037 < baseStart_2917037 := by decide
  rcases family_descends (prefixWord ++ tailWord_2917037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2917087 : List Nat := [1, 1, 2, 3, 2, 4, 2, 2, 6]
def baseStart_2917087 : Nat := 118140960795 + 2917087 * 2 ^ 59
def prefixEnd_2917087 : Nat := 4983230072969 + 3 ^ 40 * 2917087 * 2
def baseEnd_2917087 : Nat := 166429749109125957488563

theorem tailTrace_2917087 : CollatzResearch.WordTrace tailWord_2917087 prefixEnd_2917087 166429749109125957488563 := by
  unfold tailWord_2917087
  simp only [CollatzResearch.WordTrace]
  refine ⟨106394903582899472641077515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70929935721932981760718343 106394903582899472641077515)
  ·
    refine ⟨159592355374349208961616273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106394903582899472641077515 159592355374349208961616273)
    ·
      refine ⟨119694266530761906721212205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159592355374349208961616273 119694266530761906721212205)
      ·
        refine ⟨44885349949035715020454577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119694266530761906721212205 44885349949035715020454577)
        ·
          refine ⟨33664012461776786265340933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44885349949035715020454577 33664012461776786265340933)
          ·
            refine ⟨6312002336583147424751425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33664012461776786265340933 6312002336583147424751425)
            ·
              refine ⟨4734001752437360568563569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6312002336583147424751425 4734001752437360568563569)
              ·
                refine ⟨3550501314328020426422677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4734001752437360568563569 3550501314328020426422677)
                ·
                  refine ⟨166429749109125957488563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3550501314328020426422677 166429749109125957488563)
                  ·
                    rfl

theorem cell23_2917087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 2, 2, 6].length) (baseStart_2917087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2917087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2917087 prefixEnd_2917087 := by exact prefixLift 2917087
  have htrace : WordTrace (prefixWord ++ tailWord_2917087) baseStart_2917087 baseEnd_2917087 := by
    simpa [prefixWord, tailWord_2917087, baseEnd_2917087] using wordTrace_append hprefix tailTrace_2917087
  have hstable : (prefixWord ++ tailWord_2917087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2917087).length < 2 ^ (prefixWord ++ tailWord_2917087).sum := by decide
  have hdescent : baseEnd_2917087 < baseStart_2917087 := by decide
  rcases family_descends (prefixWord ++ tailWord_2917087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2917091 : List Nat := [1, 1, 1, 7, 1, 2, 1, 4, 1, 4]
def baseStart_2917091 : Nat := 118140960795 + 2917091 * 2 ^ 59
def prefixEnd_2917091 : Nat := 4983230072969 + 3 ^ 40 * 2917091 * 2
def baseEnd_2917091 : Nat := 499289931968250533915683

theorem tailTrace_2917091 : CollatzResearch.WordTrace tailWord_2917091 prefixEnd_2917091 499289931968250533915683 := by
  unfold tailWord_2917091
  simp only [CollatzResearch.WordTrace]
  refine ⟨106395049474884981324223127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70930032983256654216148751 106395049474884981324223127)
  ·
    refine ⟨159592574212327471986334691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106395049474884981324223127 159592574212327471986334691)
    ·
      refine ⟨239388861318491207979502037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159592574212327471986334691 239388861318491207979502037)
      ·
        refine ⟨5610676437152137687019579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 239388861318491207979502037 5610676437152137687019579)
        ·
          refine ⟨8416014655728206530529369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5610676437152137687019579 8416014655728206530529369)
          ·
            refine ⟨6312010991796154897897027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8416014655728206530529369 6312010991796154897897027)
            ·
              refine ⟨9468016487694232346845541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6312010991796154897897027 9468016487694232346845541)
              ·
                refine ⟨1775253091442668565033539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9468016487694232346845541 1775253091442668565033539)
                ·
                  refine ⟨2662879637164002847550309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1775253091442668565033539 2662879637164002847550309)
                  ·
                    refine ⟨499289931968250533915683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2662879637164002847550309 499289931968250533915683)
                    ·
                      rfl

theorem cell23_2917091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 4, 1, 4].length) (baseStart_2917091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2917091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2917091 prefixEnd_2917091 := by exact prefixLift 2917091
  have htrace : WordTrace (prefixWord ++ tailWord_2917091) baseStart_2917091 baseEnd_2917091 := by
    simpa [prefixWord, tailWord_2917091, baseEnd_2917091] using wordTrace_append hprefix tailTrace_2917091
  have hstable : (prefixWord ++ tailWord_2917091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2917091).length < 2 ^ (prefixWord ++ tailWord_2917091).sum := by decide
  have hdescent : baseEnd_2917091 < baseStart_2917091 := by decide
  rcases family_descends (prefixWord ++ tailWord_2917091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2917107 : List Nat := [1, 1, 1, 2, 2, 3, 1, 4, 1, 5, 2]
def baseStart_2917107 : Nat := 118140960795 + 2917107 * 2 ^ 59
def prefixEnd_2917107 : Nat := 4983230072969 + 3 ^ 40 * 2917107 * 2
def baseEnd_2917107 : Nat := 1497878011595223539146975

theorem tailTrace_2917107 : CollatzResearch.WordTrace tailWord_2917107 prefixEnd_2917107 1497878011595223539146975 := by
  unfold tailWord_2917107
  simp only [CollatzResearch.WordTrace]
  refine ⟨106395633042827016056805575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70930422028551344037870383 106395633042827016056805575)
  ·
    refine ⟨159593449564240524085208363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106395633042827016056805575 159593449564240524085208363)
    ·
      refine ⟨239390174346360786127812545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159593449564240524085208363 239390174346360786127812545)
      ·
        refine ⟨179542630759770589595859409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 239390174346360786127812545 179542630759770589595859409)
        ·
          refine ⟨134656973069827942196894557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179542630759770589595859409 134656973069827942196894557)
          ·
            refine ⟨50496364901185478323835459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 134656973069827942196894557 50496364901185478323835459)
            ·
              refine ⟨75744547351778217485753189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50496364901185478323835459 75744547351778217485753189)
              ·
                refine ⟨14202102628458415778578723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 75744547351778217485753189 14202102628458415778578723)
                ·
                  refine ⟨21303153942687623667868085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14202102628458415778578723 21303153942687623667868085)
                  ·
                    refine ⟨1997170682126964718862633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21303153942687623667868085 1997170682126964718862633)
                    ·
                      refine ⟨1497878011595223539146975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1997170682126964718862633 1497878011595223539146975)
                      ·
                        rfl

theorem cell23_2917107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 4, 1, 5, 2].length) (baseStart_2917107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2917107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2917107 prefixEnd_2917107 := by exact prefixLift 2917107
  have htrace : WordTrace (prefixWord ++ tailWord_2917107) baseStart_2917107 baseEnd_2917107 := by
    simpa [prefixWord, tailWord_2917107, baseEnd_2917107] using wordTrace_append hprefix tailTrace_2917107
  have hstable : (prefixWord ++ tailWord_2917107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2917107).length < 2 ^ (prefixWord ++ tailWord_2917107).sum := by decide
  have hdescent : baseEnd_2917107 < baseStart_2917107 := by decide
  rcases family_descends (prefixWord ++ tailWord_2917107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
