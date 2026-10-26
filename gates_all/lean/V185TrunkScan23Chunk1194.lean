import V185TrunkScan23Chunk1193

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7074133 : List Nat := [1, 3, 2, 2, 5, 1, 1, 1, 3, 1, 3]
def baseStart_7074133 : Nat := 118140960795 + 7074133 * 2 ^ 59
def prefixEnd_7074133 : Nat := 4983230072969 + 3 ^ 40 * 7074133 * 2
def baseEnd_7074133 : Nat := 3632430442832476155804161

theorem tailTrace_7074133 : CollatzResearch.WordTrace tailWord_7074133 prefixEnd_7074133 3632430442832476155804161 := by
  unfold tailWord_7074133
  simp only [CollatzResearch.WordTrace]
  refine ⟨258014827280631781574523053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172009884853754521049682035 258014827280631781574523053)
  ·
    refine ⟨96755560230236918090446145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 258014827280631781574523053 96755560230236918090446145)
    ·
      refine ⟨72566670172677688567834609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96755560230236918090446145 72566670172677688567834609)
      ·
        refine ⟨54425002629508266425875957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72566670172677688567834609 54425002629508266425875957)
        ·
          refine ⟨5102343996516399977425871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54425002629508266425875957 5102343996516399977425871)
          ·
            refine ⟨7653515994774599966138807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5102343996516399977425871 7653515994774599966138807)
            ·
              refine ⟨11480273992161899949208211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7653515994774599966138807 11480273992161899949208211)
              ·
                refine ⟨17220410988242849923812317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11480273992161899949208211 17220410988242849923812317)
                ·
                  refine ⟨6457654120591068721429619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17220410988242849923812317 6457654120591068721429619)
                  ·
                    refine ⟨9686481180886603082144429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6457654120591068721429619 9686481180886603082144429)
                    ·
                      refine ⟨3632430442832476155804161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9686481180886603082144429 3632430442832476155804161)
                      ·
                        rfl

theorem cell23_7074133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 1, 1, 3, 1, 3].length) (baseStart_7074133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7074133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7074133 prefixEnd_7074133 := by exact prefixLift 7074133
  have htrace : WordTrace (prefixWord ++ tailWord_7074133) baseStart_7074133 baseEnd_7074133 := by
    simpa [prefixWord, tailWord_7074133, baseEnd_7074133] using wordTrace_append hprefix tailTrace_7074133
  have hstable : (prefixWord ++ tailWord_7074133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7074133).length < 2 ^ (prefixWord ++ tailWord_7074133).sum := by decide
  have hdescent : baseEnd_7074133 < baseStart_7074133 := by decide
  rcases family_descends (prefixWord ++ tailWord_7074133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7074135 : List Nat := [1, 1, 3, 2, 3, 1, 1, 1, 3, 1, 6]
def baseStart_7074135 : Nat := 118140960795 + 7074135 * 2 ^ 59
def prefixEnd_7074135 : Nat := 4983230072969 + 3 ^ 40 * 7074135 * 2
def baseEnd_7074135 : Nat := 3632431469793785147979151

theorem tailTrace_7074135 : CollatzResearch.WordTrace tailWord_7074135 prefixEnd_7074135 3632431469793785147979151 := by
  unfold tailWord_7074135
  simp only [CollatzResearch.WordTrace]
  refine ⟨258014900226624535916095859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172009933484416357277397239 258014900226624535916095859)
  ·
    refine ⟨387022350339936803874143789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258014900226624535916095859 387022350339936803874143789)
    ·
      refine ⟨145133381377476301452803921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 387022350339936803874143789 145133381377476301452803921)
      ·
        refine ⟨108850036033107226089602941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145133381377476301452803921 108850036033107226089602941)
        ·
          refine ⟨40818763512415209783601103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108850036033107226089602941 40818763512415209783601103)
          ·
            refine ⟨61228145268622814675401655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40818763512415209783601103 61228145268622814675401655)
            ·
              refine ⟨91842217902934222013102483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61228145268622814675401655 91842217902934222013102483)
              ·
                refine ⟨137763326854401333019653725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91842217902934222013102483 137763326854401333019653725)
                ·
                  refine ⟨51661247570400499882370147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 137763326854401333019653725 51661247570400499882370147)
                  ·
                    refine ⟨77491871355600749823555221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51661247570400499882370147 77491871355600749823555221)
                    ·
                      refine ⟨3632431469793785147979151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77491871355600749823555221 3632431469793785147979151)
                      ·
                        rfl

theorem cell23_7074135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 1, 3, 1, 6].length) (baseStart_7074135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7074135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7074135 prefixEnd_7074135 := by exact prefixLift 7074135
  have htrace : WordTrace (prefixWord ++ tailWord_7074135) baseStart_7074135 baseEnd_7074135 := by
    simpa [prefixWord, tailWord_7074135, baseEnd_7074135] using wordTrace_append hprefix tailTrace_7074135
  have hstable : (prefixWord ++ tailWord_7074135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7074135).length < 2 ^ (prefixWord ++ tailWord_7074135).sum := by decide
  have hdescent : baseEnd_7074135 < baseStart_7074135 := by decide
  rcases family_descends (prefixWord ++ tailWord_7074135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7074149 : List Nat := [1, 3, 1, 3, 1, 4, 1, 3, 2, 4]
def baseStart_7074149 : Nat := 118140960795 + 7074149 * 2 ^ 59
def prefixEnd_7074149 : Nat := 4983230072969 + 3 ^ 40 * 7074149 * 2
def baseEnd_7074149 : Nat := 1210812886174316031068029

theorem tailTrace_7074149 : CollatzResearch.WordTrace tailWord_7074149 prefixEnd_7074149 1210812886174316031068029 := by
  unfold tailWord_7074149
  simp only [CollatzResearch.WordTrace]
  refine ⟨258015410848573816307105501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172010273899049210871403667 258015410848573816307105501)
  ·
    refine ⟨96755779068215181115164563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 258015410848573816307105501 96755779068215181115164563)
    ·
      refine ⟨145133668602322771672746845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96755779068215181115164563 145133668602322771672746845)
      ·
        refine ⟨54425125725871039377280067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145133668602322771672746845 54425125725871039377280067)
        ·
          refine ⟨81637688588806559065920101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54425125725871039377280067 81637688588806559065920101)
          ·
            refine ⟨15307066610401229824860019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81637688588806559065920101 15307066610401229824860019)
            ·
              refine ⟨22960599915601844737290029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15307066610401229824860019 22960599915601844737290029)
              ·
                refine ⟨8610224968350691776483761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22960599915601844737290029 8610224968350691776483761)
                ·
                  refine ⟨6457668726263018832362821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8610224968350691776483761 6457668726263018832362821)
                  ·
                    refine ⟨1210812886174316031068029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6457668726263018832362821 1210812886174316031068029)
                    ·
                      rfl

theorem cell23_7074149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 3, 2, 4].length) (baseStart_7074149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7074149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7074149 prefixEnd_7074149 := by exact prefixLift 7074149
  have htrace : WordTrace (prefixWord ++ tailWord_7074149) baseStart_7074149 baseEnd_7074149 := by
    simpa [prefixWord, tailWord_7074149, baseEnd_7074149] using wordTrace_append hprefix tailTrace_7074149
  have hstable : (prefixWord ++ tailWord_7074149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7074149).length < 2 ^ (prefixWord ++ tailWord_7074149).sum := by decide
  have hdescent : baseEnd_7074149 < baseStart_7074149 := by decide
  rcases family_descends (prefixWord ++ tailWord_7074149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7074152 : List Nat := [2, 1, 4, 2, 2, 1, 2, 1, 1, 1, 6]
def baseStart_7074152 : Nat := 118140960795 + 7074152 * 2 ^ 59
def prefixEnd_7074152 : Nat := 4983230072969 + 3 ^ 40 * 7074152 * 2
def baseEnd_7074152 : Nat := 3632440198964911581466573

theorem tailTrace_7074152 : CollatzResearch.WordTrace tailWord_7074152 prefixEnd_7074152 3632440198964911581466573 := by
  unfold tailWord_7074152
  simp only [CollatzResearch.WordTrace]
  refine ⟨129007760133781473909732355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172010346845041965212976473 129007760133781473909732355)
  ·
    refine ⟨193511640200672210864598533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129007760133781473909732355 193511640200672210864598533)
    ·
      refine ⟨36283432537626039537112225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 193511640200672210864598533 36283432537626039537112225)
      ·
        refine ⟨27212574403219529652834169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36283432537626039537112225 27212574403219529652834169)
        ·
          refine ⟨20409430802414647239625627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27212574403219529652834169 20409430802414647239625627)
          ·
            refine ⟨30614146203621970859438441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20409430802414647239625627 30614146203621970859438441)
            ·
              refine ⟨22960609652716478144578831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30614146203621970859438441 22960609652716478144578831)
              ·
                refine ⟨34440914479074717216868247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22960609652716478144578831 34440914479074717216868247)
                ·
                  refine ⟨51661371718612075825302371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34440914479074717216868247 51661371718612075825302371)
                  ·
                    refine ⟨77492057577918113737953557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51661371718612075825302371 77492057577918113737953557)
                    ·
                      refine ⟨3632440198964911581466573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77492057577918113737953557 3632440198964911581466573)
                      ·
                        rfl

theorem cell23_7074152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_7074152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7074152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7074152 prefixEnd_7074152 := by exact prefixLift 7074152
  have htrace : WordTrace (prefixWord ++ tailWord_7074152) baseStart_7074152 baseEnd_7074152 := by
    simpa [prefixWord, tailWord_7074152, baseEnd_7074152] using wordTrace_append hprefix tailTrace_7074152
  have hstable : (prefixWord ++ tailWord_7074152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7074152).length < 2 ^ (prefixWord ++ tailWord_7074152).sum := by decide
  have hdescent : baseEnd_7074152 < baseStart_7074152 := by decide
  rcases family_descends (prefixWord ++ tailWord_7074152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7074156 : List Nat := [2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 4]
def baseStart_7074156 : Nat := 118140960795 + 7074156 * 2 ^ 59
def prefixEnd_7074156 : Nat := 4983230072969 + 3 ^ 40 * 7074156 * 2
def baseEnd_7074156 : Nat := 3632442252887529565816555

theorem tailTrace_7074156 : CollatzResearch.WordTrace tailWord_7074156 prefixEnd_7074156 3632442252887529565816555 := by
  unfold tailWord_7074156
  simp only [CollatzResearch.WordTrace]
  refine ⟨129007833079774228251305161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172010444106365637668406881 129007833079774228251305161)
  ·
    refine ⟨96755874809830671188478871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129007833079774228251305161 96755874809830671188478871)
    ·
      refine ⟨145133812214746006782718307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96755874809830671188478871 145133812214746006782718307)
      ·
        refine ⟨217700718322119010174077461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145133812214746006782718307 217700718322119010174077461)
        ·
          refine ⟨10204721171349328601909881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 217700718322119010174077461 10204721171349328601909881)
          ·
            refine ⟨7653540878511996451432411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10204721171349328601909881 7653540878511996451432411)
            ·
              refine ⟨11480311317767994677148617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7653540878511996451432411 11480311317767994677148617)
              ·
                refine ⟨8610233488325996007861463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11480311317767994677148617 8610233488325996007861463)
                ·
                  refine ⟨12915350232488994011792195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8610233488325996007861463 12915350232488994011792195)
                  ·
                    refine ⟨19373025348733491017688293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12915350232488994011792195 19373025348733491017688293)
                    ·
                      refine ⟨3632442252887529565816555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19373025348733491017688293 3632442252887529565816555)
                      ·
                        rfl

theorem cell23_7074156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 4].length) (baseStart_7074156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7074156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7074156 prefixEnd_7074156 := by exact prefixLift 7074156
  have htrace : WordTrace (prefixWord ++ tailWord_7074156) baseStart_7074156 baseEnd_7074156 := by
    simpa [prefixWord, tailWord_7074156, baseEnd_7074156] using wordTrace_append hprefix tailTrace_7074156
  have hstable : (prefixWord ++ tailWord_7074156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7074156).length < 2 ^ (prefixWord ++ tailWord_7074156).sum := by decide
  have hdescent : baseEnd_7074156 < baseStart_7074156 := by decide
  rcases family_descends (prefixWord ++ tailWord_7074156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7074166 : List Nat := [5, 1, 1, 4, 1, 1, 1, 2, 1, 6]
def baseStart_7074166 : Nat := 118140960795 + 7074166 * 2 ^ 59
def prefixEnd_7074166 : Nat := 4983230072969 + 3 ^ 40 * 7074166 * 2
def baseEnd_7074166 : Nat := 1210815795898024842230503

theorem tailTrace_7074166 : CollatzResearch.WordTrace tailWord_7074166 prefixEnd_7074166 1210815795898024842230503 := by
  unfold tailWord_7074166
  simp only [CollatzResearch.WordTrace]
  refine ⟨16126001930594514263154647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 172010687259674818806982901 16126001930594514263154647)
  ·
    refine ⟨24189002895891771394731971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16126001930594514263154647 24189002895891771394731971)
    ·
      refine ⟨36283504343837657092097957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24189002895891771394731971 36283504343837657092097957)
      ·
        refine ⟨6803157064469560704768367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36283504343837657092097957 6803157064469560704768367)
        ·
          refine ⟨10204735596704341057152551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6803157064469560704768367 10204735596704341057152551)
          ·
            refine ⟨15307103395056511585728827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10204735596704341057152551 15307103395056511585728827)
            ·
              refine ⟨22960655092584767378593241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15307103395056511585728827 22960655092584767378593241)
              ·
                refine ⟨17220491319438575533944931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22960655092584767378593241 17220491319438575533944931)
                ·
                  refine ⟨25830736979157863300917397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17220491319438575533944931 25830736979157863300917397)
                  ·
                    refine ⟨1210815795898024842230503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25830736979157863300917397 1210815795898024842230503)
                    ·
                      rfl

theorem cell23_7074166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 2, 1, 6].length) (baseStart_7074166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7074166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7074166 prefixEnd_7074166 := by exact prefixLift 7074166
  have htrace : WordTrace (prefixWord ++ tailWord_7074166) baseStart_7074166 baseEnd_7074166 := by
    simpa [prefixWord, tailWord_7074166, baseEnd_7074166] using wordTrace_append hprefix tailTrace_7074166
  have hstable : (prefixWord ++ tailWord_7074166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7074166).length < 2 ^ (prefixWord ++ tailWord_7074166).sum := by decide
  have hdescent : baseEnd_7074166 < baseStart_7074166 := by decide
  rcases family_descends (prefixWord ++ tailWord_7074166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7074190 : List Nat := [4, 1, 1, 4, 1, 2, 1, 4, 1, 2, 2]
def baseStart_7074190 : Nat := 118140960795 + 7074190 * 2 ^ 59
def prefixEnd_7074190 : Nat := 4983230072969 + 3 ^ 40 * 7074190 * 2
def baseEnd_7074190 : Nat := 3632459711229782432791399

theorem tailTrace_7074190 : CollatzResearch.WordTrace tailWord_7074190 prefixEnd_7074190 3632459711229782432791399 := by
  unfold tailWord_7074190
  simp only [CollatzResearch.WordTrace]
  refine ⟨32252113280178160038668503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172011270827616853539565349 32252113280178160038668503)
  ·
    refine ⟨48378169920267240058002755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32252113280178160038668503 48378169920267240058002755)
    ·
      refine ⟨72567254880400860087004133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48378169920267240058002755 72567254880400860087004133)
      ·
        refine ⟨13606360290075161266313275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72567254880400860087004133 13606360290075161266313275)
        ·
          refine ⟨20409540435112741899469913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13606360290075161266313275 20409540435112741899469913)
          ·
            refine ⟨15307155326334556424602435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20409540435112741899469913 15307155326334556424602435)
            ·
              refine ⟨22960732989501834636903653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15307155326334556424602435 22960732989501834636903653)
              ·
                refine ⟨4305137435531593994419435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22960732989501834636903653 4305137435531593994419435)
                ·
                  refine ⟨6457706153297390991629153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4305137435531593994419435 6457706153297390991629153)
                  ·
                    refine ⟨4843279614973043243721865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6457706153297390991629153 4843279614973043243721865)
                    ·
                      refine ⟨3632459711229782432791399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4843279614973043243721865 3632459711229782432791399)
                      ·
                        rfl

theorem cell23_7074190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 4, 1, 2, 2].length) (baseStart_7074190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7074190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7074190 prefixEnd_7074190 := by exact prefixLift 7074190
  have htrace : WordTrace (prefixWord ++ tailWord_7074190) baseStart_7074190 baseEnd_7074190 := by
    simpa [prefixWord, tailWord_7074190, baseEnd_7074190] using wordTrace_append hprefix tailTrace_7074190
  have hstable : (prefixWord ++ tailWord_7074190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7074190).length < 2 ^ (prefixWord ++ tailWord_7074190).sum := by decide
  have hdescent : baseEnd_7074190 < baseStart_7074190 := by decide
  rcases family_descends (prefixWord ++ tailWord_7074190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7074196 : List Nat := [2, 4, 2, 1, 4, 1, 1, 8]
def baseStart_7074196 : Nat := 118140960795 + 7074196 * 2 ^ 59
def prefixEnd_7074196 : Nat := 4983230072969 + 3 ^ 40 * 7074196 * 2
def baseEnd_7074196 : Nat := 134535658967174422567273

theorem tailTrace_7074196 : CollatzResearch.WordTrace tailWord_7074196 prefixEnd_7074196 134535658967174422567273 := by
  unfold tailWord_7074196
  simp only [CollatzResearch.WordTrace]
  refine ⟨129008562539701771667033221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172011416719602362222710961 129008562539701771667033221)
  ·
    refine ⟨24189105476194082187568729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 129008562539701771667033221 24189105476194082187568729)
    ·
      refine ⟨18141829107145561640676547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24189105476194082187568729 18141829107145561640676547)
      ·
        refine ⟨27212743660718342461014821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18141829107145561640676547 27212743660718342461014821)
        ·
          refine ⟨5102389436384689211440279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27212743660718342461014821 5102389436384689211440279)
          ·
            refine ⟨7653584154577033817160419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5102389436384689211440279 7653584154577033817160419)
            ·
              refine ⟨11480376231865550725740629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7653584154577033817160419 11480376231865550725740629)
              ·
                refine ⟨134535658967174422567273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11480376231865550725740629 134535658967174422567273)
                ·
                  rfl

theorem cell23_7074196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 1, 8].length) (baseStart_7074196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7074196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7074196 prefixEnd_7074196 := by exact prefixLift 7074196
  have htrace : WordTrace (prefixWord ++ tailWord_7074196) baseStart_7074196 baseEnd_7074196 := by
    simpa [prefixWord, tailWord_7074196, baseEnd_7074196] using wordTrace_append hprefix tailTrace_7074196
  have hstable : (prefixWord ++ tailWord_7074196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7074196).length < 2 ^ (prefixWord ++ tailWord_7074196).sum := by decide
  have hdescent : baseEnd_7074196 < baseStart_7074196 := by decide
  rcases family_descends (prefixWord ++ tailWord_7074196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7074199 : List Nat := [1, 1, 3, 3, 1, 1, 3, 2, 3, 3, 2]
def baseStart_7074199 : Nat := 118140960795 + 7074199 * 2 ^ 59
def prefixEnd_7074199 : Nat := 4983230072969 + 3 ^ 40 * 7074199 * 2
def baseEnd_7074199 : Nat := 3632464332555672897578857

theorem tailTrace_7074199 : CollatzResearch.WordTrace tailWord_7074199 prefixEnd_7074199 3632464332555672897578857 := by
  unfold tailWord_7074199
  simp only [CollatzResearch.WordTrace]
  refine ⟨258017234498392674846425651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172011489665595116564283767 258017234498392674846425651)
  ·
    refine ⟨387025851747589012269638477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258017234498392674846425651 387025851747589012269638477)
    ·
      refine ⟨145134694405345879601114429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 387025851747589012269638477 145134694405345879601114429)
      ·
        refine ⟨54425510402004704850417911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145134694405345879601114429 54425510402004704850417911)
        ·
          refine ⟨81638265603007057275626867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54425510402004704850417911 81638265603007057275626867)
          ·
            refine ⟨122457398404510585913440301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81638265603007057275626867 122457398404510585913440301)
            ·
              refine ⟨45921524401691469717540113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 122457398404510585913440301 45921524401691469717540113)
              ·
                refine ⟨34441143301268602288155085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45921524401691469717540113 34441143301268602288155085)
                ·
                  refine ⟨12915428737975725858058157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34441143301268602288155085 12915428737975725858058157)
                  ·
                    refine ⟨4843285776740897196771809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12915428737975725858058157 4843285776740897196771809)
                    ·
                      refine ⟨3632464332555672897578857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4843285776740897196771809 3632464332555672897578857)
                      ·
                        rfl

theorem cell23_7074199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 2, 3, 3, 2].length) (baseStart_7074199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7074199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7074199 prefixEnd_7074199 := by exact prefixLift 7074199
  have htrace : WordTrace (prefixWord ++ tailWord_7074199) baseStart_7074199 baseEnd_7074199 := by
    simpa [prefixWord, tailWord_7074199, baseEnd_7074199] using wordTrace_append hprefix tailTrace_7074199
  have hstable : (prefixWord ++ tailWord_7074199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7074199).length < 2 ^ (prefixWord ++ tailWord_7074199).sum := by decide
  have hdescent : baseEnd_7074199 < baseStart_7074199 := by decide
  rcases family_descends (prefixWord ++ tailWord_7074199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7074206 : List Nat := [4, 3, 1, 2, 1, 1, 1, 3, 1, 3, 3]
def baseStart_7074206 : Nat := 118140960795 + 7074206 * 2 ^ 59
def prefixEnd_7074206 : Nat := 4983230072969 + 3 ^ 40 * 7074206 * 2
def baseEnd_7074206 : Nat := 3632467926920254370191325

theorem tailTrace_7074206 : CollatzResearch.WordTrace tailWord_7074206 prefixEnd_7074206 3632467926920254370191325 := by
  unfold tailWord_7074206
  simp only [CollatzResearch.WordTrace]
  refine ⟨32252186226170914380241309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172011659872911543361286981 32252186226170914380241309)
  ·
    refine ⟨12094569834814092892590491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32252186226170914380241309 12094569834814092892590491)
    ·
      refine ⟨18141854752221139338885737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12094569834814092892590491 18141854752221139338885737)
      ·
        refine ⟨13606391064165854504164303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18141854752221139338885737 13606391064165854504164303)
        ·
          refine ⟨20409586596248781756246455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13606391064165854504164303 20409586596248781756246455)
          ·
            refine ⟨30614379894373172634369683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20409586596248781756246455 30614379894373172634369683)
            ·
              refine ⟨45921569841559758951554525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30614379894373172634369683 45921569841559758951554525)
              ·
                refine ⟨17220588690584909606832947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45921569841559758951554525 17220588690584909606832947)
                ·
                  refine ⟨25830883035877364410249421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17220588690584909606832947 25830883035877364410249421)
                  ·
                    refine ⟨9686581138454011653843533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25830883035877364410249421 9686581138454011653843533)
                    ·
                      refine ⟨3632467926920254370191325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9686581138454011653843533 3632467926920254370191325)
                      ·
                        rfl

theorem cell23_7074206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_7074206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7074206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7074206 prefixEnd_7074206 := by exact prefixLift 7074206
  have htrace : WordTrace (prefixWord ++ tailWord_7074206) baseStart_7074206 baseEnd_7074206 := by
    simpa [prefixWord, tailWord_7074206, baseEnd_7074206] using wordTrace_append hprefix tailTrace_7074206
  have hstable : (prefixWord ++ tailWord_7074206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7074206).length < 2 ^ (prefixWord ++ tailWord_7074206).sum := by decide
  have hdescent : baseEnd_7074206 < baseStart_7074206 := by decide
  rcases family_descends (prefixWord ++ tailWord_7074206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7074233 : List Nat := [1, 2, 1, 4, 3, 1, 4, 1, 1, 3, 2]
def baseStart_7074233 : Nat := 118140960795 + 7074233 * 2 ^ 59
def prefixEnd_7074233 : Nat := 4983230072969 + 3 ^ 40 * 7074233 * 2
def baseEnd_7074233 : Nat := 3632481790897925764553701

theorem tailTrace_7074233 : CollatzResearch.WordTrace tailWord_7074233 prefixEnd_7074233 3632481790897925764553701 := by
  unfold tailWord_7074233
  simp only [CollatzResearch.WordTrace]
  refine ⟨258018474580269498653163353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172012316386846332435442235 258018474580269498653163353)
  ·
    refine ⟨193513855935202123989872515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258018474580269498653163353 193513855935202123989872515)
    ·
      refine ⟨290270783902803185984808773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193513855935202123989872515 290270783902803185984808773)
      ·
        refine ⟨54425771981775597372151645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 290270783902803185984808773 54425771981775597372151645)
        ·
          refine ⟨20409664493165849014556867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54425771981775597372151645 20409664493165849014556867)
          ·
            refine ⟨30614496739748773521835301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20409664493165849014556867 30614496739748773521835301)
            ·
              refine ⟨5740218138702895035344119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30614496739748773521835301 5740218138702895035344119)
              ·
                refine ⟨8610327208054342553016179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5740218138702895035344119 8610327208054342553016179)
                ·
                  refine ⟨12915490812081513829524269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8610327208054342553016179 12915490812081513829524269)
                  ·
                    refine ⟨4843309054530567686071601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12915490812081513829524269 4843309054530567686071601)
                    ·
                      refine ⟨3632481790897925764553701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4843309054530567686071601 3632481790897925764553701)
                      ·
                        rfl

theorem cell23_7074233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 4, 1, 1, 3, 2].length) (baseStart_7074233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7074233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7074233 prefixEnd_7074233 := by exact prefixLift 7074233
  have htrace : WordTrace (prefixWord ++ tailWord_7074233) baseStart_7074233 baseEnd_7074233 := by
    simpa [prefixWord, tailWord_7074233, baseEnd_7074233] using wordTrace_append hprefix tailTrace_7074233
  have hstable : (prefixWord ++ tailWord_7074233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7074233).length < 2 ^ (prefixWord ++ tailWord_7074233).sum := by decide
  have hdescent : baseEnd_7074233 < baseStart_7074233 := by decide
  rcases family_descends (prefixWord ++ tailWord_7074233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7074286 : List Nat := [4, 1, 2, 1, 2, 2, 3, 3, 5]
def baseStart_7074286 : Nat := 118140960795 + 7074286 * 2 ^ 59
def prefixEnd_7074286 : Nat := 4983230072969 + 3 ^ 40 * 7074286 * 2
def baseEnd_7074286 : Nat := 403612111708068228576773

theorem tailTrace_7074286 : CollatzResearch.WordTrace tailWord_7074286 prefixEnd_7074286 403612111708068228576773 := by
  unfold tailWord_7074286
  simp only [CollatzResearch.WordTrace]
  refine ⟨32252550956134686088105339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172013605099384992469895141 32252550956134686088105339)
  ·
    refine ⟨48378826434202029132158009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32252550956134686088105339 48378826434202029132158009)
    ·
      refine ⟨36284119825651521849118507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48378826434202029132158009 36284119825651521849118507)
      ·
        refine ⟨54426179738477282773677761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36284119825651521849118507 54426179738477282773677761)
        ·
          refine ⟨40819634803857962080258321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54426179738477282773677761 40819634803857962080258321)
          ·
            refine ⟨30614726102893471560193741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40819634803857962080258321 30614726102893471560193741)
            ·
              refine ⟨11480522288585051835072653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30614726102893471560193741 11480522288585051835072653)
              ·
                refine ⟨4305195858219394438152245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11480522288585051835072653 4305195858219394438152245)
                ·
                  refine ⟨403612111708068228576773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4305195858219394438152245 403612111708068228576773)
                  ·
                    rfl

theorem cell23_7074286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 3, 3, 5].length) (baseStart_7074286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7074286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7074286 prefixEnd_7074286 := by exact prefixLift 7074286
  have htrace : WordTrace (prefixWord ++ tailWord_7074286) baseStart_7074286 baseEnd_7074286 := by
    simpa [prefixWord, tailWord_7074286, baseEnd_7074286] using wordTrace_append hprefix tailTrace_7074286
  have hstable : (prefixWord ++ tailWord_7074286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7074286).length < 2 ^ (prefixWord ++ tailWord_7074286).sum := by decide
  have hdescent : baseEnd_7074286 < baseStart_7074286 := by decide
  rcases family_descends (prefixWord ++ tailWord_7074286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7074359 : List Nat := [1, 1, 3, 1, 2, 3, 4, 2, 6]
def baseStart_7074359 : Nat := 118140960795 + 7074359 * 2 ^ 59
def prefixEnd_7074359 : Nat := 4983230072969 + 3 ^ 40 * 7074359 * 2
def baseEnd_7074359 : Nat := 403616276606710252397569

theorem tailTrace_7074359 : CollatzResearch.WordTrace tailWord_7074359 prefixEnd_7074359 403616276606710252397569 := by
  unfold tailWord_7074359
  simp only [CollatzResearch.WordTrace]
  refine ⟨258023070177813022172250131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172015380118542014781500087 258023070177813022172250131)
  ·
    refine ⟨387034605266719533258375197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258023070177813022172250131 387034605266719533258375197)
    ·
      refine ⟨145137976975019824971890699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 387034605266719533258375197 145137976975019824971890699)
      ·
        refine ⟨217706965462529737457836049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145137976975019824971890699 217706965462529737457836049)
        ·
          refine ⟨163280224096897303093377037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217706965462529737457836049 163280224096897303093377037)
          ·
            refine ⟨61230084036336488660016389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 163280224096897303093377037 61230084036336488660016389)
            ·
              refine ⟨11480640756813091623753073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61230084036336488660016389 11480640756813091623753073)
              ·
                refine ⟨8610480567609818717814805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11480640756813091623753073 8610480567609818717814805)
                ·
                  refine ⟨403616276606710252397569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8610480567609818717814805 403616276606710252397569)
                  ·
                    rfl

theorem cell23_7074359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 4, 2, 6].length) (baseStart_7074359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7074359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7074359 prefixEnd_7074359 := by exact prefixLift 7074359
  have htrace : WordTrace (prefixWord ++ tailWord_7074359) baseStart_7074359 baseEnd_7074359 := by
    simpa [prefixWord, tailWord_7074359, baseEnd_7074359] using wordTrace_append hprefix tailTrace_7074359
  have hstable : (prefixWord ++ tailWord_7074359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7074359).length < 2 ^ (prefixWord ++ tailWord_7074359).sum := by decide
  have hdescent : baseEnd_7074359 < baseStart_7074359 := by decide
  rcases family_descends (prefixWord ++ tailWord_7074359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7074389 : List Nat := [1, 3, 2, 2, 1, 1, 4, 1, 3, 5]
def baseStart_7074389 : Nat := 118140960795 + 7074389 * 2 ^ 59
def prefixEnd_7074389 : Nat := 4983230072969 + 3 ^ 40 * 7074389 * 2
def baseEnd_7074389 : Nat := 1210853964626675718067661

theorem tailTrace_7074389 : CollatzResearch.WordTrace tailWord_7074389 prefixEnd_7074389 1210853964626675718067661 := by
  unfold tailWord_7074389
  simp only [CollatzResearch.WordTrace]
  refine ⟨258024164367704337295842221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172016109578469558197228147 258024164367704337295842221)
  ·
    refine ⟨96759061637889126485940833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 258024164367704337295842221 96759061637889126485940833)
    ·
      refine ⟨72569296228416844864455625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96759061637889126485940833 72569296228416844864455625)
      ·
        refine ⟨54426972171312633648341719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72569296228416844864455625 54426972171312633648341719)
        ·
          refine ⟨81640458256968950472512579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54426972171312633648341719 81640458256968950472512579)
          ·
            refine ⟨122460687385453425708768869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81640458256968950472512579 122460687385453425708768869)
            ·
              refine ⟨22961378884772517320394163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 122460687385453425708768869 22961378884772517320394163)
              ·
                refine ⟨34442068327158775980591245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22961378884772517320394163 34442068327158775980591245)
                ·
                  refine ⟨12915775622684540992721717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34442068327158775980591245 12915775622684540992721717)
                  ·
                    refine ⟨1210853964626675718067661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12915775622684540992721717 1210853964626675718067661)
                    ·
                      rfl

theorem cell23_7074389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 1, 3, 5].length) (baseStart_7074389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7074389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7074389 prefixEnd_7074389 := by exact prefixLift 7074389
  have htrace : WordTrace (prefixWord ++ tailWord_7074389) baseStart_7074389 baseEnd_7074389 := by
    simpa [prefixWord, tailWord_7074389, baseEnd_7074389] using wordTrace_append hprefix tailTrace_7074389
  have hstable : (prefixWord ++ tailWord_7074389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7074389).length < 2 ^ (prefixWord ++ tailWord_7074389).sum := by decide
  have hdescent : baseEnd_7074389 < baseStart_7074389 := by decide
  rcases family_descends (prefixWord ++ tailWord_7074389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7074436 : List Nat := [2, 3, 2, 1, 3, 1, 3, 1, 1, 6]
def baseStart_7074436 : Nat := 118140960795 + 7074436 * 2 ^ 59
def prefixEnd_7074436 : Nat := 4983230072969 + 3 ^ 40 * 7074436 * 2
def baseEnd_7074436 : Nat := 1210862009156929490105089

theorem tailTrace_7074436 : CollatzResearch.WordTrace tailWord_7074436 prefixEnd_7074436 1210862009156929490105089 := by
  unfold tailWord_7074436
  simp only [CollatzResearch.WordTrace]
  refine ⟨129012939299267032161401581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172017252399022709548535441 129012939299267032161401581)
  ·
    refine ⟨48379852237225137060525593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129012939299267032161401581 48379852237225137060525593)
    ·
      refine ⟨36284889177918852795394195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48379852237225137060525593 36284889177918852795394195)
      ·
        refine ⟨54427333766878279193091293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36284889177918852795394195 54427333766878279193091293)
        ·
          refine ⟨20410250162579354697409235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54427333766878279193091293 20410250162579354697409235)
          ·
            refine ⟨30615375243869032046113853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20410250162579354697409235 30615375243869032046113853)
            ·
              refine ⟨11480765716450887017292695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30615375243869032046113853 11480765716450887017292695)
              ·
                refine ⟨17221148574676330525939043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11480765716450887017292695 17221148574676330525939043)
                ·
                  refine ⟨25831722862014495788908565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17221148574676330525939043 25831722862014495788908565)
                  ·
                    refine ⟨1210862009156929490105089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25831722862014495788908565 1210862009156929490105089)
                    ·
                      rfl

theorem cell23_7074436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 3, 1, 1, 6].length) (baseStart_7074436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7074436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7074436 prefixEnd_7074436 := by exact prefixLift 7074436
  have htrace : WordTrace (prefixWord ++ tailWord_7074436) baseStart_7074436 baseEnd_7074436 := by
    simpa [prefixWord, tailWord_7074436, baseEnd_7074436] using wordTrace_append hprefix tailTrace_7074436
  have hstable : (prefixWord ++ tailWord_7074436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7074436).length < 2 ^ (prefixWord ++ tailWord_7074436).sum := by decide
  have hdescent : baseEnd_7074436 < baseStart_7074436 := by decide
  rcases family_descends (prefixWord ++ tailWord_7074436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7074439 : List Nat := [1, 1, 4, 2, 1, 2, 3, 1, 1, 1, 6]
def baseStart_7074439 : Nat := 118140960795 + 7074439 * 2 ^ 59
def prefixEnd_7074439 : Nat := 4983230072969 + 3 ^ 40 * 7074439 * 2
def baseEnd_7074439 : Nat := 3632587567912751958577753

theorem tailTrace_7074439 : CollatzResearch.WordTrace tailWord_7074439 prefixEnd_7074439 3632587567912751958577753 := by
  unfold tailWord_7074439
  simp only [CollatzResearch.WordTrace]
  refine ⟨258025988017523195835162371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172017325345015463890108247 258025988017523195835162371)
  ·
    refine ⟨387038982026284793752743557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258025988017523195835162371 387038982026284793752743557)
    ·
      refine ⟨72569809129928398828639417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 387038982026284793752743557 72569809129928398828639417)
      ·
        refine ⟨54427356847446299121479563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72569809129928398828639417 54427356847446299121479563)
        ·
          refine ⟨81641035271169448682219345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54427356847446299121479563 81641035271169448682219345)
          ·
            refine ⟨61230776453377086511664509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81641035271169448682219345 61230776453377086511664509)
            ·
              refine ⟨22961541170016407441874191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61230776453377086511664509 22961541170016407441874191)
              ·
                refine ⟨34442311755024611162811287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22961541170016407441874191 34442311755024611162811287)
                ·
                  refine ⟨51663467632536916744216931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34442311755024611162811287 51663467632536916744216931)
                  ·
                    refine ⟨77495201448805375116325397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51663467632536916744216931 77495201448805375116325397)
                    ·
                      refine ⟨3632587567912751958577753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77495201448805375116325397 3632587567912751958577753)
                      ·
                        rfl

theorem cell23_7074439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 1, 1, 1, 6].length) (baseStart_7074439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7074439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7074439 prefixEnd_7074439 := by exact prefixLift 7074439
  have htrace : WordTrace (prefixWord ++ tailWord_7074439) baseStart_7074439 baseEnd_7074439 := by
    simpa [prefixWord, tailWord_7074439, baseEnd_7074439] using wordTrace_append hprefix tailTrace_7074439
  have hstable : (prefixWord ++ tailWord_7074439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7074439).length < 2 ^ (prefixWord ++ tailWord_7074439).sum := by decide
  have hdescent : baseEnd_7074439 < baseStart_7074439 := by decide
  rcases family_descends (prefixWord ++ tailWord_7074439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7074459 : List Nat := [1, 1, 1, 1, 1, 1, 2, 2, 7, 3, 3]
def baseStart_7074459 : Nat := 118140960795 + 7074459 * 2 ^ 59
def prefixEnd_7074459 : Nat := 4983230072969 + 3 ^ 40 * 7074459 * 2
def baseEnd_7074459 : Nat := 3632597837525841880327661

theorem tailTrace_7074459 : CollatzResearch.WordTrace tailWord_7074459 prefixEnd_7074459 3632597837525841880327661 := by
  unfold tailWord_7074459
  simp only [CollatzResearch.WordTrace]
  refine ⟨258026717477450739250890431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172017811651633826167260287 258026717477450739250890431)
  ·
    refine ⟨387040076216176108876335647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258026717477450739250890431 387040076216176108876335647)
    ·
      refine ⟨580560114324264163314503471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 387040076216176108876335647 580560114324264163314503471)
      ·
        refine ⟨870840171486396244971755207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 580560114324264163314503471 870840171486396244971755207)
        ·
          refine ⟨1306260257229594367457632811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 870840171486396244971755207 1306260257229594367457632811)
          ·
            refine ⟨1959390385844391551186449217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1306260257229594367457632811 1959390385844391551186449217)
            ·
              refine ⟨1469542789383293663389836913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1959390385844391551186449217 1469542789383293663389836913)
              ·
                refine ⟨1102157092037470247542377685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1469542789383293663389836913 1102157092037470247542377685)
                ·
                  refine ⟨25831806844628208926774477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1102157092037470247542377685 25831806844628208926774477)
                  ·
                    refine ⟨9686927566735578347540429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25831806844628208926774477 9686927566735578347540429)
                    ·
                      refine ⟨3632597837525841880327661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9686927566735578347540429 3632597837525841880327661)
                      ·
                        rfl

theorem cell23_7074459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 7, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 7, 3, 3].length) (baseStart_7074459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7074459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7074459 prefixEnd_7074459 := by exact prefixLift 7074459
  have htrace : WordTrace (prefixWord ++ tailWord_7074459) baseStart_7074459 baseEnd_7074459 := by
    simpa [prefixWord, tailWord_7074459, baseEnd_7074459] using wordTrace_append hprefix tailTrace_7074459
  have hstable : (prefixWord ++ tailWord_7074459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7074459).length < 2 ^ (prefixWord ++ tailWord_7074459).sum := by decide
  have hdescent : baseEnd_7074459 < baseStart_7074459 := by decide
  rcases family_descends (prefixWord ++ tailWord_7074459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7074477 : List Nat := [1, 5, 2, 1, 1, 4, 1, 1, 3, 2, 2]
def baseStart_7074477 : Nat := 118140960795 + 7074477 * 2 ^ 59
def prefixEnd_7074477 : Nat := 4983230072969 + 3 ^ 40 * 7074477 * 2
def baseEnd_7074477 : Nat := 3632607080177622809902579

theorem tailTrace_7074477 : CollatzResearch.WordTrace tailWord_7074477 prefixEnd_7074477 3632607080177622809902579 := by
  unfold tailWord_7074477
  simp only [CollatzResearch.WordTrace]
  refine ⟨258027373991385528325045685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172018249327590352216697123 258027373991385528325045685)
  ·
    refine ⟨24190066311692393280473033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 258027373991385528325045685 24190066311692393280473033)
    ·
      refine ⟨18142549733769294960354775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24190066311692393280473033 18142549733769294960354775)
      ·
        refine ⟨27213824600653942440532163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18142549733769294960354775 27213824600653942440532163)
        ·
          refine ⟨40820736900980913660798245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27213824600653942440532163 40820736900980913660798245)
          ·
            refine ⟨7653888168933921311399671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40820736900980913660798245 7653888168933921311399671)
            ·
              refine ⟨11480832253400881967099507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7653888168933921311399671 11480832253400881967099507)
              ·
                refine ⟨17221248380101322950649261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11480832253400881967099507 17221248380101322950649261)
                ·
                  refine ⟨6457968142537996106493473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17221248380101322950649261 6457968142537996106493473)
                  ·
                    refine ⟨4843476106903497079870105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6457968142537996106493473 4843476106903497079870105)
                    ·
                      refine ⟨3632607080177622809902579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4843476106903497079870105 3632607080177622809902579)
                      ·
                        rfl

theorem cell23_7074477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 1, 1, 3, 2, 2].length) (baseStart_7074477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7074477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7074477 prefixEnd_7074477 := by exact prefixLift 7074477
  have htrace : WordTrace (prefixWord ++ tailWord_7074477) baseStart_7074477 baseEnd_7074477 := by
    simpa [prefixWord, tailWord_7074477, baseEnd_7074477] using wordTrace_append hprefix tailTrace_7074477
  have hstable : (prefixWord ++ tailWord_7074477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7074477).length < 2 ^ (prefixWord ++ tailWord_7074477).sum := by decide
  have hdescent : baseEnd_7074477 < baseStart_7074477 := by decide
  rcases family_descends (prefixWord ++ tailWord_7074477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7074487 : List Nat := [1, 1, 3, 1, 7, 1, 2, 1, 2, 4]
def baseStart_7074487 : Nat := 118140960795 + 7074487 * 2 ^ 59
def prefixEnd_7074487 : Nat := 4983230072969 + 3 ^ 40 * 7074487 * 2
def baseEnd_7074487 : Nat := 1210870738328055923592511

theorem tailTrace_7074487 : CollatzResearch.WordTrace tailWord_7074487 prefixEnd_7074487 1210870738328055923592511 := by
  unfold tailWord_7074487
  simp only [CollatzResearch.WordTrace]
  refine ⟨258027738721349300032909715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172018492480899533355273143 258027738721349300032909715)
  ·
    refine ⟨387041608082023950049364573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258027738721349300032909715 387041608082023950049364573)
    ·
      refine ⟨145140603030758981268511715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 387041608082023950049364573 145140603030758981268511715)
      ·
        refine ⟨217710904546138471902767573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145140603030758981268511715 217710904546138471902767573)
        ·
          refine ⟨5102599325300120435221115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 217710904546138471902767573 5102599325300120435221115)
          ·
            refine ⟨7653898987950180652831673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5102599325300120435221115 7653898987950180652831673)
            ·
              refine ⟨5740424240962635489623755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7653898987950180652831673 5740424240962635489623755)
              ·
                refine ⟨8610636361443953234435633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5740424240962635489623755 8610636361443953234435633)
                ·
                  refine ⟨6457977271082964925826725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8610636361443953234435633 6457977271082964925826725)
                  ·
                    refine ⟨1210870738328055923592511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6457977271082964925826725 1210870738328055923592511)
                    ·
                      rfl

theorem cell23_7074487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 2, 1, 2, 4].length) (baseStart_7074487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7074487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7074487 prefixEnd_7074487 := by exact prefixLift 7074487
  have htrace : WordTrace (prefixWord ++ tailWord_7074487) baseStart_7074487 baseEnd_7074487 := by
    simpa [prefixWord, tailWord_7074487, baseEnd_7074487] using wordTrace_append hprefix tailTrace_7074487
  have hstable : (prefixWord ++ tailWord_7074487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7074487).length < 2 ^ (prefixWord ++ tailWord_7074487).sum := by decide
  have hdescent : baseEnd_7074487 < baseStart_7074487 := by decide
  rcases family_descends (prefixWord ++ tailWord_7074487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7074503 : List Nat := [1, 1, 4, 1, 1, 1, 2, 6, 1, 3, 2]
def baseStart_7074503 : Nat := 118140960795 + 7074503 * 2 ^ 59
def prefixEnd_7074503 : Nat := 4983230072969 + 3 ^ 40 * 7074503 * 2
def baseEnd_7074503 : Nat := 3632620430674639708177459

theorem tailTrace_7074503 : CollatzResearch.WordTrace tailWord_7074503 prefixEnd_7074503 3632620430674639708177459 := by
  unfold tailWord_7074503
  simp only [CollatzResearch.WordTrace]
  refine ⟨258028322289291334765492163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172018881526194223176994775 258028322289291334765492163)
  ·
    refine ⟨387042483433937002148238245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258028322289291334765492163 387042483433937002148238245)
    ·
      refine ⟨72570465643863187902794671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 387042483433937002148238245 72570465643863187902794671)
      ·
        refine ⟨108855698465794781854192007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72570465643863187902794671 108855698465794781854192007)
        ·
          refine ⟨163283547698692172781288011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108855698465794781854192007 163283547698692172781288011)
          ·
            refine ⟨244925321548038259171932017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163283547698692172781288011 244925321548038259171932017)
            ·
              refine ⟨183693991161028694378949013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 244925321548038259171932017 183693991161028694378949013)
              ·
                refine ⟨8610655835673220049013235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 183693991161028694378949013 8610655835673220049013235)
                ·
                  refine ⟨12915983753509830073519853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8610655835673220049013235 12915983753509830073519853)
                  ·
                    refine ⟨4843493907566186277569945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12915983753509830073519853 4843493907566186277569945)
                    ·
                      refine ⟨3632620430674639708177459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4843493907566186277569945 3632620430674639708177459)
                      ·
                        rfl

theorem cell23_7074503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 6, 1, 3, 2].length) (baseStart_7074503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7074503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7074503 prefixEnd_7074503 := by exact prefixLift 7074503
  have htrace : WordTrace (prefixWord ++ tailWord_7074503) baseStart_7074503 baseEnd_7074503 := by
    simpa [prefixWord, tailWord_7074503, baseEnd_7074503] using wordTrace_append hprefix tailTrace_7074503
  have hstable : (prefixWord ++ tailWord_7074503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7074503).length < 2 ^ (prefixWord ++ tailWord_7074503).sum := by decide
  have hdescent : baseEnd_7074503 < baseStart_7074503 := by decide
  rcases family_descends (prefixWord ++ tailWord_7074503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7074539 : List Nat := [1, 1, 1, 1, 2, 4, 1, 5, 7]
def baseStart_7074539 : Nat := 118140960795 + 7074539 * 2 ^ 59
def prefixEnd_7074539 : Nat := 4983230072969 + 3 ^ 40 * 7074539 * 2
def baseEnd_7074539 : Nat := 403626546219800174147477

theorem tailTrace_7074539 : CollatzResearch.WordTrace tailWord_7074539 prefixEnd_7074539 403626546219800174147477 := by
  unfold tailWord_7074539
  simp only [CollatzResearch.WordTrace]
  refine ⟨258029635317160912913802671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172019756878107275275868447 258029635317160912913802671)
  ·
    refine ⟨387044452975741369370704007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258029635317160912913802671 387044452975741369370704007)
    ·
      refine ⟨580566679463612054056056011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 387044452975741369370704007 580566679463612054056056011)
      ·
        refine ⟨870850019195418081084084017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 580566679463612054056056011 870850019195418081084084017)
        ·
          refine ⟨653137514396563560813063013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 870850019195418081084084017 653137514396563560813063013)
          ·
            refine ⟨122463283949355667652449315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 653137514396563560813063013 122463283949355667652449315)
            ·
              refine ⟨183694925924033501478673973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122463283949355667652449315 183694925924033501478673973)
              ·
                refine ⟨17221399305378140763625685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 183694925924033501478673973 17221399305378140763625685)
                ·
                  refine ⟨403626546219800174147477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17221399305378140763625685 403626546219800174147477)
                  ·
                    rfl

theorem cell23_7074539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 5, 7].length) (baseStart_7074539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7074539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7074539 prefixEnd_7074539 := by exact prefixLift 7074539
  have htrace : WordTrace (prefixWord ++ tailWord_7074539) baseStart_7074539 baseEnd_7074539 := by
    simpa [prefixWord, tailWord_7074539, baseEnd_7074539] using wordTrace_append hprefix tailTrace_7074539
  have hstable : (prefixWord ++ tailWord_7074539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7074539).length < 2 ^ (prefixWord ++ tailWord_7074539).sum := by decide
  have hdescent : baseEnd_7074539 < baseStart_7074539 := by decide
  rcases family_descends (prefixWord ++ tailWord_7074539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7074546 : List Nat := [3, 2, 1, 3, 1, 2, 1, 1, 1, 4, 4]
def baseStart_7074546 : Nat := 118140960795 + 7074546 * 2 ^ 59
def prefixEnd_7074546 : Nat := 4983230072969 + 3 ^ 40 * 7074546 * 2
def baseEnd_7074546 : Nat := 3632642510342783039939761

theorem tailTrace_7074546 : CollatzResearch.WordTrace tailWord_7074546 prefixEnd_7074546 3632642510342783039939761 := by
  unfold tailWord_7074546
  simp only [CollatzResearch.WordTrace]
  refine ⟨64507472657033888277326873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172019927085423702072871661 64507472657033888277326873)
  ·
    refine ⟨48380604492775416207995155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64507472657033888277326873 48380604492775416207995155)
    ·
      refine ⟨72570906739163124311992733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48380604492775416207995155 72570906739163124311992733)
      ·
        refine ⟨27214090027186171616997275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72570906739163124311992733 27214090027186171616997275)
        ·
          refine ⟨40821135040779257425495913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27214090027186171616997275 40821135040779257425495913)
          ·
            refine ⟨30615851280584443069121935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40821135040779257425495913 30615851280584443069121935)
            ·
              refine ⟨45923776920876664603682903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30615851280584443069121935 45923776920876664603682903)
              ·
                refine ⟨68885665381314996905524355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45923776920876664603682903 68885665381314996905524355)
                ·
                  refine ⟨103328498071972495358286533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68885665381314996905524355 103328498071972495358286533)
                  ·
                    refine ⟨19374093388494842879678725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 103328498071972495358286533 19374093388494842879678725)
                    ·
                      refine ⟨3632642510342783039939761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19374093388494842879678725 3632642510342783039939761)
                      ·
                        rfl

theorem cell23_7074546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_7074546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7074546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7074546 prefixEnd_7074546 := by exact prefixLift 7074546
  have htrace : WordTrace (prefixWord ++ tailWord_7074546) baseStart_7074546 baseEnd_7074546 := by
    simpa [prefixWord, tailWord_7074546, baseEnd_7074546] using wordTrace_append hprefix tailTrace_7074546
  have hstable : (prefixWord ++ tailWord_7074546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7074546).length < 2 ^ (prefixWord ++ tailWord_7074546).sum := by decide
  have hdescent : baseEnd_7074546 < baseStart_7074546 := by decide
  rcases family_descends (prefixWord ++ tailWord_7074546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7074550 : List Nat := [5, 1, 1, 1, 1, 2, 4, 1, 1, 4, 2]
def baseStart_7074550 : Nat := 118140960795 + 7074550 * 2 ^ 59
def prefixEnd_7074550 : Nat := 4983230072969 + 3 ^ 40 * 7074550 * 2
def baseEnd_7074550 : Nat := 3632644564265401024289743

theorem tailTrace_7074550 : CollatzResearch.WordTrace tailWord_7074550 prefixEnd_7074550 3632644564265401024289743 := by
  unfold tailWord_7074550
  simp only [CollatzResearch.WordTrace]
  refine ⟨16126877282507566362028319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 172020024346747374528302069 16126877282507566362028319)
  ·
    refine ⟨24190315923761349543042479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16126877282507566362028319 24190315923761349543042479)
    ·
      refine ⟨36285473885642024314563719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24190315923761349543042479 36285473885642024314563719)
      ·
        refine ⟨54428210828463036471845579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36285473885642024314563719 54428210828463036471845579)
        ·
          refine ⟨81642316242694554707768369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54428210828463036471845579 81642316242694554707768369)
          ·
            refine ⟨61231737182020916030826277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81642316242694554707768369 61231737182020916030826277)
            ·
              refine ⟨11480950721628921755779927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61231737182020916030826277 11480950721628921755779927)
              ·
                refine ⟨17221426082443382633669891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11480950721628921755779927 17221426082443382633669891)
                ·
                  refine ⟨25832139123665073950504837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17221426082443382633669891 25832139123665073950504837)
                  ·
                    refine ⟨4843526085687201365719657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25832139123665073950504837 4843526085687201365719657)
                    ·
                      refine ⟨3632644564265401024289743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4843526085687201365719657 3632644564265401024289743)
                      ·
                        rfl

theorem cell23_7074550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 4, 1, 1, 4, 2].length) (baseStart_7074550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7074550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7074550 prefixEnd_7074550 := by exact prefixLift 7074550
  have htrace : WordTrace (prefixWord ++ tailWord_7074550) baseStart_7074550 baseEnd_7074550 := by
    simpa [prefixWord, tailWord_7074550, baseEnd_7074550] using wordTrace_append hprefix tailTrace_7074550
  have hstable : (prefixWord ++ tailWord_7074550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7074550).length < 2 ^ (prefixWord ++ tailWord_7074550).sum := by decide
  have hdescent : baseEnd_7074550 < baseStart_7074550 := by decide
  rcases family_descends (prefixWord ++ tailWord_7074550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7074556 : List Nat := [2, 2, 2, 1, 3, 3, 1, 2, 7]
def baseStart_7074556 : Nat := 118140960795 + 7074556 * 2 ^ 59
def prefixEnd_7074556 : Nat := 4983230072969 + 3 ^ 40 * 7074556 * 2
def baseEnd_7074556 : Nat := 403627516127703111201635

theorem tailTrace_7074556 : CollatzResearch.WordTrace tailWord_7074556 prefixEnd_7074556 403627516127703111201635 := by
  unfold tailWord_7074556
  simp only [CollatzResearch.WordTrace]
  refine ⟨129015127679049662408585761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172020170238732883211447681 129015127679049662408585761)
  ·
    refine ⟨96761345759287246806439321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129015127679049662408585761 96761345759287246806439321)
    ·
      refine ⟨72571009319465435104829491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96761345759287246806439321 72571009319465435104829491)
      ·
        refine ⟨108856513979198152657244237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72571009319465435104829491 108856513979198152657244237)
        ·
          refine ⟨40821192742199307246466589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108856513979198152657244237 40821192742199307246466589)
          ·
            refine ⟨15307947278324740217424971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40821192742199307246466589 15307947278324740217424971)
            ·
              refine ⟨22961920917487110326137457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15307947278324740217424971 22961920917487110326137457)
              ·
                refine ⟨17221440688115332744603093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22961920917487110326137457 17221440688115332744603093)
                ·
                  refine ⟨403627516127703111201635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17221440688115332744603093 403627516127703111201635)
                  ·
                    rfl

theorem cell23_7074556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 2, 7].length) (baseStart_7074556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7074556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7074556 prefixEnd_7074556 := by exact prefixLift 7074556
  have htrace : WordTrace (prefixWord ++ tailWord_7074556) baseStart_7074556 baseEnd_7074556 := by
    simpa [prefixWord, tailWord_7074556, baseEnd_7074556] using wordTrace_append hprefix tailTrace_7074556
  have hstable : (prefixWord ++ tailWord_7074556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7074556).length < 2 ^ (prefixWord ++ tailWord_7074556).sum := by decide
  have hdescent : baseEnd_7074556 < baseStart_7074556 := by decide
  rcases family_descends (prefixWord ++ tailWord_7074556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7074586 : List Nat := [3, 1, 1, 3, 2, 1, 2, 1, 4, 5]
def baseStart_7074586 : Nat := 118140960795 + 7074586 * 2 ^ 59
def prefixEnd_7074586 : Nat := 4983230072969 + 3 ^ 40 * 7074586 * 2
def baseEnd_7074586 : Nat := 1210887683189654294479859

theorem tailTrace_7074586 : CollatzResearch.WordTrace tailWord_7074586 prefixEnd_7074586 1210887683189654294479859 := by
  unfold tailWord_7074586
  simp only [CollatzResearch.WordTrace]
  refine ⟨64507837386997659985190903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172020899698660426627175741 64507837386997659985190903)
  ·
    refine ⟨96761756080496489977786355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64507837386997659985190903 96761756080496489977786355)
    ·
      refine ⟨145142634120744734966679533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96761756080496489977786355 145142634120744734966679533)
      ·
        refine ⟨54428487795279275612504825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145142634120744734966679533 54428487795279275612504825)
        ·
          refine ⟨40821365846459456709378619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54428487795279275612504825 40821365846459456709378619)
          ·
            refine ⟨61232048769689185064067929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40821365846459456709378619 61232048769689185064067929)
            ·
              refine ⟨45924036577266888798050947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61232048769689185064067929 45924036577266888798050947)
              ·
                refine ⟨68886054865900333197076421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45924036577266888798050947 68886054865900333197076421)
                ·
                  refine ⟨12916135287356312474451829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68886054865900333197076421 12916135287356312474451829)
                  ·
                    refine ⟨1210887683189654294479859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12916135287356312474451829 1210887683189654294479859)
                    ·
                      rfl

theorem cell23_7074586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 1, 4, 5].length) (baseStart_7074586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7074586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7074586 prefixEnd_7074586 := by exact prefixLift 7074586
  have htrace : WordTrace (prefixWord ++ tailWord_7074586) baseStart_7074586 baseEnd_7074586 := by
    simpa [prefixWord, tailWord_7074586, baseEnd_7074586] using wordTrace_append hprefix tailTrace_7074586
  have hstable : (prefixWord ++ tailWord_7074586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7074586).length < 2 ^ (prefixWord ++ tailWord_7074586).sum := by decide
  have hdescent : baseEnd_7074586 < baseStart_7074586 := by decide
  rcases family_descends (prefixWord ++ tailWord_7074586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7074650 : List Nat := [3, 1, 1, 2, 1, 6, 1, 1, 3, 4]
def baseStart_7074650 : Nat := 118140960795 + 7074650 * 2 ^ 59
def prefixEnd_7074650 : Nat := 4983230072969 + 3 ^ 40 * 7074650 * 2
def baseEnd_7074650 : Nat := 1210898637443616877679761

theorem tailTrace_7074650 : CollatzResearch.WordTrace tailWord_7074650 prefixEnd_7074650 1210898637443616877679761 := by
  unfold tailWord_7074650
  simp only [CollatzResearch.WordTrace]
  refine ⟨64508420954939694717773351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172022455879839185914062269 64508420954939694717773351)
  ·
    refine ⟨96762631432409542076660027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64508420954939694717773351 96762631432409542076660027)
    ·
      refine ⟨145143947148614313114990041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96762631432409542076660027 145143947148614313114990041)
      ·
        refine ⟨108857960361460734836242531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145143947148614313114990041 108857960361460734836242531)
        ·
          refine ⟨163286940542191102254363797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108857960361460734836242531 163286940542191102254363797)
          ·
            refine ⟨7654075337915207918173303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 163286940542191102254363797 7654075337915207918173303)
            ·
              refine ⟨11481113006872811877259955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7654075337915207918173303 11481113006872811877259955)
              ·
                refine ⟨17221669510309217815889933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11481113006872811877259955 17221669510309217815889933)
                ·
                  refine ⟨6458126066365956680958725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17221669510309217815889933 6458126066365956680958725)
                  ·
                    refine ⟨1210898637443616877679761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6458126066365956680958725 1210898637443616877679761)
                    ·
                      rfl

theorem cell23_7074650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 1, 1, 3, 4].length) (baseStart_7074650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7074650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7074650 prefixEnd_7074650 := by exact prefixLift 7074650
  have htrace : WordTrace (prefixWord ++ tailWord_7074650) baseStart_7074650 baseEnd_7074650 := by
    simpa [prefixWord, tailWord_7074650, baseEnd_7074650] using wordTrace_append hprefix tailTrace_7074650
  have hstable : (prefixWord ++ tailWord_7074650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7074650).length < 2 ^ (prefixWord ++ tailWord_7074650).sum := by decide
  have hdescent : baseEnd_7074650 < baseStart_7074650 := by decide
  rcases family_descends (prefixWord ++ tailWord_7074650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7074663 : List Nat := [1, 1, 5, 1, 2, 3, 1, 3, 6]
def baseStart_7074663 : Nat := 118140960795 + 7074663 * 2 ^ 59
def prefixEnd_7074663 : Nat := 4983230072969 + 3 ^ 40 * 7074663 * 2
def baseEnd_7074663 : Nat := 403633620842151009130747

theorem tailTrace_7074663 : CollatzResearch.WordTrace tailWord_7074663 prefixEnd_7074663 403633620842151009130747 := by
  unfold tailWord_7074663
  simp only [CollatzResearch.WordTrace]
  refine ⟨258034157968711682091316643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172022771979141121394211095 258034157968711682091316643)
  ·
    refine ⟨387051236953067523136974965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258034157968711682091316643 387051236953067523136974965)
    ·
      refine ⟨36286053464350080294091403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 387051236953067523136974965 36286053464350080294091403)
      ·
        refine ⟨54429080196525120441137105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36286053464350080294091403 54429080196525120441137105)
        ·
          refine ⟨40821810147393840330852829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54429080196525120441137105 40821810147393840330852829)
          ·
            refine ⟨15308178805272690124069811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40821810147393840330852829 15308178805272690124069811)
            ·
              refine ⟨22962268207909035186104717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15308178805272690124069811 22962268207909035186104717)
              ·
                refine ⟨8610850577965888194789269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22962268207909035186104717 8610850577965888194789269)
                ·
                  refine ⟨403633620842151009130747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8610850577965888194789269 403633620842151009130747)
                  ·
                    rfl

theorem cell23_7074663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 3, 6].length) (baseStart_7074663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7074663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7074663 prefixEnd_7074663 := by exact prefixLift 7074663
  have htrace : WordTrace (prefixWord ++ tailWord_7074663) baseStart_7074663 baseEnd_7074663 := by
    simpa [prefixWord, tailWord_7074663, baseEnd_7074663] using wordTrace_append hprefix tailTrace_7074663
  have hstable : (prefixWord ++ tailWord_7074663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7074663).length < 2 ^ (prefixWord ++ tailWord_7074663).sum := by decide
  have hdescent : baseEnd_7074663 < baseStart_7074663 := by decide
  rcases family_descends (prefixWord ++ tailWord_7074663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7074683 : List Nat := [1, 1, 1, 1, 1, 5, 2, 3, 1, 5, 2]
def baseStart_7074683 : Nat := 118140960795 + 7074683 * 2 ^ 59
def prefixEnd_7074683 : Nat := 4983230072969 + 3 ^ 40 * 7074683 * 2
def baseEnd_7074683 : Nat := 3632712857192449003926631

theorem tailTrace_7074683 : CollatzResearch.WordTrace tailWord_7074683 prefixEnd_7074683 3632712857192449003926631 := by
  unfold tailWord_7074683
  simp only [CollatzResearch.WordTrace]
  refine ⟨258034887428639225507044703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172023258285759483671363135 258034887428639225507044703)
  ·
    refine ⟨387052331142958838260567055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258034887428639225507044703 387052331142958838260567055)
    ·
      refine ⟨580578496714438257390850583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 387052331142958838260567055 580578496714438257390850583)
      ·
        refine ⟨870867745071657386086275875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 580578496714438257390850583 870867745071657386086275875)
        ·
          refine ⟨1306301617607486079129413813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 870867745071657386086275875 1306301617607486079129413813)
          ·
            refine ⟨122465776650701819918382545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1306301617607486079129413813 122465776650701819918382545)
            ·
              refine ⟨91849332488026364938786909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122465776650701819918382545 91849332488026364938786909)
              ·
                refine ⟨34443499683009886852045091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91849332488026364938786909 34443499683009886852045091)
                ·
                  refine ⟨51665249524514830278067637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34443499683009886852045091 51665249524514830278067637)
                  ·
                    refine ⟨4843617142923265338568841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51665249524514830278067637 4843617142923265338568841)
                    ·
                      refine ⟨3632712857192449003926631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4843617142923265338568841 3632712857192449003926631)
                      ·
                        rfl

theorem cell23_7074683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 3, 1, 5, 2].length) (baseStart_7074683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7074683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7074683 prefixEnd_7074683 := by exact prefixLift 7074683
  have htrace : WordTrace (prefixWord ++ tailWord_7074683) baseStart_7074683 baseEnd_7074683 := by
    simpa [prefixWord, tailWord_7074683, baseEnd_7074683] using wordTrace_append hprefix tailTrace_7074683
  have hstable : (prefixWord ++ tailWord_7074683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7074683).length < 2 ^ (prefixWord ++ tailWord_7074683).sum := by decide
  have hdescent : baseEnd_7074683 < baseStart_7074683 := by decide
  rcases family_descends (prefixWord ++ tailWord_7074683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7074700 : List Nat := [2, 2, 1, 2, 1, 2, 4, 2, 2, 3, 2]
def baseStart_7074700 : Nat := 118140960795 + 7074700 * 2 ^ 59
def prefixEnd_7074700 : Nat := 4983230072969 + 3 ^ 40 * 7074700 * 2
def baseEnd_7074700 : Nat := 3632721586363575437414053

theorem tailTrace_7074700 : CollatzResearch.WordTrace tailWord_7074700 prefixEnd_7074700 3632721586363575437414053 := by
  unfold tailWord_7074700
  simp only [CollatzResearch.WordTrace]
  refine ⟨129017753734788818705206777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172023671646385091606942369 129017753734788818705206777)
  ·
    refine ⟨96763315301091614028905083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129017753734788818705206777 96763315301091614028905083)
    ·
      refine ⟨145144972951637421043357625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96763315301091614028905083 145144972951637421043357625)
      ·
        refine ⟨108858729713728065782518219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145144972951637421043357625 108858729713728065782518219)
        ·
          refine ⟨163288094570592098673777329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108858729713728065782518219 163288094570592098673777329)
          ·
            refine ⟨122466070927944074005332997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163288094570592098673777329 122466070927944074005332997)
            ·
              refine ⟨22962388298989513875999937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 122466070927944074005332997 22962388298989513875999937)
              ·
                refine ⟨17221791224242135406999953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22962388298989513875999937 17221791224242135406999953)
                ·
                  refine ⟨12916343418181601555249965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17221791224242135406999953 12916343418181601555249965)
                  ·
                    refine ⟨4843628781818100583218737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12916343418181601555249965 4843628781818100583218737)
                    ·
                      refine ⟨3632721586363575437414053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4843628781818100583218737 3632721586363575437414053)
                      ·
                        rfl

theorem cell23_7074700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 2, 2, 3, 2].length) (baseStart_7074700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7074700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7074700 prefixEnd_7074700 := by exact prefixLift 7074700
  have htrace : WordTrace (prefixWord ++ tailWord_7074700) baseStart_7074700 baseEnd_7074700 := by
    simpa [prefixWord, tailWord_7074700, baseEnd_7074700] using wordTrace_append hprefix tailTrace_7074700
  have hstable : (prefixWord ++ tailWord_7074700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7074700).length < 2 ^ (prefixWord ++ tailWord_7074700).sum := by decide
  have hdescent : baseEnd_7074700 < baseStart_7074700 := by decide
  rcases family_descends (prefixWord ++ tailWord_7074700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7074713 : List Nat := [1, 2, 1, 2, 1, 3, 1, 2, 2, 6, 2]
def baseStart_7074713 : Nat := 118140960795 + 7074713 * 2 ^ 59
def prefixEnd_7074713 : Nat := 4983230072969 + 3 ^ 40 * 7074713 * 2
def baseEnd_7074713 : Nat := 3632728261612083886551493

theorem tailTrace_7074713 : CollatzResearch.WordTrace tailWord_7074713 prefixEnd_7074713 3632728261612083886551493 := by
  unfold tailWord_7074713
  simp only [CollatzResearch.WordTrace]
  refine ⟨258035981618530540630636793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172023987745687027087091195 258035981618530540630636793)
  ·
    refine ⟨193526986213897905472977595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258035981618530540630636793 193526986213897905472977595)
    ·
      refine ⟨290290479320846858209466393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193526986213897905472977595 290290479320846858209466393)
      ·
        refine ⟨217717859490635143657099795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 290290479320846858209466393 217717859490635143657099795)
        ·
          refine ⟨326576789235952715485649693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217717859490635143657099795 326576789235952715485649693)
          ·
            refine ⟨122466295963482268307118635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 326576789235952715485649693 122466295963482268307118635)
            ·
              refine ⟨183699443945223402460677953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122466295963482268307118635 183699443945223402460677953)
              ·
                refine ⟨137774582958917551845508465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 183699443945223402460677953 137774582958917551845508465)
                ·
                  refine ⟨103330937219188163884131349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 137774582958917551845508465 103330937219188163884131349)
                  ·
                    refine ⟨4843637682149445182068657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 103330937219188163884131349 4843637682149445182068657)
                    ·
                      refine ⟨3632728261612083886551493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4843637682149445182068657 3632728261612083886551493)
                      ·
                        rfl

theorem cell23_7074713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 2, 2, 6, 2].length) (baseStart_7074713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7074713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7074713 prefixEnd_7074713 := by exact prefixLift 7074713
  have htrace : WordTrace (prefixWord ++ tailWord_7074713) baseStart_7074713 baseEnd_7074713 := by
    simpa [prefixWord, tailWord_7074713, baseEnd_7074713] using wordTrace_append hprefix tailTrace_7074713
  have hstable : (prefixWord ++ tailWord_7074713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7074713).length < 2 ^ (prefixWord ++ tailWord_7074713).sum := by decide
  have hdescent : baseEnd_7074713 < baseStart_7074713 := by decide
  rcases family_descends (prefixWord ++ tailWord_7074713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7074743 : List Nat := [1, 1, 3, 1, 3, 1, 4, 2, 1, 2, 4]
def baseStart_7074743 : Nat := 118140960795 + 7074743 * 2 ^ 59
def prefixEnd_7074743 : Nat := 4983230072969 + 3 ^ 40 * 7074743 * 2
def baseEnd_7074743 : Nat := 3632743666031718769176355

theorem tailTrace_7074743 : CollatzResearch.WordTrace tailWord_7074743 prefixEnd_7074743 3632743666031718769176355 := by
  unfold tailWord_7074743
  simp only [CollatzResearch.WordTrace]
  refine ⟨258037075808421855754228883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172024717205614570502819255 258037075808421855754228883)
  ·
    refine ⟨387055613712632783631343325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258037075808421855754228883 387055613712632783631343325)
    ·
      refine ⟨145145855142237293861753747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 387055613712632783631343325 145145855142237293861753747)
      ·
        refine ⟨217718782713355940792630621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145145855142237293861753747 217718782713355940792630621)
        ·
          refine ⟨81644543517508477797236483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 217718782713355940792630621 81644543517508477797236483)
          ·
            refine ⟨122466815276262716695854725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81644543517508477797236483 122466815276262716695854725)
            ·
              refine ⟨22962527864299259380472761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 122466815276262716695854725 22962527864299259380472761)
              ·
                refine ⟨17221895898224444535354571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22962527864299259380472761 17221895898224444535354571)
                ·
                  refine ⟨25832843847336666803031857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17221895898224444535354571 25832843847336666803031857)
                  ·
                    refine ⟨19374632885502500102273893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25832843847336666803031857 19374632885502500102273893)
                    ·
                      refine ⟨3632743666031718769176355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19374632885502500102273893 3632743666031718769176355)
                      ·
                        rfl

theorem cell23_7074743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 2, 1, 2, 4].length) (baseStart_7074743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7074743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7074743 prefixEnd_7074743 := by exact prefixLift 7074743
  have htrace : WordTrace (prefixWord ++ tailWord_7074743) baseStart_7074743 baseEnd_7074743 := by
    simpa [prefixWord, tailWord_7074743, baseEnd_7074743] using wordTrace_append hprefix tailTrace_7074743
  have hstable : (prefixWord ++ tailWord_7074743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7074743).length < 2 ^ (prefixWord ++ tailWord_7074743).sum := by decide
  have hdescent : baseEnd_7074743 < baseStart_7074743 := by decide
  rcases family_descends (prefixWord ++ tailWord_7074743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7074764 : List Nat := [2, 2, 1, 4, 1, 1, 1, 6, 1, 2, 2]
def baseStart_7074764 : Nat := 118140960795 + 7074764 * 2 ^ 59
def prefixEnd_7074764 : Nat := 4983230072969 + 3 ^ 40 * 7074764 * 2
def baseEnd_7074764 : Nat := 3632754449125463187013759

theorem tailTrace_7074764 : CollatzResearch.WordTrace tailWord_7074764 prefixEnd_7074764 3632754449125463187013759 := by
  unfold tailWord_7074764
  simp only [CollatzResearch.WordTrace]
  refine ⟨129018920870672888170371673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172025227827563850893828897 129018920870672888170371673)
  ·
    refine ⟨96764190653004666127778755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129018920870672888170371673 96764190653004666127778755)
    ·
      refine ⟨145146285979506999191668133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96764190653004666127778755 145146285979506999191668133)
      ·
        refine ⟨27214928621157562348437775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 145146285979506999191668133 27214928621157562348437775)
        ·
          refine ⟨40822392931736343522656663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27214928621157562348437775 40822392931736343522656663)
          ·
            refine ⟨61233589397604515283984995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40822392931736343522656663 61233589397604515283984995)
            ·
              refine ⟨91850384096406772925977493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61233589397604515283984995 91850384096406772925977493)
              ·
                refine ⟨4305486754519067480905195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 91850384096406772925977493 4305486754519067480905195)
                ·
                  refine ⟨6458230131778601221357793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4305486754519067480905195 6458230131778601221357793)
                  ·
                    refine ⟨4843672598833950916018345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6458230131778601221357793 4843672598833950916018345)
                    ·
                      refine ⟨3632754449125463187013759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4843672598833950916018345 3632754449125463187013759)
                      ·
                        rfl

theorem cell23_7074764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 6, 1, 2, 2].length) (baseStart_7074764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7074764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7074764 prefixEnd_7074764 := by exact prefixLift 7074764
  have htrace : WordTrace (prefixWord ++ tailWord_7074764) baseStart_7074764 baseEnd_7074764 := by
    simpa [prefixWord, tailWord_7074764, baseEnd_7074764] using wordTrace_append hprefix tailTrace_7074764
  have hstable : (prefixWord ++ tailWord_7074764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7074764).length < 2 ^ (prefixWord ++ tailWord_7074764).sum := by decide
  have hdescent : baseEnd_7074764 < baseStart_7074764 := by decide
  rcases family_descends (prefixWord ++ tailWord_7074764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7074798 : List Nat := [4, 1, 2, 1, 4, 2, 1, 3, 1, 2, 2]
def baseStart_7074798 : Nat := 118140960795 + 7074798 * 2 ^ 59
def prefixEnd_7074798 : Nat := 4983230072969 + 3 ^ 40 * 7074798 * 2
def baseEnd_7074798 : Nat := 3632771907467716053988603

theorem tailTrace_7074798 : CollatzResearch.WordTrace tailWord_7074798 prefixEnd_7074798 3632771907467716053988603 := by
  unfold tailWord_7074798
  simp only [CollatzResearch.WordTrace]
  refine ⟨32254885227902825018435131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172026054548815066764987365 32254885227902825018435131)
  ·
    refine ⟨48382327841854237527652697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32254885227902825018435131 48382327841854237527652697)
    ·
      refine ⟨36286745881390678145739523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48382327841854237527652697 36286745881390678145739523)
      ·
        refine ⟨54430118822086017218609285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36286745881390678145739523 54430118822086017218609285)
        ·
          refine ⟨10205647279141128228489241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54430118822086017218609285 10205647279141128228489241)
          ·
            refine ⟨7654235459355846171366931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10205647279141128228489241 7654235459355846171366931)
            ·
              refine ⟨11481353189033769257050397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7654235459355846171366931 11481353189033769257050397)
              ·
                refine ⟨4305507445887663471393899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11481353189033769257050397 4305507445887663471393899)
                ·
                  refine ⟨6458261168831495207090849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4305507445887663471393899 6458261168831495207090849)
                  ·
                    refine ⟨4843695876623621405318137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6458261168831495207090849 4843695876623621405318137)
                    ·
                      refine ⟨3632771907467716053988603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4843695876623621405318137 3632771907467716053988603)
                      ·
                        rfl

theorem cell23_7074798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 1, 3, 1, 2, 2].length) (baseStart_7074798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7074798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7074798 prefixEnd_7074798 := by exact prefixLift 7074798
  have htrace : WordTrace (prefixWord ++ tailWord_7074798) baseStart_7074798 baseEnd_7074798 := by
    simpa [prefixWord, tailWord_7074798, baseEnd_7074798] using wordTrace_append hprefix tailTrace_7074798
  have hstable : (prefixWord ++ tailWord_7074798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7074798).length < 2 ^ (prefixWord ++ tailWord_7074798).sum := by decide
  have hdescent : baseEnd_7074798 < baseStart_7074798 := by decide
  rcases family_descends (prefixWord ++ tailWord_7074798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7074823 : List Nat := [1, 1, 4, 3, 1, 1, 1, 2, 1, 3, 5]
def baseStart_7074823 : Nat := 118140960795 + 7074823 * 2 ^ 59
def prefixEnd_7074823 : Nat := 4983230072969 + 3 ^ 40 * 7074823 * 2
def baseEnd_7074823 : Nat := 3632784744484078456175987

theorem tailTrace_7074823 : CollatzResearch.WordTrace tailWord_7074823 prefixEnd_7074823 3632784744484078456175987 := by
  unfold tailWord_7074823
  simp only [CollatzResearch.WordTrace]
  refine ⟨258039993648132029417141123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172026662432088019611427415 258039993648132029417141123)
  ·
    refine ⟨387059990472198044125711685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258039993648132029417141123 387059990472198044125711685)
    ·
      refine ⟨72573748213537133273570941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 387059990472198044125711685 72573748213537133273570941)
      ·
        refine ⟨27215155580076424977589103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72573748213537133273570941 27215155580076424977589103)
        ·
          refine ⟨40822733370114637466383655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27215155580076424977589103 40822733370114637466383655)
          ·
            refine ⟨61234100055171956199575483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40822733370114637466383655 61234100055171956199575483)
            ·
              refine ⟨91851150082757934299363225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61234100055171956199575483 91851150082757934299363225)
              ·
                refine ⟨68888362562068450724522419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91851150082757934299363225 68888362562068450724522419)
                ·
                  refine ⟨103332543843102676086783629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68888362562068450724522419 103332543843102676086783629)
                  ·
                    refine ⟨38749703941163503532543861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 103332543843102676086783629 38749703941163503532543861)
                    ·
                      refine ⟨3632784744484078456175987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38749703941163503532543861 3632784744484078456175987)
                      ·
                        rfl

theorem cell23_7074823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_7074823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7074823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7074823 prefixEnd_7074823 := by exact prefixLift 7074823
  have htrace : WordTrace (prefixWord ++ tailWord_7074823) baseStart_7074823 baseEnd_7074823 := by
    simpa [prefixWord, tailWord_7074823, baseEnd_7074823] using wordTrace_append hprefix tailTrace_7074823
  have hstable : (prefixWord ++ tailWord_7074823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7074823).length < 2 ^ (prefixWord ++ tailWord_7074823).sum := by decide
  have hdescent : baseEnd_7074823 < baseStart_7074823 := by decide
  rcases family_descends (prefixWord ++ tailWord_7074823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7074833 : List Nat := [1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 4]
def baseStart_7074833 : Nat := 118140960795 + 7074833 * 2 ^ 59
def prefixEnd_7074833 : Nat := 4983230072969 + 3 ^ 40 * 7074833 * 2
def baseEnd_7074833 : Nat := 3632789879290623417050941

theorem tailTrace_7074833 : CollatzResearch.WordTrace tailWord_7074833 prefixEnd_7074833 3632789879290623417050941 := by
  unfold tailWord_7074833
  simp only [CollatzResearch.WordTrace]
  refine ⟨258040358378095801125005153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172026905585397200750003435 258040358378095801125005153)
  ·
    refine ⟨193530268783571850843753865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258040358378095801125005153 193530268783571850843753865)
    ·
      refine ⟨145147701587678888132815399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193530268783571850843753865 145147701587678888132815399)
      ·
        refine ⟨217721552381518332199223099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145147701587678888132815399 217721552381518332199223099)
        ·
          refine ⟨326582328572277498298834649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217721552381518332199223099 326582328572277498298834649)
          ·
            refine ⟨244936746429208123724125987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 326582328572277498298834649 244936746429208123724125987)
            ·
              refine ⟨367405119643812185586188981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 244936746429208123724125987 367405119643812185586188981)
              ·
                refine ⟨34444229966607392398705217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 367405119643812185586188981 34444229966607392398705217)
                ·
                  refine ⟨25833172474955544299028913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34444229966607392398705217 25833172474955544299028913)
                  ·
                    refine ⟨19374879356216658224271685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25833172474955544299028913 19374879356216658224271685)
                    ·
                      refine ⟨3632789879290623417050941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19374879356216658224271685 3632789879290623417050941)
                      ·
                        rfl

theorem cell23_7074833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 4].length) (baseStart_7074833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7074833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7074833 prefixEnd_7074833 := by exact prefixLift 7074833
  have htrace : WordTrace (prefixWord ++ tailWord_7074833) baseStart_7074833 baseEnd_7074833 := by
    simpa [prefixWord, tailWord_7074833, baseEnd_7074833] using wordTrace_append hprefix tailTrace_7074833
  have hstable : (prefixWord ++ tailWord_7074833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7074833).length < 2 ^ (prefixWord ++ tailWord_7074833).sum := by decide
  have hdescent : baseEnd_7074833 < baseStart_7074833 := by decide
  rcases family_descends (prefixWord ++ tailWord_7074833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7074860 : List Nat := [2, 2, 1, 1, 1, 2, 4, 5, 5]
def baseStart_7074860 : Nat := 118140960795 + 7074860 * 2 ^ 59
def prefixEnd_7074860 : Nat := 4983230072969 + 3 ^ 40 * 7074860 * 2
def baseEnd_7074860 : Nat := 403644860363143867934813

theorem tailTrace_7074860 : CollatzResearch.WordTrace tailWord_7074860 prefixEnd_7074860 403644860363143867934813 := by
  unfold tailWord_7074860
  simp only [CollatzResearch.WordTrace]
  refine ⟨129020671574498992368119017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172027562099331989824158689 129020671574498992368119017)
  ·
    refine ⟨96765503680874244276089263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129020671574498992368119017 96765503680874244276089263)
    ·
      refine ⟨145148255521311366414133895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96765503680874244276089263 145148255521311366414133895)
      ·
        refine ⟨217722383281967049621200843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145148255521311366414133895 217722383281967049621200843)
        ·
          refine ⟨326583574922950574431801265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217722383281967049621200843 326583574922950574431801265)
          ·
            refine ⟨244937681192212930823850949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 326583574922950574431801265 244937681192212930823850949)
            ·
              refine ⟨45925815223539924529472053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 244937681192212930823850949 45925815223539924529472053)
              ·
                refine ⟨4305545177206867924638005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45925815223539924529472053 4305545177206867924638005)
                ·
                  refine ⟨403644860363143867934813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4305545177206867924638005 403644860363143867934813)
                  ·
                    rfl

theorem cell23_7074860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 5, 5].length) (baseStart_7074860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7074860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7074860 prefixEnd_7074860 := by exact prefixLift 7074860
  have htrace : WordTrace (prefixWord ++ tailWord_7074860) baseStart_7074860 baseEnd_7074860 := by
    simpa [prefixWord, tailWord_7074860, baseEnd_7074860] using wordTrace_append hprefix tailTrace_7074860
  have hstable : (prefixWord ++ tailWord_7074860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7074860).length < 2 ^ (prefixWord ++ tailWord_7074860).sum := by decide
  have hdescent : baseEnd_7074860 < baseStart_7074860 := by decide
  rcases family_descends (prefixWord ++ tailWord_7074860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7074877 : List Nat := [1, 4, 1, 3, 1, 3, 1, 4, 5]
def baseStart_7074877 : Nat := 118140960795 + 7074877 * 2 ^ 59
def prefixEnd_7074877 : Nat := 4983230072969 + 3 ^ 40 * 7074877 * 2
def baseEnd_7074877 : Nat := 403645830271046804988971

theorem tailTrace_7074877 : CollatzResearch.WordTrace tailWord_7074877 prefixEnd_7074877 403645830271046804988971 := by
  unfold tailWord_7074877
  simp only [CollatzResearch.WordTrace]
  refine ⟨258041963189936396639606885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172027975459957597759737923 258041963189936396639606885)
  ·
    refine ⟨48382868098113074369926291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 258041963189936396639606885 48382868098113074369926291)
    ·
      refine ⟨72574302147169611554889437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48382868098113074369926291 72574302147169611554889437)
      ·
        refine ⟨27215363305188604333083539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72574302147169611554889437 27215363305188604333083539)
        ·
          refine ⟨40823044957782906499625309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27215363305188604333083539 40823044957782906499625309)
          ·
            refine ⟨15308641859168589937359491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40823044957782906499625309 15308641859168589937359491)
            ·
              refine ⟨22962962788752884906039237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15308641859168589937359491 22962962788752884906039237)
              ·
                refine ⟨4305555522891165919882357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22962962788752884906039237 4305555522891165919882357)
                ·
                  refine ⟨403645830271046804988971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4305555522891165919882357 403645830271046804988971)
                  ·
                    rfl

theorem cell23_7074877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 4, 5].length) (baseStart_7074877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7074877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7074877 prefixEnd_7074877 := by exact prefixLift 7074877
  have htrace : WordTrace (prefixWord ++ tailWord_7074877) baseStart_7074877 baseEnd_7074877 := by
    simpa [prefixWord, tailWord_7074877, baseEnd_7074877] using wordTrace_append hprefix tailTrace_7074877
  have hstable : (prefixWord ++ tailWord_7074877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7074877).length < 2 ^ (prefixWord ++ tailWord_7074877).sum := by decide
  have hdescent : baseEnd_7074877 < baseStart_7074877 := by decide
  rcases family_descends (prefixWord ++ tailWord_7074877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7074880 : List Nat := [2, 1, 1, 2, 2, 3, 1, 1, 1, 7, 2]
def baseStart_7074880 : Nat := 118140960795 + 7074880 * 2 ^ 59
def prefixEnd_7074880 : Nat := 4983230072969 + 3 ^ 40 * 7074880 * 2
def baseEnd_7074880 : Nat := 3632814012881384733163225

theorem tailTrace_7074880 : CollatzResearch.WordTrace tailWord_7074880 prefixEnd_7074880 3632814012881384733163225 := by
  unfold tailWord_7074880
  simp only [CollatzResearch.WordTrace]
  refine ⟨129021036304462764075983047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172028048405950352101310729 129021036304462764075983047)
  ·
    refine ⟨193531554456694146113974571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129021036304462764075983047 193531554456694146113974571)
    ·
      refine ⟨290297331685041219170961857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193531554456694146113974571 290297331685041219170961857)
      ·
        refine ⟨217722998763780914378221393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 290297331685041219170961857 217722998763780914378221393)
        ·
          refine ⟨163292249072835685783666045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217722998763780914378221393 163292249072835685783666045)
          ·
            refine ⟨61234593402313382168874767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 163292249072835685783666045 61234593402313382168874767)
            ·
              refine ⟨91851890103470073253312151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61234593402313382168874767 91851890103470073253312151)
              ·
                refine ⟨137777835155205109879968227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91851890103470073253312151 137777835155205109879968227)
                ·
                  refine ⟨206666752732807664819952341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 137777835155205109879968227 206666752732807664819952341)
                  ·
                    refine ⟨4843752017175179644217633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 206666752732807664819952341 4843752017175179644217633)
                    ·
                      refine ⟨3632814012881384733163225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4843752017175179644217633 3632814012881384733163225)
                      ·
                        rfl

theorem cell23_7074880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 1, 1, 7, 2].length) (baseStart_7074880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7074880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7074880 prefixEnd_7074880 := by exact prefixLift 7074880
  have htrace : WordTrace (prefixWord ++ tailWord_7074880) baseStart_7074880 baseEnd_7074880 := by
    simpa [prefixWord, tailWord_7074880, baseEnd_7074880] using wordTrace_append hprefix tailTrace_7074880
  have hstable : (prefixWord ++ tailWord_7074880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7074880).length < 2 ^ (prefixWord ++ tailWord_7074880).sum := by decide
  have hdescent : baseEnd_7074880 < baseStart_7074880 := by decide
  rcases family_descends (prefixWord ++ tailWord_7074880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7074883 : List Nat := [1, 1, 1, 3, 1, 2, 3, 3, 1, 2, 5]
def baseStart_7074883 : Nat := 118140960795 + 7074883 * 2 ^ 59
def prefixEnd_7074883 : Nat := 4983230072969 + 3 ^ 40 * 7074883 * 2
def baseEnd_7074883 : Nat := 3632815553323348221425711

theorem tailTrace_7074883 : CollatzResearch.WordTrace tailWord_7074883 prefixEnd_7074883 3632815553323348221425711 := by
  unfold tailWord_7074883
  simp only [CollatzResearch.WordTrace]
  refine ⟨258042182027914659664325303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172028121351943106442883535 258042182027914659664325303)
  ·
    refine ⟨387063273041871989496487955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258042182027914659664325303 387063273041871989496487955)
    ·
      refine ⟨580594909562807984244731933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 387063273041871989496487955 580594909562807984244731933)
      ·
        refine ⟨217723091086052994091774475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 580594909562807984244731933 217723091086052994091774475)
        ·
          refine ⟨326584636629079491137661713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217723091086052994091774475 326584636629079491137661713)
          ·
            refine ⟨244938477471809618353246285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 326584636629079491137661713 244938477471809618353246285)
            ·
              refine ⟨91851929051928606882467357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 244938477471809618353246285 91851929051928606882467357)
              ·
                refine ⟨34444473394473227580925259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91851929051928606882467357 34444473394473227580925259)
                ·
                  refine ⟨51666710091709841371387889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34444473394473227580925259 51666710091709841371387889)
                  ·
                    refine ⟨38750032568782381028540917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51666710091709841371387889 38750032568782381028540917)
                    ·
                      refine ⟨3632815553323348221425711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38750032568782381028540917 3632815553323348221425711)
                      ·
                        rfl

theorem cell23_7074883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 3, 1, 2, 5].length) (baseStart_7074883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7074883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7074883 prefixEnd_7074883 := by exact prefixLift 7074883
  have htrace : WordTrace (prefixWord ++ tailWord_7074883) baseStart_7074883 baseEnd_7074883 := by
    simpa [prefixWord, tailWord_7074883, baseEnd_7074883] using wordTrace_append hprefix tailTrace_7074883
  have hstable : (prefixWord ++ tailWord_7074883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7074883).length < 2 ^ (prefixWord ++ tailWord_7074883).sum := by decide
  have hdescent : baseEnd_7074883 < baseStart_7074883 := by decide
  rcases family_descends (prefixWord ++ tailWord_7074883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7074923 : List Nat := [1, 1, 1, 1, 2, 2, 1, 1, 3, 6, 4]
def baseStart_7074923 : Nat := 118140960795 + 7074923 * 2 ^ 59
def prefixEnd_7074923 : Nat := 4983230072969 + 3 ^ 40 * 7074923 * 2
def baseEnd_7074923 : Nat := 3632836092549528064925527

theorem tailTrace_7074923 : CollatzResearch.WordTrace tailWord_7074923 prefixEnd_7074923 3632836092549528064925527 := by
  unfold tailWord_7074923
  simp only [CollatzResearch.WordTrace]
  refine ⟨258043640947769746495781423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172029093965179830997187615 258043640947769746495781423)
  ·
    refine ⟨387065461421654619743672135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258043640947769746495781423 387065461421654619743672135)
    ·
      refine ⟨580598192132481929615508203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 387065461421654619743672135 580598192132481929615508203)
      ·
        refine ⟨870897288198722894423262305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 580598192132481929615508203 870897288198722894423262305)
        ·
          refine ⟨653172966149042170817446729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 870897288198722894423262305 653172966149042170817446729)
          ·
            refine ⟨489879724611781628113085047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 653172966149042170817446729 489879724611781628113085047)
            ·
              refine ⟨734819586917672442169627571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 489879724611781628113085047 734819586917672442169627571)
              ·
                refine ⟨1102229380376508663254441357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 734819586917672442169627571 1102229380376508663254441357)
                ·
                  refine ⟨413336017641190748720415509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1102229380376508663254441357 413336017641190748720415509)
                  ·
                    refine ⟨19375125826930816346269477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 413336017641190748720415509 19375125826930816346269477)
                    ·
                      refine ⟨3632836092549528064925527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19375125826930816346269477 3632836092549528064925527)
                      ·
                        rfl

theorem cell23_7074923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 6, 4].length) (baseStart_7074923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7074923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7074923 prefixEnd_7074923 := by exact prefixLift 7074923
  have htrace : WordTrace (prefixWord ++ tailWord_7074923) baseStart_7074923 baseEnd_7074923 := by
    simpa [prefixWord, tailWord_7074923, baseEnd_7074923] using wordTrace_append hprefix tailTrace_7074923
  have hstable : (prefixWord ++ tailWord_7074923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7074923).length < 2 ^ (prefixWord ++ tailWord_7074923).sum := by decide
  have hdescent : baseEnd_7074923 < baseStart_7074923 := by decide
  rcases family_descends (prefixWord ++ tailWord_7074923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7074994 : List Nat := [3, 2, 1, 1, 1, 4, 3, 1, 3, 1, 3]
def baseStart_7074994 : Nat := 118140960795 + 7074994 * 2 ^ 59
def prefixEnd_7074994 : Nat := 4983230072969 + 3 ^ 40 * 7074994 * 2
def baseEnd_7074994 : Nat := 3632872549675997287137701

theorem tailTrace_7074994 : CollatzResearch.WordTrace tailWord_7074994 prefixEnd_7074994 3632872549675997287137701 := by
  unfold tailWord_7074994
  simp only [CollatzResearch.WordTrace]
  refine ⟨64511557632628131405404009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172030820353675017081077357 64511557632628131405404009)
  ·
    refine ⟨48383668224471098554053007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64511557632628131405404009 48383668224471098554053007)
    ·
      refine ⟨72575502336706647831079511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48383668224471098554053007 72575502336706647831079511)
      ·
        refine ⟨108863253505059971746619267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72575502336706647831079511 108863253505059971746619267)
        ·
          refine ⟨163294880257589957619928901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108863253505059971746619267 163294880257589957619928901)
          ·
            refine ⟨30617790048298117053736669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 163294880257589957619928901 30617790048298117053736669)
            ·
              refine ⟨11481671268111793895151251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30617790048298117053736669 11481671268111793895151251)
              ·
                refine ⟨17222506902167690842726877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11481671268111793895151251 17222506902167690842726877)
                ·
                  refine ⟨6458440088312884066022579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17222506902167690842726877 6458440088312884066022579)
                  ·
                    refine ⟨9687660132469326099033869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6458440088312884066022579 9687660132469326099033869)
                    ·
                      refine ⟨3632872549675997287137701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9687660132469326099033869 3632872549675997287137701)
                      ·
                        rfl

theorem cell23_7074994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 3, 1, 3, 1, 3].length) (baseStart_7074994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7074994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7074994 prefixEnd_7074994 := by exact prefixLift 7074994
  have htrace : WordTrace (prefixWord ++ tailWord_7074994) baseStart_7074994 baseEnd_7074994 := by
    simpa [prefixWord, tailWord_7074994, baseEnd_7074994] using wordTrace_append hprefix tailTrace_7074994
  have hstable : (prefixWord ++ tailWord_7074994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7074994).length < 2 ^ (prefixWord ++ tailWord_7074994).sum := by decide
  have hdescent : baseEnd_7074994 < baseStart_7074994 := by decide
  rcases family_descends (prefixWord ++ tailWord_7074994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7075045 : List Nat := [1, 3, 1, 4, 3, 2, 2, 2, 1, 1, 3]
def baseStart_7075045 : Nat := 118140960795 + 7075045 * 2 ^ 59
def prefixEnd_7075045 : Nat := 4983230072969 + 3 ^ 40 * 7075045 * 2
def baseEnd_7075045 : Nat := 3632898737189376587599967

theorem tailTrace_7075045 : CollatzResearch.WordTrace tailWord_7075045 prefixEnd_7075045 3632898737189376587599967 := by
  unfold tailWord_7075045
  simp only [CollatzResearch.WordTrace]
  refine ⟨258048090653327761331722589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172032060435551840887815059 258048090653327761331722589)
  ·
    refine ⟨96768033994997910499395971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 258048090653327761331722589 96768033994997910499395971)
    ·
      refine ⟨145152050992496865749093957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96768033994997910499395971 145152050992496865749093957)
      ·
        refine ⟨27216009561093162327955117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 145152050992496865749093957 27216009561093162327955117)
        ·
          refine ⟨10206003585409935872983169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27216009561093162327955117 10206003585409935872983169)
          ·
            refine ⟨7654502689057451904737377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10206003585409935872983169 7654502689057451904737377)
            ·
              refine ⟨5740877016793088928553033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7654502689057451904737377 5740877016793088928553033)
              ·
                refine ⟨4305657762594816696414775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5740877016793088928553033 4305657762594816696414775)
                ·
                  refine ⟨6458486643892225044622163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4305657762594816696414775 6458486643892225044622163)
                  ·
                    refine ⟨9687729965838337566933245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6458486643892225044622163 9687729965838337566933245)
                    ·
                      refine ⟨3632898737189376587599967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9687729965838337566933245 3632898737189376587599967)
                      ·
                        rfl

theorem cell23_7075045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 2, 2, 1, 1, 3].length) (baseStart_7075045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7075045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7075045 prefixEnd_7075045 := by exact prefixLift 7075045
  have htrace : WordTrace (prefixWord ++ tailWord_7075045) baseStart_7075045 baseEnd_7075045 := by
    simpa [prefixWord, tailWord_7075045, baseEnd_7075045] using wordTrace_append hprefix tailTrace_7075045
  have hstable : (prefixWord ++ tailWord_7075045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7075045).length < 2 ^ (prefixWord ++ tailWord_7075045).sum := by decide
  have hdescent : baseEnd_7075045 < baseStart_7075045 := by decide
  rcases family_descends (prefixWord ++ tailWord_7075045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7075101 : List Nat := [1, 4, 2, 3, 1, 2, 1, 1, 4, 1, 3]
def baseStart_7075101 : Nat := 118140960795 + 7075101 * 2 ^ 59
def prefixEnd_7075101 : Nat := 4983230072969 + 3 ^ 40 * 7075101 * 2
def baseEnd_7075101 : Nat := 3632927492106028368499709

theorem tailTrace_7075101 : CollatzResearch.WordTrace tailWord_7075101 prefixEnd_7075101 3632927492106028368499709 := by
  unfold tailWord_7075101
  simp only [CollatzResearch.WordTrace]
  refine ⟨258050133141124882895761157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172033422094083255263840771 258050133141124882895761157)
  ·
    refine ⟨48384399963960915542955217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 258050133141124882895761157 48384399963960915542955217)
    ·
      refine ⟨36288299972970686657216413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48384399963960915542955217 36288299972970686657216413)
      ·
        refine ⟨13608112489864007496456155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36288299972970686657216413 13608112489864007496456155)
        ·
          refine ⟨20412168734796011244684233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13608112489864007496456155 20412168734796011244684233)
          ·
            refine ⟨15309126551097008433513175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20412168734796011244684233 15309126551097008433513175)
            ·
              refine ⟨22963689826645512650269763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15309126551097008433513175 22963689826645512650269763)
              ·
                refine ⟨34445534739968268975404645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22963689826645512650269763 34445534739968268975404645)
                ·
                  refine ⟨6458537763744050432888371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34445534739968268975404645 6458537763744050432888371)
                  ·
                    refine ⟨9687806645616075649332557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6458537763744050432888371 9687806645616075649332557)
                    ·
                      refine ⟨3632927492106028368499709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9687806645616075649332557 3632927492106028368499709)
                      ·
                        rfl

theorem cell23_7075101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_7075101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7075101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7075101 prefixEnd_7075101 := by exact prefixLift 7075101
  have htrace : WordTrace (prefixWord ++ tailWord_7075101) baseStart_7075101 baseEnd_7075101 := by
    simpa [prefixWord, tailWord_7075101, baseEnd_7075101] using wordTrace_append hprefix tailTrace_7075101
  have hstable : (prefixWord ++ tailWord_7075101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7075101).length < 2 ^ (prefixWord ++ tailWord_7075101).sum := by decide
  have hdescent : baseEnd_7075101 < baseStart_7075101 := by decide
  rcases family_descends (prefixWord ++ tailWord_7075101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7075231 : List Nat := [1, 1, 2, 5, 1, 3, 1, 1, 2, 4, 2]
def baseStart_7075231 : Nat := 118140960795 + 7075231 * 2 ^ 59
def prefixEnd_7075231 : Nat := 4983230072969 + 3 ^ 40 * 7075231 * 2
def baseEnd_7075231 : Nat := 3632994244591112859874111

theorem tailTrace_7075231 : CollatzResearch.WordTrace tailWord_7075231 prefixEnd_7075231 3632994244591112859874111 := by
  unfold tailWord_7075231
  simp only [CollatzResearch.WordTrace]
  refine ⟨258054874630653915097993547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172036583087102610065329031 258054874630653915097993547)
  ·
    refine ⟨387082311945980872646990321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258054874630653915097993547 387082311945980872646990321)
    ·
      refine ⟨290311733959485654485242741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 387082311945980872646990321 290311733959485654485242741)
      ·
        refine ⟨27216725058701780107991507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 290311733959485654485242741 27216725058701780107991507)
        ·
          refine ⟨40825087588052670161987261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27216725058701780107991507 40825087588052670161987261)
          ·
            refine ⟨15309407845519751310745223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40825087588052670161987261 15309407845519751310745223)
            ·
              refine ⟨22964111768279626966117835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15309407845519751310745223 22964111768279626966117835)
              ·
                refine ⟨34446167652419440449176753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22964111768279626966117835 34446167652419440449176753)
                ·
                  refine ⟨25834625739314580336882565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34446167652419440449176753 25834625739314580336882565)
                  ·
                    refine ⟨4843992326121483813165481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25834625739314580336882565 4843992326121483813165481)
                    ·
                      refine ⟨3632994244591112859874111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4843992326121483813165481 3632994244591112859874111)
                      ·
                        rfl

theorem cell23_7075231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 1, 2, 4, 2].length) (baseStart_7075231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7075231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7075231 prefixEnd_7075231 := by exact prefixLift 7075231
  have htrace : WordTrace (prefixWord ++ tailWord_7075231) baseStart_7075231 baseEnd_7075231 := by
    simpa [prefixWord, tailWord_7075231, baseEnd_7075231] using wordTrace_append hprefix tailTrace_7075231
  have hstable : (prefixWord ++ tailWord_7075231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7075231).length < 2 ^ (prefixWord ++ tailWord_7075231).sum := by decide
  have hdescent : baseEnd_7075231 < baseStart_7075231 := by decide
  rcases family_descends (prefixWord ++ tailWord_7075231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7075301 : List Nat := [1, 3, 1, 5, 1, 1, 1, 4, 1, 5]
def baseStart_7075301 : Nat := 118140960795 + 7075301 * 2 ^ 59
def prefixEnd_7075301 : Nat := 4983230072969 + 3 ^ 40 * 7075301 * 2
def baseEnd_7075301 : Nat := 1211010062745642528666263

theorem tailTrace_7075301 : CollatzResearch.WordTrace tailWord_7075301 prefixEnd_7075301 1211010062745642528666263 := by
  unfold tailWord_7075301
  simp only [CollatzResearch.WordTrace]
  refine ⟨258057427740400317053041757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172038285160266878035361171 258057427740400317053041757)
  ·
    refine ⟨96771535402650118894890659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 258057427740400317053041757 96771535402650118894890659)
    ·
      refine ⟨145157303103975178342335989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96771535402650118894890659 145157303103975178342335989)
      ·
        refine ⟨13608497165997672969593999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 145157303103975178342335989 13608497165997672969593999)
        ·
          refine ⟨20412745748996509454390999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13608497165997672969593999 20412745748996509454390999)
          ·
            refine ⟨30619118623494764181586499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20412745748996509454390999 30619118623494764181586499)
            ·
              refine ⟨45928677935242146272379749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30619118623494764181586499 45928677935242146272379749)
              ·
                refine ⟨8611627112857902426071203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45928677935242146272379749 8611627112857902426071203)
                ·
                  refine ⟨12917440669286853639106805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8611627112857902426071203 12917440669286853639106805)
                  ·
                    refine ⟨1211010062745642528666263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12917440669286853639106805 1211010062745642528666263)
                    ·
                      rfl

theorem cell23_7075301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 4, 1, 5].length) (baseStart_7075301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7075301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7075301 prefixEnd_7075301 := by exact prefixLift 7075301
  have htrace : WordTrace (prefixWord ++ tailWord_7075301) baseStart_7075301 baseEnd_7075301 := by
    simpa [prefixWord, tailWord_7075301, baseEnd_7075301] using wordTrace_append hprefix tailTrace_7075301
  have hstable : (prefixWord ++ tailWord_7075301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7075301).length < 2 ^ (prefixWord ++ tailWord_7075301).sum := by decide
  have hdescent : baseEnd_7075301 < baseStart_7075301 := by decide
  rcases family_descends (prefixWord ++ tailWord_7075301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7075324 : List Nat := [2, 2, 2, 1, 2, 1, 3, 3, 1, 1, 5]
def baseStart_7075324 : Nat := 118140960795 + 7075324 * 2 ^ 59
def prefixEnd_7075324 : Nat := 4983230072969 + 3 ^ 40 * 7075324 * 2
def baseEnd_7075324 : Nat := 3633041998291980996011183

theorem tailTrace_7075324 : CollatzResearch.WordTrace tailWord_7075324 prefixEnd_7075324 3633041998291980996011183 := by
  unfold tailWord_7075324
  simp only [CollatzResearch.WordTrace]
  refine ⟨129029133309658495990564513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172038844412877994654086017 129029133309658495990564513)
  ·
    refine ⟨96771849982243871992923385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129029133309658495990564513 96771849982243871992923385)
    ·
      refine ⟨72578887486682903994692539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96771849982243871992923385 72578887486682903994692539)
      ·
        refine ⟨108868331230024355992038809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72578887486682903994692539 108868331230024355992038809)
        ·
          refine ⟨81651248422518266994029107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108868331230024355992038809 81651248422518266994029107)
          ·
            refine ⟨122476872633777400491043661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81651248422518266994029107 122476872633777400491043661)
            ·
              refine ⟨45928827237666525184141373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 122476872633777400491043661 45928827237666525184141373)
              ·
                refine ⟨17223310214124946944053015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45928827237666525184141373 17223310214124946944053015)
                ·
                  refine ⟨25834965321187420416079523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17223310214124946944053015 25834965321187420416079523)
                  ·
                    refine ⟨38752447981781130624119285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25834965321187420416079523 38752447981781130624119285)
                    ·
                      refine ⟨3633041998291980996011183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38752447981781130624119285 3633041998291980996011183)
                      ·
                        rfl

theorem cell23_7075324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 3, 1, 1, 5].length) (baseStart_7075324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7075324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7075324 prefixEnd_7075324 := by exact prefixLift 7075324
  have htrace : WordTrace (prefixWord ++ tailWord_7075324) baseStart_7075324 baseEnd_7075324 := by
    simpa [prefixWord, tailWord_7075324, baseEnd_7075324] using wordTrace_append hprefix tailTrace_7075324
  have hstable : (prefixWord ++ tailWord_7075324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7075324).length < 2 ^ (prefixWord ++ tailWord_7075324).sum := by decide
  have hdescent : baseEnd_7075324 < baseStart_7075324 := by decide
  rcases family_descends (prefixWord ++ tailWord_7075324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7075332 : List Nat := [2, 3, 2, 3, 3, 1, 1, 1, 3, 1, 3]
def baseStart_7075332 : Nat := 118140960795 + 7075332 * 2 ^ 59
def prefixEnd_7075332 : Nat := 4983230072969 + 3 ^ 40 * 7075332 * 2
def baseEnd_7075332 : Nat := 3633046106137216964711147

theorem tailTrace_7075332 : CollatzResearch.WordTrace tailWord_7075332 prefixEnd_7075332 3633046106137216964711147 := by
  unfold tailWord_7075332
  simp only [CollatzResearch.WordTrace]
  refine ⟨129029279201644004673710125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172039038935525339564946833 129029279201644004673710125)
  ·
    refine ⟨48385979700616501752641297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129029279201644004673710125 48385979700616501752641297)
    ·
      refine ⟨36289484775462376314480973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48385979700616501752641297 36289484775462376314480973)
      ·
        refine ⟨13608556790798391117930365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36289484775462376314480973 13608556790798391117930365)
        ·
          refine ⟨5103208796549396669223887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13608556790798391117930365 5103208796549396669223887)
          ·
            refine ⟨7654813194824095003835831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5103208796549396669223887 7654813194824095003835831)
            ·
              refine ⟨11482219792236142505753747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7654813194824095003835831 11482219792236142505753747)
              ·
                refine ⟨17223329688354213758630621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11482219792236142505753747 17223329688354213758630621)
                ·
                  refine ⟨6458748633132830159486483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17223329688354213758630621 6458748633132830159486483)
                  ·
                    refine ⟨9688122949699245239229725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6458748633132830159486483 9688122949699245239229725)
                    ·
                      refine ⟨3633046106137216964711147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9688122949699245239229725 3633046106137216964711147)
                      ·
                        rfl

theorem cell23_7075332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 1, 1, 3, 1, 3].length) (baseStart_7075332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7075332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7075332 prefixEnd_7075332 := by exact prefixLift 7075332
  have htrace : WordTrace (prefixWord ++ tailWord_7075332) baseStart_7075332 baseEnd_7075332 := by
    simpa [prefixWord, tailWord_7075332, baseEnd_7075332] using wordTrace_append hprefix tailTrace_7075332
  have hstable : (prefixWord ++ tailWord_7075332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7075332).length < 2 ^ (prefixWord ++ tailWord_7075332).sum := by decide
  have hdescent : baseEnd_7075332 < baseStart_7075332 := by decide
  rcases family_descends (prefixWord ++ tailWord_7075332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7075368 : List Nat := [2, 1, 5, 2, 2, 1, 1, 2, 1, 2, 4]
def baseStart_7075368 : Nat := 118140960795 + 7075368 * 2 ^ 59
def prefixEnd_7075368 : Nat := 4983230072969 + 3 ^ 40 * 7075368 * 2
def baseEnd_7075368 : Nat := 3633064591440778823860981

theorem tailTrace_7075368 : CollatzResearch.WordTrace tailWord_7075368 prefixEnd_7075368 3633064591440778823860981 := by
  unfold tailWord_7075368
  simp only [CollatzResearch.WordTrace]
  refine ⟨129029935715578793747865379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172039914287438391663820505 129029935715578793747865379)
  ·
    refine ⟨193544903573368190621798069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129029935715578793747865379 193544903573368190621798069)
    ·
      refine ⟨18144834710003267870793569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 193544903573368190621798069 18144834710003267870793569)
      ·
        refine ⟨13608626032502450903095177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18144834710003267870793569 13608626032502450903095177)
        ·
          refine ⟨10206469524376838177321383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13608626032502450903095177 10206469524376838177321383)
          ·
            refine ⟨15309704286565257265982075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10206469524376838177321383 15309704286565257265982075)
            ·
              refine ⟨22964556429847885898973113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15309704286565257265982075 22964556429847885898973113)
              ·
                refine ⟨17223417322385914424229835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22964556429847885898973113 17223417322385914424229835)
                ·
                  refine ⟨25835125983578871636344753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17223417322385914424229835 25835125983578871636344753)
                  ·
                    refine ⟨19376344487684153727258565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25835125983578871636344753 19376344487684153727258565)
                    ·
                      refine ⟨3633064591440778823860981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19376344487684153727258565 3633064591440778823860981)
                      ·
                        rfl

theorem cell23_7075368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_7075368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7075368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7075368 prefixEnd_7075368 := by exact prefixLift 7075368
  have htrace : WordTrace (prefixWord ++ tailWord_7075368) baseStart_7075368 baseEnd_7075368 := by
    simpa [prefixWord, tailWord_7075368, baseEnd_7075368] using wordTrace_append hprefix tailTrace_7075368
  have hstable : (prefixWord ++ tailWord_7075368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7075368).length < 2 ^ (prefixWord ++ tailWord_7075368).sum := by decide
  have hdescent : baseEnd_7075368 < baseStart_7075368 := by decide
  rcases family_descends (prefixWord ++ tailWord_7075368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7075404 : List Nat := [2, 2, 1, 3, 1, 3, 1, 1, 1, 8]
def baseStart_7075404 : Nat := 118140960795 + 7075404 * 2 ^ 59
def prefixEnd_7075404 : Nat := 4983230072969 + 3 ^ 40 * 7075404 * 2
def baseEnd_7075404 : Nat := 1211027692248113561003605

theorem tailTrace_7075404 : CollatzResearch.WordTrace tailWord_7075404 prefixEnd_7075404 1211027692248113561003605 := by
  unfold tailWord_7075404
  simp only [CollatzResearch.WordTrace]
  refine ⟨129030592229513582822020633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172040789639351443762694177 129030592229513582822020633)
  ·
    refine ⟨96772944172135187116515475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129030592229513582822020633 96772944172135187116515475)
    ·
      refine ⟨145159416258202780674773213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96772944172135187116515475 145159416258202780674773213)
      ·
        refine ⟨54434781096826042753039955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145159416258202780674773213 54434781096826042753039955)
        ·
          refine ⟨81652171645239064129559933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54434781096826042753039955 81652171645239064129559933)
          ·
            refine ⟨30619564366964649048584975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81652171645239064129559933 30619564366964649048584975)
            ·
              refine ⟨45929346550446973572877463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30619564366964649048584975 45929346550446973572877463)
              ·
                refine ⟨68894019825670460359316195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45929346550446973572877463 68894019825670460359316195)
                ·
                  refine ⟨103341029738505690538974293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68894019825670460359316195 103341029738505690538974293)
                  ·
                    refine ⟨1211027692248113561003605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 103341029738505690538974293 1211027692248113561003605)
                    ·
                      rfl

theorem cell23_7075404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 1, 1, 8].length) (baseStart_7075404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7075404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7075404 prefixEnd_7075404 := by exact prefixLift 7075404
  have htrace : WordTrace (prefixWord ++ tailWord_7075404) baseStart_7075404 baseEnd_7075404 := by
    simpa [prefixWord, tailWord_7075404, baseEnd_7075404] using wordTrace_append hprefix tailTrace_7075404
  have hstable : (prefixWord ++ tailWord_7075404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7075404).length < 2 ^ (prefixWord ++ tailWord_7075404).sum := by decide
  have hdescent : baseEnd_7075404 < baseStart_7075404 := by decide
  rcases family_descends (prefixWord ++ tailWord_7075404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7075405 : List Nat := [1, 6, 1, 1, 3, 1, 2, 1, 1, 3, 3]
def baseStart_7075405 : Nat := 118140960795 + 7075405 * 2 ^ 59
def prefixEnd_7075405 : Nat := 4983230072969 + 3 ^ 40 * 7075405 * 2
def baseEnd_7075405 : Nat := 3633083590224995179098311

theorem tailTrace_7075405 : CollatzResearch.WordTrace tailWord_7075405 prefixEnd_7075405 3633083590224995179098311 := by
  unfold tailWord_7075405
  simp only [CollatzResearch.WordTrace]
  refine ⟨258061220932023542814827669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172040813954682361876551779 258061220932023542814827669)
  ·
    refine ⟨12096619731188603569445047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 258061220932023542814827669 12096619731188603569445047)
    ·
      refine ⟨18144929596782905354167571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12096619731188603569445047 18144929596782905354167571)
      ·
        refine ⟨27217394395174358031251357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18144929596782905354167571 27217394395174358031251357)
        ·
          refine ⟨10206522898190384261719259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27217394395174358031251357 10206522898190384261719259)
          ·
            refine ⟨15309784347285576392578889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10206522898190384261719259 15309784347285576392578889)
            ·
              refine ⟨11482338260464182294434167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15309784347285576392578889 11482338260464182294434167)
              ·
                refine ⟨17223507390696273441651251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11482338260464182294434167 17223507390696273441651251)
                ·
                  refine ⟨25835261086044410162476877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17223507390696273441651251 25835261086044410162476877)
                  ·
                    refine ⟨9688222907266653810928829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25835261086044410162476877 9688222907266653810928829)
                    ·
                      refine ⟨3633083590224995179098311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9688222907266653810928829 3633083590224995179098311)
                      ·
                        rfl

theorem cell23_7075405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 2, 1, 1, 3, 3].length) (baseStart_7075405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7075405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7075405 prefixEnd_7075405 := by exact prefixLift 7075405
  have htrace : WordTrace (prefixWord ++ tailWord_7075405) baseStart_7075405 baseEnd_7075405 := by
    simpa [prefixWord, tailWord_7075405, baseEnd_7075405] using wordTrace_append hprefix tailTrace_7075405
  have hstable : (prefixWord ++ tailWord_7075405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7075405).length < 2 ^ (prefixWord ++ tailWord_7075405).sum := by decide
  have hdescent : baseEnd_7075405 < baseStart_7075405 := by decide
  rcases family_descends (prefixWord ++ tailWord_7075405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7075424 : List Nat := [2, 1, 1, 3, 2, 1, 1, 1, 3, 4, 4]
def baseStart_7075424 : Nat := 118140960795 + 7075424 * 2 ^ 59
def prefixEnd_7075424 : Nat := 4983230072969 + 3 ^ 40 * 7075424 * 2
def baseEnd_7075424 : Nat := 3633093346357430604760723

theorem tailTrace_7075424 : CollatzResearch.WordTrace tailWord_7075424 prefixEnd_7075424 3633093346357430604760723 := by
  unfold tailWord_7075424
  simp only [CollatzResearch.WordTrace]
  refine ⟨129030956959477354529884663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172041275945969806039846217 129030956959477354529884663)
  ·
    refine ⟨193546435439216031794826995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129030956959477354529884663 193546435439216031794826995)
    ·
      refine ⟨290319653158824047692240493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193546435439216031794826995 290319653158824047692240493)
      ·
        refine ⟨108869869934559017884590185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 290319653158824047692240493 108869869934559017884590185)
        ·
          refine ⟨81652402450919263413442639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108869869934559017884590185 81652402450919263413442639)
          ·
            refine ⟨122478603676378895120163959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81652402450919263413442639 122478603676378895120163959)
            ·
              refine ⟨183717905514568342680245939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122478603676378895120163959 183717905514568342680245939)
              ·
                refine ⟨275576858271852514020368909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 183717905514568342680245939 275576858271852514020368909)
                ·
                  refine ⟨103341321851944692757638341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 275576858271852514020368909 103341321851944692757638341)
                  ·
                    refine ⟨19376497847239629892057189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 103341321851944692757638341 19376497847239629892057189)
                    ·
                      refine ⟨3633093346357430604760723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19376497847239629892057189 3633093346357430604760723)
                      ·
                        rfl

theorem cell23_7075424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 3, 4, 4].length) (baseStart_7075424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7075424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7075424 prefixEnd_7075424 := by exact prefixLift 7075424
  have htrace : WordTrace (prefixWord ++ tailWord_7075424) baseStart_7075424 baseEnd_7075424 := by
    simpa [prefixWord, tailWord_7075424, baseEnd_7075424] using wordTrace_append hprefix tailTrace_7075424
  have hstable : (prefixWord ++ tailWord_7075424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7075424).length < 2 ^ (prefixWord ++ tailWord_7075424).sum := by decide
  have hdescent : baseEnd_7075424 < baseStart_7075424 := by decide
  rcases family_descends (prefixWord ++ tailWord_7075424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7075428 : List Nat := [2, 3, 1, 1, 2, 3, 2, 2, 1, 4, 2]
def baseStart_7075428 : Nat := 118140960795 + 7075428 * 2 ^ 59
def prefixEnd_7075428 : Nat := 4983230072969 + 3 ^ 40 * 7075428 * 2
def baseEnd_7075428 : Nat := 3633095400280048589110705

theorem tailTrace_7075428 : CollatzResearch.WordTrace tailWord_7075428 prefixEnd_7075428 3633095400280048589110705 := by
  unfold tailWord_7075428
  simp only [CollatzResearch.WordTrace]
  refine ⟨129031029905470108871457469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172041373207293478495276625 129031029905470108871457469)
  ·
    refine ⟨48386636214551290826796551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129031029905470108871457469 48386636214551290826796551)
    ·
      refine ⟨72579954321826936240194827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48386636214551290826796551 72579954321826936240194827)
      ·
        refine ⟨108869931482740404360292241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72579954321826936240194827 108869931482740404360292241)
        ·
          refine ⟨81652448612055303270219181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108869931482740404360292241 81652448612055303270219181)
          ·
            refine ⟨30619668229520738726332193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81652448612055303270219181 30619668229520738726332193)
            ·
              refine ⟨22964751172140554044749145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30619668229520738726332193 22964751172140554044749145)
              ·
                refine ⟨17223563379105415533561859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22964751172140554044749145 17223563379105415533561859)
                ·
                  refine ⟨25835345068658123300342789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17223563379105415533561859 25835345068658123300342789)
                  ·
                    refine ⟨4844127200373398118814273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25835345068658123300342789 4844127200373398118814273)
                    ·
                      refine ⟨3633095400280048589110705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4844127200373398118814273 3633095400280048589110705)
                      ·
                        rfl

theorem cell23_7075428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 2, 1, 4, 2].length) (baseStart_7075428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7075428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7075428 prefixEnd_7075428 := by exact prefixLift 7075428
  have htrace : WordTrace (prefixWord ++ tailWord_7075428) baseStart_7075428 baseEnd_7075428 := by
    simpa [prefixWord, tailWord_7075428, baseEnd_7075428] using wordTrace_append hprefix tailTrace_7075428
  have hstable : (prefixWord ++ tailWord_7075428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7075428).length < 2 ^ (prefixWord ++ tailWord_7075428).sum := by decide
  have hdescent : baseEnd_7075428 < baseStart_7075428 := by decide
  rcases family_descends (prefixWord ++ tailWord_7075428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7075432 : List Nat := [2, 1, 4, 3, 1, 1, 4, 1, 1, 3, 2]
def baseStart_7075432 : Nat := 118140960795 + 7075432 * 2 ^ 59
def prefixEnd_7075432 : Nat := 4983230072969 + 3 ^ 40 * 7075432 * 2
def baseEnd_7075432 : Nat := 3633097454202666573460687

theorem tailTrace_7075432 : CollatzResearch.WordTrace tailWord_7075432 prefixEnd_7075432 3633097454202666573460687 := by
  unfold tailWord_7075432
  simp only [CollatzResearch.WordTrace]
  refine ⟨129031102851462863213030275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172041470468617150950707033 129031102851462863213030275)
  ·
    refine ⟨193546654277194294819545413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129031102851462863213030275 193546654277194294819545413)
    ·
      refine ⟨36289997676973930278664765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 193546654277194294819545413 36289997676973930278664765)
      ·
        refine ⟨13608749128865223854499287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36289997676973930278664765 13608749128865223854499287)
        ·
          refine ⟨20413123693297835781748931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13608749128865223854499287 20413123693297835781748931)
          ·
            refine ⟨30619685539946753672623397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20413123693297835781748931 30619685539946753672623397)
            ·
              refine ⟨5741191038740016313616887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30619685539946753672623397 5741191038740016313616887)
              ·
                refine ⟨8611786558110024470425331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5741191038740016313616887 8611786558110024470425331)
                ·
                  refine ⟨12917679837165036705637997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8611786558110024470425331 12917679837165036705637997)
                  ·
                    refine ⟨4844129938936888764614249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12917679837165036705637997 4844129938936888764614249)
                    ·
                      refine ⟨3633097454202666573460687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4844129938936888764614249 3633097454202666573460687)
                      ·
                        rfl

theorem cell23_7075432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 4, 1, 1, 3, 2].length) (baseStart_7075432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7075432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7075432 prefixEnd_7075432 := by exact prefixLift 7075432
  have htrace : WordTrace (prefixWord ++ tailWord_7075432) baseStart_7075432 baseEnd_7075432 := by
    simpa [prefixWord, tailWord_7075432, baseEnd_7075432] using wordTrace_append hprefix tailTrace_7075432
  have hstable : (prefixWord ++ tailWord_7075432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7075432).length < 2 ^ (prefixWord ++ tailWord_7075432).sum := by decide
  have hdescent : baseEnd_7075432 < baseStart_7075432 := by decide
  rcases family_descends (prefixWord ++ tailWord_7075432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7075451 : List Nat := [1, 1, 1, 1, 1, 4, 3, 6, 5]
def baseStart_7075451 : Nat := 118140960795 + 7075451 * 2 ^ 59
def prefixEnd_7075451 : Nat := 4983230072969 + 3 ^ 40 * 7075451 * 2
def baseEnd_7075451 : Nat := 403678578926122444347011

theorem tailTrace_7075451 : CollatzResearch.WordTrace tailWord_7075451 prefixEnd_7075451 403678578926122444347011 := by
  unfold tailWord_7075451
  simp only [CollatzResearch.WordTrace]
  refine ⟨258062898689856892671002207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172041932459904595114001471 258062898689856892671002207)
  ·
    refine ⟨387094348034785339006503311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258062898689856892671002207 387094348034785339006503311)
    ·
      refine ⟨580641522052178008509754967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 387094348034785339006503311 580641522052178008509754967)
      ·
        refine ⟨870962283078267012764632451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 580641522052178008509754967 870962283078267012764632451)
        ·
          refine ⟨1306443424617400519146948677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 870962283078267012764632451 1306443424617400519146948677)
          ·
            refine ⟨244958142115762597340052877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1306443424617400519146948677 244958142115762597340052877)
            ·
              refine ⟨91859303293410974002519829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 244958142115762597340052877 91859303293410974002519829)
              ·
                refine ⟨4305904841878639406368117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 91859303293410974002519829 4305904841878639406368117)
                ·
                  refine ⟨403678578926122444347011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4305904841878639406368117 403678578926122444347011)
                  ·
                    rfl

theorem cell23_7075451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 6, 5].length) (baseStart_7075451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7075451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7075451 prefixEnd_7075451 := by exact prefixLift 7075451
  have htrace : WordTrace (prefixWord ++ tailWord_7075451) baseStart_7075451 baseEnd_7075451 := by
    simpa [prefixWord, tailWord_7075451, baseEnd_7075451] using wordTrace_append hprefix tailTrace_7075451
  have hstable : (prefixWord ++ tailWord_7075451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7075451).length < 2 ^ (prefixWord ++ tailWord_7075451).sum := by decide
  have hdescent : baseEnd_7075451 < baseStart_7075451 := by decide
  rcases family_descends (prefixWord ++ tailWord_7075451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7075461 : List Nat := [1, 3, 1, 1, 4, 1, 1, 3, 2, 3, 3]
def baseStart_7075461 : Nat := 118140960795 + 7075461 * 2 ^ 59
def prefixEnd_7075461 : Nat := 4983230072969 + 3 ^ 40 * 7075461 * 2
def baseEnd_7075461 : Nat := 3633112345141646959998053

theorem tailTrace_7075461 : CollatzResearch.WordTrace tailWord_7075461 prefixEnd_7075461 3633112345141646959998053 := by
  unfold tailWord_7075461
  simp only [CollatzResearch.WordTrace]
  refine ⟨258063263419820664378866237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172042175613213776252577491 258063263419820664378866237)
  ·
    refine ⟨96773723782432749142074839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 258063263419820664378866237 96773723782432749142074839)
    ·
      refine ⟨145160585673649123713112259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96773723782432749142074839 145160585673649123713112259)
      ·
        refine ⟨217740878510473685569668389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145160585673649123713112259 217740878510473685569668389)
        ·
          refine ⟨40826414720713816044312823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 217740878510473685569668389 40826414720713816044312823)
          ·
            refine ⟨61239622081070724066469235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40826414720713816044312823 61239622081070724066469235)
            ·
              refine ⟨91859433121606086099703853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61239622081070724066469235 91859433121606086099703853)
              ·
                refine ⟨34447287420602282287388945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91859433121606086099703853 34447287420602282287388945)
                ·
                  refine ⟨25835465565451711715541709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34447287420602282287388945 25835465565451711715541709)
                  ·
                    refine ⟨9688299587044391893328141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25835465565451711715541709 9688299587044391893328141)
                    ·
                      refine ⟨3633112345141646959998053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9688299587044391893328141 3633112345141646959998053)
                      ·
                        rfl

theorem cell23_7075461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 3, 2, 3, 3].length) (baseStart_7075461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7075461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7075461 prefixEnd_7075461 := by exact prefixLift 7075461
  have htrace : WordTrace (prefixWord ++ tailWord_7075461) baseStart_7075461 baseEnd_7075461 := by
    simpa [prefixWord, tailWord_7075461, baseEnd_7075461] using wordTrace_append hprefix tailTrace_7075461
  have hstable : (prefixWord ++ tailWord_7075461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7075461).length < 2 ^ (prefixWord ++ tailWord_7075461).sum := by decide
  have hdescent : baseEnd_7075461 < baseStart_7075461 := by decide
  rcases family_descends (prefixWord ++ tailWord_7075461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7075502 : List Nat := [4, 1, 4, 1, 3, 1, 1, 1, 7]
def baseStart_7075502 : Nat := 118140960795 + 7075502 * 2 ^ 59
def prefixEnd_7075502 : Nat := 4983230072969 + 3 ^ 40 * 7075502 * 2
def baseEnd_7075502 : Nat := 403681488649831255509485

theorem tailTrace_7075502 : CollatzResearch.WordTrace tailWord_7075502 prefixEnd_7075502 403681488649831255509485 := by
  unfold tailWord_7075502
  simp only [CollatzResearch.WordTrace]
  refine ⟨32258094851584016047638595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172043172541781418920739173 32258094851584016047638595)
  ·
    refine ⟨48387142277376024071457893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32258094851584016047638595 48387142277376024071457893)
    ·
      refine ⟨9072589177008004513398355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48387142277376024071457893 9072589177008004513398355)
      ·
        refine ⟨13608883765512006770097533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9072589177008004513398355 13608883765512006770097533)
        ·
          refine ⟨5103331412067002538786575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13608883765512006770097533 5103331412067002538786575)
          ·
            refine ⟨7654997118100503808179863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5103331412067002538786575 7654997118100503808179863)
            ·
              refine ⟨11482495677150755712269795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7654997118100503808179863 11482495677150755712269795)
              ·
                refine ⟨17223743515726133568404693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11482495677150755712269795 17223743515726133568404693)
                ·
                  refine ⟨403681488649831255509485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17223743515726133568404693 403681488649831255509485)
                  ·
                    rfl

theorem cell23_7075502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 1, 1, 7].length) (baseStart_7075502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7075502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7075502 prefixEnd_7075502 := by exact prefixLift 7075502
  have htrace : WordTrace (prefixWord ++ tailWord_7075502) baseStart_7075502 baseEnd_7075502 := by
    simpa [prefixWord, tailWord_7075502, baseEnd_7075502] using wordTrace_append hprefix tailTrace_7075502
  have hstable : (prefixWord ++ tailWord_7075502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7075502).length < 2 ^ (prefixWord ++ tailWord_7075502).sum := by decide
  have hdescent : baseEnd_7075502 < baseStart_7075502 := by decide
  rcases family_descends (prefixWord ++ tailWord_7075502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7075562 : List Nat := [3, 1, 3, 1, 1, 1, 6, 2, 1, 4]
def baseStart_7075562 : Nat := 118140960795 + 7075562 * 2 ^ 59
def prefixEnd_7075562 : Nat := 4983230072969 + 3 ^ 40 * 7075562 * 2
def baseEnd_7075562 : Nat := 1211054735562583688278363

theorem tailTrace_7075562 : CollatzResearch.WordTrace tailWord_7075562 prefixEnd_7075562 1211054735562583688278363 := by
  unfold tailWord_7075562
  simp only [CollatzResearch.WordTrace]
  refine ⟨64516736798113689657073235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172044631461636505752195293 64516736798113689657073235)
  ·
    refine ⟨96775105197170534485609853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64516736798113689657073235 96775105197170534485609853)
    ·
      refine ⟨36290664448938950432103695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96775105197170534485609853 36290664448938950432103695)
      ·
        refine ⟨54435996673408425648155543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36290664448938950432103695 54435996673408425648155543)
        ·
          refine ⟨81653995010112638472233315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54435996673408425648155543 81653995010112638472233315)
          ·
            refine ⟨122480992515168957708349973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81653995010112638472233315 122480992515168957708349973)
            ·
              refine ⟨5741296524148544892578905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 122480992515168957708349973 5741296524148544892578905)
              ·
                refine ⟨4305972393111408669434179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5741296524148544892578905 4305972393111408669434179)
                ·
                  refine ⟨6458958589667113004151269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4305972393111408669434179 6458958589667113004151269)
                  ·
                    refine ⟨1211054735562583688278363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6458958589667113004151269 1211054735562583688278363)
                    ·
                      rfl

theorem cell23_7075562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 6, 2, 1, 4].length) (baseStart_7075562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7075562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7075562 prefixEnd_7075562 := by exact prefixLift 7075562
  have htrace : WordTrace (prefixWord ++ tailWord_7075562) baseStart_7075562 baseEnd_7075562 := by
    simpa [prefixWord, tailWord_7075562, baseEnd_7075562] using wordTrace_append hprefix tailTrace_7075562
  have hstable : (prefixWord ++ tailWord_7075562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7075562).length < 2 ^ (prefixWord ++ tailWord_7075562).sum := by decide
  have hdescent : baseEnd_7075562 < baseStart_7075562 := by decide
  rcases family_descends (prefixWord ++ tailWord_7075562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7075571 : List Nat := [1, 1, 1, 2, 2, 3, 3, 2, 3, 5]
def baseStart_7075571 : Nat := 118140960795 + 7075571 * 2 ^ 59
def prefixEnd_7075571 : Nat := 4983230072969 + 3 ^ 40 * 7075571 * 2
def baseEnd_7075571 : Nat := 1211056276004547176540849

theorem tailTrace_7075571 : CollatzResearch.WordTrace tailWord_7075571 prefixEnd_7075571 1211056276004547176540849 := by
  unfold tailWord_7075571
  simp only [CollatzResearch.WordTrace]
  refine ⟨258067275449422153165370567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172044850299614768776913711 258067275449422153165370567)
  ·
    refine ⟨387100913174133229748055851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258067275449422153165370567 387100913174133229748055851)
    ·
      refine ⟨580651369761199844622083777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 387100913174133229748055851 580651369761199844622083777)
      ·
        refine ⟨435488527320899883466562833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 580651369761199844622083777 435488527320899883466562833)
        ·
          refine ⟨326616395490674912599922125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 435488527320899883466562833 326616395490674912599922125)
          ·
            refine ⟨122481148309003092224970797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 326616395490674912599922125 122481148309003092224970797)
            ·
              refine ⟨45930430615876159584364049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 122481148309003092224970797 45930430615876159584364049)
              ·
                refine ⟨34447822961907119688273037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45930430615876159584364049 34447822961907119688273037)
                ·
                  refine ⟨12917933610715169883102389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34447822961907119688273037 12917933610715169883102389)
                  ·
                    refine ⟨1211056276004547176540849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12917933610715169883102389 1211056276004547176540849)
                    ·
                      rfl

theorem cell23_7075571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 2, 3, 5].length) (baseStart_7075571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7075571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7075571 prefixEnd_7075571 := by exact prefixLift 7075571
  have htrace : WordTrace (prefixWord ++ tailWord_7075571) baseStart_7075571 baseEnd_7075571 := by
    simpa [prefixWord, tailWord_7075571, baseEnd_7075571] using wordTrace_append hprefix tailTrace_7075571
  have hstable : (prefixWord ++ tailWord_7075571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7075571).length < 2 ^ (prefixWord ++ tailWord_7075571).sum := by decide
  have hdescent : baseEnd_7075571 < baseStart_7075571 := by decide
  rcases family_descends (prefixWord ++ tailWord_7075571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7075578 : List Nat := [3, 1, 1, 1, 1, 3, 1, 4, 1, 5, 2]
def baseStart_7075578 : Nat := 118140960795 + 7075578 * 2 ^ 59
def prefixEnd_7075578 : Nat := 4983230072969 + 3 ^ 40 * 7075578 * 2
def baseEnd_7075578 : Nat := 3633172422378223002235015

theorem tailTrace_7075578 : CollatzResearch.WordTrace tailWord_7075578 prefixEnd_7075578 3633172422378223002235015 := by
  unfold tailWord_7075578
  simp only [CollatzResearch.WordTrace]
  refine ⟨64516882690099198340218847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172045020506931195573916925 64516882690099198340218847)
  ·
    refine ⟨96775324035148797510328271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64516882690099198340218847 96775324035148797510328271)
    ·
      refine ⟨145162986052723196265492407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96775324035148797510328271 145162986052723196265492407)
      ·
        refine ⟨217744479079084794398238611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145162986052723196265492407 217744479079084794398238611)
        ·
          refine ⟨326616718618627191597357917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217744479079084794398238611 326616718618627191597357917)
          ·
            refine ⟨122481269481985196849009219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 326616718618627191597357917 122481269481985196849009219)
            ·
              refine ⟨183721904222977795273513829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122481269481985196849009219 183721904222977795273513829)
              ·
                refine ⟨34447857041808336613783843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 183721904222977795273513829 34447857041808336613783843)
                ·
                  refine ⟨51671785562712504920675765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34447857041808336613783843 51671785562712504920675765)
                  ·
                    refine ⟨4844229896504297336313353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51671785562712504920675765 4844229896504297336313353)
                    ·
                      refine ⟨3633172422378223002235015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4844229896504297336313353 3633172422378223002235015)
                      ·
                        rfl

theorem cell23_7075578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 4, 1, 5, 2].length) (baseStart_7075578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7075578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7075578 prefixEnd_7075578 := by exact prefixLift 7075578
  have htrace : WordTrace (prefixWord ++ tailWord_7075578) baseStart_7075578 baseEnd_7075578 := by
    simpa [prefixWord, tailWord_7075578, baseEnd_7075578] using wordTrace_append hprefix tailTrace_7075578
  have hstable : (prefixWord ++ tailWord_7075578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7075578).length < 2 ^ (prefixWord ++ tailWord_7075578).sum := by decide
  have hdescent : baseEnd_7075578 < baseStart_7075578 := by decide
  rcases family_descends (prefixWord ++ tailWord_7075578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7075588 : List Nat := [2, 3, 2, 2, 1, 2, 2, 1, 3, 5]
def baseStart_7075588 : Nat := 118140960795 + 7075588 * 2 ^ 59
def prefixEnd_7075588 : Nat := 4983230072969 + 3 ^ 40 * 7075588 * 2
def baseEnd_7075588 : Nat := 1211059185728255987703323

theorem tailTrace_7075588 : CollatzResearch.WordTrace tailWord_7075588 prefixEnd_7075588 1211059185728255987703323 := by
  unfold tailWord_7075588
  simp only [CollatzResearch.WordTrace]
  refine ⟨129033947745180282534369709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172045263660240376712492945 129033947745180282534369709)
  ·
    refine ⟨48387730404442605950388641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129033947745180282534369709 48387730404442605950388641)
    ·
      refine ⟨36290797803331954462791481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48387730404442605950388641 36290797803331954462791481)
      ·
        refine ⟨27218098352498965847093611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36290797803331954462791481 27218098352498965847093611)
        ·
          refine ⟨40827147528748448770640417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27218098352498965847093611 40827147528748448770640417)
          ·
            refine ⟨30620360646561336577980313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40827147528748448770640417 30620360646561336577980313)
            ·
              refine ⟨22965270484921002433485235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30620360646561336577980313 22965270484921002433485235)
              ·
                refine ⟨34447905727381503650227853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22965270484921002433485235 34447905727381503650227853)
                ·
                  refine ⟨12917964647768063868835445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34447905727381503650227853 12917964647768063868835445)
                  ·
                    refine ⟨1211059185728255987703323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12917964647768063868835445 1211059185728255987703323)
                    ·
                      rfl

theorem cell23_7075588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 1, 3, 5].length) (baseStart_7075588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7075588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7075588 prefixEnd_7075588 := by exact prefixLift 7075588
  have htrace : WordTrace (prefixWord ++ tailWord_7075588) baseStart_7075588 baseEnd_7075588 := by
    simpa [prefixWord, tailWord_7075588, baseEnd_7075588] using wordTrace_append hprefix tailTrace_7075588
  have hstable : (prefixWord ++ tailWord_7075588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7075588).length < 2 ^ (prefixWord ++ tailWord_7075588).sum := by decide
  have hdescent : baseEnd_7075588 < baseStart_7075588 := by decide
  rcases family_descends (prefixWord ++ tailWord_7075588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7075595 : List Nat := [1, 1, 1, 1, 5, 1, 5, 1, 2, 3, 2]
def baseStart_7075595 : Nat := 118140960795 + 7075595 * 2 ^ 59
def prefixEnd_7075595 : Nat := 4983230072969 + 3 ^ 40 * 7075595 * 2
def baseEnd_7075595 : Nat := 3633181151549349435722437

theorem tailTrace_7075595 : CollatzResearch.WordTrace tailWord_7075595 prefixEnd_7075595 3633181151549349435722437 := by
  unfold tailWord_7075595
  simp only [CollatzResearch.WordTrace]
  refine ⟨258068150801335205264244239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172045433867556803509496159 258068150801335205264244239)
  ·
    refine ⟨387102226202002807896366359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258068150801335205264244239 387102226202002807896366359)
    ·
      refine ⟨580653339303004211844549539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 387102226202002807896366359 580653339303004211844549539)
      ·
        refine ⟨870980008954506317766824309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 580653339303004211844549539 870980008954506317766824309)
        ·
          refine ⟨81654375839484967290639779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 870980008954506317766824309 81654375839484967290639779)
          ·
            refine ⟨122481563759227450935959669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81654375839484967290639779 122481563759227450935959669)
            ·
              refine ⟨11482646602427573525246219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 122481563759227450935959669 11482646602427573525246219)
              ·
                refine ⟨17223969903641360287869329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11482646602427573525246219 17223969903641360287869329)
                ·
                  refine ⟨12917977427731020215901997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17223969903641360287869329 12917977427731020215901997)
                  ·
                    refine ⟨4844241535399132580963249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12917977427731020215901997 4844241535399132580963249)
                    ·
                      refine ⟨3633181151549349435722437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4844241535399132580963249 3633181151549349435722437)
                      ·
                        rfl

theorem cell23_7075595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 5, 1, 2, 3, 2].length) (baseStart_7075595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7075595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7075595 prefixEnd_7075595 := by exact prefixLift 7075595
  have htrace : WordTrace (prefixWord ++ tailWord_7075595) baseStart_7075595 baseEnd_7075595 := by
    simpa [prefixWord, tailWord_7075595, baseEnd_7075595] using wordTrace_append hprefix tailTrace_7075595
  have hstable : (prefixWord ++ tailWord_7075595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7075595).length < 2 ^ (prefixWord ++ tailWord_7075595).sum := by decide
  have hdescent : baseEnd_7075595 < baseStart_7075595 := by decide
  rcases family_descends (prefixWord ++ tailWord_7075595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7075605 : List Nat := [1, 3, 2, 1, 2, 3, 4, 1, 1, 5]
def baseStart_7075605 : Nat := 118140960795 + 7075605 * 2 ^ 59
def prefixEnd_7075605 : Nat := 4983230072969 + 3 ^ 40 * 7075605 * 2
def baseEnd_7075605 : Nat := 1211062095451964798865797

theorem tailTrace_7075605 : CollatzResearch.WordTrace tailWord_7075605 prefixEnd_7075605 1211062095451964798865797 := by
  unfold tailWord_7075605
  simp only [CollatzResearch.WordTrace]
  refine ⟨258068515531298976972108269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172045677020865984648072179 258068515531298976972108269)
  ·
    refine ⟨96775693324237116364540601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 258068515531298976972108269 96775693324237116364540601)
    ·
      refine ⟨72581769993177837273405451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96775693324237116364540601 72581769993177837273405451)
      ·
        refine ⟨108872654989766755910108177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72581769993177837273405451 108872654989766755910108177)
        ·
          refine ⟨81654491242325066932581133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108872654989766755910108177 81654491242325066932581133)
          ·
            refine ⟨30620434215871900099717925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81654491242325066932581133 30620434215871900099717925)
            ·
              refine ⟨5741331415475981268697111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30620434215871900099717925 5741331415475981268697111)
              ·
                refine ⟨8611997123213971903045667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5741331415475981268697111 8611997123213971903045667)
                ·
                  refine ⟨12917995684820957854568501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8611997123213971903045667 12917995684820957854568501)
                  ·
                    refine ⟨1211062095451964798865797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12917995684820957854568501 1211062095451964798865797)
                    ·
                      rfl

theorem cell23_7075605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 4, 1, 1, 5].length) (baseStart_7075605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7075605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7075605 prefixEnd_7075605 := by exact prefixLift 7075605
  have htrace : WordTrace (prefixWord ++ tailWord_7075605) baseStart_7075605 baseEnd_7075605 := by
    simpa [prefixWord, tailWord_7075605, baseEnd_7075605] using wordTrace_append hprefix tailTrace_7075605
  have hstable : (prefixWord ++ tailWord_7075605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7075605).length < 2 ^ (prefixWord ++ tailWord_7075605).sum := by decide
  have hdescent : baseEnd_7075605 < baseStart_7075605 := by decide
  rcases family_descends (prefixWord ++ tailWord_7075605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7075628 : List Nat := [2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 5]
def baseStart_7075628 : Nat := 118140960795 + 7075628 * 2 ^ 59
def prefixEnd_7075628 : Nat := 4983230072969 + 3 ^ 40 * 7075628 * 2
def baseEnd_7075628 : Nat := 3633198096410947806609785

theorem tailTrace_7075628 : CollatzResearch.WordTrace tailWord_7075628 prefixEnd_7075628 3633198096410947806609785 := by
  unfold tailWord_7075628
  simp only [CollatzResearch.WordTrace]
  refine ⟨129034677205107825950097769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172046236273477101266797025 129034677205107825950097769)
  ·
    refine ⟨96776007903830869462573327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129034677205107825950097769 96776007903830869462573327)
    ·
      refine ⟨145164011855746304193859991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96776007903830869462573327 145164011855746304193859991)
      ·
        refine ⟨217746017783619456290789987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145164011855746304193859991 217746017783619456290789987)
        ·
          refine ⟨326619026675429184436184981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217746017783619456290789987 326619026675429184436184981)
          ·
            refine ⟨15310266875410743020446171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 326619026675429184436184981 15310266875410743020446171)
            ·
              refine ⟨22965400313116114530669257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15310266875410743020446171 22965400313116114530669257)
              ·
                refine ⟨17224050234837085898001943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22965400313116114530669257 17224050234837085898001943)
                ·
                  refine ⟨25836075352255628847002915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17224050234837085898001943 25836075352255628847002915)
                  ·
                    refine ⟨38754113028383443270504373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25836075352255628847002915 38754113028383443270504373)
                    ·
                      refine ⟨3633198096410947806609785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38754113028383443270504373 3633198096410947806609785)
                      ·
                        rfl

theorem cell23_7075628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 5].length) (baseStart_7075628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7075628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7075628 prefixEnd_7075628 := by exact prefixLift 7075628
  have htrace : WordTrace (prefixWord ++ tailWord_7075628) baseStart_7075628 baseEnd_7075628 := by
    simpa [prefixWord, tailWord_7075628, baseEnd_7075628] using wordTrace_append hprefix tailTrace_7075628
  have hstable : (prefixWord ++ tailWord_7075628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7075628).length < 2 ^ (prefixWord ++ tailWord_7075628).sum := by decide
  have hdescent : baseEnd_7075628 < baseStart_7075628 := by decide
  rcases family_descends (prefixWord ++ tailWord_7075628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7075635 : List Nat := [1, 1, 1, 2, 7, 2, 1, 1, 1, 6]
def baseStart_7075635 : Nat := 118140960795 + 7075635 * 2 ^ 59
def prefixEnd_7075635 : Nat := 4983230072969 + 3 ^ 40 * 7075635 * 2
def baseEnd_7075635 : Nat := 1211067230258509759740751

theorem tailTrace_7075635 : CollatzResearch.WordTrace tailWord_7075635 prefixEnd_7075635 1211067230258509759740751 := by
  unfold tailWord_7075635
  simp only [CollatzResearch.WordTrace]
  refine ⟨258069609721190292095700359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172046406480793528063800239 258069609721190292095700359)
  ·
    refine ⟨387104414581785438143550539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258069609721190292095700359 387104414581785438143550539)
    ·
      refine ⟨580656621872678157215325809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 387104414581785438143550539 580656621872678157215325809)
      ·
        refine ⟨435492466404508617911494357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 580656621872678157215325809 435492466404508617911494357)
        ·
          refine ⟨10206854681355670732300649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 435492466404508617911494357 10206854681355670732300649)
          ·
            refine ⟨7655141011016753049225487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10206854681355670732300649 7655141011016753049225487)
            ·
              refine ⟨11482711516525129573838231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7655141011016753049225487 11482711516525129573838231)
              ·
                refine ⟨17224067274787694360757347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11482711516525129573838231 17224067274787694360757347)
                ·
                  refine ⟨25836100912181541541136021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17224067274787694360757347 25836100912181541541136021)
                  ·
                    refine ⟨1211067230258509759740751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25836100912181541541136021 1211067230258509759740751)
                    ·
                      rfl

theorem cell23_7075635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 1, 1, 1, 6].length) (baseStart_7075635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7075635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7075635 prefixEnd_7075635 := by exact prefixLift 7075635
  have htrace : WordTrace (prefixWord ++ tailWord_7075635) baseStart_7075635 baseEnd_7075635 := by
    simpa [prefixWord, tailWord_7075635, baseEnd_7075635] using wordTrace_append hprefix tailTrace_7075635
  have hstable : (prefixWord ++ tailWord_7075635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7075635).length < 2 ^ (prefixWord ++ tailWord_7075635).sum := by decide
  have hdescent : baseEnd_7075635 < baseStart_7075635 := by decide
  rcases family_descends (prefixWord ++ tailWord_7075635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7075642 : List Nat := [3, 1, 1, 1, 5, 1, 2, 2, 3, 2, 2]
def baseStart_7075642 : Nat := 118140960795 + 7075642 * 2 ^ 59
def prefixEnd_7075642 : Nat := 4983230072969 + 3 ^ 40 * 7075642 * 2
def baseEnd_7075642 : Nat := 3633205285140110751834721

theorem tailTrace_7075642 : CollatzResearch.WordTrace tailWord_7075642 prefixEnd_7075642 3633205285140110751834721 := by
  unfold tailWord_7075642
  simp only [CollatzResearch.WordTrace]
  refine ⟨64517466258041233072801295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172046576688109954860803453 64517466258041233072801295)
  ·
    refine ⟨96776199387061849609201943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64517466258041233072801295 96776199387061849609201943)
    ·
      refine ⟨145164299080592774413802915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96776199387061849609201943 145164299080592774413802915)
      ·
        refine ⟨217746448620889161620704373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145164299080592774413802915 217746448620889161620704373)
        ·
          refine ⟨20413729558208358901941035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 217746448620889161620704373 20413729558208358901941035)
          ·
            refine ⟨30620594337312538352911553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20413729558208358901941035 30620594337312538352911553)
            ·
              refine ⟨22965445752984403764683665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30620594337312538352911553 22965445752984403764683665)
              ·
                refine ⟨17224084314738302823512749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22965445752984403764683665 17224084314738302823512749)
                ·
                  refine ⟨6459031618026863558817281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17224084314738302823512749 6459031618026863558817281)
                  ·
                    refine ⟨4844273713520147669112961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6459031618026863558817281 4844273713520147669112961)
                    ·
                      refine ⟨3633205285140110751834721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4844273713520147669112961 3633205285140110751834721)
                      ·
                        rfl

theorem cell23_7075642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 2, 3, 2, 2].length) (baseStart_7075642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7075642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7075642 prefixEnd_7075642 := by exact prefixLift 7075642
  have htrace : WordTrace (prefixWord ++ tailWord_7075642) baseStart_7075642 baseEnd_7075642 := by
    simpa [prefixWord, tailWord_7075642, baseEnd_7075642] using wordTrace_append hprefix tailTrace_7075642
  have hstable : (prefixWord ++ tailWord_7075642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7075642).length < 2 ^ (prefixWord ++ tailWord_7075642).sum := by decide
  have hdescent : baseEnd_7075642 < baseStart_7075642 := by decide
  rcases family_descends (prefixWord ++ tailWord_7075642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7075658 : List Nat := [3, 1, 2, 1, 1, 1, 4, 1, 3, 3, 3]
def baseStart_7075658 : Nat := 118140960795 + 7075658 * 2 ^ 59
def prefixEnd_7075658 : Nat := 4983230072969 + 3 ^ 40 * 7075658 * 2
def baseEnd_7075658 : Nat := 3633213500830582689234647

theorem tailTrace_7075658 : CollatzResearch.WordTrace tailWord_7075658 prefixEnd_7075658 3633213500830582689234647 := by
  unfold tailWord_7075658
  simp only [CollatzResearch.WordTrace]
  refine ⟨64517612150026741755946907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172046965733404644682525085 64517612150026741755946907)
  ·
    refine ⟨96776418225040112633920361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64517612150026741755946907 96776418225040112633920361)
    ·
      refine ⟨72582313668780084475440271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96776418225040112633920361 72582313668780084475440271)
      ·
        refine ⟨108873470503170126713160407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72582313668780084475440271 108873470503170126713160407)
        ·
          refine ⟨163310205754755190069740611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108873470503170126713160407 163310205754755190069740611)
          ·
            refine ⟨244965308632132785104610917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163310205754755190069740611 244965308632132785104610917)
            ·
              refine ⟨45930995368524897207114547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 244965308632132785104610917 45930995368524897207114547)
              ·
                refine ⟨68896493052787345810671821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45930995368524897207114547 68896493052787345810671821)
                ·
                  refine ⟨25836184894795254679001933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68896493052787345810671821 25836184894795254679001933)
                  ·
                    refine ⟨9688569335548220504625725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25836184894795254679001933 9688569335548220504625725)
                    ·
                      refine ⟨3633213500830582689234647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9688569335548220504625725 3633213500830582689234647)
                      ·
                        rfl

theorem cell23_7075658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 1, 3, 3, 3].length) (baseStart_7075658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7075658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7075658 prefixEnd_7075658 := by exact prefixLift 7075658
  have htrace : WordTrace (prefixWord ++ tailWord_7075658) baseStart_7075658 baseEnd_7075658 := by
    simpa [prefixWord, tailWord_7075658, baseEnd_7075658] using wordTrace_append hprefix tailTrace_7075658
  have hstable : (prefixWord ++ tailWord_7075658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7075658).length < 2 ^ (prefixWord ++ tailWord_7075658).sum := by decide
  have hdescent : baseEnd_7075658 < baseStart_7075658 := by decide
  rcases family_descends (prefixWord ++ tailWord_7075658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7075676 : List Nat := [2, 2, 4, 2, 2, 2, 1, 1, 3, 2, 2]
def baseStart_7075676 : Nat := 118140960795 + 7075676 * 2 ^ 59
def prefixEnd_7075676 : Nat := 4983230072969 + 3 ^ 40 * 7075676 * 2
def baseEnd_7075676 : Nat := 3633222743482363618809565

theorem tailTrace_7075676 : CollatzResearch.WordTrace tailWord_7075676 prefixEnd_7075676 3633222743482363618809565 := by
  unfold tailWord_7075676
  simp only [CollatzResearch.WordTrace]
  refine ⟨129035552557020878048971441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172047403409361170731961921 129035552557020878048971441)
  ·
    refine ⟨96776664417765658536728581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129035552557020878048971441 96776664417765658536728581)
    ·
      refine ⟨18145624578331060975636609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96776664417765658536728581 18145624578331060975636609)
      ·
        refine ⟨13609218433748295731727457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18145624578331060975636609 13609218433748295731727457)
        ·
          refine ⟨10206913825311221798795593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13609218433748295731727457 10206913825311221798795593)
          ·
            refine ⟨7655185368983416349096695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10206913825311221798795593 7655185368983416349096695)
            ·
              refine ⟨11482778053475124523645043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7655185368983416349096695 11482778053475124523645043)
              ·
                refine ⟨17224167080212686785467565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11482778053475124523645043 17224167080212686785467565)
                ·
                  refine ⟨6459062655079757544550337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17224167080212686785467565 6459062655079757544550337)
                  ·
                    refine ⟨4844296991309818158412753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6459062655079757544550337 4844296991309818158412753)
                    ·
                      refine ⟨3633222743482363618809565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4844296991309818158412753 3633222743482363618809565)
                      ·
                        rfl

theorem cell23_7075676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 1, 1, 3, 2, 2].length) (baseStart_7075676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7075676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7075676 prefixEnd_7075676 := by exact prefixLift 7075676
  have htrace : WordTrace (prefixWord ++ tailWord_7075676) baseStart_7075676 baseEnd_7075676 := by
    simpa [prefixWord, tailWord_7075676, baseEnd_7075676] using wordTrace_append hprefix tailTrace_7075676
  have hstable : (prefixWord ++ tailWord_7075676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7075676).length < 2 ^ (prefixWord ++ tailWord_7075676).sum := by decide
  have hdescent : baseEnd_7075676 < baseStart_7075676 := by decide
  rcases family_descends (prefixWord ++ tailWord_7075676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7075685 : List Nat := [1, 3, 1, 3, 1, 1, 1, 4, 3, 3, 2]
def baseStart_7075685 : Nat := 118140960795 + 7075685 * 2 ^ 59
def prefixEnd_7075685 : Nat := 4983230072969 + 3 ^ 40 * 7075685 * 2
def baseEnd_7075685 : Nat := 3633227364808254083597023

theorem tailTrace_7075685 : CollatzResearch.WordTrace tailWord_7075685 prefixEnd_7075685 3633227364808254083597023 := by
  unfold tailWord_7075685
  simp only [CollatzResearch.WordTrace]
  refine ⟨258071433371009150635020509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172047622247339433756680339 258071433371009150635020509)
  ·
    refine ⟨96776787514128431488132691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 258071433371009150635020509 96776787514128431488132691)
    ·
      refine ⟨145165181271192647232199037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96776787514128431488132691 145165181271192647232199037)
      ·
        refine ⟨54436942976697242712074639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145165181271192647232199037 54436942976697242712074639)
        ·
          refine ⟨81655414465045864068111959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54436942976697242712074639 81655414465045864068111959)
          ·
            refine ⟨122483121697568796102167939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81655414465045864068111959 122483121697568796102167939)
            ·
              refine ⟨183724682546353194153251909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122483121697568796102167939 183724682546353194153251909)
              ·
                refine ⟨34448377977441223903734733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 183724682546353194153251909 34448377977441223903734733)
                ·
                  refine ⟨12918141741540458963900525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34448377977441223903734733 12918141741540458963900525)
                  ·
                    refine ⟨4844303153077672111462697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12918141741540458963900525 4844303153077672111462697)
                    ·
                      refine ⟨3633227364808254083597023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4844303153077672111462697 3633227364808254083597023)
                      ·
                        rfl

theorem cell23_7075685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 4, 3, 3, 2].length) (baseStart_7075685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7075685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7075685 prefixEnd_7075685 := by exact prefixLift 7075685
  have htrace : WordTrace (prefixWord ++ tailWord_7075685) baseStart_7075685 baseEnd_7075685 := by
    simpa [prefixWord, tailWord_7075685, baseEnd_7075685] using wordTrace_append hprefix tailTrace_7075685
  have hstable : (prefixWord ++ tailWord_7075685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7075685).length < 2 ^ (prefixWord ++ tailWord_7075685).sum := by decide
  have hdescent : baseEnd_7075685 < baseStart_7075685 := by decide
  rcases family_descends (prefixWord ++ tailWord_7075685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7075691 : List Nat := [1, 1, 1, 1, 2, 2, 3, 3, 1, 8]
def baseStart_7075691 : Nat := 118140960795 + 7075691 * 2 ^ 59
def prefixEnd_7075691 : Nat := 4983230072969 + 3 ^ 40 * 7075691 * 2
def baseEnd_7075691 : Nat := 1211076815230727020040665

theorem tailTrace_7075691 : CollatzResearch.WordTrace tailWord_7075691 prefixEnd_7075691 1211076815230727020040665 := by
  unfold tailWord_7075691
  simp only [CollatzResearch.WordTrace]
  refine ⟨258071652208987413659738927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172047768139324942439825951 258071652208987413659738927)
  ·
    refine ⟨387107478313481120489608391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258071652208987413659738927 387107478313481120489608391)
    ·
      refine ⟨580661217470221680734412587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 387107478313481120489608391 580661217470221680734412587)
      ·
        refine ⟨870991826205332521101618881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 580661217470221680734412587 870991826205332521101618881)
        ·
          refine ⟨653243869653999390826214161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 870991826205332521101618881 653243869653999390826214161)
          ·
            refine ⟨489932902240499543119660621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 653243869653999390826214161 489932902240499543119660621)
            ·
              refine ⟨183724838340187328669872733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 489932902240499543119660621 183724838340187328669872733)
              ·
                refine ⟨68896814377570248251202275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 183724838340187328669872733 68896814377570248251202275)
                ·
                  refine ⟨103345221566355372376803413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68896814377570248251202275 103345221566355372376803413)
                  ·
                    refine ⟨1211076815230727020040665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 103345221566355372376803413 1211076815230727020040665)
                    ·
                      rfl

theorem cell23_7075691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 1, 8].length) (baseStart_7075691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7075691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7075691 prefixEnd_7075691 := by exact prefixLift 7075691
  have htrace : WordTrace (prefixWord ++ tailWord_7075691) baseStart_7075691 baseEnd_7075691 := by
    simpa [prefixWord, tailWord_7075691, baseEnd_7075691] using wordTrace_append hprefix tailTrace_7075691
  have hstable : (prefixWord ++ tailWord_7075691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7075691).length < 2 ^ (prefixWord ++ tailWord_7075691).sum := by decide
  have hdescent : baseEnd_7075691 < baseStart_7075691 := by decide
  rcases family_descends (prefixWord ++ tailWord_7075691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7075692 : List Nat := [2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 3]
def baseStart_7075692 : Nat := 118140960795 + 7075692 * 2 ^ 59
def prefixEnd_7075692 : Nat := 4983230072969 + 3 ^ 40 * 7075692 * 2
def baseEnd_7075692 : Nat := 3633230959172835556209491

theorem tailTrace_7075692 : CollatzResearch.WordTrace tailWord_7075692 prefixEnd_7075692 3633230959172835556209491 := by
  unfold tailWord_7075692
  simp only [CollatzResearch.WordTrace]
  refine ⟨129035844340991895415262665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172047792454655860553683553 129035844340991895415262665)
  ·
    refine ⟨96776883255743921561446999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129035844340991895415262665 96776883255743921561446999)
    ·
      refine ⟨145165324883615882342170499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96776883255743921561446999 145165324883615882342170499)
      ·
        refine ⟨217747987325423823513255749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145165324883615882342170499 217747987325423823513255749)
        ·
          refine ⟨40827747623516966908735453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 217747987325423823513255749 40827747623516966908735453)
          ·
            refine ⟨15310405358818862590775795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40827747623516966908735453 15310405358818862590775795)
            ·
              refine ⟨22965608038228293886163693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15310405358818862590775795 22965608038228293886163693)
              ·
                refine ⟨8612103014335610207311385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22965608038228293886163693 8612103014335610207311385)
                ·
                  refine ⟨6459077260751707655483539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8612103014335610207311385 6459077260751707655483539)
                  ·
                    refine ⟨9688615891127561483225309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6459077260751707655483539 9688615891127561483225309)
                    ·
                      refine ⟨3633230959172835556209491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9688615891127561483225309 3633230959172835556209491)
                      ·
                        rfl

theorem cell23_7075692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 3].length) (baseStart_7075692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7075692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7075692 prefixEnd_7075692 := by exact prefixLift 7075692
  have htrace : WordTrace (prefixWord ++ tailWord_7075692) baseStart_7075692 baseEnd_7075692 := by
    simpa [prefixWord, tailWord_7075692, baseEnd_7075692] using wordTrace_append hprefix tailTrace_7075692
  have hstable : (prefixWord ++ tailWord_7075692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7075692).length < 2 ^ (prefixWord ++ tailWord_7075692).sum := by decide
  have hdescent : baseEnd_7075692 < baseStart_7075692 := by decide
  rcases family_descends (prefixWord ++ tailWord_7075692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7075715 : List Nat := [1, 1, 1, 3, 4, 2, 1, 1, 3, 4, 2]
def baseStart_7075715 : Nat := 118140960795 + 7075715 * 2 ^ 59
def prefixEnd_7075715 : Nat := 4983230072969 + 3 ^ 40 * 7075715 * 2
def baseEnd_7075715 : Nat := 3633242769227888966221885

theorem tailTrace_7075715 : CollatzResearch.WordTrace tailWord_7075715 prefixEnd_7075715 3633242769227888966221885 := by
  unfold tailWord_7075715
  simp only [CollatzResearch.WordTrace]
  refine ⟨258072527560900465758612599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172048351707266977172408399 258072527560900465758612599)
  ·
    refine ⟨387108791341350698637918899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258072527560900465758612599 387108791341350698637918899)
    ·
      refine ⟨580663187012026047956878349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 387108791341350698637918899 580663187012026047956878349)
      ·
        refine ⟨217748695129509767983829381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 580663187012026047956878349 217748695129509767983829381)
        ·
          refine ⟨40827880336783081496968009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 217748695129509767983829381 40827880336783081496968009)
          ·
            refine ⟨30620910252587311122726007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40827880336783081496968009 30620910252587311122726007)
            ·
              refine ⟨45931365378880966684089011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30620910252587311122726007 45931365378880966684089011)
              ·
                refine ⟨68897048068321450026133517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45931365378880966684089011 68897048068321450026133517)
                ·
                  refine ⟨25836393025620543759800069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68897048068321450026133517 25836393025620543759800069)
                  ·
                    refine ⟨4844323692303851954962513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25836393025620543759800069 4844323692303851954962513)
                    ·
                      refine ⟨3633242769227888966221885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4844323692303851954962513 3633242769227888966221885)
                      ·
                        rfl

theorem cell23_7075715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 1, 3, 4, 2].length) (baseStart_7075715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7075715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7075715 prefixEnd_7075715 := by exact prefixLift 7075715
  have htrace : WordTrace (prefixWord ++ tailWord_7075715) baseStart_7075715 baseEnd_7075715 := by
    simpa [prefixWord, tailWord_7075715, baseEnd_7075715] using wordTrace_append hprefix tailTrace_7075715
  have hstable : (prefixWord ++ tailWord_7075715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7075715).length < 2 ^ (prefixWord ++ tailWord_7075715).sum := by decide
  have hdescent : baseEnd_7075715 < baseStart_7075715 := by decide
  rcases family_descends (prefixWord ++ tailWord_7075715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7075726 : List Nat := [4, 1, 1, 5, 1, 1, 2, 2, 2, 1, 3]
def baseStart_7075726 : Nat := 118140960795 + 7075726 * 2 ^ 59
def prefixEnd_7075726 : Nat := 4983230072969 + 3 ^ 40 * 7075726 * 2
def baseEnd_7075726 : Nat := 3633248417515088423184335

theorem tailTrace_7075726 : CollatzResearch.WordTrace tailWord_7075726 prefixEnd_7075726 3633248417515088423184335 := by
  unfold tailWord_7075726
  simp only [CollatzResearch.WordTrace]
  refine ⟨32259116095482576829657879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172048619175907076424842021 32259116095482576829657879)
  ·
    refine ⟨48388674143223865244486819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32259116095482576829657879 48388674143223865244486819)
    ·
      refine ⟨72583011214835797866730229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48388674143223865244486819 72583011214835797866730229)
      ·
        refine ⟨6804657301390856050005959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 72583011214835797866730229 6804657301390856050005959)
        ·
          refine ⟨10206985952086284075008939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6804657301390856050005959 10206985952086284075008939)
          ·
            refine ⟨15310478928129426112513409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10206985952086284075008939 15310478928129426112513409)
            ·
              refine ⟨11482859196097069584385057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15310478928129426112513409 11482859196097069584385057)
              ·
                refine ⟨8612144397072802188288793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11482859196097069584385057 8612144397072802188288793)
                ·
                  refine ⟨6459108297804601641216595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8612144397072802188288793 6459108297804601641216595)
                  ·
                    refine ⟨9688662446706902461824893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6459108297804601641216595 9688662446706902461824893)
                    ·
                      refine ⟨3633248417515088423184335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9688662446706902461824893 3633248417515088423184335)
                      ·
                        rfl

theorem cell23_7075726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_7075726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7075726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7075726 prefixEnd_7075726 := by exact prefixLift 7075726
  have htrace : WordTrace (prefixWord ++ tailWord_7075726) baseStart_7075726 baseEnd_7075726 := by
    simpa [prefixWord, tailWord_7075726, baseEnd_7075726] using wordTrace_append hprefix tailTrace_7075726
  have hstable : (prefixWord ++ tailWord_7075726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7075726).length < 2 ^ (prefixWord ++ tailWord_7075726).sum := by decide
  have hdescent : baseEnd_7075726 < baseStart_7075726 := by decide
  rcases family_descends (prefixWord ++ tailWord_7075726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7075768 : List Nat := [2, 1, 2, 1, 2, 3, 3, 1, 1, 7]
def baseStart_7075768 : Nat := 118140960795 + 7075768 * 2 ^ 59
def prefixEnd_7075768 : Nat := 4983230072969 + 3 ^ 40 * 7075768 * 2
def baseEnd_7075768 : Nat := 1211089994567525752953047

theorem tailTrace_7075768 : CollatzResearch.WordTrace tailWord_7075768 prefixEnd_7075768 1211089994567525752953047 := by
  unfold tailWord_7075768
  simp only [CollatzResearch.WordTrace]
  refine ⟨129037230314854227905145979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172049640419805637206861305 129037230314854227905145979)
  ·
    refine ⟨193555845472281341857718969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129037230314854227905145979 193555845472281341857718969)
    ·
      refine ⟨145166884104211006393289227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193555845472281341857718969 145166884104211006393289227)
      ·
        refine ⟨217750326156316509589933841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145166884104211006393289227 217750326156316509589933841)
        ·
          refine ⟨163312744617237382192450381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217750326156316509589933841 163312744617237382192450381)
          ·
            refine ⟨61242279231464018322168893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 163312744617237382192450381 61242279231464018322168893)
            ·
              refine ⟨22965854711799006870813335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61242279231464018322168893 22965854711799006870813335)
              ·
                refine ⟨34448782067698510306220003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22965854711799006870813335 34448782067698510306220003)
                ·
                  refine ⟨51673173101547765459330005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34448782067698510306220003 51673173101547765459330005)
                  ·
                    refine ⟨1211089994567525752953047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51673173101547765459330005 1211089994567525752953047)
                    ·
                      rfl

theorem cell23_7075768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 1, 1, 7].length) (baseStart_7075768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7075768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7075768 prefixEnd_7075768 := by exact prefixLift 7075768
  have htrace : WordTrace (prefixWord ++ tailWord_7075768) baseStart_7075768 baseEnd_7075768 := by
    simpa [prefixWord, tailWord_7075768, baseEnd_7075768] using wordTrace_append hprefix tailTrace_7075768
  have hstable : (prefixWord ++ tailWord_7075768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7075768).length < 2 ^ (prefixWord ++ tailWord_7075768).sum := by decide
  have hdescent : baseEnd_7075768 < baseStart_7075768 := by decide
  rcases family_descends (prefixWord ++ tailWord_7075768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7075875 : List Nat := [1, 1, 1, 4, 3, 1, 3, 1, 3, 5]
def baseStart_7075875 : Nat := 118140960795 + 7075875 * 2 ^ 59
def prefixEnd_7075875 : Nat := 4983230072969 + 3 ^ 40 * 7075875 * 2
def baseEnd_7075875 : Nat := 1211108308710869446740383

theorem tailTrace_7075875 : CollatzResearch.WordTrace tailWord_7075875 prefixEnd_7075875 1211108308710869446740383 := by
  unfold tailWord_7075875
  simp only [CollatzResearch.WordTrace]
  refine ⟨258078363240320813084437079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172052242160213875389624719 258078363240320813084437079)
  ·
    refine ⟨387117544860481219626655619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258078363240320813084437079 387117544860481219626655619)
    ·
      refine ⟨580676317290721829439983429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 387117544860481219626655619 580676317290721829439983429)
      ·
        refine ⟨108876809492010343019996893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 580676317290721829439983429 108876809492010343019996893)
        ·
          refine ⟨40828803559503878632498835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108876809492010343019996893 40828803559503878632498835)
          ·
            refine ⟨61243205339255817948748253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40828803559503878632498835 61243205339255817948748253)
            ·
              refine ⟨22966202002220931730780595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61243205339255817948748253 22966202002220931730780595)
              ·
                refine ⟨34449303003331397596170893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22966202002220931730780595 34449303003331397596170893)
                ·
                  refine ⟨12918488626249274098564085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34449303003331397596170893 12918488626249274098564085)
                  ·
                    refine ⟨1211108308710869446740383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12918488626249274098564085 1211108308710869446740383)
                    ·
                      rfl

theorem cell23_7075875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 1, 3, 5].length) (baseStart_7075875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7075875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7075875 prefixEnd_7075875 := by exact prefixLift 7075875
  have htrace : WordTrace (prefixWord ++ tailWord_7075875) baseStart_7075875 baseEnd_7075875 := by
    simpa [prefixWord, tailWord_7075875, baseEnd_7075875] using wordTrace_append hprefix tailTrace_7075875
  have hstable : (prefixWord ++ tailWord_7075875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7075875).length < 2 ^ (prefixWord ++ tailWord_7075875).sum := by decide
  have hdescent : baseEnd_7075875 < baseStart_7075875 := by decide
  rcases family_descends (prefixWord ++ tailWord_7075875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7075929 : List Nat := [1, 2, 1, 2, 2, 1, 5, 2, 3, 2, 2]
def baseStart_7075929 : Nat := 118140960795 + 7075929 * 2 ^ 59
def prefixEnd_7075929 : Nat := 4983230072969 + 3 ^ 40 * 7075929 * 2
def baseEnd_7075929 : Nat := 3633352654087951128945901

theorem tailTrace_7075929 : CollatzResearch.WordTrace tailWord_7075929 prefixEnd_7075929 3633352654087951128945901 := by
  unfold tailWord_7075929
  simp only [CollatzResearch.WordTrace]
  refine ⟨258080332782125180306902841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172053555188083453537935227 258080332782125180306902841)
  ·
    refine ⟨193560249586593885230177131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258080332782125180306902841 193560249586593885230177131)
    ·
      refine ⟨290340374379890827845265697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193560249586593885230177131 290340374379890827845265697)
      ·
        refine ⟨217755280784918120883949273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 290340374379890827845265697 217755280784918120883949273)
        ·
          refine ⟨163316460588688590662961955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217755280784918120883949273 163316460588688590662961955)
          ·
            refine ⟨244974690883032885994442933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163316460588688590662961955 244974690883032885994442933)
            ·
              refine ⟨22966377270284333061979025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 244974690883032885994442933 22966377270284333061979025)
              ·
                refine ⟨17224782952713249796484269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22966377270284333061979025 17224782952713249796484269)
                ·
                  refine ⟨6459293607267468673681601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17224782952713249796484269 6459293607267468673681601)
                  ·
                    refine ⟨4844470205450601505261201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6459293607267468673681601 4844470205450601505261201)
                    ·
                      refine ⟨3633352654087951128945901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4844470205450601505261201 3633352654087951128945901)
                      ·
                        rfl

theorem cell23_7075929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 2, 3, 2, 2].length) (baseStart_7075929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7075929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7075929 prefixEnd_7075929 := by exact prefixLift 7075929
  have htrace : WordTrace (prefixWord ++ tailWord_7075929) baseStart_7075929 baseEnd_7075929 := by
    simpa [prefixWord, tailWord_7075929, baseEnd_7075929] using wordTrace_append hprefix tailTrace_7075929
  have hstable : (prefixWord ++ tailWord_7075929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7075929).length < 2 ^ (prefixWord ++ tailWord_7075929).sum := by decide
  have hdescent : baseEnd_7075929 < baseStart_7075929 := by decide
  rcases family_descends (prefixWord ++ tailWord_7075929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7075933 : List Nat := [1, 4, 4, 1, 1, 3, 1, 1, 2, 3, 2]
def baseStart_7075933 : Nat := 118140960795 + 7075933 * 2 ^ 59
def prefixEnd_7075933 : Nat := 4983230072969 + 3 ^ 40 * 7075933 * 2
def baseEnd_7075933 : Nat := 3633354708010569113295883

theorem tailTrace_7075933 : CollatzResearch.WordTrace tailWord_7075933 prefixEnd_7075933 3633354708010569113295883 := by
  unfold tailWord_7075933
  simp only [CollatzResearch.WordTrace]
  refine ⟨258080478674110688990048453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172053652449407125993365635 258080478674110688990048453)
  ·
    refine ⟨48390089751395754185634085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 258080478674110688990048453 48390089751395754185634085)
    ·
      refine ⟨9073141828386703909806391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48390089751395754185634085 9073141828386703909806391)
      ·
        refine ⟨13609712742580055864709587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9073141828386703909806391 13609712742580055864709587)
        ·
          refine ⟨20414569113870083797064381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13609712742580055864709587 20414569113870083797064381)
          ·
            refine ⟨7655463417701281423899143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20414569113870083797064381 7655463417701281423899143)
            ·
              refine ⟨11483195126551922135848715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7655463417701281423899143 11483195126551922135848715)
              ·
                refine ⟨17224792689827883203773073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11483195126551922135848715 17224792689827883203773073)
                ·
                  refine ⟨12918594517370912402829805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17224792689827883203773073 12918594517370912402829805)
                  ·
                    refine ⟨4844472944014092151061177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12918594517370912402829805 4844472944014092151061177)
                    ·
                      refine ⟨3633354708010569113295883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4844472944014092151061177 3633354708010569113295883)
                      ·
                        rfl

theorem cell23_7075933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 1, 1, 2, 3, 2].length) (baseStart_7075933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7075933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7075933 prefixEnd_7075933 := by exact prefixLift 7075933
  have htrace : WordTrace (prefixWord ++ tailWord_7075933) baseStart_7075933 baseEnd_7075933 := by
    simpa [prefixWord, tailWord_7075933, baseEnd_7075933] using wordTrace_append hprefix tailTrace_7075933
  have hstable : (prefixWord ++ tailWord_7075933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7075933).length < 2 ^ (prefixWord ++ tailWord_7075933).sum := by decide
  have hdescent : baseEnd_7075933 < baseStart_7075933 := by decide
  rcases family_descends (prefixWord ++ tailWord_7075933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7075949 : List Nat := [1, 5, 1, 1, 2, 1, 3, 3, 1, 2, 3]
def baseStart_7075949 : Nat := 118140960795 + 7075949 * 2 ^ 59
def prefixEnd_7075949 : Nat := 4983230072969 + 3 ^ 40 * 7075949 * 2
def baseEnd_7075949 : Nat := 3633362923701041050695809

theorem tailTrace_7075949 : CollatzResearch.WordTrace tailWord_7075949 prefixEnd_7075949 3633362923701041050695809 := by
  unfold tailWord_7075949
  simp only [CollatzResearch.WordTrace]
  refine ⟨258081062242052723722630901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172054041494701815815087267 258081062242052723722630901)
  ·
    refine ⟨24195099585192442848996647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 258081062242052723722630901 24195099585192442848996647)
    ·
      refine ⟨36292649377788664273494971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24195099585192442848996647 36292649377788664273494971)
      ·
        refine ⟨54438974066682996410242457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36292649377788664273494971 54438974066682996410242457)
        ·
          refine ⟨40829230550012247307681843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54438974066682996410242457 40829230550012247307681843)
          ·
            refine ⟨61243845825018370961522765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40829230550012247307681843 61243845825018370961522765)
            ·
              refine ⟨22966442184381889110571037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61243845825018370961522765 22966442184381889110571037)
              ·
                refine ⟨8612415819143208416464139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22966442184381889110571037 8612415819143208416464139)
                ·
                  refine ⟨12918623728714812624696209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8612415819143208416464139 12918623728714812624696209)
                  ·
                    refine ⟨9688967796536109468522157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12918623728714812624696209 9688967796536109468522157)
                    ·
                      refine ⟨3633362923701041050695809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9688967796536109468522157 3633362923701041050695809)
                      ·
                        rfl

theorem cell23_7075949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 3, 1, 2, 3].length) (baseStart_7075949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7075949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7075949 prefixEnd_7075949 := by exact prefixLift 7075949
  have htrace : WordTrace (prefixWord ++ tailWord_7075949) baseStart_7075949 baseEnd_7075949 := by
    simpa [prefixWord, tailWord_7075949, baseEnd_7075949] using wordTrace_append hprefix tailTrace_7075949
  have hstable : (prefixWord ++ tailWord_7075949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7075949).length < 2 ^ (prefixWord ++ tailWord_7075949).sum := by decide
  have hdescent : baseEnd_7075949 < baseStart_7075949 := by decide
  rcases family_descends (prefixWord ++ tailWord_7075949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7076014 : List Nat := [4, 1, 4, 2, 1, 1, 3, 2, 1, 2, 2]
def baseStart_7076014 : Nat := 118140960795 + 7076014 * 2 ^ 59
def prefixEnd_7076014 : Nat := 4983230072969 + 3 ^ 40 * 7076014 * 2
def baseEnd_7076014 : Nat := 3633396299943583296383011

theorem tailTrace_7076014 : CollatzResearch.WordTrace tailWord_7076014 prefixEnd_7076014 3633396299943583296383011 := by
  unfold tailWord_7076014
  simp only [CollatzResearch.WordTrace]
  refine ⟨32260429123352154977968387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172055621991211493215831397 32260429123352154977968387)
  ·
    refine ⟨48390643685028232466952581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32260429123352154977968387 48390643685028232466952581)
    ·
      refine ⟨9073245690942793587553609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48390643685028232466952581 9073245690942793587553609)
      ·
        refine ⟨6804934268207095190665207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9073245690942793587553609 6804934268207095190665207)
        ·
          refine ⟨10207401402310642785997811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6804934268207095190665207 10207401402310642785997811)
          ·
            refine ⟨15311102103465964178996717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10207401402310642785997811 15311102103465964178996717)
            ·
              refine ⟨5741663288799736567123769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15311102103465964178996717 5741663288799736567123769)
              ·
                refine ⟨4306247466599802425342827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5741663288799736567123769 4306247466599802425342827)
                ·
                  refine ⟨6459371199899703638014241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4306247466599802425342827 6459371199899703638014241)
                  ·
                    refine ⟨4844528399924777728510681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6459371199899703638014241 4844528399924777728510681)
                    ·
                      refine ⟨3633396299943583296383011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4844528399924777728510681 3633396299943583296383011)
                      ·
                        rfl

theorem cell23_7076014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 3, 2, 1, 2, 2].length) (baseStart_7076014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7076014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7076014 prefixEnd_7076014 := by exact prefixLift 7076014
  have htrace : WordTrace (prefixWord ++ tailWord_7076014) baseStart_7076014 baseEnd_7076014 := by
    simpa [prefixWord, tailWord_7076014, baseEnd_7076014] using wordTrace_append hprefix tailTrace_7076014
  have hstable : (prefixWord ++ tailWord_7076014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7076014).length < 2 ^ (prefixWord ++ tailWord_7076014).sum := by decide
  have hdescent : baseEnd_7076014 < baseStart_7076014 := by decide
  rcases family_descends (prefixWord ++ tailWord_7076014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7076030 : List Nat := [4, 2, 1, 1, 4, 2, 2, 1, 2, 1, 3]
def baseStart_7076030 : Nat := 118140960795 + 7076030 * 2 ^ 59
def prefixEnd_7076030 : Nat := 4983230072969 + 3 ^ 40 * 7076030 * 2
def baseEnd_7076030 : Nat := 3633404515634055233782937

theorem tailTrace_7076030 : CollatzResearch.WordTrace tailWord_7076030 prefixEnd_7076030 3633404515634055233782937 := by
  unfold tailWord_7076030
  simp only [CollatzResearch.WordTrace]
  refine ⟨32260502069344909319541193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172056011036506183037553029 32260502069344909319541193)
  ·
    refine ⟨24195376552008681989655895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32260502069344909319541193 24195376552008681989655895)
    ·
      refine ⟨36293064828013022984483843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24195376552008681989655895 36293064828013022984483843)
      ·
        refine ⟨54439597242019534476725765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36293064828013022984483843 54439597242019534476725765)
        ·
          refine ⟨10207424482878662714386081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54439597242019534476725765 10207424482878662714386081)
          ·
            refine ⟨7655568362158997035789561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10207424482878662714386081 7655568362158997035789561)
            ·
              refine ⟨5741676271619247776842171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7655568362158997035789561 5741676271619247776842171)
              ·
                refine ⟨8612514407428871665263257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5741676271619247776842171 8612514407428871665263257)
                ·
                  refine ⟨6459385805571653748947443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8612514407428871665263257 6459385805571653748947443)
                  ·
                    refine ⟨9689078708357480623421165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6459385805571653748947443 9689078708357480623421165)
                    ·
                      refine ⟨3633404515634055233782937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9689078708357480623421165 3633404515634055233782937)
                      ·
                        rfl

theorem cell23_7076030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 2, 1, 2, 1, 3].length) (baseStart_7076030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7076030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7076030 prefixEnd_7076030 := by exact prefixLift 7076030
  have htrace : WordTrace (prefixWord ++ tailWord_7076030) baseStart_7076030 baseEnd_7076030 := by
    simpa [prefixWord, tailWord_7076030, baseEnd_7076030] using wordTrace_append hprefix tailTrace_7076030
  have hstable : (prefixWord ++ tailWord_7076030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7076030).length < 2 ^ (prefixWord ++ tailWord_7076030).sum := by decide
  have hdescent : baseEnd_7076030 < baseStart_7076030 := by decide
  rcases family_descends (prefixWord ++ tailWord_7076030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7076079 : List Nat := [1, 1, 2, 1, 6, 1, 1, 1, 2, 5, 2]
def baseStart_7076079 : Nat := 118140960795 + 7076079 * 2 ^ 59
def prefixEnd_7076079 : Nat := 4983230072969 + 3 ^ 40 * 7076079 * 2
def baseEnd_7076079 : Nat := 3633429676186125542070211

theorem tailTrace_7076079 : CollatzResearch.WordTrace tailWord_7076079 prefixEnd_7076079 3633429676186125542070211 := by
  unfold tailWord_7076079
  simp only [CollatzResearch.WordTrace]
  refine ⟨258085803731581755924863291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172057202487721170616575527 258085803731581755924863291)
  ·
    refine ⟨387128705597372633887294937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258085803731581755924863291 387128705597372633887294937)
    ·
      refine ⟨290346529198029475415471203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 387128705597372633887294937 290346529198029475415471203)
      ·
        refine ⟨435519793797044213123206805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290346529198029475415471203 435519793797044213123206805)
        ·
          refine ⟨20414990334236447490150319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 435519793797044213123206805 20414990334236447490150319)
          ·
            refine ⟨30622485501354671235225479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20414990334236447490150319 30622485501354671235225479)
            ·
              refine ⟨45933728252032006852838219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30622485501354671235225479 45933728252032006852838219)
              ·
                refine ⟨68900592378048010279257329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45933728252032006852838219 68900592378048010279257329)
                ·
                  refine ⟨51675444283536007709442997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68900592378048010279257329 51675444283536007709442997)
                  ·
                    refine ⟨4844572901581500722760281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51675444283536007709442997 4844572901581500722760281)
                    ·
                      refine ⟨3633429676186125542070211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4844572901581500722760281 3633429676186125542070211)
                      ·
                        rfl

theorem cell23_7076079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 1, 2, 5, 2].length) (baseStart_7076079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7076079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7076079 prefixEnd_7076079 := by exact prefixLift 7076079
  have htrace : WordTrace (prefixWord ++ tailWord_7076079) baseStart_7076079 baseEnd_7076079 := by
    simpa [prefixWord, tailWord_7076079, baseEnd_7076079] using wordTrace_append hprefix tailTrace_7076079
  have hstable : (prefixWord ++ tailWord_7076079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7076079).length < 2 ^ (prefixWord ++ tailWord_7076079).sum := by decide
  have hdescent : baseEnd_7076079 < baseStart_7076079 := by decide
  rcases family_descends (prefixWord ++ tailWord_7076079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7076129 : List Nat := [1, 2, 3, 2, 1, 1, 2, 4, 2, 2, 3]
def baseStart_7076129 : Nat := 118140960795 + 7076129 * 2 ^ 59
def prefixEnd_7076129 : Nat := 4983230072969 + 3 ^ 40 * 7076129 * 2
def baseEnd_7076129 : Nat := 3633455350218850346444981

theorem tailTrace_7076129 : CollatzResearch.WordTrace tailWord_7076129 prefixEnd_7076129 3633455350218850346444981 := by
  unfold tailWord_7076129
  simp only [CollatzResearch.WordTrace]
  refine ⟨258087627381400614464183441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172058418254267076309455627 258087627381400614464183441)
  ·
    refine ⟨193565720536050460848137581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258087627381400614464183441 193565720536050460848137581)
    ·
      refine ⟨72587145201018922818051593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193565720536050460848137581 72587145201018922818051593)
      ·
        refine ⟨54440358900764192113538695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72587145201018922818051593 54440358900764192113538695)
        ·
          refine ⟨81660538351146288170308043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54440358900764192113538695 81660538351146288170308043)
          ·
            refine ⟨122490807526719432255462065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81660538351146288170308043 122490807526719432255462065)
            ·
              refine ⟨91868105645039574191596549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122490807526719432255462065 91868105645039574191596549)
              ·
                refine ⟨17225269808444920160924353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 91868105645039574191596549 17225269808444920160924353)
                ·
                  refine ⟨12918952356333690120693265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17225269808444920160924353 12918952356333690120693265)
                  ·
                    refine ⟨9689214267250267590519949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12918952356333690120693265 9689214267250267590519949)
                    ·
                      refine ⟨3633455350218850346444981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9689214267250267590519949 3633455350218850346444981)
                      ·
                        rfl

theorem cell23_7076129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 4, 2, 2, 3].length) (baseStart_7076129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7076129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7076129 prefixEnd_7076129 := by exact prefixLift 7076129
  have htrace : WordTrace (prefixWord ++ tailWord_7076129) baseStart_7076129 baseEnd_7076129 := by
    simpa [prefixWord, tailWord_7076129, baseEnd_7076129] using wordTrace_append hprefix tailTrace_7076129
  have hstable : (prefixWord ++ tailWord_7076129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7076129).length < 2 ^ (prefixWord ++ tailWord_7076129).sum := by decide
  have hdescent : baseEnd_7076129 < baseStart_7076129 := by decide
  rcases family_descends (prefixWord ++ tailWord_7076129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7076213 : List Nat := [1, 3, 4, 1, 2, 3, 1, 2, 1, 5]
def baseStart_7076213 : Nat := 118140960795 + 7076213 * 2 ^ 59
def prefixEnd_7076213 : Nat := 4983230072969 + 3 ^ 40 * 7076213 * 2
def baseEnd_7076213 : Nat := 1211166160864609339264865

theorem tailTrace_7076213 : CollatzResearch.WordTrace tailWord_7076213 prefixEnd_7076213 1211166160864609339264865 := by
  unfold tailWord_7076213
  simp only [CollatzResearch.WordTrace]
  refine ⟨258090691113096296810241293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172060460742064197873494195 258090691113096296810241293)
  ·
    refine ⟨96784009167411111303840485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 258090691113096296810241293 96784009167411111303840485)
    ·
      refine ⟨18147001718889583369470091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96784009167411111303840485 18147001718889583369470091)
      ·
        refine ⟨27220502578334375054205137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18147001718889583369470091 27220502578334375054205137)
        ·
          refine ⟨20415376933750781290653853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27220502578334375054205137 20415376933750781290653853)
          ·
            refine ⟨7655766350156542983995195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20415376933750781290653853 7655766350156542983995195)
            ·
              refine ⟨11483649525234814475992793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7655766350156542983995195 11483649525234814475992793)
              ·
                refine ⟨8612737143926110856994595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11483649525234814475992793 8612737143926110856994595)
                ·
                  refine ⟨12919105715889166285491893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8612737143926110856994595 12919105715889166285491893)
                  ·
                    refine ⟨1211166160864609339264865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12919105715889166285491893 1211166160864609339264865)
                    ·
                      rfl

theorem cell23_7076213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 1, 2, 1, 5].length) (baseStart_7076213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7076213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7076213 prefixEnd_7076213 := by exact prefixLift 7076213
  have htrace : WordTrace (prefixWord ++ tailWord_7076213) baseStart_7076213 baseEnd_7076213 := by
    simpa [prefixWord, tailWord_7076213, baseEnd_7076213] using wordTrace_append hprefix tailTrace_7076213
  have hstable : (prefixWord ++ tailWord_7076213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7076213).length < 2 ^ (prefixWord ++ tailWord_7076213).sum := by decide
  have hdescent : baseEnd_7076213 < baseStart_7076213 := by decide
  rcases family_descends (prefixWord ++ tailWord_7076213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7076233 : List Nat := [1, 2, 1, 1, 6, 2, 3, 1, 1, 1, 4]
def baseStart_7076233 : Nat := 118140960795 + 7076233 * 2 ^ 59
def prefixEnd_7076233 : Nat := 4983230072969 + 3 ^ 40 * 7076233 * 2
def baseEnd_7076233 : Nat := 3633508752206917939544503

theorem tailTrace_7076233 : CollatzResearch.WordTrace tailWord_7076233 prefixEnd_7076233 3633508752206917939544503 := by
  unfold tailWord_7076233
  simp only [CollatzResearch.WordTrace]
  refine ⟨258091420573023840225969353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172060947048682560150646235 258091420573023840225969353)
  ·
    refine ⟨193568565429767880169477015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258091420573023840225969353 193568565429767880169477015)
    ·
      refine ⟨290352848144651820254215523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193568565429767880169477015 290352848144651820254215523)
      ·
        refine ⟨435529272216977730381323285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290352848144651820254215523 435529272216977730381323285)
        ·
          refine ⟨20415434635170831111624529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 435529272216977730381323285 20415434635170831111624529)
          ·
            refine ⟨15311575976378123333718397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20415434635170831111624529 15311575976378123333718397)
            ·
              refine ⟨5741840991141796250144399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15311575976378123333718397 5741840991141796250144399)
              ·
                refine ⟨8612761486712694375216599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5741840991141796250144399 8612761486712694375216599)
                ·
                  refine ⟨12919142230069041562824899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8612761486712694375216599 12919142230069041562824899)
                  ·
                    refine ⟨19378713345103562344237349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12919142230069041562824899 19378713345103562344237349)
                    ·
                      refine ⟨3633508752206917939544503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19378713345103562344237349 3633508752206917939544503)
                      ·
                        rfl

theorem cell23_7076233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 3, 1, 1, 1, 4].length) (baseStart_7076233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7076233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7076233 prefixEnd_7076233 := by exact prefixLift 7076233
  have htrace : WordTrace (prefixWord ++ tailWord_7076233) baseStart_7076233 baseEnd_7076233 := by
    simpa [prefixWord, tailWord_7076233, baseEnd_7076233] using wordTrace_append hprefix tailTrace_7076233
  have hstable : (prefixWord ++ tailWord_7076233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7076233).length < 2 ^ (prefixWord ++ tailWord_7076233).sum := by decide
  have hdescent : baseEnd_7076233 < baseStart_7076233 := by decide
  rcases family_descends (prefixWord ++ tailWord_7076233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7076236 : List Nat := [2, 2, 1, 2, 1, 6, 1, 1, 1, 1, 5]
def baseStart_7076236 : Nat := 118140960795 + 7076236 * 2 ^ 59
def prefixEnd_7076236 : Nat := 4983230072969 + 3 ^ 40 * 7076236 * 2
def baseEnd_7076236 : Nat := 3633510292648881427806989

theorem tailTrace_7076236 : CollatzResearch.WordTrace tailWord_7076236 prefixEnd_7076236 3633510292648881427806989 := by
  unfold tailWord_7076236
  simp only [CollatzResearch.WordTrace]
  refine ⟨129045764996006485869164281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172061019994675314492219041 129045764996006485869164281)
  ·
    refine ⟨96784323747004864401873211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129045764996006485869164281 96784323747004864401873211)
    ·
      refine ⟨145176485620507296602809817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96784323747004864401873211 145176485620507296602809817)
      ·
        refine ⟨108882364215380472452107363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145176485620507296602809817 108882364215380472452107363)
        ·
          refine ⟨163323546323070708678161045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108882364215380472452107363 163323546323070708678161045)
          ·
            refine ⟨7655791233893939469288799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 163323546323070708678161045 7655791233893939469288799)
            ·
              refine ⟨11483686850840909203933199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7655791233893939469288799 11483686850840909203933199)
              ·
                refine ⟨17225530276261363805899799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11483686850840909203933199 17225530276261363805899799)
                ·
                  refine ⟨25838295414392045708849699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17225530276261363805899799 25838295414392045708849699)
                  ·
                    refine ⟨38757443121588068563274549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25838295414392045708849699 38757443121588068563274549)
                    ·
                      refine ⟨3633510292648881427806989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38757443121588068563274549 3633510292648881427806989)
                      ·
                        rfl

theorem cell23_7076236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 1, 1, 1, 1, 5].length) (baseStart_7076236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7076236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7076236 prefixEnd_7076236 := by exact prefixLift 7076236
  have htrace : WordTrace (prefixWord ++ tailWord_7076236) baseStart_7076236 baseEnd_7076236 := by
    simpa [prefixWord, tailWord_7076236, baseEnd_7076236] using wordTrace_append hprefix tailTrace_7076236
  have hstable : (prefixWord ++ tailWord_7076236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7076236).length < 2 ^ (prefixWord ++ tailWord_7076236).sum := by decide
  have hdescent : baseEnd_7076236 < baseStart_7076236 := by decide
  rcases family_descends (prefixWord ++ tailWord_7076236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7076244 : List Nat := [2, 4, 2, 1, 3, 2, 2, 2, 1, 1, 3]
def baseStart_7076244 : Nat := 118140960795 + 7076244 * 2 ^ 59
def prefixEnd_7076244 : Nat := 4983230072969 + 3 ^ 40 * 7076244 * 2
def baseEnd_7076244 : Nat := 3633514400494117396506953

theorem tailTrace_7076244 : CollatzResearch.WordTrace tailWord_7076244 prefixEnd_7076244 3633514400494117396506953 := by
  unfold tailWord_7076244
  simp only [CollatzResearch.WordTrace]
  refine ⟨129045910887991994552309893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172061214517322659403079857 129045910887991994552309893)
  ·
    refine ⟨24196108291498498978558105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 129045910887991994552309893 24196108291498498978558105)
    ·
      refine ⟨18147081218623874233918579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24196108291498498978558105 18147081218623874233918579)
      ·
        refine ⟨27220621827935811350877869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18147081218623874233918579 27220621827935811350877869)
        ·
          refine ⟨10207733185475929256579201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27220621827935811350877869 10207733185475929256579201)
          ·
            refine ⟨7655799889106946942434401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10207733185475929256579201 7655799889106946942434401)
            ·
              refine ⟨5741849916830210206825801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7655799889106946942434401 5741849916830210206825801)
              ·
                refine ⟨4306387437622657655119351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5741849916830210206825801 4306387437622657655119351)
                ·
                  refine ⟨6459581156433986482679027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4306387437622657655119351 6459581156433986482679027)
                  ·
                    refine ⟨9689371734650979724018541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6459581156433986482679027 9689371734650979724018541)
                    ·
                      refine ⟨3633514400494117396506953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9689371734650979724018541 3633514400494117396506953)
                      ·
                        rfl

theorem cell23_7076244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 2, 2, 1, 1, 3].length) (baseStart_7076244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7076244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7076244 prefixEnd_7076244 := by exact prefixLift 7076244
  have htrace : WordTrace (prefixWord ++ tailWord_7076244) baseStart_7076244 baseEnd_7076244 := by
    simpa [prefixWord, tailWord_7076244, baseEnd_7076244] using wordTrace_append hprefix tailTrace_7076244
  have hstable : (prefixWord ++ tailWord_7076244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7076244).length < 2 ^ (prefixWord ++ tailWord_7076244).sum := by decide
  have hdescent : baseEnd_7076244 < baseStart_7076244 := by decide
  rcases family_descends (prefixWord ++ tailWord_7076244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7076249 : List Nat := [1, 2, 1, 2, 1, 4, 1, 2, 3, 3, 3]
def baseStart_7076249 : Nat := 118140960795 + 7076249 * 2 ^ 59
def prefixEnd_7076249 : Nat := 4983230072969 + 3 ^ 40 * 7076249 * 2
def baseEnd_7076249 : Nat := 3633516967897389876944429

theorem tailTrace_7076249 : CollatzResearch.WordTrace tailWord_7076249 prefixEnd_7076249 3633516967897389876944429 := by
  unfold tailWord_7076249
  simp only [CollatzResearch.WordTrace]
  refine ⟨258092004140965874958551801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172061336093977249972367867 258092004140965874958551801)
  ·
    refine ⟨193569003105724406218913851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258092004140965874958551801 193569003105724406218913851)
    ·
      refine ⟨290353504658586609328370777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193569003105724406218913851 290353504658586609328370777)
      ·
        refine ⟨217765128493939956996278083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 290353504658586609328370777 217765128493939956996278083)
        ·
          refine ⟨326647692740909935494417125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217765128493939956996278083 326647692740909935494417125)
          ·
            refine ⟨61246442388920612905203211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 326647692740909935494417125 61246442388920612905203211)
            ·
              refine ⟨91869663583380919357804817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61246442388920612905203211 91869663583380919357804817)
              ·
                refine ⟨68902247687535689518353613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91869663583380919357804817 68902247687535689518353613)
                ·
                  refine ⟨25838342882825883569382605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68902247687535689518353613 25838342882825883569382605)
                  ·
                    refine ⟨9689378581059706338518477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25838342882825883569382605 9689378581059706338518477)
                    ·
                      refine ⟨3633516967897389876944429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9689378581059706338518477 3633516967897389876944429)
                      ·
                        rfl

theorem cell23_7076249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 2, 3, 3, 3].length) (baseStart_7076249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7076249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7076249 prefixEnd_7076249 := by exact prefixLift 7076249
  have htrace : WordTrace (prefixWord ++ tailWord_7076249) baseStart_7076249 baseEnd_7076249 := by
    simpa [prefixWord, tailWord_7076249, baseEnd_7076249] using wordTrace_append hprefix tailTrace_7076249
  have hstable : (prefixWord ++ tailWord_7076249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7076249).length < 2 ^ (prefixWord ++ tailWord_7076249).sum := by decide
  have hdescent : baseEnd_7076249 < baseStart_7076249 := by decide
  rcases family_descends (prefixWord ++ tailWord_7076249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7076346 : List Nat := [3, 1, 1, 1, 1, 2, 2, 7, 5]
def baseStart_7076346 : Nat := 118140960795 + 7076346 * 2 ^ 59
def prefixEnd_7076346 : Nat := 4983230072969 + 3 ^ 40 * 7076346 * 2
def baseEnd_7076346 : Nat := 403729641724541777492387

theorem tailTrace_7076346 : CollatzResearch.WordTrace tailWord_7076346 prefixEnd_7076346 403729641724541777492387 := by
  unfold tailWord_7076346
  simp only [CollatzResearch.WordTrace]
  refine ⟨64523885505403615131208223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172063694681076307016555261 64523885505403615131208223)
  ·
    refine ⟨96785828258105422696812335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64523885505403615131208223 96785828258105422696812335)
    ·
      refine ⟨145178742387158134045218503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96785828258105422696812335 145178742387158134045218503)
      ·
        refine ⟨217768113580737201067827755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145178742387158134045218503 217768113580737201067827755)
        ·
          refine ⟨326652170371105801601741633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217768113580737201067827755 326652170371105801601741633)
          ·
            refine ⟨244989127778329351201306225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 326652170371105801601741633 244989127778329351201306225)
            ·
              refine ⟨183741845833747013400979669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 244989127778329351201306225 183741845833747013400979669)
              ·
                refine ⟨4306449511728445626585461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 183741845833747013400979669 4306449511728445626585461)
                ·
                  refine ⟨403729641724541777492387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4306449511728445626585461 403729641724541777492387)
                  ·
                    rfl

theorem cell23_7076346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 7, 5].length) (baseStart_7076346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7076346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7076346 prefixEnd_7076346 := by exact prefixLift 7076346
  have htrace : WordTrace (prefixWord ++ tailWord_7076346) baseStart_7076346 baseEnd_7076346 := by
    simpa [prefixWord, tailWord_7076346, baseEnd_7076346] using wordTrace_append hprefix tailTrace_7076346
  have hstable : (prefixWord ++ tailWord_7076346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7076346).length < 2 ^ (prefixWord ++ tailWord_7076346).sum := by decide
  have hdescent : baseEnd_7076346 < baseStart_7076346 := by decide
  rcases family_descends (prefixWord ++ tailWord_7076346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7076389 : List Nat := [1, 3, 1, 2, 2, 1, 2, 1, 2, 8]
def baseStart_7076389 : Nat := 118140960795 + 7076389 * 2 ^ 59
def prefixEnd_7076389 : Nat := 4983230072969 + 3 ^ 40 * 7076389 * 2
def baseEnd_7076389 : Nat := 1211196285063006443064595

theorem tailTrace_7076389 : CollatzResearch.WordTrace tailWord_7076389 prefixEnd_7076389 1211196285063006443064595 := by
  unfold tailWord_7076389
  simp only [CollatzResearch.WordTrace]
  refine ⟨258097110360458678868648221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172064740240305785912432147 258097110360458678868648221)
  ·
    refine ⟨96786416385172004575743083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 258097110360458678868648221 96786416385172004575743083)
    ·
      refine ⟨145179624577758006863614625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96786416385172004575743083 145179624577758006863614625)
      ·
        refine ⟨108884718433318505147710969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145179624577758006863614625 108884718433318505147710969)
        ·
          refine ⟨81663538824988878860783227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108884718433318505147710969 81663538824988878860783227)
          ·
            refine ⟨122495308237483318291174841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81663538824988878860783227 122495308237483318291174841)
            ·
              refine ⟨91871481178112488718381131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122495308237483318291174841 91871481178112488718381131)
              ·
                refine ⟨137807221767168733077571697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91871481178112488718381131 137807221767168733077571697)
                ·
                  refine ⟨103355416325376549808178773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 137807221767168733077571697 103355416325376549808178773)
                  ·
                    refine ⟨1211196285063006443064595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 103355416325376549808178773 1211196285063006443064595)
                    ·
                      rfl

theorem cell23_7076389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 2, 8].length) (baseStart_7076389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7076389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7076389 prefixEnd_7076389 := by exact prefixLift 7076389
  have htrace : WordTrace (prefixWord ++ tailWord_7076389) baseStart_7076389 baseEnd_7076389 := by
    simpa [prefixWord, tailWord_7076389, baseEnd_7076389] using wordTrace_append hprefix tailTrace_7076389
  have hstable : (prefixWord ++ tailWord_7076389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7076389).length < 2 ^ (prefixWord ++ tailWord_7076389).sum := by decide
  have hdescent : baseEnd_7076389 < baseStart_7076389 := by decide
  rcases family_descends (prefixWord ++ tailWord_7076389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7076413 : List Nat := [1, 4, 1, 3, 2, 1, 2, 2, 2, 1, 4]
def baseStart_7076413 : Nat := 118140960795 + 7076413 * 2 ^ 59
def prefixEnd_7076413 : Nat := 4983230072969 + 3 ^ 40 * 7076413 * 2
def baseEnd_7076413 : Nat := 3633601178724727235293675

theorem tailTrace_7076413 : CollatzResearch.WordTrace tailWord_7076413 prefixEnd_7076413 3633601178724727235293675 := by
  unfold tailWord_7076413
  simp only [CollatzResearch.WordTrace]
  refine ⟨258097985712371730967521893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172065323808247820645014595 258097985712371730967521893)
  ·
    refine ⟨48393372321069699556410355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 258097985712371730967521893 48393372321069699556410355)
    ·
      refine ⟨72590058481604549334615533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48393372321069699556410355 72590058481604549334615533)
      ·
        refine ⟨27221271930601706000480825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72590058481604549334615533 27221271930601706000480825)
        ·
          refine ⟨20415953947951279500360619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27221271930601706000480825 20415953947951279500360619)
          ·
            refine ⟨30623930921926919250540929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20415953947951279500360619 30623930921926919250540929)
            ·
              refine ⟨22967948191445189437905697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30623930921926919250540929 22967948191445189437905697)
              ·
                refine ⟨17225961143583892078429273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22967948191445189437905697 17225961143583892078429273)
                ·
                  refine ⟨12919470857687919058821955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17225961143583892078429273 12919470857687919058821955)
                  ·
                    refine ⟨19379206286531878588232933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12919470857687919058821955 19379206286531878588232933)
                    ·
                      refine ⟨3633601178724727235293675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19379206286531878588232933 3633601178724727235293675)
                      ·
                        rfl

theorem cell23_7076413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_7076413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7076413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7076413 prefixEnd_7076413 := by exact prefixLift 7076413
  have htrace : WordTrace (prefixWord ++ tailWord_7076413) baseStart_7076413 baseEnd_7076413 := by
    simpa [prefixWord, tailWord_7076413, baseEnd_7076413] using wordTrace_append hprefix tailTrace_7076413
  have hstable : (prefixWord ++ tailWord_7076413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7076413).length < 2 ^ (prefixWord ++ tailWord_7076413).sum := by decide
  have hdescent : baseEnd_7076413 < baseStart_7076413 := by decide
  rcases family_descends (prefixWord ++ tailWord_7076413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7076414 : List Nat := [4, 2, 1, 4, 1, 2, 2, 2, 5]
def baseStart_7076414 : Nat := 118140960795 + 7076414 * 2 ^ 59
def prefixEnd_7076414 : Nat := 4983230072969 + 3 ^ 40 * 7076414 * 2
def baseEnd_7076414 : Nat := 403733521356153525709019

theorem tailTrace_7076414 : CollatzResearch.WordTrace tailWord_7076414 prefixEnd_7076414 403733521356153525709019 := by
  unfold tailWord_7076414
  simp only [CollatzResearch.WordTrace]
  refine ⟨32262252773171013517288537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172065348123578738758872197 32262252773171013517288537)
  ·
    refine ⟨24196689579878260137966403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32262252773171013517288537 24196689579878260137966403)
    ·
      refine ⟨36295034369817390206949605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24196689579878260137966403 36295034369817390206949605)
      ·
        refine ⟨6805318944340760663803051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36295034369817390206949605 6805318944340760663803051)
        ·
          refine ⟨10207978416511140995704577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6805318944340760663803051 10207978416511140995704577)
          ·
            refine ⟨7655983812383355746778433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10207978416511140995704577 7655983812383355746778433)
            ·
              refine ⟨5741987859287516810083825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7655983812383355746778433 5741987859287516810083825)
              ·
                refine ⟨4306490894465637607562869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5741987859287516810083825 4306490894465637607562869)
                ·
                  refine ⟨403733521356153525709019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4306490894465637607562869 403733521356153525709019)
                  ·
                    rfl

theorem cell23_7076414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 2, 2, 5].length) (baseStart_7076414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7076414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7076414 prefixEnd_7076414 := by exact prefixLift 7076414
  have htrace : WordTrace (prefixWord ++ tailWord_7076414) baseStart_7076414 baseEnd_7076414 := by
    simpa [prefixWord, tailWord_7076414, baseEnd_7076414] using wordTrace_append hprefix tailTrace_7076414
  have hstable : (prefixWord ++ tailWord_7076414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7076414).length < 2 ^ (prefixWord ++ tailWord_7076414).sum := by decide
  have hdescent : baseEnd_7076414 < baseStart_7076414 := by decide
  rcases family_descends (prefixWord ++ tailWord_7076414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7076419 : List Nat := [1, 1, 1, 3, 1, 2, 1, 5, 8]
def baseStart_7076419 : Nat := 118140960795 + 7076419 * 2 ^ 59
def prefixEnd_7076419 : Nat := 4983230072969 + 3 ^ 40 * 7076419 * 2
def baseEnd_7076419 : Nat := 403733806623183801313183

theorem tailTrace_7076419 : CollatzResearch.WordTrace tailWord_7076419 prefixEnd_7076419 403733806623183801313183 := by
  unfold tailWord_7076419
  simp only [CollatzResearch.WordTrace]
  refine ⟨258098204550349993992240311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172065469700233329328160207 258098204550349993992240311)
  ·
    refine ⟨387147306825524990988360467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258098204550349993992240311 387147306825524990988360467)
    ·
      refine ⟨580720960238287486482540701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 387147306825524990988360467 580720960238287486482540701)
      ·
        refine ⟨217770360089357807430952763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 580720960238287486482540701 217770360089357807430952763)
        ·
          refine ⟨326655540134036711146429145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217770360089357807430952763 326655540134036711146429145)
          ·
            refine ⟨244991655100527533359821859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 326655540134036711146429145 244991655100527533359821859)
            ·
              refine ⟨367487482650791300039732789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 244991655100527533359821859 367487482650791300039732789)
              ·
                refine ⟨34451951498511684378724949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 367487482650791300039732789 34451951498511684378724949)
                ·
                  refine ⟨403733806623183801313183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34451951498511684378724949 403733806623183801313183)
                  ·
                    rfl

theorem cell23_7076419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 5, 8].length) (baseStart_7076419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7076419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7076419 prefixEnd_7076419 := by exact prefixLift 7076419
  have htrace : WordTrace (prefixWord ++ tailWord_7076419) baseStart_7076419 baseEnd_7076419 := by
    simpa [prefixWord, tailWord_7076419, baseEnd_7076419] using wordTrace_append hprefix tailTrace_7076419
  have hstable : (prefixWord ++ tailWord_7076419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7076419).length < 2 ^ (prefixWord ++ tailWord_7076419).sum := by decide
  have hdescent : baseEnd_7076419 < baseStart_7076419 := by decide
  rcases family_descends (prefixWord ++ tailWord_7076419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7076480 : List Nat := [2, 1, 1, 2, 1, 6, 2, 1, 3, 1, 3]
def baseStart_7076480 : Nat := 118140960795 + 7076480 * 2 ^ 59
def prefixEnd_7076480 : Nat := 4983230072969 + 3 ^ 40 * 7076480 * 2
def baseEnd_7076480 : Nat := 3633635581928578473155867

theorem tailTrace_7076480 : CollatzResearch.WordTrace tailWord_7076480 prefixEnd_7076480 3633635581928578473155867 := by
  unfold tailWord_7076480
  simp only [CollatzResearch.WordTrace]
  refine ⟨129050214701564500705105447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172066952935419334273473929 129050214701564500705105447)
  ·
    refine ⟨193575322052346751057658171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129050214701564500705105447 193575322052346751057658171)
    ·
      refine ⟨290362983078520126586487257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193575322052346751057658171 290362983078520126586487257)
      ·
        refine ⟨217772237308890094939865443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 290362983078520126586487257 217772237308890094939865443)
        ·
          refine ⟨326658355963335142409798165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217772237308890094939865443 326658355963335142409798165)
          ·
            refine ⟨15312110435781334800459289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 326658355963335142409798165 15312110435781334800459289)
            ·
              refine ⟨11484082826836001100344467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15312110435781334800459289 11484082826836001100344467)
              ·
                refine ⟨17226124240254001650516701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11484082826836001100344467 17226124240254001650516701)
                ·
                  refine ⟨6459796590095250618943763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17226124240254001650516701 6459796590095250618943763)
                  ·
                    refine ⟨9689694885142875928415645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6459796590095250618943763 9689694885142875928415645)
                    ·
                      refine ⟨3633635581928578473155867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9689694885142875928415645 3633635581928578473155867)
                      ·
                        rfl

theorem cell23_7076480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 2, 1, 3, 1, 3].length) (baseStart_7076480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7076480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7076480 prefixEnd_7076480 := by exact prefixLift 7076480
  have htrace : WordTrace (prefixWord ++ tailWord_7076480) baseStart_7076480 baseEnd_7076480 := by
    simpa [prefixWord, tailWord_7076480, baseEnd_7076480] using wordTrace_append hprefix tailTrace_7076480
  have hstable : (prefixWord ++ tailWord_7076480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7076480).length < 2 ^ (prefixWord ++ tailWord_7076480).sum := by decide
  have hdescent : baseEnd_7076480 < baseStart_7076480 := by decide
  rcases family_descends (prefixWord ++ tailWord_7076480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7076500 : List Nat := [2, 4, 2, 2, 1, 1, 1, 4, 1, 5]
def baseStart_7076500 : Nat := 118140960795 + 7076500 * 2 ^ 59
def prefixEnd_7076500 : Nat := 4983230072969 + 3 ^ 40 * 7076500 * 2
def baseEnd_7076500 : Nat := 1211215283847222798301925

theorem tailTrace_7076500 : CollatzResearch.WordTrace tailWord_7076500 prefixEnd_7076500 1211215283847222798301925 := by
  unfold tailWord_7076500
  simp only [CollatzResearch.WordTrace]
  refine ⟨129050579431528272412969477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172067439242037696550625969 129050579431528272412969477)
  ·
    refine ⟨24196983643411551077431777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 129050579431528272412969477 24196983643411551077431777)
    ·
      refine ⟨18147737732558663308073833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24196983643411551077431777 18147737732558663308073833)
      ·
        refine ⟨13610803299418997481055375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18147737732558663308073833 13610803299418997481055375)
        ·
          refine ⟨20416204949128496221583063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13610803299418997481055375 20416204949128496221583063)
          ·
            refine ⟨30624307423692744332374595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20416204949128496221583063 30624307423692744332374595)
            ·
              refine ⟨45936461135539116498561893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30624307423692744332374595 45936461135539116498561893)
              ·
                refine ⟨8613086462913584343480355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45936461135539116498561893 8613086462913584343480355)
                ·
                  refine ⟨12919629694370376515220533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8613086462913584343480355 12919629694370376515220533)
                  ·
                    refine ⟨1211215283847222798301925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12919629694370376515220533 1211215283847222798301925)
                    ·
                      rfl

theorem cell23_7076500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 4, 1, 5].length) (baseStart_7076500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7076500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7076500 prefixEnd_7076500 := by exact prefixLift 7076500
  have htrace : WordTrace (prefixWord ++ tailWord_7076500) baseStart_7076500 baseEnd_7076500 := by
    simpa [prefixWord, tailWord_7076500, baseEnd_7076500] using wordTrace_append hprefix tailTrace_7076500
  have hstable : (prefixWord ++ tailWord_7076500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7076500).length < 2 ^ (prefixWord ++ tailWord_7076500).sum := by decide
  have hdescent : baseEnd_7076500 < baseStart_7076500 := by decide
  rcases family_descends (prefixWord ++ tailWord_7076500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7076503 : List Nat := [1, 1, 3, 3, 2, 1, 1, 1, 2, 6, 2]
def baseStart_7076503 : Nat := 118140960795 + 7076503 * 2 ^ 59
def prefixEnd_7076503 : Nat := 4983230072969 + 3 ^ 40 * 7076503 * 2
def baseEnd_7076503 : Nat := 3633647391983631883168261

theorem tailTrace_7076503 : CollatzResearch.WordTrace tailWord_7076503 prefixEnd_7076503 3633647391983631883168261 := by
  unfold tailWord_7076503
  simp only [CollatzResearch.WordTrace]
  refine ⟨258101268282045676338298163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172067512188030450892198775 258101268282045676338298163)
  ·
    refine ⟨387151902423068514507447245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258101268282045676338298163 387151902423068514507447245)
    ·
      refine ⟨145181963408650692940292717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 387151902423068514507447245 145181963408650692940292717)
      ·
        refine ⟨54443236278244009852609769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145181963408650692940292717 54443236278244009852609769)
        ·
          refine ⟨40832427208683007389457327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54443236278244009852609769 40832427208683007389457327)
          ·
            refine ⟨61248640813024511084185991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40832427208683007389457327 61248640813024511084185991)
            ·
              refine ⟨91872961219536766626278987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61248640813024511084185991 91872961219536766626278987)
              ·
                refine ⟨137809441829305149939418481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91872961219536766626278987 137809441829305149939418481)
                ·
                  refine ⟨103357081371978862454563861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 137809441829305149939418481 103357081371978862454563861)
                  ·
                    refine ⟨4844863189311509177557681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 103357081371978862454563861 4844863189311509177557681)
                    ·
                      refine ⟨3633647391983631883168261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4844863189311509177557681 3633647391983631883168261)
                      ·
                        rfl

theorem cell23_7076503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 1, 2, 6, 2].length) (baseStart_7076503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7076503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7076503 prefixEnd_7076503 := by exact prefixLift 7076503
  have htrace : WordTrace (prefixWord ++ tailWord_7076503) baseStart_7076503 baseEnd_7076503 := by
    simpa [prefixWord, tailWord_7076503, baseEnd_7076503] using wordTrace_append hprefix tailTrace_7076503
  have hstable : (prefixWord ++ tailWord_7076503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7076503).length < 2 ^ (prefixWord ++ tailWord_7076503).sum := by decide
  have hdescent : baseEnd_7076503 < baseStart_7076503 := by decide
  rcases family_descends (prefixWord ++ tailWord_7076503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7076533 : List Nat := [1, 3, 3, 3, 1, 1, 1, 2, 1, 1, 6]
def baseStart_7076533 : Nat := 118140960795 + 7076533 * 2 ^ 59
def prefixEnd_7076533 : Nat := 4983230072969 + 3 ^ 40 * 7076533 * 2
def baseEnd_7076533 : Nat := 3633662796403266765793123

theorem tailTrace_7076533 : CollatzResearch.WordTrace tailWord_7076533 prefixEnd_7076533 3633662796403266765793123 := by
  unfold tailWord_7076533
  simp only [CollatzResearch.WordTrace]
  refine ⟨258102362471936991461890253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172068241647957994307926835 258102362471936991461890253)
  ·
    refine ⟨96788385926976371798208845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 258102362471936991461890253 96788385926976371798208845)
    ·
      refine ⟨36295644722616139424328317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96788385926976371798208845 36295644722616139424328317)
      ·
        refine ⟨13610866770981052284123119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36295644722616139424328317 13610866770981052284123119)
        ·
          refine ⟨20416300156471578426184679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13610866770981052284123119 20416300156471578426184679)
          ·
            refine ⟨30624450234707367639277019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20416300156471578426184679 30624450234707367639277019)
            ·
              refine ⟨45936675352061051458915529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30624450234707367639277019 45936675352061051458915529)
              ·
                refine ⟨34452506514045788594186647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45936675352061051458915529 34452506514045788594186647)
                ·
                  refine ⟨51678759771068682891279971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34452506514045788594186647 51678759771068682891279971)
                  ·
                    refine ⟨77518139656603024336919957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51678759771068682891279971 77518139656603024336919957)
                    ·
                      refine ⟨3633662796403266765793123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77518139656603024336919957 3633662796403266765793123)
                      ·
                        rfl

theorem cell23_7076533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_7076533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7076533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7076533 prefixEnd_7076533 := by exact prefixLift 7076533
  have htrace : WordTrace (prefixWord ++ tailWord_7076533) baseStart_7076533 baseEnd_7076533 := by
    simpa [prefixWord, tailWord_7076533, baseEnd_7076533] using wordTrace_append hprefix tailTrace_7076533
  have hstable : (prefixWord ++ tailWord_7076533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7076533).length < 2 ^ (prefixWord ++ tailWord_7076533).sum := by decide
  have hdescent : baseEnd_7076533 < baseStart_7076533 := by decide
  rcases family_descends (prefixWord ++ tailWord_7076533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7076631 : List Nat := [1, 1, 3, 4, 3, 2, 2, 1, 1, 3, 2]
def baseStart_7076631 : Nat := 118140960795 + 7076631 * 2 ^ 59
def prefixEnd_7076631 : Nat := 4983230072969 + 3 ^ 40 * 7076631 * 2
def baseEnd_7076631 : Nat := 3633713117507407382367673

theorem tailTrace_7076631 : CollatzResearch.WordTrace tailWord_7076631 prefixEnd_7076631 3633713117507407382367673 := by
  unfold tailWord_7076631
  simp only [CollatzResearch.WordTrace]
  refine ⟨258105936825581954198957747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172070624550387969465971831 258105936825581954198957747)
  ·
    refine ⟨387158905238372931298436621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258105936825581954198957747 387158905238372931298436621)
    ·
      refine ⟨145184589464389849236913733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 387158905238372931298436621 145184589464389849236913733)
      ·
        refine ⟨27222110524573096731921325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 145184589464389849236913733 27222110524573096731921325)
        ·
          refine ⟨10208291446714911274470497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27222110524573096731921325 10208291446714911274470497)
          ·
            refine ⟨7656218585036183455852873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10208291446714911274470497 7656218585036183455852873)
            ·
              refine ⟨5742163938777137591889655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7656218585036183455852873 5742163938777137591889655)
              ·
                refine ⟨8613245908165706387834483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5742163938777137591889655 8613245908165706387834483)
                ·
                  refine ⟨12919868862248559581751725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8613245908165706387834483 12919868862248559581751725)
                  ·
                    refine ⟨4844950823343209843156897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12919868862248559581751725 4844950823343209843156897)
                    ·
                      refine ⟨3633713117507407382367673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4844950823343209843156897 3633713117507407382367673)
                      ·
                        rfl

theorem cell23_7076631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 2, 1, 1, 3, 2].length) (baseStart_7076631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7076631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7076631 prefixEnd_7076631 := by exact prefixLift 7076631
  have htrace : WordTrace (prefixWord ++ tailWord_7076631) baseStart_7076631 baseEnd_7076631 := by
    simpa [prefixWord, tailWord_7076631, baseEnd_7076631] using wordTrace_append hprefix tailTrace_7076631
  have hstable : (prefixWord ++ tailWord_7076631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7076631).length < 2 ^ (prefixWord ++ tailWord_7076631).sum := by decide
  have hdescent : baseEnd_7076631 < baseStart_7076631 := by decide
  rcases family_descends (prefixWord ++ tailWord_7076631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7076644 : List Nat := [2, 3, 1, 3, 3, 1, 1, 1, 4, 2, 2]
def baseStart_7076644 : Nat := 118140960795 + 7076644 * 2 ^ 59
def prefixEnd_7076644 : Nat := 4983230072969 + 3 ^ 40 * 7076644 * 2
def baseEnd_7076644 : Nat := 3633719792755915831505113

theorem tailTrace_7076644 : CollatzResearch.WordTrace tailWord_7076644 prefixEnd_7076644 3633719792755915831505113 := by
  unfold tailWord_7076644
  simp only [CollatzResearch.WordTrace]
  refine ⟨129053205487267428709590493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172070940649689904946120657 129053205487267428709590493)
  ·
    refine ⟨48394952057725285766096435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129053205487267428709590493 48394952057725285766096435)
    ·
      refine ⟨72592428086587928649144653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48394952057725285766096435 72592428086587928649144653)
      ·
        refine ⟨27222160532470473243429245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72592428086587928649144653 27222160532470473243429245)
        ·
          refine ⟨10208310199676427466285967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27222160532470473243429245 10208310199676427466285967)
          ·
            refine ⟨15312465299514641199428951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10208310199676427466285967 15312465299514641199428951)
            ·
              refine ⟨22968697949271961799143427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15312465299514641199428951 22968697949271961799143427)
              ·
                refine ⟨34453046923907942698715141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22968697949271961799143427 34453046923907942698715141)
                ·
                  refine ⟨6459946298232739256009089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34453046923907942698715141 6459946298232739256009089)
                  ·
                    refine ⟨4844959723674554442006817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6459946298232739256009089 4844959723674554442006817)
                    ·
                      refine ⟨3633719792755915831505113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4844959723674554442006817 3633719792755915831505113)
                      ·
                        rfl

theorem cell23_7076644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 1, 4, 2, 2].length) (baseStart_7076644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7076644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7076644 prefixEnd_7076644 := by exact prefixLift 7076644
  have htrace : WordTrace (prefixWord ++ tailWord_7076644) baseStart_7076644 baseEnd_7076644 := by
    simpa [prefixWord, tailWord_7076644, baseEnd_7076644] using wordTrace_append hprefix tailTrace_7076644
  have hstable : (prefixWord ++ tailWord_7076644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7076644).length < 2 ^ (prefixWord ++ tailWord_7076644).sum := by decide
  have hdescent : baseEnd_7076644 < baseStart_7076644 := by decide
  rcases family_descends (prefixWord ++ tailWord_7076644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7076661 : List Nat := [1, 3, 3, 1, 3, 2, 3, 1, 2, 2, 2]
def baseStart_7076661 : Nat := 118140960795 + 7076661 * 2 ^ 59
def prefixEnd_7076661 : Nat := 4983230072969 + 3 ^ 40 * 7076661 * 2
def baseEnd_7076661 : Nat := 3633728521927042264992535

theorem tailTrace_7076661 : CollatzResearch.WordTrace tailWord_7076661 prefixEnd_7076661 3633728521927042264992535 := by
  unfold tailWord_7076661
  simp only [CollatzResearch.WordTrace]
  refine ⟨258107031015473269322549837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172071354010315512881699891 258107031015473269322549837)
  ·
    refine ⟨96790136630802475995956189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 258107031015473269322549837 96790136630802475995956189)
    ·
      refine ⟨36296301236550928498483571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96790136630802475995956189 36296301236550928498483571)
      ·
        refine ⟨54444451854826392747725357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36296301236550928498483571 54444451854826392747725357)
        ·
          refine ⟨20416669445559897280397009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54444451854826392747725357 20416669445559897280397009)
          ·
            refine ⟨15312502084169922960297757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20416669445559897280397009 15312502084169922960297757)
            ·
              refine ⟨5742188281563721110111659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15312502084169922960297757 5742188281563721110111659)
              ·
                refine ⟨8613282422345581665167489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5742188281563721110111659 8613282422345581665167489)
                ·
                  refine ⟨6459961816759186248875617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8613282422345581665167489 6459961816759186248875617)
                  ·
                    refine ⟨4844971362569389686656713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6459961816759186248875617 4844971362569389686656713)
                    ·
                      refine ⟨3633728521927042264992535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4844971362569389686656713 3633728521927042264992535)
                      ·
                        rfl

theorem cell23_7076661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 3, 1, 2, 2, 2].length) (baseStart_7076661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7076661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7076661 prefixEnd_7076661 := by exact prefixLift 7076661
  have htrace : WordTrace (prefixWord ++ tailWord_7076661) baseStart_7076661 baseEnd_7076661 := by
    simpa [prefixWord, tailWord_7076661, baseEnd_7076661] using wordTrace_append hprefix tailTrace_7076661
  have hstable : (prefixWord ++ tailWord_7076661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7076661).length < 2 ^ (prefixWord ++ tailWord_7076661).sum := by decide
  have hdescent : baseEnd_7076661 < baseStart_7076661 := by decide
  rcases family_descends (prefixWord ++ tailWord_7076661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7076683 : List Nat := [1, 1, 1, 1, 3, 1, 1, 1, 8, 1, 4]
def baseStart_7076683 : Nat := 118140960795 + 7076683 * 2 ^ 59
def prefixEnd_7076683 : Nat := 4983230072969 + 3 ^ 40 * 7076683 * 2
def baseEnd_7076683 : Nat := 3633739818501441178917433

theorem tailTrace_7076683 : CollatzResearch.WordTrace tailWord_7076683 prefixEnd_7076683 3633739818501441178917433 := by
  unfold tailWord_7076683
  simp only [CollatzResearch.WordTrace]
  refine ⟨258107833421393567079850703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172071888947595711386567135 258107833421393567079850703)
  ·
    refine ⟨387161750132090350619776055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258107833421393567079850703 387161750132090350619776055)
    ·
      refine ⟨580742625198135525929664083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 387161750132090350619776055 580742625198135525929664083)
      ·
        refine ⟨871113937797203288894496125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 580742625198135525929664083 871113937797203288894496125)
        ·
          refine ⟨326667726673951233335436047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 871113937797203288894496125 326667726673951233335436047)
          ·
            refine ⟨490001590010926850003154071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 326667726673951233335436047 490001590010926850003154071)
            ·
              refine ⟨735002385016390275004731107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 490001590010926850003154071 735002385016390275004731107)
              ·
                refine ⟨1102503577524585412507096661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 735002385016390275004731107 1102503577524585412507096661)
                ·
                  refine ⟨12919963799116235302817539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1102503577524585412507096661 12919963799116235302817539)
                  ·
                    refine ⟨19379945698674352954226309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12919963799116235302817539 19379945698674352954226309)
                    ·
                      refine ⟨3633739818501441178917433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19379945698674352954226309 3633739818501441178917433)
                      ·
                        rfl

theorem cell23_7076683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 8, 1, 4].length) (baseStart_7076683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7076683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7076683 prefixEnd_7076683 := by exact prefixLift 7076683
  have htrace : WordTrace (prefixWord ++ tailWord_7076683) baseStart_7076683 baseEnd_7076683 := by
    simpa [prefixWord, tailWord_7076683, baseEnd_7076683] using wordTrace_append hprefix tailTrace_7076683
  have hstable : (prefixWord ++ tailWord_7076683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7076683).length < 2 ^ (prefixWord ++ tailWord_7076683).sum := by decide
  have hdescent : baseEnd_7076683 < baseStart_7076683 := by decide
  rcases family_descends (prefixWord ++ tailWord_7076683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7076800 : List Nat := [2, 1, 1, 2, 3, 3, 2, 2, 1, 6]
def baseStart_7076800 : Nat := 118140960795 + 7076800 * 2 ^ 59
def prefixEnd_7076800 : Nat := 4983230072969 + 3 ^ 40 * 7076800 * 2
def baseEnd_7076800 : Nat := 1211266631912672407051465

theorem tailTrace_7076800 : CollatzResearch.WordTrace tailWord_7076800 prefixEnd_7076800 1211266631912672407051465 := by
  unfold tailWord_7076800
  simp only [CollatzResearch.WordTrace]
  refine ⟨129056050380984848030929927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172074733841313130707906569 129056050380984848030929927)
  ·
    refine ⟨193584075571477272046394891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129056050380984848030929927 193584075571477272046394891)
    ·
      refine ⟨290376113357215908069592337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193584075571477272046394891 290376113357215908069592337)
      ·
        refine ⟨217782085017911931052194253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 290376113357215908069592337 217782085017911931052194253)
        ·
          refine ⟨81668281881716974144572845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 217782085017911931052194253 81668281881716974144572845)
          ·
            refine ⟨30625605705643865304214817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81668281881716974144572845 30625605705643865304214817)
            ·
              refine ⟨22969204279232898978161113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30625605705643865304214817 22969204279232898978161113)
              ·
                refine ⟨17226903209424674233620835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22969204279232898978161113 17226903209424674233620835)
                ·
                  refine ⟨25840354814137011350431253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17226903209424674233620835 25840354814137011350431253)
                  ·
                    refine ⟨1211266631912672407051465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25840354814137011350431253 1211266631912672407051465)
                    ·
                      rfl

theorem cell23_7076800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 2, 1, 6].length) (baseStart_7076800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7076800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7076800 prefixEnd_7076800 := by exact prefixLift 7076800
  have htrace : WordTrace (prefixWord ++ tailWord_7076800) baseStart_7076800 baseEnd_7076800 := by
    simpa [prefixWord, tailWord_7076800, baseEnd_7076800] using wordTrace_append hprefix tailTrace_7076800
  have hstable : (prefixWord ++ tailWord_7076800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7076800).length < 2 ^ (prefixWord ++ tailWord_7076800).sum := by decide
  have hdescent : baseEnd_7076800 < baseStart_7076800 := by decide
  rcases family_descends (prefixWord ++ tailWord_7076800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7076810 : List Nat := [3, 1, 2, 1, 2, 1, 1, 5, 1, 1, 5]
def baseStart_7076810 : Nat := 118140960795 + 7076810 * 2 ^ 59
def prefixEnd_7076810 : Nat := 4983230072969 + 3 ^ 40 * 7076810 * 2
def baseEnd_7076810 : Nat := 3633805030544562182029349

theorem tailTrace_7076810 : CollatzResearch.WordTrace tailWord_7076810 prefixEnd_7076810 3633805030544562182029349 := by
  unfold tailWord_7076810
  simp only [CollatzResearch.WordTrace]
  refine ⟨64528116372983366942430971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172074976994622311846482589 64528116372983366942430971)
  ·
    refine ⟨96792174559475050413646457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64528116372983366942430971 96792174559475050413646457)
    ·
      refine ⟨72594130919606287810234843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96792174559475050413646457 72594130919606287810234843)
      ·
        refine ⟨108891196379409431715352265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72594130919606287810234843 108891196379409431715352265)
        ·
          refine ⟨81668397284557073786514199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108891196379409431715352265 81668397284557073786514199)
          ·
            refine ⟨122502595926835610679771299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81668397284557073786514199 122502595926835610679771299)
            ·
              refine ⟨183753893890253416019656949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122502595926835610679771299 183753893890253416019656949)
              ·
                refine ⟨17226927552211257751842839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 183753893890253416019656949 17226927552211257751842839)
                ·
                  refine ⟨25840391328316886627764259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17226927552211257751842839 25840391328316886627764259)
                  ·
                    refine ⟨38760586992475329941646389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25840391328316886627764259 38760586992475329941646389)
                    ·
                      refine ⟨3633805030544562182029349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38760586992475329941646389 3633805030544562182029349)
                      ·
                        rfl

theorem cell23_7076810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 5, 1, 1, 5].length) (baseStart_7076810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7076810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7076810 prefixEnd_7076810 := by exact prefixLift 7076810
  have htrace : WordTrace (prefixWord ++ tailWord_7076810) baseStart_7076810 baseEnd_7076810 := by
    simpa [prefixWord, tailWord_7076810, baseEnd_7076810] using wordTrace_append hprefix tailTrace_7076810
  have hstable : (prefixWord ++ tailWord_7076810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7076810).length < 2 ^ (prefixWord ++ tailWord_7076810).sum := by decide
  have hdescent : baseEnd_7076810 < baseStart_7076810 := by decide
  rcases family_descends (prefixWord ++ tailWord_7076810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7076824 : List Nat := [2, 1, 2, 2, 2, 3, 1, 3, 3, 2, 2]
def baseStart_7076824 : Nat := 118140960795 + 7076824 * 2 ^ 59
def prefixEnd_7076824 : Nat := 4983230072969 + 3 ^ 40 * 7076824 * 2
def baseEnd_7076824 : Nat := 3633812219273725127254285

theorem tailTrace_7076824 : CollatzResearch.WordTrace tailWord_7076824 prefixEnd_7076824 3633812219273725127254285 := by
  unfold tailWord_7076824
  simp only [CollatzResearch.WordTrace]
  refine ⟨129056488056941374080366763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172075317409255165440489017 129056488056941374080366763)
  ·
    refine ⟨193584732085412061120550145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129056488056941374080366763 193584732085412061120550145)
    ·
      refine ⟨145188549064059045840412609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193584732085412061120550145 145188549064059045840412609)
      ·
        refine ⟨108891411798044284380309457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145188549064059045840412609 108891411798044284380309457)
        ·
          refine ⟨81668558848533213285232093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108891411798044284380309457 81668558848533213285232093)
          ·
            refine ⟨30625709568199954981962035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81668558848533213285232093 30625709568199954981962035)
            ·
              refine ⟨45938564352299932472943053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30625709568199954981962035 45938564352299932472943053)
              ·
                refine ⟨17226961632112474677353645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45938564352299932472943053 17226961632112474677353645)
                ·
                  refine ⟨6460110612042178004007617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17226961632112474677353645 6460110612042178004007617)
                  ·
                    refine ⟨4845082959031633503005713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6460110612042178004007617 4845082959031633503005713)
                    ·
                      refine ⟨3633812219273725127254285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4845082959031633503005713 3633812219273725127254285)
                      ·
                        rfl

theorem cell23_7076824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 3, 3, 2, 2].length) (baseStart_7076824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7076824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7076824 prefixEnd_7076824 := by exact prefixLift 7076824
  have htrace : WordTrace (prefixWord ++ tailWord_7076824) baseStart_7076824 baseEnd_7076824 := by
    simpa [prefixWord, tailWord_7076824, baseEnd_7076824] using wordTrace_append hprefix tailTrace_7076824
  have hstable : (prefixWord ++ tailWord_7076824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7076824).length < 2 ^ (prefixWord ++ tailWord_7076824).sum := by decide
  have hdescent : baseEnd_7076824 < baseStart_7076824 := by decide
  rcases family_descends (prefixWord ++ tailWord_7076824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7076834 : List Nat := [3, 3, 3, 1, 1, 1, 3, 1, 1, 6]
def baseStart_7076834 : Nat := 118140960795 + 7076834 * 2 ^ 59
def prefixEnd_7076834 : Nat := 4983230072969 + 3 ^ 40 * 7076834 * 2
def baseEnd_7076834 : Nat := 1211272451360090029376413

theorem tailTrace_7076834 : CollatzResearch.WordTrace tailWord_7076834 prefixEnd_7076834 1211272451360090029376413 := by
  unfold tailWord_7076834
  simp only [CollatzResearch.WordTrace]
  refine ⟨64528335210961629967149389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172075560562564346579065037 64528335210961629967149389)
  ·
    refine ⟨24198125704110611237681021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64528335210961629967149389 24198125704110611237681021)
    ·
      refine ⟨9074297139041479214130383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24198125704110611237681021 9074297139041479214130383)
      ·
        refine ⟨13611445708562218821195575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9074297139041479214130383 13611445708562218821195575)
        ·
          refine ⟨20417168562843328231793363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13611445708562218821195575 20417168562843328231793363)
          ·
            refine ⟨30625752844264992347690045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20417168562843328231793363 30625752844264992347690045)
            ·
              refine ⟨11484657316599372130383767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30625752844264992347690045 11484657316599372130383767)
              ·
                refine ⟨17226985974899058195575651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11484657316599372130383767 17226985974899058195575651)
                ·
                  refine ⟨25840478962348587293363477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17226985974899058195575651 25840478962348587293363477)
                  ·
                    refine ⟨1211272451360090029376413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25840478962348587293363477 1211272451360090029376413)
                    ·
                      rfl

theorem cell23_7076834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_7076834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7076834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7076834 prefixEnd_7076834 := by exact prefixLift 7076834
  have htrace : WordTrace (prefixWord ++ tailWord_7076834) baseStart_7076834 baseEnd_7076834 := by
    simpa [prefixWord, tailWord_7076834, baseEnd_7076834] using wordTrace_append hprefix tailTrace_7076834
  have hstable : (prefixWord ++ tailWord_7076834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7076834).length < 2 ^ (prefixWord ++ tailWord_7076834).sum := by decide
  have hdescent : baseEnd_7076834 < baseStart_7076834 := by decide
  rcases family_descends (prefixWord ++ tailWord_7076834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7076847 : List Nat := [1, 1, 2, 1, 4, 5, 2, 7]
def baseStart_7076847 : Nat := 118140960795 + 7076847 * 2 ^ 59
def prefixEnd_7076847 : Nat := 4983230072969 + 3 ^ 40 * 7076847 * 2
def baseEnd_7076847 : Nat := 134586075160325131009877

theorem tailTrace_7076847 : CollatzResearch.WordTrace tailWord_7076847 prefixEnd_7076847 134586075160325131009877 := by
  unfold tailWord_7076847
  simp only [CollatzResearch.WordTrace]
  refine ⟨258113814992799423088820795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172075876661866282059213863 258113814992799423088820795)
  ·
    refine ⟨387170722489199134633231193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258113814992799423088820795 387170722489199134633231193)
    ·
      refine ⟨290378041866899350974923395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 387170722489199134633231193 290378041866899350974923395)
      ·
        refine ⟨435567062800349026462385093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290378041866899350974923395 435567062800349026462385093)
        ·
          refine ⟨81668824275065442461697205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 435567062800349026462385093 81668824275065442461697205)
          ·
            refine ⟨7656452275787385230784113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 81668824275065442461697205 7656452275787385230784113)
            ·
              refine ⟨5742339206840538923088085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7656452275787385230784113 5742339206840538923088085)
              ·
                refine ⟨134586075160325131009877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5742339206840538923088085 134586075160325131009877)
                ·
                  rfl

theorem cell23_7076847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 2, 7].length) (baseStart_7076847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7076847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7076847 prefixEnd_7076847 := by exact prefixLift 7076847
  have htrace : WordTrace (prefixWord ++ tailWord_7076847) baseStart_7076847 baseEnd_7076847 := by
    simpa [prefixWord, tailWord_7076847, baseEnd_7076847] using wordTrace_append hprefix tailTrace_7076847
  have hstable : (prefixWord ++ tailWord_7076847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7076847).length < 2 ^ (prefixWord ++ tailWord_7076847).sum := by decide
  have hdescent : baseEnd_7076847 < baseStart_7076847 := by decide
  rcases family_descends (prefixWord ++ tailWord_7076847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7076857 : List Nat := [1, 2, 1, 3, 1, 3, 1, 1, 6, 1, 3]
def baseStart_7076857 : Nat := 118140960795 + 7076857 * 2 ^ 59
def prefixEnd_7076857 : Nat := 4983230072969 + 3 ^ 40 * 7076857 * 2
def baseEnd_7076857 : Nat := 3633829164135323498141633

theorem tailTrace_7076857 : CollatzResearch.WordTrace tailWord_7076857 prefixEnd_7076857 3633829164135323498141633 := by
  unfold tailWord_7076857
  simp only [CollatzResearch.WordTrace]
  refine ⟨258114179722763194796684825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172076119815175463197789883 258114179722763194796684825)
  ·
    refine ⟨193585634792072396097513619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258114179722763194796684825 193585634792072396097513619)
    ·
      refine ⟨290378452188108594146270429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193585634792072396097513619 290378452188108594146270429)
      ·
        refine ⟨108891919570540722804851411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 290378452188108594146270429 108891919570540722804851411)
        ·
          refine ⟨163337879355811084207277117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108891919570540722804851411 163337879355811084207277117)
          ·
            refine ⟨61251704758429156577728919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 163337879355811084207277117 61251704758429156577728919)
            ·
              refine ⟨91877557137643734866593379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61251704758429156577728919 91877557137643734866593379)
              ·
                refine ⟨137816335706465602299890069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91877557137643734866593379 137816335706465602299890069)
                ·
                  refine ⟨6460140736240575107807347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 137816335706465602299890069 6460140736240575107807347)
                  ·
                    refine ⟨9690211104360862661711021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6460140736240575107807347 9690211104360862661711021)
                    ·
                      refine ⟨3633829164135323498141633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9690211104360862661711021 3633829164135323498141633)
                      ·
                        rfl

theorem cell23_7076857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 1, 6, 1, 3].length) (baseStart_7076857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7076857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7076857 prefixEnd_7076857 := by exact prefixLift 7076857
  have htrace : WordTrace (prefixWord ++ tailWord_7076857) baseStart_7076857 baseEnd_7076857 := by
    simpa [prefixWord, tailWord_7076857, baseEnd_7076857] using wordTrace_append hprefix tailTrace_7076857
  have hstable : (prefixWord ++ tailWord_7076857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7076857).length < 2 ^ (prefixWord ++ tailWord_7076857).sum := by decide
  have hdescent : baseEnd_7076857 < baseStart_7076857 := by decide
  rcases family_descends (prefixWord ++ tailWord_7076857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7076867 : List Nat := [1, 1, 1, 3, 2, 1, 1, 1, 7, 3, 2]
def baseStart_7076867 : Nat := 118140960795 + 7076867 * 2 ^ 59
def prefixEnd_7076867 : Nat := 4983230072969 + 3 ^ 40 * 7076867 * 2
def baseEnd_7076867 : Nat := 3633834298941868459016587

theorem tailTrace_7076867 : CollatzResearch.WordTrace tailWord_7076867 prefixEnd_7076867 3633834298941868459016587 := by
  unfold tailWord_7076867
  simp only [CollatzResearch.WordTrace]
  refine ⟨258114544452726966504548855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172076362968484644336365903 258114544452726966504548855)
  ·
    refine ⟨387171816679090449756823283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258114544452726966504548855 387171816679090449756823283)
    ·
      refine ⟨580757725018635674635234925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 387171816679090449756823283 580757725018635674635234925)
      ·
        refine ⟨217784146881988377988213097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 580757725018635674635234925 217784146881988377988213097)
        ·
          refine ⟨163338110161491283491159823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217784146881988377988213097 163338110161491283491159823)
          ·
            refine ⟨245007165242236925236739735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163338110161491283491159823 245007165242236925236739735)
            ·
              refine ⟨367510747863355387855109603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 245007165242236925236739735 367510747863355387855109603)
              ·
                refine ⟨551266121795033081782664405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 367510747863355387855109603 551266121795033081782664405)
                ·
                  refine ⟨12920299729571087854281197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 551266121795033081782664405 12920299729571087854281197)
                  ·
                    refine ⟨4845112398589157945355449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12920299729571087854281197 4845112398589157945355449)
                    ·
                      refine ⟨3633834298941868459016587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4845112398589157945355449 3633834298941868459016587)
                      ·
                        rfl

theorem cell23_7076867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 7, 3, 2].length) (baseStart_7076867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7076867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7076867 prefixEnd_7076867 := by exact prefixLift 7076867
  have htrace : WordTrace (prefixWord ++ tailWord_7076867) baseStart_7076867 baseEnd_7076867 := by
    simpa [prefixWord, tailWord_7076867, baseEnd_7076867] using wordTrace_append hprefix tailTrace_7076867
  have hstable : (prefixWord ++ tailWord_7076867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7076867).length < 2 ^ (prefixWord ++ tailWord_7076867).sum := by decide
  have hdescent : baseEnd_7076867 < baseStart_7076867 := by decide
  rcases family_descends (prefixWord ++ tailWord_7076867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7076874 : List Nat := [3, 1, 2, 2, 3, 1, 2, 1, 4, 1, 3]
def baseStart_7076874 : Nat := 118140960795 + 7076874 * 2 ^ 59
def prefixEnd_7076874 : Nat := 4983230072969 + 3 ^ 40 * 7076874 * 2
def baseEnd_7076874 : Nat := 3633837893306449931629055

theorem tailTrace_7076874 : CollatzResearch.WordTrace tailWord_7076874 prefixEnd_7076874 3633837893306449931629055 := by
  unfold tailWord_7076874
  simp only [CollatzResearch.WordTrace]
  refine ⟨64528699940925401675013419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172076533175801071133369117 64528699940925401675013419)
  ·
    refine ⟨96793049911388102512520129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64528699940925401675013419 96793049911388102512520129)
    ·
      refine ⟨72594787433541076884390097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96793049911388102512520129 72594787433541076884390097)
      ·
        refine ⟨54446090575155807663292573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72594787433541076884390097 54446090575155807663292573)
        ·
          refine ⟨20417283965683427873734715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54446090575155807663292573 20417283965683427873734715)
          ·
            refine ⟨30625925948525141810602073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20417283965683427873734715 30625925948525141810602073)
            ·
              refine ⟨22969444461393856357951555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30625925948525141810602073 22969444461393856357951555)
              ·
                refine ⟨34454166692090784536927333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22969444461393856357951555 34454166692090784536927333)
                ·
                  refine ⟨6460156254767022100673875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34454166692090784536927333 6460156254767022100673875)
                  ·
                    refine ⟨9690234382150533151010813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6460156254767022100673875 9690234382150533151010813)
                    ·
                      refine ⟨3633837893306449931629055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9690234382150533151010813 3633837893306449931629055)
                      ·
                        rfl

theorem cell23_7076874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 1, 4, 1, 3].length) (baseStart_7076874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7076874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7076874 prefixEnd_7076874 := by exact prefixLift 7076874
  have htrace : WordTrace (prefixWord ++ tailWord_7076874) baseStart_7076874 baseEnd_7076874 := by
    simpa [prefixWord, tailWord_7076874, baseEnd_7076874] using wordTrace_append hprefix tailTrace_7076874
  have hstable : (prefixWord ++ tailWord_7076874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7076874).length < 2 ^ (prefixWord ++ tailWord_7076874).sum := by decide
  have hdescent : baseEnd_7076874 < baseStart_7076874 := by decide
  rcases family_descends (prefixWord ++ tailWord_7076874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7076890 : List Nat := [3, 1, 1, 3, 1, 2, 2, 1, 1, 8]
def baseStart_7076890 : Nat := 118140960795 + 7076890 * 2 ^ 59
def prefixEnd_7076890 : Nat := 4983230072969 + 3 ^ 40 * 7076890 * 2
def baseEnd_7076890 : Nat := 1211282036332307289676327

theorem tailTrace_7076890 : CollatzResearch.WordTrace tailWord_7076890 prefixEnd_7076890 1211282036332307289676327 := by
  unfold tailWord_7076890
  simp only [CollatzResearch.WordTrace]
  refine ⟨64528845832910910358159031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172076922221095760955090749 64528845832910910358159031)
  ·
    refine ⟨96793268749366365537238547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64528845832910910358159031 96793268749366365537238547)
    ·
      refine ⟨145189903124049548305857821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96793268749366365537238547 145189903124049548305857821)
      ·
        refine ⟨54446213671518580614696683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145189903124049548305857821 54446213671518580614696683)
        ·
          refine ⟨81669320507277870922045025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54446213671518580614696683 81669320507277870922045025)
          ·
            refine ⟨61251990380458403191533769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81669320507277870922045025 61251990380458403191533769)
            ·
              refine ⟨45938992785343802393650327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61251990380458403191533769 45938992785343802393650327)
              ·
                refine ⟨68908489178015703590475491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45938992785343802393650327 68908489178015703590475491)
                ·
                  refine ⟨103362733767023555385713237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68908489178015703590475491 103362733767023555385713237)
                  ·
                    refine ⟨1211282036332307289676327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 103362733767023555385713237 1211282036332307289676327)
                    ·
                      rfl

theorem cell23_7076890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 1, 1, 8].length) (baseStart_7076890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7076890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7076890 prefixEnd_7076890 := by exact prefixLift 7076890
  have htrace : WordTrace (prefixWord ++ tailWord_7076890) baseStart_7076890 baseEnd_7076890 := by
    simpa [prefixWord, tailWord_7076890, baseEnd_7076890] using wordTrace_append hprefix tailTrace_7076890
  have hstable : (prefixWord ++ tailWord_7076890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7076890).length < 2 ^ (prefixWord ++ tailWord_7076890).sum := by decide
  have hdescent : baseEnd_7076890 < baseStart_7076890 := by decide
  rcases family_descends (prefixWord ++ tailWord_7076890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7076914 : List Nat := [3, 2, 1, 1, 2, 2, 3, 2, 1, 4, 2]
def baseStart_7076914 : Nat := 118140960795 + 7076914 * 2 ^ 59
def prefixEnd_7076914 : Nat := 4983230072969 + 3 ^ 40 * 7076914 * 2
def baseEnd_7076914 : Nat := 3633858432532629775128871

theorem tailTrace_7076914 : CollatzResearch.WordTrace tailWord_7076914 prefixEnd_7076914 3633858432532629775128871 := by
  unfold tailWord_7076914
  simp only [CollatzResearch.WordTrace]
  refine ⟨64529064670889173382877449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172077505789037795687673197 64529064670889173382877449)
  ·
    refine ⟨48396798503166880037158087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64529064670889173382877449 48396798503166880037158087)
    ·
      refine ⟨72595197754750320055737131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48396798503166880037158087 72595197754750320055737131)
      ·
        refine ⟨108892796632125480083605697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72595197754750320055737131 108892796632125480083605697)
        ·
          refine ⟨81669597474094110062704273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108892796632125480083605697 81669597474094110062704273)
          ·
            refine ⟨61252198105570582547028205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81669597474094110062704273 61252198105570582547028205)
            ·
              refine ⟨22969574289588968455135577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61252198105570582547028205 22969574289588968455135577)
              ·
                refine ⟨17227180717191726341351683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22969574289588968455135577 17227180717191726341351683)
                ·
                  refine ⟨25840771075787589512027525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17227180717191726341351683 25840771075787589512027525)
                  ·
                    refine ⟨4845144576710173033505161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25840771075787589512027525 4845144576710173033505161)
                    ·
                      refine ⟨3633858432532629775128871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4845144576710173033505161 3633858432532629775128871)
                      ·
                        rfl

theorem cell23_7076914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 2, 1, 4, 2].length) (baseStart_7076914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7076914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7076914 prefixEnd_7076914 := by exact prefixLift 7076914
  have htrace : WordTrace (prefixWord ++ tailWord_7076914) baseStart_7076914 baseEnd_7076914 := by
    simpa [prefixWord, tailWord_7076914, baseEnd_7076914] using wordTrace_append hprefix tailTrace_7076914
  have hstable : (prefixWord ++ tailWord_7076914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7076914).length < 2 ^ (prefixWord ++ tailWord_7076914).sum := by decide
  have hdescent : baseEnd_7076914 < baseStart_7076914 := by decide
  rcases family_descends (prefixWord ++ tailWord_7076914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7076931 : List Nat := [1, 1, 1, 3, 1, 2, 6, 2, 2, 2, 2]
def baseStart_7076931 : Nat := 118140960795 + 7076931 * 2 ^ 59
def prefixEnd_7076931 : Nat := 4983230072969 + 3 ^ 40 * 7076931 * 2
def baseEnd_7076931 : Nat := 3633867161703756208616293

theorem tailTrace_7076931 : CollatzResearch.WordTrace tailWord_7076931 prefixEnd_7076931 3633867161703756208616293 := by
  unfold tailWord_7076931
  simp only [CollatzResearch.WordTrace]
  refine ⟨258116878724495105434878647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172077919149663403623252431 258116878724495105434878647)
  ·
    refine ⟨387175318086742658152317971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258116878724495105434878647 387175318086742658152317971)
    ·
      refine ⟨580762977130113987228476957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 387175318086742658152317971 580762977130113987228476957)
      ·
        refine ⟨217786116423792745210678859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 580762977130113987228476957 217786116423792745210678859)
        ·
          refine ⟨326679174635689117816018289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217786116423792745210678859 326679174635689117816018289)
          ·
            refine ⟨245009380976766838362013717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 326679174635689117816018289 245009380976766838362013717)
            ·
              refine ⟨11484814733285945548219393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 245009380976766838362013717 11484814733285945548219393)
              ·
                refine ⟨8613611049964459161164545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11484814733285945548219393 8613611049964459161164545)
                ·
                  refine ⟨6460208287473344370873409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8613611049964459161164545 6460208287473344370873409)
                  ·
                    refine ⟨4845156215605008278155057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6460208287473344370873409 4845156215605008278155057)
                    ·
                      refine ⟨3633867161703756208616293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4845156215605008278155057 3633867161703756208616293)
                      ·
                        rfl

theorem cell23_7076931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 6, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 6, 2, 2, 2, 2].length) (baseStart_7076931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7076931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7076931 prefixEnd_7076931 := by exact prefixLift 7076931
  have htrace : WordTrace (prefixWord ++ tailWord_7076931) baseStart_7076931 baseEnd_7076931 := by
    simpa [prefixWord, tailWord_7076931, baseEnd_7076931] using wordTrace_append hprefix tailTrace_7076931
  have hstable : (prefixWord ++ tailWord_7076931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7076931).length < 2 ^ (prefixWord ++ tailWord_7076931).sum := by decide
  have hdescent : baseEnd_7076931 < baseStart_7076931 := by decide
  rcases family_descends (prefixWord ++ tailWord_7076931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7076940 : List Nat := [2, 2, 1, 3, 1, 1, 1, 1, 2, 1, 8]
def baseStart_7076940 : Nat := 118140960795 + 7076940 * 2 ^ 59
def prefixEnd_7076940 : Nat := 4983230072969 + 3 ^ 40 * 7076940 * 2
def baseEnd_7076940 : Nat := 3633871783029646673403751

theorem tailTrace_7076940 : CollatzResearch.WordTrace tailWord_7076940 prefixEnd_7076940 3633871783029646673403751 := by
  unfold tailWord_7076940
  simp only [CollatzResearch.WordTrace]
  refine ⟨129058603490731249985978137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172078137987641666647970849 129058603490731249985978137)
  ·
    refine ⟨96793952618048437489483603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129058603490731249985978137 96793952618048437489483603)
    ·
      refine ⟨145190928927072656234225405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96793952618048437489483603 145190928927072656234225405)
      ·
        refine ⟨54446598347652246087834527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145190928927072656234225405 54446598347652246087834527)
        ·
          refine ⟨81669897521478369131751791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54446598347652246087834527 81669897521478369131751791)
          ·
            refine ⟨122504846282217553697627687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81669897521478369131751791 122504846282217553697627687)
            ·
              refine ⟨183757269423326330546441531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122504846282217553697627687 183757269423326330546441531)
              ·
                refine ⟨275635904134989495819662297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 183757269423326330546441531 275635904134989495819662297)
                ·
                  refine ⟨206726928101242121864746723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 275635904134989495819662297 206726928101242121864746723)
                  ·
                    refine ⟨310090392151863182797120085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 206726928101242121864746723 310090392151863182797120085)
                    ·
                      refine ⟨3633871783029646673403751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 310090392151863182797120085 3633871783029646673403751)
                      ·
                        rfl

theorem cell23_7076940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 2, 1, 8].length) (baseStart_7076940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7076940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7076940 prefixEnd_7076940 := by exact prefixLift 7076940
  have htrace : WordTrace (prefixWord ++ tailWord_7076940) baseStart_7076940 baseEnd_7076940 := by
    simpa [prefixWord, tailWord_7076940, baseEnd_7076940] using wordTrace_append hprefix tailTrace_7076940
  have hstable : (prefixWord ++ tailWord_7076940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7076940).length < 2 ^ (prefixWord ++ tailWord_7076940).sum := by decide
  have hdescent : baseEnd_7076940 < baseStart_7076940 := by decide
  rcases family_descends (prefixWord ++ tailWord_7076940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7076967 : List Nat := [1, 1, 5, 1, 1, 4, 1, 1, 1, 7]
def baseStart_7076967 : Nat := 118140960795 + 7076967 * 2 ^ 59
def prefixEnd_7076967 : Nat := 4983230072969 + 3 ^ 40 * 7076967 * 2
def baseEnd_7076967 : Nat := 1211295215669106022588709

theorem tailTrace_7076967 : CollatzResearch.WordTrace tailWord_7076967 prefixEnd_7076967 1211295215669106022588709 := by
  unfold tailWord_7076967
  simp only [CollatzResearch.WordTrace]
  refine ⟨258118191752364683583189155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172078794501576455722126103 258118191752364683583189155)
  ·
    refine ⟨387177287628547025374783733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258118191752364683583189155 387177287628547025374783733)
    ·
      refine ⟨36297870715176283628885975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 387177287628547025374783733 36297870715176283628885975)
      ·
        refine ⟨54446806072764425443328963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36297870715176283628885975 54446806072764425443328963)
        ·
          refine ⟨81670209109146638164993445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54446806072764425443328963 81670209109146638164993445)
          ·
            refine ⟨15313164207964994655936271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81670209109146638164993445 15313164207964994655936271)
            ·
              refine ⟨22969746311947491983904407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15313164207964994655936271 22969746311947491983904407)
              ·
                refine ⟨34454619467921237975856611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22969746311947491983904407 34454619467921237975856611)
                ·
                  refine ⟨51681929201881856963784917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34454619467921237975856611 51681929201881856963784917)
                  ·
                    refine ⟨1211295215669106022588709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51681929201881856963784917 1211295215669106022588709)
                    ·
                      rfl

theorem cell23_7076967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 1, 1, 7].length) (baseStart_7076967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7076967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7076967 prefixEnd_7076967 := by exact prefixLift 7076967
  have htrace : WordTrace (prefixWord ++ tailWord_7076967) baseStart_7076967 baseEnd_7076967 := by
    simpa [prefixWord, tailWord_7076967, baseEnd_7076967] using wordTrace_append hprefix tailTrace_7076967
  have hstable : (prefixWord ++ tailWord_7076967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7076967).length < 2 ^ (prefixWord ++ tailWord_7076967).sum := by decide
  have hdescent : baseEnd_7076967 < baseStart_7076967 := by decide
  rcases family_descends (prefixWord ++ tailWord_7076967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7076987 : List Nat := [1, 1, 1, 1, 1, 4, 1, 6, 2, 1, 4]
def baseStart_7076987 : Nat := 118140960795 + 7076987 * 2 ^ 59
def prefixEnd_7076987 : Nat := 4983230072969 + 3 ^ 40 * 7076987 * 2
def baseEnd_7076987 : Nat := 3633895916620407989516035

theorem tailTrace_7076987 : CollatzResearch.WordTrace tailWord_7076987 prefixEnd_7076987 3633895916620407989516035 := by
  unfold tailWord_7076987
  simp only [CollatzResearch.WordTrace]
  refine ⟨258118921212292226998917215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172079280808194817999278143 258118921212292226998917215)
  ·
    refine ⟨387178381818438340498375823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258118921212292226998917215 387178381818438340498375823)
    ·
      refine ⟨580767572727657510747563735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 387178381818438340498375823 580767572727657510747563735)
      ·
        refine ⟨871151359091486266121345603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 580767572727657510747563735 871151359091486266121345603)
        ·
          refine ⟨1306727038637229399182018405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 871151359091486266121345603 1306727038637229399182018405)
          ·
            refine ⟨245011319744480512346628451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1306727038637229399182018405 245011319744480512346628451)
            ·
              refine ⟨367516979616720768519942677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 245011319744480512346628451 367516979616720768519942677)
              ·
                refine ⟨17227358419533786024372313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 367516979616720768519942677 17227358419533786024372313)
                ·
                  refine ⟨12920518814650339518279235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17227358419533786024372313 12920518814650339518279235)
                  ·
                    refine ⟨19380778221975509277418853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12920518814650339518279235 19380778221975509277418853)
                    ·
                      refine ⟨3633895916620407989516035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19380778221975509277418853 3633895916620407989516035)
                      ·
                        rfl

theorem cell23_7076987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 6, 2, 1, 4].length) (baseStart_7076987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7076987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7076987 prefixEnd_7076987 := by exact prefixLift 7076987
  have htrace : WordTrace (prefixWord ++ tailWord_7076987) baseStart_7076987 baseEnd_7076987 := by
    simpa [prefixWord, tailWord_7076987, baseEnd_7076987] using wordTrace_append hprefix tailTrace_7076987
  have hstable : (prefixWord ++ tailWord_7076987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7076987).length < 2 ^ (prefixWord ++ tailWord_7076987).sum := by decide
  have hdescent : baseEnd_7076987 < baseStart_7076987 := by decide
  rcases family_descends (prefixWord ++ tailWord_7076987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7077024 : List Nat := [2, 1, 1, 4, 2, 1, 2, 3, 2, 2, 3]
def baseStart_7077024 : Nat := 118140960795 + 7077024 * 2 ^ 59
def prefixEnd_7077024 : Nat := 4983230072969 + 3 ^ 40 * 7077024 * 2
def baseEnd_7077024 : Nat := 3633914915404624344753365

theorem tailTrace_7077024 : CollatzResearch.WordTrace tailWord_7077024 prefixEnd_7077024 3633914915404624344753365 := by
  unfold tailWord_7077024
  simp only [CollatzResearch.WordTrace]
  refine ⟨129060135356579091159007063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172080180475438788212009417 129060135356579091159007063)
  ·
    refine ⟨193590203034868636738510595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129060135356579091159007063 193590203034868636738510595)
    ·
      refine ⟨290385304552302955107765893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193590203034868636738510595 290385304552302955107765893)
      ·
        refine ⟨54447244603556804082706105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 290385304552302955107765893 54447244603556804082706105)
        ·
          refine ⟨40835433452667603062029579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54447244603556804082706105 40835433452667603062029579)
          ·
            refine ⟨61253150179001404593044369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40835433452667603062029579 61253150179001404593044369)
            ·
              refine ⟨45939862634251053444783277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61253150179001404593044369 45939862634251053444783277)
              ·
                refine ⟨17227448487844145041793729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45939862634251053444783277 17227448487844145041793729)
                ·
                  refine ⟨12920586365883108781345297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17227448487844145041793729 12920586365883108781345297)
                  ·
                    refine ⟨9690439774412331586008973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12920586365883108781345297 9690439774412331586008973)
                    ·
                      refine ⟨3633914915404624344753365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9690439774412331586008973 3633914915404624344753365)
                      ·
                        rfl

theorem cell23_7077024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 3, 2, 2, 3].length) (baseStart_7077024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7077024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7077024 prefixEnd_7077024 := by exact prefixLift 7077024
  have htrace : WordTrace (prefixWord ++ tailWord_7077024) baseStart_7077024 baseEnd_7077024 := by
    simpa [prefixWord, tailWord_7077024, baseEnd_7077024] using wordTrace_append hprefix tailTrace_7077024
  have hstable : (prefixWord ++ tailWord_7077024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7077024).length < 2 ^ (prefixWord ++ tailWord_7077024).sum := by decide
  have hdescent : baseEnd_7077024 < baseStart_7077024 := by decide
  rcases family_descends (prefixWord ++ tailWord_7077024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7077041 : List Nat := [1, 2, 2, 5, 1, 2, 1, 2, 2, 2, 3]
def baseStart_7077041 : Nat := 118140960795 + 7077041 * 2 ^ 59
def prefixEnd_7077041 : Nat := 4983230072969 + 3 ^ 40 * 7077041 * 2
def baseEnd_7077041 : Nat := 3633923644575750778240787

theorem tailTrace_7077041 : CollatzResearch.WordTrace tailWord_7077041 prefixEnd_7077041 3633923644575750778240787 := by
  unfold tailWord_7077041
  simp only [CollatzResearch.WordTrace]
  refine ⟨258120890754096594221382977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172080593836064396147588651 258120890754096594221382977)
  ·
    refine ⟨193590668065572445666037233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258120890754096594221382977 193590668065572445666037233)
    ·
      refine ⟨145193001049179334249527925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193590668065572445666037233 145193001049179334249527925)
      ·
        refine ⟨13611843848360562585893243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 145193001049179334249527925 13611843848360562585893243)
        ·
          refine ⟨20417765772540843878839865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13611843848360562585893243 20417765772540843878839865)
          ·
            refine ⟨15313324329405632909129899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20417765772540843878839865 15313324329405632909129899)
            ·
              refine ⟨22969986494108449363694849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15313324329405632909129899 22969986494108449363694849)
              ·
                refine ⟨17227489870581337022771137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22969986494108449363694849 17227489870581337022771137)
                ·
                  refine ⟨12920617402936002767078353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17227489870581337022771137 12920617402936002767078353)
                  ·
                    refine ⟨9690463052202002075308765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12920617402936002767078353 9690463052202002075308765)
                    ·
                      refine ⟨3633923644575750778240787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9690463052202002075308765 3633923644575750778240787)
                      ·
                        rfl

theorem cell23_7077041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_7077041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7077041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7077041 prefixEnd_7077041 := by exact prefixLift 7077041
  have htrace : WordTrace (prefixWord ++ tailWord_7077041) baseStart_7077041 baseEnd_7077041 := by
    simpa [prefixWord, tailWord_7077041, baseEnd_7077041] using wordTrace_append hprefix tailTrace_7077041
  have hstable : (prefixWord ++ tailWord_7077041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7077041).length < 2 ^ (prefixWord ++ tailWord_7077041).sum := by decide
  have hdescent : baseEnd_7077041 < baseStart_7077041 := by decide
  rcases family_descends (prefixWord ++ tailWord_7077041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7077064 : List Nat := [2, 1, 3, 1, 2, 1, 2, 1, 3, 5, 2]
def baseStart_7077064 : Nat := 118140960795 + 7077064 * 2 ^ 59
def prefixEnd_7077064 : Nat := 4983230072969 + 3 ^ 40 * 7077064 * 2
def baseEnd_7077064 : Nat := 3633935454630804188253181

theorem tailTrace_7077064 : CollatzResearch.WordTrace tailWord_7077064 prefixEnd_7077064 3633935454630804188253181 := by
  unfold tailWord_7077064
  simp only [CollatzResearch.WordTrace]
  refine ⟨129060864816506634574735123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172081153088675512766313497 129060864816506634574735123)
  ·
    refine ⟨193591297224759951862102685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129060864816506634574735123 193591297224759951862102685)
    ·
      refine ⟨72596736459284981948288507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193591297224759951862102685 72596736459284981948288507)
      ·
        refine ⟨108895104688927472922432761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72596736459284981948288507 108895104688927472922432761)
        ·
          refine ⟨81671328516695604691824571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108895104688927472922432761 81671328516695604691824571)
          ·
            refine ⟨122506992775043407037736857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81671328516695604691824571 122506992775043407037736857)
            ·
              refine ⟨91880244581282555278302643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122506992775043407037736857 91880244581282555278302643)
              ·
                refine ⟨137820366871923832917453965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91880244581282555278302643 137820366871923832917453965)
                ·
                  refine ⟨51682637576971437344045237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 137820366871923832917453965 51682637576971437344045237)
                  ·
                    refine ⟨4845247272841072251004241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51682637576971437344045237 4845247272841072251004241)
                    ·
                      refine ⟨3633935454630804188253181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4845247272841072251004241 3633935454630804188253181)
                      ·
                        rfl

theorem cell23_7077064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 1, 3, 5, 2].length) (baseStart_7077064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7077064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7077064 prefixEnd_7077064 := by exact prefixLift 7077064
  have htrace : WordTrace (prefixWord ++ tailWord_7077064) baseStart_7077064 baseEnd_7077064 := by
    simpa [prefixWord, tailWord_7077064, baseEnd_7077064] using wordTrace_append hprefix tailTrace_7077064
  have hstable : (prefixWord ++ tailWord_7077064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7077064).length < 2 ^ (prefixWord ++ tailWord_7077064).sum := by decide
  have hdescent : baseEnd_7077064 < baseStart_7077064 := by decide
  rcases family_descends (prefixWord ++ tailWord_7077064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7077074 : List Nat := [3, 2, 2, 2, 1, 1, 3, 1, 3, 5]
def baseStart_7077074 : Nat := 118140960795 + 7077074 * 2 ^ 59
def prefixEnd_7077074 : Nat := 4983230072969 + 3 ^ 40 * 7077074 * 2
def baseEnd_7077074 : Nat := 1211313529812449716376045

theorem tailTrace_7077074 : CollatzResearch.WordTrace tailWord_7077074 prefixEnd_7077074 1211313529812449716376045 := by
  unfold tailWord_7077074
  simp only [CollatzResearch.WordTrace]
  refine ⟨64530523590744260214333569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172081396241984693904889517 64530523590744260214333569)
  ·
    refine ⟨48397892693058195160750177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64530523590744260214333569 48397892693058195160750177)
    ·
      refine ⟨36298419519793646370562633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48397892693058195160750177 36298419519793646370562633)
      ·
        refine ⟨27223814639845234777921975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36298419519793646370562633 27223814639845234777921975)
        ·
          refine ⟨40835721959767852166882963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27223814639845234777921975 40835721959767852166882963)
          ·
            refine ⟨61253582939651778250324445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40835721959767852166882963 61253582939651778250324445)
            ·
              refine ⟨22970093602369416843871667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61253582939651778250324445 22970093602369416843871667)
              ·
                refine ⟨34455140403554125265807501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22970093602369416843871667 34455140403554125265807501)
                ·
                  refine ⟨12920677651332796974677813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34455140403554125265807501 12920677651332796974677813)
                  ·
                    refine ⟨1211313529812449716376045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12920677651332796974677813 1211313529812449716376045)
                    ·
                      rfl

theorem cell23_7077074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 1, 3, 5].length) (baseStart_7077074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7077074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7077074 prefixEnd_7077074 := by exact prefixLift 7077074
  have htrace : WordTrace (prefixWord ++ tailWord_7077074) baseStart_7077074 baseEnd_7077074 := by
    simpa [prefixWord, tailWord_7077074, baseEnd_7077074] using wordTrace_append hprefix tailTrace_7077074
  have hstable : (prefixWord ++ tailWord_7077074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7077074).length < 2 ^ (prefixWord ++ tailWord_7077074).sum := by decide
  have hdescent : baseEnd_7077074 < baseStart_7077074 := by decide
  rcases family_descends (prefixWord ++ tailWord_7077074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7077087 : List Nat := [1, 1, 2, 3, 2, 1, 3, 1, 3, 6]
def baseStart_7077087 : Nat := 118140960795 + 7077087 * 2 ^ 59
def prefixEnd_7077087 : Nat := 4983230072969 + 3 ^ 40 * 7077087 * 2
def baseEnd_7077087 : Nat := 1211315754895285866088525

theorem tailTrace_7077087 : CollatzResearch.WordTrace tailWord_7077087 prefixEnd_7077087 1211315754895285866088525 := by
  unfold tailWord_7077087
  simp only [CollatzResearch.WordTrace]
  refine ⟨258122568511929944077557515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172081712341286629385038343 258122568511929944077557515)
  ·
    refine ⟨387183852767894916116336273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258122568511929944077557515 387183852767894916116336273)
    ·
      refine ⟨290387889575921187087252205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 387183852767894916116336273 290387889575921187087252205)
      ·
        refine ⟨108895458590970445157719577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 290387889575921187087252205 108895458590970445157719577)
        ·
          refine ⟨81671593943227833868289683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108895458590970445157719577 81671593943227833868289683)
          ·
            refine ⟨122507390914841750802434525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81671593943227833868289683 122507390914841750802434525)
            ·
              refine ⟨45940271593065656550912947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 122507390914841750802434525 45940271593065656550912947)
              ·
                refine ⟨68910407389598484826369421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45940271593065656550912947 68910407389598484826369421)
                ·
                  refine ⟨25841402771099431809888533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68910407389598484826369421 25841402771099431809888533)
                  ·
                    refine ⟨1211315754895285866088525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25841402771099431809888533 1211315754895285866088525)
                    ·
                      rfl

theorem cell23_7077087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 1, 3, 6].length) (baseStart_7077087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7077087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7077087 prefixEnd_7077087 := by exact prefixLift 7077087
  have htrace : WordTrace (prefixWord ++ tailWord_7077087) baseStart_7077087 baseEnd_7077087 := by
    simpa [prefixWord, tailWord_7077087, baseEnd_7077087] using wordTrace_append hprefix tailTrace_7077087
  have hstable : (prefixWord ++ tailWord_7077087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7077087).length < 2 ^ (prefixWord ++ tailWord_7077087).sum := by decide
  have hdescent : baseEnd_7077087 < baseStart_7077087 := by decide
  rcases family_descends (prefixWord ++ tailWord_7077087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7077114 : List Nat := [3, 1, 1, 1, 1, 4, 1, 1, 5, 2, 3]
def baseStart_7077114 : Nat := 118140960795 + 7077114 * 2 ^ 59
def prefixEnd_7077114 : Nat := 4983230072969 + 3 ^ 40 * 7077114 * 2
def baseEnd_7077114 : Nat := 3633961128663528992627951

theorem tailTrace_7077114 : CollatzResearch.WordTrace tailWord_7077114 prefixEnd_7077114 3633961128663528992627951 := by
  unfold tailWord_7077114
  simp only [CollatzResearch.WordTrace]
  refine ⟨64530888320708031922197599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172082368855221418459193597 64530888320708031922197599)
  ·
    refine ⟨96796332481062047883296399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64530888320708031922197599 96796332481062047883296399)
    ·
      refine ⟨145194498721593071824944599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96796332481062047883296399 145194498721593071824944599)
      ·
        refine ⟨217791748082389607737416899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145194498721593071824944599 217791748082389607737416899)
        ·
          refine ⟨326687622123584411606125349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217791748082389607737416899 326687622123584411606125349)
          ·
            refine ⟨61253929148172077176148503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 326687622123584411606125349 61253929148172077176148503)
            ·
              refine ⟨91880893722258115764222755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61253929148172077176148503 91880893722258115764222755)
              ·
                refine ⟨137821340583387173646334133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91880893722258115764222755 137821340583387173646334133)
                ·
                  refine ⟨12920750679692547529343825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 137821340583387173646334133 12920750679692547529343825)
                  ·
                    refine ⟨9690563009769410647007869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12920750679692547529343825 9690563009769410647007869)
                    ·
                      refine ⟨3633961128663528992627951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9690563009769410647007869 3633961128663528992627951)
                      ·
                        rfl

theorem cell23_7077114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 1, 5, 2, 3].length) (baseStart_7077114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7077114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7077114 prefixEnd_7077114 := by exact prefixLift 7077114
  have htrace : WordTrace (prefixWord ++ tailWord_7077114) baseStart_7077114 baseEnd_7077114 := by
    simpa [prefixWord, tailWord_7077114, baseEnd_7077114] using wordTrace_append hprefix tailTrace_7077114
  have hstable : (prefixWord ++ tailWord_7077114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7077114).length < 2 ^ (prefixWord ++ tailWord_7077114).sum := by decide
  have hdescent : baseEnd_7077114 < baseStart_7077114 := by decide
  rcases family_descends (prefixWord ++ tailWord_7077114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7077121 : List Nat := [1, 2, 4, 1, 1, 3, 2, 3, 2, 4]
def baseStart_7077121 : Nat := 118140960795 + 7077121 * 2 ^ 59
def prefixEnd_7077121 : Nat := 4983230072969 + 3 ^ 40 * 7077121 * 2
def baseEnd_7077121 : Nat := 1211321574342703488413473

theorem tailTrace_7077121 : CollatzResearch.WordTrace tailWord_7077121 prefixEnd_7077121 1211321574342703488413473 := by
  unfold tailWord_7077121
  simp only [CollatzResearch.WordTrace]
  refine ⟨258123808593806767884295217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172082539062537845256196811 258123808593806767884295217)
  ·
    refine ⟨193592856445355075913221413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258123808593806767884295217 193592856445355075913221413)
    ·
      refine ⟨36298660583504076733729015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 193592856445355075913221413 36298660583504076733729015)
      ·
        refine ⟨54447990875256115100593523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36298660583504076733729015 54447990875256115100593523)
        ·
          refine ⟨81671986312884172650890285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54447990875256115100593523 81671986312884172650890285)
          ·
            refine ⟨30626994867331564744083857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81671986312884172650890285 30626994867331564744083857)
            ·
              refine ⟨22970246150498673558062893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30626994867331564744083857 22970246150498673558062893)
              ·
                refine ⟨8613842306437002584273585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22970246150498673558062893 8613842306437002584273585)
                ·
                  refine ⟨6460381729827751938205189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8613842306437002584273585 6460381729827751938205189)
                  ·
                    refine ⟨1211321574342703488413473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6460381729827751938205189 1211321574342703488413473)
                    ·
                      rfl

theorem cell23_7077121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 3, 2, 4].length) (baseStart_7077121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7077121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7077121 prefixEnd_7077121 := by exact prefixLift 7077121
  have htrace : WordTrace (prefixWord ++ tailWord_7077121) baseStart_7077121 baseEnd_7077121 := by
    simpa [prefixWord, tailWord_7077121, baseEnd_7077121] using wordTrace_append hprefix tailTrace_7077121
  have hstable : (prefixWord ++ tailWord_7077121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7077121).length < 2 ^ (prefixWord ++ tailWord_7077121).sum := by decide
  have hdescent : baseEnd_7077121 < baseStart_7077121 := by decide
  rcases family_descends (prefixWord ++ tailWord_7077121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7077148 : List Nat := [2, 2, 3, 1, 1, 1, 6, 1, 1, 2, 3]
def baseStart_7077148 : Nat := 118140960795 + 7077148 * 2 ^ 59
def prefixEnd_7077148 : Nat := 4983230072969 + 3 ^ 40 * 7077148 * 2
def baseEnd_7077148 : Nat := 3633978587005781859602795

theorem tailTrace_7077148 : CollatzResearch.WordTrace tailWord_7077148 prefixEnd_7077148 3633978587005781859602795 := by
  unfold tailWord_7077148
  simp only [CollatzResearch.WordTrace]
  refine ⟨129062396682354475747764049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172083195576472634330352065 129062396682354475747764049)
  ·
    refine ⟨96796797511765856810823037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129062396682354475747764049 96796797511765856810823037)
    ·
      refine ⟨36298799066912196304058639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96796797511765856810823037 36298799066912196304058639)
      ·
        refine ⟨54448198600368294456087959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36298799066912196304058639 54448198600368294456087959)
        ·
          refine ⟨81672297900552441684131939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54448198600368294456087959 81672297900552441684131939)
          ·
            refine ⟨122508446850828662526197909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81672297900552441684131939 122508446850828662526197909)
            ·
              refine ⟨5742583446132593555915527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 122508446850828662526197909 5742583446132593555915527)
              ·
                refine ⟨8613875169198890333873291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5742583446132593555915527 8613875169198890333873291)
                ·
                  refine ⟨12920812753798335500809937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8613875169198890333873291 12920812753798335500809937)
                  ·
                    refine ⟨9690609565348751625607453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12920812753798335500809937 9690609565348751625607453)
                    ·
                      refine ⟨3633978587005781859602795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9690609565348751625607453 3633978587005781859602795)
                      ·
                        rfl

theorem cell23_7077148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 6, 1, 1, 2, 3].length) (baseStart_7077148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7077148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7077148 prefixEnd_7077148 := by exact prefixLift 7077148
  have htrace : WordTrace (prefixWord ++ tailWord_7077148) baseStart_7077148 baseEnd_7077148 := by
    simpa [prefixWord, tailWord_7077148, baseEnd_7077148] using wordTrace_append hprefix tailTrace_7077148
  have hstable : (prefixWord ++ tailWord_7077148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7077148).length < 2 ^ (prefixWord ++ tailWord_7077148).sum := by decide
  have hdescent : baseEnd_7077148 < baseStart_7077148 := by decide
  rcases family_descends (prefixWord ++ tailWord_7077148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7077162 : List Nat := [3, 1, 4, 2, 1, 1, 2, 4, 1, 2, 2]
def baseStart_7077162 : Nat := 118140960795 + 7077162 * 2 ^ 59
def prefixEnd_7077162 : Nat := 4983230072969 + 3 ^ 40 * 7077162 * 2
def baseEnd_7077162 : Nat := 3633985775734944804827731

theorem tailTrace_7077162 : CollatzResearch.WordTrace tailWord_7077162 prefixEnd_7077162 3633985775734944804827731 := by
  unfold tailWord_7077162
  simp only [CollatzResearch.WordTrace]
  refine ⟨64531325996664557971634435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172083535991105487924358493 64531325996664557971634435)
  ·
    refine ⟨96796988994996836957451653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64531325996664557971634435 96796988994996836957451653)
    ·
      refine ⟨18149435436561906929522185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96796988994996836957451653 18149435436561906929522185)
      ·
        refine ⟨13612076577421430197141639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18149435436561906929522185 13612076577421430197141639)
        ·
          refine ⟨20418114866132145295712459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13612076577421430197141639 20418114866132145295712459)
          ·
            refine ⟨30627172299198217943568689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20418114866132145295712459 30627172299198217943568689)
            ·
              refine ⟨22970379224398663457676517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30627172299198217943568689 22970379224398663457676517)
              ·
                refine ⟨4306946104574749398314347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22970379224398663457676517 4306946104574749398314347)
                ·
                  refine ⟨6460419156862124097471521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4306946104574749398314347 6460419156862124097471521)
                  ·
                    refine ⟨4845314367646593073103641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6460419156862124097471521 4845314367646593073103641)
                    ·
                      refine ⟨3633985775734944804827731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4845314367646593073103641 3633985775734944804827731)
                      ·
                        rfl

theorem cell23_7077162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 4, 1, 2, 2].length) (baseStart_7077162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7077162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7077162 prefixEnd_7077162 := by exact prefixLift 7077162
  have htrace : WordTrace (prefixWord ++ tailWord_7077162) baseStart_7077162 baseEnd_7077162 := by
    simpa [prefixWord, tailWord_7077162, baseEnd_7077162] using wordTrace_append hprefix tailTrace_7077162
  have hstable : (prefixWord ++ tailWord_7077162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7077162).length < 2 ^ (prefixWord ++ tailWord_7077162).sum := by decide
  have hdescent : baseEnd_7077162 < baseStart_7077162 := by decide
  rcases family_descends (prefixWord ++ tailWord_7077162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7077201 : List Nat := [1, 2, 2, 1, 4, 1, 2, 1, 3, 4, 2]
def baseStart_7077201 : Nat := 118140960795 + 7077201 * 2 ^ 59
def prefixEnd_7077201 : Nat := 4983230072969 + 3 ^ 40 * 7077201 * 2
def baseEnd_7077201 : Nat := 3634005801480470152240051

theorem tailTrace_7077201 : CollatzResearch.WordTrace tailWord_7077201 prefixEnd_7077201 3634005801480470152240051 := by
  unfold tailWord_7077201
  simp only [CollatzResearch.WordTrace]
  refine ⟨258126726433516941547207457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172084484289011294364804971 258126726433516941547207457)
  ·
    refine ⟨193595044825137706160405593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258126726433516941547207457 193595044825137706160405593)
    ·
      refine ⟨145196283618853279620304195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193595044825137706160405593 145196283618853279620304195)
      ·
        refine ⟨217794425428279919430456293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145196283618853279620304195 217794425428279919430456293)
        ·
          refine ⟨40836454767802484893210555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 217794425428279919430456293 40836454767802484893210555)
          ·
            refine ⟨61254682151703727339815833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40836454767802484893210555 61254682151703727339815833)
            ·
              refine ⟨45941011613777795504861875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61254682151703727339815833 45941011613777795504861875)
              ·
                refine ⟨68911517420666693257292813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45941011613777795504861875 68911517420666693257292813)
                ·
                  refine ⟨25841819032750009971484805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68911517420666693257292813 25841819032750009971484805)
                  ·
                    refine ⟨4845341068640626869653401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25841819032750009971484805 4845341068640626869653401)
                    ·
                      refine ⟨3634005801480470152240051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4845341068640626869653401 3634005801480470152240051)
                      ·
                        rfl

theorem cell23_7077201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 1, 3, 4, 2].length) (baseStart_7077201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7077201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7077201 prefixEnd_7077201 := by exact prefixLift 7077201
  have htrace : WordTrace (prefixWord ++ tailWord_7077201) baseStart_7077201 baseEnd_7077201 := by
    simpa [prefixWord, tailWord_7077201, baseEnd_7077201] using wordTrace_append hprefix tailTrace_7077201
  have hstable : (prefixWord ++ tailWord_7077201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7077201).length < 2 ^ (prefixWord ++ tailWord_7077201).sum := by decide
  have hdescent : baseEnd_7077201 < baseStart_7077201 := by decide
  rcases family_descends (prefixWord ++ tailWord_7077201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7077213 : List Nat := [1, 4, 5, 1, 1, 1, 3, 2, 1, 2, 2]
def baseStart_7077213 : Nat := 118140960795 + 7077213 * 2 ^ 59
def prefixEnd_7077213 : Nat := 4983230072969 + 3 ^ 40 * 7077213 * 2
def baseEnd_7077213 : Nat := 3634011963248324105289997

theorem tailTrace_7077213 : CollatzResearch.WordTrace tailWord_7077213 prefixEnd_7077213 3634011963248324105289997 := by
  unfold tailWord_7077213
  simp only [CollatzResearch.WordTrace]
  refine ⟨258127164109473467596644293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172084776072982311731096195 258127164109473467596644293)
  ·
    refine ⟨48398843270526275174370805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 258127164109473467596644293 48398843270526275174370805)
    ·
      refine ⟨4537391556611838297597263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 48398843270526275174370805 4537391556611838297597263)
      ·
        refine ⟨6806087334917757446395895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4537391556611838297597263 6806087334917757446395895)
        ·
          refine ⟨10209131002376636169593843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6806087334917757446395895 10209131002376636169593843)
          ·
            refine ⟨15313696503564954254390765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10209131002376636169593843 15313696503564954254390765)
            ·
              refine ⟨5742636188836857845396537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15313696503564954254390765 5742636188836857845396537)
              ·
                refine ⟨4306977141627643384047403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5742636188836857845396537 4306977141627643384047403)
                ·
                  refine ⟨6460465712441465076071105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4306977141627643384047403 6460465712441465076071105)
                  ·
                    refine ⟨4845349284331098807053329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6460465712441465076071105 4845349284331098807053329)
                    ·
                      refine ⟨3634011963248324105289997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4845349284331098807053329 3634011963248324105289997)
                      ·
                        rfl

theorem cell23_7077213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 3, 2, 1, 2, 2].length) (baseStart_7077213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7077213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7077213 prefixEnd_7077213 := by exact prefixLift 7077213
  have htrace : WordTrace (prefixWord ++ tailWord_7077213) baseStart_7077213 baseEnd_7077213 := by
    simpa [prefixWord, tailWord_7077213, baseEnd_7077213] using wordTrace_append hprefix tailTrace_7077213
  have hstable : (prefixWord ++ tailWord_7077213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7077213).length < 2 ^ (prefixWord ++ tailWord_7077213).sum := by decide
  have hdescent : baseEnd_7077213 < baseStart_7077213 := by decide
  rcases family_descends (prefixWord ++ tailWord_7077213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7077284 : List Nat := [2, 3, 1, 2, 1, 1, 1, 2, 2, 8]
def baseStart_7077284 : Nat := 118140960795 + 7077284 * 2 ^ 59
def prefixEnd_7077284 : Nat := 4983230072969 + 3 ^ 40 * 7077284 * 2
def baseEnd_7077284 : Nat := 1211349473458264442500723

theorem tailTrace_7077284 : CollatzResearch.WordTrace tailWord_7077284 prefixEnd_7077284 1211349473458264442500723 := by
  unfold tailWord_7077284
  simp only [CollatzResearch.WordTrace]
  refine ⟨129064876846108123361239453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172086502461477497814985937 129064876846108123361239453)
  ·
    refine ⟨48399328817290546260464795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129064876846108123361239453 48399328817290546260464795)
    ·
      refine ⟨72598993225935819390697193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48399328817290546260464795 72598993225935819390697193)
      ·
        refine ⟨54449244919451864543022895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72598993225935819390697193 54449244919451864543022895)
        ·
          refine ⟨81673867379177796814534343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54449244919451864543022895 81673867379177796814534343)
          ·
            refine ⟨122510801068766695221801515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81673867379177796814534343 122510801068766695221801515)
            ·
              refine ⟨183766201603150042832702273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122510801068766695221801515 183766201603150042832702273)
              ·
                refine ⟨137824651202362532124526705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 183766201603150042832702273 137824651202362532124526705)
                ·
                  refine ⟨103368488401771899093395029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 137824651202362532124526705 103368488401771899093395029)
                  ·
                    refine ⟨1211349473458264442500723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 103368488401771899093395029 1211349473458264442500723)
                    ·
                      rfl

theorem cell23_7077284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 2, 2, 8].length) (baseStart_7077284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7077284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7077284 prefixEnd_7077284 := by exact prefixLift 7077284
  have htrace : WordTrace (prefixWord ++ tailWord_7077284) baseStart_7077284 baseEnd_7077284 := by
    simpa [prefixWord, tailWord_7077284, baseEnd_7077284] using wordTrace_append hprefix tailTrace_7077284
  have hstable : (prefixWord ++ tailWord_7077284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7077284).length < 2 ^ (prefixWord ++ tailWord_7077284).sum := by decide
  have hdescent : baseEnd_7077284 < baseStart_7077284 := by decide
  rcases family_descends (prefixWord ++ tailWord_7077284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7077305 : List Nat := [1, 2, 1, 4, 5, 1, 1, 1, 2, 5]
def baseStart_7077305 : Nat := 118140960795 + 7077305 * 2 ^ 59
def prefixEnd_7077305 : Nat := 4983230072969 + 3 ^ 40 * 7077305 * 2
def baseEnd_7077305 : Nat := 1211353067822845915113191

theorem tailTrace_7077305 : CollatzResearch.WordTrace tailWord_7077305 prefixEnd_7077305 1211353067822845915113191 := by
  unfold tailWord_7077305
  simp only [CollatzResearch.WordTrace]
  refine ⟨258130519625140167308993369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172087013083426778205995579 258130519625140167308993369)
  ·
    refine ⟨193597889718855125481745027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258130519625140167308993369 193597889718855125481745027)
    ·
      refine ⟨290396834578282688222617541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193597889718855125481745027 290396834578282688222617541)
      ·
        refine ⟨54449406483428004041740789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 290396834578282688222617541 54449406483428004041740789)
        ·
          refine ⟨5104631857821375378913199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54449406483428004041740789 5104631857821375378913199)
          ·
            refine ⟨7656947786732063068369799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5104631857821375378913199 7656947786732063068369799)
            ·
              refine ⟨11485421680098094602554699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7656947786732063068369799 11485421680098094602554699)
              ·
                refine ⟨17228132520147141903832049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11485421680098094602554699 17228132520147141903832049)
                ·
                  refine ⟨12921099390110356427874037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17228132520147141903832049 12921099390110356427874037)
                  ·
                    refine ⟨1211353067822845915113191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12921099390110356427874037 1211353067822845915113191)
                    ·
                      rfl

theorem cell23_7077305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 1, 1, 2, 5].length) (baseStart_7077305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7077305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7077305 prefixEnd_7077305 := by exact prefixLift 7077305
  have htrace : WordTrace (prefixWord ++ tailWord_7077305) baseStart_7077305 baseEnd_7077305 := by
    simpa [prefixWord, tailWord_7077305, baseEnd_7077305] using wordTrace_append hprefix tailTrace_7077305
  have hstable : (prefixWord ++ tailWord_7077305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7077305).length < 2 ^ (prefixWord ++ tailWord_7077305).sum := by decide
  have hdescent : baseEnd_7077305 < baseStart_7077305 := by decide
  rcases family_descends (prefixWord ++ tailWord_7077305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7077308 : List Nat := [2, 2, 2, 4, 2, 1, 1, 1, 1, 3, 4]
def baseStart_7077308 : Nat := 118140960795 + 7077308 * 2 ^ 59
def prefixEnd_7077308 : Nat := 4983230072969 + 3 ^ 40 * 7077308 * 2
def baseEnd_7077308 : Nat := 3634060743910501233602059

theorem tailTrace_7077308 : CollatzResearch.WordTrace tailWord_7077308 prefixEnd_7077308 3634060743910501233602059 := by
  unfold tailWord_7077308
  simp only [CollatzResearch.WordTrace]
  refine ⟨129065314522064649410676289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172087086029419532547568385 129065314522064649410676289)
  ·
    refine ⟨96798985891548487058007217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129065314522064649410676289 96798985891548487058007217)
    ·
      refine ⟨72599239418661365293505413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96798985891548487058007217 72599239418661365293505413)
      ·
        refine ⟨13612357390999005992532265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72599239418661365293505413 13612357390999005992532265)
        ·
          refine ⟨10209268043249254494399199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13612357390999005992532265 10209268043249254494399199)
          ·
            refine ⟨15313902064873881741598799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10209268043249254494399199 15313902064873881741598799)
            ·
              refine ⟨22970853097310822612398199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15313902064873881741598799 22970853097310822612398199)
              ·
                refine ⟨34456279645966233918597299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22970853097310822612398199 34456279645966233918597299)
                ·
                  refine ⟨51684419468949350877895949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34456279645966233918597299 51684419468949350877895949)
                  ·
                    refine ⟨19381657300856006579210981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51684419468949350877895949 19381657300856006579210981)
                    ·
                      refine ⟨3634060743910501233602059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19381657300856006579210981 3634060743910501233602059)
                      ·
                        rfl

theorem cell23_7077308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_7077308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7077308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7077308 prefixEnd_7077308 := by exact prefixLift 7077308
  have htrace : WordTrace (prefixWord ++ tailWord_7077308) baseStart_7077308 baseEnd_7077308 := by
    simpa [prefixWord, tailWord_7077308, baseEnd_7077308] using wordTrace_append hprefix tailTrace_7077308
  have hstable : (prefixWord ++ tailWord_7077308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7077308).length < 2 ^ (prefixWord ++ tailWord_7077308).sum := by decide
  have hdescent : baseEnd_7077308 < baseStart_7077308 := by decide
  rcases family_descends (prefixWord ++ tailWord_7077308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7077344 : List Nat := [2, 1, 1, 3, 1, 1, 2, 1, 2, 9]
def baseStart_7077344 : Nat := 118140960795 + 7077344 * 2 ^ 59
def prefixEnd_7077344 : Nat := 4983230072969 + 3 ^ 40 * 7077344 * 2
def baseEnd_7077344 : Nat := 1211359743071354364250631

theorem tailTrace_7077344 : CollatzResearch.WordTrace tailWord_7077344 prefixEnd_7077344 1211359743071354364250631 := by
  unfold tailWord_7077344
  simp only [CollatzResearch.WordTrace]
  refine ⟨129065971035999438484831543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172087961381332584646442057 129065971035999438484831543)
  ·
    refine ⟨193598956553999157727247315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129065971035999438484831543 193598956553999157727247315)
    ·
      refine ⟨290398434830998736590870973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193598956553999157727247315 290398434830998736590870973)
      ·
        refine ⟨108899413061624526221576615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 290398434830998736590870973 108899413061624526221576615)
        ·
          refine ⟨163349119592436789332364923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108899413061624526221576615 163349119592436789332364923)
          ·
            refine ⟨245023679388655183998547385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163349119592436789332364923 245023679388655183998547385)
            ·
              refine ⟨183767759541491387998910539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 245023679388655183998547385 183767759541491387998910539)
              ·
                refine ⟨275651639312237081998365809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 183767759541491387998910539 275651639312237081998365809)
                ·
                  refine ⟨206738729484177811498774357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 275651639312237081998365809 206738729484177811498774357)
                  ·
                    refine ⟨1211359743071354364250631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 206738729484177811498774357 1211359743071354364250631)
                    ·
                      rfl

theorem cell23_7077344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 2, 9].length) (baseStart_7077344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7077344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7077344 prefixEnd_7077344 := by exact prefixLift 7077344
  have htrace : WordTrace (prefixWord ++ tailWord_7077344) baseStart_7077344 baseEnd_7077344 := by
    simpa [prefixWord, tailWord_7077344, baseEnd_7077344] using wordTrace_append hprefix tailTrace_7077344
  have hstable : (prefixWord ++ tailWord_7077344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7077344).length < 2 ^ (prefixWord ++ tailWord_7077344).sum := by decide
  have hdescent : baseEnd_7077344 < baseStart_7077344 := by decide
  rcases family_descends (prefixWord ++ tailWord_7077344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7077368 : List Nat := [2, 1, 2, 1, 1, 5, 2, 1, 1, 5, 2]
def baseStart_7077368 : Nat := 118140960795 + 7077368 * 2 ^ 59
def prefixEnd_7077368 : Nat := 4983230072969 + 3 ^ 40 * 7077368 * 2
def baseEnd_7077368 : Nat := 3634091552749770998851783

theorem tailTrace_7077368 : CollatzResearch.WordTrace tailWord_7077368 prefixEnd_7077368 3634091552749770998851783 := by
  unfold tailWord_7077368
  simp only [CollatzResearch.WordTrace]
  refine ⟨129066408711955964534268379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172088544949274619379024505 129066408711955964534268379)
  ·
    refine ⟨193599613067933946801402569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129066408711955964534268379 193599613067933946801402569)
    ·
      refine ⟨145199709800950460101051927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193599613067933946801402569 145199709800950460101051927)
      ·
        refine ⟨217799564701425690151577891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145199709800950460101051927 217799564701425690151577891)
        ·
          refine ⟨326699347052138535227366837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217799564701425690151577891 326699347052138535227366837)
          ·
            refine ⟨30628063786137987677565641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 326699347052138535227366837 30628063786137987677565641)
            ·
              refine ⟨22971047839603490758174231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30628063786137987677565641 22971047839603490758174231)
              ·
                refine ⟨34456571759405236137261347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22971047839603490758174231 34456571759405236137261347)
                ·
                  refine ⟨51684857639107854205892021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34456571759405236137261347 51684857639107854205892021)
                  ·
                    refine ⟨4845455403666361331802377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51684857639107854205892021 4845455403666361331802377)
                    ·
                      refine ⟨3634091552749770998851783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4845455403666361331802377 3634091552749770998851783)
                      ·
                        rfl

theorem cell23_7077368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 1, 1, 5, 2].length) (baseStart_7077368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7077368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7077368 prefixEnd_7077368 := by exact prefixLift 7077368
  have htrace : WordTrace (prefixWord ++ tailWord_7077368) baseStart_7077368 baseEnd_7077368 := by
    simpa [prefixWord, tailWord_7077368, baseEnd_7077368] using wordTrace_append hprefix tailTrace_7077368
  have hstable : (prefixWord ++ tailWord_7077368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7077368).length < 2 ^ (prefixWord ++ tailWord_7077368).sum := by decide
  have hdescent : baseEnd_7077368 < baseStart_7077368 := by decide
  rcases family_descends (prefixWord ++ tailWord_7077368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7077375 : List Nat := [1, 1, 2, 2, 1, 2, 2, 7, 1, 1, 3]
def baseStart_7077375 : Nat := 118140960795 + 7077375 * 2 ^ 59
def prefixEnd_7077375 : Nat := 4983230072969 + 3 ^ 40 * 7077375 * 2
def baseEnd_7077375 : Nat := 3634095147114352471464251

theorem tailTrace_7077375 : CollatzResearch.WordTrace tailWord_7077375 prefixEnd_7077375 3634095147114352471464251 := by
  unfold tailWord_7077375
  simp only [CollatzResearch.WordTrace]
  refine ⟨258133072734886569264041579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172088715156591046176027719 258133072734886569264041579)
  ·
    refine ⟨387199609102329853896062369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258133072734886569264041579 387199609102329853896062369)
    ·
      refine ⟨290399706826747390422046777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 387199609102329853896062369 290399706826747390422046777)
      ·
        refine ⟨217799780120060542816535083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 290399706826747390422046777 217799780120060542816535083)
        ·
          refine ⟨326699670180090814224802625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217799780120060542816535083 326699670180090814224802625)
          ·
            refine ⟨245024752635068110668601969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 326699670180090814224802625 245024752635068110668601969)
            ·
              refine ⟨183768564476301083001451477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 245024752635068110668601969 183768564476301083001451477)
              ·
                refine ⟨4307075729913306632846519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 183768564476301083001451477 4307075729913306632846519)
                ·
                  refine ⟨6460613594869959949269779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4307075729913306632846519 6460613594869959949269779)
                  ·
                    refine ⟨9690920392304939923904669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6460613594869959949269779 9690920392304939923904669)
                    ·
                      refine ⟨3634095147114352471464251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9690920392304939923904669 3634095147114352471464251)
                      ·
                        rfl

theorem cell23_7077375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 7, 1, 1, 3].length) (baseStart_7077375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7077375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7077375 prefixEnd_7077375 := by exact prefixLift 7077375
  have htrace : WordTrace (prefixWord ++ tailWord_7077375) baseStart_7077375 baseEnd_7077375 := by
    simpa [prefixWord, tailWord_7077375, baseEnd_7077375] using wordTrace_append hprefix tailTrace_7077375
  have hstable : (prefixWord ++ tailWord_7077375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7077375).length < 2 ^ (prefixWord ++ tailWord_7077375).sum := by decide
  have hdescent : baseEnd_7077375 < baseStart_7077375 := by decide
  rcases family_descends (prefixWord ++ tailWord_7077375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7077381 : List Nat := [1, 3, 1, 1, 2, 2, 1, 2, 5, 1, 4]
def baseStart_7077381 : Nat := 118140960795 + 7077381 * 2 ^ 59
def prefixEnd_7077381 : Nat := 4983230072969 + 3 ^ 40 * 7077381 * 2
def baseEnd_7077381 : Nat := 3634098227998279447989223

theorem tailTrace_7077381 : CollatzResearch.WordTrace tailWord_7077381 prefixEnd_7077381 3634098227998279447989223 := by
  unfold tailWord_7077381
  simp only [CollatzResearch.WordTrace]
  refine ⟨258133291572864832288759997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172088861048576554859173331 258133291572864832288759997)
  ·
    refine ⟨96799984339824312108284999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 258133291572864832288759997 96799984339824312108284999)
    ·
      refine ⟨145199976509736468162427499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96799984339824312108284999 145199976509736468162427499)
      ·
        refine ⟨217799964764604702243641249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145199976509736468162427499 217799964764604702243641249)
        ·
          refine ⟨163349973573453526682730937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217799964764604702243641249 163349973573453526682730937)
          ·
            refine ⟨122512480180090145012048203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163349973573453526682730937 122512480180090145012048203)
            ·
              refine ⟨183768720270135217518072305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122512480180090145012048203 183768720270135217518072305)
              ·
                refine ⟨137826540202601413138554229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 183768720270135217518072305 137826540202601413138554229)
                ·
                  refine ⟨12921238143993882481739459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 137826540202601413138554229 12921238143993882481739459)
                  ·
                    refine ⟨19381857215990823722609189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12921238143993882481739459 19381857215990823722609189)
                    ·
                      refine ⟨3634098227998279447989223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19381857215990823722609189 3634098227998279447989223)
                      ·
                        rfl

theorem cell23_7077381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 2, 5, 1, 4].length) (baseStart_7077381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7077381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7077381 prefixEnd_7077381 := by exact prefixLift 7077381
  have htrace : WordTrace (prefixWord ++ tailWord_7077381) baseStart_7077381 baseEnd_7077381 := by
    simpa [prefixWord, tailWord_7077381, baseEnd_7077381] using wordTrace_append hprefix tailTrace_7077381
  have hstable : (prefixWord ++ tailWord_7077381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7077381).length < 2 ^ (prefixWord ++ tailWord_7077381).sum := by decide
  have hdescent : baseEnd_7077381 < baseStart_7077381 := by decide
  rcases family_descends (prefixWord ++ tailWord_7077381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7077391 : List Nat := [1, 1, 2, 1, 1, 1, 2, 2, 8, 4]
def baseStart_7077391 : Nat := 118140960795 + 7077391 * 2 ^ 59
def prefixEnd_7077391 : Nat := 4983230072969 + 3 ^ 40 * 7077391 * 2
def baseEnd_7077391 : Nat := 1211367787601608136288059

theorem tailTrace_7077391 : CollatzResearch.WordTrace tailWord_7077391 prefixEnd_7077391 1211367787601608136288059 := by
  unfold tailWord_7077391
  simp only [CollatzResearch.WordTrace]
  refine ⟨258133656302828603996624027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172089104201885735997749351 258133656302828603996624027)
  ·
    refine ⟨387200484454242905994936041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258133656302828603996624027 387200484454242905994936041)
    ·
      refine ⟨290400363340682179496202031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 387200484454242905994936041 290400363340682179496202031)
      ·
        refine ⟨435600545011023269244303047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290400363340682179496202031 435600545011023269244303047)
        ·
          refine ⟨653400817516534903866454571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 435600545011023269244303047 653400817516534903866454571)
          ·
            refine ⟨980101226274802355799681857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 653400817516534903866454571 980101226274802355799681857)
            ·
              refine ⟨735075919706101766849761393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 980101226274802355799681857 735075919706101766849761393)
              ·
                refine ⟨551306939779576325137321045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 735075919706101766849761393 551306939779576325137321045)
                ·
                  refine ⟨6460628200541910060202981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 551306939779576325137321045 6460628200541910060202981)
                  ·
                    refine ⟨1211367787601608136288059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6460628200541910060202981 1211367787601608136288059)
                    ·
                      rfl

theorem cell23_7077391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 8, 4].length) (baseStart_7077391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7077391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7077391 prefixEnd_7077391 := by exact prefixLift 7077391
  have htrace : WordTrace (prefixWord ++ tailWord_7077391) baseStart_7077391 baseEnd_7077391 := by
    simpa [prefixWord, tailWord_7077391, baseEnd_7077391] using wordTrace_append hprefix tailTrace_7077391
  have hstable : (prefixWord ++ tailWord_7077391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7077391).length < 2 ^ (prefixWord ++ tailWord_7077391).sum := by decide
  have hdescent : baseEnd_7077391 < baseStart_7077391 := by decide
  rcases family_descends (prefixWord ++ tailWord_7077391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7077461 : List Nat := [1, 3, 2, 2, 1, 1, 1, 2, 1, 4, 5]
def baseStart_7077461 : Nat := 118140960795 + 7077461 * 2 ^ 59
def prefixEnd_7077461 : Nat := 4983230072969 + 3 ^ 40 * 7077461 * 2
def baseEnd_7077461 : Nat := 3634139306450639134988855

theorem tailTrace_7077461 : CollatzResearch.WordTrace tailWord_7077461 prefixEnd_7077461 3634139306450639134988855 := by
  unfold tailWord_7077461
  simp only [CollatzResearch.WordTrace]
  refine ⟨258136209412575005951672237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172090806275050003967781491 258136209412575005951672237)
  ·
    refine ⟨96801078529715627231877089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 258136209412575005951672237 96801078529715627231877089)
    ·
      refine ⟨72600808897286720423907817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96801078529715627231877089 72600808897286720423907817)
      ·
        refine ⟨54450606672965040317930863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72600808897286720423907817 54450606672965040317930863)
        ·
          refine ⟨81675910009447560476896295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54450606672965040317930863 81675910009447560476896295)
          ·
            refine ⟨122513865014171340715344443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81675910009447560476896295 122513865014171340715344443)
            ·
              refine ⟨183770797521257011073016665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122513865014171340715344443 183770797521257011073016665)
              ·
                refine ⟨137828098140942758304762499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 183770797521257011073016665 137828098140942758304762499)
                ·
                  refine ⟨206742147211414137457143749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 137828098140942758304762499 206742147211414137457143749)
                  ·
                    refine ⟨38764152602140150773214453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 206742147211414137457143749 38764152602140150773214453)
                    ·
                      refine ⟨3634139306450639134988855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38764152602140150773214453 3634139306450639134988855)
                      ·
                        rfl

theorem cell23_7077461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 2, 1, 4, 5].length) (baseStart_7077461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7077461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7077461 prefixEnd_7077461 := by exact prefixLift 7077461
  have htrace : WordTrace (prefixWord ++ tailWord_7077461) baseStart_7077461 baseEnd_7077461 := by
    simpa [prefixWord, tailWord_7077461, baseEnd_7077461] using wordTrace_append hprefix tailTrace_7077461
  have hstable : (prefixWord ++ tailWord_7077461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7077461).length < 2 ^ (prefixWord ++ tailWord_7077461).sum := by decide
  have hdescent : baseEnd_7077461 < baseStart_7077461 := by decide
  rcases family_descends (prefixWord ++ tailWord_7077461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7077475 : List Nat := [1, 1, 1, 5, 1, 3, 2, 1, 3, 3, 2]
def baseStart_7077475 : Nat := 118140960795 + 7077475 * 2 ^ 59
def prefixEnd_7077475 : Nat := 4983230072969 + 3 ^ 40 * 7077475 * 2
def baseEnd_7077475 : Nat := 3634146495179802080213791

theorem tailTrace_7077475 : CollatzResearch.WordTrace tailWord_7077475 prefixEnd_7077475 3634146495179802080213791 := by
  unfold tailWord_7077475
  simp only [CollatzResearch.WordTrace]
  refine ⟨258136720034524286342681879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172091146689682857561787919 258136720034524286342681879)
  ·
    refine ⟨387205080051786429514022819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258136720034524286342681879 387205080051786429514022819)
    ·
      refine ⟨580807620077679644271034229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 387205080051786429514022819 580807620077679644271034229)
      ·
        refine ⟨54450714382282466650409459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 580807620077679644271034229 54450714382282466650409459)
        ·
          refine ⟨81676071573423699975614189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54450714382282466650409459 81676071573423699975614189)
          ·
            refine ⟨30628526840033887490855321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81676071573423699975614189 30628526840033887490855321)
            ·
              refine ⟨22971395130025415618141491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30628526840033887490855321 22971395130025415618141491)
              ·
                refine ⟨34457092695038123427212237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22971395130025415618141491 34457092695038123427212237)
                ·
                  refine ⟨12921409760639296285204589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34457092695038123427212237 12921409760639296285204589)
                  ·
                    refine ⟨4845528660239736106951721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12921409760639296285204589 4845528660239736106951721)
                    ·
                      refine ⟨3634146495179802080213791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4845528660239736106951721 3634146495179802080213791)
                      ·
                        rfl

theorem cell23_7077475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 1, 3, 3, 2].length) (baseStart_7077475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7077475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7077475 prefixEnd_7077475 := by exact prefixLift 7077475
  have htrace : WordTrace (prefixWord ++ tailWord_7077475) baseStart_7077475 baseEnd_7077475 := by
    simpa [prefixWord, tailWord_7077475, baseEnd_7077475] using wordTrace_append hprefix tailTrace_7077475
  have hstable : (prefixWord ++ tailWord_7077475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7077475).length < 2 ^ (prefixWord ++ tailWord_7077475).sum := by decide
  have hdescent : baseEnd_7077475 < baseStart_7077475 := by decide
  rcases family_descends (prefixWord ++ tailWord_7077475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7077486 : List Nat := [4, 1, 2, 2, 4, 1, 2, 1, 1, 2, 3]
def baseStart_7077486 : Nat := 118140960795 + 7077486 * 2 ^ 59
def prefixEnd_7077486 : Nat := 4983230072969 + 3 ^ 40 * 7077486 * 2
def baseEnd_7077486 : Nat := 3634152143467001537176241

theorem tailTrace_7077486 : CollatzResearch.WordTrace tailWord_7077486 prefixEnd_7077486 3634152143467001537176241 := by
  unfold tailWord_7077486
  simp only [CollatzResearch.WordTrace]
  refine ⟨32267140154685554402666539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172091414158322956814221541 32267140154685554402666539)
  ·
    refine ⟨48400710232028331603999809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32267140154685554402666539 48400710232028331603999809)
    ·
      refine ⟨36300532674021248702999857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48400710232028331603999809 36300532674021248702999857)
      ·
        refine ⟨27225399505515936527249893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36300532674021248702999857 27225399505515936527249893)
        ·
          refine ⟨5104762407284238098859355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27225399505515936527249893 5104762407284238098859355)
          ·
            refine ⟨7657143610926357148289033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5104762407284238098859355 7657143610926357148289033)
            ·
              refine ⟨5742857708194767861216775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7657143610926357148289033 5742857708194767861216775)
              ·
                refine ⟨8614286562292151791825163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5742857708194767861216775 8614286562292151791825163)
                ·
                  refine ⟨12921429843438227687737745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8614286562292151791825163 12921429843438227687737745)
                  ·
                    refine ⟨9691072382578670765803309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12921429843438227687737745 9691072382578670765803309)
                    ·
                      refine ⟨3634152143467001537176241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9691072382578670765803309 3634152143467001537176241)
                      ·
                        rfl

theorem cell23_7077486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 2, 1, 1, 2, 3].length) (baseStart_7077486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7077486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7077486 prefixEnd_7077486 := by exact prefixLift 7077486
  have htrace : WordTrace (prefixWord ++ tailWord_7077486) baseStart_7077486 baseEnd_7077486 := by
    simpa [prefixWord, tailWord_7077486, baseEnd_7077486] using wordTrace_append hprefix tailTrace_7077486
  have hstable : (prefixWord ++ tailWord_7077486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7077486).length < 2 ^ (prefixWord ++ tailWord_7077486).sum := by decide
  have hdescent : baseEnd_7077486 < baseStart_7077486 := by decide
  rcases family_descends (prefixWord ++ tailWord_7077486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7077491 : List Nat := [1, 1, 1, 2, 2, 1, 1, 2, 6, 1, 5]
def baseStart_7077491 : Nat := 118140960795 + 7077491 * 2 ^ 59
def prefixEnd_7077491 : Nat := 4983230072969 + 3 ^ 40 * 7077491 * 2
def baseEnd_7077491 : Nat := 3634154710870274017613717

theorem tailTrace_7077491 : CollatzResearch.WordTrace tailWord_7077491 prefixEnd_7077491 3634154710870274017613717 := by
  unfold tailWord_7077491
  simp only [CollatzResearch.WordTrace]
  refine ⟨258137303602466321075264327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172091535734977547383509551 258137303602466321075264327)
  ·
    refine ⟨387205955403699481612896491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258137303602466321075264327 387205955403699481612896491)
    ·
      refine ⟨580808933105549222419344737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 387205955403699481612896491 580808933105549222419344737)
      ·
        refine ⟨435606699829161916814508553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 580808933105549222419344737 435606699829161916814508553)
        ·
          refine ⟨326705024871871437610881415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 435606699829161916814508553 326705024871871437610881415)
          ·
            refine ⟨490057537307807156416322123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 326705024871871437610881415 490057537307807156416322123)
            ·
              refine ⟨735086305961710734624483185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 490057537307807156416322123 735086305961710734624483185)
              ·
                refine ⟨551314729471283050968362389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 735086305961710734624483185 551314729471283050968362389)
                ·
                  refine ⟨25842877943966393014141987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 551314729471283050968362389 25842877943966393014141987)
                  ·
                    refine ⟨38764316915949589521212981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25842877943966393014141987 38764316915949589521212981)
                    ·
                      refine ⟨3634154710870274017613717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38764316915949589521212981 3634154710870274017613717)
                      ·
                        rfl

theorem cell23_7077491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 6, 1, 5].length) (baseStart_7077491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7077491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7077491 prefixEnd_7077491 := by exact prefixLift 7077491
  have htrace : WordTrace (prefixWord ++ tailWord_7077491) baseStart_7077491 baseEnd_7077491 := by
    simpa [prefixWord, tailWord_7077491, baseEnd_7077491] using wordTrace_append hprefix tailTrace_7077491
  have hstable : (prefixWord ++ tailWord_7077491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7077491).length < 2 ^ (prefixWord ++ tailWord_7077491).sum := by decide
  have hdescent : baseEnd_7077491 < baseStart_7077491 := by decide
  rcases family_descends (prefixWord ++ tailWord_7077491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7077528 : List Nat := [2, 1, 2, 4, 1, 2, 2, 2, 7]
def baseStart_7077528 : Nat := 118140960795 + 7077528 * 2 ^ 59
def prefixEnd_7077528 : Nat := 4983230072969 + 3 ^ 40 * 7077528 * 2
def baseEnd_7077528 : Nat := 403797078850498930316783

theorem tailTrace_7077528 : CollatzResearch.WordTrace tailWord_7077528 prefixEnd_7077528 403797078850498930316783 := by
  unfold tailWord_7077528
  simp only [CollatzResearch.WordTrace]
  refine ⟨129069326551666138197180619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172092435402221517596240825 129069326551666138197180619)
  ·
    refine ⟨193603989827499207295770929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129069326551666138197180619 193603989827499207295770929)
    ·
      refine ⟨145202992370624405471828197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193603989827499207295770929 145202992370624405471828197)
      ·
        refine ⟨27225561069492076025967787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 145202992370624405471828197 27225561069492076025967787)
        ·
          refine ⟨40838341604238114038951681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27225561069492076025967787 40838341604238114038951681)
          ·
            refine ⟨30628756203178585529213761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40838341604238114038951681 30628756203178585529213761)
            ·
              refine ⟨22971567152383939146910321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30628756203178585529213761 22971567152383939146910321)
              ·
                refine ⟨17228675364287954360182741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22971567152383939146910321 17228675364287954360182741)
                ·
                  refine ⟨403797078850498930316783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17228675364287954360182741 403797078850498930316783)
                  ·
                    rfl

theorem cell23_7077528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 2, 7].length) (baseStart_7077528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7077528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7077528 prefixEnd_7077528 := by exact prefixLift 7077528
  have htrace : WordTrace (prefixWord ++ tailWord_7077528) baseStart_7077528 baseEnd_7077528 := by
    simpa [prefixWord, tailWord_7077528, baseEnd_7077528] using wordTrace_append hprefix tailTrace_7077528
  have hstable : (prefixWord ++ tailWord_7077528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7077528).length < 2 ^ (prefixWord ++ tailWord_7077528).sum := by decide
  have hdescent : baseEnd_7077528 < baseStart_7077528 := by decide
  rcases family_descends (prefixWord ++ tailWord_7077528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7077562 : List Nat := [3, 1, 1, 1, 2, 5, 3, 2, 5]
def baseStart_7077562 : Nat := 118140960795 + 7077562 * 2 ^ 59
def prefixEnd_7077562 : Nat := 4983230072969 + 3 ^ 40 * 7077562 * 2
def baseEnd_7077562 : Nat := 403799018666304804425099

theorem tailTrace_7077562 : CollatzResearch.WordTrace tailWord_7077562 prefixEnd_7077562 403799018666304804425099 := by
  unfold tailWord_7077562
  simp only [CollatzResearch.WordTrace]
  refine ⟨64534973296302275050274735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172093262123472733467399293 64534973296302275050274735)
  ·
    refine ⟨96802459944453412575412103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64534973296302275050274735 96802459944453412575412103)
    ·
      refine ⟨145203689916680118863118155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96802459944453412575412103 145203689916680118863118155)
      ·
        refine ⟨217805534875020178294677233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145203689916680118863118155 217805534875020178294677233)
        ·
          refine ⟨163354151156265133721007925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217805534875020178294677233 163354151156265133721007925)
          ·
            refine ⟨15314451670899856286344493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 163354151156265133721007925 15314451670899856286344493)
            ·
              refine ⟨5742919376587446107379185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15314451670899856286344493 5742919376587446107379185)
              ·
                refine ⟨4307189532440584580534389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5742919376587446107379185 4307189532440584580534389)
                ·
                  refine ⟨403799018666304804425099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4307189532440584580534389 403799018666304804425099)
                  ·
                    rfl

theorem cell23_7077562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 3, 2, 5].length) (baseStart_7077562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7077562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7077562 prefixEnd_7077562 := by exact prefixLift 7077562
  have htrace : WordTrace (prefixWord ++ tailWord_7077562) baseStart_7077562 baseEnd_7077562 := by
    simpa [prefixWord, tailWord_7077562, baseEnd_7077562] using wordTrace_append hprefix tailTrace_7077562
  have hstable : (prefixWord ++ tailWord_7077562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7077562).length < 2 ^ (prefixWord ++ tailWord_7077562).sum := by decide
  have hdescent : baseEnd_7077562 < baseStart_7077562 := by decide
  rcases family_descends (prefixWord ++ tailWord_7077562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7077565 : List Nat := [1, 4, 1, 2, 1, 2, 2, 1, 2, 5, 2]
def baseStart_7077565 : Nat := 118140960795 + 7077565 * 2 ^ 59
def prefixEnd_7077565 : Nat := 4983230072969 + 3 ^ 40 * 7077565 * 2
def baseEnd_7077565 : Nat := 3634192708438706728088377

theorem tailTrace_7077565 : CollatzResearch.WordTrace tailWord_7077565 prefixEnd_7077565 3634192708438706728088377 := by
  unfold tailWord_7077565
  simp only [CollatzResearch.WordTrace]
  refine ⟨258140002604198231713458149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172093335069465487808972099 258140002604198231713458149)
  ·
    refine ⟨48401250488287168446273403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 258140002604198231713458149 48401250488287168446273403)
    ·
      refine ⟨72601875732430752669410105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48401250488287168446273403 72601875732430752669410105)
      ·
        refine ⟨54451406799323064502057579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72601875732430752669410105 54451406799323064502057579)
        ·
          refine ⟨81677110198984596753086369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54451406799323064502057579 81677110198984596753086369)
          ·
            refine ⟨61257832649238447564814777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81677110198984596753086369 61257832649238447564814777)
            ·
              refine ⟨45943374486928835673611083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61257832649238447564814777 45943374486928835673611083)
              ·
                refine ⟨68915061730393253510416625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45943374486928835673611083 68915061730393253510416625)
                ·
                  refine ⟨51686296297794940132812469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68915061730393253510416625 51686296297794940132812469)
                  ·
                    refine ⟨4845590277918275637451169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51686296297794940132812469 4845590277918275637451169)
                    ·
                      refine ⟨3634192708438706728088377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4845590277918275637451169 3634192708438706728088377)
                      ·
                        rfl

theorem cell23_7077565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 1, 2, 5, 2].length) (baseStart_7077565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7077565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7077565 prefixEnd_7077565 := by exact prefixLift 7077565
  have htrace : WordTrace (prefixWord ++ tailWord_7077565) baseStart_7077565 baseEnd_7077565 := by
    simpa [prefixWord, tailWord_7077565, baseEnd_7077565] using wordTrace_append hprefix tailTrace_7077565
  have hstable : (prefixWord ++ tailWord_7077565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7077565).length < 2 ^ (prefixWord ++ tailWord_7077565).sum := by decide
  have hdescent : baseEnd_7077565 < baseStart_7077565 := by decide
  rcases family_descends (prefixWord ++ tailWord_7077565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7077568 : List Nat := [2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 5]
def baseStart_7077568 : Nat := 118140960795 + 7077568 * 2 ^ 59
def prefixEnd_7077568 : Nat := 4983230072969 + 3 ^ 40 * 7077568 * 2
def baseEnd_7077568 : Nat := 3634194248880670216350863

theorem tailTrace_7077568 : CollatzResearch.WordTrace tailWord_7077568 prefixEnd_7077568 3634194248880670216350863 := by
  unfold tailWord_7077568
  simp only [CollatzResearch.WordTrace]
  refine ⟨129070056011593681612908679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172093408015458242150544905 129070056011593681612908679)
  ·
    refine ⟨193605084017390522419363019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129070056011593681612908679 193605084017390522419363019)
    ·
      refine ⟨290407626026085783629044529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193605084017390522419363019 290407626026085783629044529)
      ·
        refine ⟨217805719519564337721783397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 290407626026085783629044529 217805719519564337721783397)
        ·
          refine ⟨40838572409918313322834387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 217805719519564337721783397 40838572409918313322834387)
          ·
            refine ⟨61257858614877469984251581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40838572409918313322834387 61257858614877469984251581)
            ·
              refine ⟨22971696980579051244094343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61257858614877469984251581 22971696980579051244094343)
              ·
                refine ⟨34457545470868576866141515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22971696980579051244094343 34457545470868576866141515)
                ·
                  refine ⟨51686318206302865299212273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34457545470868576866141515 51686318206302865299212273)
                  ·
                    refine ⟨38764738654727148974409205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51686318206302865299212273 38764738654727148974409205)
                    ·
                      refine ⟨3634194248880670216350863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38764738654727148974409205 3634194248880670216350863)
                      ·
                        rfl

theorem cell23_7077568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 5].length) (baseStart_7077568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7077568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7077568 prefixEnd_7077568 := by exact prefixLift 7077568
  have htrace : WordTrace (prefixWord ++ tailWord_7077568) baseStart_7077568 baseEnd_7077568 := by
    simpa [prefixWord, tailWord_7077568, baseEnd_7077568] using wordTrace_append hprefix tailTrace_7077568
  have hstable : (prefixWord ++ tailWord_7077568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7077568).length < 2 ^ (prefixWord ++ tailWord_7077568).sum := by decide
  have hdescent : baseEnd_7077568 < baseStart_7077568 := by decide
  rcases family_descends (prefixWord ++ tailWord_7077568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7077615 : List Nat := [1, 1, 2, 1, 5, 1, 1, 4, 2, 2, 3]
def baseStart_7077615 : Nat := 118140960795 + 7077615 * 2 ^ 59
def prefixEnd_7077615 : Nat := 4983230072969 + 3 ^ 40 * 7077615 * 2
def baseEnd_7077615 : Nat := 3634218382471431532463147

theorem tailTrace_7077615 : CollatzResearch.WordTrace tailWord_7077615 prefixEnd_7077615 3634218382471431532463147 := by
  unfold tailWord_7077615
  simp only [CollatzResearch.WordTrace]
  refine ⟨258141826254017090252778299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172094550836011393501852199 258141826254017090252778299)
  ·
    refine ⟨387212739381025635379167449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258141826254017090252778299 387212739381025635379167449)
    ·
      refine ⟨290409554535769226534375587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 387212739381025635379167449 290409554535769226534375587)
      ·
        refine ⟨435614331803653839801563381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290409554535769226534375587 435614331803653839801563381)
        ·
          refine ⟨40838843606592547481396567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 435614331803653839801563381 40838843606592547481396567)
          ·
            refine ⟨61258265409888821222094851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40838843606592547481396567 61258265409888821222094851)
            ·
              refine ⟨91887398114833231833142277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61258265409888821222094851 91887398114833231833142277)
              ·
                refine ⟨17228887146531230968714177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 91887398114833231833142277 17228887146531230968714177)
                ·
                  refine ⟨12921665359898423226535633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17228887146531230968714177 12921665359898423226535633)
                  ·
                    refine ⟨9691249019923817419901725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12921665359898423226535633 9691249019923817419901725)
                    ·
                      refine ⟨3634218382471431532463147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9691249019923817419901725 3634218382471431532463147)
                      ·
                        rfl

theorem cell23_7077615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 4, 2, 2, 3].length) (baseStart_7077615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7077615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7077615 prefixEnd_7077615 := by exact prefixLift 7077615
  have htrace : WordTrace (prefixWord ++ tailWord_7077615) baseStart_7077615 baseEnd_7077615 := by
    simpa [prefixWord, tailWord_7077615, baseEnd_7077615] using wordTrace_append hprefix tailTrace_7077615
  have hstable : (prefixWord ++ tailWord_7077615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7077615).length < 2 ^ (prefixWord ++ tailWord_7077615).sum := by decide
  have hdescent : baseEnd_7077615 < baseStart_7077615 := by decide
  rcases family_descends (prefixWord ++ tailWord_7077615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7077722 : List Nat := [3, 1, 1, 2, 1, 3, 1, 5, 1, 2, 3]
def baseStart_7077722 : Nat := 118140960795 + 7077722 * 2 ^ 59
def prefixEnd_7077722 : Nat := 4983230072969 + 3 ^ 40 * 7077722 * 2
def baseEnd_7077722 : Nat := 3634273324901462613825155

theorem tailTrace_7077722 : CollatzResearch.WordTrace tailWord_7077722 prefixEnd_7077722 3634273324901462613825155 := by
  unfold tailWord_7077722
  simp only [CollatzResearch.WordTrace]
  refine ⟨64536432216157361881730855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172097152576419631684615613 64536432216157361881730855)
  ·
    refine ⟨96804648324236042822596283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64536432216157361881730855 96804648324236042822596283)
    ·
      refine ⟨145206972486354064233894425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96804648324236042822596283 145206972486354064233894425)
      ·
        refine ⟨108905229364765548175420819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145206972486354064233894425 108905229364765548175420819)
        ·
          refine ⟨163357844047148322263131229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108905229364765548175420819 163357844047148322263131229)
          ·
            refine ⟨61259191517680620848674211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 163357844047148322263131229 61259191517680620848674211)
            ·
              refine ⟨91888787276520931273011317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61259191517680620848674211 91888787276520931273011317)
              ·
                refine ⟨8614573807173837306844811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 91888787276520931273011317 8614573807173837306844811)
                ·
                  refine ⟨12921860710760755960267217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8614573807173837306844811 12921860710760755960267217)
                  ·
                    refine ⟨9691395533070566970200413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12921860710760755960267217 9691395533070566970200413)
                    ·
                      refine ⟨3634273324901462613825155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9691395533070566970200413 3634273324901462613825155)
                      ·
                        rfl

theorem cell23_7077722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 5, 1, 2, 3].length) (baseStart_7077722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7077722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7077722 prefixEnd_7077722 := by exact prefixLift 7077722
  have htrace : WordTrace (prefixWord ++ tailWord_7077722) baseStart_7077722 baseEnd_7077722 := by
    simpa [prefixWord, tailWord_7077722, baseEnd_7077722] using wordTrace_append hprefix tailTrace_7077722
  have hstable : (prefixWord ++ tailWord_7077722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7077722).length < 2 ^ (prefixWord ++ tailWord_7077722).sum := by decide
  have hdescent : baseEnd_7077722 < baseStart_7077722 := by decide
  rcases family_descends (prefixWord ++ tailWord_7077722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7077742 : List Nat := [4, 1, 2, 3, 1, 2, 2, 8]
def baseStart_7077742 : Nat := 118140960795 + 7077742 * 2 ^ 59
def prefixEnd_7077742 : Nat := 4983230072969 + 3 ^ 40 * 7077742 * 2
def baseEnd_7077742 : Nat := 134603096093131575391669

theorem tailTrace_7077742 : CollatzResearch.WordTrace tailWord_7077742 prefixEnd_7077742 134603096093131575391669 := by
  unfold tailWord_7077742
  simp only [CollatzResearch.WordTrace]
  refine ⟨32268307290569623867831435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172097638883037993961767653 32268307290569623867831435)
  ·
    refine ⟨48402460935854435801747153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32268307290569623867831435 48402460935854435801747153)
    ·
      refine ⟨36301845701890826851310365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48402460935854435801747153 36301845701890826851310365)
      ·
        refine ⟨13613192138209060069241387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36301845701890826851310365 13613192138209060069241387)
        ·
          refine ⟨20419788207313590103862081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13613192138209060069241387 20419788207313590103862081)
          ·
            refine ⟨15314841155485192577896561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20419788207313590103862081 15314841155485192577896561)
            ·
              refine ⟨11486130866613894433422421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15314841155485192577896561 11486130866613894433422421)
              ·
                refine ⟨134603096093131575391669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11486130866613894433422421 134603096093131575391669)
                ·
                  rfl

theorem cell23_7077742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 2, 8].length) (baseStart_7077742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7077742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7077742 prefixEnd_7077742 := by exact prefixLift 7077742
  have htrace : WordTrace (prefixWord ++ tailWord_7077742) baseStart_7077742 baseEnd_7077742 := by
    simpa [prefixWord, tailWord_7077742, baseEnd_7077742] using wordTrace_append hprefix tailTrace_7077742
  have hstable : (prefixWord ++ tailWord_7077742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7077742).length < 2 ^ (prefixWord ++ tailWord_7077742).sum := by decide
  have hdescent : baseEnd_7077742 < baseStart_7077742 := by decide
  rcases family_descends (prefixWord ++ tailWord_7077742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7077786 : List Nat := [3, 1, 1, 4, 2, 2, 2, 2, 2, 1, 3]
def baseStart_7077786 : Nat := 118140960795 + 7077786 * 2 ^ 59
def prefixEnd_7077786 : Nat := 4983230072969 + 3 ^ 40 * 7077786 * 2
def baseEnd_7077786 : Nat := 3634306187663350363424861

theorem tailTrace_7077786 : CollatzResearch.WordTrace tailWord_7077786 prefixEnd_7077786 3634306187663350363424861 := by
  unfold tailWord_7077786
  simp only [CollatzResearch.WordTrace]
  refine ⟨64537015784099396614313303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172098708757598390971502141 64537015784099396614313303)
  ·
    refine ⟨96805523676149094921469955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64537015784099396614313303 96805523676149094921469955)
    ·
      refine ⟨145208285514223642382204933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96805523676149094921469955 145208285514223642382204933)
      ·
        refine ⟨27226553533916932946663425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 145208285514223642382204933 27226553533916932946663425)
        ·
          refine ⟨20419915150437699709997569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27226553533916932946663425 20419915150437699709997569)
          ·
            refine ⟨15314936362828274782498177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20419915150437699709997569 15314936362828274782498177)
            ·
              refine ⟨11486202272121206086873633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15314936362828274782498177 11486202272121206086873633)
              ·
                refine ⟨8614651704090904565155225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11486202272121206086873633 8614651704090904565155225)
                ·
                  refine ⟨6460988778068178423866419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8614651704090904565155225 6460988778068178423866419)
                  ·
                    refine ⟨9691483167102267635799629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6460988778068178423866419 9691483167102267635799629)
                    ·
                      refine ⟨3634306187663350363424861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9691483167102267635799629 3634306187663350363424861)
                      ·
                        rfl

theorem cell23_7077786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 2, 2, 2, 1, 3].length) (baseStart_7077786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7077786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7077786 prefixEnd_7077786 := by exact prefixLift 7077786
  have htrace : WordTrace (prefixWord ++ tailWord_7077786) baseStart_7077786 baseEnd_7077786 := by
    simpa [prefixWord, tailWord_7077786, baseEnd_7077786] using wordTrace_append hprefix tailTrace_7077786
  have hstable : (prefixWord ++ tailWord_7077786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7077786).length < 2 ^ (prefixWord ++ tailWord_7077786).sum := by decide
  have hdescent : baseEnd_7077786 < baseStart_7077786 := by decide
  rcases family_descends (prefixWord ++ tailWord_7077786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7077792 : List Nat := [2, 1, 1, 4, 1, 1, 1, 1, 5, 4, 2]
def baseStart_7077792 : Nat := 118140960795 + 7077792 * 2 ^ 59
def prefixEnd_7077792 : Nat := 4983230072969 + 3 ^ 40 * 7077792 * 2
def baseEnd_7077792 : Nat := 3634309268547277339949833

theorem tailTrace_7077792 : CollatzResearch.WordTrace tailWord_7077792 prefixEnd_7077792 3634309268547277339949833 := by
  unfold tailWord_7077792
  simp only [CollatzResearch.WordTrace]
  refine ⟨129074140987187924740985815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172098854649583899654647753 129074140987187924740985815)
  ·
    refine ⟨193611211480781887111478723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129074140987187924740985815 193611211480781887111478723)
    ·
      refine ⟨290416817221172830667218085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193611211480781887111478723 290416817221172830667218085)
      ·
        refine ⟨54453153228969905750103391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 290416817221172830667218085 54453153228969905750103391)
        ·
          refine ⟨81679729843454858625155087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54453153228969905750103391 81679729843454858625155087)
          ·
            refine ⟨122519594765182287937732631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81679729843454858625155087 122519594765182287937732631)
            ·
              refine ⟨183779392147773431906598947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122519594765182287937732631 183779392147773431906598947)
              ·
                refine ⟨275669088221660147859898421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 183779392147773431906598947 275669088221660147859898421)
                ·
                  refine ⟨25843977020780638861865477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 275669088221660147859898421 25843977020780638861865477)
                  ·
                    refine ⟨4845745691396369786599777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25843977020780638861865477 4845745691396369786599777)
                    ·
                      refine ⟨3634309268547277339949833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4845745691396369786599777 3634309268547277339949833)
                      ·
                        rfl

theorem cell23_7077792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 5, 4, 2].length) (baseStart_7077792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7077792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7077792 prefixEnd_7077792 := by exact prefixLift 7077792
  have htrace : WordTrace (prefixWord ++ tailWord_7077792) baseStart_7077792 baseEnd_7077792 := by
    simpa [prefixWord, tailWord_7077792, baseEnd_7077792] using wordTrace_append hprefix tailTrace_7077792
  have hstable : (prefixWord ++ tailWord_7077792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7077792).length < 2 ^ (prefixWord ++ tailWord_7077792).sum := by decide
  have hdescent : baseEnd_7077792 < baseStart_7077792 := by decide
  rcases family_descends (prefixWord ++ tailWord_7077792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7077809 : List Nat := [1, 2, 2, 4, 2, 1, 1, 3, 1, 4, 2]
def baseStart_7077809 : Nat := 118140960795 + 7077809 * 2 ^ 59
def prefixEnd_7077809 : Nat := 4983230072969 + 3 ^ 40 * 7077809 * 2
def baseEnd_7077809 : Nat := 3634317997718403773437255

theorem tailTrace_7077809 : CollatzResearch.WordTrace tailWord_7077809 prefixEnd_7077809 3634317997718403773437255 := by
  unfold tailWord_7077809
  simp only [CollatzResearch.WordTrace]
  refine ⟨258148902015314261385340481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172099268010209507590226987 258148902015314261385340481)
  ·
    refine ⟨193611676511485696039005361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258148902015314261385340481 193611676511485696039005361)
    ·
      refine ⟨145208757383614272029254021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193611676511485696039005361 145208757383614272029254021)
      ·
        refine ⟨27226642009427676005485129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 145208757383614272029254021 27226642009427676005485129)
        ·
          refine ⟨20419981507070757004113847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27226642009427676005485129 20419981507070757004113847)
          ·
            refine ⟨30629972260606135506170771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20419981507070757004113847 30629972260606135506170771)
            ·
              refine ⟨45944958390909203259256157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30629972260606135506170771 45944958390909203259256157)
              ·
                refine ⟨17229359396590951222221059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45944958390909203259256157 17229359396590951222221059)
                ·
                  refine ⟨25844039094886426833331589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17229359396590951222221059 25844039094886426833331589)
                  ·
                    refine ⟨4845757330291205031249673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25844039094886426833331589 4845757330291205031249673)
                    ·
                      refine ⟨3634317997718403773437255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4845757330291205031249673 3634317997718403773437255)
                      ·
                        rfl

theorem cell23_7077809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 3, 1, 4, 2].length) (baseStart_7077809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7077809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7077809 prefixEnd_7077809 := by exact prefixLift 7077809
  have htrace : WordTrace (prefixWord ++ tailWord_7077809) baseStart_7077809 baseEnd_7077809 := by
    simpa [prefixWord, tailWord_7077809, baseEnd_7077809] using wordTrace_append hprefix tailTrace_7077809
  have hstable : (prefixWord ++ tailWord_7077809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7077809).length < 2 ^ (prefixWord ++ tailWord_7077809).sum := by decide
  have hdescent : baseEnd_7077809 < baseStart_7077809 := by decide
  rcases family_descends (prefixWord ++ tailWord_7077809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7077989 : List Nat := [1, 3, 1, 3, 2, 2, 2, 1, 3, 1, 4]
def baseStart_7077989 : Nat := 118140960795 + 7077989 * 2 ^ 59
def prefixEnd_7077989 : Nat := 4983230072969 + 3 ^ 40 * 7077989 * 2
def baseEnd_7077989 : Nat := 3634410424236213069186427

theorem tailTrace_7077989 : CollatzResearch.WordTrace tailWord_7077989 prefixEnd_7077989 3634410424236213069186427 := by
  unfold tailWord_7077989
  simp only [CollatzResearch.WordTrace]
  refine ⟨258155467154662152126893021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172103644769774768084595347 258155467154662152126893021)
  ·
    refine ⟨96808300182998307047584883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 258155467154662152126893021 96808300182998307047584883)
    ·
      refine ⟨145212450274497460571377325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96808300182998307047584883 145212450274497460571377325)
      ·
        refine ⟨54454668852936547714266497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145212450274497460571377325 54454668852936547714266497)
        ·
          refine ⟨40841001639702410785699873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54454668852936547714266497 40841001639702410785699873)
          ·
            refine ⟨30630751229776808089274905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40841001639702410785699873 30630751229776808089274905)
            ·
              refine ⟨22973063422332606066956179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30630751229776808089274905 22973063422332606066956179)
              ·
                refine ⟨34459595133498909100434269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22973063422332606066956179 34459595133498909100434269)
                ·
                  refine ⟨12922348175062090912662851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34459595133498909100434269 12922348175062090912662851)
                  ·
                    refine ⟨19383522262593136368994277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12922348175062090912662851 19383522262593136368994277)
                    ·
                      refine ⟨3634410424236213069186427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19383522262593136368994277 3634410424236213069186427)
                      ·
                        rfl

theorem cell23_7077989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 1, 3, 1, 4].length) (baseStart_7077989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7077989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7077989 prefixEnd_7077989 := by exact prefixLift 7077989
  have htrace : WordTrace (prefixWord ++ tailWord_7077989) baseStart_7077989 baseEnd_7077989 := by
    simpa [prefixWord, tailWord_7077989, baseEnd_7077989] using wordTrace_append hprefix tailTrace_7077989
  have hstable : (prefixWord ++ tailWord_7077989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7077989).length < 2 ^ (prefixWord ++ tailWord_7077989).sum := by decide
  have hdescent : baseEnd_7077989 < baseStart_7077989 := by decide
  rcases family_descends (prefixWord ++ tailWord_7077989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7078012 : List Nat := [2, 2, 2, 1, 1, 5, 10]
def baseStart_7078012 : Nat := 118140960795 + 7078012 * 2 ^ 59
def prefixEnd_7078012 : Nat := 4983230072969 + 3 ^ 40 * 7078012 * 2
def baseEnd_7078012 : Nat := 44869410299892178755541

theorem tailTrace_7078012 : CollatzResearch.WordTrace tailWord_7078012 prefixEnd_7078012 44869410299892178755541 := by
  unfold tailWord_7078012
  simp only [CollatzResearch.WordTrace]
  refine ⟨129078153016789413527490145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172104204022385884703320193 129078153016789413527490145)
  ·
    refine ⟨96808614762592060145617609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129078153016789413527490145 96808614762592060145617609)
    ·
      refine ⟨72606461071944045109213207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96808614762592060145617609 72606461071944045109213207)
      ·
        refine ⟨108909691607916067663819811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72606461071944045109213207 108909691607916067663819811)
        ·
          refine ⟨163364537411874101495729717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108909691607916067663819811 163364537411874101495729717)
          ·
            refine ⟨15315425382363197015224661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 163364537411874101495729717 15315425382363197015224661)
            ·
              refine ⟨44869410299892178755541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 15315425382363197015224661 44869410299892178755541)
              ·
                rfl

theorem cell23_7078012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 10].length) (baseStart_7078012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7078012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7078012 prefixEnd_7078012 := by exact prefixLift 7078012
  have htrace : WordTrace (prefixWord ++ tailWord_7078012) baseStart_7078012 baseEnd_7078012 := by
    simpa [prefixWord, tailWord_7078012, baseEnd_7078012] using wordTrace_append hprefix tailTrace_7078012
  have hstable : (prefixWord ++ tailWord_7078012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7078012).length < 2 ^ (prefixWord ++ tailWord_7078012).sum := by decide
  have hdescent : baseEnd_7078012 < baseStart_7078012 := by decide
  rcases family_descends (prefixWord ++ tailWord_7078012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7078046 : List Nat := [4, 3, 1, 1, 3, 1, 1, 9]
def baseStart_7078046 : Nat := 118140960795 + 7078046 * 2 ^ 59
def prefixEnd_7078046 : Nat := 4983230072969 + 3 ^ 40 * 7078046 * 2
def baseEnd_7078046 : Nat := 134608877504945160969395

theorem tailTrace_7078046 : CollatzResearch.WordTrace tailWord_7078046 prefixEnd_7078046 134608877504945160969395 := by
  unfold tailWord_7078046
  simp only [CollatzResearch.WordTrace]
  refine ⟨32269693264431956357714749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172105030743637100574478661 32269693264431956357714749)
  ·
    refine ⟨12101134974161983634143031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32269693264431956357714749 12101134974161983634143031)
    ·
      refine ⟨18151702461242975451214547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12101134974161983634143031 18151702461242975451214547)
      ·
        refine ⟨27227553691864463176821821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18151702461242975451214547 27227553691864463176821821)
        ·
          refine ⟨10210332634449173691308183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27227553691864463176821821 10210332634449173691308183)
          ·
            refine ⟨15315498951673760536962275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10210332634449173691308183 15315498951673760536962275)
            ·
              refine ⟨22973248427510640805443413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15315498951673760536962275 22973248427510640805443413)
              ·
                refine ⟨134608877504945160969395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22973248427510640805443413 134608877504945160969395)
                ·
                  rfl

theorem cell23_7078046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 9].length) (baseStart_7078046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7078046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7078046 prefixEnd_7078046 := by exact prefixLift 7078046
  have htrace : WordTrace (prefixWord ++ tailWord_7078046) baseStart_7078046 baseEnd_7078046 := by
    simpa [prefixWord, tailWord_7078046, baseEnd_7078046] using wordTrace_append hprefix tailTrace_7078046
  have hstable : (prefixWord ++ tailWord_7078046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7078046).length < 2 ^ (prefixWord ++ tailWord_7078046).sum := by decide
  have hdescent : baseEnd_7078046 < baseStart_7078046 := by decide
  rcases family_descends (prefixWord ++ tailWord_7078046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7078130 : List Nat := [3, 2, 1, 3, 2, 1, 1, 4, 2, 2, 2]
def baseStart_7078130 : Nat := 118140960795 + 7078130 * 2 ^ 59
def prefixEnd_7078130 : Nat := 4983230072969 + 3 ^ 40 * 7078130 * 2
def baseEnd_7078130 : Nat := 3634482825008497017523279

theorem tailTrace_7078130 : CollatzResearch.WordTrace tailWord_7078130 prefixEnd_7078130 3634482825008497017523279 := by
  unfold tailWord_7078130
  simp only [CollatzResearch.WordTrace]
  refine ⟨64540152461787833301943961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172107073231434222138517229 64540152461787833301943961)
  ·
    refine ⟨48405114346340874976457971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64540152461787833301943961 48405114346340874976457971)
    ·
      refine ⟨72607671519511312464686957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48405114346340874976457971 72607671519511312464686957)
      ·
        refine ⟨27227876819816742174257609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72607671519511312464686957 27227876819816742174257609)
        ·
          refine ⟨20420907614862556630693207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27227876819816742174257609 20420907614862556630693207)
          ·
            refine ⟨30631361422293834946039811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20420907614862556630693207 30631361422293834946039811)
            ·
              refine ⟨45947042133440752419059717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30631361422293834946039811 45947042133440752419059717)
              ·
                refine ⟨8615070400020141078573697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45947042133440752419059717 8615070400020141078573697)
                ·
                  refine ⟨6461302800015105808930273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8615070400020141078573697 6461302800015105808930273)
                  ·
                    refine ⟨4845977100011329356697705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6461302800015105808930273 4845977100011329356697705)
                    ·
                      refine ⟨3634482825008497017523279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4845977100011329356697705 3634482825008497017523279)
                      ·
                        rfl

theorem cell23_7078130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 4, 2, 2, 2].length) (baseStart_7078130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7078130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7078130 prefixEnd_7078130 := by exact prefixLift 7078130
  have htrace : WordTrace (prefixWord ++ tailWord_7078130) baseStart_7078130 baseEnd_7078130 := by
    simpa [prefixWord, tailWord_7078130, baseEnd_7078130] using wordTrace_append hprefix tailTrace_7078130
  have hstable : (prefixWord ++ tailWord_7078130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7078130).length < 2 ^ (prefixWord ++ tailWord_7078130).sum := by decide
  have hdescent : baseEnd_7078130 < baseStart_7078130 := by decide
  rcases family_descends (prefixWord ++ tailWord_7078130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7078156 : List Nat := [2, 2, 1, 2, 2, 2, 1, 2, 2, 5, 2]
def baseStart_7078156 : Nat := 118140960795 + 7078156 * 2 ^ 59
def prefixEnd_7078156 : Nat := 4983230072969 + 3 ^ 40 * 7078156 * 2
def baseEnd_7078156 : Nat := 3634496175505513915798159

theorem tailTrace_7078156 : CollatzResearch.WordTrace tailWord_7078156 prefixEnd_7078156 3634496175505513915798159 := by
  unfold tailWord_7078156
  simp only [CollatzResearch.WordTrace]
  refine ⟨129080779072528569824111161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172107705430038093098814881 129080779072528569824111161)
  ·
    refine ⟨96810584304396427368083371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129080779072528569824111161 96810584304396427368083371)
    ·
      refine ⟨145215876456594641052125057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96810584304396427368083371 145215876456594641052125057)
      ·
        refine ⟨108911907342445980789093793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145215876456594641052125057 108911907342445980789093793)
        ·
          refine ⟨81683930506834485591820345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108911907342445980789093793 81683930506834485591820345)
          ·
            refine ⟨61262947880125864193865259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81683930506834485591820345 61262947880125864193865259)
            ·
              refine ⟨91894421820188796290797889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61262947880125864193865259 91894421820188796290797889)
              ·
                refine ⟨68920816365141597218098417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91894421820188796290797889 68920816365141597218098417)
                ·
                  refine ⟨51690612273856197913573813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68920816365141597218098417 51690612273856197913573813)
                  ·
                    refine ⟨4845994900674018554397545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51690612273856197913573813 4845994900674018554397545)
                    ·
                      refine ⟨3634496175505513915798159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4845994900674018554397545 3634496175505513915798159)
                      ·
                        rfl

theorem cell23_7078156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 2, 2, 5, 2].length) (baseStart_7078156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7078156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7078156 prefixEnd_7078156 := by exact prefixLift 7078156
  have htrace : WordTrace (prefixWord ++ tailWord_7078156) baseStart_7078156 baseEnd_7078156 := by
    simpa [prefixWord, tailWord_7078156, baseEnd_7078156] using wordTrace_append hprefix tailTrace_7078156
  have hstable : (prefixWord ++ tailWord_7078156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7078156).length < 2 ^ (prefixWord ++ tailWord_7078156).sum := by decide
  have hdescent : baseEnd_7078156 < baseStart_7078156 := by decide
  rcases family_descends (prefixWord ++ tailWord_7078156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7078247 : List Nat := [1, 1, 5, 1, 3, 2, 3, 2, 1, 4]
def baseStart_7078247 : Nat := 118140960795 + 7078247 * 2 ^ 59
def prefixEnd_7078247 : Nat := 4983230072969 + 3 ^ 40 * 7078247 * 2
def baseEnd_7078247 : Nat := 1211514300748357686586747

theorem tailTrace_7078247 : CollatzResearch.WordTrace tailWord_7078247 prefixEnd_7078247 1211514300748357686586747 := by
  unfold tailWord_7078247
  simp only [CollatzResearch.WordTrace]
  refine ⟨258164877187727462189784995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172109918125151641459856663 258164877187727462189784995)
  ·
    refine ⟨387247315781591193284677493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258164877187727462189784995 387247315781591193284677493)
    ·
      refine ⟨36304435854524174370438515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 387247315781591193284677493 36304435854524174370438515)
      ·
        refine ⟨54456653781786261555657773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36304435854524174370438515 54456653781786261555657773)
        ·
          refine ⟨20421245168169848083371665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54456653781786261555657773 20421245168169848083371665)
          ·
            refine ⟨15315933876127386062528749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20421245168169848083371665 15315933876127386062528749)
            ·
              refine ⟨5743475203547769773448281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15315933876127386062528749 5743475203547769773448281)
              ·
                refine ⟨4307606402660827330086211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5743475203547769773448281 4307606402660827330086211)
                ·
                  refine ⟨6461409603991240995129317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4307606402660827330086211 6461409603991240995129317)
                  ·
                    refine ⟨1211514300748357686586747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6461409603991240995129317 1211514300748357686586747)
                    ·
                      rfl

theorem cell23_7078247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 3, 2, 1, 4].length) (baseStart_7078247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7078247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7078247 prefixEnd_7078247 := by exact prefixLift 7078247
  have htrace : WordTrace (prefixWord ++ tailWord_7078247) baseStart_7078247 baseEnd_7078247 := by
    simpa [prefixWord, tailWord_7078247, baseEnd_7078247] using wordTrace_append hprefix tailTrace_7078247
  have hstable : (prefixWord ++ tailWord_7078247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7078247).length < 2 ^ (prefixWord ++ tailWord_7078247).sum := by decide
  have hdescent : baseEnd_7078247 < baseStart_7078247 := by decide
  rcases family_descends (prefixWord ++ tailWord_7078247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7078273 : List Nat := [1, 2, 4, 3, 1, 2, 1, 1, 3, 5]
def baseStart_7078273 : Nat := 118140960795 + 7078273 * 2 ^ 59
def prefixEnd_7078273 : Nat := 4983230072969 + 3 ^ 40 * 7078273 * 2
def baseEnd_7078273 : Nat := 1211518750914029986011707

theorem tailTrace_7078273 : CollatzResearch.WordTrace tailWord_7078273 prefixEnd_7078273 1211518750914029986011707 := by
  unfold tailWord_7078273
  simp only [CollatzResearch.WordTrace]
  refine ⟨258165825485633268630231473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172110550323755512420154315 258165825485633268630231473)
  ·
    refine ⟨193624369114224951472673605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258165825485633268630231473 193624369114224951472673605)
    ·
      refine ⟨36304569208917178401126301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 193624369114224951472673605 36304569208917178401126301)
      ·
        refine ⟨13614213453343941900422363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36304569208917178401126301 13614213453343941900422363)
        ·
          refine ⟨20421320180015912850633545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13614213453343941900422363 20421320180015912850633545)
          ·
            refine ⟨15315990135011934637975159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20421320180015912850633545 15315990135011934637975159)
            ·
              refine ⟨22973985202517901956962739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15315990135011934637975159 22973985202517901956962739)
              ·
                refine ⟨34460977803776852935444109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22973985202517901956962739 34460977803776852935444109)
                ·
                  refine ⟨12922866676416319850791541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34460977803776852935444109 12922866676416319850791541)
                  ·
                    refine ⟨1211518750914029986011707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12922866676416319850791541 1211518750914029986011707)
                    ·
                      rfl

theorem cell23_7078273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 1, 3, 5].length) (baseStart_7078273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7078273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7078273 prefixEnd_7078273 := by exact prefixLift 7078273
  have htrace : WordTrace (prefixWord ++ tailWord_7078273) baseStart_7078273 baseEnd_7078273 := by
    simpa [prefixWord, tailWord_7078273, baseEnd_7078273] using wordTrace_append hprefix tailTrace_7078273
  have hstable : (prefixWord ++ tailWord_7078273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7078273).length < 2 ^ (prefixWord ++ tailWord_7078273).sum := by decide
  have hdescent : baseEnd_7078273 < baseStart_7078273 := by decide
  rcases family_descends (prefixWord ++ tailWord_7078273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7078280 : List Nat := [2, 1, 3, 3, 1, 1, 4, 1, 2, 3, 2]
def baseStart_7078280 : Nat := 118140960795 + 7078280 * 2 ^ 59
def prefixEnd_7078280 : Nat := 4983230072969 + 3 ^ 40 * 7078280 * 2
def baseEnd_7078280 : Nat := 3634559847106671430647589

theorem tailTrace_7078280 : CollatzResearch.WordTrace tailWord_7078280 prefixEnd_7078280 3634559847106671430647589 := by
  unfold tailWord_7078280
  simp only [CollatzResearch.WordTrace]
  refine ⟨129083040398303954412868147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172110720531071939217157529 129083040398303954412868147)
  ·
    refine ⟨193624560597455931619302221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129083040398303954412868147 193624560597455931619302221)
    ·
      refine ⟨72609210224045974357238333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193624560597455931619302221 72609210224045974357238333)
      ·
        refine ⟨27228453834017240383964375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72609210224045974357238333 27228453834017240383964375)
        ·
          refine ⟨40842680751025860575946563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27228453834017240383964375 40842680751025860575946563)
          ·
            refine ⟨61264021126538790863919845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40842680751025860575946563 61264021126538790863919845)
            ·
              refine ⟨11487003961226023286984971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61264021126538790863919845 11487003961226023286984971)
              ·
                refine ⟨17230505941839034930477457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11487003961226023286984971 17230505941839034930477457)
                ·
                  refine ⟨12922879456379276197858093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17230505941839034930477457 12922879456379276197858093)
                  ·
                    refine ⟨4846079796142228574196785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12922879456379276197858093 4846079796142228574196785)
                    ·
                      refine ⟨3634559847106671430647589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4846079796142228574196785 3634559847106671430647589)
                      ·
                        rfl

theorem cell23_7078280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 4, 1, 2, 3, 2].length) (baseStart_7078280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7078280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7078280 prefixEnd_7078280 := by exact prefixLift 7078280
  have htrace : WordTrace (prefixWord ++ tailWord_7078280) baseStart_7078280 baseEnd_7078280 := by
    simpa [prefixWord, tailWord_7078280, baseEnd_7078280] using wordTrace_append hprefix tailTrace_7078280
  have hstable : (prefixWord ++ tailWord_7078280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7078280).length < 2 ^ (prefixWord ++ tailWord_7078280).sum := by decide
  have hdescent : baseEnd_7078280 < baseStart_7078280 := by decide
  rcases family_descends (prefixWord ++ tailWord_7078280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7078294 : List Nat := [5, 3, 1, 2, 1, 1, 2, 2, 6]
def baseStart_7078294 : Nat := 118140960795 + 7078294 * 2 ^ 59
def prefixEnd_7078294 : Nat := 4983230072969 + 3 ^ 40 * 7078294 * 2
def baseEnd_7078294 : Nat := 403840781759537152874725

theorem tailTrace_7078294 : CollatzResearch.WordTrace tailWord_7078294 prefixEnd_7078294 403840781759537152874725 := by
  unfold tailWord_7078294
  simp only [CollatzResearch.WordTrace]
  refine ⟨16135411963659824326046621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 172111060945704792811163957 16135411963659824326046621)
  ·
    refine ⟨6050779486372434122267483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16135411963659824326046621 6050779486372434122267483)
    ·
      refine ⟨9076169229558651183401225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6050779486372434122267483 9076169229558651183401225)
      ·
        refine ⟨6807126922168988387550919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9076169229558651183401225 6807126922168988387550919)
        ·
          refine ⟨10210690383253482581326379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6807126922168988387550919 10210690383253482581326379)
          ·
            refine ⟨15316035574880223871989569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10210690383253482581326379 15316035574880223871989569)
            ·
              refine ⟨11487026681160167903992177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15316035574880223871989569 11487026681160167903992177)
              ·
                refine ⟨8615270010870125927994133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11487026681160167903992177 8615270010870125927994133)
                ·
                  refine ⟨403840781759537152874725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8615270010870125927994133 403840781759537152874725)
                  ·
                    rfl

theorem cell23_7078294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 2, 2, 6].length) (baseStart_7078294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7078294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7078294 prefixEnd_7078294 := by exact prefixLift 7078294
  have htrace : WordTrace (prefixWord ++ tailWord_7078294) baseStart_7078294 baseEnd_7078294 := by
    simpa [prefixWord, tailWord_7078294, baseEnd_7078294] using wordTrace_append hprefix tailTrace_7078294
  have hstable : (prefixWord ++ tailWord_7078294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7078294).length < 2 ^ (prefixWord ++ tailWord_7078294).sum := by decide
  have hdescent : baseEnd_7078294 < baseStart_7078294 := by decide
  rcases family_descends (prefixWord ++ tailWord_7078294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7078304 : List Nat := [2, 1, 1, 4, 1, 5, 2, 2, 1, 1, 3]
def baseStart_7078304 : Nat := 118140960795 + 7078304 * 2 ^ 59
def prefixEnd_7078304 : Nat := 4983230072969 + 3 ^ 40 * 7078304 * 2
def baseEnd_7078304 : Nat := 3634572170642379336747479

theorem tailTrace_7078304 : CollatzResearch.WordTrace tailWord_7078304 prefixEnd_7078304 3634572170642379336747479 := by
  unfold tailWord_7078304
  simp only [CollatzResearch.WordTrace]
  refine ⟨129083478074260480462304983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172111304099013973949739977 129083478074260480462304983)
  ·
    refine ⟨193625217111390720693457475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129083478074260480462304983 193625217111390720693457475)
    ·
      refine ⟨290437825667086081040186213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193625217111390720693457475 290437825667086081040186213)
      ·
        refine ⟨54457092312578640195034915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 290437825667086081040186213 54457092312578640195034915)
        ·
          refine ⟨81685638468867960292552373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54457092312578640195034915 81685638468867960292552373)
          ·
            refine ⟨7658028606456371277426785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 81685638468867960292552373 7658028606456371277426785)
            ·
              refine ⟨5743521454842278458070089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7658028606456371277426785 5743521454842278458070089)
              ·
                refine ⟨4307641091131708843552567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5743521454842278458070089 4307641091131708843552567)
                ·
                  refine ⟨6461461636697563265328851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4307641091131708843552567 6461461636697563265328851)
                  ·
                    refine ⟨9692192455046344897993277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6461461636697563265328851 9692192455046344897993277)
                    ·
                      refine ⟨3634572170642379336747479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9692192455046344897993277 3634572170642379336747479)
                      ·
                        rfl

theorem cell23_7078304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 2, 2, 1, 1, 3].length) (baseStart_7078304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7078304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7078304 prefixEnd_7078304 := by exact prefixLift 7078304
  have htrace : WordTrace (prefixWord ++ tailWord_7078304) baseStart_7078304 baseEnd_7078304 := by
    simpa [prefixWord, tailWord_7078304, baseEnd_7078304] using wordTrace_append hprefix tailTrace_7078304
  have hstable : (prefixWord ++ tailWord_7078304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7078304).length < 2 ^ (prefixWord ++ tailWord_7078304).sum := by decide
  have hdescent : baseEnd_7078304 < baseStart_7078304 := by decide
  rcases family_descends (prefixWord ++ tailWord_7078304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7078333 : List Nat := [1, 4, 1, 2, 2, 3, 3, 7]
def baseStart_7078333 : Nat := 118140960795 + 7078333 * 2 ^ 59
def prefixEnd_7078333 : Nat := 4983230072969 + 3 ^ 40 * 7078333 * 2
def baseEnd_7078333 : Nat := 134614335614124434195735

theorem tailTrace_7078333 : CollatzResearch.WordTrace tailWord_7078333 prefixEnd_7078333 134614335614124434195735 := by
  unfold tailWord_7078333
  simp only [CollatzResearch.WordTrace]
  refine ⟨258168013865415898877415653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172112009243610599251610435 258168013865415898877415653)
  ·
    refine ⟨48406502599765481039515435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 258168013865415898877415653 48406502599765481039515435)
    ·
      refine ⟨72609753899648221559273153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48406502599765481039515435 72609753899648221559273153)
      ·
        refine ⟨54457315424736166169454865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72609753899648221559273153 54457315424736166169454865)
        ·
          refine ⟨40842986568552124627091149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54457315424736166169454865 40842986568552124627091149)
          ·
            refine ⟨15316119963207046735159181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40842986568552124627091149 15316119963207046735159181)
            ·
              refine ⟨5743544986202642525684693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15316119963207046735159181 5743544986202642525684693)
              ·
                refine ⟨134614335614124434195735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5743544986202642525684693 134614335614124434195735)
                ·
                  rfl

theorem cell23_7078333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 3, 7].length) (baseStart_7078333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7078333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7078333 prefixEnd_7078333 := by exact prefixLift 7078333
  have htrace : WordTrace (prefixWord ++ tailWord_7078333) baseStart_7078333 baseEnd_7078333 := by
    simpa [prefixWord, tailWord_7078333, baseEnd_7078333] using wordTrace_append hprefix tailTrace_7078333
  have hstable : (prefixWord ++ tailWord_7078333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7078333).length < 2 ^ (prefixWord ++ tailWord_7078333).sum := by decide
  have hdescent : baseEnd_7078333 < baseStart_7078333 := by decide
  rcases family_descends (prefixWord ++ tailWord_7078333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7078343 : List Nat := [1, 1, 4, 1, 1, 4, 2, 2, 1, 3, 3]
def baseStart_7078343 : Nat := 118140960795 + 7078343 * 2 ^ 59
def prefixEnd_7078343 : Nat := 4983230072969 + 3 ^ 40 * 7078343 * 2
def baseEnd_7078343 : Nat := 3634592196387904684159799

theorem tailTrace_7078343 : CollatzResearch.WordTrace tailWord_7078343 prefixEnd_7078343 3634592196387904684159799 := by
  unfold tailWord_7078343
  simp only [CollatzResearch.WordTrace]
  refine ⟨258168378595379670585279683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172112252396919780390186455 258168378595379670585279683)
  ·
    refine ⟨387252567893069505877919525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258168378595379670585279683 387252567893069505877919525)
    ·
      refine ⟨72609856479950532352109911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 387252567893069505877919525 72609856479950532352109911)
      ·
        refine ⟨108914784719925798528164867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72609856479950532352109911 108914784719925798528164867)
        ·
          refine ⟨163372177079888697792247301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108914784719925798528164867 163372177079888697792247301)
          ·
            refine ⟨30632283202479130836046369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 163372177079888697792247301 30632283202479130836046369)
            ·
              refine ⟨22974212401859348127034777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30632283202479130836046369 22974212401859348127034777)
              ·
                refine ⟨17230659301394511095276083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22974212401859348127034777 17230659301394511095276083)
                ·
                  refine ⟨25845988952091766642914125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17230659301394511095276083 25845988952091766642914125)
                  ·
                    refine ⟨9692245857034412491092797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25845988952091766642914125 9692245857034412491092797)
                    ·
                      refine ⟨3634592196387904684159799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9692245857034412491092797 3634592196387904684159799)
                      ·
                        rfl

theorem cell23_7078343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 2, 1, 3, 3].length) (baseStart_7078343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7078343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7078343 prefixEnd_7078343 := by exact prefixLift 7078343
  have htrace : WordTrace (prefixWord ++ tailWord_7078343) baseStart_7078343 baseEnd_7078343 := by
    simpa [prefixWord, tailWord_7078343, baseEnd_7078343] using wordTrace_append hprefix tailTrace_7078343
  have hstable : (prefixWord ++ tailWord_7078343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7078343).length < 2 ^ (prefixWord ++ tailWord_7078343).sum := by decide
  have hdescent : baseEnd_7078343 < baseStart_7078343 := by decide
  rcases family_descends (prefixWord ++ tailWord_7078343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7078344 : List Nat := [2, 1, 3, 1, 3, 3, 2, 3, 1, 2, 2]
def baseStart_7078344 : Nat := 118140960795 + 7078344 * 2 ^ 59
def prefixEnd_7078344 : Nat := 4983230072969 + 3 ^ 40 * 7078344 * 2
def baseEnd_7078344 : Nat := 3634592709868559180247295

theorem tailTrace_7078344 : CollatzResearch.WordTrace tailWord_7078344 prefixEnd_7078344 3634592709868559180247295 := by
  unfold tailWord_7078344
  simp only [CollatzResearch.WordTrace]
  refine ⟨129084207534188023878033043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172112276712250698504044057 129084207534188023878033043)
  ·
    refine ⟨193626311301282035817049565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129084207534188023878033043 193626311301282035817049565)
    ·
      refine ⟨72609866737980763431393587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193626311301282035817049565 72609866737980763431393587)
      ·
        refine ⟨108914800106971145147090381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72609866737980763431393587 108914800106971145147090381)
        ·
          refine ⟨40843050040114179430158893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108914800106971145147090381 40843050040114179430158893)
          ·
            refine ⟨15316143765042817286309585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40843050040114179430158893 15316143765042817286309585)
            ·
              refine ⟨11487107823782112964732189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15316143765042817286309585 11487107823782112964732189)
              ·
                refine ⟨4307665433918292361774571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11487107823782112964732189 4307665433918292361774571)
                ·
                  refine ⟨6461498150877438542661857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4307665433918292361774571 6461498150877438542661857)
                  ·
                    refine ⟨4846123613158078906996393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6461498150877438542661857 4846123613158078906996393)
                    ·
                      refine ⟨3634592709868559180247295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4846123613158078906996393 3634592709868559180247295)
                      ·
                        rfl

theorem cell23_7078344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 2, 3, 1, 2, 2].length) (baseStart_7078344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7078344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7078344 prefixEnd_7078344 := by exact prefixLift 7078344
  have htrace : WordTrace (prefixWord ++ tailWord_7078344) baseStart_7078344 baseEnd_7078344 := by
    simpa [prefixWord, tailWord_7078344, baseEnd_7078344] using wordTrace_append hprefix tailTrace_7078344
  have hstable : (prefixWord ++ tailWord_7078344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7078344).length < 2 ^ (prefixWord ++ tailWord_7078344).sum := by decide
  have hdescent : baseEnd_7078344 < baseStart_7078344 := by decide
  rcases family_descends (prefixWord ++ tailWord_7078344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7078354 : List Nat := [3, 2, 2, 4, 1, 2, 1, 2, 2, 4]
def baseStart_7078354 : Nat := 118140960795 + 7078354 * 2 ^ 59
def prefixEnd_7078354 : Nat := 4983230072969 + 3 ^ 40 * 7078354 * 2
def baseEnd_7078354 : Nat := 1211532614891701380374083

theorem tailTrace_7078354 : CollatzResearch.WordTrace tailWord_7078354 prefixEnd_7078354 1211532614891701380374083 := by
  unfold tailWord_7078354
  simp only [CollatzResearch.WordTrace]
  refine ⟨64542194949584954865982529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172112519865559879642620077 64542194949584954865982529)
  ·
    refine ⟨48406646212188716149486897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64542194949584954865982529 48406646212188716149486897)
    ·
      refine ⟨36304984659141537112115173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48406646212188716149486897 36304984659141537112115173)
      ·
        refine ⟨6807184623589038208521595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36304984659141537112115173 6807184623589038208521595)
        ·
          refine ⟨10210776935383557312782393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6807184623589038208521595 10210776935383557312782393)
          ·
            refine ⟨7658082701537667984586795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10210776935383557312782393 7658082701537667984586795)
            ·
              refine ⟨11487124052306501976880193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7658082701537667984586795 11487124052306501976880193)
              ·
                refine ⟨8615343039229876482660145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11487124052306501976880193 8615343039229876482660145)
                ·
                  refine ⟨6461507279422407361995109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8615343039229876482660145 6461507279422407361995109)
                  ·
                    refine ⟨1211532614891701380374083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6461507279422407361995109 1211532614891701380374083)
                    ·
                      rfl

theorem cell23_7078354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 1, 2, 2, 4].length) (baseStart_7078354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7078354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7078354 prefixEnd_7078354 := by exact prefixLift 7078354
  have htrace : WordTrace (prefixWord ++ tailWord_7078354) baseStart_7078354 baseEnd_7078354 := by
    simpa [prefixWord, tailWord_7078354, baseEnd_7078354] using wordTrace_append hprefix tailTrace_7078354
  have hstable : (prefixWord ++ tailWord_7078354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7078354).length < 2 ^ (prefixWord ++ tailWord_7078354).sum := by decide
  have hdescent : baseEnd_7078354 < baseStart_7078354 := by decide
  rcases family_descends (prefixWord ++ tailWord_7078354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7078433 : List Nat := [1, 2, 3, 2, 2, 1, 2, 1, 1, 5, 3]
def baseStart_7078433 : Nat := 118140960795 + 7078433 * 2 ^ 59
def prefixEnd_7078433 : Nat := 4983230072969 + 3 ^ 40 * 7078433 * 2
def baseEnd_7078433 : Nat := 3634638409646809332034385

theorem tailTrace_7078433 : CollatzResearch.WordTrace tailWord_7078433 prefixEnd_7078433 3634638409646809332034385 := by
  unfold tailWord_7078433
  simp only [CollatzResearch.WordTrace]
  refine ⟨258171661165053615956055953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172114440776702410637370635 258171661165053615956055953)
  ·
    refine ⟨193628745873790211967041965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258171661165053615956055953 193628745873790211967041965)
    ·
      refine ⟨72610779702671329487640737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193628745873790211967041965 72610779702671329487640737)
      ·
        refine ⟨54458084777003497115730553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72610779702671329487640737 54458084777003497115730553)
        ·
          refine ⟨40843563582752622836797915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54458084777003497115730553 40843563582752622836797915)
          ·
            refine ⟨61265345374128934255196873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40843563582752622836797915 61265345374128934255196873)
            ·
              refine ⟨45949009030596700691397655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61265345374128934255196873 45949009030596700691397655)
              ·
                refine ⟨68923513545895051037096483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45949009030596700691397655 68923513545895051037096483)
                ·
                  refine ⟨103385270318842576555644725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68923513545895051037096483 103385270318842576555644725)
                  ·
                    refine ⟨9692369092391491552091693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 103385270318842576555644725 9692369092391491552091693)
                    ·
                      refine ⟨3634638409646809332034385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9692369092391491552091693 3634638409646809332034385)
                      ·
                        rfl

theorem cell23_7078433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 1, 1, 5, 3].length) (baseStart_7078433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7078433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7078433 prefixEnd_7078433 := by exact prefixLift 7078433
  have htrace : WordTrace (prefixWord ++ tailWord_7078433) baseStart_7078433 baseEnd_7078433 := by
    simpa [prefixWord, tailWord_7078433, baseEnd_7078433] using wordTrace_append hprefix tailTrace_7078433
  have hstable : (prefixWord ++ tailWord_7078433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7078433).length < 2 ^ (prefixWord ++ tailWord_7078433).sum := by decide
  have hdescent : baseEnd_7078433 < baseStart_7078433 := by decide
  rcases family_descends (prefixWord ++ tailWord_7078433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7078477 : List Nat := [1, 6, 1, 1, 2, 1, 1, 1, 2, 5, 2]
def baseStart_7078477 : Nat := 118140960795 + 7078477 * 2 ^ 59
def prefixEnd_7078477 : Nat := 4983230072969 + 3 ^ 40 * 7078477 * 2
def baseEnd_7078477 : Nat := 3634661002795607159884183

theorem tailTrace_7078477 : CollatzResearch.WordTrace tailWord_7078477 prefixEnd_7078477 3634661002795607159884183 := by
  unfold tailWord_7078477
  simp only [CollatzResearch.WordTrace]
  refine ⟨258173265976894211470657685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172115510651262807647105123 258173265976894211470657685)
  ·
    refine ⟨12101871842666916162687079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 258173265976894211470657685 12101871842666916162687079)
    ·
      refine ⟨18152807764000374244030619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12101871842666916162687079 18152807764000374244030619)
      ·
        refine ⟨27229211646000561366045929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18152807764000374244030619 27229211646000561366045929)
        ·
          refine ⟨20421908734500421024534447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27229211646000561366045929 20421908734500421024534447)
          ·
            refine ⟨30632863101750631536801671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20421908734500421024534447 30632863101750631536801671)
            ·
              refine ⟨45949294652625947305202507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30632863101750631536801671 45949294652625947305202507)
              ·
                refine ⟨68923941978938920957803761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45949294652625947305202507 68923941978938920957803761)
                ·
                  refine ⟨51692956484204190718352821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68923941978938920957803761 51692956484204190718352821)
                  ·
                    refine ⟨4846214670394142879845577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51692956484204190718352821 4846214670394142879845577)
                    ·
                      refine ⟨3634661002795607159884183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4846214670394142879845577 3634661002795607159884183)
                      ·
                        rfl

theorem cell23_7078477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 1, 2, 5, 2].length) (baseStart_7078477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7078477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7078477 prefixEnd_7078477 := by exact prefixLift 7078477
  have htrace : WordTrace (prefixWord ++ tailWord_7078477) baseStart_7078477 baseEnd_7078477 := by
    simpa [prefixWord, tailWord_7078477, baseEnd_7078477] using wordTrace_append hprefix tailTrace_7078477
  have hstable : (prefixWord ++ tailWord_7078477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7078477).length < 2 ^ (prefixWord ++ tailWord_7078477).sum := by decide
  have hdescent : baseEnd_7078477 < baseStart_7078477 := by decide
  rcases family_descends (prefixWord ++ tailWord_7078477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7078500 : List Nat := [2, 3, 1, 1, 2, 2, 3, 2, 3, 4]
def baseStart_7078500 : Nat := 118140960795 + 7078500 * 2 ^ 59
def prefixEnd_7078500 : Nat := 4983230072969 + 3 ^ 40 * 7078500 * 2
def baseEnd_7078500 : Nat := 1211557604283553523298859

theorem tailTrace_7078500 : CollatzResearch.WordTrace tailWord_7078500 prefixEnd_7078500 1211557604283553523298859 := by
  unfold tailWord_7078500
  simp only [CollatzResearch.WordTrace]
  refine ⟨129087052427905443199372477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172116069903873924265829969 129087052427905443199372477)
  ·
    refine ⟨48407644660464541199764679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129087052427905443199372477 48407644660464541199764679)
    ·
      refine ⟨72611466990696811799647019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48407644660464541199764679 72611466990696811799647019)
      ·
        refine ⟨108917200486045217699470529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72611466990696811799647019 108917200486045217699470529)
        ·
          refine ⟨81687900364533913274602897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108917200486045217699470529 81687900364533913274602897)
          ·
            refine ⟨61265925273400434955952173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81687900364533913274602897 61265925273400434955952173)
            ·
              refine ⟨22974721977525163108482065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61265925273400434955952173 22974721977525163108482065)
              ·
                refine ⟨17231041483143872331361549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22974721977525163108482065 17231041483143872331361549)
                ·
                  refine ⟨6461640556178952124260581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17231041483143872331361549 6461640556178952124260581)
                  ·
                    refine ⟨1211557604283553523298859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6461640556178952124260581 1211557604283553523298859)
                    ·
                      rfl

theorem cell23_7078500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 2, 3, 4].length) (baseStart_7078500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7078500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7078500 prefixEnd_7078500 := by exact prefixLift 7078500
  have htrace : WordTrace (prefixWord ++ tailWord_7078500) baseStart_7078500 baseEnd_7078500 := by
    simpa [prefixWord, tailWord_7078500, baseEnd_7078500] using wordTrace_append hprefix tailTrace_7078500
  have hstable : (prefixWord ++ tailWord_7078500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7078500).length < 2 ^ (prefixWord ++ tailWord_7078500).sum := by decide
  have hdescent : baseEnd_7078500 < baseStart_7078500 := by decide
  rcases family_descends (prefixWord ++ tailWord_7078500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7078504 : List Nat := [2, 1, 4, 3, 3, 1, 1, 1, 2, 5]
def baseStart_7078504 : Nat := 118140960795 + 7078504 * 2 ^ 59
def prefixEnd_7078504 : Nat := 4983230072969 + 3 ^ 40 * 7078504 * 2
def baseEnd_7078504 : Nat := 1211558288924426184748853

theorem tailTrace_7078504 : CollatzResearch.WordTrace tailWord_7078504 prefixEnd_7078504 1211558288924426184748853 := by
  unfold tailWord_7078504
  simp only [CollatzResearch.WordTrace]
  refine ⟨129087125373898197540945283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172116167165197596721260377 129087125373898197540945283)
  ·
    refine ⟨193630688060847296311417925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129087125373898197540945283 193630688060847296311417925)
    ·
      refine ⟨36305754011408868058390861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 193630688060847296311417925 36305754011408868058390861)
      ·
        refine ⟨13614657754278325521896573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36305754011408868058390861 13614657754278325521896573)
        ·
          refine ⟨5105496657854372070711215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13614657754278325521896573 5105496657854372070711215)
          ·
            refine ⟨7658244986781558106066823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5105496657854372070711215 7658244986781558106066823)
            ·
              refine ⟨11487367480172337159100235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7658244986781558106066823 11487367480172337159100235)
              ·
                refine ⟨17231051220258505738650353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11487367480172337159100235 17231051220258505738650353)
                ·
                  refine ⟨12923288415193879303987765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17231051220258505738650353 12923288415193879303987765)
                  ·
                    refine ⟨1211558288924426184748853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12923288415193879303987765 1211558288924426184748853)
                    ·
                      rfl

theorem cell23_7078504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 1, 1, 2, 5].length) (baseStart_7078504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7078504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7078504 prefixEnd_7078504 := by exact prefixLift 7078504
  have htrace : WordTrace (prefixWord ++ tailWord_7078504) baseStart_7078504 baseEnd_7078504 := by
    simpa [prefixWord, tailWord_7078504, baseEnd_7078504] using wordTrace_append hprefix tailTrace_7078504
  have hstable : (prefixWord ++ tailWord_7078504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7078504).length < 2 ^ (prefixWord ++ tailWord_7078504).sum := by decide
  have hdescent : baseEnd_7078504 < baseStart_7078504 := by decide
  rcases family_descends (prefixWord ++ tailWord_7078504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7078533 : List Nat := [1, 3, 1, 1, 4, 2, 1, 1, 1, 2, 6]
def baseStart_7078533 : Nat := 118140960795 + 7078533 * 2 ^ 59
def prefixEnd_7078533 : Nat := 4983230072969 + 3 ^ 40 * 7078533 * 2
def baseEnd_7078533 : Nat := 3634689757712258940783925

theorem tailTrace_7078533 : CollatzResearch.WordTrace tailWord_7078533 prefixEnd_7078533 3634689757712258940783925 := by
  unfold tailWord_7078533
  simp only [CollatzResearch.WordTrace]
  refine ⟨258175308464691333034696253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172116872309794222023130835 258175308464691333034696253)
  ·
    refine ⟨96815740674259249888011095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 258175308464691333034696253 96815740674259249888011095)
    ·
      refine ⟨145223611011388874832016643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96815740674259249888011095 145223611011388874832016643)
      ·
        refine ⟨217835416517083312248024965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145223611011388874832016643 217835416517083312248024965)
        ·
          refine ⟨40844140596953121046504681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 217835416517083312248024965 40844140596953121046504681)
          ·
            refine ⟨30633105447714840784878511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40844140596953121046504681 30633105447714840784878511)
            ·
              refine ⟨45949658171572261177317767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30633105447714840784878511 45949658171572261177317767)
              ·
                refine ⟨68924487257358391765976651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45949658171572261177317767 68924487257358391765976651)
                ·
                  refine ⟨103386730886037587648964977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68924487257358391765976651 103386730886037587648964977)
                  ·
                    refine ⟨77540048164528190736723733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 103386730886037587648964977 77540048164528190736723733)
                    ·
                      refine ⟨3634689757712258940783925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77540048164528190736723733 3634689757712258940783925)
                      ·
                        rfl

theorem cell23_7078533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 1, 1, 2, 6].length) (baseStart_7078533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7078533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7078533 prefixEnd_7078533 := by exact prefixLift 7078533
  have htrace : WordTrace (prefixWord ++ tailWord_7078533) baseStart_7078533 baseEnd_7078533 := by
    simpa [prefixWord, tailWord_7078533, baseEnd_7078533] using wordTrace_append hprefix tailTrace_7078533
  have hstable : (prefixWord ++ tailWord_7078533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7078533).length < 2 ^ (prefixWord ++ tailWord_7078533).sum := by decide
  have hdescent : baseEnd_7078533 < baseStart_7078533 := by decide
  rcases family_descends (prefixWord ++ tailWord_7078533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7078557 : List Nat := [1, 4, 2, 1, 1, 1, 4, 2, 3, 1, 3]
def baseStart_7078557 : Nat := 118140960795 + 7078557 * 2 ^ 59
def prefixEnd_7078557 : Nat := 4983230072969 + 3 ^ 40 * 7078557 * 2
def baseEnd_7078557 : Nat := 3634702081247966846883815

theorem tailTrace_7078557 : CollatzResearch.WordTrace tailWord_7078557 prefixEnd_7078557 3634702081247966846883815 := by
  unfold tailWord_7078557
  simp only [CollatzResearch.WordTrace]
  refine ⟨258176183816604385133569925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172117455877736256755713283 258176183816604385133569925)
  ·
    refine ⟨48408034465613322212544361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 258176183816604385133569925 48408034465613322212544361)
    ·
      refine ⟨36306025849209991659408271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48408034465613322212544361 36306025849209991659408271)
      ·
        refine ⟨54459038773814987489112407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36306025849209991659408271 54459038773814987489112407)
        ·
          refine ⟨81688558160722481233668611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54459038773814987489112407 81688558160722481233668611)
          ·
            refine ⟨122532837241083721850502917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81688558160722481233668611 122532837241083721850502917)
            ·
              refine ⟨22974906982703197846969297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 122532837241083721850502917 22974906982703197846969297)
              ·
                refine ⟨17231180237027398385226973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22974906982703197846969297 17231180237027398385226973)
                ·
                  refine ⟨6461692588885274394460115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17231180237027398385226973 6461692588885274394460115)
                  ·
                    refine ⟨9692538883327911591690173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6461692588885274394460115 9692538883327911591690173)
                    ·
                      refine ⟨3634702081247966846883815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9692538883327911591690173 3634702081247966846883815)
                      ·
                        rfl

theorem cell23_7078557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 2, 3, 1, 3].length) (baseStart_7078557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7078557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7078557 prefixEnd_7078557 := by exact prefixLift 7078557
  have htrace : WordTrace (prefixWord ++ tailWord_7078557) baseStart_7078557 baseEnd_7078557 := by
    simpa [prefixWord, tailWord_7078557, baseEnd_7078557] using wordTrace_append hprefix tailTrace_7078557
  have hstable : (prefixWord ++ tailWord_7078557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7078557).length < 2 ^ (prefixWord ++ tailWord_7078557).sum := by decide
  have hdescent : baseEnd_7078557 < baseStart_7078557 := by decide
  rcases family_descends (prefixWord ++ tailWord_7078557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7078591 : List Nat := [1, 1, 2, 2, 2, 5, 3, 2, 1, 1, 3]
def baseStart_7078591 : Nat := 118140960795 + 7078591 * 2 ^ 59
def prefixEnd_7078591 : Nat := 4983230072969 + 3 ^ 40 * 7078591 * 2
def baseEnd_7078591 : Nat := 3634719539590219713858659

theorem tailTrace_7078591 : CollatzResearch.WordTrace tailWord_7078591 prefixEnd_7078591 3634719539590219713858659 := by
  unfold tailWord_7078591
  simp only [CollatzResearch.WordTrace]
  refine ⟨258177423898481208940307627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172118282598987472626871751 258177423898481208940307627)
  ·
    refine ⟨387266135847721813410461441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258177423898481208940307627 387266135847721813410461441)
    ·
      refine ⟨290449601885791360057846081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 387266135847721813410461441 290449601885791360057846081)
      ·
        refine ⟨217837201414343520043384561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 290449601885791360057846081 217837201414343520043384561)
        ·
          refine ⟨163377901060757640032538421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217837201414343520043384561 163377901060757640032538421)
          ·
            refine ⟨15316678224446028753050477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 163377901060757640032538421 15316678224446028753050477)
            ·
              refine ⟨5743754334167260782393929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15316678224446028753050477 5743754334167260782393929)
              ·
                refine ⟨4307815750625445586795447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5743754334167260782393929 4307815750625445586795447)
                ·
                  refine ⟨6461723625938168380193171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4307815750625445586795447 6461723625938168380193171)
                  ·
                    refine ⟨9692585438907252570289757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6461723625938168380193171 9692585438907252570289757)
                    ·
                      refine ⟨3634719539590219713858659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9692585438907252570289757 3634719539590219713858659)
                      ·
                        rfl

theorem cell23_7078591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 3, 2, 1, 1, 3].length) (baseStart_7078591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7078591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7078591 prefixEnd_7078591 := by exact prefixLift 7078591
  have htrace : WordTrace (prefixWord ++ tailWord_7078591) baseStart_7078591 baseEnd_7078591 := by
    simpa [prefixWord, tailWord_7078591, baseEnd_7078591] using wordTrace_append hprefix tailTrace_7078591
  have hstable : (prefixWord ++ tailWord_7078591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7078591).length < 2 ^ (prefixWord ++ tailWord_7078591).sum := by decide
  have hdescent : baseEnd_7078591 < baseStart_7078591 := by decide
  rcases family_descends (prefixWord ++ tailWord_7078591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7078598 : List Nat := [6, 1, 2, 1, 2, 2, 2, 1, 6]
def baseStart_7078598 : Nat := 118140960795 + 7078598 * 2 ^ 59
def prefixEnd_7078598 : Nat := 4983230072969 + 3 ^ 40 * 7078598 * 2
def baseEnd_7078598 : Nat := 403858125994977909607903

theorem tailTrace_7078598 : CollatzResearch.WordTrace tailWord_7078598 prefixEnd_7078598 403858125994977909607903 := by
  unfold tailWord_7078598
  simp only [CollatzResearch.WordTrace]
  refine ⟨8068052475295495285494139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 172118452806303899423874965 8068052475295495285494139)
  ·
    refine ⟨12102078712943242928241209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8068052475295495285494139 12102078712943242928241209)
    ·
      refine ⟨9076559034707432196180907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12102078712943242928241209 9076559034707432196180907)
      ·
        refine ⟨13614838552061148294271361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9076559034707432196180907 13614838552061148294271361)
        ·
          refine ⟨10211128914045861220703521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13614838552061148294271361 10211128914045861220703521)
          ·
            refine ⟨7658346685534395915527641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10211128914045861220703521 7658346685534395915527641)
            ·
              refine ⟨5743760014150796936645731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7658346685534395915527641 5743760014150796936645731)
              ·
                refine ⟨8615640021226195404968597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5743760014150796936645731 8615640021226195404968597)
                ·
                  refine ⟨403858125994977909607903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8615640021226195404968597 403858125994977909607903)
                  ·
                    rfl

theorem cell23_7078598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 2, 1, 6].length) (baseStart_7078598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7078598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7078598 prefixEnd_7078598 := by exact prefixLift 7078598
  have htrace : WordTrace (prefixWord ++ tailWord_7078598) baseStart_7078598 baseEnd_7078598 := by
    simpa [prefixWord, tailWord_7078598, baseEnd_7078598] using wordTrace_append hprefix tailTrace_7078598
  have hstable : (prefixWord ++ tailWord_7078598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7078598).length < 2 ^ (prefixWord ++ tailWord_7078598).sum := by decide
  have hdescent : baseEnd_7078598 < baseStart_7078598 := by decide
  rcases family_descends (prefixWord ++ tailWord_7078598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7078600 : List Nat := [2, 1, 3, 1, 2, 3, 2, 2, 1, 1, 5]
def baseStart_7078600 : Nat := 118140960795 + 7078600 * 2 ^ 59
def prefixEnd_7078600 : Nat := 4983230072969 + 3 ^ 40 * 7078600 * 2
def baseEnd_7078600 : Nat := 3634724160916110178646117

theorem tailTrace_7078600 : CollatzResearch.WordTrace tailWord_7078600 prefixEnd_7078600 3634724160916110178646117 := by
  unfold tailWord_7078600
  simp only [CollatzResearch.WordTrace]
  refine ⟨129088876077724301738692627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172118501436965735651590169 129088876077724301738692627)
  ·
    refine ⟨193633314116586452608038941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129088876077724301738692627 193633314116586452608038941)
    ·
      refine ⟨72612492793719919728014603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193633314116586452608038941 72612492793719919728014603)
      ·
        refine ⟨108918739190579879592021905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72612492793719919728014603 108918739190579879592021905)
        ·
          refine ⟨81689054392934909694016429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108918739190579879592021905 81689054392934909694016429)
          ·
            refine ⟨30633395397350591135256161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81689054392934909694016429 30633395397350591135256161)
            ·
              refine ⟨22975046548012943351442121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30633395397350591135256161 22975046548012943351442121)
              ·
                refine ⟨17231284911009707513581591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22975046548012943351442121 17231284911009707513581591)
                ·
                  refine ⟨25846927366514561270372387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17231284911009707513581591 25846927366514561270372387)
                  ·
                    refine ⟨38770391049771841905558581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25846927366514561270372387 38770391049771841905558581)
                    ·
                      refine ⟨3634724160916110178646117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38770391049771841905558581 3634724160916110178646117)
                      ·
                        rfl

theorem cell23_7078600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 2, 1, 1, 5].length) (baseStart_7078600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7078600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7078600 prefixEnd_7078600 := by exact prefixLift 7078600
  have htrace : WordTrace (prefixWord ++ tailWord_7078600) baseStart_7078600 baseEnd_7078600 := by
    simpa [prefixWord, tailWord_7078600, baseEnd_7078600] using wordTrace_append hprefix tailTrace_7078600
  have hstable : (prefixWord ++ tailWord_7078600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7078600).length < 2 ^ (prefixWord ++ tailWord_7078600).sum := by decide
  have hdescent : baseEnd_7078600 < baseStart_7078600 := by decide
  rcases family_descends (prefixWord ++ tailWord_7078600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7078627 : List Nat := [1, 1, 1, 7, 1, 2, 1, 2, 1, 2, 4]
def baseStart_7078627 : Nat := 118140960795 + 7078627 * 2 ^ 59
def prefixEnd_7078627 : Nat := 4983230072969 + 3 ^ 40 * 7078627 * 2
def baseEnd_7078627 : Nat := 3634738024893781573008493

theorem tailTrace_7078627 : CollatzResearch.WordTrace tailWord_7078627 prefixEnd_7078627 3634738024893781573008493 := by
  unfold tailWord_7078627
  simp only [CollatzResearch.WordTrace]
  refine ⟨258178736926350787088618135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172119157950900524725745423 258178736926350787088618135)
  ·
    refine ⟨387268105389526180632927203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258178736926350787088618135 387268105389526180632927203)
    ·
      refine ⟨580902158084289270949390805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 387268105389526180632927203 580902158084289270949390805)
      ·
        refine ⟨13614894330100529787876347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 580902158084289270949390805 13614894330100529787876347)
        ·
          refine ⟨20422341495150794681814521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13614894330100529787876347 20422341495150794681814521)
          ·
            refine ⟨15316756121363096011360891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20422341495150794681814521 15316756121363096011360891)
            ·
              refine ⟨22975134182044644017041337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15316756121363096011360891 22975134182044644017041337)
              ·
                refine ⟨17231350636533483012781003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22975134182044644017041337 17231350636533483012781003)
                ·
                  refine ⟨25847025954800224519171505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17231350636533483012781003 25847025954800224519171505)
                  ·
                    refine ⟨19385269466100168389378629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25847025954800224519171505 19385269466100168389378629)
                    ·
                      refine ⟨3634738024893781573008493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19385269466100168389378629 3634738024893781573008493)
                      ·
                        rfl

theorem cell23_7078627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_7078627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7078627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7078627 prefixEnd_7078627 := by exact prefixLift 7078627
  have htrace : WordTrace (prefixWord ++ tailWord_7078627) baseStart_7078627 baseEnd_7078627 := by
    simpa [prefixWord, tailWord_7078627, baseEnd_7078627] using wordTrace_append hprefix tailTrace_7078627
  have hstable : (prefixWord ++ tailWord_7078627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7078627).length < 2 ^ (prefixWord ++ tailWord_7078627).sum := by decide
  have hdescent : baseEnd_7078627 < baseStart_7078627 := by decide
  rcases family_descends (prefixWord ++ tailWord_7078627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7078664 : List Nat := [2, 1, 3, 2, 2, 2, 2, 3, 2, 1, 3]
def baseStart_7078664 : Nat := 118140960795 + 7078664 * 2 ^ 59
def prefixEnd_7078664 : Nat := 4983230072969 + 3 ^ 40 * 7078664 * 2
def baseEnd_7078664 : Nat := 3634757023677997928245823

theorem tailTrace_7078664 : CollatzResearch.WordTrace tailWord_7078664 prefixEnd_7078664 3634757023677997928245823 := by
  unfold tailWord_7078664
  simp only [CollatzResearch.WordTrace]
  refine ⟨129090043213608371203857523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172120057618144494938476697 129090043213608371203857523)
  ·
    refine ⟨193635064820412556805786285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129090043213608371203857523 193635064820412556805786285)
    ·
      refine ⟨72613149307654708802169857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193635064820412556805786285 72613149307654708802169857)
      ·
        refine ⟨54459861980741031601627393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72613149307654708802169857 54459861980741031601627393)
        ·
          refine ⟨40844896485555773701220545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54459861980741031601627393 40844896485555773701220545)
          ·
            refine ⟨30633672364166830275915409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40844896485555773701220545 30633672364166830275915409)
            ·
              refine ⟨22975254273125122706936557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30633672364166830275915409 22975254273125122706936557)
              ·
                refine ⟨8615720352421921015101209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22975254273125122706936557 8615720352421921015101209)
                ·
                  refine ⟨6461790264316440761325907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8615720352421921015101209 6461790264316440761325907)
                  ·
                    refine ⟨9692685396474661141988861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6461790264316440761325907 9692685396474661141988861)
                    ·
                      refine ⟨3634757023677997928245823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9692685396474661141988861 3634757023677997928245823)
                      ·
                        rfl

theorem cell23_7078664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 3, 2, 1, 3].length) (baseStart_7078664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7078664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7078664 prefixEnd_7078664 := by exact prefixLift 7078664
  have htrace : WordTrace (prefixWord ++ tailWord_7078664) baseStart_7078664 baseEnd_7078664 := by
    simpa [prefixWord, tailWord_7078664, baseEnd_7078664] using wordTrace_append hprefix tailTrace_7078664
  have hstable : (prefixWord ++ tailWord_7078664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7078664).length < 2 ^ (prefixWord ++ tailWord_7078664).sum := by decide
  have hdescent : baseEnd_7078664 < baseStart_7078664 := by decide
  rcases family_descends (prefixWord ++ tailWord_7078664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7078670 : List Nat := [4, 1, 1, 2, 1, 1, 1, 1, 4, 3, 4]
def baseStart_7078670 : Nat := 118140960795 + 7078670 * 2 ^ 59
def prefixEnd_7078670 : Nat := 4983230072969 + 3 ^ 40 * 7078670 * 2
def baseEnd_7078670 : Nat := 3634760104561924904770795

theorem tailTrace_7078670 : CollatzResearch.WordTrace tailWord_7078670 prefixEnd_7078670 3634760104561924904770795 := by
  unfold tailWord_7078670
  simp only [CollatzResearch.WordTrace]
  refine ⟨32272538158149375679054183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172120203510130003621622309 32272538158149375679054183)
  ·
    refine ⟨48408807237224063518581275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32272538158149375679054183 48408807237224063518581275)
    ·
      refine ⟨72613210855836095277871913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48408807237224063518581275 72613210855836095277871913)
      ·
        refine ⟨54459908141877071458403935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72613210855836095277871913 54459908141877071458403935)
        ·
          refine ⟨81689862212815607187605903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54459908141877071458403935 81689862212815607187605903)
          ·
            refine ⟨122534793319223410781408855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81689862212815607187605903 122534793319223410781408855)
            ·
              refine ⟨183802189978835116172113283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122534793319223410781408855 183802189978835116172113283)
              ·
                refine ⟨275703284968252674258169925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 183802189978835116172113283 275703284968252674258169925)
                ·
                  refine ⟨51694365931547376423406861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 275703284968252674258169925 51694365931547376423406861)
                  ·
                    refine ⟨19385387224330266158777573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51694365931547376423406861 19385387224330266158777573)
                    ·
                      refine ⟨3634760104561924904770795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19385387224330266158777573 3634760104561924904770795)
                      ·
                        rfl

theorem cell23_7078670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 4, 3, 4].length) (baseStart_7078670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7078670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7078670 prefixEnd_7078670 := by exact prefixLift 7078670
  have htrace : WordTrace (prefixWord ++ tailWord_7078670) baseStart_7078670 baseEnd_7078670 := by
    simpa [prefixWord, tailWord_7078670, baseEnd_7078670] using wordTrace_append hprefix tailTrace_7078670
  have hstable : (prefixWord ++ tailWord_7078670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7078670).length < 2 ^ (prefixWord ++ tailWord_7078670).sum := by decide
  have hdescent : baseEnd_7078670 < baseStart_7078670 := by decide
  rcases family_descends (prefixWord ++ tailWord_7078670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7078685 : List Nat := [1, 4, 2, 4, 2, 1, 2, 1, 1, 2, 3]
def baseStart_7078685 : Nat := 118140960795 + 7078685 * 2 ^ 59
def prefixEnd_7078685 : Nat := 4983230072969 + 3 ^ 40 * 7078685 * 2
def baseEnd_7078685 : Nat := 3634767806771742346083227

theorem tailTrace_7078685 : CollatzResearch.WordTrace tailWord_7078685 prefixEnd_7078685 3634767806771742346083227 := by
  unfold tailWord_7078685
  simp only [CollatzResearch.WordTrace]
  refine ⟨258180852360140662994229509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172120568240093775329486339 258180852360140662994229509)
  ·
    refine ⟨48408909817526374311418033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 258180852360140662994229509 48408909817526374311418033)
    ·
      refine ⟨36306682363144780733563525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48408909817526374311418033 36306682363144780733563525)
      ·
        refine ⟨6807502943089646387543161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36306682363144780733563525 6807502943089646387543161)
        ·
          refine ⟨5105627207317234790657371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6807502943089646387543161 5105627207317234790657371)
          ·
            refine ⟨7658440810975852185986057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5105627207317234790657371 7658440810975852185986057)
            ·
              refine ⟨5743830608231889139489543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7658440810975852185986057 5743830608231889139489543)
              ·
                refine ⟨8615745912347833709234315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5743830608231889139489543 8615745912347833709234315)
                ·
                  refine ⟨12923618868521750563851473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8615745912347833709234315 12923618868521750563851473)
                  ·
                    refine ⟨9692714151391312922888605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12923618868521750563851473 9692714151391312922888605)
                    ·
                      refine ⟨3634767806771742346083227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9692714151391312922888605 3634767806771742346083227)
                      ·
                        rfl

theorem cell23_7078685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_7078685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7078685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7078685 prefixEnd_7078685 := by exact prefixLift 7078685
  have htrace : WordTrace (prefixWord ++ tailWord_7078685) baseStart_7078685 baseEnd_7078685 := by
    simpa [prefixWord, tailWord_7078685, baseEnd_7078685] using wordTrace_append hprefix tailTrace_7078685
  have hstable : (prefixWord ++ tailWord_7078685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7078685).length < 2 ^ (prefixWord ++ tailWord_7078685).sum := by decide
  have hdescent : baseEnd_7078685 < baseStart_7078685 := by decide
  rcases family_descends (prefixWord ++ tailWord_7078685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7078700 : List Nat := [2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 4]
def baseStart_7078700 : Nat := 118140960795 + 7078700 * 2 ^ 59
def prefixEnd_7078700 : Nat := 4983230072969 + 3 ^ 40 * 7078700 * 2
def baseEnd_7078700 : Nat := 3634775508981559787395657

theorem tailTrace_7078700 : CollatzResearch.WordTrace tailWord_7078700 prefixEnd_7078700 3634775508981559787395657 := by
  unfold tailWord_7078700
  simp only [CollatzResearch.WordTrace]
  refine ⟨129090699727543160278012777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172120932970057547037350369 129090699727543160278012777)
  ·
    refine ⟨96818024795657370208509583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129090699727543160278012777 96818024795657370208509583)
    ·
      refine ⟨145227037193486055312764375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96818024795657370208509583 145227037193486055312764375)
      ·
        refine ⟨217840555790229082969146563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145227037193486055312764375 217840555790229082969146563)
        ·
          refine ⟨326760833685343624453719845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217840555790229082969146563 326760833685343624453719845)
          ·
            refine ⟨61267656316001929585072471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 326760833685343624453719845 61267656316001929585072471)
            ·
              refine ⟨91901484474002894377608707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61267656316001929585072471 91901484474002894377608707)
              ·
                refine ⟨137852226711004341566413061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91901484474002894377608707 137852226711004341566413061)
                ·
                  refine ⟨25847292508313314043702449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 137852226711004341566413061 25847292508313314043702449)
                  ·
                    refine ⟨19385469381234985532776837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25847292508313314043702449 19385469381234985532776837)
                    ·
                      refine ⟨3634775508981559787395657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19385469381234985532776837 3634775508981559787395657)
                      ·
                        rfl

theorem cell23_7078700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 4].length) (baseStart_7078700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7078700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7078700 prefixEnd_7078700 := by exact prefixLift 7078700
  have htrace : WordTrace (prefixWord ++ tailWord_7078700) baseStart_7078700 baseEnd_7078700 := by
    simpa [prefixWord, tailWord_7078700, baseEnd_7078700] using wordTrace_append hprefix tailTrace_7078700
  have hstable : (prefixWord ++ tailWord_7078700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7078700).length < 2 ^ (prefixWord ++ tailWord_7078700).sum := by decide
  have hdescent : baseEnd_7078700 < baseStart_7078700 := by decide
  rcases family_descends (prefixWord ++ tailWord_7078700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7078780 : List Nat := [2, 2, 2, 1, 1, 1, 1, 2, 1, 5, 5]
def baseStart_7078780 : Nat := 118140960795 + 7078780 * 2 ^ 59
def prefixEnd_7078780 : Nat := 4983230072969 + 3 ^ 40 * 7078780 * 2
def baseEnd_7078780 : Nat := 3634816587433919474395289

theorem tailTrace_7078780 : CollatzResearch.WordTrace tailWord_7078780 prefixEnd_7078780 3634816587433919474395289 := by
  unfold tailWord_7078780
  simp only [CollatzResearch.WordTrace]
  refine ⟨129092158647398247109468897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172122878196530996145958529 129092158647398247109468897)
  ·
    refine ⟨96819118985548685332101673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129092158647398247109468897 96819118985548685332101673)
    ·
      refine ⟨72614339239161513999076255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96819118985548685332101673 72614339239161513999076255)
      ·
        refine ⟨108921508858742270998614383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72614339239161513999076255 108921508858742270998614383)
        ·
          refine ⟨163382263288113406497921575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108921508858742270998614383 163382263288113406497921575)
          ·
            refine ⟨245073394932170109746882363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163382263288113406497921575 245073394932170109746882363)
            ·
              refine ⟨367610092398255164620323545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 245073394932170109746882363 367610092398255164620323545)
              ·
                refine ⟨275707569298691373465242659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 367610092398255164620323545 275707569298691373465242659)
                ·
                  refine ⟨413561353948037060197863989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 275707569298691373465242659 413561353948037060197863989)
                  ·
                    refine ⟨38771376932628474393549749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 413561353948037060197863989 38771376932628474393549749)
                    ·
                      refine ⟨3634816587433919474395289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38771376932628474393549749 3634816587433919474395289)
                      ·
                        rfl

theorem cell23_7078780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 1, 5, 5].length) (baseStart_7078780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7078780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7078780 prefixEnd_7078780 := by exact prefixLift 7078780
  have htrace : WordTrace (prefixWord ++ tailWord_7078780) baseStart_7078780 baseEnd_7078780 := by
    simpa [prefixWord, tailWord_7078780, baseEnd_7078780] using wordTrace_append hprefix tailTrace_7078780
  have hstable : (prefixWord ++ tailWord_7078780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7078780).length < 2 ^ (prefixWord ++ tailWord_7078780).sum := by decide
  have hdescent : baseEnd_7078780 < baseStart_7078780 := by decide
  rcases family_descends (prefixWord ++ tailWord_7078780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7078787 : List Nat := [1, 1, 1, 3, 4, 1, 2, 1, 5, 4]
def baseStart_7078787 : Nat := 118140960795 + 7078787 * 2 ^ 59
def prefixEnd_7078787 : Nat := 4983230072969 + 3 ^ 40 * 7078787 * 2
def baseEnd_7078787 : Nat := 1211606727266166982335919

theorem tailTrace_7078787 : CollatzResearch.WordTrace tailWord_7078787 prefixEnd_7078787 1211606727266166982335919 := by
  unfold tailWord_7078787
  simp only [CollatzResearch.WordTrace]
  refine ⟨258184572605771134414442615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172123048403847422942961743 258184572605771134414442615)
  ·
    refine ⟨387276858908656701621663923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258184572605771134414442615 387276858908656701621663923)
    ·
      refine ⟨580915288362985052432495885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 387276858908656701621663923 580915288362985052432495885)
      ·
        refine ⟨217843233136119394662185957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 580915288362985052432495885 217843233136119394662185957)
        ·
          refine ⟨40845606213022386499159867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 217843233136119394662185957 40845606213022386499159867)
          ·
            refine ⟨61268409319533579748739801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40845606213022386499159867 61268409319533579748739801)
            ·
              refine ⟨45951306989650184811554851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61268409319533579748739801 45951306989650184811554851)
              ·
                refine ⟨68926960484475277217332277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45951306989650184811554851 68926960484475277217332277)
                ·
                  refine ⟨6461902545419557239124901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68926960484475277217332277 6461902545419557239124901)
                  ·
                    refine ⟨1211606727266166982335919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6461902545419557239124901 1211606727266166982335919)
                    ·
                      rfl

theorem cell23_7078787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 1, 5, 4].length) (baseStart_7078787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7078787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7078787 prefixEnd_7078787 := by exact prefixLift 7078787
  have htrace : WordTrace (prefixWord ++ tailWord_7078787) baseStart_7078787 baseEnd_7078787 := by
    simpa [prefixWord, tailWord_7078787, baseEnd_7078787] using wordTrace_append hprefix tailTrace_7078787
  have hstable : (prefixWord ++ tailWord_7078787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7078787).length < 2 ^ (prefixWord ++ tailWord_7078787).sum := by decide
  have hdescent : baseEnd_7078787 < baseStart_7078787 := by decide
  rcases family_descends (prefixWord ++ tailWord_7078787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7078794 : List Nat := [3, 1, 2, 4, 1, 1, 1, 3, 2, 1, 4]
def baseStart_7078794 : Nat := 118140960795 + 7078794 * 2 ^ 59
def prefixEnd_7078794 : Nat := 4983230072969 + 3 ^ 40 * 7078794 * 2
def baseEnd_7078794 : Nat := 3634823776163082419620225

theorem tailTrace_7078794 : CollatzResearch.WordTrace tailWord_7078794 prefixEnd_7078794 3634823776163082419620225 := by
  unfold tailWord_7078794
  simp only [CollatzResearch.WordTrace]
  refine ⟨64546206979186443652486859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172123218611163849739964957 64546206979186443652486859)
  ·
    refine ⟨96819310468779665478730289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64546206979186443652486859 96819310468779665478730289)
    ·
      refine ⟨72614482851584749109047717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96819310468779665478730289 72614482851584749109047717)
      ·
        refine ⟨13615215534672140457946447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72614482851584749109047717 13615215534672140457946447)
        ·
          refine ⟨20422823302008210686919671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13615215534672140457946447 20422823302008210686919671)
          ·
            refine ⟨30634234953012316030379507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20422823302008210686919671 30634234953012316030379507)
            ·
              refine ⟨45951352429518474045569261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30634234953012316030379507 45951352429518474045569261)
              ·
                refine ⟨17231757161069427767088473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45951352429518474045569261 17231757161069427767088473)
                ·
                  refine ⟨12923817870802070825316355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17231757161069427767088473 12923817870802070825316355)
                  ·
                    refine ⟨19385726806203106237974533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12923817870802070825316355 19385726806203106237974533)
                    ·
                      refine ⟨3634823776163082419620225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19385726806203106237974533 3634823776163082419620225)
                      ·
                        rfl

theorem cell23_7078794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_7078794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7078794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7078794 prefixEnd_7078794 := by exact prefixLift 7078794
  have htrace : WordTrace (prefixWord ++ tailWord_7078794) baseStart_7078794 baseEnd_7078794 := by
    simpa [prefixWord, tailWord_7078794, baseEnd_7078794] using wordTrace_append hprefix tailTrace_7078794
  have hstable : (prefixWord ++ tailWord_7078794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7078794).length < 2 ^ (prefixWord ++ tailWord_7078794).sum := by decide
  have hdescent : baseEnd_7078794 < baseStart_7078794 := by decide
  rcases family_descends (prefixWord ++ tailWord_7078794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7078898 : List Nat := [3, 2, 1, 5, 1, 1, 2, 2, 1, 5]
def baseStart_7078898 : Nat := 118140960795 + 7078898 * 2 ^ 59
def prefixEnd_7078898 : Nat := 4983230072969 + 3 ^ 40 * 7078898 * 2
def baseEnd_7078898 : Nat := 1211625726050383337573249

theorem tailTrace_7078898 : CollatzResearch.WordTrace tailWord_7078898 prefixEnd_7078898 1211625726050383337573249 := by
  unfold tailWord_7078898
  simp only [CollatzResearch.WordTrace]
  refine ⟨64547155277092250092933337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172125747405579333581155565 64547155277092250092933337)
  ·
    refine ⟨48410366457819187569700003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64547155277092250092933337 48410366457819187569700003)
    ·
      refine ⟨72615549686728781354550005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48410366457819187569700003 72615549686728781354550005)
      ·
        refine ⟨6807707783130823251989063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 72615549686728781354550005 6807707783130823251989063)
        ·
          refine ⟨10211561674696234877983595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6807707783130823251989063 10211561674696234877983595)
          ·
            refine ⟨15317342512044352316975393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10211561674696234877983595 15317342512044352316975393)
            ·
              refine ⟨11488006884033264237731545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15317342512044352316975393 11488006884033264237731545)
              ·
                refine ⟨8616005163024948178298659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11488006884033264237731545 8616005163024948178298659)
                ·
                  refine ⟨12924007744537422267447989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8616005163024948178298659 12924007744537422267447989)
                  ·
                    refine ⟨1211625726050383337573249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12924007744537422267447989 1211625726050383337573249)
                    ·
                      rfl

theorem cell23_7078898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 2, 2, 1, 5].length) (baseStart_7078898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7078898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7078898 prefixEnd_7078898 := by exact prefixLift 7078898
  have htrace : WordTrace (prefixWord ++ tailWord_7078898) baseStart_7078898 baseEnd_7078898 := by
    simpa [prefixWord, tailWord_7078898, baseEnd_7078898] using wordTrace_append hprefix tailTrace_7078898
  have hstable : (prefixWord ++ tailWord_7078898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7078898).length < 2 ^ (prefixWord ++ tailWord_7078898).sum := by decide
  have hdescent : baseEnd_7078898 < baseStart_7078898 := by decide
  rcases family_descends (prefixWord ++ tailWord_7078898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7078935 : List Nat := [1, 1, 3, 5, 1, 3, 1, 1, 3, 2, 2]
def baseStart_7078935 : Nat := 118140960795 + 7078935 * 2 ^ 59
def prefixEnd_7078935 : Nat := 4983230072969 + 3 ^ 40 * 7078935 * 2
def baseEnd_7078935 : Nat := 3634896176935366367957077

theorem tailTrace_7078935 : CollatzResearch.WordTrace tailWord_7078935 prefixEnd_7078935 3634896176935366367957077 := by
  unfold tailWord_7078935
  simp only [CollatzResearch.WordTrace]
  refine ⟨258189970609234955690830259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172126647072823303793886839 258189970609234955690830259)
  ·
    refine ⟨387284955913852433536245389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258189970609234955690830259 387284955913852433536245389)
    ·
      refine ⟨145231858467694662576092021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 387284955913852433536245389 145231858467694662576092021)
      ·
        refine ⟨13615486731346374616508627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 145231858467694662576092021 13615486731346374616508627)
        ·
          refine ⟨20423230097019561924762941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13615486731346374616508627 20423230097019561924762941)
          ·
            refine ⟨7658711286382335721786103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20423230097019561924762941 7658711286382335721786103)
            ·
              refine ⟨11488066929573503582679155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7658711286382335721786103 11488066929573503582679155)
              ·
                refine ⟨17232100394360255374018733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11488066929573503582679155 17232100394360255374018733)
                ·
                  refine ⟨6462037647885095765257025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17232100394360255374018733 6462037647885095765257025)
                  ·
                    refine ⟨4846528235913821823942769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6462037647885095765257025 4846528235913821823942769)
                    ·
                      refine ⟨3634896176935366367957077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4846528235913821823942769 3634896176935366367957077)
                      ·
                        rfl

theorem cell23_7078935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 1, 1, 3, 2, 2].length) (baseStart_7078935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7078935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7078935 prefixEnd_7078935 := by exact prefixLift 7078935
  have htrace : WordTrace (prefixWord ++ tailWord_7078935) baseStart_7078935 baseEnd_7078935 := by
    simpa [prefixWord, tailWord_7078935, baseEnd_7078935] using wordTrace_append hprefix tailTrace_7078935
  have hstable : (prefixWord ++ tailWord_7078935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7078935).length < 2 ^ (prefixWord ++ tailWord_7078935).sum := by decide
  have hdescent : baseEnd_7078935 < baseStart_7078935 := by decide
  rcases family_descends (prefixWord ++ tailWord_7078935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7078961 : List Nat := [1, 2, 2, 3, 1, 2, 3, 1, 3, 3, 2]
def baseStart_7078961 : Nat := 118140960795 + 7078961 * 2 ^ 59
def prefixEnd_7078961 : Nat := 4983230072969 + 3 ^ 40 * 7078961 * 2
def baseEnd_7078961 : Nat := 3634909527432383266231957

theorem tailTrace_7078961 : CollatzResearch.WordTrace tailWord_7078961 prefixEnd_7078961 3634909527432383266231957 := by
  unfold tailWord_7078961
  simp only [CollatzResearch.WordTrace]
  refine ⟨258190918907140762131276737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172127279271427174754184491 258190918907140762131276737)
  ·
    refine ⟨193643189180355571598457553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258190918907140762131276737 193643189180355571598457553)
    ·
      refine ⟨145232391885266678698843165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193643189180355571598457553 145232391885266678698843165)
      ·
        refine ⟨54462146956975004512066187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145232391885266678698843165 54462146956975004512066187)
        ·
          refine ⟨81693220435462506768099281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54462146956975004512066187 81693220435462506768099281)
          ·
            refine ⟨61269915326596880076074461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81693220435462506768099281 61269915326596880076074461)
            ·
              refine ⟨22976218247473830028527923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61269915326596880076074461 22976218247473830028527923)
              ·
                refine ⟨34464327371210745042791885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22976218247473830028527923 34464327371210745042791885)
                ·
                  refine ⟨12924122764204029391046957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34464327371210745042791885 12924122764204029391046957)
                  ·
                    refine ⟨4846546036576511021642609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12924122764204029391046957 4846546036576511021642609)
                    ·
                      refine ⟨3634909527432383266231957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4846546036576511021642609 3634909527432383266231957)
                      ·
                        rfl

theorem cell23_7078961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 1, 3, 3, 2].length) (baseStart_7078961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7078961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7078961 prefixEnd_7078961 := by exact prefixLift 7078961
  have htrace : WordTrace (prefixWord ++ tailWord_7078961) baseStart_7078961 baseEnd_7078961 := by
    simpa [prefixWord, tailWord_7078961, baseEnd_7078961] using wordTrace_append hprefix tailTrace_7078961
  have hstable : (prefixWord ++ tailWord_7078961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7078961).length < 2 ^ (prefixWord ++ tailWord_7078961).sum := by decide
  have hdescent : baseEnd_7078961 < baseStart_7078961 := by decide
  rcases family_descends (prefixWord ++ tailWord_7078961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7078967 : List Nat := [1, 1, 3, 1, 2, 2, 1, 2, 4, 6]
def baseStart_7078967 : Nat := 118140960795 + 7078967 * 2 ^ 59
def prefixEnd_7078967 : Nat := 4983230072969 + 3 ^ 40 * 7078967 * 2
def baseEnd_7078967 : Nat := 1211637536105436747585643

theorem tailTrace_7078967 : CollatzResearch.WordTrace tailWord_7078967 prefixEnd_7078967 1211637536105436747585643 := by
  unfold tailWord_7078967
  simp only [CollatzResearch.WordTrace]
  refine ⟨258191137745119025155995155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172127425163412683437330103 258191137745119025155995155)
  ·
    refine ⟨387286706617678537733992733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258191137745119025155995155 387286706617678537733992733)
    ·
      refine ⟨145232514981629451650247275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 387286706617678537733992733 145232514981629451650247275)
      ·
        refine ⟨217848772472444177475370913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145232514981629451650247275 217848772472444177475370913)
        ·
          refine ⟨163386579354333133106528185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217848772472444177475370913 163386579354333133106528185)
          ·
            refine ⟨122539934515749849829896139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163386579354333133106528185 122539934515749849829896139)
            ·
              refine ⟨183809901773624774744844209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122539934515749849829896139 183809901773624774744844209)
              ·
                refine ⟨137857426330218581058633157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 183809901773624774744844209 137857426330218581058633157)
                ·
                  refine ⟨25848267436915983948493717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 137857426330218581058633157 25848267436915983948493717)
                  ·
                    refine ⟨1211637536105436747585643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25848267436915983948493717 1211637536105436747585643)
                    ·
                      rfl

theorem cell23_7078967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 4, 6].length) (baseStart_7078967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7078967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7078967 prefixEnd_7078967 := by exact prefixLift 7078967
  have htrace : WordTrace (prefixWord ++ tailWord_7078967) baseStart_7078967 baseEnd_7078967 := by
    simpa [prefixWord, tailWord_7078967, baseEnd_7078967] using wordTrace_append hprefix tailTrace_7078967
  have hstable : (prefixWord ++ tailWord_7078967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7078967).length < 2 ^ (prefixWord ++ tailWord_7078967).sum := by decide
  have hdescent : baseEnd_7078967 < baseStart_7078967 := by decide
  rcases family_descends (prefixWord ++ tailWord_7078967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7079008 : List Nat := [2, 1, 1, 3, 2, 2, 1, 5, 2, 2, 2]
def baseStart_7079008 : Nat := 118140960795 + 7079008 * 2 ^ 59
def prefixEnd_7079008 : Nat := 4983230072969 + 3 ^ 40 * 7079008 * 2
def baseEnd_7079008 : Nat := 3634933661023144582344241

theorem tailTrace_7079008 : CollatzResearch.WordTrace tailWord_7079008 prefixEnd_7079008 3634933661023144582344241 := by
  unfold tailWord_7079008
  simp only [CollatzResearch.WordTrace]
  refine ⟨129096316568985244579118839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172128422091980326105491785 129096316568985244579118839)
  ·
    refine ⟨193644474853477866868678259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129096316568985244579118839 193644474853477866868678259)
    ·
      refine ⟨290466712280216800303017389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193644474853477866868678259 290466712280216800303017389)
      ·
        refine ⟨108925017105081300113631521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 290466712280216800303017389 108925017105081300113631521)
        ·
          refine ⟨81693762828810975085223641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108925017105081300113631521 81693762828810975085223641)
          ·
            refine ⟨61270322121608231313917731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81693762828810975085223641 61270322121608231313917731)
            ·
              refine ⟨91905483182412346970876597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61270322121608231313917731 91905483182412346970876597)
              ·
                refine ⟨8616139048351157528519681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 91905483182412346970876597 8616139048351157528519681)
                ·
                  refine ⟨6462104286263368146389761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8616139048351157528519681 6462104286263368146389761)
                  ·
                    refine ⟨4846578214697526109792321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6462104286263368146389761 4846578214697526109792321)
                    ·
                      refine ⟨3634933661023144582344241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4846578214697526109792321 3634933661023144582344241)
                      ·
                        rfl

theorem cell23_7079008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 5, 2, 2, 2].length) (baseStart_7079008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7079008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7079008 prefixEnd_7079008 := by exact prefixLift 7079008
  have htrace : WordTrace (prefixWord ++ tailWord_7079008) baseStart_7079008 baseEnd_7079008 := by
    simpa [prefixWord, tailWord_7079008, baseEnd_7079008] using wordTrace_append hprefix tailTrace_7079008
  have hstable : (prefixWord ++ tailWord_7079008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7079008).length < 2 ^ (prefixWord ++ tailWord_7079008).sum := by decide
  have hdescent : baseEnd_7079008 < baseStart_7079008 := by decide
  rcases family_descends (prefixWord ++ tailWord_7079008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7079024 : List Nat := [2, 1, 1, 1, 5, 1, 1, 2, 1, 5, 3]
def baseStart_7079024 : Nat := 118140960795 + 7079024 * 2 ^ 59
def prefixEnd_7079024 : Nat := 4983230072969 + 3 ^ 40 * 7079024 * 2
def baseEnd_7079024 : Nat := 3634941876713616519744167

theorem tailTrace_7079024 : CollatzResearch.WordTrace tailWord_7079024 prefixEnd_7079024 3634941876713616519744167 := by
  unfold tailWord_7079024
  simp only [CollatzResearch.WordTrace]
  refine ⟨129096608352956261945410063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172128811137275015927213417 129096608352956261945410063)
  ·
    refine ⟨193644912529434392918115095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129096608352956261945410063 193644912529434392918115095)
    ·
      refine ⟨290467368794151589377172643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193644912529434392918115095 290467368794151589377172643)
      ·
        refine ⟨435701053191227384065758965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290467368794151589377172643 435701053191227384065758965)
        ·
          refine ⟨40846973736677567256164903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 435701053191227384065758965 40846973736677567256164903)
          ·
            refine ⟨61270460605016350884247355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40846973736677567256164903 61270460605016350884247355)
            ·
              refine ⟨91905690907524526326371033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61270460605016350884247355 91905690907524526326371033)
              ·
                refine ⟨68929268180643394744778275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91905690907524526326371033 68929268180643394744778275)
                ·
                  refine ⟨103393902270965092117167413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68929268180643394744778275 103393902270965092117167413)
                  ·
                    refine ⟨9693178337902977385984445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 103393902270965092117167413 9693178337902977385984445)
                    ·
                      refine ⟨3634941876713616519744167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9693178337902977385984445 3634941876713616519744167)
                      ·
                        rfl

theorem cell23_7079024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 2, 1, 5, 3].length) (baseStart_7079024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7079024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7079024 prefixEnd_7079024 := by exact prefixLift 7079024
  have htrace : WordTrace (prefixWord ++ tailWord_7079024) baseStart_7079024 baseEnd_7079024 := by
    simpa [prefixWord, tailWord_7079024, baseEnd_7079024] using wordTrace_append hprefix tailTrace_7079024
  have hstable : (prefixWord ++ tailWord_7079024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7079024).length < 2 ^ (prefixWord ++ tailWord_7079024).sum := by decide
  have hdescent : baseEnd_7079024 < baseStart_7079024 := by decide
  rcases family_descends (prefixWord ++ tailWord_7079024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7079029 : List Nat := [1, 3, 4, 3, 1, 2, 2, 1, 1, 3, 2]
def baseStart_7079029 : Nat := 118140960795 + 7079029 * 2 ^ 59
def prefixEnd_7079029 : Nat := 4983230072969 + 3 ^ 40 * 7079029 * 2
def baseEnd_7079029 : Nat := 3634944444116889000181645

theorem tailTrace_7079029 : CollatzResearch.WordTrace tailWord_7079029 prefixEnd_7079029 3634944444116889000181645 := by
  unfold tailWord_7079029
  simp only [CollatzResearch.WordTrace]
  refine ⟨258193399070894409744752141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172128932713929606496501427 258193399070894409744752141)
  ·
    refine ⟨96822524651585403654282053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 258193399070894409744752141 96822524651585403654282053)
    ·
      refine ⟨18154223372172263185177885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96822524651585403654282053 18154223372172263185177885)
      ·
        refine ⟨6807833764564598694441707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18154223372172263185177885 6807833764564598694441707)
        ·
          refine ⟨10211750646846898041662561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6807833764564598694441707 10211750646846898041662561)
          ·
            refine ⟨7658812985135173531246921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10211750646846898041662561 7658812985135173531246921)
            ·
              refine ⟨5744109738851380148435191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7658812985135173531246921 5744109738851380148435191)
              ·
                refine ⟨8616164608277070222652787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5744109738851380148435191 8616164608277070222652787)
                ·
                  refine ⟨12924246912415605333979181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8616164608277070222652787 12924246912415605333979181)
                  ·
                    refine ⟨4846592592155852000242193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12924246912415605333979181 4846592592155852000242193)
                    ·
                      refine ⟨3634944444116889000181645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4846592592155852000242193 3634944444116889000181645)
                      ·
                        rfl

theorem cell23_7079029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_7079029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7079029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7079029 prefixEnd_7079029 := by exact prefixLift 7079029
  have htrace : WordTrace (prefixWord ++ tailWord_7079029) baseStart_7079029 baseEnd_7079029 := by
    simpa [prefixWord, tailWord_7079029, baseEnd_7079029] using wordTrace_append hprefix tailTrace_7079029
  have hstable : (prefixWord ++ tailWord_7079029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7079029).length < 2 ^ (prefixWord ++ tailWord_7079029).sum := by decide
  have hdescent : baseEnd_7079029 < baseStart_7079029 := by decide
  rcases family_descends (prefixWord ++ tailWord_7079029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7079031 : List Nat := [1, 1, 3, 1, 1, 4, 4, 3, 5]
def baseStart_7079031 : Nat := 118140960795 + 7079031 * 2 ^ 59
def prefixEnd_7079031 : Nat := 4983230072969 + 3 ^ 40 * 7079031 * 2
def baseEnd_7079031 : Nat := 403882830119799776928515

theorem tailTrace_7079031 : CollatzResearch.WordTrace tailWord_7079031 prefixEnd_7079031 403882830119799776928515 := by
  unfold tailWord_7079031
  simp only [CollatzResearch.WordTrace]
  refine ⟨258193472016887164086324947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172128981344591442724216631 258193472016887164086324947)
  ·
    refine ⟨387290208025330746129487421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258193472016887164086324947 387290208025330746129487421)
    ·
      refine ⟨145233828009499029798557783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 387290208025330746129487421 145233828009499029798557783)
      ·
        refine ⟨217850742014248544697836675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145233828009499029798557783 217850742014248544697836675)
        ·
          refine ⟨326776113021372817046755013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217850742014248544697836675 326776113021372817046755013)
          ·
            refine ⟨61270521191507403196266565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 326776113021372817046755013 61270521191507403196266565)
            ·
              refine ⟨11488222723407638099299981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61270521191507403196266565 11488222723407638099299981)
              ·
                refine ⟨4308083521277864287237493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11488222723407638099299981 4308083521277864287237493)
                ·
                  refine ⟨403882830119799776928515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4308083521277864287237493 403882830119799776928515)
                  ·
                    rfl

theorem cell23_7079031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 4, 3, 5].length) (baseStart_7079031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7079031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7079031 prefixEnd_7079031 := by exact prefixLift 7079031
  have htrace : WordTrace (prefixWord ++ tailWord_7079031) baseStart_7079031 baseEnd_7079031 := by
    simpa [prefixWord, tailWord_7079031, baseEnd_7079031] using wordTrace_append hprefix tailTrace_7079031
  have hstable : (prefixWord ++ tailWord_7079031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7079031).length < 2 ^ (prefixWord ++ tailWord_7079031).sum := by decide
  have hdescent : baseEnd_7079031 < baseStart_7079031 := by decide
  rcases family_descends (prefixWord ++ tailWord_7079031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7079041 : List Nat := [1, 2, 4, 2, 2, 1, 1, 2, 2, 3, 3]
def baseStart_7079041 : Nat := 118140960795 + 7079041 * 2 ^ 59
def prefixEnd_7079041 : Nat := 4983230072969 + 3 ^ 40 * 7079041 * 2
def baseEnd_7079041 : Nat := 3634950605884742953231589

theorem tailTrace_7079041 : CollatzResearch.WordTrace tailWord_7079041 prefixEnd_7079041 3634950605884742953231589 := by
  unfold tailWord_7079041
  simp only [CollatzResearch.WordTrace]
  refine ⟨258193836746850935794188977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172129224497900623862792651 258193836746850935794188977)
  ·
    refine ⟨193645377560138201845641733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258193836746850935794188977 193645377560138201845641733)
    ·
      refine ⟨36308508292525912846057825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 193645377560138201845641733 36308508292525912846057825)
      ·
        refine ⟨27231381219394434634543369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36308508292525912846057825 27231381219394434634543369)
        ·
          refine ⟨20423535914545825975907527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27231381219394434634543369 20423535914545825975907527)
          ·
            refine ⟨30635303871818738963861291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20423535914545825975907527 30635303871818738963861291)
            ·
              refine ⟨45952955807728108445791937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30635303871818738963861291 45952955807728108445791937)
              ·
                refine ⟨34464716855796081334343953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45952955807728108445791937 34464716855796081334343953)
                ·
                  refine ⟨25848537641847061000757965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34464716855796081334343953 25848537641847061000757965)
                  ·
                    refine ⟨9693201615692647875284237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25848537641847061000757965 9693201615692647875284237)
                    ·
                      refine ⟨3634950605884742953231589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9693201615692647875284237 3634950605884742953231589)
                      ·
                        rfl

theorem cell23_7079041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 2, 2, 3, 3].length) (baseStart_7079041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7079041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7079041 prefixEnd_7079041 := by exact prefixLift 7079041
  have htrace : WordTrace (prefixWord ++ tailWord_7079041) baseStart_7079041 baseEnd_7079041 := by
    simpa [prefixWord, tailWord_7079041, baseEnd_7079041] using wordTrace_append hprefix tailTrace_7079041
  have hstable : (prefixWord ++ tailWord_7079041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7079041).length < 2 ^ (prefixWord ++ tailWord_7079041).sum := by decide
  have hdescent : baseEnd_7079041 < baseStart_7079041 := by decide
  rcases family_descends (prefixWord ++ tailWord_7079041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7079101 : List Nat := [1, 4, 1, 2, 1, 1, 3, 1, 4, 2, 3]
def baseStart_7079101 : Nat := 118140960795 + 7079101 * 2 ^ 59
def prefixEnd_7079101 : Nat := 4983230072969 + 3 ^ 40 * 7079101 * 2
def baseEnd_7079101 : Nat := 3634981414724012718481313

theorem tailTrace_7079101 : CollatzResearch.WordTrace tailWord_7079101 prefixEnd_7079101 3634981414724012718481313 := by
  unfold tailWord_7079101
  simp only [CollatzResearch.WordTrace]
  refine ⟨258196025126633566041373157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172130683417755710694248771 258196025126633566041373157)
  ·
    refine ⟨48411754711243793632757467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 258196025126633566041373157 48411754711243793632757467)
    ·
      refine ⟨72617632066865690449136201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48411754711243793632757467 72617632066865690449136201)
      ·
        refine ⟨54463224050149267836852151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72617632066865690449136201 54463224050149267836852151)
        ·
          refine ⟨81694836075223901755278227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54463224050149267836852151 81694836075223901755278227)
          ·
            refine ⟨122542254112835852632917341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81694836075223901755278227 122542254112835852632917341)
            ·
              refine ⟨45953345292313444737344003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 122542254112835852632917341 45953345292313444737344003)
              ·
                refine ⟨68930017938470167106016005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45953345292313444737344003 68930017938470167106016005)
                ·
                  refine ⟨12924378363463156332378001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68930017938470167106016005 12924378363463156332378001)
                  ·
                    refine ⟨9693283772597367249283501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12924378363463156332378001 9693283772597367249283501)
                    ·
                      refine ⟨3634981414724012718481313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9693283772597367249283501 3634981414724012718481313)
                      ·
                        rfl

theorem cell23_7079101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 1, 4, 2, 3].length) (baseStart_7079101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7079101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7079101 prefixEnd_7079101 := by exact prefixLift 7079101
  have htrace : WordTrace (prefixWord ++ tailWord_7079101) baseStart_7079101 baseEnd_7079101 := by
    simpa [prefixWord, tailWord_7079101, baseEnd_7079101] using wordTrace_append hprefix tailTrace_7079101
  have hstable : (prefixWord ++ tailWord_7079101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7079101).length < 2 ^ (prefixWord ++ tailWord_7079101).sum := by decide
  have hdescent : baseEnd_7079101 < baseStart_7079101 := by decide
  rcases family_descends (prefixWord ++ tailWord_7079101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7079110 : List Nat := [6, 1, 2, 2, 2, 1, 2, 1, 2, 2, 2]
def baseStart_7079110 : Nat := 118140960795 + 7079110 * 2 ^ 59
def prefixEnd_7079110 : Nat := 4983230072969 + 3 ^ 40 * 7079110 * 2
def baseEnd_7079110 : Nat := 3634986036049903183268773

theorem tailTrace_7079110 : CollatzResearch.WordTrace tailWord_7079110 prefixEnd_7079110 3634986036049903183268773 := by
  unfold tailWord_7079110
  simp only [CollatzResearch.WordTrace]
  refine ⟨8068636043237530018076587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 172130902255733973718967189 8068636043237530018076587)
  ·
    refine ⟨12102954064856295027114881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8068636043237530018076587 12102954064856295027114881)
    ·
      refine ⟨9077215548642221270336161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12102954064856295027114881 9077215548642221270336161)
      ·
        refine ⟨6807911661481665952752121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9077215548642221270336161 6807911661481665952752121)
        ·
          refine ⟨5105933746111249464564091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6807911661481665952752121 5105933746111249464564091)
          ·
            refine ⟨7658900619166874196846137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5105933746111249464564091 7658900619166874196846137)
            ·
              refine ⟨5744175464375155647634603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7658900619166874196846137 5744175464375155647634603)
              ·
                refine ⟨8616263196562733471451905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5744175464375155647634603 8616263196562733471451905)
                ·
                  refine ⟨6462197397422050103588929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8616263196562733471451905 6462197397422050103588929)
                  ·
                    refine ⟨4846648048066537577691697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6462197397422050103588929 4846648048066537577691697)
                    ·
                      refine ⟨3634986036049903183268773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4846648048066537577691697 3634986036049903183268773)
                      ·
                        rfl

theorem cell23_7079110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_7079110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7079110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7079110 prefixEnd_7079110 := by exact prefixLift 7079110
  have htrace : WordTrace (prefixWord ++ tailWord_7079110) baseStart_7079110 baseEnd_7079110 := by
    simpa [prefixWord, tailWord_7079110, baseEnd_7079110] using wordTrace_append hprefix tailTrace_7079110
  have hstable : (prefixWord ++ tailWord_7079110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7079110).length < 2 ^ (prefixWord ++ tailWord_7079110).sum := by decide
  have hdescent : baseEnd_7079110 < baseStart_7079110 := by decide
  rcases family_descends (prefixWord ++ tailWord_7079110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7079158 : List Nat := [5, 1, 1, 1, 1, 1, 1, 2, 3, 5, 2]
def baseStart_7079158 : Nat := 118140960795 + 7079158 * 2 ^ 59
def prefixEnd_7079158 : Nat := 4983230072969 + 3 ^ 40 * 7079158 * 2
def baseEnd_7079158 : Nat := 3635010683121318995468551

theorem tailTrace_7079158 : CollatzResearch.WordTrace tailWord_7079158 prefixEnd_7079158 3635010683121318995468551 := by
  unfold tailWord_7079158
  simp only [CollatzResearch.WordTrace]
  refine ⟨16137381505464191548512383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 172132069391618043184132085 16137381505464191548512383)
  ·
    refine ⟨24206072258196287322768575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16137381505464191548512383 24206072258196287322768575)
    ·
      refine ⟨36309108387294430984152863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24206072258196287322768575 36309108387294430984152863)
      ·
        refine ⟨54463662580941646476229295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36309108387294430984152863 54463662580941646476229295)
        ·
          refine ⟨81695493871412469714343943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54463662580941646476229295 81695493871412469714343943)
          ·
            refine ⟨122543240807118704571515915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81695493871412469714343943 122543240807118704571515915)
            ·
              refine ⟨183814861210678056857273873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122543240807118704571515915 183814861210678056857273873)
              ·
                refine ⟨137861145908008542642955405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 183814861210678056857273873 137861145908008542642955405)
                ·
                  refine ⟨51697929715503203491108277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 137861145908008542642955405 51697929715503203491108277)
                  ·
                    refine ⟨4846680910828425327291401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51697929715503203491108277 4846680910828425327291401)
                    ·
                      refine ⟨3635010683121318995468551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4846680910828425327291401 3635010683121318995468551)
                      ·
                        rfl

theorem cell23_7079158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 2, 3, 5, 2].length) (baseStart_7079158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7079158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7079158 prefixEnd_7079158 := by exact prefixLift 7079158
  have htrace : WordTrace (prefixWord ++ tailWord_7079158) baseStart_7079158 baseEnd_7079158 := by
    simpa [prefixWord, tailWord_7079158, baseEnd_7079158] using wordTrace_append hprefix tailTrace_7079158
  have hstable : (prefixWord ++ tailWord_7079158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7079158).length < 2 ^ (prefixWord ++ tailWord_7079158).sum := by decide
  have hdescent : baseEnd_7079158 < baseStart_7079158 := by decide
  rcases family_descends (prefixWord ++ tailWord_7079158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7079171 : List Nat := [1, 1, 1, 3, 2, 4, 1, 2, 3, 1, 4]
def baseStart_7079171 : Nat := 118140960795 + 7079171 * 2 ^ 59
def prefixEnd_7079171 : Nat := 4983230072969 + 3 ^ 40 * 7079171 * 2
def baseEnd_7079171 : Nat := 3635017358369827444605991

theorem tailTrace_7079171 : CollatzResearch.WordTrace tailWord_7079171 prefixEnd_7079171 3635017358369827444605991 := by
  unfold tailWord_7079171
  simp only [CollatzResearch.WordTrace]
  refine ⟨258198578236379967996421367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172132385490919978664280911 258198578236379967996421367)
  ·
    refine ⟨387297867354569951994632051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258198578236379967996421367 387297867354569951994632051)
    ·
      refine ⟨580946801031854927991948077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 387297867354569951994632051 580946801031854927991948077)
      ·
        refine ⟨217855050386945597996980529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 580946801031854927991948077 217855050386945597996980529)
        ·
          refine ⟨163391287790209198497735397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217855050386945597996980529 163391287790209198497735397)
          ·
            refine ⟨30635866460664224718325387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 163391287790209198497735397 30635866460664224718325387)
            ·
              refine ⟨45953799690996337077488081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30635866460664224718325387 45953799690996337077488081)
              ·
                refine ⟨34465349768247252808116061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45953799690996337077488081 34465349768247252808116061)
                ·
                  refine ⟨12924506163092719803043523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34465349768247252808116061 12924506163092719803043523)
                  ·
                    refine ⟨19386759244639079704565285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12924506163092719803043523 19386759244639079704565285)
                    ·
                      refine ⟨3635017358369827444605991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19386759244639079704565285 3635017358369827444605991)
                      ·
                        rfl

theorem cell23_7079171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 2, 3, 1, 4].length) (baseStart_7079171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7079171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7079171 prefixEnd_7079171 := by exact prefixLift 7079171
  have htrace : WordTrace (prefixWord ++ tailWord_7079171) baseStart_7079171 baseEnd_7079171 := by
    simpa [prefixWord, tailWord_7079171, baseEnd_7079171] using wordTrace_append hprefix tailTrace_7079171
  have hstable : (prefixWord ++ tailWord_7079171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7079171).length < 2 ^ (prefixWord ++ tailWord_7079171).sum := by decide
  have hdescent : baseEnd_7079171 < baseStart_7079171 := by decide
  rcases family_descends (prefixWord ++ tailWord_7079171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7079184 : List Nat := [2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 6]
def baseStart_7079184 : Nat := 118140960795 + 7079184 * 2 ^ 59
def prefixEnd_7079184 : Nat := 4983230072969 + 3 ^ 40 * 7079184 * 2
def baseEnd_7079184 : Nat := 3635024033618335893743431

theorem tailTrace_7079184 : CollatzResearch.WordTrace tailWord_7079184 prefixEnd_7079184 3635024033618335893743431 := by
  unfold tailWord_7079184
  simp only [CollatzResearch.WordTrace]
  refine ⟨129099526192666435608322303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172132701590221914144429737 129099526192666435608322303)
  ·
    refine ⟨193649289288999653412483455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129099526192666435608322303 193649289288999653412483455)
    ·
      refine ⟨290473933933499480118725183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193649289288999653412483455 290473933933499480118725183)
      ·
        refine ⟨435710900900249220178087775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290473933933499480118725183 435710900900249220178087775)
        ·
          refine ⟨653566351350373830267131663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 435710900900249220178087775 653566351350373830267131663)
          ·
            refine ⟨980349527025560745400697495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 653566351350373830267131663 980349527025560745400697495)
            ·
              refine ⟨1470524290538341118101046243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 980349527025560745400697495 1470524290538341118101046243)
              ·
                refine ⟨2205786435807511677151569365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1470524290538341118101046243 2205786435807511677151569365)
                ·
                  refine ⟨51698119589238554933239907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2205786435807511677151569365 51698119589238554933239907)
                  ·
                    refine ⟨77547179383857832399859861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51698119589238554933239907 77547179383857832399859861)
                    ·
                      refine ⟨3635024033618335893743431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77547179383857832399859861 3635024033618335893743431)
                      ·
                        rfl

theorem cell23_7079184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 6].length) (baseStart_7079184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7079184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7079184 prefixEnd_7079184 := by exact prefixLift 7079184
  have htrace : WordTrace (prefixWord ++ tailWord_7079184) baseStart_7079184 baseEnd_7079184 := by
    simpa [prefixWord, tailWord_7079184, baseEnd_7079184] using wordTrace_append hprefix tailTrace_7079184
  have hstable : (prefixWord ++ tailWord_7079184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7079184).length < 2 ^ (prefixWord ++ tailWord_7079184).sum := by decide
  have hdescent : baseEnd_7079184 < baseStart_7079184 := by decide
  rcases family_descends (prefixWord ++ tailWord_7079184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7079202 : List Nat := [3, 3, 1, 1, 4, 2, 2, 1, 1, 5]
def baseStart_7079202 : Nat := 118140960795 + 7079202 * 2 ^ 59
def prefixEnd_7079202 : Nat := 4983230072969 + 3 ^ 40 * 7079202 * 2
def baseEnd_7079202 : Nat := 1211677758756705607772783

theorem tailTrace_7079202 : CollatzResearch.WordTrace tailWord_7079202 prefixEnd_7079202 1211677758756705607772783 := by
  unfold tailWord_7079202
  simp only [CollatzResearch.WordTrace]
  refine ⟨64549927224816915072699965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172133139266178440193866573 64549927224816915072699965)
  ·
    refine ⟨24206222709306343152262487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64549927224816915072699965 24206222709306343152262487)
    ·
      refine ⟨36309334063959514728393731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24206222709306343152262487 36309334063959514728393731)
      ·
        refine ⟨54464001095939272092590597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36309334063959514728393731 54464001095939272092590597)
        ·
          refine ⟨10212000205488613517360737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54464001095939272092590597 10212000205488613517360737)
          ·
            refine ⟨7659000154116460138020553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10212000205488613517360737 7659000154116460138020553)
            ·
              refine ⟨5744250115587345103515415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7659000154116460138020553 5744250115587345103515415)
              ·
                refine ⟨8616375173381017655273123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5744250115587345103515415 8616375173381017655273123)
                ·
                  refine ⟨12924562760071526482909685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8616375173381017655273123 12924562760071526482909685)
                  ·
                    refine ⟨1211677758756705607772783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12924562760071526482909685 1211677758756705607772783)
                    ·
                      rfl

theorem cell23_7079202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 2, 1, 1, 5].length) (baseStart_7079202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7079202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7079202 prefixEnd_7079202 := by exact prefixLift 7079202
  have htrace : WordTrace (prefixWord ++ tailWord_7079202) baseStart_7079202 baseEnd_7079202 := by
    simpa [prefixWord, tailWord_7079202, baseEnd_7079202] using wordTrace_append hprefix tailTrace_7079202
  have hstable : (prefixWord ++ tailWord_7079202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7079202).length < 2 ^ (prefixWord ++ tailWord_7079202).sum := by decide
  have hdescent : baseEnd_7079202 < baseStart_7079202 := by decide
  rcases family_descends (prefixWord ++ tailWord_7079202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7079205 : List Nat := [1, 3, 1, 2, 4, 1, 4, 1, 1, 1, 4]
def baseStart_7079205 : Nat := 118140960795 + 7079205 * 2 ^ 59
def prefixEnd_7079205 : Nat := 4983230072969 + 3 ^ 40 * 7079205 * 2
def baseEnd_7079205 : Nat := 3635034816712080311580835

theorem tailTrace_7079205 : CollatzResearch.WordTrace tailWord_7079205 prefixEnd_7079205 3635034816712080311580835 := by
  unfold tailWord_7079205
  simp only [CollatzResearch.WordTrace]
  refine ⟨258199818318256791803159069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172133212212171194535439379 258199818318256791803159069)
  ·
    refine ⟨96824931869346296926184651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 258199818318256791803159069 96824931869346296926184651)
    ·
      refine ⟨145237397804019445389276977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96824931869346296926184651 145237397804019445389276977)
      ·
        refine ⟨108928048353014584041957733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145237397804019445389276977 108928048353014584041957733)
        ·
          refine ⟨20424009066190234507867075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 108928048353014584041957733 20424009066190234507867075)
          ·
            refine ⟨30636013599285351761800613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20424009066190234507867075 30636013599285351761800613)
            ·
              refine ⟨5744252549866003455337615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30636013599285351761800613 5744252549866003455337615)
              ·
                refine ⟨8616378824799005183006423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5744252549866003455337615 8616378824799005183006423)
                ·
                  refine ⟨12924568237198507774509635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8616378824799005183006423 12924568237198507774509635)
                  ·
                    refine ⟨19386852355797761661764453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12924568237198507774509635 19386852355797761661764453)
                    ·
                      refine ⟨3635034816712080311580835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19386852355797761661764453 3635034816712080311580835)
                      ·
                        rfl

theorem cell23_7079205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 4, 1, 1, 1, 4].length) (baseStart_7079205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7079205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7079205 prefixEnd_7079205 := by exact prefixLift 7079205
  have htrace : WordTrace (prefixWord ++ tailWord_7079205) baseStart_7079205 baseEnd_7079205 := by
    simpa [prefixWord, tailWord_7079205, baseEnd_7079205] using wordTrace_append hprefix tailTrace_7079205
  have hstable : (prefixWord ++ tailWord_7079205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7079205).length < 2 ^ (prefixWord ++ tailWord_7079205).sum := by decide
  have hdescent : baseEnd_7079205 < baseStart_7079205 := by decide
  rcases family_descends (prefixWord ++ tailWord_7079205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7079245 : List Nat := [1, 6, 1, 3, 1, 1, 1, 9]
def baseStart_7079245 : Nat := 118140960795 + 7079245 * 2 ^ 59
def prefixEnd_7079245 : Nat := 4983230072969 + 3 ^ 40 * 7079245 * 2
def baseEnd_7079245 : Nat := 134631679849565190928913

theorem tailTrace_7079245 : CollatzResearch.WordTrace tailWord_7079245 prefixEnd_7079245 134631679849565190928913 := by
  unfold tailWord_7079245
  simp only [CollatzResearch.WordTrace]
  refine ⟨258201277238111878634615189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172134184825407919089743459 258201277238111878634615189)
  ·
    refine ⟨12103184870536494310997587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 258201277238111878634615189 12103184870536494310997587)
    ·
      refine ⟨18154777305804741466496381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12103184870536494310997587 18154777305804741466496381)
      ·
        refine ⟨6808041489676778049936143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18154777305804741466496381 6808041489676778049936143)
        ·
          refine ⟨10212062234515167074904215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6808041489676778049936143 10212062234515167074904215)
          ·
            refine ⟨15318093351772750612356323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10212062234515167074904215 15318093351772750612356323)
            ·
              refine ⟨22977140027659125918534485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15318093351772750612356323 22977140027659125918534485)
              ·
                refine ⟨134631679849565190928913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22977140027659125918534485 134631679849565190928913)
                ·
                  rfl

theorem cell23_7079245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 9].length) (baseStart_7079245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7079245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7079245 prefixEnd_7079245 := by exact prefixLift 7079245
  have htrace : WordTrace (prefixWord ++ tailWord_7079245) baseStart_7079245 baseEnd_7079245 := by
    simpa [prefixWord, tailWord_7079245, baseEnd_7079245] using wordTrace_append hprefix tailTrace_7079245
  have hstable : (prefixWord ++ tailWord_7079245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7079245).length < 2 ^ (prefixWord ++ tailWord_7079245).sum := by decide
  have hdescent : baseEnd_7079245 < baseStart_7079245 := by decide
  rcases family_descends (prefixWord ++ tailWord_7079245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7079291 : List Nat := [1, 1, 1, 1, 1, 6, 2, 1, 1, 4, 4]
def baseStart_7079291 : Nat := 118140960795 + 7079291 * 2 ^ 59
def prefixEnd_7079291 : Nat := 4983230072969 + 3 ^ 40 * 7079291 * 2
def baseEnd_7079291 : Nat := 3635078976048366975105439

theorem tailTrace_7079291 : CollatzResearch.WordTrace tailWord_7079291 prefixEnd_7079291 3635078976048366975105439 := by
  unfold tailWord_7079291
  simp only [CollatzResearch.WordTrace]
  refine ⟨258202954995945228490789727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172135303330630152327193151 258202954995945228490789727)
  ·
    refine ⟨387304432493917842736184591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258202954995945228490789727 387304432493917842736184591)
    ·
      refine ⟨580956648740876764104276887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 387304432493917842736184591 580956648740876764104276887)
      ·
        refine ⟨871434973111315146156415331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 580956648740876764104276887 871434973111315146156415331)
        ·
          refine ⟨1307152459666972719234622997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 871434973111315146156415331 1307152459666972719234622997)
          ·
            refine ⟨61272771546889346214122953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1307152459666972719234622997 61272771546889346214122953)
            ·
              refine ⟨45954578660167009660592215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61272771546889346214122953 45954578660167009660592215)
              ·
                refine ⟨68931867990250514490888323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45954578660167009660592215 68931867990250514490888323)
                ·
                  refine ⟨103397801985375771736332485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68931867990250514490888323 103397801985375771736332485)
                  ·
                    refine ⟨19387087872257957200562341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 103397801985375771736332485 19387087872257957200562341)
                    ·
                      refine ⟨3635078976048366975105439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19387087872257957200562341 3635078976048366975105439)
                      ·
                        rfl

theorem cell23_7079291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 1, 1, 4, 4].length) (baseStart_7079291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7079291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7079291 prefixEnd_7079291 := by exact prefixLift 7079291
  have htrace : WordTrace (prefixWord ++ tailWord_7079291) baseStart_7079291 baseEnd_7079291 := by
    simpa [prefixWord, tailWord_7079291, baseEnd_7079291] using wordTrace_append hprefix tailTrace_7079291
  have hstable : (prefixWord ++ tailWord_7079291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7079291).length < 2 ^ (prefixWord ++ tailWord_7079291).sum := by decide
  have hdescent : baseEnd_7079291 < baseStart_7079291 := by decide
  rcases family_descends (prefixWord ++ tailWord_7079291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7079301 : List Nat := [1, 3, 1, 1, 3, 1, 2, 4, 7]
def baseStart_7079301 : Nat := 118140960795 + 7079301 * 2 ^ 59
def prefixEnd_7079301 : Nat := 4983230072969 + 3 ^ 40 * 7079301 * 2
def baseEnd_7079301 : Nat := 403898234539434659553377

theorem tailTrace_7079301 : CollatzResearch.WordTrace tailWord_7079301 prefixEnd_7079301 403898234539434659553377 := by
  unfold tailWord_7079301
  simp only [CollatzResearch.WordTrace]
  refine ⟨258203319725909000198653757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172135546483939333465769171 258203319725909000198653757)
  ·
    refine ⟨96826244897215875074495159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 258203319725909000198653757 96826244897215875074495159)
    ·
      refine ⟨145239367345823812611742739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96826244897215875074495159 145239367345823812611742739)
      ·
        refine ⟨217859051018735718917614109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145239367345823812611742739 217859051018735718917614109)
        ·
          refine ⟨81697144132025894594105291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 217859051018735718917614109 81697144132025894594105291)
          ·
            refine ⟨122545716198038841891157937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81697144132025894594105291 122545716198038841891157937)
            ·
              refine ⟨91909287148529131418368453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122545716198038841891157937 91909287148529131418368453)
              ·
                refine ⟨17232991340349212140944085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 91909287148529131418368453 17232991340349212140944085)
                ·
                  refine ⟨403898234539434659553377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17232991340349212140944085 403898234539434659553377)
                  ·
                    rfl

theorem cell23_7079301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 4, 7].length) (baseStart_7079301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7079301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7079301 prefixEnd_7079301 := by exact prefixLift 7079301
  have htrace : WordTrace (prefixWord ++ tailWord_7079301) baseStart_7079301 baseEnd_7079301 := by
    simpa [prefixWord, tailWord_7079301, baseEnd_7079301] using wordTrace_append hprefix tailTrace_7079301
  have hstable : (prefixWord ++ tailWord_7079301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7079301).length < 2 ^ (prefixWord ++ tailWord_7079301).sum := by decide
  have hdescent : baseEnd_7079301 < baseStart_7079301 := by decide
  rcases family_descends (prefixWord ++ tailWord_7079301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7079328 : List Nat := [2, 1, 1, 4, 1, 2, 2, 2, 2, 3, 3]
def baseStart_7079328 : Nat := 118140960795 + 7079328 * 2 ^ 59
def prefixEnd_7079328 : Nat := 4983230072969 + 3 ^ 40 * 7079328 * 2
def baseEnd_7079328 : Nat := 3635097974832583330342769

theorem tailTrace_7079328 : CollatzResearch.WordTrace tailWord_7079328 prefixEnd_7079328 3635097974832583330342769 := by
  unfold tailWord_7079328
  simp only [CollatzResearch.WordTrace]
  refine ⟨129102152248405591904943319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172136202997874122539924425 129102152248405591904943319)
  ·
    refine ⟨193653228372608387857414979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129102152248405591904943319 193653228372608387857414979)
    ·
      refine ⟨290479842558912581786122469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193653228372608387857414979 290479842558912581786122469)
      ·
        refine ⟨54464970479796109084897963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 290479842558912581786122469 54464970479796109084897963)
        ·
          refine ⟨81697455719694163627346945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54464970479796109084897963 81697455719694163627346945)
          ·
            refine ⟨61273091789770622720510209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81697455719694163627346945 61273091789770622720510209)
            ·
              refine ⟨45954818842327967040382657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61273091789770622720510209 45954818842327967040382657)
              ·
                refine ⟨34466114131745975280286993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45954818842327967040382657 34466114131745975280286993)
                ·
                  refine ⟨25849585598809481460215245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34466114131745975280286993 25849585598809481460215245)
                  ·
                    refine ⟨9693594599553555547580717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25849585598809481460215245 9693594599553555547580717)
                    ·
                      refine ⟨3635097974832583330342769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9693594599553555547580717 3635097974832583330342769)
                      ·
                        rfl

theorem cell23_7079328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 2, 2, 3, 3].length) (baseStart_7079328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7079328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7079328 prefixEnd_7079328 := by exact prefixLift 7079328
  have htrace : WordTrace (prefixWord ++ tailWord_7079328) baseStart_7079328 baseEnd_7079328 := by
    simpa [prefixWord, tailWord_7079328, baseEnd_7079328] using wordTrace_append hprefix tailTrace_7079328
  have hstable : (prefixWord ++ tailWord_7079328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7079328).length < 2 ^ (prefixWord ++ tailWord_7079328).sum := by decide
  have hdescent : baseEnd_7079328 < baseStart_7079328 := by decide
  rcases family_descends (prefixWord ++ tailWord_7079328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7079335 : List Nat := [1, 1, 6, 1, 1, 1, 3, 4, 5]
def baseStart_7079335 : Nat := 118140960795 + 7079335 * 2 ^ 59
def prefixEnd_7079335 : Nat := 4983230072969 + 3 ^ 40 * 7079335 * 2
def baseEnd_7079335 : Nat := 403900174355240533661693

theorem tailTrace_7079335 : CollatzResearch.WordTrace tailWord_7079335 prefixEnd_7079335 403900174355240533661693 := by
  unfold tailWord_7079335
  simp only [CollatzResearch.WordTrace]
  refine ⟨258204559807785824005391459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172136373205190549336927639 258204559807785824005391459)
  ·
    refine ⟨387306839711678736008087189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258204559807785824005391459 387306839711678736008087189)
    ·
      refine ⟨18155008111484940750379087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 387306839711678736008087189 18155008111484940750379087)
      ·
        refine ⟨27232512167227411125568631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18155008111484940750379087 27232512167227411125568631)
        ·
          refine ⟨40848768250841116688352947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27232512167227411125568631 40848768250841116688352947)
          ·
            refine ⟨61273152376261675032529421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40848768250841116688352947 61273152376261675032529421)
            ·
              refine ⟨22977432141098128137198533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61273152376261675032529421 22977432141098128137198533)
              ·
                refine ⟨4308268526455899025724725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22977432141098128137198533 4308268526455899025724725)
                ·
                  refine ⟨403900174355240533661693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4308268526455899025724725 403900174355240533661693)
                  ·
                    rfl

theorem cell23_7079335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 4, 5].length) (baseStart_7079335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7079335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7079335 prefixEnd_7079335 := by exact prefixLift 7079335
  have htrace : WordTrace (prefixWord ++ tailWord_7079335) baseStart_7079335 baseEnd_7079335 := by
    simpa [prefixWord, tailWord_7079335, baseEnd_7079335] using wordTrace_append hprefix tailTrace_7079335
  have hstable : (prefixWord ++ tailWord_7079335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7079335).length < 2 ^ (prefixWord ++ tailWord_7079335).sum := by decide
  have hdescent : baseEnd_7079335 < baseStart_7079335 := by decide
  rcases family_descends (prefixWord ++ tailWord_7079335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7079368 : List Nat := [2, 1, 3, 1, 3, 1, 3, 1, 1, 3, 4]
def baseStart_7079368 : Nat := 118140960795 + 7079368 * 2 ^ 59
def prefixEnd_7079368 : Nat := 4983230072969 + 3 ^ 40 * 7079368 * 2
def baseEnd_7079368 : Nat := 3635118514058763173842585

theorem tailTrace_7079368 : CollatzResearch.WordTrace tailWord_7079368 prefixEnd_7079368 3635118514058763173842585 := by
  unfold tailWord_7079368
  simp only [CollatzResearch.WordTrace]
  refine ⟨129102881708333135320671379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172137175611110847094228505 129102881708333135320671379)
  ·
    refine ⟨193654322562499702981007069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129102881708333135320671379 193654322562499702981007069)
    ·
      refine ⟨72620370960937388617877651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193654322562499702981007069 72620370960937388617877651)
      ·
        refine ⟨108930556441406082926816477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72620370960937388617877651 108930556441406082926816477)
        ·
          refine ⟨40848958665527281097556179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108930556441406082926816477 40848958665527281097556179)
          ·
            refine ⟨61273437998290921646334269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40848958665527281097556179 61273437998290921646334269)
            ·
              refine ⟨22977539249359095617375351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61273437998290921646334269 22977539249359095617375351)
              ·
                refine ⟨34466308874038643426063027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22977539249359095617375351 34466308874038643426063027)
                ·
                  refine ⟨51699463311057965139094541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34466308874038643426063027 51699463311057965139094541)
                  ·
                    refine ⟨19387298741646736927160453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51699463311057965139094541 19387298741646736927160453)
                    ·
                      refine ⟨3635118514058763173842585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19387298741646736927160453 3635118514058763173842585)
                      ·
                        rfl

theorem cell23_7079368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 1, 1, 3, 4].length) (baseStart_7079368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7079368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7079368 prefixEnd_7079368 := by exact prefixLift 7079368
  have htrace : WordTrace (prefixWord ++ tailWord_7079368) baseStart_7079368 baseEnd_7079368 := by
    simpa [prefixWord, tailWord_7079368, baseEnd_7079368] using wordTrace_append hprefix tailTrace_7079368
  have hstable : (prefixWord ++ tailWord_7079368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7079368).length < 2 ^ (prefixWord ++ tailWord_7079368).sum := by decide
  have hdescent : baseEnd_7079368 < baseStart_7079368 := by decide
  rcases family_descends (prefixWord ++ tailWord_7079368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7079385 : List Nat := [1, 2, 1, 2, 4, 2, 1, 2, 2, 4, 2]
def baseStart_7079385 : Nat := 118140960795 + 7079385 * 2 ^ 59
def prefixEnd_7079385 : Nat := 4983230072969 + 3 ^ 40 * 7079385 * 2
def baseEnd_7079385 : Nat := 3635127243229889607330007

theorem tailTrace_7079385 : CollatzResearch.WordTrace tailWord_7079385 prefixEnd_7079385 3635127243229889607330007 := by
  unfold tailWord_7079385
  simp only [CollatzResearch.WordTrace]
  refine ⟨258206383457604682544711609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172137588971736455029807739 258206383457604682544711609)
  ·
    refine ⟨193654787593203511908533707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258206383457604682544711609 193654787593203511908533707)
    ·
      refine ⟨290482181389805267862800561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193654787593203511908533707 290482181389805267862800561)
      ·
        refine ⟨217861636042353950897100421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 290482181389805267862800561 217861636042353950897100421)
        ·
          refine ⟨40849056757941365793206329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 217861636042353950897100421 40849056757941365793206329)
          ·
            refine ⟨30636792568456024344904747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40849056757941365793206329 30636792568456024344904747)
            ·
              refine ⟨45955188852684036517357121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30636792568456024344904747 45955188852684036517357121)
              ·
                refine ⟨34466391639513027388017841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45955188852684036517357121 34466391639513027388017841)
                ·
                  refine ⟨25849793729634770541013381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34466391639513027388017841 25849793729634770541013381)
                  ·
                    refine ⟨4846836324306519476440009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25849793729634770541013381 4846836324306519476440009)
                    ·
                      refine ⟨3635127243229889607330007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4846836324306519476440009 3635127243229889607330007)
                      ·
                        rfl

theorem cell23_7079385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 2, 2, 4, 2].length) (baseStart_7079385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7079385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7079385 prefixEnd_7079385 := by exact prefixLift 7079385
  have htrace : WordTrace (prefixWord ++ tailWord_7079385) baseStart_7079385 baseEnd_7079385 := by
    simpa [prefixWord, tailWord_7079385, baseEnd_7079385] using wordTrace_append hprefix tailTrace_7079385
  have hstable : (prefixWord ++ tailWord_7079385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7079385).length < 2 ^ (prefixWord ++ tailWord_7079385).sum := by decide
  have hdescent : baseEnd_7079385 < baseStart_7079385 := by decide
  rcases family_descends (prefixWord ++ tailWord_7079385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7079395 : List Nat := [1, 1, 1, 6, 2, 1, 1, 3, 3, 4]
def baseStart_7079395 : Nat := 118140960795 + 7079395 * 2 ^ 59
def prefixEnd_7079395 : Nat := 4983230072969 + 3 ^ 40 * 7079395 * 2
def baseEnd_7079395 : Nat := 1211710792678811522734987

theorem tailTrace_7079395 : CollatzResearch.WordTrace tailWord_7079395 prefixEnd_7079395 1211710792678811522734987 := by
  unfold tailWord_7079395
  simp only [CollatzResearch.WordTrace]
  refine ⟨258206748187568454252575639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172137832125045636168383759 258206748187568454252575639)
  ·
    refine ⟨387310122281352681378863459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258206748187568454252575639 387310122281352681378863459)
    ·
      refine ⟨580965183422029022068295189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 387310122281352681378863459 580965183422029022068295189)
      ·
        refine ⟨27232742972907610409451337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 580965183422029022068295189 27232742972907610409451337)
        ·
          refine ⟨20424557229680707807088503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27232742972907610409451337 20424557229680707807088503)
          ·
            refine ⟨30636835844521061710632755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20424557229680707807088503 30636835844521061710632755)
            ·
              refine ⟨45955253766781592565949133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30636835844521061710632755 45955253766781592565949133)
              ·
                refine ⟨17233220162543097212230925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45955253766781592565949133 17233220162543097212230925)
                ·
                  refine ⟨6462457560953661454586597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17233220162543097212230925 6462457560953661454586597)
                  ·
                    refine ⟨1211710792678811522734987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6462457560953661454586597 1211710792678811522734987)
                    ·
                      rfl

theorem cell23_7079395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 3, 3, 4].length) (baseStart_7079395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7079395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7079395 prefixEnd_7079395 := by exact prefixLift 7079395
  have htrace : WordTrace (prefixWord ++ tailWord_7079395) baseStart_7079395 baseEnd_7079395 := by
    simpa [prefixWord, tailWord_7079395, baseEnd_7079395] using wordTrace_append hprefix tailTrace_7079395
  have hstable : (prefixWord ++ tailWord_7079395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7079395).length < 2 ^ (prefixWord ++ tailWord_7079395).sum := by decide
  have hdescent : baseEnd_7079395 < baseStart_7079395 := by decide
  rcases family_descends (prefixWord ++ tailWord_7079395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7079401 : List Nat := [1, 2, 1, 1, 1, 2, 1, 2, 2, 1, 9]
def baseStart_7079401 : Nat := 118140960795 + 7079401 * 2 ^ 59
def prefixEnd_7079401 : Nat := 4983230072969 + 3 ^ 40 * 7079401 * 2
def baseEnd_7079401 : Nat := 3635135458920361544729933

theorem tailTrace_7079401 : CollatzResearch.WordTrace tailWord_7079401 prefixEnd_7079401 3635135458920361544729933 := by
  unfold tailWord_7079401
  simp only [CollatzResearch.WordTrace]
  refine ⟨258206967025546717277294057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172137978017031144851529371 258206967025546717277294057)
  ·
    refine ⟨193655225269160037957970543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258206967025546717277294057 193655225269160037957970543)
    ·
      refine ⟨290482837903740056936955815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193655225269160037957970543 290482837903740056936955815)
      ·
        refine ⟨435724256855610085405433723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290482837903740056936955815 435724256855610085405433723)
        ·
          refine ⟨653586385283415128108150585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 435724256855610085405433723 653586385283415128108150585)
          ·
            refine ⟨490189788962561346081112939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 653586385283415128108150585 490189788962561346081112939)
            ·
              refine ⟨735284683443842019121669409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 490189788962561346081112939 735284683443842019121669409)
              ·
                refine ⟨551463512582881514341252057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 735284683443842019121669409 551463512582881514341252057)
                ·
                  refine ⟨413597634437161135755939043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 551463512582881514341252057 413597634437161135755939043)
                  ·
                    refine ⟨620396451655741703633908565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 413597634437161135755939043 620396451655741703633908565)
                    ·
                      refine ⟨3635135458920361544729933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 620396451655741703633908565 3635135458920361544729933)
                      ·
                        rfl

theorem cell23_7079401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 1, 9].length) (baseStart_7079401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7079401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7079401 prefixEnd_7079401 := by exact prefixLift 7079401
  have htrace : WordTrace (prefixWord ++ tailWord_7079401) baseStart_7079401 baseEnd_7079401 := by
    simpa [prefixWord, tailWord_7079401, baseEnd_7079401] using wordTrace_append hprefix tailTrace_7079401
  have hstable : (prefixWord ++ tailWord_7079401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7079401).length < 2 ^ (prefixWord ++ tailWord_7079401).sum := by decide
  have hdescent : baseEnd_7079401 < baseStart_7079401 := by decide
  rcases family_descends (prefixWord ++ tailWord_7079401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7079418 : List Nat := [3, 1, 1, 1, 1, 2, 3, 1, 2, 5, 3]
def baseStart_7079418 : Nat := 118140960795 + 7079418 * 2 ^ 59
def prefixEnd_7079418 : Nat := 4983230072969 + 3 ^ 40 * 7079418 * 2
def baseEnd_7079418 : Nat := 3635144188091487978217355

theorem tailTrace_7079418 : CollatzResearch.WordTrace tailWord_7079418 prefixEnd_7079418 3635144188091487978217355 := by
  unfold tailWord_7079418
  simp only [CollatzResearch.WordTrace]
  refine ⟨64551896766621282295165727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172138391377656752787108605 64551896766621282295165727)
  ·
    refine ⟨96827845149931923442748591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64551896766621282295165727 96827845149931923442748591)
    ·
      refine ⟨145241767724897885164122887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96827845149931923442748591 145241767724897885164122887)
      ·
        refine ⟨217862651587346827746184331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145241767724897885164122887 217862651587346827746184331)
        ·
          refine ⟨326793977381020241619276497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217862651587346827746184331 326793977381020241619276497)
          ·
            refine ⟨245095483035765181214457373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 326793977381020241619276497 245095483035765181214457373)
            ·
              refine ⟨91910806138411942955421515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 245095483035765181214457373 91910806138411942955421515)
              ·
                refine ⟨137866209207617914433132273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91910806138411942955421515 137866209207617914433132273)
                ·
                  refine ⟨103399656905713435824849205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 137866209207617914433132273 103399656905713435824849205)
                  ·
                    refine ⟨9693717834910634608579613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 103399656905713435824849205 9693717834910634608579613)
                    ·
                      refine ⟨3635144188091487978217355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9693717834910634608579613 3635144188091487978217355)
                      ·
                        rfl

theorem cell23_7079418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 1, 2, 5, 3].length) (baseStart_7079418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7079418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7079418 prefixEnd_7079418 := by exact prefixLift 7079418
  have htrace : WordTrace (prefixWord ++ tailWord_7079418) baseStart_7079418 baseEnd_7079418 := by
    simpa [prefixWord, tailWord_7079418, baseEnd_7079418] using wordTrace_append hprefix tailTrace_7079418
  have hstable : (prefixWord ++ tailWord_7079418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7079418).length < 2 ^ (prefixWord ++ tailWord_7079418).sum := by decide
  have hdescent : baseEnd_7079418 < baseStart_7079418 := by decide
  rcases family_descends (prefixWord ++ tailWord_7079418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7079459 : List Nat := [1, 1, 1, 4, 6, 1, 2, 1, 6]
def baseStart_7079459 : Nat := 118140960795 + 7079459 * 2 ^ 59
def prefixEnd_7079459 : Nat := 4983230072969 + 3 ^ 40 * 7079459 * 2
def baseEnd_7079459 : Nat := 403907248977591368644963

theorem tailTrace_7079459 : CollatzResearch.WordTrace tailWord_7079459 prefixEnd_7079459 403907248977591368644963 := by
  unfold tailWord_7079459
  simp only [CollatzResearch.WordTrace]
  refine ⟨258209082459336593182905431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172139388306224395455270287 258209082459336593182905431)
  ·
    refine ⟨387313623689004889774358147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258209082459336593182905431 387313623689004889774358147)
    ·
      refine ⟨580970435533507334661537221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 387313623689004889774358147 580970435533507334661537221)
      ·
        refine ⟨108931956662532625249038229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 580970435533507334661537221 108931956662532625249038229)
        ·
          refine ⟨5106185468556216808548667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 108931956662532625249038229 5106185468556216808548667)
          ·
            refine ⟨7659278202834325212823001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5106185468556216808548667 7659278202834325212823001)
            ·
              refine ⟨5744458652125743909617251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7659278202834325212823001 5744458652125743909617251)
              ·
                refine ⟨8616687978188615864425877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5744458652125743909617251 8616687978188615864425877)
                ·
                  refine ⟨403907248977591368644963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8616687978188615864425877 403907248977591368644963)
                  ·
                    rfl

theorem cell23_7079459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 2, 1, 6].length) (baseStart_7079459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7079459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7079459 prefixEnd_7079459 := by exact prefixLift 7079459
  have htrace : WordTrace (prefixWord ++ tailWord_7079459) baseStart_7079459 baseEnd_7079459 := by
    simpa [prefixWord, tailWord_7079459, baseEnd_7079459] using wordTrace_append hprefix tailTrace_7079459
  have hstable : (prefixWord ++ tailWord_7079459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7079459).length < 2 ^ (prefixWord ++ tailWord_7079459).sum := by decide
  have hdescent : baseEnd_7079459 < baseStart_7079459 := by decide
  rcases family_descends (prefixWord ++ tailWord_7079459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7079475 : List Nat := [1, 1, 1, 2, 4, 4, 1, 1, 3, 1, 4]
def baseStart_7079475 : Nat := 118140960795 + 7079475 * 2 ^ 59
def prefixEnd_7079475 : Nat := 4983230072969 + 3 ^ 40 * 7079475 * 2
def baseEnd_7079475 : Nat := 3635173456488794255204593

theorem tailTrace_7079475 : CollatzResearch.WordTrace tailWord_7079475 prefixEnd_7079475 3635173456488794255204593 := by
  unfold tailWord_7079475
  simp only [CollatzResearch.WordTrace]
  refine ⟨258209666027278627915487879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172139777351519085276991919 258209666027278627915487879)
  ·
    refine ⟨387314499040917941873231819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258209666027278627915487879 387314499040917941873231819)
    ·
      refine ⟨580971748561376912809847729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 387314499040917941873231819 580971748561376912809847729)
      ·
        refine ⟨435728811421032684607385797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 580971748561376912809847729 435728811421032684607385797)
        ·
          refine ⟨81699152141443628363884837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 435728811421032684607385797 81699152141443628363884837)
          ·
            refine ⟨15318591026520680318228407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81699152141443628363884837 15318591026520680318228407)
            ·
              refine ⟨22977886539781020477342611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15318591026520680318228407 22977886539781020477342611)
              ·
                refine ⟨34466829809671530716013917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22977886539781020477342611 34466829809671530716013917)
                ·
                  refine ⟨12925061178626824018505219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34466829809671530716013917 12925061178626824018505219)
                  ·
                    refine ⟨19387591767940236027757829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12925061178626824018505219 19387591767940236027757829)
                    ·
                      refine ⟨3635173456488794255204593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19387591767940236027757829 3635173456488794255204593)
                      ·
                        rfl

theorem cell23_7079475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 1, 3, 1, 4].length) (baseStart_7079475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7079475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7079475 prefixEnd_7079475 := by exact prefixLift 7079475
  have htrace : WordTrace (prefixWord ++ tailWord_7079475) baseStart_7079475 baseEnd_7079475 := by
    simpa [prefixWord, tailWord_7079475, baseEnd_7079475] using wordTrace_append hprefix tailTrace_7079475
  have hstable : (prefixWord ++ tailWord_7079475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7079475).length < 2 ^ (prefixWord ++ tailWord_7079475).sum := by decide
  have hdescent : baseEnd_7079475 < baseStart_7079475 := by decide
  rcases family_descends (prefixWord ++ tailWord_7079475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7079559 : List Nat := [1, 1, 4, 2, 1, 3, 3, 2, 2, 1, 3]
def baseStart_7079559 : Nat := 118140960795 + 7079559 * 2 ^ 59
def prefixEnd_7079559 : Nat := 4983230072969 + 3 ^ 40 * 7079559 * 2
def baseEnd_7079559 : Nat := 3635216588863771926554207

theorem tailTrace_7079559 : CollatzResearch.WordTrace tailWord_7079559 prefixEnd_7079559 3635216588863771926554207 := by
  unfold tailWord_7079559
  simp only [CollatzResearch.WordTrace]
  refine ⟨258212729758974310261545731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172141819839316206841030487 258212729758974310261545731)
  ·
    refine ⟨387319094638461465392318597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258212729758974310261545731 387319094638461465392318597)
    ·
      refine ⟨72622330244711524761059737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 387319094638461465392318597 72622330244711524761059737)
      ·
        refine ⟨54466747683533643570794803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72622330244711524761059737 54466747683533643570794803)
        ·
          refine ⟨81700121525300465356192205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54466747683533643570794803 81700121525300465356192205)
          ·
            refine ⟨30637545571987674508572077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81700121525300465356192205 30637545571987674508572077)
            ·
              refine ⟨11489079589495377940714529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30637545571987674508572077 11489079589495377940714529)
              ·
                refine ⟨8616809692121533455535897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11489079589495377940714529 8616809692121533455535897)
                ·
                  refine ⟨6462607269091150091651923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8616809692121533455535897 6462607269091150091651923)
                  ·
                    refine ⟨9693910903636725137477885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6462607269091150091651923 9693910903636725137477885)
                    ·
                      refine ⟨3635216588863771926554207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9693910903636725137477885 3635216588863771926554207)
                      ·
                        rfl

theorem cell23_7079559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 3, 2, 2, 1, 3].length) (baseStart_7079559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7079559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7079559 prefixEnd_7079559 := by exact prefixLift 7079559
  have htrace : WordTrace (prefixWord ++ tailWord_7079559) baseStart_7079559 baseEnd_7079559 := by
    simpa [prefixWord, tailWord_7079559, baseEnd_7079559] using wordTrace_append hprefix tailTrace_7079559
  have hstable : (prefixWord ++ tailWord_7079559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7079559).length < 2 ^ (prefixWord ++ tailWord_7079559).sum := by decide
  have hdescent : baseEnd_7079559 < baseStart_7079559 := by decide
  rcases family_descends (prefixWord ++ tailWord_7079559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7079575 : List Nat := [1, 1, 3, 3, 2, 2, 2, 1, 2, 6]
def baseStart_7079575 : Nat := 118140960795 + 7079575 * 2 ^ 59
def prefixEnd_7079575 : Nat := 4983230072969 + 3 ^ 40 * 7079575 * 2
def baseEnd_7079575 : Nat := 1211741601518081287984711

theorem tailTrace_7079575 : CollatzResearch.WordTrace tailWord_7079575 prefixEnd_7079575 1211741601518081287984711 := by
  unfold tailWord_7079575
  simp only [CollatzResearch.WordTrace]
  refine ⟨258213313326916344994128179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172142208884610896662752119 258213313326916344994128179)
  ·
    refine ⟨387319969990374517491192269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258213313326916344994128179 387319969990374517491192269)
    ·
      refine ⟨145244988746390444059197101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 387319969990374517491192269 145244988746390444059197101)
      ·
        refine ⟨54466870779896416522198913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145244988746390444059197101 54466870779896416522198913)
        ·
          refine ⟨40850153084922312391649185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54466870779896416522198913 40850153084922312391649185)
          ·
            refine ⟨30637614813691734293736889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40850153084922312391649185 30637614813691734293736889)
            ·
              refine ⟨22978211110268800720302667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30637614813691734293736889 22978211110268800720302667)
              ·
                refine ⟨34467316665403201080454001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22978211110268800720302667 34467316665403201080454001)
                ·
                  refine ⟨25850487499052400810340501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34467316665403201080454001 25850487499052400810340501)
                  ·
                    refine ⟨1211741601518081287984711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25850487499052400810340501 1211741601518081287984711)
                    ·
                      rfl

theorem cell23_7079575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 1, 2, 6].length) (baseStart_7079575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7079575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7079575 prefixEnd_7079575 := by exact prefixLift 7079575
  have htrace : WordTrace (prefixWord ++ tailWord_7079575) baseStart_7079575 baseEnd_7079575 := by
    simpa [prefixWord, tailWord_7079575, baseEnd_7079575] using wordTrace_append hprefix tailTrace_7079575
  have hstable : (prefixWord ++ tailWord_7079575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7079575).length < 2 ^ (prefixWord ++ tailWord_7079575).sum := by decide
  have hdescent : baseEnd_7079575 < baseStart_7079575 := by decide
  rcases family_descends (prefixWord ++ tailWord_7079575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7079576 : List Nat := [2, 1, 2, 4, 1, 3, 3, 1, 2, 1, 3]
def baseStart_7079576 : Nat := 118140960795 + 7079576 * 2 ^ 59
def prefixEnd_7079576 : Nat := 4983230072969 + 3 ^ 40 * 7079576 * 2
def baseEnd_7079576 : Nat := 3635225318034898360041629

theorem tailTrace_7079576 : CollatzResearch.WordTrace tailWord_7079576 prefixEnd_7079576 3635225318034898360041629 := by
  unfold tailWord_7079576
  simp only [CollatzResearch.WordTrace]
  refine ⟨129106674899956361082457291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172142233199941814776609721 129106674899956361082457291)
  ·
    refine ⟨193660012349934541623685937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129106674899956361082457291 193660012349934541623685937)
    ·
      refine ⟨145245009262450906217764453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193660012349934541623685937 145245009262450906217764453)
      ·
        refine ⟨27233439236709544915830835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 145245009262450906217764453 27233439236709544915830835)
        ·
          refine ⟨40850158855064317373746253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27233439236709544915830835 40850158855064317373746253)
          ·
            refine ⟨15318809570649119015154845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40850158855064317373746253 15318809570649119015154845)
            ·
              refine ⟨5744553588993419630683067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15318809570649119015154845 5744553588993419630683067)
              ·
                refine ⟨8616830383490129446024601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5744553588993419630683067 8616830383490129446024601)
                ·
                  refine ⟨6462622787617597084518451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8616830383490129446024601 6462622787617597084518451)
                  ·
                    refine ⟨9693934181426395626777677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6462622787617597084518451 9693934181426395626777677)
                    ·
                      refine ⟨3635225318034898360041629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9693934181426395626777677 3635225318034898360041629)
                      ·
                        rfl

theorem cell23_7079576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 3, 1, 2, 1, 3].length) (baseStart_7079576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7079576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7079576 prefixEnd_7079576 := by exact prefixLift 7079576
  have htrace : WordTrace (prefixWord ++ tailWord_7079576) baseStart_7079576 baseEnd_7079576 := by
    simpa [prefixWord, tailWord_7079576, baseEnd_7079576] using wordTrace_append hprefix tailTrace_7079576
  have hstable : (prefixWord ++ tailWord_7079576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7079576).length < 2 ^ (prefixWord ++ tailWord_7079576).sum := by decide
  have hdescent : baseEnd_7079576 < baseStart_7079576 := by decide
  rcases family_descends (prefixWord ++ tailWord_7079576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7079633 : List Nat := [1, 2, 2, 1, 2, 6, 2, 1, 2, 2, 2]
def baseStart_7079633 : Nat := 118140960795 + 7079633 * 2 ^ 59
def prefixEnd_7079633 : Nat := 4983230072969 + 3 ^ 40 * 7079633 * 2
def baseEnd_7079633 : Nat := 3635254586432204637028867

theorem tailTrace_7079633 : CollatzResearch.WordTrace tailWord_7079633 prefixEnd_7079633 3635254586432204637028867 := by
  unfold tailWord_7079633
  simp only [CollatzResearch.WordTrace]
  refine ⟨258215428760706220899739553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172143619173804147266493035 258215428760706220899739553)
  ·
    refine ⟨193661571570529665674804665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258215428760706220899739553 193661571570529665674804665)
    ·
      refine ⟨145246178677897249256103499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193661571570529665674804665 145246178677897249256103499)
      ·
        refine ⟨217869268016845873884155249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145246178677897249256103499 217869268016845873884155249)
        ·
          refine ⟨163401951012634405413116437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217869268016845873884155249 163401951012634405413116437)
          ·
            refine ⟨7659466453717237753739833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 163401951012634405413116437 7659466453717237753739833)
            ·
              refine ⟨5744599840287928315304875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7659466453717237753739833 5744599840287928315304875)
              ·
                refine ⟨8616899760431892472957313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5744599840287928315304875 8616899760431892472957313)
                ·
                  refine ⟨6462674820323919354717985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8616899760431892472957313 6462674820323919354717985)
                  ·
                    refine ⟨4847006115242939516038489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6462674820323919354717985 4847006115242939516038489)
                    ·
                      refine ⟨3635254586432204637028867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4847006115242939516038489 3635254586432204637028867)
                      ·
                        rfl

theorem cell23_7079633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 2, 1, 2, 2, 2].length) (baseStart_7079633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7079633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7079633 prefixEnd_7079633 := by exact prefixLift 7079633
  have htrace : WordTrace (prefixWord ++ tailWord_7079633) baseStart_7079633 baseEnd_7079633 := by
    simpa [prefixWord, tailWord_7079633, baseEnd_7079633] using wordTrace_append hprefix tailTrace_7079633
  have hstable : (prefixWord ++ tailWord_7079633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7079633).length < 2 ^ (prefixWord ++ tailWord_7079633).sum := by decide
  have hdescent : baseEnd_7079633 < baseStart_7079633 := by decide
  rcases family_descends (prefixWord ++ tailWord_7079633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7079652 : List Nat := [2, 3, 1, 1, 1, 3, 4, 1, 2, 5]
def baseStart_7079652 : Nat := 118140960795 + 7079652 * 2 ^ 59
def prefixEnd_7079652 : Nat := 4983230072969 + 3 ^ 40 * 7079652 * 2
def baseEnd_7079652 : Nat := 1211754780854880020897093

theorem tailTrace_7079652 : CollatzResearch.WordTrace tailWord_7079652 prefixEnd_7079652 1211754780854880020897093 := by
  unfold tailWord_7079652
  simp only [CollatzResearch.WordTrace]
  refine ⟨129108060873818693572340605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172144081165091591429787473 129108060873818693572340605)
  ·
    refine ⟨48415522827682010089627727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129108060873818693572340605 48415522827682010089627727)
    ·
      refine ⟨72623284241523015134441591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48415522827682010089627727 72623284241523015134441591)
      ·
        refine ⟨108934926362284522701662387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72623284241523015134441591 108934926362284522701662387)
        ·
          refine ⟨163402389543426784052493581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108934926362284522701662387 163402389543426784052493581)
          ·
            refine ⟨61275896078785044019685093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 163402389543426784052493581 61275896078785044019685093)
            ·
              refine ⟨11489230514772195753690955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61275896078785044019685093 11489230514772195753690955)
              ·
                refine ⟨17233845772158293630536433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11489230514772195753690955 17233845772158293630536433)
                ·
                  refine ⟨12925384329118720222902325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17233845772158293630536433 12925384329118720222902325)
                  ·
                    refine ⟨1211754780854880020897093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12925384329118720222902325 1211754780854880020897093)
                    ·
                      rfl

theorem cell23_7079652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 4, 1, 2, 5].length) (baseStart_7079652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7079652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7079652 prefixEnd_7079652 := by exact prefixLift 7079652
  have htrace : WordTrace (prefixWord ++ tailWord_7079652) baseStart_7079652 baseEnd_7079652 := by
    simpa [prefixWord, tailWord_7079652, baseEnd_7079652] using wordTrace_append hprefix tailTrace_7079652
  have hstable : (prefixWord ++ tailWord_7079652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7079652).length < 2 ^ (prefixWord ++ tailWord_7079652).sum := by decide
  have hdescent : baseEnd_7079652 < baseStart_7079652 := by decide
  rcases family_descends (prefixWord ++ tailWord_7079652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7079685 : List Nat := [1, 3, 1, 1, 2, 1, 1, 1, 4, 4, 4]
def baseStart_7079685 : Nat := 118140960795 + 7079685 * 2 ^ 59
def prefixEnd_7079685 : Nat := 4983230072969 + 3 ^ 40 * 7079685 * 2
def baseEnd_7079685 : Nat := 3635281287426238433578627

theorem tailTrace_7079685 : CollatzResearch.WordTrace tailWord_7079685 prefixEnd_7079685 3635281287426238433578627 := by
  unfold tailWord_7079685
  simp only [CollatzResearch.WordTrace]
  refine ⟨258217325356517833780632509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172144883571011889187088339 258217325356517833780632509)
  ·
    refine ⟨96831497008694187667737191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 258217325356517833780632509 96831497008694187667737191)
    ·
      refine ⟨145247245513041281501605787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96831497008694187667737191 145247245513041281501605787)
      ·
        refine ⟨217870868269561922252408681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145247245513041281501605787 217870868269561922252408681)
        ·
          refine ⟨163403151202171441689306511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217870868269561922252408681 163403151202171441689306511)
          ·
            refine ⟨245104726803257162533959767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163403151202171441689306511 245104726803257162533959767)
            ·
              refine ⟨367657090204885743800939651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 245104726803257162533959767 367657090204885743800939651)
              ·
                refine ⟨551485635307328615701409477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 367657090204885743800939651 551485635307328615701409477)
                ·
                  refine ⟨103403556620124115444014277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 551485635307328615701409477 103403556620124115444014277)
                  ·
                    refine ⟨19388166866273271645752677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 103403556620124115444014277 19388166866273271645752677)
                    ·
                      refine ⟨3635281287426238433578627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19388166866273271645752677 3635281287426238433578627)
                      ·
                        rfl

theorem cell23_7079685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 4, 4, 4].length) (baseStart_7079685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7079685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7079685 prefixEnd_7079685 := by exact prefixLift 7079685
  have htrace : WordTrace (prefixWord ++ tailWord_7079685) baseStart_7079685 baseEnd_7079685 := by
    simpa [prefixWord, tailWord_7079685, baseEnd_7079685] using wordTrace_append hprefix tailTrace_7079685
  have hstable : (prefixWord ++ tailWord_7079685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7079685).length < 2 ^ (prefixWord ++ tailWord_7079685).sum := by decide
  have hdescent : baseEnd_7079685 < baseStart_7079685 := by decide
  rcases family_descends (prefixWord ++ tailWord_7079685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7079692 : List Nat := [2, 2, 1, 2, 2, 1, 2, 2, 4, 2, 3]
def baseStart_7079692 : Nat := 118140960795 + 7079692 * 2 ^ 59
def prefixEnd_7079692 : Nat := 4983230072969 + 3 ^ 40 * 7079692 * 2
def baseEnd_7079692 : Nat := 3635284881790819906191095

theorem tailTrace_7079692 : CollatzResearch.WordTrace tailWord_7079692 prefixEnd_7079692 3635284881790819906191095 := by
  unfold tailWord_7079692
  simp only [CollatzResearch.WordTrace]
  refine ⟨129108790333746236988068665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172145053778328315984091553 129108790333746236988068665)
  ·
    refine ⟨96831592750309677741051499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129108790333746236988068665 96831592750309677741051499)
    ·
      refine ⟨145247389125464516611577249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96831592750309677741051499 145247389125464516611577249)
      ·
        refine ⟨108935541844098387458682937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145247389125464516611577249 108935541844098387458682937)
        ·
          refine ⟨81701656383073790594012203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108935541844098387458682937 81701656383073790594012203)
          ·
            refine ⟨122552484574610685891018305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81701656383073790594012203 122552484574610685891018305)
            ·
              refine ⟨91914363430958014418263729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122552484574610685891018305 91914363430958014418263729)
              ·
                refine ⟨68935772573218510813697797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91914363430958014418263729 68935772573218510813697797)
                ·
                  refine ⟨12925457357478470777568337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68935772573218510813697797 12925457357478470777568337)
                  ·
                    refine ⟨9694093018108853083176253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12925457357478470777568337 9694093018108853083176253)
                    ·
                      refine ⟨3635284881790819906191095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9694093018108853083176253 3635284881790819906191095)
                      ·
                        rfl

theorem cell23_7079692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 2, 4, 2, 3].length) (baseStart_7079692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7079692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7079692 prefixEnd_7079692 := by exact prefixLift 7079692
  have htrace : WordTrace (prefixWord ++ tailWord_7079692) baseStart_7079692 baseEnd_7079692 := by
    simpa [prefixWord, tailWord_7079692, baseEnd_7079692] using wordTrace_append hprefix tailTrace_7079692
  have hstable : (prefixWord ++ tailWord_7079692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7079692).length < 2 ^ (prefixWord ++ tailWord_7079692).sum := by decide
  have hdescent : baseEnd_7079692 < baseStart_7079692 := by decide
  rcases family_descends (prefixWord ++ tailWord_7079692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7079716 : List Nat := [2, 3, 1, 3, 2, 1, 1, 5, 1, 4]
def baseStart_7079716 : Nat := 118140960795 + 7079716 * 2 ^ 59
def prefixEnd_7079716 : Nat := 4983230072969 + 3 ^ 40 * 7079716 * 2
def baseEnd_7079716 : Nat := 1211765735108842604096995

theorem tailTrace_7079716 : CollatzResearch.WordTrace tailWord_7079716 prefixEnd_7079716 1211765735108842604096995 := by
  unfold tailWord_7079716
  simp only [CollatzResearch.WordTrace]
  refine ⟨129109228009702763037505501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172145637346270350716674001 129109228009702763037505501)
  ·
    refine ⟨48415960503638536139064563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129109228009702763037505501 48415960503638536139064563)
    ·
      refine ⟨72623940755457804208596845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48415960503638536139064563 72623940755457804208596845)
      ·
        refine ⟨27233977783296676578223817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72623940755457804208596845 27233977783296676578223817)
        ·
          refine ⟨20425483337472507433667863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27233977783296676578223817 20425483337472507433667863)
          ·
            refine ⟨30638225006208761150501795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20425483337472507433667863 30638225006208761150501795)
            ·
              refine ⟨45957337509313141725752693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30638225006208761150501795 45957337509313141725752693)
              ·
                refine ⟨4308500391498107036789315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45957337509313141725752693 4308500391498107036789315)
                ·
                  refine ⟨6462750587247160555183973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4308500391498107036789315 6462750587247160555183973)
                  ·
                    refine ⟨1211765735108842604096995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6462750587247160555183973 1211765735108842604096995)
                    ·
                      rfl

theorem cell23_7079716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 5, 1, 4].length) (baseStart_7079716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7079716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7079716 prefixEnd_7079716 := by exact prefixLift 7079716
  have htrace : WordTrace (prefixWord ++ tailWord_7079716) baseStart_7079716 baseEnd_7079716 := by
    simpa [prefixWord, tailWord_7079716, baseEnd_7079716] using wordTrace_append hprefix tailTrace_7079716
  have hstable : (prefixWord ++ tailWord_7079716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7079716).length < 2 ^ (prefixWord ++ tailWord_7079716).sum := by decide
  have hdescent : baseEnd_7079716 < baseStart_7079716 := by decide
  rcases family_descends (prefixWord ++ tailWord_7079716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7079729 : List Nat := [1, 2, 2, 3, 2, 4, 1, 2, 6]
def baseStart_7079729 : Nat := 118140960795 + 7079729 * 2 ^ 59
def prefixEnd_7079729 : Nat := 4983230072969 + 3 ^ 40 * 7079729 * 2
def baseEnd_7079729 : Nat := 403922653397226251269825

theorem tailTrace_7079729 : CollatzResearch.WordTrace tailWord_7079729 prefixEnd_7079729 403922653397226251269825 := by
  unfold tailWord_7079729
  simp only [CollatzResearch.WordTrace]
  refine ⟨258218930168358429295234241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172145953445572286196822827 258218930168358429295234241)
  ·
    refine ⟨193664197626268821971425681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258218930168358429295234241 193664197626268821971425681)
    ·
      refine ⟨145248148219701616478569261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193664197626268821971425681 145248148219701616478569261)
      ·
        refine ⟨54468055582388106179463473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145248148219701616478569261 54468055582388106179463473)
        ·
          refine ⟨40851041686791079634597605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54468055582388106179463473 40851041686791079634597605)
          ·
            refine ⟨7659570316273327431487051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40851041686791079634597605 7659570316273327431487051)
            ·
              refine ⟨11489355474409991147230577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7659570316273327431487051 11489355474409991147230577)
              ·
                refine ⟨8617016605807493360422933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11489355474409991147230577 8617016605807493360422933)
                ·
                  refine ⟨403922653397226251269825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8617016605807493360422933 403922653397226251269825)
                  ·
                    rfl

theorem cell23_7079729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 1, 2, 6].length) (baseStart_7079729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7079729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7079729 prefixEnd_7079729 := by exact prefixLift 7079729
  have htrace : WordTrace (prefixWord ++ tailWord_7079729) baseStart_7079729 baseEnd_7079729 := by
    simpa [prefixWord, tailWord_7079729, baseEnd_7079729] using wordTrace_append hprefix tailTrace_7079729
  have hstable : (prefixWord ++ tailWord_7079729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7079729).length < 2 ^ (prefixWord ++ tailWord_7079729).sum := by decide
  have hdescent : baseEnd_7079729 < baseStart_7079729 := by decide
  rcases family_descends (prefixWord ++ tailWord_7079729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7079735 : List Nat := [1, 1, 3, 1, 2, 1, 2, 2, 2, 1, 7]
def baseStart_7079735 : Nat := 118140960795 + 7079735 * 2 ^ 59
def prefixEnd_7079735 : Nat := 4983230072969 + 3 ^ 40 * 7079735 * 2
def baseEnd_7079735 : Nat := 3635306961458963237953397

theorem tailTrace_7079735 : CollatzResearch.WordTrace tailWord_7079735 prefixEnd_7079735 3635306961458963237953397 := by
  unfold tailWord_7079735
  simp only [CollatzResearch.WordTrace]
  refine ⟨258219149006336692319952659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172146099337557794879968439 258219149006336692319952659)
  ·
    refine ⟨387328723509505038479928989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258219149006336692319952659 387328723509505038479928989)
    ·
      refine ⟨145248271316064389429973371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 387328723509505038479928989 145248271316064389429973371)
      ·
        refine ⟨217872406974096584144960057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145248271316064389429973371 217872406974096584144960057)
        ·
          refine ⟨163404305230572438108720043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217872406974096584144960057 163404305230572438108720043)
          ·
            refine ⟨245106457845858657163080065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163404305230572438108720043 245106457845858657163080065)
            ·
              refine ⟨183829843384393992872310049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 245106457845858657163080065 183829843384393992872310049)
              ·
                refine ⟨137872382538295494654232537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 183829843384393992872310049 137872382538295494654232537)
                ·
                  refine ⟨103404286903721620990674403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 137872382538295494654232537 103404286903721620990674403)
                  ·
                    refine ⟨155106430355582431486011605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 103404286903721620990674403 155106430355582431486011605)
                    ·
                      refine ⟨3635306961458963237953397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 155106430355582431486011605 3635306961458963237953397)
                      ·
                        rfl

theorem cell23_7079735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 2, 2, 1, 7].length) (baseStart_7079735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7079735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7079735 prefixEnd_7079735 := by exact prefixLift 7079735
  have htrace : WordTrace (prefixWord ++ tailWord_7079735) baseStart_7079735 baseEnd_7079735 := by
    simpa [prefixWord, tailWord_7079735, baseEnd_7079735] using wordTrace_append hprefix tailTrace_7079735
  have hstable : (prefixWord ++ tailWord_7079735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7079735).length < 2 ^ (prefixWord ++ tailWord_7079735).sum := by decide
  have hdescent : baseEnd_7079735 < baseStart_7079735 := by decide
  rcases family_descends (prefixWord ++ tailWord_7079735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7079789 : List Nat := [1, 5, 1, 1, 1, 1, 4, 1, 4, 4]
def baseStart_7079789 : Nat := 118140960795 + 7079789 * 2 ^ 59
def prefixEnd_7079789 : Nat := 4983230072969 + 3 ^ 40 * 7079789 * 2
def baseEnd_7079789 : Nat := 1211778229804768675559383

theorem tailTrace_7079789 : CollatzResearch.WordTrace tailWord_7079789 prefixEnd_7079789 1211778229804768675559383 := by
  unfold tailWord_7079789
  simp only [CollatzResearch.WordTrace]
  refine ⟨258221118548141059542418421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172147412365427373028278947 258221118548141059542418421)
  ·
    refine ⟨24208229863888224332101727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 258221118548141059542418421 24208229863888224332101727)
    ·
      refine ⟨36312344795832336498152591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24208229863888224332101727 36312344795832336498152591)
      ·
        refine ⟨54468517193748504747228887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36312344795832336498152591 54468517193748504747228887)
        ·
          refine ⟨81702775790622757120843331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54468517193748504747228887 81702775790622757120843331)
          ·
            refine ⟨122554163685934135681264997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81702775790622757120843331 122554163685934135681264997)
            ·
              refine ⟨22978905691112650440237187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 122554163685934135681264997 22978905691112650440237187)
              ·
                refine ⟨34468358536668975660355781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22978905691112650440237187 34468358536668975660355781)
                ·
                  refine ⟨6462817225625432936316709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34468358536668975660355781 6462817225625432936316709)
                  ·
                    refine ⟨1211778229804768675559383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6462817225625432936316709 1211778229804768675559383)
                    ·
                      rfl

theorem cell23_7079789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 1, 4, 4].length) (baseStart_7079789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7079789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7079789 prefixEnd_7079789 := by exact prefixLift 7079789
  have htrace : WordTrace (prefixWord ++ tailWord_7079789) baseStart_7079789 baseEnd_7079789 := by
    simpa [prefixWord, tailWord_7079789, baseEnd_7079789] using wordTrace_append hprefix tailTrace_7079789
  have hstable : (prefixWord ++ tailWord_7079789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7079789).length < 2 ^ (prefixWord ++ tailWord_7079789).sum := by decide
  have hdescent : baseEnd_7079789 < baseStart_7079789 := by decide
  rcases family_descends (prefixWord ++ tailWord_7079789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7079816 : List Nat := [2, 1, 3, 3, 3, 1, 1, 1, 3, 2, 3]
def baseStart_7079816 : Nat := 118140960795 + 7079816 * 2 ^ 59
def prefixEnd_7079816 : Nat := 4983230072969 + 3 ^ 40 * 7079816 * 2
def baseEnd_7079816 : Nat := 3635348553391977421040525

theorem tailTrace_7079816 : CollatzResearch.WordTrace tailWord_7079816 prefixEnd_7079816 3635348553391977421040525 := by
  unfold tailWord_7079816
  simp only [CollatzResearch.WordTrace]
  refine ⟨129111051659521621576825651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172148068879362162102434201 129111051659521621576825651)
  ·
    refine ⟨193666577489282432365238477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129111051659521621576825651 193666577489282432365238477)
    ·
      refine ⟨72624966558480912136964429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193666577489282432365238477 72624966558480912136964429)
      ·
        refine ⟨27234362459430342051361661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72624966558480912136964429 27234362459430342051361661)
        ·
          refine ⟨10212885922286378269260623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27234362459430342051361661 10212885922286378269260623)
          ·
            refine ⟨15319328883429567403890935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10212885922286378269260623 15319328883429567403890935)
            ·
              refine ⟨22978993325144351105836403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15319328883429567403890935 22978993325144351105836403)
              ·
                refine ⟨34468489987716526658754605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22978993325144351105836403 34468489987716526658754605)
                ·
                  refine ⟨12925683745393697497032977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34468489987716526658754605 12925683745393697497032977)
                  ·
                    refine ⟨9694262809045273122774733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12925683745393697497032977 9694262809045273122774733)
                    ·
                      refine ⟨3635348553391977421040525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9694262809045273122774733 3635348553391977421040525)
                      ·
                        rfl

theorem cell23_7079816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 1, 3, 2, 3].length) (baseStart_7079816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7079816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7079816 prefixEnd_7079816 := by exact prefixLift 7079816
  have htrace : WordTrace (prefixWord ++ tailWord_7079816) baseStart_7079816 baseEnd_7079816 := by
    simpa [prefixWord, tailWord_7079816, baseEnd_7079816] using wordTrace_append hprefix tailTrace_7079816
  have hstable : (prefixWord ++ tailWord_7079816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7079816).length < 2 ^ (prefixWord ++ tailWord_7079816).sum := by decide
  have hdescent : baseEnd_7079816 < baseStart_7079816 := by decide
  rcases family_descends (prefixWord ++ tailWord_7079816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7079826 : List Nat := [3, 2, 3, 2, 1, 2, 1, 2, 1, 2, 4]
def baseStart_7079826 : Nat := 118140960795 + 7079826 * 2 ^ 59
def prefixEnd_7079826 : Nat := 4983230072969 + 3 ^ 40 * 7079826 * 2
def baseEnd_7079826 : Nat := 3635353688198522381915479

theorem tailTrace_7079826 : CollatzResearch.WordTrace tailWord_7079826 prefixEnd_7079826 3635353688198522381915479 := by
  unfold tailWord_7079826
  simp only [CollatzResearch.WordTrace]
  refine ⟨64555617012251753715378833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172148312032671343241010221 64555617012251753715378833)
  ·
    refine ⟨48416712759188815286534125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64555617012251753715378833 48416712759188815286534125)
    ·
      refine ⟨18156267284695805732450297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48416712759188815286534125 18156267284695805732450297)
      ·
        refine ⟨13617200463521854299337723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18156267284695805732450297 13617200463521854299337723)
        ·
          refine ⟨20425800695282781449006585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13617200463521854299337723 20425800695282781449006585)
          ·
            refine ⟨15319350521462086086754939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20425800695282781449006585 15319350521462086086754939)
            ·
              refine ⟨22979025782193129130132409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15319350521462086086754939 22979025782193129130132409)
              ·
                refine ⟨17234269336644846847599307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22979025782193129130132409 17234269336644846847599307)
                ·
                  refine ⟨25851404004967270271398961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17234269336644846847599307 25851404004967270271398961)
                  ·
                    refine ⟨19388553003725452703549221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25851404004967270271398961 19388553003725452703549221)
                    ·
                      refine ⟨3635353688198522381915479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19388553003725452703549221 3635353688198522381915479)
                      ·
                        rfl

theorem cell23_7079826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_7079826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7079826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7079826 prefixEnd_7079826 := by exact prefixLift 7079826
  have htrace : WordTrace (prefixWord ++ tailWord_7079826) baseStart_7079826 baseEnd_7079826 := by
    simpa [prefixWord, tailWord_7079826, baseEnd_7079826] using wordTrace_append hprefix tailTrace_7079826
  have hstable : (prefixWord ++ tailWord_7079826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7079826).length < 2 ^ (prefixWord ++ tailWord_7079826).sum := by decide
  have hdescent : baseEnd_7079826 < baseStart_7079826 := by decide
  rcases family_descends (prefixWord ++ tailWord_7079826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7079829 : List Nat := [1, 3, 2, 1, 1, 3, 3, 2, 1, 3, 3]
def baseStart_7079829 : Nat := 118140960795 + 7079829 * 2 ^ 59
def prefixEnd_7079829 : Nat := 4983230072969 + 3 ^ 40 * 7079829 * 2
def baseEnd_7079829 : Nat := 3635355228640485870177965

theorem tailTrace_7079829 : CollatzResearch.WordTrace tailWord_7079829 prefixEnd_7079829 3635355228640485870177965 := by
  unfold tailWord_7079829
  simp only [CollatzResearch.WordTrace]
  refine ⟨258222577467996146373874541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172148384978664097582583027 258222577467996146373874541)
  ·
    refine ⟨96833466550498554890202953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 258222577467996146373874541 96833466550498554890202953)
    ·
      refine ⟨72625099912873916167652215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96833466550498554890202953 72625099912873916167652215)
      ·
        refine ⟨108937649869310874251478323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72625099912873916167652215 108937649869310874251478323)
        ·
          refine ⟨163406474803966311377217485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108937649869310874251478323 163406474803966311377217485)
          ·
            refine ⟨61277428051487366766456557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 163406474803966311377217485 61277428051487366766456557)
            ·
              refine ⟨22979035519307762537421209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61277428051487366766456557 22979035519307762537421209)
              ·
                refine ⟨17234276639480821903065907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22979035519307762537421209 17234276639480821903065907)
                ·
                  refine ⟨25851414959221232854598861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17234276639480821903065907 25851414959221232854598861)
                  ·
                    refine ⟨9694280609707962320474573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25851414959221232854598861 9694280609707962320474573)
                    ·
                      refine ⟨3635355228640485870177965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9694280609707962320474573 3635355228640485870177965)
                      ·
                        rfl

theorem cell23_7079829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 2, 1, 3, 3].length) (baseStart_7079829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7079829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7079829 prefixEnd_7079829 := by exact prefixLift 7079829
  have htrace : WordTrace (prefixWord ++ tailWord_7079829) baseStart_7079829 baseEnd_7079829 := by
    simpa [prefixWord, tailWord_7079829, baseEnd_7079829] using wordTrace_append hprefix tailTrace_7079829
  have hstable : (prefixWord ++ tailWord_7079829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7079829).length < 2 ^ (prefixWord ++ tailWord_7079829).sum := by decide
  have hdescent : baseEnd_7079829 < baseStart_7079829 := by decide
  rcases family_descends (prefixWord ++ tailWord_7079829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7079847 : List Nat := [1, 1, 6, 1, 2, 1, 4, 2, 1, 2, 2]
def baseStart_7079847 : Nat := 118140960795 + 7079847 * 2 ^ 59
def prefixEnd_7079847 : Nat := 4983230072969 + 3 ^ 40 * 7079847 * 2
def baseEnd_7079847 : Nat := 3635364471292266799752883

theorem tailTrace_7079847 : CollatzResearch.WordTrace tailWord_7079847 prefixEnd_7079847 3635364471292266799752883 := by
  unfold tailWord_7079847
  simp only [CollatzResearch.WordTrace]
  refine ⟨258223233981930935448029795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172148822654620623632019863 258223233981930935448029795)
  ·
    refine ⟨387334850972896403172044693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258223233981930935448029795 387334850972896403172044693)
    ·
      refine ⟨18156321139354518898689595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 387334850972896403172044693 18156321139354518898689595)
      ·
        refine ⟨27234481709031778348034393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18156321139354518898689595 27234481709031778348034393)
        ·
          refine ⟨20425861281773833761025795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27234481709031778348034393 20425861281773833761025795)
          ·
            refine ⟨30638791922660750641538693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20425861281773833761025795 30638791922660750641538693)
            ·
              refine ⟨5744773485498890745288505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30638791922660750641538693 5744773485498890745288505)
              ·
                refine ⟨4308580114124168058966379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5744773485498890745288505 4308580114124168058966379)
                ·
                  refine ⟨6462870171186252088449569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4308580114124168058966379 6462870171186252088449569)
                  ·
                    refine ⟨4847152628389689066337177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6462870171186252088449569 4847152628389689066337177)
                    ·
                      refine ⟨3635364471292266799752883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4847152628389689066337177 3635364471292266799752883)
                      ·
                        rfl

theorem cell23_7079847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 4, 2, 1, 2, 2].length) (baseStart_7079847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7079847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7079847 prefixEnd_7079847 := by exact prefixLift 7079847
  have htrace : WordTrace (prefixWord ++ tailWord_7079847) baseStart_7079847 baseEnd_7079847 := by
    simpa [prefixWord, tailWord_7079847, baseEnd_7079847] using wordTrace_append hprefix tailTrace_7079847
  have hstable : (prefixWord ++ tailWord_7079847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7079847).length < 2 ^ (prefixWord ++ tailWord_7079847).sum := by decide
  have hdescent : baseEnd_7079847 < baseStart_7079847 := by decide
  rcases family_descends (prefixWord ++ tailWord_7079847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7079886 : List Nat := [4, 1, 1, 1, 2, 2, 1, 4, 1, 4, 2]
def baseStart_7079886 : Nat := 118140960795 + 7079886 * 2 ^ 59
def prefixEnd_7079886 : Nat := 4983230072969 + 3 ^ 40 * 7079886 * 2
def baseEnd_7079886 : Nat := 3635384497037792147165203

theorem tailTrace_7079886 : CollatzResearch.WordTrace tailWord_7079886 prefixEnd_7079886 3635384497037792147165203 := by
  unfold tailWord_7079886
  simp only [CollatzResearch.WordTrace]
  refine ⟨32278082053598705638587439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172149770952526430072466341 32278082053598705638587439)
  ·
    refine ⟨48417123080398058457881159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32278082053598705638587439 48417123080398058457881159)
    ·
      refine ⟨72625684620597087686821739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48417123080398058457881159 72625684620597087686821739)
      ·
        refine ⟨108938526930895631530232609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72625684620597087686821739 108938526930895631530232609)
        ·
          refine ⟨81703895198171723647674457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108938526930895631530232609 81703895198171723647674457)
          ·
            refine ⟨61277921398628792735755843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81703895198171723647674457 61277921398628792735755843)
            ·
              refine ⟨91916882097943189103633765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61277921398628792735755843 91916882097943189103633765)
              ·
                refine ⟨17234415393364347956931331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 91916882097943189103633765 17234415393364347956931331)
                ·
                  refine ⟨25851623090046521935396997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17234415393364347956931331 25851623090046521935396997)
                  ·
                    refine ⟨4847179329383722862886937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25851623090046521935396997 4847179329383722862886937)
                    ·
                      refine ⟨3635384497037792147165203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4847179329383722862886937 3635384497037792147165203)
                      ·
                        rfl

theorem cell23_7079886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 4, 1, 4, 2].length) (baseStart_7079886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7079886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7079886 prefixEnd_7079886 := by exact prefixLift 7079886
  have htrace : WordTrace (prefixWord ++ tailWord_7079886) baseStart_7079886 baseEnd_7079886 := by
    simpa [prefixWord, tailWord_7079886, baseEnd_7079886] using wordTrace_append hprefix tailTrace_7079886
  have hstable : (prefixWord ++ tailWord_7079886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7079886).length < 2 ^ (prefixWord ++ tailWord_7079886).sum := by decide
  have hdescent : baseEnd_7079886 < baseStart_7079886 := by decide
  rcases family_descends (prefixWord ++ tailWord_7079886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7079890 : List Nat := [3, 2, 2, 3, 2, 1, 1, 3, 1, 3, 2]
def baseStart_7079890 : Nat := 118140960795 + 7079890 * 2 ^ 59
def prefixEnd_7079890 : Nat := 4983230072969 + 3 ^ 40 * 7079890 * 2
def baseEnd_7079890 : Nat := 3635386550960410131515185

theorem tailTrace_7079890 : CollatzResearch.WordTrace tailWord_7079890 prefixEnd_7079890 3635386550960410131515185 := by
  unfold tailWord_7079890
  simp only [CollatzResearch.WordTrace]
  refine ⟨64556200580193788447961281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172149868213850102527896749 64556200580193788447961281)
  ·
    refine ⟨48417150435145341335970961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64556200580193788447961281 48417150435145341335970961)
    ·
      refine ⟨36312862826359006001978221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48417150435145341335970961 36312862826359006001978221)
      ·
        refine ⟨13617323559884627250741833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36312862826359006001978221 13617323559884627250741833)
        ·
          refine ⟨10212992669913470438056375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13617323559884627250741833 10212992669913470438056375)
          ·
            refine ⟨15319489004870205657084563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10212992669913470438056375 15319489004870205657084563)
            ·
              refine ⟨22979233507305308485626845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15319489004870205657084563 22979233507305308485626845)
              ·
                refine ⟨8617212565239490682110067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22979233507305308485626845 8617212565239490682110067)
                ·
                  refine ⟨12925818847859236023165101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8617212565239490682110067 12925818847859236023165101)
                  ·
                    refine ⟨4847182067947213508686913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12925818847859236023165101 4847182067947213508686913)
                    ·
                      refine ⟨3635386550960410131515185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4847182067947213508686913 3635386550960410131515185)
                      ·
                        rfl

theorem cell23_7079890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 3, 1, 3, 2].length) (baseStart_7079890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7079890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7079890 prefixEnd_7079890 := by exact prefixLift 7079890
  have htrace : WordTrace (prefixWord ++ tailWord_7079890) baseStart_7079890 baseEnd_7079890 := by
    simpa [prefixWord, tailWord_7079890, baseEnd_7079890] using wordTrace_append hprefix tailTrace_7079890
  have hstable : (prefixWord ++ tailWord_7079890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7079890).length < 2 ^ (prefixWord ++ tailWord_7079890).sum := by decide
  have hdescent : baseEnd_7079890 < baseStart_7079890 := by decide
  rcases family_descends (prefixWord ++ tailWord_7079890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7079903 : List Nat := [1, 1, 2, 3, 4, 2, 1, 1, 4, 2, 2]
def baseStart_7079903 : Nat := 118140960795 + 7079903 * 2 ^ 59
def prefixEnd_7079903 : Nat := 4983230072969 + 3 ^ 40 * 7079903 * 2
def baseEnd_7079903 : Nat := 3635393226208918580652625

theorem tailTrace_7079903 : CollatzResearch.WordTrace tailWord_7079903 prefixEnd_7079903 3635393226208918580652625 := by
  unfold tailWord_7079903
  simp only [CollatzResearch.WordTrace]
  refine ⟨258225276469728057012068363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172150184313152038008045575 258225276469728057012068363)
  ·
    refine ⟨387337914704592085518102545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258225276469728057012068363 387337914704592085518102545)
    ·
      refine ⟨290503436028444064138576909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 387337914704592085518102545 290503436028444064138576909)
      ·
        refine ⟨108938788510666524051966341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 290503436028444064138576909 108938788510666524051966341)
        ·
          refine ⟨20426022845749973259743689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 108938788510666524051966341 20426022845749973259743689)
          ·
            refine ⟨15319517134312479944807767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20426022845749973259743689 15319517134312479944807767)
            ·
              refine ⟨22979275701468719917211651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15319517134312479944807767 22979275701468719917211651)
              ·
                refine ⟨34468913552203079875817477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22979275701468719917211651 34468913552203079875817477)
                ·
                  refine ⟨6462921291038077476715777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34468913552203079875817477 6462921291038077476715777)
                  ·
                    refine ⟨4847190968278558107536833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6462921291038077476715777 4847190968278558107536833)
                    ·
                      refine ⟨3635393226208918580652625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4847190968278558107536833 3635393226208918580652625)
                      ·
                        rfl

theorem cell23_7079903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 1, 4, 2, 2].length) (baseStart_7079903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7079903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7079903 prefixEnd_7079903 := by exact prefixLift 7079903
  have htrace : WordTrace (prefixWord ++ tailWord_7079903) baseStart_7079903 baseEnd_7079903 := by
    simpa [prefixWord, tailWord_7079903, baseEnd_7079903] using wordTrace_append hprefix tailTrace_7079903
  have hstable : (prefixWord ++ tailWord_7079903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7079903).length < 2 ^ (prefixWord ++ tailWord_7079903).sum := by decide
  have hdescent : baseEnd_7079903 < baseStart_7079903 := by decide
  rcases family_descends (prefixWord ++ tailWord_7079903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7079919 : List Nat := [1, 1, 2, 1, 4, 2, 1, 3, 2, 3, 3]
def baseStart_7079919 : Nat := 118140960795 + 7079919 * 2 ^ 59
def prefixEnd_7079919 : Nat := 4983230072969 + 3 ^ 40 * 7079919 * 2
def baseEnd_7079919 : Nat := 3635401441899390518052551

theorem tailTrace_7079919 : CollatzResearch.WordTrace tailWord_7079919 prefixEnd_7079919 3635401441899390518052551 := by
  unfold tailWord_7079919
  simp only [CollatzResearch.WordTrace]
  refine ⟨258225860037670091744650811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172150573358446727829767207 258225860037670091744650811)
  ·
    refine ⟨387338790056505137616976217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258225860037670091744650811 387338790056505137616976217)
    ·
      refine ⟨290504092542378853212732163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 387338790056505137616976217 290504092542378853212732163)
      ·
        refine ⟨435756138813568279819098245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290504092542378853212732163 435756138813568279819098245)
        ·
          refine ⟨81704276027544052466080921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 435756138813568279819098245 81704276027544052466080921)
          ·
            refine ⟨61278207020658039349560691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81704276027544052466080921 61278207020658039349560691)
            ·
              refine ⟨91917310530987059024341037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61278207020658039349560691 91917310530987059024341037)
              ·
                refine ⟨34468991449120147134127889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91917310530987059024341037 34468991449120147134127889)
                ·
                  refine ⟨25851743586840110350595917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34468991449120147134127889 25851743586840110350595917)
                  ·
                    refine ⟨9694403845065041381473469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25851743586840110350595917 9694403845065041381473469)
                    ·
                      refine ⟨3635401441899390518052551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9694403845065041381473469 3635401441899390518052551)
                      ·
                        rfl

theorem cell23_7079919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 3, 2, 3, 3].length) (baseStart_7079919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7079919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7079919 prefixEnd_7079919 := by exact prefixLift 7079919
  have htrace : WordTrace (prefixWord ++ tailWord_7079919) baseStart_7079919 baseEnd_7079919 := by
    simpa [prefixWord, tailWord_7079919, baseEnd_7079919] using wordTrace_append hprefix tailTrace_7079919
  have hstable : (prefixWord ++ tailWord_7079919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7079919).length < 2 ^ (prefixWord ++ tailWord_7079919).sum := by decide
  have hdescent : baseEnd_7079919 < baseStart_7079919 := by decide
  rcases family_descends (prefixWord ++ tailWord_7079919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7079943 : List Nat := [1, 1, 4, 3, 1, 4, 1, 3, 5]
def baseStart_7079943 : Nat := 118140960795 + 7079943 * 2 ^ 59
def prefixEnd_7079943 : Nat := 4983230072969 + 3 ^ 40 * 7079943 * 2
def baseEnd_7079943 : Nat := 403934862826122047128049

theorem tailTrace_7079943 : CollatzResearch.WordTrace tailWord_7079943 prefixEnd_7079943 403934862826122047128049 := by
  unfold tailWord_7079943
  simp only [CollatzResearch.WordTrace]
  refine ⟨258226735389583143843524483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172151156926388762562349655 258226735389583143843524483)
  ·
    refine ⟨387340103084374715765286725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258226735389583143843524483 387340103084374715765286725)
    ·
      refine ⟨72626269328320259205991261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 387340103084374715765286725 72626269328320259205991261)
      ·
        refine ⟨27234850998120097202246723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72626269328320259205991261 27234850998120097202246723)
        ·
          refine ⟨40852276497180145803370085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27234850998120097202246723 40852276497180145803370085)
          ·
            refine ⟨7659801843221277338131891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40852276497180145803370085 7659801843221277338131891)
            ·
              refine ⟨11489702764831916007197837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7659801843221277338131891 11489702764831916007197837)
              ·
                refine ⟨4308638536811968502699189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11489702764831916007197837 4308638536811968502699189)
                ·
                  refine ⟨403934862826122047128049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4308638536811968502699189 403934862826122047128049)
                  ·
                    rfl

theorem cell23_7079943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 1, 3, 5].length) (baseStart_7079943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7079943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7079943 prefixEnd_7079943 := by exact prefixLift 7079943
  have htrace : WordTrace (prefixWord ++ tailWord_7079943) baseStart_7079943 baseEnd_7079943 := by
    simpa [prefixWord, tailWord_7079943, baseEnd_7079943] using wordTrace_append hprefix tailTrace_7079943
  have hstable : (prefixWord ++ tailWord_7079943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7079943).length < 2 ^ (prefixWord ++ tailWord_7079943).sum := by decide
  have hdescent : baseEnd_7079943 < baseStart_7079943 := by decide
  rcases family_descends (prefixWord ++ tailWord_7079943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7079952 : List Nat := [2, 1, 1, 1, 1, 1, 1, 4, 1, 10]
def baseStart_7079952 : Nat := 118140960795 + 7079952 * 2 ^ 59
def prefixEnd_7079952 : Nat := 4983230072969 + 3 ^ 40 * 7079952 * 2
def baseEnd_7079952 : Nat := 1211806128920329629646633

theorem tailTrace_7079952 : CollatzResearch.WordTrace tailWord_7079952 prefixEnd_7079952 1211806128920329629646633 := by
  unfold tailWord_7079952
  simp only [CollatzResearch.WordTrace]
  refine ⟨129113531823275269190301055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172151375764367025587068073 129113531823275269190301055)
  ·
    refine ⟨193670297734912903785451583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129113531823275269190301055 193670297734912903785451583)
    ·
      refine ⟨290505446602369355678177375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193670297734912903785451583 290505446602369355678177375)
      ·
        refine ⟨435758169903554033517266063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290505446602369355678177375 435758169903554033517266063)
        ·
          refine ⟨653637254855331050275899095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 435758169903554033517266063 653637254855331050275899095)
          ·
            refine ⟨980455882282996575413848643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 653637254855331050275899095 980455882282996575413848643)
            ·
              refine ⟨1470683823424494863120772965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 980455882282996575413848643 1470683823424494863120772965)
              ·
                refine ⟨275753216892092786835144931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1470683823424494863120772965 275753216892092786835144931)
                ·
                  refine ⟨413629825338139180252717397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 275753216892092786835144931 413629825338139180252717397)
                  ·
                    refine ⟨1211806128920329629646633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 413629825338139180252717397 1211806128920329629646633)
                    ·
                      rfl

theorem cell23_7079952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 1, 10].length) (baseStart_7079952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7079952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7079952 prefixEnd_7079952 := by exact prefixLift 7079952
  have htrace : WordTrace (prefixWord ++ tailWord_7079952) baseStart_7079952 baseEnd_7079952 := by
    simpa [prefixWord, tailWord_7079952, baseEnd_7079952] using wordTrace_append hprefix tailTrace_7079952
  have hstable : (prefixWord ++ tailWord_7079952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7079952).length < 2 ^ (prefixWord ++ tailWord_7079952).sum := by decide
  have hdescent : baseEnd_7079952 < baseStart_7079952 := by decide
  rcases family_descends (prefixWord ++ tailWord_7079952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7079979 : List Nat := [1, 1, 1, 1, 2, 1, 4, 4, 1, 4, 3]
def baseStart_7079979 : Nat := 118140960795 + 7079979 * 2 ^ 59
def prefixEnd_7079979 : Nat := 4983230072969 + 3 ^ 40 * 7079979 * 2
def baseEnd_7079979 : Nat := 3635432250738660283302275

theorem tailTrace_7079979 : CollatzResearch.WordTrace tailWord_7079979 prefixEnd_7079979 3635432250738660283302275 := by
  unfold tailWord_7079979
  simp only [CollatzResearch.WordTrace]
  refine ⟨258228048417452721991834991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172152032278301814661223327 258228048417452721991834991)
  ·
    refine ⟨387342072626179082987752487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258228048417452721991834991 387342072626179082987752487)
    ·
      refine ⟨581013108939268624481628731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 387342072626179082987752487 581013108939268624481628731)
      ·
        refine ⟨871519663408902936722443097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 581013108939268624481628731 871519663408902936722443097)
        ·
          refine ⟨653639747556677202541832323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 871519663408902936722443097 653639747556677202541832323)
          ·
            refine ⟨980459621335015803812748485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 653639747556677202541832323 980459621335015803812748485)
            ·
              refine ⟨183836179000315463214890341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 980459621335015803812748485 183836179000315463214890341)
              ·
                refine ⟨34469283562559149352791939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 183836179000315463214890341 34469283562559149352791939)
                ·
                  refine ⟨51703925343838724029187909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34469283562559149352791939 51703925343838724029187909)
                  ·
                    refine ⟨9694486001969760755472733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51703925343838724029187909 9694486001969760755472733)
                    ·
                      refine ⟨3635432250738660283302275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9694486001969760755472733 3635432250738660283302275)
                      ·
                        rfl

theorem cell23_7079979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 4, 1, 4, 3].length) (baseStart_7079979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7079979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7079979 prefixEnd_7079979 := by exact prefixLift 7079979
  have htrace : WordTrace (prefixWord ++ tailWord_7079979) baseStart_7079979 baseEnd_7079979 := by
    simpa [prefixWord, tailWord_7079979, baseEnd_7079979] using wordTrace_append hprefix tailTrace_7079979
  have hstable : (prefixWord ++ tailWord_7079979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7079979).length < 2 ^ (prefixWord ++ tailWord_7079979).sum := by decide
  have hdescent : baseEnd_7079979 < baseStart_7079979 := by decide
  rcases family_descends (prefixWord ++ tailWord_7079979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7079989 : List Nat := [1, 3, 3, 1, 1, 1, 2, 1, 2, 4, 4]
def baseStart_7079989 : Nat := 118140960795 + 7079989 * 2 ^ 59
def prefixEnd_7079989 : Nat := 4983230072969 + 3 ^ 40 * 7079989 * 2
def baseEnd_7079989 : Nat := 3635437385545205244177229

theorem tailTrace_7079989 : CollatzResearch.WordTrace tailWord_7079989 prefixEnd_7079989 3635437385545205244177229 := by
  unfold tailWord_7079989
  simp only [CollatzResearch.WordTrace]
  refine ⟨258228413147416493699699021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172152275431610995799799347 258228413147416493699699021)
  ·
    refine ⟨96835654930281185137387133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 258228413147416493699699021 96835654930281185137387133)
    ·
      refine ⟨36313370598855444426520175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96835654930281185137387133 36313370598855444426520175)
      ·
        refine ⟨54470055898283166639780263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36313370598855444426520175 54470055898283166639780263)
        ·
          refine ⟨81705083847424749959670395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54470055898283166639780263 81705083847424749959670395)
          ·
            refine ⟨122557625771137124939505593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81705083847424749959670395 122557625771137124939505593)
            ·
              refine ⟨91918219328352843704629195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122557625771137124939505593 91918219328352843704629195)
              ·
                refine ⟨137877328992529265556943793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91918219328352843704629195 137877328992529265556943793)
                ·
                  refine ⟨103407996744396949167707845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 137877328992529265556943793 103407996744396949167707845)
                  ·
                    refine ⟨19388999389574427968945221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 103407996744396949167707845 19388999389574427968945221)
                    ·
                      refine ⟨3635437385545205244177229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19388999389574427968945221 3635437385545205244177229)
                      ·
                        rfl

theorem cell23_7079989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 1, 2, 4, 4].length) (baseStart_7079989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7079989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7079989 prefixEnd_7079989 := by exact prefixLift 7079989
  have htrace : WordTrace (prefixWord ++ tailWord_7079989) baseStart_7079989 baseEnd_7079989 := by
    simpa [prefixWord, tailWord_7079989, baseEnd_7079989] using wordTrace_append hprefix tailTrace_7079989
  have hstable : (prefixWord ++ tailWord_7079989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7079989).length < 2 ^ (prefixWord ++ tailWord_7079989).sum := by decide
  have hdescent : baseEnd_7079989 < baseStart_7079989 := by decide
  rcases family_descends (prefixWord ++ tailWord_7079989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7079993 : List Nat := [1, 2, 1, 5, 3, 1, 2, 1, 2, 1, 4]
def baseStart_7079993 : Nat := 118140960795 + 7079993 * 2 ^ 59
def prefixEnd_7079993 : Nat := 4983230072969 + 3 ^ 40 * 7079993 * 2
def baseEnd_7079993 : Nat := 3635439439467823228527211

theorem tailTrace_7079993 : CollatzResearch.WordTrace tailWord_7079993 prefixEnd_7079993 3635439439467823228527211 := by
  unfold tailWord_7079993
  simp only [CollatzResearch.WordTrace]
  refine ⟨258228559039402002382844633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172152372692934668255229755 258228559039402002382844633)
  ·
    refine ⟨193671419279551501787133475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258228559039402002382844633 193671419279551501787133475)
    ·
      refine ⟨290507128919327252680700213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193671419279551501787133475 290507128919327252680700213)
      ·
        refine ⟨27235043336186929938815645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 290507128919327252680700213 27235043336186929938815645)
        ·
          refine ⟨10213141251070098727055867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27235043336186929938815645 10213141251070098727055867)
          ·
            refine ⟨15319711876605148090583801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10213141251070098727055867 15319711876605148090583801)
            ·
              refine ⟨11489783907453861067937851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15319711876605148090583801 11489783907453861067937851)
              ·
                refine ⟨17234675861180791601906777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11489783907453861067937851 17234675861180791601906777)
                ·
                  refine ⟨12926006895885593701430083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17234675861180791601906777 12926006895885593701430083)
                  ·
                    refine ⟨19389010343828390552145125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12926006895885593701430083 19389010343828390552145125)
                    ·
                      refine ⟨3635439439467823228527211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19389010343828390552145125 3635439439467823228527211)
                      ·
                        rfl

theorem cell23_7079993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 2, 1, 2, 1, 4].length) (baseStart_7079993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7079993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7079993 prefixEnd_7079993 := by exact prefixLift 7079993
  have htrace : WordTrace (prefixWord ++ tailWord_7079993) baseStart_7079993 baseEnd_7079993 := by
    simpa [prefixWord, tailWord_7079993, baseEnd_7079993] using wordTrace_append hprefix tailTrace_7079993
  have hstable : (prefixWord ++ tailWord_7079993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7079993).length < 2 ^ (prefixWord ++ tailWord_7079993).sum := by decide
  have hdescent : baseEnd_7079993 < baseStart_7079993 := by decide
  rcases family_descends (prefixWord ++ tailWord_7079993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7080013 : List Nat := [1, 6, 1, 1, 1, 1, 1, 4, 2, 2, 3]
def baseStart_7080013 : Nat := 118140960795 + 7080013 * 2 ^ 59
def prefixEnd_7080013 : Nat := 4983230072969 + 3 ^ 40 * 7080013 * 2
def baseEnd_7080013 : Nat := 3635449709080913150277119

theorem tailTrace_7080013 : CollatzResearch.WordTrace tailWord_7080013 prefixEnd_7080013 3635449709080913150277119 := by
  unfold tailWord_7080013
  simp only [CollatzResearch.WordTrace]
  refine ⟨258229288499329545798572693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172152858999553030532381795 258229288499329545798572693)
  ·
    refine ⟨12104497898406072459308095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 258229288499329545798572693 12104497898406072459308095)
    ·
      refine ⟨18156746847609108688962143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12104497898406072459308095 18156746847609108688962143)
      ·
        refine ⟨27235120271413663033443215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18156746847609108688962143 27235120271413663033443215)
        ·
          refine ⟨40852680407120494550164823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27235120271413663033443215 40852680407120494550164823)
          ·
            refine ⟨61279020610680741825247235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40852680407120494550164823 61279020610680741825247235)
            ·
              refine ⟨91918530916021112737870853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61279020610680741825247235 91918530916021112737870853)
              ·
                refine ⟨17234724546753958638350785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 91918530916021112737870853 17234724546753958638350785)
                ·
                  refine ⟨12926043410065468978763089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17234724546753958638350785 12926043410065468978763089)
                  ·
                    refine ⟨9694532557549101734072317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12926043410065468978763089 9694532557549101734072317)
                    ·
                      refine ⟨3635449709080913150277119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9694532557549101734072317 3635449709080913150277119)
                      ·
                        rfl

theorem cell23_7080013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 4, 2, 2, 3].length) (baseStart_7080013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7080013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7080013 prefixEnd_7080013 := by exact prefixLift 7080013
  have htrace : WordTrace (prefixWord ++ tailWord_7080013) baseStart_7080013 baseEnd_7080013 := by
    simpa [prefixWord, tailWord_7080013, baseEnd_7080013] using wordTrace_append hprefix tailTrace_7080013
  have hstable : (prefixWord ++ tailWord_7080013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7080013).length < 2 ^ (prefixWord ++ tailWord_7080013).sum := by decide
  have hdescent : baseEnd_7080013 < baseStart_7080013 := by decide
  rcases family_descends (prefixWord ++ tailWord_7080013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7080039 : List Nat := [1, 1, 5, 1, 1, 2, 1, 1, 2, 1, 7]
def baseStart_7080039 : Nat := 118140960795 + 7080039 * 2 ^ 59
def prefixEnd_7080039 : Nat := 4983230072969 + 3 ^ 40 * 7080039 * 2
def baseEnd_7080039 : Nat := 3635463059577930048551999

theorem tailTrace_7080039 : CollatzResearch.WordTrace tailWord_7080039 prefixEnd_7080039 3635463059577930048551999 := by
  unfold tailWord_7080039
  simp only [CollatzResearch.WordTrace]
  refine ⟨258230236797235352239019171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172153491198156901492679447 258230236797235352239019171)
  ·
    refine ⟨387345355195853028358528757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258230236797235352239019171 387345355195853028358528757)
    ·
      refine ⟨36313627049611221408612071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 387345355195853028358528757 36313627049611221408612071)
      ·
        refine ⟨54470440574416832112918107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36313627049611221408612071 54470440574416832112918107)
        ·
          refine ⟨81705660861625248169377161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54470440574416832112918107 81705660861625248169377161)
          ·
            refine ⟨61279245646218936127032871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81705660861625248169377161 61279245646218936127032871)
            ·
              refine ⟨91918868469328404190549307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61279245646218936127032871 91918868469328404190549307)
              ·
                refine ⟨137878302703992606285823961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91918868469328404190549307 137878302703992606285823961)
                ·
                  refine ⟨103408727027994454714367971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 137878302703992606285823961 103408727027994454714367971)
                  ·
                    refine ⟨155113090541991682071551957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 103408727027994454714367971 155113090541991682071551957)
                    ·
                      refine ⟨3635463059577930048551999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 155113090541991682071551957 3635463059577930048551999)
                      ·
                        rfl

theorem cell23_7080039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 1, 2, 1, 7].length) (baseStart_7080039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7080039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7080039 prefixEnd_7080039 := by exact prefixLift 7080039
  have htrace : WordTrace (prefixWord ++ tailWord_7080039) baseStart_7080039 baseEnd_7080039 := by
    simpa [prefixWord, tailWord_7080039, baseEnd_7080039] using wordTrace_append hprefix tailTrace_7080039
  have hstable : (prefixWord ++ tailWord_7080039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7080039).length < 2 ^ (prefixWord ++ tailWord_7080039).sum := by decide
  have hdescent : baseEnd_7080039 < baseStart_7080039 := by decide
  rcases family_descends (prefixWord ++ tailWord_7080039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7080046 : List Nat := [4, 1, 2, 2, 1, 1, 1, 3, 3, 5]
def baseStart_7080046 : Nat := 118140960795 + 7080046 * 2 ^ 59
def prefixEnd_7080046 : Nat := 4983230072969 + 3 ^ 40 * 7080046 * 2
def baseEnd_7080046 : Nat := 1211822217980837173721489

theorem tailTrace_7080046 : CollatzResearch.WordTrace tailWord_7080046 prefixEnd_7080046 1211822217980837173721489 := by
  unfold tailWord_7080046
  simp only [CollatzResearch.WordTrace]
  refine ⟨32278811513526249054315499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172153661405473328289682661 32278811513526249054315499)
  ·
    refine ⟨48418217270289373581473249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32278811513526249054315499 48418217270289373581473249)
    ·
      refine ⟨36313662952717030186104937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48418217270289373581473249 36313662952717030186104937)
      ·
        refine ⟨27235247214537772639578703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36313662952717030186104937 27235247214537772639578703)
        ·
          refine ⟨40852870821806658959368055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27235247214537772639578703 40852870821806658959368055)
          ·
            refine ⟨61279306232709988439052083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40852870821806658959368055 61279306232709988439052083)
            ·
              refine ⟨91918959349064982658578125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61279306232709988439052083 91918959349064982658578125)
              ·
                refine ⟨34469609755899368496966797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91918959349064982658578125 34469609755899368496966797)
                ·
                  refine ⟨12926103658462263186362549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34469609755899368496966797 12926103658462263186362549)
                  ·
                    refine ⟨1211822217980837173721489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12926103658462263186362549 1211822217980837173721489)
                    ·
                      rfl

theorem cell23_7080046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 3, 3, 5].length) (baseStart_7080046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7080046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7080046 prefixEnd_7080046 := by exact prefixLift 7080046
  have htrace : WordTrace (prefixWord ++ tailWord_7080046) baseStart_7080046 baseEnd_7080046 := by
    simpa [prefixWord, tailWord_7080046, baseEnd_7080046] using wordTrace_append hprefix tailTrace_7080046
  have hstable : (prefixWord ++ tailWord_7080046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7080046).length < 2 ^ (prefixWord ++ tailWord_7080046).sum := by decide
  have hdescent : baseEnd_7080046 < baseStart_7080046 := by decide
  rcases family_descends (prefixWord ++ tailWord_7080046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7080060 : List Nat := [2, 2, 2, 1, 1, 4, 1, 5, 1, 1, 3]
def baseStart_7080060 : Nat := 118140960795 + 7080060 * 2 ^ 59
def prefixEnd_7080060 : Nat := 4983230072969 + 3 ^ 40 * 7080060 * 2
def baseEnd_7080060 : Nat := 3635473842671674466389403

theorem tailTrace_7080060 : CollatzResearch.WordTrace tailWord_7080060 prefixEnd_7080060 3635473842671674466389403 := by
  unfold tailWord_7080060
  simp only [CollatzResearch.WordTrace]
  refine ⟨129115501365079636412766817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172154001820106181883689089 129115501365079636412766817)
  ·
    refine ⟨96836626023809727309575113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129115501365079636412766817 96836626023809727309575113)
    ·
      refine ⟨72627469517857295482181335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96836626023809727309575113 72627469517857295482181335)
      ·
        refine ⟨108941204276785943223272003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72627469517857295482181335 108941204276785943223272003)
        ·
          refine ⟨163411806415178914834908005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108941204276785943223272003 163411806415178914834908005)
          ·
            refine ⟨30639713702846046531545251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 163411806415178914834908005 30639713702846046531545251)
            ·
              refine ⟨45959570554269069797317877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30639713702846046531545251 45959570554269069797317877)
              ·
                refine ⟨4308709739462725293498551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45959570554269069797317877 4308709739462725293498551)
                ·
                  refine ⟨6463064609194087940247827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4308709739462725293498551 6463064609194087940247827)
                  ·
                    refine ⟨9694596913791131910371741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6463064609194087940247827 9694596913791131910371741)
                    ·
                      refine ⟨3635473842671674466389403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9694596913791131910371741 3635473842671674466389403)
                      ·
                        rfl

theorem cell23_7080060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 5, 1, 1, 3].length) (baseStart_7080060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7080060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7080060 prefixEnd_7080060 := by exact prefixLift 7080060
  have htrace : WordTrace (prefixWord ++ tailWord_7080060) baseStart_7080060 baseEnd_7080060 := by
    simpa [prefixWord, tailWord_7080060, baseEnd_7080060] using wordTrace_append hprefix tailTrace_7080060
  have hstable : (prefixWord ++ tailWord_7080060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7080060).length < 2 ^ (prefixWord ++ tailWord_7080060).sum := by decide
  have hdescent : baseEnd_7080060 < baseStart_7080060 := by decide
  rcases family_descends (prefixWord ++ tailWord_7080060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7080093 : List Nat := [1, 4, 2, 1, 1, 5, 1, 1, 1, 6]
def baseStart_7080093 : Nat := 118140960795 + 7080093 * 2 ^ 59
def prefixEnd_7080093 : Nat := 4983230072969 + 3 ^ 40 * 7080093 * 2
def baseEnd_7080093 : Nat := 1211830262511090945758917

theorem tailTrace_7080093 : CollatzResearch.WordTrace tailWord_7080093 prefixEnd_7080093 1211830262511090945758917 := by
  unfold tailWord_7080093
  simp only [CollatzResearch.WordTrace]
  refine ⟨258232206339039719461484933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172154804226026479640989955 258232206339039719461484933)
  ·
    refine ⟨48418538688569947399028425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 258232206339039719461484933 48418538688569947399028425)
    ·
      refine ⟨36313904016427460549271319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48418538688569947399028425 36313904016427460549271319)
      ·
        refine ⟨54470856024641190823906979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36313904016427460549271319 54470856024641190823906979)
        ·
          refine ⟨81706284036961786235860469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54470856024641190823906979 81706284036961786235860469)
          ·
            refine ⟨7659964128465167459611919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 81706284036961786235860469 7659964128465167459611919)
            ·
              refine ⟨11489946192697751189417879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7659964128465167459611919 11489946192697751189417879)
              ·
                refine ⟨17234919289046626784126819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11489946192697751189417879 17234919289046626784126819)
                ·
                  refine ⟨25852378933569940176190229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17234919289046626784126819 25852378933569940176190229)
                  ·
                    refine ⟨1211830262511090945758917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25852378933569940176190229 1211830262511090945758917)
                    ·
                      rfl

theorem cell23_7080093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 1, 1, 1, 6].length) (baseStart_7080093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7080093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7080093 prefixEnd_7080093 := by exact prefixLift 7080093
  have htrace : WordTrace (prefixWord ++ tailWord_7080093) baseStart_7080093 baseEnd_7080093 := by
    simpa [prefixWord, tailWord_7080093, baseEnd_7080093] using wordTrace_append hprefix tailTrace_7080093
  have hstable : (prefixWord ++ tailWord_7080093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7080093).length < 2 ^ (prefixWord ++ tailWord_7080093).sum := by decide
  have hdescent : baseEnd_7080093 < baseStart_7080093 := by decide
  rcases family_descends (prefixWord ++ tailWord_7080093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7080096 : List Nat := [2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 6]
def baseStart_7080096 : Nat := 118140960795 + 7080096 * 2 ^ 59
def prefixEnd_7080096 : Nat := 4983230072969 + 3 ^ 40 * 7080096 * 2
def baseEnd_7080096 : Nat := 3635492327975236325539237

theorem tailTrace_7080096 : CollatzResearch.WordTrace tailWord_7080096 prefixEnd_7080096 3635492327975236325539237 := by
  unfold tailWord_7080096
  simp only [CollatzResearch.WordTrace]
  refine ⟨129116157879014425486922071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172154877172019233982562761 129116157879014425486922071)
  ·
    refine ⟨193674236818521638230383107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129116157879014425486922071 193674236818521638230383107)
    ·
      refine ⟨290511355227782457345574661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193674236818521638230383107 290511355227782457345574661)
      ·
        refine ⟨54470879105209210752295249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 290511355227782457345574661 54470879105209210752295249)
        ·
          refine ⟨40853159328906908064221437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54470879105209210752295249 40853159328906908064221437)
          ·
            refine ⟨15319934748340090524083039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40853159328906908064221437 15319934748340090524083039)
            ·
              refine ⟨22979902122510135786124559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15319934748340090524083039 22979902122510135786124559)
              ·
                refine ⟨34469853183765203679186839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22979902122510135786124559 34469853183765203679186839)
                ·
                  refine ⟨51704779775647805518780259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34469853183765203679186839 51704779775647805518780259)
                  ·
                    refine ⟨77557169663471708278170389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51704779775647805518780259 77557169663471708278170389)
                    ·
                      refine ⟨3635492327975236325539237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77557169663471708278170389 3635492327975236325539237)
                      ·
                        rfl

theorem cell23_7080096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 6].length) (baseStart_7080096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7080096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7080096 prefixEnd_7080096 := by exact prefixLift 7080096
  have htrace : WordTrace (prefixWord ++ tailWord_7080096) baseStart_7080096 baseEnd_7080096 := by
    simpa [prefixWord, tailWord_7080096, baseEnd_7080096] using wordTrace_append hprefix tailTrace_7080096
  have hstable : (prefixWord ++ tailWord_7080096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7080096).length < 2 ^ (prefixWord ++ tailWord_7080096).sum := by decide
  have hdescent : baseEnd_7080096 < baseStart_7080096 := by decide
  rcases family_descends (prefixWord ++ tailWord_7080096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7080100 : List Nat := [2, 3, 1, 2, 4, 1, 2, 2, 1, 1, 4]
def baseStart_7080100 : Nat := 118140960795 + 7080100 * 2 ^ 59
def prefixEnd_7080100 : Nat := 4983230072969 + 3 ^ 40 * 7080100 * 2
def baseEnd_7080100 : Nat := 3635494381897854309889219

theorem tailTrace_7080100 : CollatzResearch.WordTrace tailWord_7080100 prefixEnd_7080100 3635494381897854309889219 := by
  unfold tailWord_7080100
  simp only [CollatzResearch.WordTrace]
  refine ⟨129116230825007179828494877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172154974433342906437993169 129116230825007179828494877)
  ·
    refine ⟨48418586559377692435685579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129116230825007179828494877 48418586559377692435685579)
    ·
      refine ⟨72627879839066538653528369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48418586559377692435685579 72627879839066538653528369)
      ·
        refine ⟨54470909879299903990146277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72627879839066538653528369 54470909879299903990146277)
        ·
          refine ⟨10213295602368731998152427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54470909879299903990146277 10213295602368731998152427)
          ·
            refine ⟨15319943403553097997228641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10213295602368731998152427 15319943403553097997228641)
            ·
              refine ⟨11489957552664823497921481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15319943403553097997228641 11489957552664823497921481)
              ·
                refine ⟨8617468164498617623441111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11489957552664823497921481 8617468164498617623441111)
                ·
                  refine ⟨12926202246747926435161667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8617468164498617623441111 12926202246747926435161667)
                  ·
                    refine ⟨19389303370121889652742501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12926202246747926435161667 19389303370121889652742501)
                    ·
                      refine ⟨3635494381897854309889219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19389303370121889652742501 3635494381897854309889219)
                      ·
                        rfl

theorem cell23_7080100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 2, 2, 1, 1, 4].length) (baseStart_7080100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7080100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7080100 prefixEnd_7080100 := by exact prefixLift 7080100
  have htrace : WordTrace (prefixWord ++ tailWord_7080100) baseStart_7080100 baseEnd_7080100 := by
    simpa [prefixWord, tailWord_7080100, baseEnd_7080100] using wordTrace_append hprefix tailTrace_7080100
  have hstable : (prefixWord ++ tailWord_7080100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7080100).length < 2 ^ (prefixWord ++ tailWord_7080100).sum := by decide
  have hdescent : baseEnd_7080100 < baseStart_7080100 := by decide
  rcases family_descends (prefixWord ++ tailWord_7080100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7080130 : List Nat := [3, 5, 1, 1, 1, 1, 1, 2, 1, 1, 6]
def baseStart_7080130 : Nat := 118140960795 + 7080130 * 2 ^ 59
def prefixEnd_7080130 : Nat := 4983230072969 + 3 ^ 40 * 7080130 * 2
def baseEnd_7080130 : Nat := 3635509786317489192514081

theorem tailTrace_7080130 : CollatzResearch.WordTrace tailWord_7080130 prefixEnd_7080130 3635509786317489192514081 := by
  unfold tailWord_7080130
  simp only [CollatzResearch.WordTrace]
  refine ⟨64558388959976418695145461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172155703893270449853721229 64558388959976418695145461)
  ·
    refine ⟨6052348964997789252669887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 64558388959976418695145461 6052348964997789252669887)
    ·
      refine ⟨9078523447496683879004831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6052348964997789252669887 9078523447496683879004831)
      ·
        refine ⟨13617785171245025818507247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9078523447496683879004831 13617785171245025818507247)
        ·
          refine ⟨20426677756867538727760871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13617785171245025818507247 20426677756867538727760871)
          ·
            refine ⟨30640016635301308091641307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20426677756867538727760871 30640016635301308091641307)
            ·
              refine ⟨45960024952951962137461961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30640016635301308091641307 45960024952951962137461961)
              ·
                refine ⟨34470018714713971603096471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45960024952951962137461961 34470018714713971603096471)
                ·
                  refine ⟨51705028072070957404644707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34470018714713971603096471 51705028072070957404644707)
                  ·
                    refine ⟨77557542108106436106967061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51705028072070957404644707 77557542108106436106967061)
                    ·
                      refine ⟨3635509786317489192514081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77557542108106436106967061 3635509786317489192514081)
                      ·
                        rfl

theorem cell23_7080130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_7080130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7080130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7080130 prefixEnd_7080130 := by exact prefixLift 7080130
  have htrace : WordTrace (prefixWord ++ tailWord_7080130) baseStart_7080130 baseEnd_7080130 := by
    simpa [prefixWord, tailWord_7080130, baseEnd_7080130] using wordTrace_append hprefix tailTrace_7080130
  have hstable : (prefixWord ++ tailWord_7080130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7080130).length < 2 ^ (prefixWord ++ tailWord_7080130).sum := by decide
  have hdescent : baseEnd_7080130 < baseStart_7080130 := by decide
  rcases family_descends (prefixWord ++ tailWord_7080130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7080133 : List Nat := [1, 3, 1, 1, 1, 1, 6, 1, 4, 1, 3]
def baseStart_7080133 : Nat := 118140960795 + 7080133 * 2 ^ 59
def prefixEnd_7080133 : Nat := 4983230072969 + 3 ^ 40 * 7080133 * 2
def baseEnd_7080133 : Nat := 3635511326759452680776567

theorem tailTrace_7080133 : CollatzResearch.WordTrace tailWord_7080133 prefixEnd_7080133 3635511326759452680776567 := by
  unfold tailWord_7080133
  simp only [CollatzResearch.WordTrace]
  refine ⟨258233665258894806292941053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172155776839263204195294035 258233665258894806292941053)
  ·
    refine ⟨96837624472085552359852895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 258233665258894806292941053 96837624472085552359852895)
    ·
      refine ⟨145256436708128328539779343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96837624472085552359852895 145256436708128328539779343)
      ·
        refine ⟨217884655062192492809669015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145256436708128328539779343 217884655062192492809669015)
        ·
          refine ⟨326826982593288739214503523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217884655062192492809669015 326826982593288739214503523)
          ·
            refine ⟨490240473889933108821755285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 326826982593288739214503523 490240473889933108821755285)
            ·
              refine ⟨22980022213590614476019779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 490240473889933108821755285 22980022213590614476019779)
              ·
                refine ⟨34470033320385921714029669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22980022213590614476019779 34470033320385921714029669)
                ·
                  refine ⟨6463131247572360321380563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34470033320385921714029669 6463131247572360321380563)
                  ·
                    refine ⟨9694696871358540482070845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6463131247572360321380563 9694696871358540482070845)
                    ·
                      refine ⟨3635511326759452680776567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9694696871358540482070845 3635511326759452680776567)
                      ·
                        rfl

theorem cell23_7080133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 1, 4, 1, 3].length) (baseStart_7080133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7080133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7080133 prefixEnd_7080133 := by exact prefixLift 7080133
  have htrace : WordTrace (prefixWord ++ tailWord_7080133) baseStart_7080133 baseEnd_7080133 := by
    simpa [prefixWord, tailWord_7080133, baseEnd_7080133] using wordTrace_append hprefix tailTrace_7080133
  have hstable : (prefixWord ++ tailWord_7080133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7080133).length < 2 ^ (prefixWord ++ tailWord_7080133).sum := by decide
  have hdescent : baseEnd_7080133 < baseStart_7080133 := by decide
  rcases family_descends (prefixWord ++ tailWord_7080133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7080143 : List Nat := [1, 1, 2, 1, 1, 3, 4, 2, 3, 3, 2]
def baseStart_7080143 : Nat := 118140960795 + 7080143 * 2 ^ 59
def prefixEnd_7080143 : Nat := 4983230072969 + 3 ^ 40 * 7080143 * 2
def baseEnd_7080143 : Nat := 3635516461565997641651521

theorem tailTrace_7080143 : CollatzResearch.WordTrace tailWord_7080143 prefixEnd_7080143 3635516461565997641651521 := by
  unfold tailWord_7080143
  simp only [CollatzResearch.WordTrace]
  refine ⟨258234029988858578000805083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172156019992572385333870055 258234029988858578000805083)
  ·
    refine ⟨387351044983287867001207625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258234029988858578000805083 387351044983287867001207625)
    ·
      refine ⟨290513283737465900250905719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 387351044983287867001207625 290513283737465900250905719)
      ·
        refine ⟨435769925606198850376358579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290513283737465900250905719 435769925606198850376358579)
        ·
          refine ⟨653654888409298275564537869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 435769925606198850376358579 653654888409298275564537869)
          ·
            refine ⟨245120583153486853336701701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 653654888409298275564537869 245120583153486853336701701)
            ·
              refine ⟨45960109341278785000631569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 245120583153486853336701701 45960109341278785000631569)
              ·
                refine ⟨34470082005959088750473677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45960109341278785000631569 34470082005959088750473677)
                ·
                  refine ⟨12926280752234658281427629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34470082005959088750473677 12926280752234658281427629)
                  ·
                    refine ⟨4847355282087996855535361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12926280752234658281427629 4847355282087996855535361)
                    ·
                      refine ⟨3635516461565997641651521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4847355282087996855535361 3635516461565997641651521)
                      ·
                        rfl

theorem cell23_7080143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 2, 3, 3, 2].length) (baseStart_7080143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7080143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7080143 prefixEnd_7080143 := by exact prefixLift 7080143
  have htrace : WordTrace (prefixWord ++ tailWord_7080143) baseStart_7080143 baseEnd_7080143 := by
    simpa [prefixWord, tailWord_7080143, baseEnd_7080143] using wordTrace_append hprefix tailTrace_7080143
  have hstable : (prefixWord ++ tailWord_7080143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7080143).length < 2 ^ (prefixWord ++ tailWord_7080143).sum := by decide
  have hdescent : baseEnd_7080143 < baseStart_7080143 := by decide
  rcases family_descends (prefixWord ++ tailWord_7080143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7080176 : List Nat := [2, 1, 1, 1, 3, 1, 1, 2, 4, 4, 3]
def baseStart_7080176 : Nat := 118140960795 + 7080176 * 2 ^ 59
def prefixEnd_7080176 : Nat := 4983230072969 + 3 ^ 40 * 7080176 * 2
def baseEnd_7080176 : Nat := 3635533406427596012538869

theorem tailTrace_7080176 : CollatzResearch.WordTrace tailWord_7080176 prefixEnd_7080176 3635533406427596012538869 := by
  unfold tailWord_7080176
  simp only [CollatzResearch.WordTrace]
  refine ⟨129117616798869512318378191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172156822398492683091170921 129117616798869512318378191)
  ·
    refine ⟨193676425198304268477567287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129117616798869512318378191 193676425198304268477567287)
    ·
      refine ⟨290514637797456402716350931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193676425198304268477567287 290514637797456402716350931)
      ·
        refine ⟨435771956696184604074526397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290514637797456402716350931 435771956696184604074526397)
        ·
          refine ⟨163414483761069226527947399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 435771956696184604074526397 163414483761069226527947399)
          ·
            refine ⟨245121725641603839791921099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163414483761069226527947399 245121725641603839791921099)
            ·
              refine ⟨367682588462405759687881649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 245121725641603839791921099 367682588462405759687881649)
              ·
                refine ⟨275761941346804319765911237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 367682588462405759687881649 275761941346804319765911237)
                ·
                  refine ⟨51705364002525809956108357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 275761941346804319765911237 51705364002525809956108357)
                  ·
                    refine ⟨9694755750473589366770317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51705364002525809956108357 9694755750473589366770317)
                    ·
                      refine ⟨3635533406427596012538869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9694755750473589366770317 3635533406427596012538869)
                      ·
                        rfl

theorem cell23_7080176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 4, 4, 3].length) (baseStart_7080176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7080176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7080176 prefixEnd_7080176 := by exact prefixLift 7080176
  have htrace : WordTrace (prefixWord ++ tailWord_7080176) baseStart_7080176 baseEnd_7080176 := by
    simpa [prefixWord, tailWord_7080176, baseEnd_7080176] using wordTrace_append hprefix tailTrace_7080176
  have hstable : (prefixWord ++ tailWord_7080176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7080176).length < 2 ^ (prefixWord ++ tailWord_7080176).sum := by decide
  have hdescent : baseEnd_7080176 < baseStart_7080176 := by decide
  rcases family_descends (prefixWord ++ tailWord_7080176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7080190 : List Nat := [4, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2]
def baseStart_7080190 : Nat := 118140960795 + 7080190 * 2 ^ 59
def prefixEnd_7080190 : Nat := 4983230072969 + 3 ^ 40 * 7080190 * 2
def baseEnd_7080190 : Nat := 3635540595156758957763805

theorem tailTrace_7080190 : CollatzResearch.WordTrace tailWord_7080190 prefixEnd_7080190 3635540595156758957763805 := by
  unfold tailWord_7080190
  simp only [CollatzResearch.WordTrace]
  refine ⟨32279468027461038128470753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172157162813125536685177349 32279468027461038128470753)
  ·
    refine ⟨24209601020595778596353065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32279468027461038128470753 24209601020595778596353065)
    ·
      refine ⟨18157200765446833947264799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24209601020595778596353065 18157200765446833947264799)
      ·
        refine ⟨27235801148170250920897199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18157200765446833947264799 27235801148170250920897199)
        ·
          refine ⟨40853701722255376381345799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27235801148170250920897199 40853701722255376381345799)
          ·
            refine ⟨61280552583383064572018699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40853701722255376381345799 61280552583383064572018699)
            ·
              refine ⟨91920828875074596858028049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61280552583383064572018699 91920828875074596858028049)
              ·
                refine ⟨68940621656305947643521037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91920828875074596858028049 68940621656305947643521037)
                ·
                  refine ⟨25852733121114730366320389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68940621656305947643521037 25852733121114730366320389)
                  ·
                    refine ⟨4847387460209011943685073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25852733121114730366320389 4847387460209011943685073)
                    ·
                      refine ⟨3635540595156758957763805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4847387460209011943685073 3635540595156758957763805)
                      ·
                        rfl

theorem cell23_7080190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2].length) (baseStart_7080190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7080190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7080190 prefixEnd_7080190 := by exact prefixLift 7080190
  have htrace : WordTrace (prefixWord ++ tailWord_7080190) baseStart_7080190 baseEnd_7080190 := by
    simpa [prefixWord, tailWord_7080190, baseEnd_7080190] using wordTrace_append hprefix tailTrace_7080190
  have hstable : (prefixWord ++ tailWord_7080190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7080190).length < 2 ^ (prefixWord ++ tailWord_7080190).sum := by decide
  have hdescent : baseEnd_7080190 < baseStart_7080190 := by decide
  rcases family_descends (prefixWord ++ tailWord_7080190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7080236 : List Nat := [2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 5]
def baseStart_7080236 : Nat := 118140960795 + 7080236 * 2 ^ 59
def prefixEnd_7080236 : Nat := 4983230072969 + 3 ^ 40 * 7080236 * 2
def baseEnd_7080236 : Nat := 3635564215266865777788593

theorem tailTrace_7080236 : CollatzResearch.WordTrace tailWord_7080236 prefixEnd_7080236 3635564215266865777788593 := by
  unfold tailWord_7080236
  simp only [CollatzResearch.WordTrace]
  refine ⟨129118710988760827441970281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172158281318347769922627041 129118710988760827441970281)
  ·
    refine ⟨96839033241570620581477711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129118710988760827441970281 96839033241570620581477711)
    ·
      refine ⟨145258549862355930872216567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96839033241570620581477711 145258549862355930872216567)
      ·
        refine ⟨217887824793533896308324851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145258549862355930872216567 217887824793533896308324851)
        ·
          refine ⟨326831737190300844462487277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217887824793533896308324851 326831737190300844462487277)
          ·
            refine ⟨122561901446362816673432729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 326831737190300844462487277 122561901446362816673432729)
            ·
              refine ⟨91921426084772112505074547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122561901446362816673432729 91921426084772112505074547)
              ·
                refine ⟨137882139127158168757611821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91921426084772112505074547 137882139127158168757611821)
                ·
                  refine ⟨51705802172684313284104433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 137882139127158168757611821 51705802172684313284104433)
                  ·
                    refine ⟨38779351629513234963078325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51705802172684313284104433 38779351629513234963078325)
                    ·
                      refine ⟨3635564215266865777788593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38779351629513234963078325 3635564215266865777788593)
                      ·
                        rfl

theorem cell23_7080236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 5].length) (baseStart_7080236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7080236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7080236 prefixEnd_7080236 := by exact prefixLift 7080236
  have htrace : WordTrace (prefixWord ++ tailWord_7080236) baseStart_7080236 baseEnd_7080236 := by
    simpa [prefixWord, tailWord_7080236, baseEnd_7080236] using wordTrace_append hprefix tailTrace_7080236
  have hstable : (prefixWord ++ tailWord_7080236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7080236).length < 2 ^ (prefixWord ++ tailWord_7080236).sum := by decide
  have hdescent : baseEnd_7080236 < baseStart_7080236 := by decide
  rcases family_descends (prefixWord ++ tailWord_7080236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7080241 : List Nat := [1, 2, 2, 3, 5, 1, 1, 2, 2, 2, 2]
def baseStart_7080241 : Nat := 118140960795 + 7080241 * 2 ^ 59
def prefixEnd_7080241 : Nat := 4983230072969 + 3 ^ 40 * 7080241 * 2
def baseEnd_7080241 : Nat := 3635566782670138258226071

theorem tailTrace_7080241 : CollatzResearch.WordTrace tailWord_7080241 prefixEnd_7080241 3635566782670138258226071 := by
  unfold tailWord_7080241
  simp only [CollatzResearch.WordTrace]
  refine ⟨258237604342503540737872577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172158402895002360491915051 258237604342503540737872577)
  ·
    refine ⟨193678203256877655553404433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258237604342503540737872577 193678203256877655553404433)
    ·
      refine ⟨145258652442658241665053325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193678203256877655553404433 145258652442658241665053325)
      ·
        refine ⟨54471994665996840624394997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145258652442658241665053325 54471994665996840624394997)
        ·
          refine ⟨5106749499937203808537031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54471994665996840624394997 5106749499937203808537031)
          ·
            refine ⟨7660124249905805712805547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5106749499937203808537031 7660124249905805712805547)
            ·
              refine ⟨11490186374858708569208321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7660124249905805712805547 11490186374858708569208321)
              ·
                refine ⟨8617639781144031426906241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11490186374858708569208321 8617639781144031426906241)
                ·
                  refine ⟨6463229835858023570179681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8617639781144031426906241 6463229835858023570179681)
                  ·
                    refine ⟨4847422376893517677634761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6463229835858023570179681 4847422376893517677634761)
                    ·
                      refine ⟨3635566782670138258226071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4847422376893517677634761 3635566782670138258226071)
                      ·
                        rfl

theorem cell23_7080241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 1, 2, 2, 2, 2].length) (baseStart_7080241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7080241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7080241 prefixEnd_7080241 := by exact prefixLift 7080241
  have htrace : WordTrace (prefixWord ++ tailWord_7080241) baseStart_7080241 baseEnd_7080241 := by
    simpa [prefixWord, tailWord_7080241, baseEnd_7080241] using wordTrace_append hprefix tailTrace_7080241
  have hstable : (prefixWord ++ tailWord_7080241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7080241).length < 2 ^ (prefixWord ++ tailWord_7080241).sum := by decide
  have hdescent : baseEnd_7080241 < baseStart_7080241 := by decide
  rcases family_descends (prefixWord ++ tailWord_7080241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7080380 : List Nat := [2, 2, 2, 4, 1, 1, 1, 3, 1, 6]
def baseStart_7080380 : Nat := 118140960795 + 7080380 * 2 ^ 59
def prefixEnd_7080380 : Nat := 4983230072969 + 3 ^ 40 * 7080380 * 2
def baseEnd_7080380 : Nat := 1211879385493704404795977

theorem tailTrace_7080380 : CollatzResearch.WordTrace tailWord_7080380 prefixEnd_7080380 1211879385493704404795977 := by
  unfold tailWord_7080380
  simp only [CollatzResearch.WordTrace]
  refine ⟨129121337044499983738591297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172161782725999978318121729 129121337044499983738591297)
  ·
    refine ⟨96841002783374987803943473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129121337044499983738591297 96841002783374987803943473)
    ·
      refine ⟨72630752087531240852957605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96841002783374987803943473 72630752087531240852957605)
      ·
        refine ⟨13618266016412107659929551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72630752087531240852957605 13618266016412107659929551)
        ·
          refine ⟨20427399024618161489894327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13618266016412107659929551 20427399024618161489894327)
          ·
            refine ⟨30641098536927242234841491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20427399024618161489894327 30641098536927242234841491)
            ·
              refine ⟨45961647805390863352262237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30641098536927242234841491 45961647805390863352262237)
              ·
                refine ⟨17235617927021573757098339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45961647805390863352262237 17235617927021573757098339)
                ·
                  refine ⟨25853426890532360635647509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17235617927021573757098339 25853426890532360635647509)
                  ·
                    refine ⟨1211879385493704404795977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25853426890532360635647509 1211879385493704404795977)
                    ·
                      rfl

theorem cell23_7080380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 3, 1, 6].length) (baseStart_7080380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7080380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7080380 prefixEnd_7080380 := by exact prefixLift 7080380
  have htrace : WordTrace (prefixWord ++ tailWord_7080380) baseStart_7080380 baseEnd_7080380 := by
    simpa [prefixWord, tailWord_7080380, baseEnd_7080380] using wordTrace_append hprefix tailTrace_7080380
  have hstable : (prefixWord ++ tailWord_7080380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7080380).length < 2 ^ (prefixWord ++ tailWord_7080380).sum := by decide
  have hdescent : baseEnd_7080380 < baseStart_7080380 := by decide
  rcases family_descends (prefixWord ++ tailWord_7080380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7080403 : List Nat := [1, 1, 1, 2, 1, 1, 1, 1, 4, 7, 3]
def baseStart_7080403 : Nat := 118140960795 + 7080403 * 2 ^ 59
def prefixEnd_7080403 : Nat := 4983230072969 + 3 ^ 40 * 7080403 * 2
def baseEnd_7080403 : Nat := 3635649966536166624400325

theorem tailTrace_7080403 : CollatzResearch.WordTrace tailWord_7080403 prefixEnd_7080403 3635649966536166624400325 := by
  unfold tailWord_7080403
  simp only [CollatzResearch.WordTrace]
  refine ⟨258243512967916642405269863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172162341978611094936846575 258243512967916642405269863)
  ·
    refine ⟨387365269451874963607904795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258243512967916642405269863 387365269451874963607904795)
    ·
      refine ⟨581047904177812445411857193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 387365269451874963607904795 581047904177812445411857193)
      ·
        refine ⟨435785928133359334058892895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 581047904177812445411857193 435785928133359334058892895)
        ·
          refine ⟨653678892200039001088339343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 435785928133359334058892895 653678892200039001088339343)
          ·
            refine ⟨980518338300058501632509015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 653678892200039001088339343 980518338300058501632509015)
            ·
              refine ⟨1470777507450087752448763523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 980518338300058501632509015 1470777507450087752448763523)
              ·
                refine ⟨2206166261175131628673145285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1470777507450087752448763523 2206166261175131628673145285)
                ·
                  refine ⟨413656173970337180376214741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2206166261175131628673145285 413656173970337180376214741)
                  ·
                    refine ⟨9695066577429777665067533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 413656173970337180376214741 9695066577429777665067533)
                    ·
                      refine ⟨3635649966536166624400325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9695066577429777665067533 3635649966536166624400325)
                      ·
                        rfl

theorem cell23_7080403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 7, 3].length) (baseStart_7080403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7080403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7080403 prefixEnd_7080403 := by exact prefixLift 7080403
  have htrace : WordTrace (prefixWord ++ tailWord_7080403) baseStart_7080403 baseEnd_7080403 := by
    simpa [prefixWord, tailWord_7080403, baseEnd_7080403] using wordTrace_append hprefix tailTrace_7080403
  have hstable : (prefixWord ++ tailWord_7080403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7080403).length < 2 ^ (prefixWord ++ tailWord_7080403).sum := by decide
  have hdescent : baseEnd_7080403 < baseStart_7080403 := by decide
  rcases family_descends (prefixWord ++ tailWord_7080403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7080404 : List Nat := [2, 4, 1, 2, 2, 1, 4, 1, 1, 1, 4]
def baseStart_7080404 : Nat := 118140960795 + 7080404 * 2 ^ 59
def prefixEnd_7080404 : Nat := 4983230072969 + 3 ^ 40 * 7080404 * 2
def baseEnd_7080404 : Nat := 3635650480016821120487821

theorem tailTrace_7080404 : CollatzResearch.WordTrace tailWord_7080404 prefixEnd_7080404 3635650480016821120487821 := by
  unfold tailWord_7080404
  simp only [CollatzResearch.WordTrace]
  refine ⟨129121774720456509788028133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172162366293942013050704177 129121774720456509788028133)
  ·
    refine ⟨24210332760085595585255275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 129121774720456509788028133 24210332760085595585255275)
    ·
      refine ⟨36315499140128393377882913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24210332760085595585255275 36315499140128393377882913)
      ·
        refine ⟨27236624355096295033412185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36315499140128393377882913 27236624355096295033412185)
        ·
          refine ⟨20427468266322221275059139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27236624355096295033412185 20427468266322221275059139)
          ·
            refine ⟨30641202399483331912588709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20427468266322221275059139 30641202399483331912588709)
            ·
              refine ⟨5745225449903124733610383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30641202399483331912588709 5745225449903124733610383)
              ·
                refine ⟨8617838174854687100415575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5745225449903124733610383 8617838174854687100415575)
                ·
                  refine ⟨12926757262282030650623363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8617838174854687100415575 12926757262282030650623363)
                  ·
                    refine ⟨19390135893423045975935045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12926757262282030650623363 19390135893423045975935045)
                    ·
                      refine ⟨3635650480016821120487821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19390135893423045975935045 3635650480016821120487821)
                      ·
                        rfl

theorem cell23_7080404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 4, 1, 1, 1, 4].length) (baseStart_7080404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7080404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7080404 prefixEnd_7080404 := by exact prefixLift 7080404
  have htrace : WordTrace (prefixWord ++ tailWord_7080404) baseStart_7080404 baseEnd_7080404 := by
    simpa [prefixWord, tailWord_7080404, baseEnd_7080404] using wordTrace_append hprefix tailTrace_7080404
  have hstable : (prefixWord ++ tailWord_7080404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7080404).length < 2 ^ (prefixWord ++ tailWord_7080404).sum := by decide
  have hdescent : baseEnd_7080404 < baseStart_7080404 := by decide
  rcases family_descends (prefixWord ++ tailWord_7080404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7080421 : List Nat := [1, 3, 1, 5, 2, 1, 2, 1, 3, 2, 2]
def baseStart_7080421 : Nat := 118140960795 + 7080421 * 2 ^ 59
def prefixEnd_7080421 : Nat := 4983230072969 + 3 ^ 40 * 7080421 * 2
def baseEnd_7080421 : Nat := 3635659209187947553975243

theorem tailTrace_7080421 : CollatzResearch.WordTrace tailWord_7080421 prefixEnd_7080421 3635659209187947553975243 := by
  unfold tailWord_7080421
  simp only [CollatzResearch.WordTrace]
  refine ⟨258244169481851431479425117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172162779654567620986283411 258244169481851431479425117)
  ·
    refine ⟨96841563555694286804784419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 258244169481851431479425117 96841563555694286804784419)
    ·
      refine ⟨145262345333541430207176629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96841563555694286804784419 145262345333541430207176629)
      ·
        refine ⟨13618344875019509081922809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 145262345333541430207176629 13618344875019509081922809)
        ·
          refine ⟨10213758656264631811442107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13618344875019509081922809 10213758656264631811442107)
          ·
            refine ⟨15320637984396947717163161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10213758656264631811442107 15320637984396947717163161)
            ·
              refine ⟨11490478488297710787872371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15320637984396947717163161 11490478488297710787872371)
              ·
                refine ⟨17235717732446566181808557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11490478488297710787872371 17235717732446566181808557)
                ·
                  refine ⟨6463394149667462318178209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17235717732446566181808557 6463394149667462318178209)
                  ·
                    refine ⟨4847545612250596738633657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6463394149667462318178209 4847545612250596738633657)
                    ·
                      refine ⟨3635659209187947553975243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4847545612250596738633657 3635659209187947553975243)
                      ·
                        rfl

theorem cell23_7080421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 2, 1, 3, 2, 2].length) (baseStart_7080421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7080421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7080421 prefixEnd_7080421 := by exact prefixLift 7080421
  have htrace : WordTrace (prefixWord ++ tailWord_7080421) baseStart_7080421 baseEnd_7080421 := by
    simpa [prefixWord, tailWord_7080421, baseEnd_7080421] using wordTrace_append hprefix tailTrace_7080421
  have hstable : (prefixWord ++ tailWord_7080421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7080421).length < 2 ^ (prefixWord ++ tailWord_7080421).sum := by decide
  have hdescent : baseEnd_7080421 < baseStart_7080421 := by decide
  rcases family_descends (prefixWord ++ tailWord_7080421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7080434 : List Nat := [3, 2, 1, 4, 2, 2, 1, 1, 1, 2, 4]
def baseStart_7080434 : Nat := 118140960795 + 7080434 * 2 ^ 59
def prefixEnd_7080434 : Nat := 4983230072969 + 3 ^ 40 * 7080434 * 2
def baseEnd_7080434 : Nat := 3635665884436456003112683

theorem tailTrace_7080434 : CollatzResearch.WordTrace tailWord_7080434 prefixEnd_7080434 3635665884436456003112683 := by
  unfold tailWord_7080434
  simp only [CollatzResearch.WordTrace]
  refine ⟨64561160907701083674912089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172163095753869556466432237 64561160907701083674912089)
  ·
    refine ⟨48420870680775812756184067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64561160907701083674912089 48420870680775812756184067)
    ·
      refine ⟨72631306021163719134276101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48420870680775812756184067 72631306021163719134276101)
      ·
        refine ⟨13618369878968197337676769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72631306021163719134276101 13618369878968197337676769)
        ·
          refine ⟨10213777409226148003257577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13618369878968197337676769 10213777409226148003257577)
          ·
            refine ⟨7660333056919611002443183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10213777409226148003257577 7660333056919611002443183)
            ·
              refine ⟨11490499585379416503664775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7660333056919611002443183 11490499585379416503664775)
              ·
                refine ⟨17235749378069124755497163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11490499585379416503664775 17235749378069124755497163)
                ·
                  refine ⟨25853624067103687133245745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17235749378069124755497163 25853624067103687133245745)
                  ·
                    refine ⟨19390218050327765349934309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25853624067103687133245745 19390218050327765349934309)
                    ·
                      refine ⟨3635665884436456003112683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19390218050327765349934309 3635665884436456003112683)
                      ·
                        rfl

theorem cell23_7080434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_7080434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7080434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7080434 prefixEnd_7080434 := by exact prefixLift 7080434
  have htrace : WordTrace (prefixWord ++ tailWord_7080434) baseStart_7080434 baseEnd_7080434 := by
    simpa [prefixWord, tailWord_7080434, baseEnd_7080434] using wordTrace_append hprefix tailTrace_7080434
  have hstable : (prefixWord ++ tailWord_7080434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7080434).length < 2 ^ (prefixWord ++ tailWord_7080434).sum := by decide
  have hdescent : baseEnd_7080434 < baseStart_7080434 := by decide
  rcases family_descends (prefixWord ++ tailWord_7080434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7080453 : List Nat := [1, 3, 1, 1, 2, 2, 2, 2, 1, 8]
def baseStart_7080453 : Nat := 118140960795 + 7080453 * 2 ^ 59
def prefixEnd_7080453 : Nat := 4983230072969 + 3 ^ 40 * 7080453 * 2
def baseEnd_7080453 : Nat := 1211891880189630476258365

theorem tailTrace_7080453 : CollatzResearch.WordTrace tailWord_7080453 prefixEnd_7080453 1211891880189630476258365 := by
  unfold tailWord_7080453
  simp only [CollatzResearch.WordTrace]
  refine ⟨258245336617735500944590013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172163557745157000629726675 258245336617735500944590013)
  ·
    refine ⟨96842001231650812854221255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 258245336617735500944590013 96842001231650812854221255)
    ·
      refine ⟨145263001847476219281331883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96842001231650812854221255 145263001847476219281331883)
      ·
        refine ⟨217894502771214328921997825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145263001847476219281331883 217894502771214328921997825)
        ·
          refine ⟨163420877078410746691498369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217894502771214328921997825 163420877078410746691498369)
          ·
            refine ⟨122565657808808060018623777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163420877078410746691498369 122565657808808060018623777)
            ·
              refine ⟨91924243356606045013967833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122565657808808060018623777 91924243356606045013967833)
              ·
                refine ⟨68943182517454533760475875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91924243356606045013967833 68943182517454533760475875)
                ·
                  refine ⟨103414773776181800640713813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68943182517454533760475875 103414773776181800640713813)
                  ·
                    refine ⟨1211891880189630476258365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 103414773776181800640713813 1211891880189630476258365)
                    ·
                      rfl

theorem cell23_7080453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 2, 1, 8].length) (baseStart_7080453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7080453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7080453 prefixEnd_7080453 := by exact prefixLift 7080453
  have htrace : WordTrace (prefixWord ++ tailWord_7080453) baseStart_7080453 baseEnd_7080453 := by
    simpa [prefixWord, tailWord_7080453, baseEnd_7080453] using wordTrace_append hprefix tailTrace_7080453
  have hstable : (prefixWord ++ tailWord_7080453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7080453).length < 2 ^ (prefixWord ++ tailWord_7080453).sum := by decide
  have hdescent : baseEnd_7080453 < baseStart_7080453 := by decide
  rcases family_descends (prefixWord ++ tailWord_7080453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7080455 : List Nat := [1, 1, 4, 3, 4, 1, 1, 3, 1, 2, 2]
def baseStart_7080455 : Nat := 118140960795 + 7080455 * 2 ^ 59
def prefixEnd_7080455 : Nat := 4983230072969 + 3 ^ 40 * 7080455 * 2
def baseEnd_7080455 : Nat := 3635676667530200420950087

theorem tailTrace_7080455 : CollatzResearch.WordTrace tailWord_7080455 prefixEnd_7080455 3635676667530200420950087 := by
  unfold tailWord_7080455
  simp only [CollatzResearch.WordTrace]
  refine ⟨258245409563728255286162819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172163606375818836857441879 258245409563728255286162819)
  ·
    refine ⟨387368114345592382929244229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258245409563728255286162819 387368114345592382929244229)
    ·
      refine ⟨72631521439798571799233293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 387368114345592382929244229 72631521439798571799233293)
      ·
        refine ⟨27236820539924464424712485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72631521439798571799233293 27236820539924464424712485)
        ·
          refine ⟨5106903851235837079633591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27236820539924464424712485 5106903851235837079633591)
          ·
            refine ⟨7660355776853755619450387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5106903851235837079633591 7660355776853755619450387)
            ·
              refine ⟨11490533665280633429175581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7660355776853755619450387 11490533665280633429175581)
              ·
                refine ⟨4308950124480237535940843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11490533665280633429175581 4308950124480237535940843)
                ·
                  refine ⟨6463425186720356303911265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4308950124480237535940843 6463425186720356303911265)
                  ·
                    refine ⟨4847568890040267227933449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6463425186720356303911265 4847568890040267227933449)
                    ·
                      refine ⟨3635676667530200420950087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4847568890040267227933449 3635676667530200420950087)
                      ·
                        rfl

theorem cell23_7080455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 1, 3, 1, 2, 2].length) (baseStart_7080455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7080455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7080455 prefixEnd_7080455 := by exact prefixLift 7080455
  have htrace : WordTrace (prefixWord ++ tailWord_7080455) baseStart_7080455 baseEnd_7080455 := by
    simpa [prefixWord, tailWord_7080455, baseEnd_7080455] using wordTrace_append hprefix tailTrace_7080455
  have hstable : (prefixWord ++ tailWord_7080455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7080455).length < 2 ^ (prefixWord ++ tailWord_7080455).sum := by decide
  have hdescent : baseEnd_7080455 < baseStart_7080455 := by decide
  rcases family_descends (prefixWord ++ tailWord_7080455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7080463 : List Nat := [1, 1, 2, 1, 1, 1, 2, 5, 1, 3, 5]
def baseStart_7080463 : Nat := 118140960795 + 7080463 * 2 ^ 59
def prefixEnd_7080463 : Nat := 4983230072969 + 3 ^ 40 * 7080463 * 2
def baseEnd_7080463 : Nat := 3635680775375436389650049

theorem tailTrace_7080463 : CollatzResearch.WordTrace tailWord_7080463 prefixEnd_7080463 3635680775375436389650049 := by
  unfold tailWord_7080463
  simp only [CollatzResearch.WordTrace]
  refine ⟨258245701347699272652454043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172163800898466181768302695 258245701347699272652454043)
  ·
    refine ⟨387368552021548908978681065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258245701347699272652454043 387368552021548908978681065)
    ·
      refine ⟨290526414016161681734010799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 387368552021548908978681065 290526414016161681734010799)
      ·
        refine ⟨435789621024242522601016199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290526414016161681734010799 435789621024242522601016199)
        ·
          refine ⟨653684431536363783901524299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 435789621024242522601016199 653684431536363783901524299)
          ·
            refine ⟨980526647304545675852286449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 653684431536363783901524299 980526647304545675852286449)
            ·
              refine ⟨735394985478409256889214837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 980526647304545675852286449 735394985478409256889214837)
              ·
                refine ⟨68943279888600867833363891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 735394985478409256889214837 68943279888600867833363891)
                ·
                  refine ⟨103414919832901301750045837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68943279888600867833363891 103414919832901301750045837)
                  ·
                    refine ⟨38780594937337988156267189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 103414919832901301750045837 38780594937337988156267189)
                    ·
                      refine ⟨3635680775375436389650049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38780594937337988156267189 3635680775375436389650049)
                      ·
                        rfl

theorem cell23_7080463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 5, 1, 3, 5].length) (baseStart_7080463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7080463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7080463 prefixEnd_7080463 := by exact prefixLift 7080463
  have htrace : WordTrace (prefixWord ++ tailWord_7080463) baseStart_7080463 baseEnd_7080463 := by
    simpa [prefixWord, tailWord_7080463, baseEnd_7080463] using wordTrace_append hprefix tailTrace_7080463
  have hstable : (prefixWord ++ tailWord_7080463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7080463).length < 2 ^ (prefixWord ++ tailWord_7080463).sum := by decide
  have hdescent : baseEnd_7080463 < baseStart_7080463 := by decide
  rcases family_descends (prefixWord ++ tailWord_7080463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7080488 : List Nat := [2, 1, 5, 2, 1, 3, 2, 1, 2, 1, 3]
def baseStart_7080488 : Nat := 118140960795 + 7080488 * 2 ^ 59
def prefixEnd_7080488 : Nat := 4983230072969 + 3 ^ 40 * 7080488 * 2
def baseEnd_7080488 : Nat := 3635693612391798791837435

theorem tailTrace_7080488 : CollatzResearch.WordTrace tailWord_7080488 prefixEnd_7080488 3635693612391798791837435 := by
  unfold tailWord_7080488
  simp only [CollatzResearch.WordTrace]
  refine ⟨129123306586304350961057059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172164408781739134614742745 129123306586304350961057059)
  ·
    refine ⟨193684959879456526441585589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129123306586304350961057059 193684959879456526441585589)
    ·
      refine ⟨18157964988699049353898649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 193684959879456526441585589 18157964988699049353898649)
      ·
        refine ⟨13618473741524287015423987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18157964988699049353898649 13618473741524287015423987)
        ·
          refine ⟨20427710612286430523135981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13618473741524287015423987 20427710612286430523135981)
          ·
            refine ⟨7660391479607411446175993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20427710612286430523135981 7660391479607411446175993)
            ·
              refine ⟨5745293609705558584631995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7660391479607411446175993 5745293609705558584631995)
              ·
                refine ⟨8617940414558337876947993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5745293609705558584631995 8617940414558337876947993)
                ·
                  refine ⟨6463455310918753407710995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8617940414558337876947993 6463455310918753407710995)
                  ·
                    refine ⟨9695182966378130111566493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6463455310918753407710995 9695182966378130111566493)
                    ·
                      refine ⟨3635693612391798791837435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9695182966378130111566493 3635693612391798791837435)
                      ·
                        rfl

theorem cell23_7080488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 2, 1, 2, 1, 3].length) (baseStart_7080488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7080488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7080488 prefixEnd_7080488 := by exact prefixLift 7080488
  have htrace : WordTrace (prefixWord ++ tailWord_7080488) baseStart_7080488 baseEnd_7080488 := by
    simpa [prefixWord, tailWord_7080488, baseEnd_7080488] using wordTrace_append hprefix tailTrace_7080488
  have hstable : (prefixWord ++ tailWord_7080488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7080488).length < 2 ^ (prefixWord ++ tailWord_7080488).sum := by decide
  have hdescent : baseEnd_7080488 < baseStart_7080488 := by decide
  rcases family_descends (prefixWord ++ tailWord_7080488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7080567 : List Nat := [1, 1, 3, 1, 1, 3, 5, 1, 2, 1, 4]
def baseStart_7080567 : Nat := 118140960795 + 7080567 * 2 ^ 59
def prefixEnd_7080567 : Nat := 4983230072969 + 3 ^ 40 * 7080567 * 2
def baseEnd_7080567 : Nat := 3635734177363503982749571

theorem tailTrace_7080567 : CollatzResearch.WordTrace tailWord_7080567 prefixEnd_7080567 3635734177363503982749571 := by
  unfold tailWord_7080567
  simp only [CollatzResearch.WordTrace]
  refine ⟨258249494539322498414239955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172166329692881665609493303 258249494539322498414239955)
  ·
    refine ⟨387374241808983747621359933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258249494539322498414239955 387374241808983747621359933)
    ·
      refine ⟨145265340678368905358009975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 387374241808983747621359933 145265340678368905358009975)
      ·
        refine ⟨217898011017553358037014963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145265340678368905358009975 217898011017553358037014963)
        ·
          refine ⟨326847016526330037055522445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217898011017553358037014963 326847016526330037055522445)
          ·
            refine ⟨122567631197373763895820917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 326847016526330037055522445 122567631197373763895820917)
            ·
              refine ⟨11490715424753790365233211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 122567631197373763895820917 11490715424753790365233211)
              ·
                refine ⟨17236073137130685547849817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11490715424753790365233211 17236073137130685547849817)
                ·
                  refine ⟨12927054852848014160887363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17236073137130685547849817 12927054852848014160887363)
                  ·
                    refine ⟨19390582279272021241331045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12927054852848014160887363 19390582279272021241331045)
                    ·
                      refine ⟨3635734177363503982749571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19390582279272021241331045 3635734177363503982749571)
                      ·
                        rfl

theorem cell23_7080567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 5, 1, 2, 1, 4].length) (baseStart_7080567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7080567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7080567 prefixEnd_7080567 := by exact prefixLift 7080567
  have htrace : WordTrace (prefixWord ++ tailWord_7080567) baseStart_7080567 baseEnd_7080567 := by
    simpa [prefixWord, tailWord_7080567, baseEnd_7080567] using wordTrace_append hprefix tailTrace_7080567
  have hstable : (prefixWord ++ tailWord_7080567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7080567).length < 2 ^ (prefixWord ++ tailWord_7080567).sum := by decide
  have hdescent : baseEnd_7080567 < baseStart_7080567 := by decide
  rcases family_descends (prefixWord ++ tailWord_7080567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7080577 : List Nat := [1, 2, 4, 2, 1, 1, 1, 2, 5, 4]
def baseStart_7080577 : Nat := 118140960795 + 7080577 * 2 ^ 59
def prefixEnd_7080577 : Nat := 4983230072969 + 3 ^ 40 * 7080577 * 2
def baseEnd_7080577 : Nat := 1211913104056682981208175

theorem tailTrace_7080577 : CollatzResearch.WordTrace tailWord_7080577 prefixEnd_7080577 1211913104056682981208175 := by
  unfold tailWord_7080577
  simp only [CollatzResearch.WordTrace]
  refine ⟨258249859269286270122103985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172166572846190846748069323 258249859269286270122103985)
  ·
    refine ⟨193687394451964702591577989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258249859269286270122103985 193687394451964702591577989)
    ·
      refine ⟨36316386459743381735920873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 193687394451964702591577989 36316386459743381735920873)
      ·
        refine ⟨27237289844807536301940655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36316386459743381735920873 27237289844807536301940655)
        ·
          refine ⟨40855934767211304452910983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27237289844807536301940655 40855934767211304452910983)
          ·
            refine ⟨61283902150816956679366475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40855934767211304452910983 61283902150816956679366475)
            ·
              refine ⟨91925853226225435019049713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61283902150816956679366475 91925853226225435019049713)
              ·
                refine ⟨68944389919669076264287285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91925853226225435019049713 68944389919669076264287285)
                ·
                  refine ⟨6463536554968975899776933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68944389919669076264287285 6463536554968975899776933)
                  ·
                    refine ⟨1211913104056682981208175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6463536554968975899776933 1211913104056682981208175)
                    ·
                      rfl

theorem cell23_7080577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 2, 5, 4].length) (baseStart_7080577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7080577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7080577 prefixEnd_7080577 := by exact prefixLift 7080577
  have htrace : WordTrace (prefixWord ++ tailWord_7080577) baseStart_7080577 baseEnd_7080577 := by
    simpa [prefixWord, tailWord_7080577, baseEnd_7080577] using wordTrace_append hprefix tailTrace_7080577
  have hstable : (prefixWord ++ tailWord_7080577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7080577).length < 2 ^ (prefixWord ++ tailWord_7080577).sum := by decide
  have hdescent : baseEnd_7080577 < baseStart_7080577 := by decide
  rcases family_descends (prefixWord ++ tailWord_7080577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7080594 : List Nat := [3, 2, 3, 1, 2, 1, 1, 3, 3, 4]
def baseStart_7080594 : Nat := 118140960795 + 7080594 * 2 ^ 59
def prefixEnd_7080594 : Nat := 4983230072969 + 3 ^ 40 * 7080594 * 2
def baseEnd_7080594 : Nat := 1211916013780391792370649

theorem tailTrace_7080594 : CollatzResearch.WordTrace tailWord_7080594 prefixEnd_7080594 1211916013780391792370649 := by
  unfold tailWord_7080594
  simp only [CollatzResearch.WordTrace]
  refine ⟨64562619827556170506368209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172166986206816454683648557 64562619827556170506368209)
  ·
    refine ⟨48421964870667127879776157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64562619827556170506368209 48421964870667127879776157)
    ·
      refine ⟨18158236826500172954916059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48421964870667127879776157 18158236826500172954916059)
      ·
        refine ⟨27237355239750259432374089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18158236826500172954916059 27237355239750259432374089)
        ·
          refine ⟨20428016429812694574280567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27237355239750259432374089 20428016429812694574280567)
          ·
            refine ⟨30642024644719041861420851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20428016429812694574280567 30642024644719041861420851)
            ·
              refine ⟨45963036967078562792131277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30642024644719041861420851 45963036967078562792131277)
              ·
                refine ⟨17236138862654461047049229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45963036967078562792131277 17236138862654461047049229)
                ·
                  refine ⟨6463552073495422892643461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17236138862654461047049229 6463552073495422892643461)
                  ·
                    refine ⟨1211916013780391792370649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6463552073495422892643461 1211916013780391792370649)
                    ·
                      rfl

theorem cell23_7080594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 3, 3, 4].length) (baseStart_7080594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7080594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7080594 prefixEnd_7080594 := by exact prefixLift 7080594
  have htrace : WordTrace (prefixWord ++ tailWord_7080594) baseStart_7080594 baseEnd_7080594 := by
    simpa [prefixWord, tailWord_7080594, baseEnd_7080594] using wordTrace_append hprefix tailTrace_7080594
  have hstable : (prefixWord ++ tailWord_7080594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7080594).length < 2 ^ (prefixWord ++ tailWord_7080594).sum := by decide
  have hdescent : baseEnd_7080594 < baseStart_7080594 := by decide
  rcases family_descends (prefixWord ++ tailWord_7080594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7080657 : List Nat := [1, 2, 2, 1, 2, 3, 2, 2, 3, 1, 4]
def baseStart_7080657 : Nat := 118140960795 + 7080657 * 2 ^ 59
def prefixEnd_7080657 : Nat := 4983230072969 + 3 ^ 40 * 7080657 * 2
def baseEnd_7080657 : Nat := 3635780390622408630624157

theorem tailTrace_7080657 : CollatzResearch.WordTrace tailWord_7080657 prefixEnd_7080657 3635780390622408630624157 := by
  unfold tailWord_7080657
  simp only [CollatzResearch.WordTrace]
  refine ⟨258252777108996443785016225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172168518072664295856677483 258252777108996443785016225)
  ·
    refine ⟨193689582831747332838762169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258252777108996443785016225 193689582831747332838762169)
    ·
      refine ⟨145267187123810499629071627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193689582831747332838762169 145267187123810499629071627)
      ·
        refine ⟨217900780685715749443607441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145267187123810499629071627 217900780685715749443607441)
        ·
          refine ⟨163425585514286812082705581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217900780685715749443607441 163425585514286812082705581)
          ·
            refine ⟨61284594567857554531014593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 163425585514286812082705581 61284594567857554531014593)
            ·
              refine ⟨45963445925893165898260945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61284594567857554531014593 45963445925893165898260945)
              ·
                refine ⟨34472584444419874423695709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45963445925893165898260945 34472584444419874423695709)
                ·
                  refine ⟨12927219166657452908885891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34472584444419874423695709 12927219166657452908885891)
                  ·
                    refine ⟨19390828749986179363328837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12927219166657452908885891 19390828749986179363328837)
                    ·
                      refine ⟨3635780390622408630624157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19390828749986179363328837 3635780390622408630624157)
                      ·
                        rfl

theorem cell23_7080657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 2, 3, 1, 4].length) (baseStart_7080657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7080657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7080657 prefixEnd_7080657 := by exact prefixLift 7080657
  have htrace : WordTrace (prefixWord ++ tailWord_7080657) baseStart_7080657 baseEnd_7080657 := by
    simpa [prefixWord, tailWord_7080657, baseEnd_7080657] using wordTrace_append hprefix tailTrace_7080657
  have hstable : (prefixWord ++ tailWord_7080657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7080657).length < 2 ^ (prefixWord ++ tailWord_7080657).sum := by decide
  have hdescent : baseEnd_7080657 < baseStart_7080657 := by decide
  rcases family_descends (prefixWord ++ tailWord_7080657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
