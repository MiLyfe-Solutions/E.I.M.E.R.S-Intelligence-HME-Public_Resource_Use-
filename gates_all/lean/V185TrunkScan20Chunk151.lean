import V185TrunkScan20Chunk150

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_918354 : List Nat := [3, 2, 2, 1, 1, 2, 2, 3, 4]
def baseStart_918354 : Nat := 118140960795 + 918354 * 2 ^ 59
def prefixEnd_918354 : Nat := 4983230072969 + 3 ^ 40 * 918354 * 2
def baseEnd_918354 : Nat := 419161789314849039512509

theorem tailTrace_918354 : CollatzResearch.WordTrace tailWord_918354 prefixEnd_918354 419161789314849039512509 := by
  unfold tailWord_918354
  simp only [CollatzResearch.WordTrace]
  refine ⟨8373780528741943805362529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22330081409978516814300077 8373780528741943805362529)
  ·
    refine ⟨6280335396556457854021897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8373780528741943805362529 6280335396556457854021897)
    ·
      refine ⟨4710251547417343390516423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6280335396556457854021897 4710251547417343390516423)
      ·
        refine ⟨7065377321126015085774635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4710251547417343390516423 7065377321126015085774635)
        ·
          refine ⟨10598065981689022628661953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7065377321126015085774635 10598065981689022628661953)
          ·
            refine ⟨7948549486266766971496465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10598065981689022628661953 7948549486266766971496465)
            ·
              refine ⟨5961412114700075228622349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7948549486266766971496465 5961412114700075228622349)
              ·
                refine ⟨2235529543012528210733381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5961412114700075228622349 2235529543012528210733381)
                ·
                  refine ⟨419161789314849039512509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2235529543012528210733381 419161789314849039512509)
                  ·
                    rfl

theorem cell20_918354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 3, 4].length) (baseStart_918354 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_918354 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_918354 prefixEnd_918354 := by exact prefixLift 918354
  have htrace : WordTrace (prefixWord ++ tailWord_918354) baseStart_918354 baseEnd_918354 := by
    simpa [prefixWord, tailWord_918354, baseEnd_918354] using wordTrace_append hprefix tailTrace_918354
  have hstable : (prefixWord ++ tailWord_918354).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918354).length < 2 ^ (prefixWord ++ tailWord_918354).sum := by decide
  have hdescent : baseEnd_918354 < baseStart_918354 := by decide
  rcases family_descends (prefixWord ++ tailWord_918354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918361 : List Nat := [1, 2, 1, 2, 2, 4, 3, 5]
def baseStart_918361 : Nat := 118140960795 + 918361 * 2 ^ 59
def prefixEnd_918361 : Nat := 4983230072969 + 3 ^ 40 * 918361 * 2
def baseEnd_918361 : Nat := 139721661435196042093049

theorem tailTrace_918361 : CollatzResearch.WordTrace tailWord_918361 prefixEnd_918361 139721661435196042093049 := by
  unfold tailWord_918361
  simp only [CollatzResearch.WordTrace]
  refine ⟨33495377425942415416954937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22330251617294943611303291 33495377425942415416954937)
  ·
    refine ⟨25121533069456811562716203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33495377425942415416954937 25121533069456811562716203)
    ·
      refine ⟨37682299604185217344074305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25121533069456811562716203 37682299604185217344074305)
      ·
        refine ⟨28261724703138913008055729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37682299604185217344074305 28261724703138913008055729)
        ·
          refine ⟨21196293527354184756041797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28261724703138913008055729 21196293527354184756041797)
          ·
            refine ⟨3974305036378909641757837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21196293527354184756041797 3974305036378909641757837)
            ·
              refine ⟨1490364388642091115659189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3974305036378909641757837 1490364388642091115659189)
              ·
                refine ⟨139721661435196042093049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1490364388642091115659189 139721661435196042093049)
                ·
                  rfl

theorem cell20_918361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 3, 5].length) (baseStart_918361 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_918361 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_918361 prefixEnd_918361 := by exact prefixLift 918361
  have htrace : WordTrace (prefixWord ++ tailWord_918361) baseStart_918361 baseEnd_918361 := by
    simpa [prefixWord, tailWord_918361, baseEnd_918361] using wordTrace_append hprefix tailTrace_918361
  have hstable : (prefixWord ++ tailWord_918361).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918361).length < 2 ^ (prefixWord ++ tailWord_918361).sum := by decide
  have hdescent : baseEnd_918361 < baseStart_918361 := by decide
  rcases family_descends (prefixWord ++ tailWord_918361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918364 : List Nat := [2, 2, 4, 2, 1, 1, 2, 3, 3]
def baseStart_918364 : Nat := 118140960795 + 918364 * 2 ^ 59
def prefixEnd_918364 : Nat := 4983230072969 + 3 ^ 40 * 918364 * 2
def baseEnd_918364 : Nat := 419166353587333449179135

theorem tailTrace_918364 : CollatzResearch.WordTrace tailWord_918364 prefixEnd_918364 419166353587333449179135 := by
  unfold tailWord_918364
  simp only [CollatzResearch.WordTrace]
  refine ⟨16747743422465773464657073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22330324563287697952876097 16747743422465773464657073)
  ·
    refine ⟨12560807566849330098492805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16747743422465773464657073 12560807566849330098492805)
    ·
      refine ⟨2355151418784249393467401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12560807566849330098492805 2355151418784249393467401)
      ·
        refine ⟨1766363564088187045100551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2355151418784249393467401 1766363564088187045100551)
        ·
          refine ⟨2649545346132280567650827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1766363564088187045100551 2649545346132280567650827)
          ·
            refine ⟨3974318019198420851476241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2649545346132280567650827 3974318019198420851476241)
            ·
              refine ⟨2980738514398815638607181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3974318019198420851476241 2980738514398815638607181)
              ·
                refine ⟨1117776942899555864477693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2980738514398815638607181 1117776942899555864477693)
                ·
                  refine ⟨419166353587333449179135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1117776942899555864477693 419166353587333449179135)
                  ·
                    rfl

theorem cell20_918364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 3, 3].length) (baseStart_918364 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_918364 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_918364 prefixEnd_918364 := by exact prefixLift 918364
  have htrace : WordTrace (prefixWord ++ tailWord_918364) baseStart_918364 baseEnd_918364 := by
    simpa [prefixWord, tailWord_918364, baseEnd_918364] using wordTrace_append hprefix tailTrace_918364
  have hstable : (prefixWord ++ tailWord_918364).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918364).length < 2 ^ (prefixWord ++ tailWord_918364).sum := by decide
  have hdescent : baseEnd_918364 < baseStart_918364 := by decide
  rcases family_descends (prefixWord ++ tailWord_918364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918398 : List Nat := [4, 2, 3, 1, 2, 2, 1, 2, 3]
def baseStart_918398 : Nat := 118140960795 + 918398 * 2 ^ 59
def prefixEnd_918398 : Nat := 4983230072969 + 3 ^ 40 * 918398 * 2
def baseEnd_918398 : Nat := 419181872113780442045663

theorem tailTrace_918398 : CollatzResearch.WordTrace tailWord_918398 prefixEnd_918398 419181872113780442045663 := by
  unfold tailWord_918398
  simp only [CollatzResearch.WordTrace]
  refine ⟨4187090865851046342006481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22331151284538913824034565 4187090865851046342006481)
  ·
    refine ⟨3140318149388284756504861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4187090865851046342006481 3140318149388284756504861)
    ·
      refine ⟨1177619306020606783689323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3140318149388284756504861 1177619306020606783689323)
      ·
        refine ⟨1766428959030910175533985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1177619306020606783689323 1766428959030910175533985)
        ·
          refine ⟨1324821719273182631650489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1766428959030910175533985 1324821719273182631650489)
          ·
            refine ⟨993616289454886973737867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1324821719273182631650489 993616289454886973737867)
            ·
              refine ⟨1490424434182330460606801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 993616289454886973737867 1490424434182330460606801)
              ·
                refine ⟨1117818325636747845455101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1490424434182330460606801 1117818325636747845455101)
                ·
                  refine ⟨419181872113780442045663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1117818325636747845455101 419181872113780442045663)
                  ·
                    rfl

theorem cell20_918398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 1, 2, 3].length) (baseStart_918398 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_918398 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_918398 prefixEnd_918398 := by exact prefixLift 918398
  have htrace : WordTrace (prefixWord ++ tailWord_918398) baseStart_918398 baseEnd_918398 := by
    simpa [prefixWord, tailWord_918398, baseEnd_918398] using wordTrace_append hprefix tailTrace_918398
  have hstable : (prefixWord ++ tailWord_918398).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918398).length < 2 ^ (prefixWord ++ tailWord_918398).sum := by decide
  have hdescent : baseEnd_918398 < baseStart_918398 := by decide
  rcases family_descends (prefixWord ++ tailWord_918398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918409 : List Nat := [1, 2, 1, 1, 5, 2, 2, 4, 2]
def baseStart_918409 : Nat := 118140960795 + 918409 * 2 ^ 59
def prefixEnd_918409 : Nat := 4983230072969 + 3 ^ 40 * 918409 * 2
def baseEnd_918409 : Nat := 419186892813513292678951

theorem tailTrace_918409 : CollatzResearch.WordTrace tailWord_918409 prefixEnd_918409 419186892813513292678951 := by
  unfold tailWord_918409
  simp only [CollatzResearch.WordTrace]
  refine ⟨33497128129768519614702281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22331418753179013076468187 33497128129768519614702281)
  ·
    refine ⟨25122846097326389711026711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33497128129768519614702281 25122846097326389711026711)
    ·
      refine ⟨37684269145989584566540067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25122846097326389711026711 37684269145989584566540067)
      ·
        refine ⟨56526403718984376849810101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37684269145989584566540067 56526403718984376849810101)
        ·
          refine ⟨5299350348654785329669697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 56526403718984376849810101 5299350348654785329669697)
          ·
            refine ⟨3974512761491088997252273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5299350348654785329669697 3974512761491088997252273)
            ·
              refine ⟨2980884571118316747939205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3974512761491088997252273 2980884571118316747939205)
              ·
                refine ⟨558915857084684390238601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2980884571118316747939205 558915857084684390238601)
                ·
                  refine ⟨419186892813513292678951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 558915857084684390238601 419186892813513292678951)
                  ·
                    rfl

theorem cell20_918409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 4, 2].length) (baseStart_918409 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_918409 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_918409 prefixEnd_918409 := by exact prefixLift 918409
  have htrace : WordTrace (prefixWord ++ tailWord_918409) baseStart_918409 baseEnd_918409 := by
    simpa [prefixWord, tailWord_918409, baseEnd_918409] using wordTrace_append hprefix tailTrace_918409
  have hstable : (prefixWord ++ tailWord_918409).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918409).length < 2 ^ (prefixWord ++ tailWord_918409).sum := by decide
  have hdescent : baseEnd_918409 < baseStart_918409 := by decide
  rcases family_descends (prefixWord ++ tailWord_918409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918433 : List Nat := [1, 2, 3, 4, 1, 3, 2, 4]
def baseStart_918433 : Nat := 118140960795 + 918433 * 2 ^ 59
def prefixEnd_918433 : Nat := 4983230072969 + 3 ^ 40 * 918433 * 2
def baseEnd_918433 : Nat := 139732615689158625292951

theorem tailTrace_918433 : CollatzResearch.WordTrace tailWord_918433 prefixEnd_918433 139732615689158625292951 := by
  unfold tailWord_918433
  simp only [CollatzResearch.WordTrace]
  refine ⟨33498003481681571713575953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22332002321121047809050635 33498003481681571713575953)
  ·
    refine ⟨25123502611261178785181965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33498003481681571713575953 25123502611261178785181965)
    ·
      refine ⟨9421313479222942044443237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25123502611261178785181965 9421313479222942044443237)
      ·
        refine ⟨1766496277354301633333107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9421313479222942044443237 1766496277354301633333107)
        ·
          refine ⟨2649744416031452449999661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1766496277354301633333107 2649744416031452449999661)
          ·
            refine ⟨993654156011794668749873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2649744416031452449999661 993654156011794668749873)
            ·
              refine ⟨745240617008846001562405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 993654156011794668749873 745240617008846001562405)
              ·
                refine ⟨139732615689158625292951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 745240617008846001562405 139732615689158625292951)
                ·
                  rfl

theorem cell20_918433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 2, 4].length) (baseStart_918433 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_918433 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_918433 prefixEnd_918433 := by exact prefixLift 918433
  have htrace : WordTrace (prefixWord ++ tailWord_918433) baseStart_918433 baseEnd_918433 := by
    simpa [prefixWord, tailWord_918433, baseEnd_918433] using wordTrace_append hprefix tailTrace_918433
  have hstable : (prefixWord ++ tailWord_918433).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918433).length < 2 ^ (prefixWord ++ tailWord_918433).sum := by decide
  have hdescent : baseEnd_918433 < baseStart_918433 := by decide
  rcases family_descends (prefixWord ++ tailWord_918433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918464 : List Nat := [2, 1, 1, 2, 3, 4, 3, 2, 2]
def baseStart_918464 : Nat := 118140960795 + 918464 * 2 ^ 59
def prefixEnd_918464 : Nat := 4983230072969 + 3 ^ 40 * 918464 * 2
def baseEnd_918464 : Nat := 419211996312177545845393

theorem tailTrace_918464 : CollatzResearch.WordTrace tailWord_918464 prefixEnd_918464 419211996312177545845393 := by
  unfold tailWord_918464
  simp only [CollatzResearch.WordTrace]
  refine ⟨16749567072284632003977223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22332756096379509338636297 16749567072284632003977223)
  ·
    refine ⟨25124350608426948005965835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16749567072284632003977223 25124350608426948005965835)
    ·
      refine ⟨37686525912640422008948753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25124350608426948005965835 37686525912640422008948753)
      ·
        refine ⟨28264894434480316506711565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37686525912640422008948753 28264894434480316506711565)
        ·
          refine ⟨10599335412930118690016837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28264894434480316506711565 10599335412930118690016837)
          ·
            refine ⟨1987375389924397254378157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10599335412930118690016837 1987375389924397254378157)
            ·
              refine ⟨745265771221648970391809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1987375389924397254378157 745265771221648970391809)
              ·
                refine ⟨558949328416236727793857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 745265771221648970391809 558949328416236727793857)
                ·
                  refine ⟨419211996312177545845393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 558949328416236727793857 419211996312177545845393)
                  ·
                    rfl

theorem cell20_918464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 3, 2, 2].length) (baseStart_918464 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_918464 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_918464 prefixEnd_918464 := by exact prefixLift 918464
  have htrace : WordTrace (prefixWord ++ tailWord_918464) baseStart_918464 baseEnd_918464 := by
    simpa [prefixWord, tailWord_918464, baseEnd_918464] using wordTrace_append hprefix tailTrace_918464
  have hstable : (prefixWord ++ tailWord_918464).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918464).length < 2 ^ (prefixWord ++ tailWord_918464).sum := by decide
  have hdescent : baseEnd_918464 < baseStart_918464 := by decide
  rcases family_descends (prefixWord ++ tailWord_918464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918475 : List Nat := [1, 1, 1, 1, 3, 6, 2, 5]
def baseStart_918475 : Nat := 118140960795 + 918475 * 2 ^ 59
def prefixEnd_918475 : Nat := 4983230072969 + 3 ^ 40 * 918475 * 2
def baseEnd_918475 : Nat := 139739005670636798826227

theorem tailTrace_918475 : CollatzResearch.WordTrace tailWord_918475 prefixEnd_918475 139739005670636798826227 := by
  unfold tailWord_918475
  simp only [CollatzResearch.WordTrace]
  refine ⟨33499535347529412886604879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22333023565019608591069919 33499535347529412886604879)
  ·
    refine ⟨50249303021294119329907319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33499535347529412886604879 50249303021294119329907319)
    ·
      refine ⟨75373954531941178994860979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50249303021294119329907319 75373954531941178994860979)
      ·
        refine ⟨113060931797911768492291469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75373954531941178994860979 113060931797911768492291469)
        ·
          refine ⟨42397849424216913184609301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113060931797911768492291469 42397849424216913184609301)
          ·
            refine ⟨1987399191760167805528561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 42397849424216913184609301 1987399191760167805528561)
            ·
              refine ⟨1490549393820125854146421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1987399191760167805528561 1490549393820125854146421)
              ·
                refine ⟨139739005670636798826227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1490549393820125854146421 139739005670636798826227)
                ·
                  rfl

theorem cell20_918475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 2, 5].length) (baseStart_918475 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_918475 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_918475 prefixEnd_918475 := by exact prefixLift 918475
  have htrace : WordTrace (prefixWord ++ tailWord_918475) baseStart_918475 baseEnd_918475 := by
    simpa [prefixWord, tailWord_918475, baseEnd_918475] using wordTrace_append hprefix tailTrace_918475
  have hstable : (prefixWord ++ tailWord_918475).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918475).length < 2 ^ (prefixWord ++ tailWord_918475).sum := by decide
  have hdescent : baseEnd_918475 < baseStart_918475 := by decide
  rcases family_descends (prefixWord ++ tailWord_918475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918478 : List Nat := [4, 1, 1, 1, 2, 3, 4, 1, 3]
def baseStart_918478 : Nat := 118140960795 + 918478 * 2 ^ 59
def prefixEnd_918478 : Nat := 4983230072969 + 3 ^ 40 * 918478 * 2
def baseEnd_918478 : Nat := 419218386293655719378669

theorem tailTrace_918478 : CollatzResearch.WordTrace tailWord_918478 prefixEnd_918478 419218386293655719378669 := by
  unfold tailWord_918478
  simp only [CollatzResearch.WordTrace]
  refine ⟨4187455595814818049870511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22333096511012362932642725 4187455595814818049870511)
  ·
    refine ⟨6281183393722227074805767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4187455595814818049870511 6281183393722227074805767)
    ·
      refine ⟨9421775090583340612208651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6281183393722227074805767 9421775090583340612208651)
      ·
        refine ⟨14132662635875010918312977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9421775090583340612208651 14132662635875010918312977)
        ·
          refine ⟨10599496976906258188734733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14132662635875010918312977 10599496976906258188734733)
          ·
            refine ⟨3974811366339846820775525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10599496976906258188734733 3974811366339846820775525)
            ·
              refine ⟨745277131188721278895411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3974811366339846820775525 745277131188721278895411)
              ·
                refine ⟨1117915696783081918343117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 745277131188721278895411 1117915696783081918343117)
                ·
                  refine ⟨419218386293655719378669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1117915696783081918343117 419218386293655719378669)
                  ·
                    rfl

theorem cell20_918478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 4, 1, 3].length) (baseStart_918478 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_918478 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_918478 prefixEnd_918478 := by exact prefixLift 918478
  have htrace : WordTrace (prefixWord ++ tailWord_918478) baseStart_918478 baseEnd_918478 := by
    simpa [prefixWord, tailWord_918478, baseEnd_918478] using wordTrace_append hprefix tailTrace_918478
  have hstable : (prefixWord ++ tailWord_918478).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918478).length < 2 ^ (prefixWord ++ tailWord_918478).sum := by decide
  have hdescent : baseEnd_918478 < baseStart_918478 := by decide
  rcases family_descends (prefixWord ++ tailWord_918478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918526 : List Nat := [4, 2, 2, 2, 3, 1, 1, 5]
def baseStart_918526 : Nat := 118140960795 + 918526 * 2 ^ 59
def prefixEnd_918526 : Nat := 4983230072969 + 3 ^ 40 * 918526 * 2
def baseEnd_918526 : Nat := 139746764933860295259491

theorem tailTrace_918526 : CollatzResearch.WordTrace tailWord_918526 prefixEnd_918526 139746764933860295259491 := by
  unfold tailWord_918526
  simp only [CollatzResearch.WordTrace]
  refine ⟨4187674433793081074588929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22334263646896432397807621 4187674433793081074588929)
  ·
    refine ⟨3140755825344810805941697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4187674433793081074588929 3140755825344810805941697)
    ·
      refine ⟨2355566869008608104456273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3140755825344810805941697 2355566869008608104456273)
      ·
        refine ⟨1766675151756456078342205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2355566869008608104456273 1766675151756456078342205)
        ·
          refine ⟨662503181908671029378327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1766675151756456078342205 662503181908671029378327)
          ·
            refine ⟨993754772863006544067491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 662503181908671029378327 993754772863006544067491)
            ·
              refine ⟨1490632159294509816101237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 993754772863006544067491 1490632159294509816101237)
              ·
                refine ⟨139746764933860295259491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1490632159294509816101237 139746764933860295259491)
                ·
                  rfl

theorem cell20_918526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 1, 5].length) (baseStart_918526 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_918526 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_918526 prefixEnd_918526 := by exact prefixLift 918526
  have htrace : WordTrace (prefixWord ++ tailWord_918526) baseStart_918526 baseEnd_918526 := by
    simpa [prefixWord, tailWord_918526, baseEnd_918526] using wordTrace_append hprefix tailTrace_918526
  have hstable : (prefixWord ++ tailWord_918526).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918526).length < 2 ^ (prefixWord ++ tailWord_918526).sum := by decide
  have hdescent : baseEnd_918526 < baseStart_918526 := by decide
  rcases family_descends (prefixWord ++ tailWord_918526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918561 : List Nat := [1, 2, 3, 2, 3, 1, 1, 5, 2]
def baseStart_918561 : Nat := 118140960795 + 918561 * 2 ^ 59
def prefixEnd_918561 : Nat := 4983230072969 + 3 ^ 40 * 918561 * 2
def baseEnd_918561 : Nat := 419256269755276319611663

theorem tailTrace_918561 : CollatzResearch.WordTrace tailWord_918561 prefixEnd_918561 419256269755276319611663 := by
  unfold tailWord_918561
  simp only [CollatzResearch.WordTrace]
  refine ⟨33502672025217849574235537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22335114683478566382823691 33502672025217849574235537)
  ·
    refine ⟨25127004018913387180676653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33502672025217849574235537 25127004018913387180676653)
    ·
      refine ⟨9422626507092520192753745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25127004018913387180676653 9422626507092520192753745)
      ·
        refine ⟨7066969880319390144565309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9422626507092520192753745 7066969880319390144565309)
        ·
          refine ⟨2650113705119771304211991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7066969880319390144565309 2650113705119771304211991)
          ·
            refine ⟨3975170557679656956317987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2650113705119771304211991 3975170557679656956317987)
            ·
              refine ⟨5962755836519485434476981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3975170557679656956317987 5962755836519485434476981)
              ·
                refine ⟨559008359673701759482217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5962755836519485434476981 559008359673701759482217)
                ·
                  refine ⟨419256269755276319611663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 559008359673701759482217 419256269755276319611663)
                  ·
                    rfl

theorem cell20_918561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 5, 2].length) (baseStart_918561 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_918561 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_918561 prefixEnd_918561 := by exact prefixLift 918561
  have htrace : WordTrace (prefixWord ++ tailWord_918561) baseStart_918561 baseEnd_918561 := by
    simpa [prefixWord, tailWord_918561, baseEnd_918561] using wordTrace_append hprefix tailTrace_918561
  have hstable : (prefixWord ++ tailWord_918561).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918561).length < 2 ^ (prefixWord ++ tailWord_918561).sum := by decide
  have hdescent : baseEnd_918561 < baseStart_918561 := by decide
  rcases family_descends (prefixWord ++ tailWord_918561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918565 : List Nat := [1, 3, 1, 2, 2, 2, 1, 2, 6]
def baseStart_918565 : Nat := 118140960795 + 918565 * 2 ^ 59
def prefixEnd_918565 : Nat := 4983230072969 + 3 ^ 40 * 918565 * 2
def baseEnd_918565 : Nat := 419258095464270083478313

theorem tailTrace_918565 : CollatzResearch.WordTrace tailWord_918565 prefixEnd_918565 419258095464270083478313 := by
  unfold tailWord_918565
  simp only [CollatzResearch.WordTrace]
  refine ⟨33502817917203358257381149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22335211944802238838254099 33502817917203358257381149)
  ·
    refine ⟨12563556718951259346517931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33502817917203358257381149 12563556718951259346517931)
    ·
      refine ⟨18845335078426889019776897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12563556718951259346517931 18845335078426889019776897)
      ·
        refine ⟨14134001308820166764832673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18845335078426889019776897 14134001308820166764832673)
        ·
          refine ⟨10600500981615125073624505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14134001308820166764832673 10600500981615125073624505)
          ·
            refine ⟨7950375736211343805218379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10600500981615125073624505 7950375736211343805218379)
            ·
              refine ⟨11925563604317015707827569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7950375736211343805218379 11925563604317015707827569)
              ·
                refine ⟨8944172703237761780870677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11925563604317015707827569 8944172703237761780870677)
                ·
                  refine ⟨419258095464270083478313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8944172703237761780870677 419258095464270083478313)
                  ·
                    rfl

theorem cell20_918565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 2, 6].length) (baseStart_918565 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_918565 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_918565 prefixEnd_918565 := by exact prefixLift 918565
  have htrace : WordTrace (prefixWord ++ tailWord_918565) baseStart_918565 baseEnd_918565 := by
    simpa [prefixWord, tailWord_918565, baseEnd_918565] using wordTrace_append hprefix tailTrace_918565
  have hstable : (prefixWord ++ tailWord_918565).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918565).length < 2 ^ (prefixWord ++ tailWord_918565).sum := by decide
  have hdescent : baseEnd_918565 < baseStart_918565 := by decide
  rcases family_descends (prefixWord ++ tailWord_918565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918572 : List Nat := [2, 2, 1, 1, 1, 2, 11]
def baseStart_918572 : Nat := 118140960795 + 918572 * 2 ^ 59
def prefixEnd_918572 : Nat := 4983230072969 + 3 ^ 40 * 918572 * 2
def baseEnd_918572 : Nat := 46584587828334352249439

theorem tailTrace_918572 : CollatzResearch.WordTrace tailWord_918572 prefixEnd_918572 46584587828334352249439 := by
  unfold tailWord_918572
  simp only [CollatzResearch.WordTrace]
  refine ⟨16751536614088999226442985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22335382152118665635257313 16751536614088999226442985)
  ·
    refine ⟨12563652460566749419832239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16751536614088999226442985 12563652460566749419832239)
    ·
      refine ⟨18845478690850124129748359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12563652460566749419832239 18845478690850124129748359)
      ·
        refine ⟨28268218036275186194622539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18845478690850124129748359 28268218036275186194622539)
        ·
          refine ⟨42402327054412779291933809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28268218036275186194622539 42402327054412779291933809)
          ·
            refine ⟨31801745290809584468950357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42402327054412779291933809 31801745290809584468950357)
            ·
              refine ⟨46584587828334352249439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 31801745290809584468950357 46584587828334352249439)
              ·
                rfl

theorem cell20_918572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 11].length) (baseStart_918572 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_918572 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_918572 prefixEnd_918572 := by exact prefixLift 918572
  have htrace : WordTrace (prefixWord ++ tailWord_918572) baseStart_918572 baseEnd_918572 := by
    simpa [prefixWord, tailWord_918572, baseEnd_918572] using wordTrace_append hprefix tailTrace_918572
  have hstable : (prefixWord ++ tailWord_918572).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918572).length < 2 ^ (prefixWord ++ tailWord_918572).sum := by decide
  have hdescent : baseEnd_918572 < baseStart_918572 := by decide
  rcases family_descends (prefixWord ++ tailWord_918572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918637 : List Nat := [1, 5, 1, 1, 2, 4, 1, 1, 4]
def baseStart_918637 : Nat := 118140960795 + 918637 * 2 ^ 59
def prefixEnd_918637 : Nat := 4983230072969 + 3 ^ 40 * 918637 * 2
def baseEnd_918637 : Nat := 419290958226157833078019

theorem tailTrace_918637 : CollatzResearch.WordTrace tailWord_918637 prefixEnd_918637 419290958226157833078019 := by
  unfold tailWord_918637
  simp only [CollatzResearch.WordTrace]
  refine ⟨33505443972942514554002165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22336962648628343036001443 33505443972942514554002165)
  ·
    refine ⟨3141135372463360739437703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33505443972942514554002165 3141135372463360739437703)
    ·
      refine ⟨4711703058695041109156555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3141135372463360739437703 4711703058695041109156555)
      ·
        refine ⟨7067554588042561663734833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4711703058695041109156555 7067554588042561663734833)
        ·
          refine ⟨5300665941031921247801125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7067554588042561663734833 5300665941031921247801125)
          ·
            refine ⟨993874863943485233962711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5300665941031921247801125 993874863943485233962711)
            ·
              refine ⟨1490812295915227850944067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 993874863943485233962711 1490812295915227850944067)
              ·
                refine ⟨2236218443872841776416101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1490812295915227850944067 2236218443872841776416101)
                ·
                  refine ⟨419290958226157833078019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2236218443872841776416101 419290958226157833078019)
                  ·
                    rfl

theorem cell20_918637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 1, 1, 4].length) (baseStart_918637 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_918637 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_918637 prefixEnd_918637 := by exact prefixLift 918637
  have htrace : WordTrace (prefixWord ++ tailWord_918637) baseStart_918637 baseEnd_918637 := by
    simpa [prefixWord, tailWord_918637, baseEnd_918637] using wordTrace_append hprefix tailTrace_918637
  have hstable : (prefixWord ++ tailWord_918637).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918637).length < 2 ^ (prefixWord ++ tailWord_918637).sum := by decide
  have hdescent : baseEnd_918637 < baseStart_918637 := by decide
  rcases family_descends (prefixWord ++ tailWord_918637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918641 : List Nat := [1, 2, 2, 2, 1, 1, 2, 5, 4]
def baseStart_918641 : Nat := 118140960795 + 918641 * 2 ^ 59
def prefixEnd_918641 : Nat := 4983230072969 + 3 ^ 40 * 918641 * 2
def baseEnd_918641 : Nat := 419292783935151596944669

theorem tailTrace_918641 : CollatzResearch.WordTrace tailWord_918641 prefixEnd_918641 419292783935151596944669 := by
  unfold tailWord_918641
  simp only [CollatzResearch.WordTrace]
  refine ⟨33505589864928023237147777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22337059909952015491431851 33505589864928023237147777)
  ·
    refine ⟨25129192398696017427860833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33505589864928023237147777 25129192398696017427860833)
    ·
      refine ⟨18846894299022013070895625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25129192398696017427860833 18846894299022013070895625)
      ·
        refine ⟨14135170724266509803171719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18846894299022013070895625 14135170724266509803171719)
        ·
          refine ⟨21202756086399764704757579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14135170724266509803171719 21202756086399764704757579)
          ·
            refine ⟨31804134129599647057136369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21202756086399764704757579 31804134129599647057136369)
            ·
              refine ⟨23853100597199735292852277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31804134129599647057136369 23853100597199735292852277)
              ·
                refine ⟨2236228180987475183704901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23853100597199735292852277 2236228180987475183704901)
                ·
                  refine ⟨419292783935151596944669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2236228180987475183704901 419292783935151596944669)
                  ·
                    rfl

theorem cell20_918641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 5, 4].length) (baseStart_918641 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_918641 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_918641 prefixEnd_918641 := by exact prefixLift 918641
  have htrace : WordTrace (prefixWord ++ tailWord_918641) baseStart_918641 baseEnd_918641 := by
    simpa [prefixWord, tailWord_918641, baseEnd_918641] using wordTrace_append hprefix tailTrace_918641
  have hstable : (prefixWord ++ tailWord_918641).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918641).length < 2 ^ (prefixWord ++ tailWord_918641).sum := by decide
  have hdescent : baseEnd_918641 < baseStart_918641 := by decide
  rcases family_descends (prefixWord ++ tailWord_918641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918648 : List Nat := [2, 1, 2, 1, 1, 1, 5, 7]
def baseStart_918648 : Nat := 118140960795 + 918648 * 2 ^ 59
def prefixEnd_918648 : Nat := 4983230072969 + 3 ^ 40 * 918648 * 2
def baseEnd_918648 : Nat := 139765326308630227903769

theorem tailTrace_918648 : CollatzResearch.WordTrace tailWord_918648 prefixEnd_918648 139765326308630227903769 := by
  unfold tailWord_918648
  simp only [CollatzResearch.WordTrace]
  refine ⟨16752922587951331716326299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22337230117268442288435065 16752922587951331716326299)
  ·
    refine ⟨25129383881926997574489449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16752922587951331716326299 25129383881926997574489449)
    ·
      refine ⟨18847037911445248180867087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25129383881926997574489449 18847037911445248180867087)
      ·
        refine ⟨28270556867167872271300631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18847037911445248180867087 28270556867167872271300631)
        ·
          refine ⟨42405835300751808406950947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28270556867167872271300631 42405835300751808406950947)
          ·
            refine ⟨63608752951127712610426421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42405835300751808406950947 63608752951127712610426421)
            ·
              refine ⟨5963320589168223057227477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63608752951127712610426421 5963320589168223057227477)
              ·
                refine ⟨139765326308630227903769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5963320589168223057227477 139765326308630227903769)
                ·
                  rfl

theorem cell20_918648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 7].length) (baseStart_918648 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_918648 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_918648 prefixEnd_918648 := by exact prefixLift 918648
  have htrace : WordTrace (prefixWord ++ tailWord_918648) baseStart_918648 baseEnd_918648 := by
    simpa [prefixWord, tailWord_918648, baseEnd_918648] using wordTrace_append hprefix tailTrace_918648
  have hstable : (prefixWord ++ tailWord_918648).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918648).length < 2 ^ (prefixWord ++ tailWord_918648).sum := by decide
  have hdescent : baseEnd_918648 < baseStart_918648 := by decide
  rcases family_descends (prefixWord ++ tailWord_918648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918689 : List Nat := [1, 2, 3, 3, 1, 1, 4, 2, 3]
def baseStart_918689 : Nat := 118140960795 + 918689 * 2 ^ 59
def prefixEnd_918689 : Nat := 4983230072969 + 3 ^ 40 * 918689 * 2
def baseEnd_918689 : Nat := 419314692443076763344473

theorem tailTrace_918689 : CollatzResearch.WordTrace tailWord_918689 prefixEnd_918689 419314692443076763344473 := by
  unfold tailWord_918689
  simp only [CollatzResearch.WordTrace]
  refine ⟨33507340568754127434895121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22338227045836084956596747 33507340568754127434895121)
  ·
    refine ⟨25130505426565595576171341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33507340568754127434895121 25130505426565595576171341)
    ·
      refine ⟨9423939534962098341064253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25130505426565595576171341 9423939534962098341064253)
      ·
        refine ⟨3533977325610786877899095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9423939534962098341064253 3533977325610786877899095)
        ·
          refine ⟨5300965988416180316848643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3533977325610786877899095 5300965988416180316848643)
          ·
            refine ⟨7951448982624270475272965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5300965988416180316848643 7951448982624270475272965)
            ·
              refine ⟨1490896684242050714113681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7951448982624270475272965 1490896684242050714113681)
              ·
                refine ⟨1118172513181538035585261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1490896684242050714113681 1118172513181538035585261)
                ·
                  refine ⟨419314692443076763344473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1118172513181538035585261 419314692443076763344473)
                  ·
                    rfl

theorem cell20_918689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 4, 2, 3].length) (baseStart_918689 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_918689 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_918689 prefixEnd_918689 := by exact prefixLift 918689
  have htrace : WordTrace (prefixWord ++ tailWord_918689) baseStart_918689 baseEnd_918689 := by
    simpa [prefixWord, tailWord_918689, baseEnd_918689] using wordTrace_append hprefix tailTrace_918689
  have hstable : (prefixWord ++ tailWord_918689).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918689).length < 2 ^ (prefixWord ++ tailWord_918689).sum := by decide
  have hdescent : baseEnd_918689 < baseStart_918689 := by decide
  rcases family_descends (prefixWord ++ tailWord_918689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918692 : List Nat := [2, 3, 1, 2, 3, 1, 4, 2, 2]
def baseStart_918692 : Nat := 118140960795 + 918692 * 2 ^ 59
def prefixEnd_918692 : Nat := 4983230072969 + 3 ^ 40 * 918692 * 2
def baseEnd_918692 : Nat := 419316061724822086244461

theorem tailTrace_918692 : CollatzResearch.WordTrace tailWord_918692 prefixEnd_918692 419316061724822086244461 := by
  unfold tailWord_918692
  simp only [CollatzResearch.WordTrace]
  refine ⟨16753724993871629473627165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22338299991828839298169553 16753724993871629473627165)
  ·
    refine ⟨6282646872701861052610187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16753724993871629473627165 6282646872701861052610187)
    ·
      refine ⟨9423970309052791578915281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6282646872701861052610187 9423970309052791578915281)
      ·
        refine ⟨7067977731789593684186461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9423970309052791578915281 7067977731789593684186461)
        ·
          refine ⟨2650491649421097631569923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7067977731789593684186461 2650491649421097631569923)
          ·
            refine ⟨3975737474131646447354885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2650491649421097631569923 3975737474131646447354885)
            ·
              refine ⟨745450776399683708879041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3975737474131646447354885 745450776399683708879041)
              ·
                refine ⟨559088082299762781659281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 745450776399683708879041 559088082299762781659281)
                ·
                  refine ⟨419316061724822086244461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 559088082299762781659281 419316061724822086244461)
                  ·
                    rfl

theorem cell20_918692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 4, 2, 2].length) (baseStart_918692 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_918692 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_918692 prefixEnd_918692 := by exact prefixLift 918692
  have htrace : WordTrace (prefixWord ++ tailWord_918692) baseStart_918692 baseEnd_918692 := by
    simpa [prefixWord, tailWord_918692, baseEnd_918692] using wordTrace_append hprefix tailTrace_918692
  have hstable : (prefixWord ++ tailWord_918692).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918692).length < 2 ^ (prefixWord ++ tailWord_918692).sum := by decide
  have hdescent : baseEnd_918692 < baseStart_918692 := by decide
  rcases family_descends (prefixWord ++ tailWord_918692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918717 : List Nat := [1, 4, 1, 2, 1, 1, 3, 1, 6]
def baseStart_918717 : Nat := 118140960795 + 918717 * 2 ^ 59
def prefixEnd_918717 : Nat := 4983230072969 + 3 ^ 40 * 918717 * 2
def baseEnd_918717 : Nat := 419327472406033110411025

theorem tailTrace_918717 : CollatzResearch.WordTrace tailWord_918717 prefixEnd_918717 419327472406033110411025 := by
  unfold tailWord_918717
  simp only [CollatzResearch.WordTrace]
  refine ⟨33508361812652688216914405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22338907875101792144609603 33508361812652688216914405)
  ·
    refine ⟨6282817839872379040671451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33508361812652688216914405 6282817839872379040671451)
    ·
      refine ⟨9424226759808568561007177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6282817839872379040671451 9424226759808568561007177)
      ·
        refine ⟨7068170069856426420755383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9424226759808568561007177 7068170069856426420755383)
        ·
          refine ⟨10602255104784639631133075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7068170069856426420755383 10602255104784639631133075)
          ·
            refine ⟨15903382657176959446699613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10602255104784639631133075 15903382657176959446699613)
            ·
              refine ⟨5963768496441359792512355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15903382657176959446699613 5963768496441359792512355)
              ·
                refine ⟨8945652744662039688768533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5963768496441359792512355 8945652744662039688768533)
                ·
                  refine ⟨419327472406033110411025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8945652744662039688768533 419327472406033110411025)
                  ·
                    rfl

theorem cell20_918717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 1, 6].length) (baseStart_918717 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_918717 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_918717 prefixEnd_918717 := by exact prefixLift 918717
  have htrace : WordTrace (prefixWord ++ tailWord_918717) baseStart_918717 baseEnd_918717 := by
    simpa [prefixWord, tailWord_918717, baseEnd_918717] using wordTrace_append hprefix tailTrace_918717
  have hstable : (prefixWord ++ tailWord_918717).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918717).length < 2 ^ (prefixWord ++ tailWord_918717).sum := by decide
  have hdescent : baseEnd_918717 < baseStart_918717 := by decide
  rcases family_descends (prefixWord ++ tailWord_918717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918720 : List Nat := [2, 1, 1, 2, 6, 1, 3, 4]
def baseStart_918720 : Nat := 118140960795 + 918720 * 2 ^ 59
def prefixEnd_918720 : Nat := 4983230072969 + 3 ^ 40 * 918720 * 2
def baseEnd_918720 : Nat := 139776280562592811103671

theorem tailTrace_918720 : CollatzResearch.WordTrace tailWord_918720 prefixEnd_918720 139776280562592811103671 := by
  unfold tailWord_918720
  simp only [CollatzResearch.WordTrace]
  refine ⟨16754235615820909864636807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22338980821094546486182409 16754235615820909864636807)
  ·
    refine ⟨25131353423731364796955211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16754235615820909864636807 25131353423731364796955211)
    ·
      refine ⟨37697030135597047195432817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25131353423731364796955211 37697030135597047195432817)
      ·
        refine ⟨28272772601697785396574613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37697030135597047195432817 28272772601697785396574613)
        ·
          refine ⟨1325286215704583690464435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 28272772601697785396574613 1325286215704583690464435)
          ·
            refine ⟨1987929323556875535696653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1325286215704583690464435 1987929323556875535696653)
            ·
              refine ⟨745473496333828325886245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1987929323556875535696653 745473496333828325886245)
              ·
                refine ⟨139776280562592811103671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 745473496333828325886245 139776280562592811103671)
                ·
                  rfl

theorem cell20_918720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 3, 4].length) (baseStart_918720 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_918720 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_918720 prefixEnd_918720 := by exact prefixLift 918720
  have htrace : WordTrace (prefixWord ++ tailWord_918720) baseStart_918720 baseEnd_918720 := by
    simpa [prefixWord, tailWord_918720, baseEnd_918720] using wordTrace_append hprefix tailTrace_918720
  have hstable : (prefixWord ++ tailWord_918720).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918720).length < 2 ^ (prefixWord ++ tailWord_918720).sum := by decide
  have hdescent : baseEnd_918720 < baseStart_918720 := by decide
  rcases family_descends (prefixWord ++ tailWord_918720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918740 : List Nat := [2, 4, 1, 4, 2, 1, 1, 2, 3]
def baseStart_918740 : Nat := 118140960795 + 918740 * 2 ^ 59
def prefixEnd_918740 : Nat := 4983230072969 + 3 ^ 40 * 918740 * 2
def baseEnd_918740 : Nat := 419337970232747252644265

theorem tailTrace_918740 : CollatzResearch.WordTrace tailWord_918740 prefixEnd_918740 419337970232747252644265 := by
  unfold tailWord_918740
  simp only [CollatzResearch.WordTrace]
  refine ⟨16754600345784681572500837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22339467127712908763334449 16754600345784681572500837)
  ·
    refine ⟨3141487564834627794843907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16754600345784681572500837 3141487564834627794843907)
    ·
      refine ⟨4712231347251941692265861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3141487564834627794843907 4712231347251941692265861)
      ·
        refine ⟨883543377609739067299849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4712231347251941692265861 883543377609739067299849)
        ·
          refine ⟨662657533207304300474887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 883543377609739067299849 662657533207304300474887)
          ·
            refine ⟨993986299810956450712331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 662657533207304300474887 993986299810956450712331)
            ·
              refine ⟨1490979449716434676068497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 993986299810956450712331 1490979449716434676068497)
              ·
                refine ⟨1118234587287326007051373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1490979449716434676068497 1118234587287326007051373)
                ·
                  refine ⟨419337970232747252644265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1118234587287326007051373 419337970232747252644265)
                  ·
                    rfl

theorem cell20_918740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 1, 2, 3].length) (baseStart_918740 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_918740 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_918740 prefixEnd_918740 := by exact prefixLift 918740
  have htrace : WordTrace (prefixWord ++ tailWord_918740) baseStart_918740 baseEnd_918740 := by
    simpa [prefixWord, tailWord_918740, baseEnd_918740] using wordTrace_append hprefix tailTrace_918740
  have hstable : (prefixWord ++ tailWord_918740).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918740).length < 2 ^ (prefixWord ++ tailWord_918740).sum := by decide
  have hdescent : baseEnd_918740 < baseStart_918740 := by decide
  rcases family_descends (prefixWord ++ tailWord_918740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918741 : List Nat := [1, 3, 2, 4, 1, 2, 7]
def baseStart_918741 : Nat := 118140960795 + 918741 * 2 ^ 59
def prefixEnd_918741 : Nat := 4983230072969 + 3 ^ 40 * 918741 * 2
def baseEnd_918741 : Nat := 46593158517777299290103

theorem tailTrace_918741 : CollatzResearch.WordTrace tailWord_918741 prefixEnd_918741 46593158517777299290103 := by
  unfold tailWord_918741
  simp only [CollatzResearch.WordTrace]
  refine ⟨33509237164565740315788077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22339491443043826877192051 33509237164565740315788077)
  ·
    refine ⟨12565963936712152618420529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33509237164565740315788077 12565963936712152618420529)
    ·
      refine ⟨9424472952534114463815397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12565963936712152618420529 9424472952534114463815397)
      ·
        refine ⟨1767088678600146461965387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9424472952534114463815397 1767088678600146461965387)
        ·
          refine ⟨2650633017900219692948081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1767088678600146461965387 2650633017900219692948081)
          ·
            refine ⟨1987974763425164769711061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2650633017900219692948081 1987974763425164769711061)
            ·
              refine ⟨46593158517777299290103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1987974763425164769711061 46593158517777299290103)
              ·
                rfl

theorem cell20_918741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 7].length) (baseStart_918741 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_918741 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_918741 prefixEnd_918741 := by exact prefixLift 918741
  have htrace : WordTrace (prefixWord ++ tailWord_918741) baseStart_918741 baseEnd_918741 := by
    simpa [prefixWord, tailWord_918741, baseEnd_918741] using wordTrace_append hprefix tailTrace_918741
  have hstable : (prefixWord ++ tailWord_918741).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918741).length < 2 ^ (prefixWord ++ tailWord_918741).sum := by decide
  have hdescent : baseEnd_918741 < baseStart_918741 := by decide
  rcases family_descends (prefixWord ++ tailWord_918741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918744 : List Nat := [2, 1, 2, 2, 5, 2, 1, 2, 3]
def baseStart_918744 : Nat := 118140960795 + 918744 * 2 ^ 59
def prefixEnd_918744 : Nat := 4983230072969 + 3 ^ 40 * 918744 * 2
def baseEnd_918744 : Nat := 419339795941741016510915

theorem tailTrace_918744 : CollatzResearch.WordTrace tailWord_918744 prefixEnd_918744 419339795941741016510915 := by
  unfold tailWord_918744
  simp only [CollatzResearch.WordTrace]
  refine ⟨16754673291777435914073643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22339564389036581218764857 16754673291777435914073643)
  ·
    refine ⟨25132009937666153871110465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16754673291777435914073643 25132009937666153871110465)
    ·
      refine ⟨18849007453249615403332849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25132009937666153871110465 18849007453249615403332849)
      ·
        refine ⟨14136755589937211552499637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18849007453249615403332849 14136755589937211552499637)
        ·
          refine ⟨1325320836556613583046841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14136755589937211552499637 1325320836556613583046841)
          ·
            refine ⟨993990627417460187285131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1325320836556613583046841 993990627417460187285131)
            ·
              refine ⟨1490985941126190280927697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 993990627417460187285131 1490985941126190280927697)
              ·
                refine ⟨1118239455844642710695773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1490985941126190280927697 1118239455844642710695773)
                ·
                  refine ⟨419339795941741016510915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1118239455844642710695773 419339795941741016510915)
                  ·
                    rfl

theorem cell20_918744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 1, 2, 3].length) (baseStart_918744 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_918744 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_918744 prefixEnd_918744 := by exact prefixLift 918744
  have htrace : WordTrace (prefixWord ++ tailWord_918744) baseStart_918744 baseEnd_918744 := by
    simpa [prefixWord, tailWord_918744, baseEnd_918744] using wordTrace_append hprefix tailTrace_918744
  have hstable : (prefixWord ++ tailWord_918744).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918744).length < 2 ^ (prefixWord ++ tailWord_918744).sum := by decide
  have hdescent : baseEnd_918744 < baseStart_918744 := by decide
  rcases family_descends (prefixWord ++ tailWord_918744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918802 : List Nat := [3, 2, 4, 2, 1, 1, 3, 2, 2]
def baseStart_918802 : Nat := 118140960795 + 918802 * 2 ^ 59
def prefixEnd_918802 : Nat := 4983230072969 + 3 ^ 40 * 918802 * 2
def baseEnd_918802 : Nat := 419366268722150592577345

theorem tailTrace_918802 : CollatzResearch.WordTrace tailWord_918802 prefixEnd_918802 419366268722150592577345 := by
  unfold tailWord_918802
  simp only [CollatzResearch.WordTrace]
  refine ⟨8377865504336186933439665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22340974678229831822505773 8377865504336186933439665)
  ·
    refine ⟨6283399128252140200079749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8377865504336186933439665 6283399128252140200079749)
    ·
      refine ⟨1178137336547276287514953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6283399128252140200079749 1178137336547276287514953)
      ·
        refine ⟨883603002410457215636215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1178137336547276287514953 883603002410457215636215)
        ·
          refine ⟨1325404503615685823454323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 883603002410457215636215 1325404503615685823454323)
          ·
            refine ⟨1988106755423528735181485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1325404503615685823454323 1988106755423528735181485)
            ·
              refine ⟨745540033283823275693057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1988106755423528735181485 745540033283823275693057)
              ·
                refine ⟨559155024962867456769793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 745540033283823275693057 559155024962867456769793)
                ·
                  refine ⟨419366268722150592577345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 559155024962867456769793 419366268722150592577345)
                  ·
                    rfl

theorem cell20_918802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 3, 2, 2].length) (baseStart_918802 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_918802 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_918802 prefixEnd_918802 := by exact prefixLift 918802
  have htrace : WordTrace (prefixWord ++ tailWord_918802) baseStart_918802 baseEnd_918802 := by
    simpa [prefixWord, tailWord_918802, baseEnd_918802] using wordTrace_append hprefix tailTrace_918802
  have hstable : (prefixWord ++ tailWord_918802).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918802).length < 2 ^ (prefixWord ++ tailWord_918802).sum := by decide
  have hdescent : baseEnd_918802 < baseStart_918802 := by decide
  rcases family_descends (prefixWord ++ tailWord_918802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918810 : List Nat := [3, 1, 1, 3, 3, 1, 3, 1, 4]
def baseStart_918810 : Nat := 118140960795 + 918810 * 2 ^ 59
def prefixEnd_918810 : Nat := 4983230072969 + 3 ^ 40 * 918810 * 2
def baseEnd_918810 : Nat := 419369920140138120310645

theorem tailTrace_918810 : CollatzResearch.WordTrace tailWord_918810 prefixEnd_918810 419369920140138120310645 := by
  unfold tailWord_918810
  simp only [CollatzResearch.WordTrace]
  refine ⟨8377938450328941275012471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22341169200877176733366589 8377938450328941275012471)
  ·
    refine ⟨12566907675493411912518707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8377938450328941275012471 12566907675493411912518707)
    ·
      refine ⟨18850361513240117868778061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12566907675493411912518707 18850361513240117868778061)
      ·
        refine ⟨7068885567465044200791773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18850361513240117868778061 7068885567465044200791773)
        ·
          refine ⟨2650832087799391575296915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7068885567465044200791773 2650832087799391575296915)
          ·
            refine ⟨3976248131699087362945373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2650832087799391575296915 3976248131699087362945373)
            ·
              refine ⟨1491093049387157761104515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3976248131699087362945373 1491093049387157761104515)
              ·
                refine ⟨2236639574080736641656773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1491093049387157761104515 2236639574080736641656773)
                ·
                  refine ⟨419369920140138120310645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2236639574080736641656773 419369920140138120310645)
                  ·
                    rfl

theorem cell20_918810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 3, 1, 4].length) (baseStart_918810 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_918810 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_918810 prefixEnd_918810 := by exact prefixLift 918810
  have htrace : WordTrace (prefixWord ++ tailWord_918810) baseStart_918810 baseEnd_918810 := by
    simpa [prefixWord, tailWord_918810, baseEnd_918810] using wordTrace_append hprefix tailTrace_918810
  have hstable : (prefixWord ++ tailWord_918810).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918810).length < 2 ^ (prefixWord ++ tailWord_918810).sum := by decide
  have hdescent : baseEnd_918810 < baseStart_918810 := by decide
  rcases family_descends (prefixWord ++ tailWord_918810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918848 : List Nat := [2, 1, 1, 2, 2, 1, 4, 5, 2]
def baseStart_918848 : Nat := 118140960795 + 918848 * 2 ^ 59
def prefixEnd_918848 : Nat := 4983230072969 + 3 ^ 40 * 918848 * 2
def baseEnd_918848 : Nat := 419387264375578877043823

theorem tailTrace_918848 : CollatzResearch.WordTrace tailWord_918848 prefixEnd_918848 419387264375578877043823 := by
  unfold tailWord_918848
  simp only [CollatzResearch.WordTrace]
  refine ⟨16756569887589048794966599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22342093183452065059955465 16756569887589048794966599)
  ·
    refine ⟨25134854831383573192449899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16756569887589048794966599 25134854831383573192449899)
    ·
      refine ⟨37702282247075359788674849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25134854831383573192449899 37702282247075359788674849)
      ·
        refine ⟨28276711685306519841506137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37702282247075359788674849 28276711685306519841506137)
        ·
          refine ⟨21207533763979889881129603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28276711685306519841506137 21207533763979889881129603)
          ·
            refine ⟨31811300645969834821694405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21207533763979889881129603 31811300645969834821694405)
            ·
              refine ⟨5964618871119344029067701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31811300645969834821694405 5964618871119344029067701)
              ·
                refine ⟨559183019167438502725097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5964618871119344029067701 559183019167438502725097)
                ·
                  refine ⟨419387264375578877043823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 559183019167438502725097 419387264375578877043823)
                  ·
                    rfl

theorem cell20_918848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 5, 2].length) (baseStart_918848 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_918848 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_918848 prefixEnd_918848 := by exact prefixLift 918848
  have htrace : WordTrace (prefixWord ++ tailWord_918848) baseStart_918848 baseEnd_918848 := by
    simpa [prefixWord, tailWord_918848, baseEnd_918848] using wordTrace_append hprefix tailTrace_918848
  have hstable : (prefixWord ++ tailWord_918848).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918848).length < 2 ^ (prefixWord ++ tailWord_918848).sum := by decide
  have hdescent : baseEnd_918848 < baseStart_918848 := by decide
  rcases family_descends (prefixWord ++ tailWord_918848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918854 : List Nat := [6, 1, 1, 3, 1, 1, 2, 2, 3]
def baseStart_918854 : Nat := 118140960795 + 918854 * 2 ^ 59
def prefixEnd_918854 : Nat := 4983230072969 + 3 ^ 40 * 918854 * 2
def baseEnd_918854 : Nat := 419390002939069522843799

theorem tailTrace_918854 : CollatzResearch.WordTrace tailWord_918854 prefixEnd_918854 419390002939069522843799 := by
  unfold tailWord_918854
  simp only [CollatzResearch.WordTrace]
  refine ⟨1047292456661136269207863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 22342239075437573743101077 1047292456661136269207863)
  ·
    refine ⟨1570938684991704403811795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1047292456661136269207863 1570938684991704403811795)
    ·
      refine ⟨2356408027487556605717693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1570938684991704403811795 2356408027487556605717693)
      ·
        refine ⟨883653010307833727144135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2356408027487556605717693 883653010307833727144135)
        ·
          refine ⟨1325479515461750590716203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 883653010307833727144135 1325479515461750590716203)
          ·
            refine ⟨1988219273192625886074305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1325479515461750590716203 1988219273192625886074305)
            ·
              refine ⟨1491164454894469414555729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1988219273192625886074305 1491164454894469414555729)
              ·
                refine ⟨1118373341170852060916797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1491164454894469414555729 1118373341170852060916797)
                ·
                  refine ⟨419390002939069522843799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1118373341170852060916797 419390002939069522843799)
                  ·
                    rfl

theorem cell20_918854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_918854 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_918854 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_918854 prefixEnd_918854 := by exact prefixLift 918854
  have htrace : WordTrace (prefixWord ++ tailWord_918854) baseStart_918854 baseEnd_918854 := by
    simpa [prefixWord, tailWord_918854, baseEnd_918854] using wordTrace_append hprefix tailTrace_918854
  have hstable : (prefixWord ++ tailWord_918854).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918854).length < 2 ^ (prefixWord ++ tailWord_918854).sum := by decide
  have hdescent : baseEnd_918854 < baseStart_918854 := by decide
  rcases family_descends (prefixWord ++ tailWord_918854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918861 : List Nat := [1, 6, 1, 3, 1, 1, 1, 4, 2]
def baseStart_918861 : Nat := 118140960795 + 918861 * 2 ^ 59
def prefixEnd_918861 : Nat := 4983230072969 + 3 ^ 40 * 918861 * 2
def baseEnd_918861 : Nat := 419393197929808609610437

theorem tailTrace_918861 : CollatzResearch.WordTrace tailWord_918861 prefixEnd_918861 419393197929808609610437 := by
  unfold tailWord_918861
  simp only [CollatzResearch.WordTrace]
  refine ⟨33513613924131000810156437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22342409282754000540104291 33513613924131000810156437)
  ·
    refine ⟨1570950652693640662976083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 33513613924131000810156437 1570950652693640662976083)
    ·
      refine ⟨2356425979040460994464125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1570950652693640662976083 2356425979040460994464125)
      ·
        refine ⟨883659742140172872924047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2356425979040460994464125 883659742140172872924047)
        ·
          refine ⟨1325489613210259309386071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 883659742140172872924047 1325489613210259309386071)
          ·
            refine ⟨1988234419815388964079107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1325489613210259309386071 1988234419815388964079107)
            ·
              refine ⟨2982351629723083446118661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1988234419815388964079107 2982351629723083446118661)
              ·
                refine ⟨559190930573078146147249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2982351629723083446118661 559190930573078146147249)
                ·
                  refine ⟨419393197929808609610437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 559190930573078146147249 419393197929808609610437)
                  ·
                    rfl

theorem cell20_918861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 4, 2].length) (baseStart_918861 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_918861 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_918861 prefixEnd_918861 := by exact prefixLift 918861
  have htrace : WordTrace (prefixWord ++ tailWord_918861) baseStart_918861 baseEnd_918861 := by
    simpa [prefixWord, tailWord_918861, baseEnd_918861] using wordTrace_append hprefix tailTrace_918861
  have hstable : (prefixWord ++ tailWord_918861).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918861).length < 2 ^ (prefixWord ++ tailWord_918861).sum := by decide
  have hdescent : baseEnd_918861 < baseStart_918861 := by decide
  rcases family_descends (prefixWord ++ tailWord_918861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918913 : List Nat := [1, 2, 4, 3, 3, 1, 1, 2, 3]
def baseStart_918913 : Nat := 118140960795 + 918913 * 2 ^ 59
def prefixEnd_918913 : Nat := 4983230072969 + 3 ^ 40 * 918913 * 2
def baseEnd_918913 : Nat := 419416932146727539876891

theorem tailTrace_918913 : CollatzResearch.WordTrace tailWord_918913 prefixEnd_918913 419416932146727539876891 := by
  unfold tailWord_918913
  simp only [CollatzResearch.WordTrace]
  refine ⟨33515510519942613691049393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22343673679961742460699595 33515510519942613691049393)
  ·
    refine ⟨25136632889956960268287045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33515510519942613691049393 25136632889956960268287045)
    ·
      refine ⟨4713118666866930050303821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25136632889956960268287045 4713118666866930050303821)
      ·
        refine ⟨1767419500075098768863933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4713118666866930050303821 1767419500075098768863933)
        ·
          refine ⟨662782312528162038323975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1767419500075098768863933 662782312528162038323975)
          ·
            refine ⟨994173468792243057485963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 662782312528162038323975 994173468792243057485963)
            ·
              refine ⟨1491260203188364586228945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 994173468792243057485963 1491260203188364586228945)
              ·
                refine ⟨1118445152391273439671709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1491260203188364586228945 1118445152391273439671709)
                ·
                  refine ⟨419416932146727539876891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1118445152391273439671709 419416932146727539876891)
                  ·
                    rfl

theorem cell20_918913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 1, 2, 3].length) (baseStart_918913 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_918913 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_918913 prefixEnd_918913 := by exact prefixLift 918913
  have htrace : WordTrace (prefixWord ++ tailWord_918913) baseStart_918913 baseEnd_918913 := by
    simpa [prefixWord, tailWord_918913, baseEnd_918913] using wordTrace_append hprefix tailTrace_918913
  have hstable : (prefixWord ++ tailWord_918913).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918913).length < 2 ^ (prefixWord ++ tailWord_918913).sum := by decide
  have hdescent : baseEnd_918913 < baseStart_918913 := by decide
  rcases family_descends (prefixWord ++ tailWord_918913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918924 : List Nat := [2, 2, 1, 2, 1, 3, 1, 6, 2]
def baseStart_918924 : Nat := 118140960795 + 918924 * 2 ^ 59
def prefixEnd_918924 : Nat := 4983230072969 + 3 ^ 40 * 918924 * 2
def baseEnd_918924 : Nat := 419421952846460390510179

theorem tailTrace_918924 : CollatzResearch.WordTrace tailWord_918924 prefixEnd_918924 419421952846460390510179 := by
  unfold tailWord_918924
  simp only [CollatzResearch.WordTrace]
  refine ⟨16757955861451381284849913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22343941148601841713133217 16757955861451381284849913)
  ·
    refine ⟨12568466896088535963637435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16757955861451381284849913 12568466896088535963637435)
    ·
      refine ⟨18852700344132803945456153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12568466896088535963637435 18852700344132803945456153)
      ·
        refine ⟨14139525258099602959092115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18852700344132803945456153 14139525258099602959092115)
        ·
          refine ⟨21209287887149404438638173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14139525258099602959092115 21209287887149404438638173)
          ·
            refine ⟨7953482957681026664489315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21209287887149404438638173 7953482957681026664489315)
            ·
              refine ⟨11930224436521539996733973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7953482957681026664489315 11930224436521539996733973)
              ·
                refine ⟨559229270461947187346905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11930224436521539996733973 559229270461947187346905)
                ·
                  refine ⟨419421952846460390510179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 559229270461947187346905 419421952846460390510179)
                  ·
                    rfl

theorem cell20_918924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 6, 2].length) (baseStart_918924 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_918924 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_918924 prefixEnd_918924 := by exact prefixLift 918924
  have htrace : WordTrace (prefixWord ++ tailWord_918924) baseStart_918924 baseEnd_918924 := by
    simpa [prefixWord, tailWord_918924, baseEnd_918924] using wordTrace_append hprefix tailTrace_918924
  have hstable : (prefixWord ++ tailWord_918924).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918924).length < 2 ^ (prefixWord ++ tailWord_918924).sum := by decide
  have hdescent : baseEnd_918924 < baseStart_918924 := by decide
  rcases family_descends (prefixWord ++ tailWord_918924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918962 : List Nat := [3, 2, 1, 1, 1, 1, 2, 7, 2]
def baseStart_918962 : Nat := 118140960795 + 918962 * 2 ^ 59
def prefixEnd_918962 : Nat := 4983230072969 + 3 ^ 40 * 918962 * 2
def baseEnd_918962 : Nat := 419439297081901147243357

theorem tailTrace_918962 : CollatzResearch.WordTrace tailWord_918962 prefixEnd_918962 419439297081901147243357 := by
  unfold tailWord_918962
  simp only [CollatzResearch.WordTrace]
  refine ⟨8379324424191273764895785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22344865131176730039722093 8379324424191273764895785)
  ·
    refine ⟨6284493318143455323671839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8379324424191273764895785 6284493318143455323671839)
    ·
      refine ⟨9426739977215182985507759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6284493318143455323671839 9426739977215182985507759)
      ·
        refine ⟨14140109965822774478261639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9426739977215182985507759 14140109965822774478261639)
        ·
          refine ⟨21210164948734161717392459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14140109965822774478261639 21210164948734161717392459)
          ·
            refine ⟨31815247423101242576088689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21210164948734161717392459 31815247423101242576088689)
            ·
              refine ⟨23861435567325931932066517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31815247423101242576088689 23861435567325931932066517)
              ·
                refine ⟨559252396109201529657809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 23861435567325931932066517 559252396109201529657809)
                ·
                  refine ⟨419439297081901147243357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 559252396109201529657809 419439297081901147243357)
                  ·
                    rfl

theorem cell20_918962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 7, 2].length) (baseStart_918962 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_918962 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_918962 prefixEnd_918962 := by exact prefixLift 918962
  have htrace : WordTrace (prefixWord ++ tailWord_918962) baseStart_918962 baseEnd_918962 := by
    simpa [prefixWord, tailWord_918962, baseEnd_918962] using wordTrace_append hprefix tailTrace_918962
  have hstable : (prefixWord ++ tailWord_918962).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918962).length < 2 ^ (prefixWord ++ tailWord_918962).sum := by decide
  have hdescent : baseEnd_918962 < baseStart_918962 := by decide
  rcases family_descends (prefixWord ++ tailWord_918962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918969 : List Nat := [1, 2, 1, 4, 4, 2, 6]
def baseStart_918969 : Nat := 118140960795 + 918969 * 2 ^ 59
def prefixEnd_918969 : Nat := 4983230072969 + 3 ^ 40 * 918969 * 2
def baseEnd_918969 : Nat := 46604721341404470445555

theorem tailTrace_918969 : CollatzResearch.WordTrace tailWord_918969 prefixEnd_918969 46604721341404470445555 := by
  unfold tailWord_918969
  simp only [CollatzResearch.WordTrace]
  refine ⟨33517553007739735255087961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22345035338493156836725307 33517553007739735255087961)
  ·
    refine ⟨25138164755804801441315971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33517553007739735255087961 25138164755804801441315971)
    ·
      refine ⟨37707247133707202161973957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25138164755804801441315971 37707247133707202161973957)
      ·
        refine ⟨7070108837570100405370117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37707247133707202161973957 7070108837570100405370117)
        ·
          refine ⟨1325645407044393826006897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7070108837570100405370117 1325645407044393826006897)
          ·
            refine ⟨994234055283295369505173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1325645407044393826006897 994234055283295369505173)
            ·
              refine ⟨46604721341404470445555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 994234055283295369505173 46604721341404470445555)
              ·
                rfl

theorem cell20_918969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 6].length) (baseStart_918969 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_918969 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_918969 prefixEnd_918969 := by exact prefixLift 918969
  have htrace : WordTrace (prefixWord ++ tailWord_918969) baseStart_918969 baseEnd_918969 := by
    simpa [prefixWord, tailWord_918969, baseEnd_918969] using wordTrace_append hprefix tailTrace_918969
  have hstable : (prefixWord ++ tailWord_918969).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918969).length < 2 ^ (prefixWord ++ tailWord_918969).sum := by decide
  have hdescent : baseEnd_918969 < baseStart_918969 := by decide
  rcases family_descends (prefixWord ++ tailWord_918969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918990 : List Nat := [4, 1, 1, 1, 2, 1, 3, 7]
def baseStart_918990 : Nat := 118140960795 + 918990 * 2 ^ 59
def prefixEnd_918990 : Nat := 4983230072969 + 3 ^ 40 * 918990 * 2
def baseEnd_918990 : Nat := 139817359014952498103303

theorem tailTrace_918990 : CollatzResearch.WordTrace tailWord_918990 prefixEnd_918990 139817359014952498103303 := by
  unfold tailWord_918990
  simp only [CollatzResearch.WordTrace]
  refine ⟨4189789867582956980200303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22345545960442437227734949 4189789867582956980200303)
  ·
    refine ⟨6284684801374435470300455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4189789867582956980200303 6284684801374435470300455)
    ·
      refine ⟨9427027202061653205450683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6284684801374435470300455 9427027202061653205450683)
      ·
        refine ⟨14140540803092479808176025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9427027202061653205450683 14140540803092479808176025)
        ·
          refine ⟨10605405602319359856132019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14140540803092479808176025 10605405602319359856132019)
          ·
            refine ⟨15908108403479039784198029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10605405602319359856132019 15908108403479039784198029)
            ·
              refine ⟨5965540651304639919074261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15908108403479039784198029 5965540651304639919074261)
              ·
                refine ⟨139817359014952498103303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5965540651304639919074261 139817359014952498103303)
                ·
                  rfl

theorem cell20_918990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 7].length) (baseStart_918990 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_918990 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_918990 prefixEnd_918990 := by exact prefixLift 918990
  have htrace : WordTrace (prefixWord ++ tailWord_918990) baseStart_918990 baseEnd_918990 := by
    simpa [prefixWord, tailWord_918990, baseEnd_918990] using wordTrace_append hprefix tailTrace_918990
  have hstable : (prefixWord ++ tailWord_918990).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918990).length < 2 ^ (prefixWord ++ tailWord_918990).sum := by decide
  have hdescent : baseEnd_918990 < baseStart_918990 := by decide
  rcases family_descends (prefixWord ++ tailWord_918990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919059 : List Nat := [1, 1, 1, 2, 1, 7, 1, 2, 4]
def baseStart_919059 : Nat := 118140960795 + 919059 * 2 ^ 59
def prefixEnd_919059 : Nat := 4983230072969 + 3 ^ 40 * 919059 * 2
def baseEnd_919059 : Nat := 419483570524999921009627

theorem tailTrace_919059 : CollatzResearch.WordTrace tailWord_919059 prefixEnd_919059 419483570524999921009627 := by
  unfold tailWord_919059
  simp only [CollatzResearch.WordTrace]
  refine ⟨33520835577413680625864231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22347223718275787083909487 33520835577413680625864231)
  ·
    refine ⟨50281253366120520938796347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33520835577413680625864231 50281253366120520938796347)
    ·
      refine ⟨75421880049180781408194521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50281253366120520938796347 75421880049180781408194521)
      ·
        refine ⟨56566410036885586056145891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75421880049180781408194521 56566410036885586056145891)
        ·
          refine ⟨84849615055328379084218837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56566410036885586056145891 84849615055328379084218837)
          ·
            refine ⟨1988662852859258884786379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 84849615055328379084218837 1988662852859258884786379)
            ·
              refine ⟨2982994279288888327179569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1988662852859258884786379 2982994279288888327179569)
              ·
                refine ⟨2237245709466666245384677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2982994279288888327179569 2237245709466666245384677)
                ·
                  refine ⟨419483570524999921009627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2237245709466666245384677 419483570524999921009627)
                  ·
                    rfl

theorem cell20_919059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 2, 4].length) (baseStart_919059 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_919059 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_919059 prefixEnd_919059 := by exact prefixLift 919059
  have htrace : WordTrace (prefixWord ++ tailWord_919059) baseStart_919059 baseEnd_919059 := by
    simpa [prefixWord, tailWord_919059, baseEnd_919059] using wordTrace_append hprefix tailTrace_919059
  have hstable : (prefixWord ++ tailWord_919059).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919059).length < 2 ^ (prefixWord ++ tailWord_919059).sum := by decide
  have hdescent : baseEnd_919059 < baseStart_919059 := by decide
  rcases family_descends (prefixWord ++ tailWord_919059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919086 : List Nat := [4, 1, 3, 1, 2, 3, 1, 2, 3]
def baseStart_919086 : Nat := 118140960795 + 919086 * 2 ^ 59
def prefixEnd_919086 : Nat := 4983230072969 + 3 ^ 40 * 919086 * 2
def baseEnd_919086 : Nat := 419495894060707827109517

theorem tailTrace_919086 : CollatzResearch.WordTrace tailWord_919086 prefixEnd_919086 419495894060707827109517 := by
  unfold tailWord_919086
  simp only [CollatzResearch.WordTrace]
  refine ⟨4190227543539483029637139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22347880232210576158064741 4190227543539483029637139)
  ·
    refine ⟨6285341315309224544455709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4190227543539483029637139 6285341315309224544455709)
    ·
      refine ⟨2357002993240959204170891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6285341315309224544455709 2357002993240959204170891)
      ·
        refine ⟨3535504489861438806256337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2357002993240959204170891 3535504489861438806256337)
        ·
          refine ⟨2651628367396079104692253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3535504489861438806256337 2651628367396079104692253)
          ·
            refine ⟨994360637773529664259595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2651628367396079104692253 994360637773529664259595)
            ·
              refine ⟨1491540956660294496389393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 994360637773529664259595 1491540956660294496389393)
              ·
                refine ⟨1118655717495220872292045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1491540956660294496389393 1118655717495220872292045)
                ·
                  refine ⟨419495894060707827109517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1118655717495220872292045 419495894060707827109517)
                  ·
                    rfl

theorem cell20_919086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 1, 2, 3].length) (baseStart_919086 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_919086 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_919086 prefixEnd_919086 := by exact prefixLift 919086
  have htrace : WordTrace (prefixWord ++ tailWord_919086) baseStart_919086 baseEnd_919086 := by
    simpa [prefixWord, tailWord_919086, baseEnd_919086] using wordTrace_append hprefix tailTrace_919086
  have hstable : (prefixWord ++ tailWord_919086).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919086).length < 2 ^ (prefixWord ++ tailWord_919086).sum := by decide
  have hdescent : baseEnd_919086 < baseStart_919086 := by decide
  rcases family_descends (prefixWord ++ tailWord_919086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919097 : List Nat := [1, 2, 1, 5, 1, 2, 1, 3, 4]
def baseStart_919097 : Nat := 118140960795 + 919097 * 2 ^ 59
def prefixEnd_919097 : Nat := 4983230072969 + 3 ^ 40 * 919097 * 2
def baseEnd_919097 : Nat := 419500914760440677742805

theorem tailTrace_919097 : CollatzResearch.WordTrace tailWord_919097 prefixEnd_919097 419500914760440677742805 := by
  unfold tailWord_919097
  simp only [CollatzResearch.WordTrace]
  refine ⟨33522221551276013115747545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22348147700850675410498363 33522221551276013115747545)
  ·
    refine ⟨25141666163457009836810659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33522221551276013115747545 25141666163457009836810659)
    ·
      refine ⟨37712499245185514755215989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25141666163457009836810659 37712499245185514755215989)
      ·
        refine ⟨3535546804236142008301499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37712499245185514755215989 3535546804236142008301499)
        ·
          refine ⟨5303320206354213012452249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3535546804236142008301499 5303320206354213012452249)
          ·
            refine ⟨3977490154765659759339187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5303320206354213012452249 3977490154765659759339187)
            ·
              refine ⟨5966235232148489639008781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3977490154765659759339187 5966235232148489639008781)
              ·
                refine ⟨2237338212055683614628293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5966235232148489639008781 2237338212055683614628293)
                ·
                  refine ⟨419500914760440677742805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2237338212055683614628293 419500914760440677742805)
                  ·
                    rfl

theorem cell20_919097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 3, 4].length) (baseStart_919097 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_919097 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_919097 prefixEnd_919097 := by exact prefixLift 919097
  have htrace : WordTrace (prefixWord ++ tailWord_919097) baseStart_919097 baseEnd_919097 := by
    simpa [prefixWord, tailWord_919097, baseEnd_919097] using wordTrace_append hprefix tailTrace_919097
  have hstable : (prefixWord ++ tailWord_919097).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919097).length < 2 ^ (prefixWord ++ tailWord_919097).sum := by decide
  have hdescent : baseEnd_919097 < baseStart_919097 := by decide
  rcases family_descends (prefixWord ++ tailWord_919097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919117 : List Nat := [1, 6, 1, 1, 3, 2, 2, 4]
def baseStart_919117 : Nat := 118140960795 + 919117 * 2 ^ 59
def prefixEnd_919117 : Nat := 4983230072969 + 3 ^ 40 * 919117 * 2
def baseEnd_919117 : Nat := 139836681101803165692019

theorem tailTrace_919117 : CollatzResearch.WordTrace tailWord_919117 prefixEnd_919117 139836681101803165692019 := by
  unfold tailWord_919117
  simp only [CollatzResearch.WordTrace]
  refine ⟨33522951011203556531475605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22348634007469037687650403 33522951011203556531475605)
  ·
    refine ⟨1571388328650166712412919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 33522951011203556531475605 1571388328650166712412919)
    ·
      refine ⟨2357082492975250068619379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1571388328650166712412919 2357082492975250068619379)
      ·
        refine ⟨3535623739462875102929069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2357082492975250068619379 3535623739462875102929069)
        ·
          refine ⟨1325858902298578163598401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3535623739462875102929069 1325858902298578163598401)
          ·
            refine ⟨994394176723933622698801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1325858902298578163598401 994394176723933622698801)
            ·
              refine ⟨745795632542950217024101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 994394176723933622698801 745795632542950217024101)
              ·
                refine ⟨139836681101803165692019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 745795632542950217024101 139836681101803165692019)
                ·
                  rfl

theorem cell20_919117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 2, 4].length) (baseStart_919117 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_919117 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_919117 prefixEnd_919117 := by exact prefixLift 919117
  have htrace : WordTrace (prefixWord ++ tailWord_919117) baseStart_919117 baseEnd_919117 := by
    simpa [prefixWord, tailWord_919117, baseEnd_919117] using wordTrace_append hprefix tailTrace_919117
  have hstable : (prefixWord ++ tailWord_919117).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919117).length < 2 ^ (prefixWord ++ tailWord_919117).sum := by decide
  have hdescent : baseEnd_919117 < baseStart_919117 := by decide
  rcases family_descends (prefixWord ++ tailWord_919117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919152 : List Nat := [2, 1, 1, 1, 6, 3, 1, 1, 4]
def baseStart_919152 : Nat := 118140960795 + 919152 * 2 ^ 59
def prefixEnd_919152 : Nat := 4983230072969 + 3 ^ 40 * 919152 * 2
def baseEnd_919152 : Nat := 419526018259104930909247

theorem tailTrace_919152 : CollatzResearch.WordTrace tailWord_919152 prefixEnd_919152 419526018259104930909247 := by
  unfold tailWord_919152
  simp only [CollatzResearch.WordTrace]
  refine ⟨16762113783038378754499855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22349485044051171672666473 16762113783038378754499855)
  ·
    refine ⟨25143170674557568131749783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16762113783038378754499855 25143170674557568131749783)
    ·
      refine ⟨37714756011836352197624675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25143170674557568131749783 37714756011836352197624675)
      ·
        refine ⟨56572134017754528296437013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37714756011836352197624675 56572134017754528296437013)
        ·
          refine ⟨2651818782082243513895485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 56572134017754528296437013 2651818782082243513895485)
          ·
            refine ⟨994432043280841317710807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2651818782082243513895485 994432043280841317710807)
            ·
              refine ⟨1491648064921261976566211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 994432043280841317710807 1491648064921261976566211)
              ·
                refine ⟨2237472097381892964849317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1491648064921261976566211 2237472097381892964849317)
                ·
                  refine ⟨419526018259104930909247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2237472097381892964849317 419526018259104930909247)
                  ·
                    rfl

theorem cell20_919152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 1, 1, 4].length) (baseStart_919152 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_919152 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_919152 prefixEnd_919152 := by exact prefixLift 919152
  have htrace : WordTrace (prefixWord ++ tailWord_919152) baseStart_919152 baseEnd_919152 := by
    simpa [prefixWord, tailWord_919152, baseEnd_919152] using wordTrace_append hprefix tailTrace_919152
  have hstable : (prefixWord ++ tailWord_919152).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919152).length < 2 ^ (prefixWord ++ tailWord_919152).sum := by decide
  have hdescent : baseEnd_919152 < baseStart_919152 := by decide
  rcases family_descends (prefixWord ++ tailWord_919152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919204 : List Nat := [2, 3, 1, 2, 2, 2, 1, 4, 3]
def baseStart_919204 : Nat := 118140960795 + 919204 * 2 ^ 59
def prefixEnd_919204 : Nat := 4983230072969 + 3 ^ 40 * 919204 * 2
def baseEnd_919204 : Nat := 419549752476023861175701

theorem tailTrace_919204 : CollatzResearch.WordTrace tailWord_919204 prefixEnd_919204 419549752476023861175701 := by
  unfold tailWord_919204
  simp only [CollatzResearch.WordTrace]
  refine ⟨16763062080944185194946333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22350749441258913593261777 16763062080944185194946333)
  ·
    refine ⟨6286148280354069448104875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16763062080944185194946333 6286148280354069448104875)
    ·
      refine ⟨9429222420531104172157313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6286148280354069448104875 9429222420531104172157313)
      ·
        refine ⟨7071916815398328129117985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9429222420531104172157313 7071916815398328129117985)
        ·
          refine ⟨5303937611548746096838489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7071916815398328129117985 5303937611548746096838489)
          ·
            refine ⟨3977953208661559572628867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5303937611548746096838489 3977953208661559572628867)
            ·
              refine ⟨5966929812992339358943301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3977953208661559572628867 5966929812992339358943301)
              ·
                refine ⟨1118799339936063629801869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5966929812992339358943301 1118799339936063629801869)
                ·
                  refine ⟨419549752476023861175701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1118799339936063629801869 419549752476023861175701)
                  ·
                    rfl

theorem cell20_919204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 4, 3].length) (baseStart_919204 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_919204 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_919204 prefixEnd_919204 := by exact prefixLift 919204
  have htrace : WordTrace (prefixWord ++ tailWord_919204) baseStart_919204 baseEnd_919204 := by
    simpa [prefixWord, tailWord_919204, baseEnd_919204] using wordTrace_append hprefix tailTrace_919204
  have hstable : (prefixWord ++ tailWord_919204).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919204).length < 2 ^ (prefixWord ++ tailWord_919204).sum := by decide
  have hdescent : baseEnd_919204 < baseStart_919204 := by decide
  rcases family_descends (prefixWord ++ tailWord_919204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919218 : List Nat := [3, 2, 1, 1, 1, 2, 5, 5]
def baseStart_919218 : Nat := 118140960795 + 919218 * 2 ^ 59
def prefixEnd_919218 : Nat := 4983230072969 + 3 ^ 40 * 919218 * 2
def baseEnd_919218 : Nat := 139852047485834011569659

theorem tailTrace_919218 : CollatzResearch.WordTrace tailWord_919218 prefixEnd_919218 139852047485834011569659 := by
  unfold tailWord_919218
  simp only [CollatzResearch.WordTrace]
  refine ⟨8381658695959412695225577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22351089855891767187268205 8381658695959412695225577)
  ·
    refine ⟨6286244021969559521419183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8381658695959412695225577 6286244021969559521419183)
    ·
      refine ⟨9429366032954339282128775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6286244021969559521419183 9429366032954339282128775)
      ·
        refine ⟨14144049049431508923193163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9429366032954339282128775 14144049049431508923193163)
        ·
          refine ⟨21216073574147263384789745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14144049049431508923193163 21216073574147263384789745)
          ·
            refine ⟨15912055180610447538592309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21216073574147263384789745 15912055180610447538592309)
            ·
              refine ⟨1491755173182229456743029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15912055180610447538592309 1491755173182229456743029)
              ·
                refine ⟨139852047485834011569659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1491755173182229456743029 139852047485834011569659)
                ·
                  rfl

theorem cell20_919218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 5, 5].length) (baseStart_919218 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_919218 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_919218 prefixEnd_919218 := by exact prefixLift 919218
  have htrace : WordTrace (prefixWord ++ tailWord_919218) baseStart_919218 baseEnd_919218 := by
    simpa [prefixWord, tailWord_919218, baseEnd_919218] using wordTrace_append hprefix tailTrace_919218
  have hstable : (prefixWord ++ tailWord_919218).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919218).length < 2 ^ (prefixWord ++ tailWord_919218).sum := by decide
  have hdescent : baseEnd_919218 < baseStart_919218 := by decide
  rcases family_descends (prefixWord ++ tailWord_919218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919263 : List Nat := [1, 1, 2, 3, 2, 2, 3, 1, 5]
def baseStart_919263 : Nat := 118140960795 + 919263 * 2 ^ 59
def prefixEnd_919263 : Nat := 4983230072969 + 3 ^ 40 * 919263 * 2
def baseEnd_919263 : Nat := 419576681683681878208793

theorem tailTrace_919263 : CollatzResearch.WordTrace tailWord_919263 prefixEnd_919263 419576681683681878208793 := by
  unfold tailWord_919263
  simp only [CollatzResearch.WordTrace]
  refine ⟨33528276068674623466290443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22352184045783082310860295 33528276068674623466290443)
  ·
    refine ⟨50292414103011935199435665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33528276068674623466290443 50292414103011935199435665)
    ·
      refine ⟨37719310577258951399576749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50292414103011935199435665 37719310577258951399576749)
      ·
        refine ⟨14144741466472106774841281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37719310577258951399576749 14144741466472106774841281)
        ·
          refine ⟨10608556099854080081130961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14144741466472106774841281 10608556099854080081130961)
          ·
            refine ⟨7956417074890560060848221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10608556099854080081130961 7956417074890560060848221)
            ·
              refine ⟨2983656403083960022818083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7956417074890560060848221 2983656403083960022818083)
              ·
                refine ⟨4475484604625940034227125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2983656403083960022818083 4475484604625940034227125)
                ·
                  refine ⟨419576681683681878208793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4475484604625940034227125 419576681683681878208793)
                  ·
                    rfl

theorem cell20_919263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 1, 5].length) (baseStart_919263 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_919263 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_919263 prefixEnd_919263 := by exact prefixLift 919263
  have htrace : WordTrace (prefixWord ++ tailWord_919263) baseStart_919263 baseEnd_919263 := by
    simpa [prefixWord, tailWord_919263, baseEnd_919263] using wordTrace_append hprefix tailTrace_919263
  have hstable : (prefixWord ++ tailWord_919263).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919263).length < 2 ^ (prefixWord ++ tailWord_919263).sum := by decide
  have hdescent : baseEnd_919263 < baseStart_919263 := by decide
  rcases family_descends (prefixWord ++ tailWord_919263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919308 : List Nat := [2, 2, 1, 2, 2, 1, 2, 2, 6]
def baseStart_919308 : Nat := 118140960795 + 919308 * 2 ^ 59
def prefixEnd_919308 : Nat := 4983230072969 + 3 ^ 40 * 919308 * 2
def baseEnd_919308 : Nat := 419597220909861721708609

theorem tailTrace_919308 : CollatzResearch.WordTrace tailWord_919308 prefixEnd_919308 419597220909861721708609 := by
  unfold tailWord_919308
  simp only [CollatzResearch.WordTrace]
  refine ⟨16764958676755798075839289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22353278235674397434452385 16764958676755798075839289)
  ·
    refine ⟨12573719007566848556879467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16764958676755798075839289 12573719007566848556879467)
    ·
      refine ⟨18860578511350272835319201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12573719007566848556879467 18860578511350272835319201)
      ·
        refine ⟨14145433883512704626489401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18860578511350272835319201 14145433883512704626489401)
        ·
          refine ⟨10609075412634528469867051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14145433883512704626489401 10609075412634528469867051)
          ·
            refine ⟨15913613118951792704800577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10609075412634528469867051 15913613118951792704800577)
            ·
              refine ⟨11935209839213844528600433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15913613118951792704800577 11935209839213844528600433)
              ·
                refine ⟨8951407379410383396450325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11935209839213844528600433 8951407379410383396450325)
                ·
                  refine ⟨419597220909861721708609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8951407379410383396450325 419597220909861721708609)
                  ·
                    rfl

theorem cell20_919308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 2, 6].length) (baseStart_919308 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_919308 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_919308 prefixEnd_919308 := by exact prefixLift 919308
  have htrace : WordTrace (prefixWord ++ tailWord_919308) baseStart_919308 baseEnd_919308 := by
    simpa [prefixWord, tailWord_919308, baseEnd_919308] using wordTrace_append hprefix tailTrace_919308
  have hstable : (prefixWord ++ tailWord_919308).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919308).length < 2 ^ (prefixWord ++ tailWord_919308).sum := by decide
  have hdescent : baseEnd_919308 < baseStart_919308 := by decide
  rcases family_descends (prefixWord ++ tailWord_919308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919332 : List Nat := [2, 3, 1, 3, 2, 1, 1, 7]
def baseStart_919332 : Nat := 118140960795 + 919332 * 2 ^ 59
def prefixEnd_919332 : Nat := 4983230072969 + 3 ^ 40 * 919332 * 2
def baseEnd_919332 : Nat := 139869391721274768302837

theorem tailTrace_919332 : CollatzResearch.WordTrace tailWord_919332 prefixEnd_919332 139869391721274768302837 := by
  unfold tailWord_919332
  simp only [CollatzResearch.WordTrace]
  refine ⟨16765396352712324125276125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22353861803616432167034833 16765396352712324125276125)
  ·
    refine ⟨6287023632267121546978547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16765396352712324125276125 6287023632267121546978547)
    ·
      refine ⟨9430535448400682320467821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6287023632267121546978547 9430535448400682320467821)
      ·
        refine ⟨3536450793150255870175433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9430535448400682320467821 3536450793150255870175433)
        ·
          refine ⟨2652338094862691902631575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3536450793150255870175433 2652338094862691902631575)
          ·
            refine ⟨3978507142294037853947363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2652338094862691902631575 3978507142294037853947363)
            ·
              refine ⟨5967760713441056780921045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3978507142294037853947363 5967760713441056780921045)
              ·
                refine ⟨139869391721274768302837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5967760713441056780921045 139869391721274768302837)
                ·
                  rfl

theorem cell20_919332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 7].length) (baseStart_919332 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_919332 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_919332 prefixEnd_919332 := by exact prefixLift 919332
  have htrace : WordTrace (prefixWord ++ tailWord_919332) baseStart_919332 baseEnd_919332 := by
    simpa [prefixWord, tailWord_919332, baseEnd_919332] using wordTrace_append hprefix tailTrace_919332
  have hstable : (prefixWord ++ tailWord_919332).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919332).length < 2 ^ (prefixWord ++ tailWord_919332).sum := by decide
  have hdescent : baseEnd_919332 < baseStart_919332 := by decide
  rcases family_descends (prefixWord ++ tailWord_919332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919373 : List Nat := [1, 6, 1, 2, 1, 1, 1, 4, 3]
def baseStart_919373 : Nat := 118140960795 + 919373 * 2 ^ 59
def prefixEnd_919373 : Nat := 4983230072969 + 3 ^ 40 * 919373 * 2
def baseEnd_919373 : Nat := 419626888681010384541677

theorem tailTrace_919373 : CollatzResearch.WordTrace tailWord_919373 prefixEnd_919373 419626888681010384541677 := by
  unfold tailWord_919373
  simp only [CollatzResearch.WordTrace]
  refine ⟨33532288098276112252794773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22354858732184074835196515 33532288098276112252794773)
  ·
    refine ⟨1571826004606692761849755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 33532288098276112252794773 1571826004606692761849755)
    ·
      refine ⟨2357739006910039142774633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1571826004606692761849755 2357739006910039142774633)
      ·
        refine ⟨1768304255182529357080975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2357739006910039142774633 1768304255182529357080975)
        ·
          refine ⟨2652456382773794035621463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1768304255182529357080975 2652456382773794035621463)
          ·
            refine ⟨3978684574160691053432195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2652456382773794035621463 3978684574160691053432195)
            ·
              refine ⟨5968026861241036580148293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3978684574160691053432195 5968026861241036580148293)
              ·
                refine ⟨1119005036482694358777805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5968026861241036580148293 1119005036482694358777805)
                ·
                  refine ⟨419626888681010384541677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1119005036482694358777805 419626888681010384541677)
                  ·
                    rfl

theorem cell20_919373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_919373 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_919373 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_919373 prefixEnd_919373 := by exact prefixLift 919373
  have htrace : WordTrace (prefixWord ++ tailWord_919373) baseStart_919373 baseEnd_919373 := by
    simpa [prefixWord, tailWord_919373, baseEnd_919373] using wordTrace_append hprefix tailTrace_919373
  have hstable : (prefixWord ++ tailWord_919373).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919373).length < 2 ^ (prefixWord ++ tailWord_919373).sum := by decide
  have hdescent : baseEnd_919373 < baseStart_919373 := by decide
  rcases family_descends (prefixWord ++ tailWord_919373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919414 : List Nat := [5, 1, 1, 3, 2, 1, 2, 3, 2]
def baseStart_919414 : Nat := 118140960795 + 919414 * 2 ^ 59
def prefixEnd_919414 : Nat := 4983230072969 + 3 ^ 40 * 919414 * 2
def baseEnd_919414 : Nat := 419645602198196464174843

theorem tailTrace_919414 : CollatzResearch.WordTrace tailWord_919414 prefixEnd_919414 419645602198196464174843 := by
  unfold tailWord_919414
  simp only [CollatzResearch.WordTrace]
  refine ⟨2095861468195473515939831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22355855660751717503358197 2095861468195473515939831)
  ·
    refine ⟨3143792202293210273909747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2095861468195473515939831 3143792202293210273909747)
    ·
      refine ⟨4715688303439815410864621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3143792202293210273909747 4715688303439815410864621)
      ·
        refine ⟨1768383113789930779074233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4715688303439815410864621 1768383113789930779074233)
        ·
          refine ⟨1326287335342448084305675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1768383113789930779074233 1326287335342448084305675)
          ·
            refine ⟨1989431003013672126458513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1326287335342448084305675 1989431003013672126458513)
            ·
              refine ⟨1492073252260254094843885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1989431003013672126458513 1492073252260254094843885)
              ·
                refine ⟨559527469597595285566457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1492073252260254094843885 559527469597595285566457)
                ·
                  refine ⟨419645602198196464174843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 559527469597595285566457 419645602198196464174843)
                  ·
                    rfl

theorem cell20_919414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 2, 3, 2].length) (baseStart_919414 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_919414 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_919414 prefixEnd_919414 := by exact prefixLift 919414
  have htrace : WordTrace (prefixWord ++ tailWord_919414) baseStart_919414 baseEnd_919414 := by
    simpa [prefixWord, tailWord_919414, baseEnd_919414] using wordTrace_append hprefix tailTrace_919414
  have hstable : (prefixWord ++ tailWord_919414).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919414).length < 2 ^ (prefixWord ++ tailWord_919414).sum := by decide
  have hdescent : baseEnd_919414 < baseStart_919414 := by decide
  rcases family_descends (prefixWord ++ tailWord_919414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919425 : List Nat := [1, 2, 4, 4, 1, 1, 7]
def baseStart_919425 : Nat := 118140960795 + 919425 * 2 ^ 59
def prefixEnd_919425 : Nat := 4983230072969 + 3 ^ 40 * 919425 * 2
def baseEnd_919425 : Nat := 46627846988658812756459

theorem tailTrace_919425 : CollatzResearch.WordTrace tailWord_919425 prefixEnd_919425 46627846988658812756459 := by
  unfold tailWord_919425
  simp only [CollatzResearch.WordTrace]
  refine ⟨33534184694087725133687729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22356123129391816755791819 33534184694087725133687729)
  ·
    refine ⟨25150638520565793850265797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33534184694087725133687729 25150638520565793850265797)
    ·
      refine ⟨4715744722606086346924837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25150638520565793850265797 4715744722606086346924837)
      ·
        refine ⟨884202135488641190048407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4715744722606086346924837 884202135488641190048407)
        ·
          refine ⟨1326303203232961785072611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 884202135488641190048407 1326303203232961785072611)
          ·
            refine ⟨1989454804849442677608917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1326303203232961785072611 1989454804849442677608917)
            ·
              refine ⟨46627846988658812756459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1989454804849442677608917 46627846988658812756459)
              ·
                rfl

theorem cell20_919425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 7].length) (baseStart_919425 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_919425 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_919425 prefixEnd_919425 := by exact prefixLift 919425
  have htrace : WordTrace (prefixWord ++ tailWord_919425) baseStart_919425 baseEnd_919425 := by
    simpa [prefixWord, tailWord_919425, baseEnd_919425] using wordTrace_append hprefix tailTrace_919425
  have hstable : (prefixWord ++ tailWord_919425).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919425).length < 2 ^ (prefixWord ++ tailWord_919425).sum := by decide
  have hdescent : baseEnd_919425 < baseStart_919425 := by decide
  rcases family_descends (prefixWord ++ tailWord_919425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919429 : List Nat := [1, 3, 1, 1, 3, 2, 9]
def baseStart_919429 : Nat := 118140960795 + 919429 * 2 ^ 59
def prefixEnd_919429 : Nat := 4983230072969 + 3 ^ 40 * 919429 * 2
def baseEnd_919429 : Nat := 46628049845213675408309

theorem tailTrace_919429 : CollatzResearch.WordTrace tailWord_919429 prefixEnd_919429 46628049845213675408309 := by
  unfold tailWord_919429
  simp only [CollatzResearch.WordTrace]
  refine ⟨33534330586073233816833341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22356220390715489211222227 33534330586073233816833341)
  ·
    refine ⟨12575373969777462681312503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33534330586073233816833341 12575373969777462681312503)
    ·
      refine ⟨18863060954666194021968755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12575373969777462681312503 18863060954666194021968755)
      ·
        refine ⟨28294591431999291032953133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18863060954666194021968755 28294591431999291032953133)
        ·
          refine ⟨10610471786999734137357425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28294591431999291032953133 10610471786999734137357425)
          ·
            refine ⟨7957853840249800603018069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10610471786999734137357425 7957853840249800603018069)
            ·
              refine ⟨46628049845213675408309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7957853840249800603018069 46628049845213675408309)
              ·
                rfl

theorem cell20_919429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 9].length) (baseStart_919429 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_919429 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_919429 prefixEnd_919429 := by exact prefixLift 919429
  have htrace : WordTrace (prefixWord ++ tailWord_919429) baseStart_919429 baseEnd_919429 := by
    simpa [prefixWord, tailWord_919429, baseEnd_919429] using wordTrace_append hprefix tailTrace_919429
  have hstable : (prefixWord ++ tailWord_919429).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919429).length < 2 ^ (prefixWord ++ tailWord_919429).sum := by decide
  have hdescent : baseEnd_919429 < baseStart_919429 := by decide
  rcases family_descends (prefixWord ++ tailWord_919429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919432 : List Nat := [2, 1, 3, 3, 3, 1, 1, 1, 5]
def baseStart_919432 : Nat := 118140960795 + 919432 * 2 ^ 59
def prefixEnd_919432 : Nat := 4983230072969 + 3 ^ 40 * 919432 * 2
def baseEnd_919432 : Nat := 419653817888668401574769

theorem tailTrace_919432 : CollatzResearch.WordTrace tailWord_919432 prefixEnd_919432 419653817888668401574769 := by
  unfold tailWord_919432
  simp only [CollatzResearch.WordTrace]
  refine ⟨16767220002531182664596275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22356293336708243552795033 16767220002531182664596275)
  ·
    refine ⟨25150830003796773996894413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16767220002531182664596275 25150830003796773996894413)
    ·
      refine ⟨9431561251423790248835405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25150830003796773996894413 9431561251423790248835405)
      ·
        refine ⟨3536835469283921343313277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9431561251423790248835405 3536835469283921343313277)
        ·
          refine ⟨1326313300981470503742479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3536835469283921343313277 1326313300981470503742479)
          ·
            refine ⟨1989469951472205755613719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1326313300981470503742479 1989469951472205755613719)
            ·
              refine ⟨2984204927208308633420579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1989469951472205755613719 2984204927208308633420579)
              ·
                refine ⟨4476307390812462950130869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2984204927208308633420579 4476307390812462950130869)
                ·
                  refine ⟨419653817888668401574769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4476307390812462950130869 419653817888668401574769)
                  ·
                    rfl

theorem cell20_919432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 1, 5].length) (baseStart_919432 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_919432 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_919432 prefixEnd_919432 := by exact prefixLift 919432
  have htrace : WordTrace (prefixWord ++ tailWord_919432) baseStart_919432 baseEnd_919432 := by
    simpa [prefixWord, tailWord_919432, baseEnd_919432] using wordTrace_append hprefix tailTrace_919432
  have hstable : (prefixWord ++ tailWord_919432).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919432).length < 2 ^ (prefixWord ++ tailWord_919432).sum := by decide
  have hdescent : baseEnd_919432 < baseStart_919432 := by decide
  rcases family_descends (prefixWord ++ tailWord_919432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919463 : List Nat := [1, 1, 6, 1, 2, 1, 4, 4]
def baseStart_919463 : Nat := 118140960795 + 919463 * 2 ^ 59
def prefixEnd_919463 : Nat := 4983230072969 + 3 ^ 40 * 919463 * 2
def baseEnd_919463 : Nat := 139889322377790023847103

theorem tailTrace_919463 : CollatzResearch.WordTrace tailWord_919463 prefixEnd_919463 139889322377790023847103 := by
  unfold tailWord_919463
  simp only [CollatzResearch.WordTrace]
  refine ⟨33535570667950057623571043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22357047111966705082380695 33535570667950057623571043)
  ·
    refine ⟨50303356001925086435356565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33535570667950057623571043 50303356001925086435356565)
    ·
      refine ⟨2357969812590238426657339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 50303356001925086435356565 2357969812590238426657339)
      ·
        refine ⟨3536954718885357639986009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2357969812590238426657339 3536954718885357639986009)
        ·
          refine ⟨2652716039164018229989507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3536954718885357639986009 2652716039164018229989507)
          ·
            refine ⟨3979074058746027344984261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2652716039164018229989507 3979074058746027344984261)
            ·
              refine ⟨746076386014880127184549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3979074058746027344984261 746076386014880127184549)
              ·
                refine ⟨139889322377790023847103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 746076386014880127184549 139889322377790023847103)
                ·
                  rfl

theorem cell20_919463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 4, 4].length) (baseStart_919463 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_919463 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_919463 prefixEnd_919463 := by exact prefixLift 919463
  have htrace : WordTrace (prefixWord ++ tailWord_919463) baseStart_919463 baseEnd_919463 := by
    simpa [prefixWord, tailWord_919463, baseEnd_919463] using wordTrace_append hprefix tailTrace_919463
  have hstable : (prefixWord ++ tailWord_919463).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919463).length < 2 ^ (prefixWord ++ tailWord_919463).sum := by decide
  have hdescent : baseEnd_919463 < baseStart_919463 := by decide
  rcases family_descends (prefixWord ++ tailWord_919463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919473 : List Nat := [1, 2, 2, 4, 2, 3, 1, 3, 2]
def baseStart_919473 : Nat := 118140960795 + 919473 * 2 ^ 59
def prefixEnd_919473 : Nat := 4983230072969 + 3 ^ 40 * 919473 * 2
def baseEnd_919473 : Nat := 419672531405854481207935

theorem tailTrace_919473 : CollatzResearch.WordTrace tailWord_919473 prefixEnd_919473 419672531405854481207935 := by
  unfold tailWord_919473
  simp only [CollatzResearch.WordTrace]
  refine ⟨33535935397913829331435073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22357290265275886220956715 33535935397913829331435073)
  ·
    refine ⟨25151951548435371998576305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33535935397913829331435073 25151951548435371998576305)
    ·
      refine ⟨18863963661326528998932229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25151951548435371998576305 18863963661326528998932229)
      ·
        refine ⟨3536993186498724187299793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18863963661326528998932229 3536993186498724187299793)
        ·
          refine ⟨2652744889874043140474845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3536993186498724187299793 2652744889874043140474845)
          ·
            refine ⟨994779333702766177678067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2652744889874043140474845 994779333702766177678067)
            ·
              refine ⟨1492169000554149266517101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 994779333702766177678067 1492169000554149266517101)
              ·
                refine ⟨559563375207805974943913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1492169000554149266517101 559563375207805974943913)
                ·
                  refine ⟨419672531405854481207935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 559563375207805974943913 419672531405854481207935)
                  ·
                    rfl

theorem cell20_919473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 1, 3, 2].length) (baseStart_919473 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_919473 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_919473 prefixEnd_919473 := by exact prefixLift 919473
  have htrace : WordTrace (prefixWord ++ tailWord_919473) baseStart_919473 baseEnd_919473 := by
    simpa [prefixWord, tailWord_919473, baseEnd_919473] using wordTrace_append hprefix tailTrace_919473
  have hstable : (prefixWord ++ tailWord_919473).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919473).length < 2 ^ (prefixWord ++ tailWord_919473).sum := by decide
  have hdescent : baseEnd_919473 < baseStart_919473 := by decide
  rcases family_descends (prefixWord ++ tailWord_919473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919508 : List Nat := [2, 4, 1, 2, 1, 1, 3, 3, 3]
def baseStart_919508 : Nat := 118140960795 + 919508 * 2 ^ 59
def prefixEnd_919508 : Nat := 4983230072969 + 3 ^ 40 * 919508 * 2
def baseEnd_919508 : Nat := 419688506359549915041125

theorem tailTrace_919508 : CollatzResearch.WordTrace tailWord_919508 prefixEnd_919508 419688506359549915041125 := by
  unfold tailWord_919508
  simp only [CollatzResearch.WordTrace]
  refine ⟨16768605976393515154479589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22358141301858020205972785 16768605976393515154479589)
  ·
    refine ⟨3144113620573784091464923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16768605976393515154479589 3144113620573784091464923)
    ·
      refine ⟨4716170430860676137197385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3144113620573784091464923 4716170430860676137197385)
      ·
        refine ⟨3537127823145507102898039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4716170430860676137197385 3537127823145507102898039)
        ·
          refine ⟨5305691734718260654347059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3537127823145507102898039 5305691734718260654347059)
          ·
            refine ⟨7958537602077390981520589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5305691734718260654347059 7958537602077390981520589)
            ·
              refine ⟨2984451600779021618070221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7958537602077390981520589 2984451600779021618070221)
              ·
                refine ⟨1119169350292133106776333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2984451600779021618070221 1119169350292133106776333)
                ·
                  refine ⟨419688506359549915041125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1119169350292133106776333 419688506359549915041125)
                  ·
                    rfl

theorem cell20_919508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 3, 3].length) (baseStart_919508 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_919508 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_919508 prefixEnd_919508 := by exact prefixLift 919508
  have htrace : WordTrace (prefixWord ++ tailWord_919508) baseStart_919508 baseEnd_919508 := by
    simpa [prefixWord, tailWord_919508, baseEnd_919508] using wordTrace_append hprefix tailTrace_919508
  have hstable : (prefixWord ++ tailWord_919508).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919508).length < 2 ^ (prefixWord ++ tailWord_919508).sum := by decide
  have hdescent : baseEnd_919508 < baseStart_919508 := by decide
  rcases family_descends (prefixWord ++ tailWord_919508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919556 : List Nat := [2, 3, 2, 4, 1, 2, 1, 5]
def baseStart_919556 : Nat := 118140960795 + 919556 * 2 ^ 59
def prefixEnd_919556 : Nat := 4983230072969 + 3 ^ 40 * 919556 * 2
def baseEnd_919556 : Nat := 139903471622491693813643

theorem tailTrace_919556 : CollatzResearch.WordTrace tailWord_919556 prefixEnd_919556 139903471622491693813643 := by
  unfold tailWord_919556
  simp only [CollatzResearch.WordTrace]
  refine ⟨16769481328306567253353261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22359308437742089671137681 16769481328306567253353261)
  ·
    refine ⟨6288555498114962720007473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16769481328306567253353261 6288555498114962720007473)
    ·
      refine ⟨4716416623586222040005605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6288555498114962720007473 4716416623586222040005605)
      ·
        refine ⟨884328116922416632501051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4716416623586222040005605 884328116922416632501051)
        ·
          refine ⟨1326492175383624948751577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 884328116922416632501051 1326492175383624948751577)
          ·
            refine ⟨994869131537718711563683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1326492175383624948751577 994869131537718711563683)
            ·
              refine ⟨1492303697306578067345525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 994869131537718711563683 1492303697306578067345525)
              ·
                refine ⟨139903471622491693813643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1492303697306578067345525 139903471622491693813643)
                ·
                  rfl

theorem cell20_919556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 1, 5].length) (baseStart_919556 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_919556 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_919556 prefixEnd_919556 := by exact prefixLift 919556
  have htrace : WordTrace (prefixWord ++ tailWord_919556) baseStart_919556 baseEnd_919556 := by
    simpa [prefixWord, tailWord_919556, baseEnd_919556] using wordTrace_append hprefix tailTrace_919556
  have hstable : (prefixWord ++ tailWord_919556).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919556).length < 2 ^ (prefixWord ++ tailWord_919556).sum := by decide
  have hdescent : baseEnd_919556 < baseStart_919556 := by decide
  rcases family_descends (prefixWord ++ tailWord_919556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919598 : List Nat := [4, 1, 3, 1, 1, 3, 7]
def baseStart_919598 : Nat := 118140960795 + 919598 * 2 ^ 59
def prefixEnd_919598 : Nat := 4983230072969 + 3 ^ 40 * 919598 * 2
def baseEnd_919598 : Nat := 46636620534656622448973

theorem tailTrace_919598 : CollatzResearch.WordTrace tailWord_919598 prefixEnd_919598 46636620534656622448973 := by
  unfold tailWord_919598
  simp only [CollatzResearch.WordTrace]
  refine ⟨4192561815307621959966931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22360329681640650453156965 4192561815307621959966931)
  ·
    refine ⟨6288842722961432939950397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4192561815307621959966931 6288842722961432939950397)
    ·
      refine ⟨2358316021110537352481399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6288842722961432939950397 2358316021110537352481399)
      ·
        refine ⟨3537474031665806028722099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2358316021110537352481399 3537474031665806028722099)
        ·
          refine ⟨5306211047498709043083149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3537474031665806028722099 5306211047498709043083149)
          ·
            refine ⟨1989829142812015891156181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5306211047498709043083149 1989829142812015891156181)
            ·
              refine ⟨46636620534656622448973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1989829142812015891156181 46636620534656622448973)
              ·
                rfl

theorem cell20_919598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 7].length) (baseStart_919598 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_919598 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_919598 prefixEnd_919598 := by exact prefixLift 919598
  have htrace : WordTrace (prefixWord ++ tailWord_919598) baseStart_919598 baseEnd_919598 := by
    simpa [prefixWord, tailWord_919598, baseEnd_919598] using wordTrace_append hprefix tailTrace_919598
  have hstable : (prefixWord ++ tailWord_919598).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919598).length < 2 ^ (prefixWord ++ tailWord_919598).sum := by decide
  have hdescent : baseEnd_919598 < baseStart_919598 := by decide
  rcases family_descends (prefixWord ++ tailWord_919598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919629 : List Nat := [1, 6, 1, 1, 1, 1, 1, 4, 4]
def baseStart_919629 : Nat := 118140960795 + 919629 * 2 ^ 59
def prefixEnd_919629 : Nat := 4983230072969 + 3 ^ 40 * 919629 * 2
def baseEnd_919629 : Nat := 419743734056611272007297

theorem tailTrace_919629 : CollatzResearch.WordTrace tailWord_919629 prefixEnd_919629 419743734056611272007297 := by
  unfold tailWord_919629
  simp only [CollatzResearch.WordTrace]
  refine ⟨33541625185348667974113941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22361083456899111982742627 33541625185348667974113941)
  ·
    refine ⟨1572263680563218811286591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 33541625185348667974113941 1572263680563218811286591)
    ·
      refine ⟨2358395520844828216929887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1572263680563218811286591 2358395520844828216929887)
      ·
        refine ⟨3537593281267242325394831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2358395520844828216929887 3537593281267242325394831)
        ·
          refine ⟨5306389921900863488092247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3537593281267242325394831 5306389921900863488092247)
          ·
            refine ⟨7959584882851295232138371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5306389921900863488092247 7959584882851295232138371)
            ·
              refine ⟨11939377324276942848207557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7959584882851295232138371 11939377324276942848207557)
              ·
                refine ⟨2238633248301926784038917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11939377324276942848207557 2238633248301926784038917)
                ·
                  refine ⟨419743734056611272007297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2238633248301926784038917 419743734056611272007297)
                  ·
                    rfl

theorem cell20_919629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_919629 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_919629 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_919629 prefixEnd_919629 := by exact prefixLift 919629
  have htrace : WordTrace (prefixWord ++ tailWord_919629) baseStart_919629 baseEnd_919629 := by
    simpa [prefixWord, tailWord_919629, baseEnd_919629] using wordTrace_append hprefix tailTrace_919629
  have hstable : (prefixWord ++ tailWord_919629).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919629).length < 2 ^ (prefixWord ++ tailWord_919629).sum := by decide
  have hdescent : baseEnd_919629 < baseStart_919629 := by decide
  rcases family_descends (prefixWord ++ tailWord_919629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919677 : List Nat := [1, 4, 1, 1, 3, 4, 2, 1, 3]
def baseStart_919677 : Nat := 118140960795 + 919677 * 2 ^ 59
def prefixEnd_919677 : Nat := 4983230072969 + 3 ^ 40 * 919677 * 2
def baseEnd_919677 : Nat := 419765642564536438407101

theorem tailTrace_919677 : CollatzResearch.WordTrace tailWord_919677 prefixEnd_919677 419765642564536438407101 := by
  unfold tailWord_919677
  simp only [CollatzResearch.WordTrace]
  refine ⟨33543375889174772171861285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22362250592783181447907523 33543375889174772171861285)
  ·
    refine ⟨6289382979220269782223991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33543375889174772171861285 6289382979220269782223991)
    ·
      refine ⟨9434074468830404673335987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6289382979220269782223991 9434074468830404673335987)
      ·
        refine ⟨14151111703245607010003981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9434074468830404673335987 14151111703245607010003981)
        ·
          refine ⟨5306666888717102628751493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14151111703245607010003981 5306666888717102628751493)
          ·
            refine ⟨995000041634456742890905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5306666888717102628751493 995000041634456742890905)
            ·
              refine ⟨746250031225842557168179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 995000041634456742890905 746250031225842557168179)
              ·
                refine ⟨1119375046838763835752269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 746250031225842557168179 1119375046838763835752269)
                ·
                  refine ⟨419765642564536438407101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1119375046838763835752269 419765642564536438407101)
                  ·
                    rfl

theorem cell20_919677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 2, 1, 3].length) (baseStart_919677 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_919677 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_919677 prefixEnd_919677 := by exact prefixLift 919677
  have htrace : WordTrace (prefixWord ++ tailWord_919677) baseStart_919677 baseEnd_919677 := by
    simpa [prefixWord, tailWord_919677, baseEnd_919677] using wordTrace_append hprefix tailTrace_919677
  have hstable : (prefixWord ++ tailWord_919677).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919677).length < 2 ^ (prefixWord ++ tailWord_919677).sum := by decide
  have hdescent : baseEnd_919677 < baseStart_919677 := by decide
  rcases family_descends (prefixWord ++ tailWord_919677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919729 : List Nat := [1, 2, 2, 5, 2, 2, 1, 5]
def baseStart_919729 : Nat := 118140960795 + 919729 * 2 ^ 59
def prefixEnd_919729 : Nat := 4983230072969 + 3 ^ 40 * 919729 * 2
def baseEnd_919729 : Nat := 139929792260485122891185

theorem tailTrace_919729 : CollatzResearch.WordTrace tailWord_919729 prefixEnd_919729 139929792260485122891185 := by
  unfold tailWord_919729
  simp only [CollatzResearch.WordTrace]
  refine ⟨33545272484986385052754241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22363514989990923368502827 33545272484986385052754241)
  ·
    refine ⟨25158954363739788789565681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33545272484986385052754241 25158954363739788789565681)
    ·
      refine ⟨18869215772804841592174261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25158954363739788789565681 18869215772804841592174261)
      ·
        refine ⟨1768988978700453899266337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18869215772804841592174261 1768988978700453899266337)
        ·
          refine ⟨1326741734025340424449753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1768988978700453899266337 1326741734025340424449753)
          ·
            refine ⟨995056300519005318337315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1326741734025340424449753 995056300519005318337315)
            ·
              refine ⟨1492584450778507977505973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 995056300519005318337315 1492584450778507977505973)
              ·
                refine ⟨139929792260485122891185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1492584450778507977505973 139929792260485122891185)
                ·
                  rfl

theorem cell20_919729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 1, 5].length) (baseStart_919729 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_919729 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_919729 prefixEnd_919729 := by exact prefixLift 919729
  have htrace : WordTrace (prefixWord ++ tailWord_919729) baseStart_919729 baseEnd_919729 := by
    simpa [prefixWord, tailWord_919729, baseEnd_919729] using wordTrace_append hprefix tailTrace_919729
  have hstable : (prefixWord ++ tailWord_919729).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919729).length < 2 ^ (prefixWord ++ tailWord_919729).sum := by decide
  have hdescent : baseEnd_919729 < baseStart_919729 := by decide
  rcases family_descends (prefixWord ++ tailWord_919729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919781 : List Nat := [1, 3, 1, 4, 2, 2, 2, 1, 4]
def baseStart_919781 : Nat := 118140960795 + 919781 * 2 ^ 59
def prefixEnd_919781 : Nat := 4983230072969 + 3 ^ 40 * 919781 * 2
def baseEnd_919781 : Nat := 419813110998374298940009

theorem tailTrace_919781 : CollatzResearch.WordTrace tailWord_919781 prefixEnd_919781 419813110998374298940009 := by
  unfold tailWord_919781
  simp only [CollatzResearch.WordTrace]
  refine ⟨33547169080797997933647197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22364779387198665289098131 33547169080797997933647197)
  ·
    refine ⟨12580188405299249225117699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33547169080797997933647197 12580188405299249225117699)
    ·
      refine ⟨18870282607948873837676549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12580188405299249225117699 18870282607948873837676549)
      ·
        refine ⟨3538177988990413844564353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18870282607948873837676549 3538177988990413844564353)
        ·
          refine ⟨2653633491742810383423265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3538177988990413844564353 2653633491742810383423265)
          ·
            refine ⟨1990225118807107787567449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2653633491742810383423265 1990225118807107787567449)
            ·
              refine ⟨1492668839105330840675587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1990225118807107787567449 1492668839105330840675587)
              ·
                refine ⟨2239003258657996261013381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1492668839105330840675587 2239003258657996261013381)
                ·
                  refine ⟨419813110998374298940009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2239003258657996261013381 419813110998374298940009)
                  ·
                    rfl

theorem cell20_919781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 2, 1, 4].length) (baseStart_919781 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_919781 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_919781 prefixEnd_919781 := by exact prefixLift 919781
  have htrace : WordTrace (prefixWord ++ tailWord_919781) baseStart_919781 baseEnd_919781 := by
    simpa [prefixWord, tailWord_919781, baseEnd_919781] using wordTrace_append hprefix tailTrace_919781
  have hstable : (prefixWord ++ tailWord_919781).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919781).length < 2 ^ (prefixWord ++ tailWord_919781).sum := by decide
  have hdescent : baseEnd_919781 < baseStart_919781 := by decide
  rcases family_descends (prefixWord ++ tailWord_919781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919785 : List Nat := [1, 2, 1, 1, 1, 2, 2, 2, 8]
def baseStart_919785 : Nat := 118140960795 + 919785 * 2 ^ 59
def prefixEnd_919785 : Nat := 4983230072969 + 3 ^ 40 * 919785 * 2
def baseEnd_919785 : Nat := 419814936707368062806659

theorem tailTrace_919785 : CollatzResearch.WordTrace tailWord_919785 prefixEnd_919785 419814936707368062806659 := by
  unfold tailWord_919785
  simp only [CollatzResearch.WordTrace]
  refine ⟨33547314972783506616792809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22364876648522337744528539 33547314972783506616792809)
  ·
    refine ⟨25160486229587629962594607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33547314972783506616792809 25160486229587629962594607)
    ·
      refine ⟨37740729344381444943891911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25160486229587629962594607 37740729344381444943891911)
      ·
        refine ⟨56611094016572167415837867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37740729344381444943891911 56611094016572167415837867)
        ·
          refine ⟨84916641024858251123756801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56611094016572167415837867 84916641024858251123756801)
          ·
            refine ⟨63687480768643688342817601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84916641024858251123756801 63687480768643688342817601)
            ·
              refine ⟨47765610576482766257113201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63687480768643688342817601 47765610576482766257113201)
              ·
                refine ⟨35824207932362074692834901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47765610576482766257113201 35824207932362074692834901)
                ·
                  refine ⟨419814936707368062806659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35824207932362074692834901 419814936707368062806659)
                  ·
                    rfl

theorem cell20_919785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 8].length) (baseStart_919785 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_919785 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_919785 prefixEnd_919785 := by exact prefixLift 919785
  have htrace : WordTrace (prefixWord ++ tailWord_919785) baseStart_919785 baseEnd_919785 := by
    simpa [prefixWord, tailWord_919785, baseEnd_919785] using wordTrace_append hprefix tailTrace_919785
  have hstable : (prefixWord ++ tailWord_919785).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919785).length < 2 ^ (prefixWord ++ tailWord_919785).sum := by decide
  have hdescent : baseEnd_919785 < baseStart_919785 := by decide
  rcases family_descends (prefixWord ++ tailWord_919785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919802 : List Nat := [3, 1, 1, 1, 1, 5, 2, 2, 4]
def baseStart_919802 : Nat := 118140960795 + 919802 * 2 ^ 59
def prefixEnd_919802 : Nat := 4983230072969 + 3 ^ 40 * 919802 * 2
def baseEnd_919802 : Nat := 419822695970591559239923

theorem tailTrace_919802 : CollatzResearch.WordTrace tailWord_919802 prefixEnd_919802 419822695970591559239923 := by
  unfold tailWord_919802
  simp only [CollatzResearch.WordTrace]
  refine ⟨8386983753430479630040415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22365290009147945680107773 8386983753430479630040415)
  ·
    refine ⟨12580475630145719445060623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8386983753430479630040415 12580475630145719445060623)
    ·
      refine ⟨18870713445218579167590935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12580475630145719445060623 18870713445218579167590935)
      ·
        refine ⟨28306070167827868751386403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18870713445218579167590935 28306070167827868751386403)
        ·
          refine ⟨42459105251741803127079605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28306070167827868751386403 42459105251741803127079605)
          ·
            refine ⟨3980541117350794043163713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42459105251741803127079605 3980541117350794043163713)
            ·
              refine ⟨2985405838013095532372785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3980541117350794043163713 2985405838013095532372785)
              ·
                refine ⟨2239054378509821649279589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2985405838013095532372785 2239054378509821649279589)
                ·
                  refine ⟨419822695970591559239923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2239054378509821649279589 419822695970591559239923)
                  ·
                    rfl

theorem cell20_919802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 2, 4].length) (baseStart_919802 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_919802 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_919802 prefixEnd_919802 := by exact prefixLift 919802
  have htrace : WordTrace (prefixWord ++ tailWord_919802) baseStart_919802 baseEnd_919802 := by
    simpa [prefixWord, tailWord_919802, baseEnd_919802] using wordTrace_append hprefix tailTrace_919802
  have hstable : (prefixWord ++ tailWord_919802).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919802).length < 2 ^ (prefixWord ++ tailWord_919802).sum := by decide
  have hdescent : baseEnd_919802 < baseStart_919802 := by decide
  rcases family_descends (prefixWord ++ tailWord_919802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919809 : List Nat := [1, 2, 4, 1, 1, 2, 3, 6]
def baseStart_919809 : Nat := 118140960795 + 919809 * 2 ^ 59
def prefixEnd_919809 : Nat := 4983230072969 + 3 ^ 40 * 919809 * 2
def baseEnd_919809 : Nat := 139941963653776882002187

theorem tailTrace_919809 : CollatzResearch.WordTrace tailWord_919809 prefixEnd_919809 139941963653776882002187 := by
  unfold tailWord_919809
  simp only [CollatzResearch.WordTrace]
  refine ⟨33548190324696558715666481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22365460216464372477110987 33548190324696558715666481)
  ·
    refine ⟨25161142743522419036749861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33548190324696558715666481 25161142743522419036749861)
    ·
      refine ⟨4717714264410453569390599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25161142743522419036749861 4717714264410453569390599)
      ·
        refine ⟨7076571396615680354085899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4717714264410453569390599 7076571396615680354085899)
        ·
          refine ⟨10614857094923520531128849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7076571396615680354085899 10614857094923520531128849)
          ·
            refine ⟨7961142821192640398346637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10614857094923520531128849 7961142821192640398346637)
            ·
              refine ⟨2985428557947240149379989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7961142821192640398346637 2985428557947240149379989)
              ·
                refine ⟨139941963653776882002187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2985428557947240149379989 139941963653776882002187)
                ·
                  rfl

theorem cell20_919809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 6].length) (baseStart_919809 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_919809 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_919809 prefixEnd_919809 := by exact prefixLift 919809
  have htrace : WordTrace (prefixWord ++ tailWord_919809) baseStart_919809 baseEnd_919809 := by
    simpa [prefixWord, tailWord_919809, baseEnd_919809] using wordTrace_append hprefix tailTrace_919809
  have hstable : (prefixWord ++ tailWord_919809).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919809).length < 2 ^ (prefixWord ++ tailWord_919809).sum := by decide
  have hdescent : baseEnd_919809 < baseStart_919809 := by decide
  rcases family_descends (prefixWord ++ tailWord_919809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919823 : List Nat := [1, 1, 2, 1, 1, 1, 3, 4, 6]
def baseStart_919823 : Nat := 118140960795 + 919823 * 2 ^ 59
def prefixEnd_919823 : Nat := 4983230072969 + 3 ^ 40 * 919823 * 2
def baseEnd_919823 : Nat := 419832280942808819539837

theorem tailTrace_919823 : CollatzResearch.WordTrace tailWord_919823 prefixEnd_919823 419832280942808819539837 := by
  unfold tailWord_919823
  simp only [CollatzResearch.WordTrace]
  refine ⟨33548700946645839106676123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22365800631097226071117415 33548700946645839106676123)
  ·
    refine ⟨50323051419968758660014185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33548700946645839106676123 50323051419968758660014185)
    ·
      refine ⟨37742288564976568995010639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50323051419968758660014185 37742288564976568995010639)
      ·
        refine ⟨56613432847464853492515959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37742288564976568995010639 56613432847464853492515959)
        ·
          refine ⟨84920149271197280238773939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56613432847464853492515959 84920149271197280238773939)
          ·
            refine ⟨127380223906795920358160909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84920149271197280238773939 127380223906795920358160909)
            ·
              refine ⟨47767583965048470134310341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127380223906795920358160909 47767583965048470134310341)
              ·
                refine ⟨8956421993446588150183189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47767583965048470134310341 8956421993446588150183189)
                ·
                  refine ⟨419832280942808819539837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8956421993446588150183189 419832280942808819539837)
                  ·
                    rfl

theorem cell20_919823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 4, 6].length) (baseStart_919823 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_919823 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_919823 prefixEnd_919823 := by exact prefixLift 919823
  have htrace : WordTrace (prefixWord ++ tailWord_919823) baseStart_919823 baseEnd_919823 := by
    simpa [prefixWord, tailWord_919823, baseEnd_919823] using wordTrace_append hprefix tailTrace_919823
  have hstable : (prefixWord ++ tailWord_919823).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919823).length < 2 ^ (prefixWord ++ tailWord_919823).sum := by decide
  have hdescent : baseEnd_919823 < baseStart_919823 := by decide
  rcases family_descends (prefixWord ++ tailWord_919823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919885 : List Nat := [1, 6, 1, 12]
def baseStart_919885 : Nat := 118140960795 + 919885 * 2 ^ 59
def prefixEnd_919885 : Nat := 4983230072969 + 3 ^ 40 * 919885 * 2
def baseEnd_919885 : Nat := 1727821314535852508119

theorem tailTrace_919885 : CollatzResearch.WordTrace tailWord_919885 prefixEnd_919885 1727821314535852508119 := by
  unfold tailWord_919885
  simp only [CollatzResearch.WordTrace]
  refine ⟨33550962272421223695433109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22367308181614149130288739 33550962272421223695433109)
  ·
    refine ⟨1572701356519744860723427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 33550962272421223695433109 1572701356519744860723427)
    ·
      refine ⟨2359052034779617291085141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1572701356519744860723427 2359052034779617291085141)
      ·
        refine ⟨1727821314535852508119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 12 2359052034779617291085141 1727821314535852508119)
        ·
          rfl

theorem cell20_919885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 12].length) (baseStart_919885 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_919885 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_919885 prefixEnd_919885 := by exact prefixLift 919885
  have htrace : WordTrace (prefixWord ++ tailWord_919885) baseStart_919885 baseEnd_919885 := by
    simpa [prefixWord, tailWord_919885, baseEnd_919885] using wordTrace_append hprefix tailTrace_919885
  have hstable : (prefixWord ++ tailWord_919885).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919885).length < 2 ^ (prefixWord ++ tailWord_919885).sum := by decide
  have hdescent : baseEnd_919885 < baseStart_919885 := by decide
  rcases family_descends (prefixWord ++ tailWord_919885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919895 : List Nat := [1, 1, 3, 2, 3, 1, 3, 4, 2]
def baseStart_919895 : Nat := 118140960795 + 919895 * 2 ^ 59
def prefixEnd_919895 : Nat := 4983230072969 + 3 ^ 40 * 919895 * 2
def baseEnd_919895 : Nat := 419865143704696569139543

theorem tailTrace_919895 : CollatzResearch.WordTrace tailWord_919895 prefixEnd_919895 419865143704696569139543 := by
  unfold tailWord_919895
  simp only [CollatzResearch.WordTrace]
  refine ⟨33551327002384995403297139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22367551334923330268864759 33551327002384995403297139)
  ·
    refine ⟨50326990503577493104945709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33551327002384995403297139 50326990503577493104945709)
    ·
      refine ⟨18872621438841559914354641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50326990503577493104945709 18872621438841559914354641)
      ·
        refine ⟨14154466079131169935765981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18872621438841559914354641 14154466079131169935765981)
        ·
          refine ⟨5307924779674188725912243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14154466079131169935765981 5307924779674188725912243)
          ·
            refine ⟨7961887169511283088868365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5307924779674188725912243 7961887169511283088868365)
            ·
              refine ⟨2985707688566731158325637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7961887169511283088868365 2985707688566731158325637)
              ·
                refine ⟨559820191606262092186057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2985707688566731158325637 559820191606262092186057)
                ·
                  refine ⟨419865143704696569139543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 559820191606262092186057 419865143704696569139543)
                  ·
                    rfl

theorem cell20_919895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 4, 2].length) (baseStart_919895 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_919895 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_919895 prefixEnd_919895 := by exact prefixLift 919895
  have htrace : WordTrace (prefixWord ++ tailWord_919895) baseStart_919895 baseEnd_919895 := by
    simpa [prefixWord, tailWord_919895, baseEnd_919895] using wordTrace_append hprefix tailTrace_919895
  have hstable : (prefixWord ++ tailWord_919895).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919895).length < 2 ^ (prefixWord ++ tailWord_919895).sum := by decide
  have hdescent : baseEnd_919895 < baseStart_919895 := by decide
  rcases family_descends (prefixWord ++ tailWord_919895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919909 : List Nat := [1, 3, 1, 3, 1, 3, 2, 3, 3]
def baseStart_919909 : Nat := 118140960795 + 919909 * 2 ^ 59
def prefixEnd_919909 : Nat := 4983230072969 + 3 ^ 40 * 919909 * 2
def baseEnd_919909 : Nat := 419871533686174742672819

theorem tailTrace_919909 : CollatzResearch.WordTrace tailWord_919909 prefixEnd_919909 419871533686174742672819 := by
  unfold tailWord_919909
  simp only [CollatzResearch.WordTrace]
  refine ⟨33551837624334275794306781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22367891749556183862871187 33551837624334275794306781)
  ·
    refine ⟨12581939109125353422865043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33551837624334275794306781 12581939109125353422865043)
    ·
      refine ⟨18872908663688030134297565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12581939109125353422865043 18872908663688030134297565)
      ·
        refine ⟨7077340748883011300361587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18872908663688030134297565 7077340748883011300361587)
        ·
          refine ⟨10616011123324516950542381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7077340748883011300361587 10616011123324516950542381)
          ·
            refine ⟨3981004171246693856453393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10616011123324516950542381 3981004171246693856453393)
            ·
              refine ⟨2985753128435020392340045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3981004171246693856453393 2985753128435020392340045)
              ·
                refine ⟨1119657423163132647127517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2985753128435020392340045 1119657423163132647127517)
                ·
                  refine ⟨419871533686174742672819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1119657423163132647127517 419871533686174742672819)
                  ·
                    rfl

theorem cell20_919909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 3, 3].length) (baseStart_919909 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_919909 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_919909 prefixEnd_919909 := by exact prefixLift 919909
  have htrace : WordTrace (prefixWord ++ tailWord_919909) baseStart_919909 baseEnd_919909 := by
    simpa [prefixWord, tailWord_919909, baseEnd_919909] using wordTrace_append hprefix tailTrace_919909
  have hstable : (prefixWord ++ tailWord_919909).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919909).length < 2 ^ (prefixWord ++ tailWord_919909).sum := by decide
  have hdescent : baseEnd_919909 < baseStart_919909 := by decide
  rcases family_descends (prefixWord ++ tailWord_919909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919933 : List Nat := [1, 4, 1, 1, 2, 3, 1, 5, 2]
def baseStart_919933 : Nat := 118140960795 + 919933 * 2 ^ 59
def prefixEnd_919933 : Nat := 4983230072969 + 3 ^ 40 * 919933 * 2
def baseEnd_919933 : Nat := 419882487940137325872721

theorem tailTrace_919933 : CollatzResearch.WordTrace tailWord_919933 prefixEnd_919933 419882487940137325872721 := by
  unfold tailWord_919933
  simp only [CollatzResearch.WordTrace]
  refine ⟨33552712976247327893180453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22368475317498218595453635 33552712976247327893180453)
  ·
    refine ⟨6291133683046373979971335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33552712976247327893180453 6291133683046373979971335)
    ·
      refine ⟨9436700524569560969957003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6291133683046373979971335 9436700524569560969957003)
      ·
        refine ⟨14155050786854341454935505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9436700524569560969957003 14155050786854341454935505)
        ·
          refine ⟨10616288090140756091201629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14155050786854341454935505 10616288090140756091201629)
          ·
            refine ⟨3981108033802783534200611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10616288090140756091201629 3981108033802783534200611)
            ·
              refine ⟨5971662050704175301300917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3981108033802783534200611 5971662050704175301300917)
              ·
                refine ⟨559843317253516434496961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5971662050704175301300917 559843317253516434496961)
                ·
                  refine ⟨419882487940137325872721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 559843317253516434496961 419882487940137325872721)
                  ·
                    rfl

theorem cell20_919933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 5, 2].length) (baseStart_919933 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_919933 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_919933 prefixEnd_919933 := by exact prefixLift 919933
  have htrace : WordTrace (prefixWord ++ tailWord_919933) baseStart_919933 baseEnd_919933 := by
    simpa [prefixWord, tailWord_919933, baseEnd_919933] using wordTrace_append hprefix tailTrace_919933
  have hstable : (prefixWord ++ tailWord_919933).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919933).length < 2 ^ (prefixWord ++ tailWord_919933).sum := by decide
  have hdescent : baseEnd_919933 < baseStart_919933 := by decide
  rcases family_descends (prefixWord ++ tailWord_919933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919947 : List Nat := [1, 1, 1, 1, 4, 4, 3, 2, 3]
def baseStart_919947 : Nat := 118140960795 + 919947 * 2 ^ 59
def prefixEnd_919947 : Nat := 4983230072969 + 3 ^ 40 * 919947 * 2
def baseEnd_919947 : Nat := 419888877921615499405997

theorem tailTrace_919947 : CollatzResearch.WordTrace tailWord_919947 prefixEnd_919947 419888877921615499405997 := by
  unfold tailWord_919947
  simp only [CollatzResearch.WordTrace]
  refine ⟨33553223598196608284190095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22368815732131072189460063 33553223598196608284190095)
  ·
    refine ⟨50329835397294912426285143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33553223598196608284190095 50329835397294912426285143)
    ·
      refine ⟨75494753095942368639427715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50329835397294912426285143 75494753095942368639427715)
      ·
        refine ⟨113242129643913552959141573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75494753095942368639427715 113242129643913552959141573)
        ·
          refine ⟨21232899308233791179839045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 113242129643913552959141573 21232899308233791179839045)
          ·
            refine ⟨3981168620293835846219821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21232899308233791179839045 3981168620293835846219821)
            ·
              refine ⟨1492938232610188442332433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3981168620293835846219821 1492938232610188442332433)
              ·
                refine ⟨1119703674457641331749325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1492938232610188442332433 1119703674457641331749325)
                ·
                  refine ⟨419888877921615499405997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1119703674457641331749325 419888877921615499405997)
                  ·
                    rfl

theorem cell20_919947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 3, 2, 3].length) (baseStart_919947 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_919947 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_919947 prefixEnd_919947 := by exact prefixLift 919947
  have htrace : WordTrace (prefixWord ++ tailWord_919947) baseStart_919947 baseEnd_919947 := by
    simpa [prefixWord, tailWord_919947, baseEnd_919947] using wordTrace_append hprefix tailTrace_919947
  have hstable : (prefixWord ++ tailWord_919947).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919947).length < 2 ^ (prefixWord ++ tailWord_919947).sum := by decide
  have hdescent : baseEnd_919947 < baseStart_919947 := by decide
  rcases family_descends (prefixWord ++ tailWord_919947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919950 : List Nat := [4, 1, 1, 4, 1, 1, 2, 4, 2]
def baseStart_919950 : Nat := 118140960795 + 919950 * 2 ^ 59
def prefixEnd_919950 : Nat := 4983230072969 + 3 ^ 40 * 919950 * 2
def baseEnd_919950 : Nat := 419890247203360822305985

theorem tailTrace_919950 : CollatzResearch.WordTrace tailWord_919950 prefixEnd_919950 419890247203360822305985 := by
  unfold tailWord_919950
  simp only [CollatzResearch.WordTrace]
  refine ⟨4194166627148217474568663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22368888678123826531032869 4194166627148217474568663)
  ·
    refine ⟨6291249940722326211852995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4194166627148217474568663 6291249940722326211852995)
    ·
      refine ⟨9436874911083489317779493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6291249940722326211852995 9436874911083489317779493)
      ·
        refine ⟨1769414045828154247083655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9436874911083489317779493 1769414045828154247083655)
        ·
          refine ⟨2654121068742231370625483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1769414045828154247083655 2654121068742231370625483)
          ·
            refine ⟨3981181603113347055938225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2654121068742231370625483 3981181603113347055938225)
            ·
              refine ⟨2985886202335010291953669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3981181603113347055938225 2985886202335010291953669)
              ·
                refine ⟨559853662937814429741313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2985886202335010291953669 559853662937814429741313)
                ·
                  refine ⟨419890247203360822305985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 559853662937814429741313 419890247203360822305985)
                  ·
                    rfl

theorem cell20_919950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 4, 2].length) (baseStart_919950 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_919950 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_919950 prefixEnd_919950 := by exact prefixLift 919950
  have htrace : WordTrace (prefixWord ++ tailWord_919950) baseStart_919950 baseEnd_919950 := by
    simpa [prefixWord, tailWord_919950, baseEnd_919950] using wordTrace_append hprefix tailTrace_919950
  have hstable : (prefixWord ++ tailWord_919950).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919950).length < 2 ^ (prefixWord ++ tailWord_919950).sum := by decide
  have hdescent : baseEnd_919950 < baseStart_919950 := by decide
  rcases family_descends (prefixWord ++ tailWord_919950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920001 : List Nat := [1, 2, 7, 1, 1, 1, 3, 2, 2]
def baseStart_920001 : Nat := 118140960795 + 920001 * 2 ^ 59
def prefixEnd_920001 : Nat := 4983230072969 + 3 ^ 40 * 920001 * 2
def baseEnd_920001 : Nat := 419913524993031311605777

theorem tailTrace_920001 : CollatzResearch.WordTrace tailWord_920001 prefixEnd_920001 419913524993031311605777 := by
  unfold tailWord_920001
  simp only [CollatzResearch.WordTrace]
  refine ⟨33555193140000975506655857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22370128760000650337770571 33555193140000975506655857)
  ·
    refine ⟨25166394855000731629991893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33555193140000975506655857 25166394855000731629991893)
    ·
      refine ⟨589837379414079647577935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 25166394855000731629991893 589837379414079647577935)
      ·
        refine ⟨884756069121119471366903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 589837379414079647577935 884756069121119471366903)
        ·
          refine ⟨1327134103681679207050355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 884756069121119471366903 1327134103681679207050355)
          ·
            refine ⟨1990701155522518810575533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1327134103681679207050355 1990701155522518810575533)
            ·
              refine ⟨746512933320944553965825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1990701155522518810575533 746512933320944553965825)
              ·
                refine ⟨559884699990708415474369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 746512933320944553965825 559884699990708415474369)
                ·
                  refine ⟨419913524993031311605777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 559884699990708415474369 419913524993031311605777)
                  ·
                    rfl

theorem cell20_920001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 3, 2, 2].length) (baseStart_920001 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_920001 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_920001 prefixEnd_920001 := by exact prefixLift 920001
  have htrace : WordTrace (prefixWord ++ tailWord_920001) baseStart_920001 baseEnd_920001 := by
    simpa [prefixWord, tailWord_920001, baseEnd_920001] using wordTrace_append hprefix tailTrace_920001
  have hstable : (prefixWord ++ tailWord_920001).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920001).length < 2 ^ (prefixWord ++ tailWord_920001).sum := by decide
  have hdescent : baseEnd_920001 < baseStart_920001 := by decide
  rcases family_descends (prefixWord ++ tailWord_920001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920061 : List Nat := [1, 4, 1, 1, 1, 3, 4, 2, 3]
def baseStart_920061 : Nat := 118140960795 + 920061 * 2 ^ 59
def prefixEnd_920061 : Nat := 4983230072969 + 3 ^ 40 * 920061 * 2
def baseEnd_920061 : Nat := 419940910627937769605531

theorem tailTrace_920061 : CollatzResearch.WordTrace tailWord_920061 prefixEnd_920061 419940910627937769605531 := by
  unfold tailWord_920061
  simp only [CollatzResearch.WordTrace]
  refine ⟨33557381519783605753840037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22371587679855737169226691 33557381519783605753840037)
  ·
    refine ⟨6292009034959426078845007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33557381519783605753840037 6292009034959426078845007)
    ·
      refine ⟨9438013552439139118267511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6292009034959426078845007 9438013552439139118267511)
      ·
        refine ⟨14157020328658708677401267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9438013552439139118267511 14157020328658708677401267)
        ·
          refine ⟨21235530492988063016101901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14157020328658708677401267 21235530492988063016101901)
          ·
            refine ⟨7963323934870523631038213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21235530492988063016101901 7963323934870523631038213)
            ·
              refine ⟨1493123237788223180819665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7963323934870523631038213 1493123237788223180819665)
              ·
                refine ⟨1119842428341167385614749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1493123237788223180819665 1119842428341167385614749)
                ·
                  refine ⟨419940910627937769605531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1119842428341167385614749 419940910627937769605531)
                  ·
                    rfl

theorem cell20_920061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 4, 2, 3].length) (baseStart_920061 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_920061 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_920061 prefixEnd_920061 := by exact prefixLift 920061
  have htrace : WordTrace (prefixWord ++ tailWord_920061) baseStart_920061 baseEnd_920061 := by
    simpa [prefixWord, tailWord_920061, baseEnd_920061] using wordTrace_append hprefix tailTrace_920061
  have hstable : (prefixWord ++ tailWord_920061).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920061).length < 2 ^ (prefixWord ++ tailWord_920061).sum := by decide
  have hdescent : baseEnd_920061 < baseStart_920061 := by decide
  rcases family_descends (prefixWord ++ tailWord_920061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920071 : List Nat := [1, 1, 4, 3, 4, 1, 1, 5]
def baseStart_920071 : Nat := 118140960795 + 920071 * 2 ^ 59
def prefixEnd_920071 : Nat := 4983230072969 + 3 ^ 40 * 920071 * 2
def baseEnd_920071 : Nat := 139981824966807393090719

theorem tailTrace_920071 : CollatzResearch.WordTrace tailWord_920071 prefixEnd_920071 139981824966807393090719 := by
  unfold tailWord_920071
  simp only [CollatzResearch.WordTrace]
  refine ⟨33557746249747377461704067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22371830833164918307802711 33557746249747377461704067)
  ·
    refine ⟨50336619374621066192556101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33557746249747377461704067 50336619374621066192556101)
    ·
      refine ⟨9438116132741449911104269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50336619374621066192556101 9438116132741449911104269)
      ·
        refine ⟨3539293549778043716664101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9438116132741449911104269 3539293549778043716664101)
        ·
          refine ⟨663617540583383196874519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3539293549778043716664101 663617540583383196874519)
          ·
            refine ⟨995426310875074795311779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 663617540583383196874519 995426310875074795311779)
            ·
              refine ⟨1493139466312612192967669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 995426310875074795311779 1493139466312612192967669)
              ·
                refine ⟨139981824966807393090719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1493139466312612192967669 139981824966807393090719)
                ·
                  rfl

theorem cell20_920071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 1, 5].length) (baseStart_920071 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_920071 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_920071 prefixEnd_920071 := by exact prefixLift 920071
  have htrace : WordTrace (prefixWord ++ tailWord_920071) baseStart_920071 baseEnd_920071 := by
    simpa [prefixWord, tailWord_920071, baseEnd_920071] using wordTrace_append hprefix tailTrace_920071
  have hstable : (prefixWord ++ tailWord_920071).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920071).length < 2 ^ (prefixWord ++ tailWord_920071).sum := by decide
  have hdescent : baseEnd_920071 < baseStart_920071 := by decide
  rcases family_descends (prefixWord ++ tailWord_920071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920075 : List Nat := [1, 1, 1, 1, 7, 1, 3, 5]
def baseStart_920075 : Nat := 118140960795 + 920075 * 2 ^ 59
def prefixEnd_920075 : Nat := 4983230072969 + 3 ^ 40 * 920075 * 2
def baseEnd_920075 : Nat := 139982433536471981046269

theorem tailTrace_920075 : CollatzResearch.WordTrace tailWord_920075 prefixEnd_920075 139982433536471981046269 := by
  unfold tailWord_920075
  simp only [CollatzResearch.WordTrace]
  refine ⟨33557892141732886144849679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22371928094488590763233119 33557892141732886144849679)
  ·
    refine ⟨50336838212599329217274519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33557892141732886144849679 50336838212599329217274519)
    ·
      refine ⟨75505257318898993825911779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50336838212599329217274519 75505257318898993825911779)
      ·
        refine ⟨113257885978348490738867669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75505257318898993825911779 113257885978348490738867669)
        ·
          refine ⟨2654481702617542751692211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 113257885978348490738867669 2654481702617542751692211)
          ·
            refine ⟨3981722553926314127538317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2654481702617542751692211 3981722553926314127538317)
            ·
              refine ⟨1493145957722367797826869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3981722553926314127538317 1493145957722367797826869)
              ·
                refine ⟨139982433536471981046269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1493145957722367797826869 139982433536471981046269)
                ·
                  rfl

theorem cell20_920075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 3, 5].length) (baseStart_920075 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_920075 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_920075 prefixEnd_920075 := by exact prefixLift 920075
  have htrace : WordTrace (prefixWord ++ tailWord_920075) baseStart_920075 baseEnd_920075 := by
    simpa [prefixWord, tailWord_920075, baseEnd_920075] using wordTrace_append hprefix tailTrace_920075
  have hstable : (prefixWord ++ tailWord_920075).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920075).length < 2 ^ (prefixWord ++ tailWord_920075).sum := by decide
  have hdescent : baseEnd_920075 < baseStart_920075 := by decide
  rcases family_descends (prefixWord ++ tailWord_920075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920089 : List Nat := [1, 2, 1, 2, 1, 1, 2, 6, 4]
def baseStart_920089 : Nat := 118140960795 + 920089 * 2 ^ 59
def prefixEnd_920089 : Nat := 4983230072969 + 3 ^ 40 * 920089 * 2
def baseEnd_920089 : Nat := 419953690590894116672083

theorem tailTrace_920089 : CollatzResearch.WordTrace tailWord_920089 prefixEnd_920089 419953690590894116672083 := by
  unfold tailWord_920089
  simp only [CollatzResearch.WordTrace]
  refine ⟨33558402763682166535859321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22372268509121444357239547 33558402763682166535859321)
  ·
    refine ⟨25168802072761624901894491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33558402763682166535859321 25168802072761624901894491)
    ·
      refine ⟨37753203109142437352841737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25168802072761624901894491 37753203109142437352841737)
      ·
        refine ⟨28314902331856828014631303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37753203109142437352841737 28314902331856828014631303)
        ·
          refine ⟨42472353497785242021946955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28314902331856828014631303 42472353497785242021946955)
          ·
            refine ⟨63708530246677863032920433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42472353497785242021946955 63708530246677863032920433)
            ·
              refine ⟨47781397685008397274690325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63708530246677863032920433 47781397685008397274690325)
              ·
                refine ⟨2239753016484768622251109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 47781397685008397274690325 2239753016484768622251109)
                ·
                  refine ⟨419953690590894116672083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2239753016484768622251109 419953690590894116672083)
                  ·
                    rfl

theorem cell20_920089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 6, 4].length) (baseStart_920089 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_920089 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_920089 prefixEnd_920089 := by exact prefixLift 920089
  have htrace : WordTrace (prefixWord ++ tailWord_920089) baseStart_920089 baseEnd_920089 := by
    simpa [prefixWord, tailWord_920089, baseEnd_920089] using wordTrace_append hprefix tailTrace_920089
  have hstable : (prefixWord ++ tailWord_920089).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920089).length < 2 ^ (prefixWord ++ tailWord_920089).sum := by decide
  have hdescent : baseEnd_920089 < baseStart_920089 := by decide
  rcases family_descends (prefixWord ++ tailWord_920089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920092 : List Nat := [2, 2, 3, 1, 2, 3, 3, 4]
def baseStart_920092 : Nat := 118140960795 + 920092 * 2 ^ 59
def prefixEnd_920092 : Nat := 4983230072969 + 3 ^ 40 * 920092 * 2
def baseEnd_920092 : Nat := 139985019957546479857357

theorem tailTrace_920092 : CollatzResearch.WordTrace tailWord_920092 prefixEnd_920092 139985019957546479857357 := by
  unfold tailWord_920092
  simp only [CollatzResearch.WordTrace]
  refine ⟨16779256091335649024109265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22372341455114198698812353 16779256091335649024109265)
  ·
    refine ⟨12584442068501736768081949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16779256091335649024109265 12584442068501736768081949)
    ·
      refine ⟨4719165775688151288030731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12584442068501736768081949 4719165775688151288030731)
      ·
        refine ⟨7078748663532226932046097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4719165775688151288030731 7078748663532226932046097)
        ·
          refine ⟨5309061497649170199034573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7078748663532226932046097 5309061497649170199034573)
          ·
            refine ⟨1990898061618438824637965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5309061497649170199034573 1990898061618438824637965)
            ·
              refine ⟨746586773106914559239237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1990898061618438824637965 746586773106914559239237)
              ·
                refine ⟨139985019957546479857357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 746586773106914559239237 139985019957546479857357)
                ·
                  rfl

theorem cell20_920092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 3, 4].length) (baseStart_920092 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_920092 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_920092 prefixEnd_920092 := by exact prefixLift 920092
  have htrace : WordTrace (prefixWord ++ tailWord_920092) baseStart_920092 baseEnd_920092 := by
    simpa [prefixWord, tailWord_920092, baseEnd_920092] using wordTrace_append hprefix tailTrace_920092
  have hstable : (prefixWord ++ tailWord_920092).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920092).length < 2 ^ (prefixWord ++ tailWord_920092).sum := by decide
  have hdescent : baseEnd_920092 < baseStart_920092 := by decide
  rcases family_descends (prefixWord ++ tailWord_920092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920120 : List Nat := [2, 1, 2, 1, 4, 1, 3, 1, 5]
def baseStart_920120 : Nat := 118140960795 + 920120 * 2 ^ 59
def prefixEnd_920120 : Nat := 4983230072969 + 3 ^ 40 * 920120 * 2
def baseEnd_920120 : Nat := 419967839835595786638623

theorem tailTrace_920120 : CollatzResearch.WordTrace tailWord_920120 prefixEnd_920120 419967839835595786638623 := by
  unfold tailWord_920120
  simp only [CollatzResearch.WordTrace]
  refine ⟨16779766713284929415118907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22373022284379905886825209 16779766713284929415118907)
  ·
    refine ⟨25169650069927394122678361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16779766713284929415118907 25169650069927394122678361)
    ·
      refine ⟨18877237552445545592008771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25169650069927394122678361 18877237552445545592008771)
      ·
        refine ⟨28315856328668318388013157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18877237552445545592008771 28315856328668318388013157)
        ·
          refine ⟨5309223061625309697752467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28315856328668318388013157 5309223061625309697752467)
          ·
            refine ⟨7963834592437964546628701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5309223061625309697752467 7963834592437964546628701)
            ·
              refine ⟨2986437972164236704985763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7963834592437964546628701 2986437972164236704985763)
              ·
                refine ⟨4479656958246355057478645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2986437972164236704985763 4479656958246355057478645)
                ·
                  refine ⟨419967839835595786638623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4479656958246355057478645 419967839835595786638623)
                  ·
                    rfl

theorem cell20_920120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 1, 5].length) (baseStart_920120 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_920120 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_920120 prefixEnd_920120 := by exact prefixLift 920120
  have htrace : WordTrace (prefixWord ++ tailWord_920120) baseStart_920120 baseEnd_920120 := by
    simpa [prefixWord, tailWord_920120, baseEnd_920120] using wordTrace_append hprefix tailTrace_920120
  have hstable : (prefixWord ++ tailWord_920120).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920120).length < 2 ^ (prefixWord ++ tailWord_920120).sum := by decide
  have hdescent : baseEnd_920120 < baseStart_920120 := by decide
  rcases family_descends (prefixWord ++ tailWord_920120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920161 : List Nat := [1, 2, 3, 1, 1, 4, 3, 3, 2]
def baseStart_920161 : Nat := 118140960795 + 920161 * 2 ^ 59
def prefixEnd_920161 : Nat := 4983230072969 + 3 ^ 40 * 920161 * 2
def baseEnd_920161 : Nat := 419986553352781866271789

theorem tailTrace_920161 : CollatzResearch.WordTrace tailWord_920161 prefixEnd_920161 419986553352781866271789 := by
  unfold tailWord_920161
  simp only [CollatzResearch.WordTrace]
  refine ⟨33561028819421322832480337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22374019212947548554986891 33561028819421322832480337)
  ·
    refine ⟨25170771614565992124360253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33561028819421322832480337 25170771614565992124360253)
    ·
      refine ⟨9439039355462247046635095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25170771614565992124360253 9439039355462247046635095)
      ·
        refine ⟨14158559033193370569952643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9439039355462247046635095 14158559033193370569952643)
        ·
          refine ⟨21237838549790055854928965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14158559033193370569952643 21237838549790055854928965)
          ·
            refine ⟨3982094728085635472799181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21237838549790055854928965 3982094728085635472799181)
            ·
              refine ⟨1493285523032113302299693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3982094728085635472799181 1493285523032113302299693)
              ·
                refine ⟨559982071137042488362385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1493285523032113302299693 559982071137042488362385)
                ·
                  refine ⟨419986553352781866271789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 559982071137042488362385 419986553352781866271789)
                  ·
                    rfl

theorem cell20_920161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 3, 3, 2].length) (baseStart_920161 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_920161 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_920161 prefixEnd_920161 := by exact prefixLift 920161
  have htrace : WordTrace (prefixWord ++ tailWord_920161) baseStart_920161 baseEnd_920161 := by
    simpa [prefixWord, tailWord_920161, baseEnd_920161] using wordTrace_append hprefix tailTrace_920161
  have hstable : (prefixWord ++ tailWord_920161).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920161).length < 2 ^ (prefixWord ++ tailWord_920161).sum := by decide
  have hdescent : baseEnd_920161 < baseStart_920161 := by decide
  rcases family_descends (prefixWord ++ tailWord_920161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920168 : List Nat := [2, 1, 4, 3, 2, 2, 6]
def baseStart_920168 : Nat := 118140960795 + 920168 * 2 ^ 59
def prefixEnd_920168 : Nat := 4983230072969 + 3 ^ 40 * 920168 * 2
def baseEnd_920168 : Nat := 46665527593724550337603

theorem tailTrace_920168 : CollatzResearch.WordTrace tailWord_920168 prefixEnd_920168 46665527593724550337603 := by
  unfold tailWord_920168
  simp only [CollatzResearch.WordTrace]
  refine ⟨16780642065197981513992579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22374189420263975351990105 16780642065197981513992579)
  ·
    refine ⟨25170963097796972270988869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16780642065197981513992579 25170963097796972270988869)
    ·
      refine ⟨4719555580836932300810413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25170963097796972270988869 4719555580836932300810413)
      ·
        refine ⟨1769833342813849612803905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4719555580836932300810413 1769833342813849612803905)
        ·
          refine ⟨1327375007110387209602929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1769833342813849612803905 1327375007110387209602929)
          ·
            refine ⟨995531255332790407202197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1327375007110387209602929 995531255332790407202197)
            ·
              refine ⟨46665527593724550337603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 995531255332790407202197 46665527593724550337603)
              ·
                rfl

theorem cell20_920168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 6].length) (baseStart_920168 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_920168 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_920168 prefixEnd_920168 := by exact prefixLift 920168
  have htrace : WordTrace (prefixWord ++ tailWord_920168) baseStart_920168 baseEnd_920168 := by
    simpa [prefixWord, tailWord_920168, baseEnd_920168] using wordTrace_append hprefix tailTrace_920168
  have hstable : (prefixWord ++ tailWord_920168).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920168).length < 2 ^ (prefixWord ++ tailWord_920168).sum := by decide
  have hdescent : baseEnd_920168 < baseStart_920168 := by decide
  rcases family_descends (prefixWord ++ tailWord_920168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920172 : List Nat := [2, 2, 1, 1, 3, 1, 10]
def baseStart_920172 : Nat := 118140960795 + 920172 * 2 ^ 59
def prefixEnd_920172 : Nat := 4983230072969 + 3 ^ 40 * 920172 * 2
def baseEnd_920172 : Nat := 46665730450279412989453

theorem tailTrace_920172 : CollatzResearch.WordTrace tailWord_920172 prefixEnd_920172 46665730450279412989453 := by
  unfold tailWord_920172
  simp only [CollatzResearch.WordTrace]
  refine ⟨16780715011190735855565385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22374286681587647807420513 16780715011190735855565385)
  ·
    refine ⟨12585536258393051891674039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16780715011190735855565385 12585536258393051891674039)
    ·
      refine ⟨18878304387589577837511059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12585536258393051891674039 18878304387589577837511059)
      ·
        refine ⟨28317456581384366756266589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18878304387589577837511059 28317456581384366756266589)
        ·
          refine ⟨10619046218019137533599971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28317456581384366756266589 10619046218019137533599971)
          ·
            refine ⟨15928569327028706300399957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10619046218019137533599971 15928569327028706300399957)
            ·
              refine ⟨46665730450279412989453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 15928569327028706300399957 46665730450279412989453)
              ·
                rfl

theorem cell20_920172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 10].length) (baseStart_920172 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_920172 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_920172 prefixEnd_920172 := by exact prefixLift 920172
  have htrace : WordTrace (prefixWord ++ tailWord_920172) baseStart_920172 baseEnd_920172 := by
    simpa [prefixWord, tailWord_920172, baseEnd_920172] using wordTrace_append hprefix tailTrace_920172
  have hstable : (prefixWord ++ tailWord_920172).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920172).length < 2 ^ (prefixWord ++ tailWord_920172).sum := by decide
  have hdescent : baseEnd_920172 < baseStart_920172 := by decide
  rcases family_descends (prefixWord ++ tailWord_920172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920178 : List Nat := [3, 2, 1, 2, 5, 1, 1, 1, 4]
def baseStart_920178 : Nat := 118140960795 + 920178 * 2 ^ 59
def prefixEnd_920178 : Nat := 4983230072969 + 3 ^ 40 * 920178 * 2
def baseEnd_920178 : Nat := 419994312616005362705053

theorem tailTrace_920178 : CollatzResearch.WordTrace tailWord_920178 prefixEnd_920178 419994312616005362705053 := by
  unfold tailWord_920178
  simp only [CollatzResearch.WordTrace]
  refine ⟨8390412215089933683962297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22374432573573156490566125 8390412215089933683962297)
  ·
    refine ⟨6292809161317450262971723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8390412215089933683962297 6292809161317450262971723)
    ·
      refine ⟨9439213741976175394457585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6292809161317450262971723 9439213741976175394457585)
      ·
        refine ⟨7079410306482131545843189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9439213741976175394457585 7079410306482131545843189)
        ·
          refine ⟨663694716232699832422799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7079410306482131545843189 663694716232699832422799)
          ·
            refine ⟨995542074349049748634199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 663694716232699832422799 995542074349049748634199)
            ·
              refine ⟨1493313111523574622951299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 995542074349049748634199 1493313111523574622951299)
              ·
                refine ⟨2239969667285361934426949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1493313111523574622951299 2239969667285361934426949)
                ·
                  refine ⟨419994312616005362705053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2239969667285361934426949 419994312616005362705053)
                  ·
                    rfl

theorem cell20_920178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 1, 1, 4].length) (baseStart_920178 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_920178 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_920178 prefixEnd_920178 := by exact prefixLift 920178
  have htrace : WordTrace (prefixWord ++ tailWord_920178) baseStart_920178 baseEnd_920178 := by
    simpa [prefixWord, tailWord_920178, baseEnd_920178] using wordTrace_append hprefix tailTrace_920178
  have hstable : (prefixWord ++ tailWord_920178).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920178).length < 2 ^ (prefixWord ++ tailWord_920178).sum := by decide
  have hdescent : baseEnd_920178 < baseStart_920178 := by decide
  rcases family_descends (prefixWord ++ tailWord_920178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920192 : List Nat := [2, 1, 1, 2, 1, 7, 2, 1, 3]
def baseStart_920192 : Nat := 118140960795 + 920192 * 2 ^ 59
def prefixEnd_920192 : Nat := 4983230072969 + 3 ^ 40 * 920192 * 2
def baseEnd_920192 : Nat := 420000702597483536238329

theorem tailTrace_920192 : CollatzResearch.WordTrace tailWord_920192 prefixEnd_920192 420000702597483536238329 := by
  unfold tailWord_920192
  simp only [CollatzResearch.WordTrace]
  refine ⟨16781079741154507563429415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22374772988206010084572553 16781079741154507563429415)
  ·
    refine ⟨25171619611731761345144123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16781079741154507563429415 25171619611731761345144123)
    ·
      refine ⟨37757429417597642017716185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25171619611731761345144123 37757429417597642017716185)
      ·
        refine ⟨28318072063198231513287139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37757429417597642017716185 28318072063198231513287139)
        ·
          refine ⟨42477108094797347269930709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28318072063198231513287139 42477108094797347269930709)
          ·
            refine ⟨995557220971812826639001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 42477108094797347269930709 995557220971812826639001)
            ·
              refine ⟨746667915728859619979251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 995557220971812826639001 746667915728859619979251)
              ·
                refine ⟨1120001873593289429968877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 746667915728859619979251 1120001873593289429968877)
                ·
                  refine ⟨420000702597483536238329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1120001873593289429968877 420000702597483536238329)
                  ·
                    rfl

theorem cell20_920192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 2, 1, 3].length) (baseStart_920192 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_920192 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_920192 prefixEnd_920192 := by exact prefixLift 920192
  have htrace : WordTrace (prefixWord ++ tailWord_920192) baseStart_920192 baseEnd_920192 := by
    simpa [prefixWord, tailWord_920192, baseEnd_920192] using wordTrace_append hprefix tailTrace_920192
  have hstable : (prefixWord ++ tailWord_920192).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920192).length < 2 ^ (prefixWord ++ tailWord_920192).sum := by decide
  have hdescent : baseEnd_920192 < baseStart_920192 := by decide
  rcases family_descends (prefixWord ++ tailWord_920192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920289 : List Nat := [1, 2, 3, 1, 4, 1, 3, 2, 3]
def baseStart_920289 : Nat := 118140960795 + 920289 * 2 ^ 59
def prefixEnd_920289 : Nat := 4983230072969 + 3 ^ 40 * 920289 * 2
def baseEnd_920289 : Nat := 420044976040582310004599

theorem tailTrace_920289 : CollatzResearch.WordTrace tailWord_920289 prefixEnd_920289 420044976040582310004599 := by
  unfold tailWord_920289
  simp only [CollatzResearch.WordTrace]
  refine ⟨33565697362957600693139921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22377131575305067128759947 33565697362957600693139921)
  ·
    refine ⟨25174273022218200519854941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33565697362957600693139921 25174273022218200519854941)
    ·
      refine ⟨9440352383331825194945603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25174273022218200519854941 9440352383331825194945603)
      ·
        refine ⟨14160528574997737792418405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9440352383331825194945603 14160528574997737792418405)
        ·
          refine ⟨2655099107812075836078451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14160528574997737792418405 2655099107812075836078451)
          ·
            refine ⟨3982648661718113754117677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2655099107812075836078451 3982648661718113754117677)
            ·
              refine ⟨1493493248144292657794129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3982648661718113754117677 1493493248144292657794129)
              ·
                refine ⟨1120119936108219493345597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1493493248144292657794129 1120119936108219493345597)
                ·
                  refine ⟨420044976040582310004599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1120119936108219493345597 420044976040582310004599)
                  ·
                    rfl

theorem cell20_920289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 3, 2, 3].length) (baseStart_920289 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_920289 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_920289 prefixEnd_920289 := by exact prefixLift 920289
  have htrace : WordTrace (prefixWord ++ tailWord_920289) baseStart_920289 baseEnd_920289 := by
    simpa [prefixWord, tailWord_920289, baseEnd_920289] using wordTrace_append hprefix tailTrace_920289
  have hstable : (prefixWord ++ tailWord_920289).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920289).length < 2 ^ (prefixWord ++ tailWord_920289).sum := by decide
  have hdescent : baseEnd_920289 < baseStart_920289 := by decide
  rcases family_descends (prefixWord ++ tailWord_920289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920306 : List Nat := [3, 2, 1, 3, 1, 3, 3, 1, 3]
def baseStart_920306 : Nat := 118140960795 + 920306 * 2 ^ 59
def prefixEnd_920306 : Nat := 4983230072969 + 3 ^ 40 * 920306 * 2
def baseEnd_920306 : Nat := 420052735303805806437863

theorem tailTrace_920306 : CollatzResearch.WordTrace tailWord_920306 prefixEnd_920306 420052735303805806437863 := by
  unfold tailWord_920306
  simp only [CollatzResearch.WordTrace]
  refine ⟨8391579350974003149127193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22377544935930675064339181 8391579350974003149127193)
  ·
    refine ⟨6293684513230502361845395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8391579350974003149127193 6293684513230502361845395)
    ·
      refine ⟨9440526769845753542768093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6293684513230502361845395 9440526769845753542768093)
      ·
        refine ⟨3540197538692157578538035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9440526769845753542768093 3540197538692157578538035)
        ·
          refine ⟨5310296308038236367807053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3540197538692157578538035 5310296308038236367807053)
          ·
            refine ⟨1991361115514338637927645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5310296308038236367807053 1991361115514338637927645)
            ·
              refine ⟨746760418317876989222867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1991361115514338637927645 746760418317876989222867)
              ·
                refine ⟨1120140627476815483834301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 746760418317876989222867 1120140627476815483834301)
                ·
                  refine ⟨420052735303805806437863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1120140627476815483834301 420052735303805806437863)
                  ·
                    rfl

theorem cell20_920306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 3, 1, 3].length) (baseStart_920306 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_920306 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_920306 prefixEnd_920306 := by exact prefixLift 920306
  have htrace : WordTrace (prefixWord ++ tailWord_920306) baseStart_920306 baseEnd_920306 := by
    simpa [prefixWord, tailWord_920306, baseEnd_920306] using wordTrace_append hprefix tailTrace_920306
  have hstable : (prefixWord ++ tailWord_920306).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920306).length < 2 ^ (prefixWord ++ tailWord_920306).sum := by decide
  have hdescent : baseEnd_920306 < baseStart_920306 := by decide
  rcases family_descends (prefixWord ++ tailWord_920306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920317 : List Nat := [1, 4, 1, 1, 1, 1, 3, 4, 4]
def baseStart_920317 : Nat := 118140960795 + 920317 * 2 ^ 59
def prefixEnd_920317 : Nat := 4983230072969 + 3 ^ 40 * 920317 * 2
def baseEnd_920317 : Nat := 420057756003538657071151

theorem tailTrace_920317 : CollatzResearch.WordTrace tailWord_920317 prefixEnd_920317 420057756003538657071151 := by
  unfold tailWord_920317
  simp only [CollatzResearch.WordTrace]
  refine ⟨33566718606856161475159205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22377812404570774316772803 33566718606856161475159205)
  ·
    refine ⟨6293759738785530276592351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33566718606856161475159205 6293759738785530276592351)
    ·
      refine ⟨9440639608178295414888527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6293759738785530276592351 9440639608178295414888527)
      ·
        refine ⟨14160959412267443122332791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9440639608178295414888527 14160959412267443122332791)
        ·
          refine ⟨21241439118401164683499187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14160959412267443122332791 21241439118401164683499187)
          ·
            refine ⟨31862158677601747025248781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21241439118401164683499187 31862158677601747025248781)
            ·
              refine ⟨11948309504100655134468293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31862158677601747025248781 11948309504100655134468293)
              ·
                refine ⟨2240308032018872837712805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11948309504100655134468293 2240308032018872837712805)
                ·
                  refine ⟨420057756003538657071151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2240308032018872837712805 420057756003538657071151)
                  ·
                    rfl

theorem cell20_920317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 4, 4].length) (baseStart_920317 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_920317 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_920317 prefixEnd_920317 := by exact prefixLift 920317
  have htrace : WordTrace (prefixWord ++ tailWord_920317) baseStart_920317 baseEnd_920317 := by
    simpa [prefixWord, tailWord_920317, baseEnd_920317] using wordTrace_append hprefix tailTrace_920317
  have hstable : (prefixWord ++ tailWord_920317).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920317).length < 2 ^ (prefixWord ++ tailWord_920317).sum := by decide
  have hdescent : baseEnd_920317 < baseStart_920317 := by decide
  rcases family_descends (prefixWord ++ tailWord_920317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920348 : List Nat := [2, 2, 3, 1, 1, 3, 2, 1, 5]
def baseStart_920348 : Nat := 118140960795 + 920348 * 2 ^ 59
def prefixEnd_920348 : Nat := 4983230072969 + 3 ^ 40 * 920348 * 2
def baseEnd_920348 : Nat := 420071905248240327037691

theorem tailTrace_920348 : CollatzResearch.WordTrace tailWord_920348 prefixEnd_920348 420071905248240327037691 := by
  unfold tailWord_920348
  simp only [CollatzResearch.WordTrace]
  refine ⟨16783924634871926884768849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22378566179829235846358465 16783924634871926884768849)
  ·
    refine ⟨12587943476153945163576637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16783924634871926884768849 12587943476153945163576637)
    ·
      refine ⟨4720478803557729436341239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12587943476153945163576637 4720478803557729436341239)
      ·
        refine ⟨7080718205336594154511859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4720478803557729436341239 7080718205336594154511859)
        ·
          refine ⟨10621077308004891231767789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7080718205336594154511859 10621077308004891231767789)
          ·
            refine ⟨3982903990501834211912921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10621077308004891231767789 3982903990501834211912921)
            ·
              refine ⟨2987177992876375658934691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3982903990501834211912921 2987177992876375658934691)
              ·
                refine ⟨4480766989314563488402037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2987177992876375658934691 4480766989314563488402037)
                ·
                  refine ⟨420071905248240327037691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4480766989314563488402037 420071905248240327037691)
                  ·
                    rfl

theorem cell20_920348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 1, 5].length) (baseStart_920348 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_920348 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_920348 prefixEnd_920348 := by exact prefixLift 920348
  have htrace : WordTrace (prefixWord ++ tailWord_920348) baseStart_920348 baseEnd_920348 := by
    simpa [prefixWord, tailWord_920348, baseEnd_920348] using wordTrace_append hprefix tailTrace_920348
  have hstable : (prefixWord ++ tailWord_920348).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920348).length < 2 ^ (prefixWord ++ tailWord_920348).sum := by decide
  have hdescent : baseEnd_920348 < baseStart_920348 := by decide
  rcases family_descends (prefixWord ++ tailWord_920348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920458 : List Nat := [3, 1, 2, 4, 1, 3, 1, 2, 3]
def baseStart_920458 : Nat := 118140960795 + 920458 * 2 ^ 59
def prefixEnd_920458 : Nat := 4983230072969 + 3 ^ 40 * 920458 * 2
def baseEnd_920458 : Nat := 420122112245568833370575

theorem tailTrace_920458 : CollatzResearch.WordTrace tailWord_920458 prefixEnd_920458 420122112245568833370575 := by
  unfold tailWord_920458
  simp only [CollatzResearch.WordTrace]
  refine ⟨8392965324836335639010507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22381240866230228370694685 8392965324836335639010507)
  ·
    refine ⟨12589447987254503458515761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8392965324836335639010507 12589447987254503458515761)
    ·
      refine ⟨9442085990440877593886821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12589447987254503458515761 9442085990440877593886821)
      ·
        refine ⟨1770391123207664548853779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9442085990440877593886821 1770391123207664548853779)
        ·
          refine ⟨2655586684811496823280669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1770391123207664548853779 2655586684811496823280669)
          ·
            refine ⟨995845006804311308730251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2655586684811496823280669 995845006804311308730251)
            ·
              refine ⟨1493767510206466963095377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 995845006804311308730251 1493767510206466963095377)
              ·
                refine ⟨1120325632654850222321533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1493767510206466963095377 1120325632654850222321533)
                ·
                  refine ⟨420122112245568833370575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1120325632654850222321533 420122112245568833370575)
                  ·
                    rfl

theorem cell20_920458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 1, 2, 3].length) (baseStart_920458 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_920458 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_920458 prefixEnd_920458 := by exact prefixLift 920458
  have htrace : WordTrace (prefixWord ++ tailWord_920458) baseStart_920458 baseEnd_920458 := by
    simpa [prefixWord, tailWord_920458, baseEnd_920458] using wordTrace_append hprefix tailTrace_920458
  have hstable : (prefixWord ++ tailWord_920458).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920458).length < 2 ^ (prefixWord ++ tailWord_920458).sum := by decide
  have hdescent : baseEnd_920458 < baseStart_920458 := by decide
  rcases family_descends (prefixWord ++ tailWord_920458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920469 : List Nat := [1, 3, 2, 1, 1, 4, 1, 3, 4]
def baseStart_920469 : Nat := 118140960795 + 920469 * 2 ^ 59
def prefixEnd_920469 : Nat := 4983230072969 + 3 ^ 40 * 920469 * 2
def baseEnd_920469 : Nat := 420127132945301684003863

theorem tailTrace_920469 : CollatzResearch.WordTrace tailWord_920469 prefixEnd_920469 420127132945301684003863 := by
  unfold tailWord_920469
  simp only [CollatzResearch.WordTrace]
  refine ⟨33572262502305491434692461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22381508334870327623128307 33572262502305491434692461)
  ·
    refine ⟨12589598438364559288009673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33572262502305491434692461 12589598438364559288009673)
    ·
      refine ⟨9442198828773419466007255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12589598438364559288009673 9442198828773419466007255)
      ·
        refine ⟨14163298243160129199010883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9442198828773419466007255 14163298243160129199010883)
        ·
          refine ⟨21244947364740193798516325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14163298243160129199010883 21244947364740193798516325)
          ·
            refine ⟨3983427630888786337221811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21244947364740193798516325 3983427630888786337221811)
            ·
              refine ⟨5975141446333179505832717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3983427630888786337221811 5975141446333179505832717)
              ·
                refine ⟨2240678042374942314687269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5975141446333179505832717 2240678042374942314687269)
                ·
                  refine ⟨420127132945301684003863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2240678042374942314687269 420127132945301684003863)
                  ·
                    rfl

theorem cell20_920469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 3, 4].length) (baseStart_920469 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_920469 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_920469 prefixEnd_920469 := by exact prefixLift 920469
  have htrace : WordTrace (prefixWord ++ tailWord_920469) baseStart_920469 baseEnd_920469 := by
    simpa [prefixWord, tailWord_920469, baseEnd_920469] using wordTrace_append hprefix tailTrace_920469
  have hstable : (prefixWord ++ tailWord_920469).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920469).length < 2 ^ (prefixWord ++ tailWord_920469).sum := by decide
  have hdescent : baseEnd_920469 < baseStart_920469 := by decide
  rcases family_descends (prefixWord ++ tailWord_920469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920520 : List Nat := [2, 1, 3, 1, 5, 1, 3, 2, 2]
def baseStart_920520 : Nat := 118140960795 + 920520 * 2 ^ 59
def prefixEnd_920520 : Nat := 4983230072969 + 3 ^ 40 * 920520 * 2
def baseEnd_920520 : Nat := 420150410734972173303655

theorem tailTrace_920520 : CollatzResearch.WordTrace tailWord_920520 prefixEnd_920520 420150410734972173303655 := by
  unfold tailWord_920520
  simp only [CollatzResearch.WordTrace]
  refine ⟨16787061312560363572399507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22382748416747151429866009 16787061312560363572399507)
  ·
    refine ⟨25180591968840545358599261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16787061312560363572399507 25180591968840545358599261)
    ·
      refine ⟨9442721988315204509474723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25180591968840545358599261 9442721988315204509474723)
      ·
        refine ⟨14164082982472806764212085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9442721988315204509474723 14164082982472806764212085)
        ·
          refine ⟨1327882779606825634144883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14164082982472806764212085 1327882779606825634144883)
          ·
            refine ⟨1991824169410238451217325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1327882779606825634144883 1991824169410238451217325)
            ·
              refine ⟨746934063528839419206497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1991824169410238451217325 746934063528839419206497)
              ·
                refine ⟨560200547646629564404873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 746934063528839419206497 560200547646629564404873)
                ·
                  refine ⟨420150410734972173303655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 560200547646629564404873 420150410734972173303655)
                  ·
                    rfl

theorem cell20_920520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 3, 2, 2].length) (baseStart_920520 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_920520 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_920520 prefixEnd_920520 := by exact prefixLift 920520
  have htrace : WordTrace (prefixWord ++ tailWord_920520) baseStart_920520 baseEnd_920520 := by
    simpa [prefixWord, tailWord_920520, baseEnd_920520] using wordTrace_append hprefix tailTrace_920520
  have hstable : (prefixWord ++ tailWord_920520).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920520).length < 2 ^ (prefixWord ++ tailWord_920520).sum := by decide
  have hdescent : baseEnd_920520 < baseStart_920520 := by decide
  rcases family_descends (prefixWord ++ tailWord_920520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920534 : List Nat := [5, 2, 1, 1, 2, 2, 1, 3, 3]
def baseStart_920534 : Nat := 118140960795 + 920534 * 2 ^ 59
def prefixEnd_920534 : Nat := 4983230072969 + 3 ^ 40 * 920534 * 2
def baseEnd_920534 : Nat := 420156800716450346836931

theorem tailTrace_920534 : CollatzResearch.WordTrace tailWord_920534 prefixEnd_920534 420156800716450346836931 := by
  unfold tailWord_920534
  simp only [CollatzResearch.WordTrace]
  refine ⟨2098414577941875470988041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22383088831380005023872437 2098414577941875470988041)
  ·
    refine ⟨1573810933456406603241031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2098414577941875470988041 1573810933456406603241031)
    ·
      refine ⟨2360716400184609904861547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1573810933456406603241031 2360716400184609904861547)
      ·
        refine ⟨3541074600276914857292321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2360716400184609904861547 3541074600276914857292321)
        ·
          refine ⟨2655805950207686142969241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3541074600276914857292321 2655805950207686142969241)
          ·
            refine ⟨1991854462655764607226931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2655805950207686142969241 1991854462655764607226931)
            ·
              refine ⟨2987781693983646910840397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1991854462655764607226931 2987781693983646910840397)
              ·
                refine ⟨1120418135243867591565149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2987781693983646910840397 1120418135243867591565149)
                ·
                  refine ⟨420156800716450346836931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1120418135243867591565149 420156800716450346836931)
                  ·
                    rfl

theorem cell20_920534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_920534 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_920534 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_920534 prefixEnd_920534 := by exact prefixLift 920534
  have htrace : WordTrace (prefixWord ++ tailWord_920534) baseStart_920534 baseEnd_920534 := by
    simpa [prefixWord, tailWord_920534, baseEnd_920534] using wordTrace_append hprefix tailTrace_920534
  have hstable : (prefixWord ++ tailWord_920534).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920534).length < 2 ^ (prefixWord ++ tailWord_920534).sum := by decide
  have hdescent : baseEnd_920534 < baseStart_920534 := by decide
  rcases family_descends (prefixWord ++ tailWord_920534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920552 : List Nat := [2, 1, 4, 1, 1, 1, 4, 6]
def baseStart_920552 : Nat := 118140960795 + 920552 * 2 ^ 59
def prefixEnd_920552 : Nat := 4983230072969 + 3 ^ 40 * 920552 * 2
def baseEnd_920552 : Nat := 140055005468974094745619

theorem tailTrace_920552 : CollatzResearch.WordTrace tailWord_920552 prefixEnd_920552 140055005468974094745619 := by
  unfold tailWord_920552
  simp only [CollatzResearch.WordTrace]
  refine ⟨16787644880502398304981955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22383526507336531073309273 16787644880502398304981955)
  ·
    refine ⟨25181467320753597457472933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16787644880502398304981955 25181467320753597457472933)
    ·
      refine ⟨4721525122641299523276175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25181467320753597457472933 4721525122641299523276175)
      ·
        refine ⟨7082287683961949284914263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4721525122641299523276175 7082287683961949284914263)
        ·
          refine ⟨10623431525942923927371395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7082287683961949284914263 10623431525942923927371395)
          ·
            refine ⟨15935147288914385891057093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10623431525942923927371395 15935147288914385891057093)
            ·
              refine ⟨2987840116671447354573205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15935147288914385891057093 2987840116671447354573205)
              ·
                refine ⟨140055005468974094745619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2987840116671447354573205 140055005468974094745619)
                ·
                  rfl

theorem cell20_920552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 6].length) (baseStart_920552 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_920552 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_920552 prefixEnd_920552 := by exact prefixLift 920552
  have htrace : WordTrace (prefixWord ++ tailWord_920552) baseStart_920552 baseEnd_920552 := by
    simpa [prefixWord, tailWord_920552, baseEnd_920552] using wordTrace_append hprefix tailTrace_920552
  have hstable : (prefixWord ++ tailWord_920552).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920552).length < 2 ^ (prefixWord ++ tailWord_920552).sum := by decide
  have hdescent : baseEnd_920552 < baseStart_920552 := by decide
  rcases family_descends (prefixWord ++ tailWord_920552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920583 : List Nat := [1, 1, 4, 3, 1, 1, 2, 3, 4]
def baseStart_920583 : Nat := 118140960795 + 920583 * 2 ^ 59
def prefixEnd_920583 : Nat := 4983230072969 + 3 ^ 40 * 920583 * 2
def baseEnd_920583 : Nat := 420179165651623954203397

theorem tailTrace_920583 : CollatzResearch.WordTrace tailWord_920583 prefixEnd_920583 420179165651623954203397 := by
  unfold tailWord_920583
  simp only [CollatzResearch.WordTrace]
  refine ⟨33576420423892488904342403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22384280282594992602894935 33576420423892488904342403)
  ·
    refine ⟨50364630635838733356513605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33576420423892488904342403 50364630635838733356513605)
    ·
      refine ⟨9443368244219762504346301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50364630635838733356513605 9443368244219762504346301)
      ·
        refine ⟨3541263091582410939129863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9443368244219762504346301 3541263091582410939129863)
        ·
          refine ⟨5311894637373616408694795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3541263091582410939129863 5311894637373616408694795)
          ·
            refine ⟨7967841956060424613042193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5311894637373616408694795 7967841956060424613042193)
            ·
              refine ⟨5975881467045318459781645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7967841956060424613042193 5975881467045318459781645)
              ·
                refine ⟨2240955550141994422418117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5975881467045318459781645 2240955550141994422418117)
                ·
                  refine ⟨420179165651623954203397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2240955550141994422418117 420179165651623954203397)
                  ·
                    rfl

theorem cell20_920583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 3, 4].length) (baseStart_920583 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_920583 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_920583 prefixEnd_920583 := by exact prefixLift 920583
  have htrace : WordTrace (prefixWord ++ tailWord_920583) baseStart_920583 baseEnd_920583 := by
    simpa [prefixWord, tailWord_920583, baseEnd_920583] using wordTrace_append hprefix tailTrace_920583
  have hstable : (prefixWord ++ tailWord_920583).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920583).length < 2 ^ (prefixWord ++ tailWord_920583).sum := by decide
  have hdescent : baseEnd_920583 < baseStart_920583 := by decide
  rcases family_descends (prefixWord ++ tailWord_920583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920607 : List Nat := [1, 1, 2, 4, 1, 4, 3, 4]
def baseStart_920607 : Nat := 118140960795 + 920607 * 2 ^ 59
def prefixEnd_920607 : Nat := 4983230072969 + 3 ^ 40 * 920607 * 2
def baseEnd_920607 : Nat := 140063373301862179134433

theorem tailTrace_920607 : CollatzResearch.WordTrace tailWord_920607 prefixEnd_920607 140063373301862179134433 := by
  unfold tailWord_920607
  simp only [CollatzResearch.WordTrace]
  refine ⟨33577295775805541003216075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22384863850537027335477383 33577295775805541003216075)
  ·
    refine ⟨50365943663708311504824113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33577295775805541003216075 50365943663708311504824113)
    ·
      refine ⟨37774457747781233628618085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50365943663708311504824113 37774457747781233628618085)
      ·
        refine ⟨7082710827708981305365891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37774457747781233628618085 7082710827708981305365891)
        ·
          refine ⟨10624066241563471958048837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7082710827708981305365891 10624066241563471958048837)
          ·
            refine ⟨1992012420293150992134157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10624066241563471958048837 1992012420293150992134157)
            ·
              refine ⟨747004657609931622050309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1992012420293150992134157 747004657609931622050309)
              ·
                refine ⟨140063373301862179134433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 747004657609931622050309 140063373301862179134433)
                ·
                  rfl

theorem cell20_920607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 3, 4].length) (baseStart_920607 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_920607 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_920607 prefixEnd_920607 := by exact prefixLift 920607
  have htrace : WordTrace (prefixWord ++ tailWord_920607) baseStart_920607 baseEnd_920607 := by
    simpa [prefixWord, tailWord_920607, baseEnd_920607] using wordTrace_append hprefix tailTrace_920607
  have hstable : (prefixWord ++ tailWord_920607).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920607).length < 2 ^ (prefixWord ++ tailWord_920607).sum := by decide
  have hdescent : baseEnd_920607 < baseStart_920607 := by decide
  rcases family_descends (prefixWord ++ tailWord_920607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920638 : List Nat := [4, 2, 1, 3, 1, 1, 1, 3, 4]
def baseStart_920638 : Nat := 118140960795 + 920638 * 2 ^ 59
def prefixEnd_920638 : Nat := 4983230072969 + 3 ^ 40 * 920638 * 2
def baseEnd_920638 : Nat := 420204269150288207369839

theorem tailTrace_920638 : CollatzResearch.WordTrace tailWord_920638 prefixEnd_920638 420204269150288207369839 := by
  unfold tailWord_920638
  simp only [CollatzResearch.WordTrace]
  refine ⟨4197303304836654162199321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22385617625795488865063045 4197303304836654162199321)
  ·
    refine ⟨3147977478627490621649491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4197303304836654162199321 3147977478627490621649491)
    ·
      refine ⟨4721966217941235932474237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3147977478627490621649491 4721966217941235932474237)
      ·
        refine ⟨1770737331727963474677839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4721966217941235932474237 1770737331727963474677839)
        ·
          refine ⟨2656105997591945212016759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1770737331727963474677839 2656105997591945212016759)
          ·
            refine ⟨3984158996387917818025139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2656105997591945212016759 3984158996387917818025139)
            ·
              refine ⟨5976238494581876727037709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3984158996387917818025139 5976238494581876727037709)
              ·
                refine ⟨2241089435468203772639141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5976238494581876727037709 2241089435468203772639141)
                ·
                  refine ⟨420204269150288207369839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2241089435468203772639141 420204269150288207369839)
                  ·
                    rfl

theorem cell20_920638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_920638 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_920638 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_920638 prefixEnd_920638 := by exact prefixLift 920638
  have htrace : WordTrace (prefixWord ++ tailWord_920638) baseStart_920638 baseEnd_920638 := by
    simpa [prefixWord, tailWord_920638, baseEnd_920638] using wordTrace_append hprefix tailTrace_920638
  have hstable : (prefixWord ++ tailWord_920638).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920638).length < 2 ^ (prefixWord ++ tailWord_920638).sum := by decide
  have hdescent : baseEnd_920638 < baseStart_920638 := by decide
  rcases family_descends (prefixWord ++ tailWord_920638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920673 : List Nat := [1, 2, 3, 1, 1, 2, 3, 2, 5]
def baseStart_920673 : Nat := 118140960795 + 920673 * 2 ^ 59
def prefixEnd_920673 : Nat := 4983230072969 + 3 ^ 40 * 920673 * 2
def baseEnd_920673 : Nat := 420220244103983641203029

theorem tailTrace_920673 : CollatzResearch.WordTrace tailWord_920673 prefixEnd_920673 420220244103983641203029 := by
  unfold tailWord_920673
  simp only [CollatzResearch.WordTrace]
  refine ⟨33579702993566434275118673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22386468662377622850079115 33579702993566434275118673)
  ·
    refine ⟨25184777245174825706339005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33579702993566434275118673 25184777245174825706339005)
    ·
      refine ⟨9444291466940559639877127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25184777245174825706339005 9444291466940559639877127)
      ·
        refine ⟨14166437200410839459815691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9444291466940559639877127 14166437200410839459815691)
        ·
          refine ⟨21249655800616259189723537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14166437200410839459815691 21249655800616259189723537)
          ·
            refine ⟨15937241850462194392292653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21249655800616259189723537 15937241850462194392292653)
            ·
              refine ⟨5976465693923322897109745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15937241850462194392292653 5976465693923322897109745)
              ·
                refine ⟨4482349270442492172832309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5976465693923322897109745 4482349270442492172832309)
                ·
                  refine ⟨420220244103983641203029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4482349270442492172832309 420220244103983641203029)
                  ·
                    rfl

theorem cell20_920673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 2, 5].length) (baseStart_920673 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_920673 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_920673 prefixEnd_920673 := by exact prefixLift 920673
  have htrace : WordTrace (prefixWord ++ tailWord_920673) baseStart_920673 baseEnd_920673 := by
    simpa [prefixWord, tailWord_920673, baseEnd_920673] using wordTrace_append hprefix tailTrace_920673
  have hstable : (prefixWord ++ tailWord_920673).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920673).length < 2 ^ (prefixWord ++ tailWord_920673).sum := by decide
  have hdescent : baseEnd_920673 < baseStart_920673 := by decide
  rcases family_descends (prefixWord ++ tailWord_920673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920690 : List Nat := [3, 2, 1, 2, 2, 1, 2, 4, 3]
def baseStart_920690 : Nat := 118140960795 + 920690 * 2 ^ 59
def prefixEnd_920690 : Nat := 4983230072969 + 3 ^ 40 * 920690 * 2
def baseEnd_920690 : Nat := 420228003367207137636293

theorem tailTrace_920690 : CollatzResearch.WordTrace tailWord_920690 prefixEnd_920690 420228003367207137636293 := by
  unfold tailWord_920690
  simp only [CollatzResearch.WordTrace]
  refine ⟨8395080758626211544621881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22386882023003230785658349 8395080758626211544621881)
  ·
    refine ⟨6296310568969658658466411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8395080758626211544621881 6296310568969658658466411)
    ·
      refine ⟨9444465853454487987699617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6296310568969658658466411 9444465853454487987699617)
      ·
        refine ⟨7083349390090865990774713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9444465853454487987699617 7083349390090865990774713)
        ·
          refine ⟨5312512042568149493081035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7083349390090865990774713 5312512042568149493081035)
          ·
            refine ⟨7968768063852224239621553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5312512042568149493081035 7968768063852224239621553)
            ·
              refine ⟨5976576047889168179716165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7968768063852224239621553 5976576047889168179716165)
              ·
                refine ⟨1120608008979219033696781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5976576047889168179716165 1120608008979219033696781)
                ·
                  refine ⟨420228003367207137636293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1120608008979219033696781 420228003367207137636293)
                  ·
                    rfl

theorem cell20_920690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 4, 3].length) (baseStart_920690 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_920690 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_920690 prefixEnd_920690 := by exact prefixLift 920690
  have htrace : WordTrace (prefixWord ++ tailWord_920690) baseStart_920690 baseEnd_920690 := by
    simpa [prefixWord, tailWord_920690, baseEnd_920690] using wordTrace_append hprefix tailTrace_920690
  have hstable : (prefixWord ++ tailWord_920690).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920690).length < 2 ^ (prefixWord ++ tailWord_920690).sum := by decide
  have hdescent : baseEnd_920690 < baseStart_920690 := by decide
  rcases family_descends (prefixWord ++ tailWord_920690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920763 : List Nat := [1, 1, 1, 1, 1, 2, 4, 9]
def baseStart_920763 : Nat := 118140960795 + 920763 * 2 ^ 59
def prefixEnd_920763 : Nat := 4983230072969 + 3 ^ 40 * 920763 * 2
def baseEnd_920763 : Nat := 140087107518781109400887

theorem tailTrace_920763 : CollatzResearch.WordTrace tailWord_920763 prefixEnd_920763 140087107518781109400887 := by
  unfold tailWord_920763
  simp only [CollatzResearch.WordTrace]
  refine ⟨33582985563240379645894943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22388657042160253097263295 33582985563240379645894943)
  ·
    refine ⟨50374478344860569468842415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33582985563240379645894943 50374478344860569468842415)
    ·
      refine ⟨75561717517290854203263623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50374478344860569468842415 75561717517290854203263623)
      ·
        refine ⟨113342576275936281304895435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75561717517290854203263623 113342576275936281304895435)
        ·
          refine ⟨170013864413904421957343153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113342576275936281304895435 170013864413904421957343153)
          ·
            refine ⟨127510398310428316468007365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170013864413904421957343153 127510398310428316468007365)
            ·
              refine ⟨23908199683205309337751381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 127510398310428316468007365 23908199683205309337751381)
              ·
                refine ⟨140087107518781109400887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23908199683205309337751381 140087107518781109400887)
                ·
                  rfl

theorem cell20_920763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 9].length) (baseStart_920763 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_920763 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_920763 prefixEnd_920763 := by exact prefixLift 920763
  have htrace : WordTrace (prefixWord ++ tailWord_920763) baseStart_920763 baseEnd_920763 := by
    simpa [prefixWord, tailWord_920763, baseEnd_920763] using wordTrace_append hprefix tailTrace_920763
  have hstable : (prefixWord ++ tailWord_920763).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920763).length < 2 ^ (prefixWord ++ tailWord_920763).sum := by decide
  have hdescent : baseEnd_920763 < baseStart_920763 := by decide
  rcases family_descends (prefixWord ++ tailWord_920763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920794 : List Nat := [3, 1, 1, 2, 2, 1, 1, 1, 8]
def baseStart_920794 : Nat := 118140960795 + 920794 * 2 ^ 59
def prefixEnd_920794 : Nat := 4983230072969 + 3 ^ 40 * 920794 * 2
def baseEnd_920794 : Nat := 420275471801044998169201

theorem tailTrace_920794 : CollatzResearch.WordTrace tailWord_920794 prefixEnd_920794 420275471801044998169201 := by
  unfold tailWord_920794
  simp only [CollatzResearch.WordTrace]
  refine ⟨8396029056532017985068359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22389410817418714626848957 8396029056532017985068359)
  ·
    refine ⟨12594043584798026977602539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8396029056532017985068359 12594043584798026977602539)
    ·
      refine ⟨18891065377197040466403809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12594043584798026977602539 18891065377197040466403809)
      ·
        refine ⟨14168299032897780349802857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18891065377197040466403809 14168299032897780349802857)
        ·
          refine ⟨10626224274673335262352143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14168299032897780349802857 10626224274673335262352143)
          ·
            refine ⟨15939336412010002893528215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10626224274673335262352143 15939336412010002893528215)
            ·
              refine ⟨23909004618015004340292323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15939336412010002893528215 23909004618015004340292323)
              ·
                refine ⟨35863506927022506510438485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23909004618015004340292323 35863506927022506510438485)
                ·
                  refine ⟨420275471801044998169201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35863506927022506510438485 420275471801044998169201)
                  ·
                    rfl

theorem cell20_920794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 8].length) (baseStart_920794 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_920794 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_920794 prefixEnd_920794 := by exact prefixLift 920794
  have htrace : WordTrace (prefixWord ++ tailWord_920794) baseStart_920794 baseEnd_920794 := by
    simpa [prefixWord, tailWord_920794, baseEnd_920794] using wordTrace_append hprefix tailTrace_920794
  have hstable : (prefixWord ++ tailWord_920794).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920794).length < 2 ^ (prefixWord ++ tailWord_920794).sum := by decide
  have hdescent : baseEnd_920794 < baseStart_920794 := by decide
  rcases family_descends (prefixWord ++ tailWord_920794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920797 : List Nat := [1, 4, 3, 2, 2, 1, 7]
def baseStart_920797 : Nat := 118140960795 + 920797 * 2 ^ 59
def prefixEnd_920797 : Nat := 4983230072969 + 3 ^ 40 * 920797 * 2
def baseEnd_920797 : Nat := 46697426786976702341021

theorem tailTrace_920797 : CollatzResearch.WordTrace tailWord_920797 prefixEnd_920797 46697426786976702341021 := by
  unfold tailWord_920797
  simp only [CollatzResearch.WordTrace]
  refine ⟨33584225645117203452632645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22389483763411468968421763 33584225645117203452632645)
  ·
    refine ⟨6297042308459475647368621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33584225645117203452632645 6297042308459475647368621)
    ·
      refine ⟨2361390865672303367763233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6297042308459475647368621 2361390865672303367763233)
      ·
        refine ⟨1771043149254227525822425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2361390865672303367763233 1771043149254227525822425)
        ·
          refine ⟨1328282361940670644366819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1771043149254227525822425 1328282361940670644366819)
          ·
            refine ⟨1992423542911005966550229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1328282361940670644366819 1992423542911005966550229)
            ·
              refine ⟨46697426786976702341021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1992423542911005966550229 46697426786976702341021)
              ·
                rfl

theorem cell20_920797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 7].length) (baseStart_920797 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_920797 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_920797 prefixEnd_920797 := by exact prefixLift 920797
  have htrace : WordTrace (prefixWord ++ tailWord_920797) baseStart_920797 baseEnd_920797 := by
    simpa [prefixWord, tailWord_920797, baseEnd_920797] using wordTrace_append hprefix tailTrace_920797
  have hstable : (prefixWord ++ tailWord_920797).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920797).length < 2 ^ (prefixWord ++ tailWord_920797).sum := by decide
  have hdescent : baseEnd_920797 < baseStart_920797 := by decide
  rcases family_descends (prefixWord ++ tailWord_920797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920804 : List Nat := [2, 3, 1, 1, 1, 2, 5, 2, 3]
def baseStart_920804 : Nat := 118140960795 + 920804 * 2 ^ 59
def prefixEnd_920804 : Nat := 4983230072969 + 3 ^ 40 * 920804 * 2
def baseEnd_920804 : Nat := 420280036073529407835827

theorem tailTrace_920804 : CollatzResearch.WordTrace tailWord_920804 prefixEnd_920804 420280036073529407835827 := by
  unfold tailWord_920804
  simp only [CollatzResearch.WordTrace]
  refine ⟨16792240478045921824068733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22389653970727895765424977 16792240478045921824068733)
  ·
    refine ⟨6297090179267220684025775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16792240478045921824068733 6297090179267220684025775)
    ·
      refine ⟨9445635268900831026038663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6297090179267220684025775 9445635268900831026038663)
      ·
        refine ⟨14168452903351246539057995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9445635268900831026038663 14168452903351246539057995)
        ·
          refine ⟨21252679355026869808586993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14168452903351246539057995 21252679355026869808586993)
          ·
            refine ⟨15939509516270152356440245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21252679355026869808586993 15939509516270152356440245)
            ·
              refine ⟨1494329017150326783416273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15939509516270152356440245 1494329017150326783416273)
              ·
                refine ⟨1120746762862745087562205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1494329017150326783416273 1120746762862745087562205)
                ·
                  refine ⟨420280036073529407835827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1120746762862745087562205 420280036073529407835827)
                  ·
                    rfl

theorem cell20_920804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 5, 2, 3].length) (baseStart_920804 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_920804 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_920804 prefixEnd_920804 := by exact prefixLift 920804
  have htrace : WordTrace (prefixWord ++ tailWord_920804) baseStart_920804 baseEnd_920804 := by
    simpa [prefixWord, tailWord_920804, baseEnd_920804] using wordTrace_append hprefix tailTrace_920804
  have hstable : (prefixWord ++ tailWord_920804).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920804).length < 2 ^ (prefixWord ++ tailWord_920804).sum := by decide
  have hdescent : baseEnd_920804 < baseStart_920804 := by decide
  rcases family_descends (prefixWord ++ tailWord_920804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920811 : List Nat := [1, 1, 1, 1, 2, 7, 2, 1, 4]
def baseStart_920811 : Nat := 118140960795 + 920811 * 2 ^ 59
def prefixEnd_920811 : Nat := 4983230072969 + 3 ^ 40 * 920811 * 2
def baseEnd_920811 : Nat := 420283231064268494602465

theorem tailTrace_920811 : CollatzResearch.WordTrace tailWord_920811 prefixEnd_920811 420283231064268494602465 := by
  unfold tailWord_920811
  simp only [CollatzResearch.WordTrace]
  refine ⟨33584736267066483843642287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22389824178044322562428191 33584736267066483843642287)
  ·
    refine ⟨50377104400599725765463431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33584736267066483843642287 50377104400599725765463431)
    ·
      refine ⟨75565656600899588648195147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50377104400599725765463431 75565656600899588648195147)
      ·
        refine ⟨113348484901349382972292721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75565656600899588648195147 113348484901349382972292721)
        ·
          refine ⟨85011363676012037229219541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113348484901349382972292721 85011363676012037229219541)
          ·
            refine ⟨1992453836156532122559833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 85011363676012037229219541 1992453836156532122559833)
            ·
              refine ⟨1494340377117399091919875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1992453836156532122559833 1494340377117399091919875)
              ·
                refine ⟨2241510565676098637879813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1494340377117399091919875 2241510565676098637879813)
                ·
                  refine ⟨420283231064268494602465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2241510565676098637879813 420283231064268494602465)
                  ·
                    rfl

theorem cell20_920811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 2, 1, 4].length) (baseStart_920811 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_920811 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_920811 prefixEnd_920811 := by exact prefixLift 920811
  have htrace : WordTrace (prefixWord ++ tailWord_920811) baseStart_920811 baseEnd_920811 := by
    simpa [prefixWord, tailWord_920811, baseEnd_920811] using wordTrace_append hprefix tailTrace_920811
  have hstable : (prefixWord ++ tailWord_920811).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920811).length < 2 ^ (prefixWord ++ tailWord_920811).sum := by decide
  have hdescent : baseEnd_920811 < baseStart_920811 := by decide
  rcases family_descends (prefixWord ++ tailWord_920811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920835 : List Nat := [1, 1, 1, 3, 2, 6, 2, 4]
def baseStart_920835 : Nat := 118140960795 + 920835 * 2 ^ 59
def prefixEnd_920835 : Nat := 4983230072969 + 3 ^ 40 * 920835 * 2
def baseEnd_920835 : Nat := 140098061772743692600789

theorem tailTrace_920835 : CollatzResearch.WordTrace tailWord_920835 prefixEnd_920835 140098061772743692600789 := by
  unfold tailWord_920835
  simp only [CollatzResearch.WordTrace]
  refine ⟨33585611618979535942515959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22390407745986357295010639 33585611618979535942515959)
  ·
    refine ⟨50378417428469303913773939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33585611618979535942515959 50378417428469303913773939)
    ·
      refine ⟨75567626142703955870660909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50378417428469303913773939 75567626142703955870660909)
      ·
        refine ⟨28337859803513983451497841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75567626142703955870660909 28337859803513983451497841)
        ·
          refine ⟨21253394852635487588623381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28337859803513983451497841 21253394852635487588623381)
          ·
            refine ⟨996252883717288480716721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 21253394852635487588623381 996252883717288480716721)
            ·
              refine ⟨747189662787966360537541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 996252883717288480716721 747189662787966360537541)
              ·
                refine ⟨140098061772743692600789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 747189662787966360537541 140098061772743692600789)
                ·
                  rfl

theorem cell20_920835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 2, 4].length) (baseStart_920835 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_920835 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_920835 prefixEnd_920835 := by exact prefixLift 920835
  have htrace : WordTrace (prefixWord ++ tailWord_920835) baseStart_920835 baseEnd_920835 := by
    simpa [prefixWord, tailWord_920835, baseEnd_920835] using wordTrace_append hprefix tailTrace_920835
  have hstable : (prefixWord ++ tailWord_920835).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920835).length < 2 ^ (prefixWord ++ tailWord_920835).sum := by decide
  have hdescent : baseEnd_920835 < baseStart_920835 := by decide
  rcases family_descends (prefixWord ++ tailWord_920835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920856 : List Nat := [2, 1, 2, 3, 1, 5, 6]
def baseStart_920856 : Nat := 118140960795 + 920856 * 2 ^ 59
def prefixEnd_920856 : Nat := 4983230072969 + 3 ^ 40 * 920856 * 2
def baseEnd_920856 : Nat := 46700418921160926455809

theorem tailTrace_920856 : CollatzResearch.WordTrace tailWord_920856 prefixEnd_920856 46700418921160926455809 := by
  unfold tailWord_920856
  simp only [CollatzResearch.WordTrace]
  refine ⟨16793188775951728264515211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22390918367935637686020281 16793188775951728264515211)
  ·
    refine ⟨25189783163927592396772817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16793188775951728264515211 25189783163927592396772817)
    ·
      refine ⟨18892337372945694297579613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25189783163927592396772817 18892337372945694297579613)
      ·
        refine ⟨7084626514854635361592355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18892337372945694297579613 7084626514854635361592355)
        ·
          refine ⟨10626939772281953042388533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7084626514854635361592355 10626939772281953042388533)
          ·
            refine ⟨996275603651433097723925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10626939772281953042388533 996275603651433097723925)
            ·
              refine ⟨46700418921160926455809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 996275603651433097723925 46700418921160926455809)
              ·
                rfl

theorem cell20_920856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 6].length) (baseStart_920856 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_920856 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_920856 prefixEnd_920856 := by exact prefixLift 920856
  have htrace : WordTrace (prefixWord ++ tailWord_920856) baseStart_920856 baseEnd_920856 := by
    simpa [prefixWord, tailWord_920856, baseEnd_920856] using wordTrace_append hprefix tailTrace_920856
  have hstable : (prefixWord ++ tailWord_920856).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920856).length < 2 ^ (prefixWord ++ tailWord_920856).sum := by decide
  have hdescent : baseEnd_920856 < baseStart_920856 := by decide
  rcases family_descends (prefixWord ++ tailWord_920856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920862 : List Nat := [4, 3, 2, 1, 2, 2, 1, 1, 4]
def baseStart_920862 : Nat := 118140960795 + 920862 * 2 ^ 59
def prefixEnd_920862 : Nat := 4983230072969 + 3 ^ 40 * 920862 * 2
def baseEnd_920862 : Nat := 420306508853938983902257

theorem tailTrace_920862 : CollatzResearch.WordTrace tailWord_920862 prefixEnd_920862 420306508853938983902257 := by
  unfold tailWord_920862
  simp only [CollatzResearch.WordTrace]
  refine ⟨4198324548735214944218605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22391064259921146369165893 4198324548735214944218605)
  ·
    refine ⟨1574371705775705604081977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4198324548735214944218605 1574371705775705604081977)
    ·
      refine ⟨1180778779331779203061483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1574371705775705604081977 1180778779331779203061483)
      ·
        refine ⟨1771168168997668804592225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1180778779331779203061483 1771168168997668804592225)
        ·
          refine ⟨1328376126748251603444169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1771168168997668804592225 1328376126748251603444169)
          ·
            refine ⟨996282095061188702583127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1328376126748251603444169 996282095061188702583127)
            ·
              refine ⟨1494423142591783053874691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 996282095061188702583127 1494423142591783053874691)
              ·
                refine ⟨2241634713887674580812037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1494423142591783053874691 2241634713887674580812037)
                ·
                  refine ⟨420306508853938983902257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2241634713887674580812037 420306508853938983902257)
                  ·
                    rfl

theorem cell20_920862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_920862 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_920862 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_920862 prefixEnd_920862 := by exact prefixLift 920862
  have htrace : WordTrace (prefixWord ++ tailWord_920862) baseStart_920862 baseEnd_920862 := by
    simpa [prefixWord, tailWord_920862, baseEnd_920862] using wordTrace_append hprefix tailTrace_920862
  have hstable : (prefixWord ++ tailWord_920862).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920862).length < 2 ^ (prefixWord ++ tailWord_920862).sum := by decide
  have hdescent : baseEnd_920862 < baseStart_920862 := by decide
  rcases family_descends (prefixWord ++ tailWord_920862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920894 : List Nat := [4, 2, 1, 2, 1, 1, 1, 8]
def baseStart_920894 : Nat := 118140960795 + 920894 * 2 ^ 59
def prefixEnd_920894 : Nat := 4983230072969 + 3 ^ 40 * 920894 * 2
def baseEnd_920894 : Nat := 140107038175296364945153

theorem tailTrace_920894 : CollatzResearch.WordTrace tailWord_920894 prefixEnd_920894 140107038175296364945153 := by
  unfold tailWord_920894
  simp only [CollatzResearch.WordTrace]
  refine ⟨4198470440720723627364217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22391842350510526012609157 4198470440720723627364217)
  ·
    refine ⟨3148852830540542720523163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4198470440720723627364217 3148852830540542720523163)
    ·
      refine ⟨4723279245810814080784745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3148852830540542720523163 4723279245810814080784745)
      ·
        refine ⟨3542459434358110560588559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4723279245810814080784745 3542459434358110560588559)
        ·
          refine ⟨5313689151537165840882839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3542459434358110560588559 5313689151537165840882839)
          ·
            refine ⟨7970533727305748761324259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5313689151537165840882839 7970533727305748761324259)
            ·
              refine ⟨11955800590958623141986389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7970533727305748761324259 11955800590958623141986389)
              ·
                refine ⟨140107038175296364945153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11955800590958623141986389 140107038175296364945153)
                ·
                  rfl

theorem cell20_920894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 8].length) (baseStart_920894 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_920894 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_920894 prefixEnd_920894 := by exact prefixLift 920894
  have htrace : WordTrace (prefixWord ++ tailWord_920894) baseStart_920894 baseEnd_920894 := by
    simpa [prefixWord, tailWord_920894, baseEnd_920894] using wordTrace_append hprefix tailTrace_920894
  have hstable : (prefixWord ++ tailWord_920894).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920894).length < 2 ^ (prefixWord ++ tailWord_920894).sum := by decide
  have hdescent : baseEnd_920894 < baseStart_920894 := by decide
  rcases family_descends (prefixWord ++ tailWord_920894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920932 : List Nat := [2, 3, 1, 1, 3, 2, 3, 5]
def baseStart_920932 : Nat := 118140960795 + 920932 * 2 ^ 59
def prefixEnd_920932 : Nat := 4983230072969 + 3 ^ 40 * 920932 * 2
def baseEnd_920932 : Nat := 140112819587109950522879

theorem tailTrace_920932 : CollatzResearch.WordTrace tailWord_920932 prefixEnd_920932 140112819587109950522879 := by
  unfold tailWord_920932
  simp only [CollatzResearch.WordTrace]
  refine ⟨16794574749814060754398525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22392766333085414339198033 16794574749814060754398525)
  ·
    refine ⟨6297965531180272782899447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16794574749814060754398525 6297965531180272782899447)
    ·
      refine ⟨9446948296770409174349171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6297965531180272782899447 9446948296770409174349171)
      ·
        refine ⟨14170422445155613761523757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9446948296770409174349171 14170422445155613761523757)
        ·
          refine ⟨5313908416933355160571409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14170422445155613761523757 5313908416933355160571409)
          ·
            refine ⟨3985431312700016370428557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5313908416933355160571409 3985431312700016370428557)
            ·
              refine ⟨1494536742262506138910709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3985431312700016370428557 1494536742262506138910709)
              ·
                refine ⟨140112819587109950522879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1494536742262506138910709 140112819587109950522879)
                ·
                  rfl

theorem cell20_920932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 3, 5].length) (baseStart_920932 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_920932 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_920932 prefixEnd_920932 := by exact prefixLift 920932
  have htrace : WordTrace (prefixWord ++ tailWord_920932) baseStart_920932 baseEnd_920932 := by
    simpa [prefixWord, tailWord_920932, baseEnd_920932] using wordTrace_append hprefix tailTrace_920932
  have hstable : (prefixWord ++ tailWord_920932).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920932).length < 2 ^ (prefixWord ++ tailWord_920932).sum := by decide
  have hdescent : baseEnd_920932 < baseStart_920932 := by decide
  rcases family_descends (prefixWord ++ tailWord_920932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920953 : List Nat := [1, 2, 1, 3, 2, 1, 2, 8]
def baseStart_920953 : Nat := 118140960795 + 920953 * 2 ^ 59
def prefixEnd_920953 : Nat := 4983230072969 + 3 ^ 40 * 920953 * 2
def baseEnd_920953 : Nat := 140116014577849037289517

theorem tailTrace_920953 : CollatzResearch.WordTrace tailWord_920953 prefixEnd_920953 140116014577849037289517 := by
  unfold tailWord_920953
  simp only [CollatzResearch.WordTrace]
  refine ⟨33589915432552042095311513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22393276955034694730207675 33589915432552042095311513)
  ·
    refine ⟨25192436574414031571483635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33589915432552042095311513 25192436574414031571483635)
    ·
      refine ⟨37788654861621047357225453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25192436574414031571483635 37788654861621047357225453)
      ·
        refine ⟨14170745573107892758959545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37788654861621047357225453 14170745573107892758959545)
        ·
          refine ⟨10628059179830919569219659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14170745573107892758959545 10628059179830919569219659)
          ·
            refine ⟨15942088769746379353829489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10628059179830919569219659 15942088769746379353829489)
            ·
              refine ⟨11956566577309784515372117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15942088769746379353829489 11956566577309784515372117)
              ·
                refine ⟨140116014577849037289517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11956566577309784515372117 140116014577849037289517)
                ·
                  rfl

theorem cell20_920953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 8].length) (baseStart_920953 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_920953 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_920953 prefixEnd_920953 := by exact prefixLift 920953
  have htrace : WordTrace (prefixWord ++ tailWord_920953) baseStart_920953 baseEnd_920953 := by
    simpa [prefixWord, tailWord_920953, baseEnd_920953] using wordTrace_append hprefix tailTrace_920953
  have hstable : (prefixWord ++ tailWord_920953).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920953).length < 2 ^ (prefixWord ++ tailWord_920953).sum := by decide
  have hdescent : baseEnd_920953 < baseStart_920953 := by decide
  rcases family_descends (prefixWord ++ tailWord_920953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920980 : List Nat := [2, 4, 2, 1, 2, 2, 2, 1, 4]
def baseStart_920980 : Nat := 118140960795 + 920980 * 2 ^ 59
def prefixEnd_920980 : Nat := 4983230072969 + 3 ^ 40 * 920980 * 2
def baseEnd_920980 : Nat := 420360367269255017968441

theorem tailTrace_920980 : CollatzResearch.WordTrace tailWord_920980 prefixEnd_920980 420360367269255017968441 := by
  unfold tailWord_920980
  simp only [CollatzResearch.WordTrace]
  refine ⟨16795450101727112853272197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22393933468969483804362929 16795450101727112853272197)
  ·
    refine ⟨3149146894073833659988537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16795450101727112853272197 3149146894073833659988537)
    ·
      refine ⟨2361860170555375244991403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3149146894073833659988537 2361860170555375244991403)
      ·
        refine ⟨3542790255833062867487105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2361860170555375244991403 3542790255833062867487105)
        ·
          refine ⟨2657092691874797150615329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3542790255833062867487105 2657092691874797150615329)
          ·
            refine ⟨1992819518906097862961497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2657092691874797150615329 1992819518906097862961497)
            ·
              refine ⟨1494614639179573397221123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1992819518906097862961497 1494614639179573397221123)
              ·
                refine ⟨2241921958769360095831685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1494614639179573397221123 2241921958769360095831685)
                ·
                  refine ⟨420360367269255017968441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2241921958769360095831685 420360367269255017968441)
                  ·
                    rfl

theorem cell20_920980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_920980 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_920980 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_920980 prefixEnd_920980 := by exact prefixLift 920980
  have htrace : WordTrace (prefixWord ++ tailWord_920980) baseStart_920980 baseEnd_920980 := by
    simpa [prefixWord, tailWord_920980, baseEnd_920980] using wordTrace_append hprefix tailTrace_920980
  have hstable : (prefixWord ++ tailWord_920980).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920980).length < 2 ^ (prefixWord ++ tailWord_920980).sum := by decide
  have hdescent : baseEnd_920980 < baseStart_920980 := by decide
  rcases family_descends (prefixWord ++ tailWord_920980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921039 : List Nat := [1, 1, 2, 1, 1, 4, 2, 6, 2]
def baseStart_921039 : Nat := 118140960795 + 921039 * 2 ^ 59
def prefixEnd_921039 : Nat := 4983230072969 + 3 ^ 40 * 921039 * 2
def baseEnd_921039 : Nat := 420387296476913035001533

theorem tailTrace_921039 : CollatzResearch.WordTrace tailWord_921039 prefixEnd_921039 420387296476913035001533 := by
  unfold tailWord_921039
  simp only [CollatzResearch.WordTrace]
  refine ⟨33593052110240478782942171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22395368073493652521961447 33593052110240478782942171)
  ·
    refine ⟨50389578165360718174413257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33593052110240478782942171 50389578165360718174413257)
    ·
      refine ⟨37792183624020538630809943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50389578165360718174413257 37792183624020538630809943)
      ·
        refine ⟨56688275436030807946214915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37792183624020538630809943 56688275436030807946214915)
        ·
          refine ⟨85032413154046211919322373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56688275436030807946214915 85032413154046211919322373)
          ·
            refine ⟨15943577466383664734872945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85032413154046211919322373 15943577466383664734872945)
            ·
              refine ⟨11957683099787748551154709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15943577466383664734872945 11957683099787748551154709)
              ·
                refine ⟨560516395302550713335377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11957683099787748551154709 560516395302550713335377)
                ·
                  refine ⟨420387296476913035001533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 560516395302550713335377 420387296476913035001533)
                  ·
                    rfl

theorem cell20_921039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 6, 2].length) (baseStart_921039 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_921039 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_921039 prefixEnd_921039 := by exact prefixLift 921039
  have htrace : WordTrace (prefixWord ++ tailWord_921039) baseStart_921039 baseEnd_921039 := by
    simpa [prefixWord, tailWord_921039, baseEnd_921039] using wordTrace_append hprefix tailTrace_921039
  have hstable : (prefixWord ++ tailWord_921039).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921039).length < 2 ^ (prefixWord ++ tailWord_921039).sum := by decide
  have hdescent : baseEnd_921039 < baseStart_921039 := by decide
  rcases family_descends (prefixWord ++ tailWord_921039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921049 : List Nat := [1, 2, 1, 2, 4, 4, 2, 1, 3]
def baseStart_921049 : Nat := 118140960795 + 921049 * 2 ^ 59
def prefixEnd_921049 : Nat := 4983230072969 + 3 ^ 40 * 921049 * 2
def baseEnd_921049 : Nat := 420391860749397444668159

theorem tailTrace_921049 : CollatzResearch.WordTrace tailWord_921049 prefixEnd_921049 420391860749397444668159 := by
  unfold tailWord_921049
  simp only [CollatzResearch.WordTrace]
  refine ⟨33593416840204250490806201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22395611226802833660537467 33593416840204250490806201)
  ·
    refine ⟨25195062630153187868104651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33593416840204250490806201 25195062630153187868104651)
    ·
      refine ⟨37792593945229781802156977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25195062630153187868104651 37792593945229781802156977)
      ·
        refine ⟨28344445458922336351617733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37792593945229781802156977 28344445458922336351617733)
        ·
          refine ⟨5314583523547938065928325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28344445458922336351617733 5314583523547938065928325)
          ·
            refine ⟨996484410665238387361561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5314583523547938065928325 996484410665238387361561)
            ·
              refine ⟨747363307998928790521171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 996484410665238387361561 747363307998928790521171)
              ·
                refine ⟨1121044961998393185781757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 747363307998928790521171 1121044961998393185781757)
                ·
                  refine ⟨420391860749397444668159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1121044961998393185781757 420391860749397444668159)
                  ·
                    rfl

theorem cell20_921049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 2, 1, 3].length) (baseStart_921049 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_921049 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_921049 prefixEnd_921049 := by exact prefixLift 921049
  have htrace : WordTrace (prefixWord ++ tailWord_921049) baseStart_921049 baseEnd_921049 := by
    simpa [prefixWord, tailWord_921049, baseEnd_921049] using wordTrace_append hprefix tailTrace_921049
  have hstable : (prefixWord ++ tailWord_921049).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921049).length < 2 ^ (prefixWord ++ tailWord_921049).sum := by decide
  have hdescent : baseEnd_921049 < baseStart_921049 := by decide
  rcases family_descends (prefixWord ++ tailWord_921049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921060 : List Nat := [2, 3, 1, 1, 1, 1, 1, 6, 4]
def baseStart_921060 : Nat := 118140960795 + 921060 * 2 ^ 59
def prefixEnd_921060 : Nat := 4983230072969 + 3 ^ 40 * 921060 * 2
def baseEnd_921060 : Nat := 420396881449130295301447

theorem tailTrace_921060 : CollatzResearch.WordTrace tailWord_921060 prefixEnd_921060 420396881449130295301447 := by
  unfold tailWord_921060
  simp only [CollatzResearch.WordTrace]
  refine ⟨16796909021582199684728317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22395878695442932912971089 16796909021582199684728317)
  ·
    refine ⟨6298840883093324881773119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16796909021582199684728317 6298840883093324881773119)
    ·
      refine ⟨9448261324639987322659679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6298840883093324881773119 9448261324639987322659679)
      ·
        refine ⟨14172391986959980983989519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9448261324639987322659679 14172391986959980983989519)
        ·
          refine ⟨21258587980439971475984279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14172391986959980983989519 21258587980439971475984279)
          ·
            refine ⟨31887881970659957213976419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21258587980439971475984279 31887881970659957213976419)
            ·
              refine ⟨47831822955989935820964629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31887881970659957213976419 47831822955989935820964629)
              ·
                refine ⟨2242116701062028241607717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 47831822955989935820964629 2242116701062028241607717)
                ·
                  refine ⟨420396881449130295301447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2242116701062028241607717 420396881449130295301447)
                  ·
                    rfl

theorem cell20_921060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 6, 4].length) (baseStart_921060 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_921060 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_921060 prefixEnd_921060 := by exact prefixLift 921060
  have htrace : WordTrace (prefixWord ++ tailWord_921060) baseStart_921060 baseEnd_921060 := by
    simpa [prefixWord, tailWord_921060, baseEnd_921060] using wordTrace_append hprefix tailTrace_921060
  have hstable : (prefixWord ++ tailWord_921060).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921060).length < 2 ^ (prefixWord ++ tailWord_921060).sum := by decide
  have hdescent : baseEnd_921060 < baseStart_921060 := by decide
  rcases family_descends (prefixWord ++ tailWord_921060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921086 : List Nat := [4, 2, 2, 3, 2, 1, 2, 2, 2]
def baseStart_921086 : Nat := 118140960795 + 921086 * 2 ^ 59
def prefixEnd_921086 : Nat := 4983230072969 + 3 ^ 40 * 921086 * 2
def baseEnd_921086 : Nat := 420408748557589760434675

theorem tailTrace_921086 : CollatzResearch.WordTrace tailWord_921086 prefixEnd_921086 420408748557589760434675 := by
  unfold tailWord_921086
  simp only [CollatzResearch.WordTrace]
  refine ⟨4199345792633775726237889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22396510894046803873268741 4199345792633775726237889)
  ·
    refine ⟨3149509344475331794678417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4199345792633775726237889 3149509344475331794678417)
    ·
      refine ⟨2362132008356498846008813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3149509344475331794678417 2362132008356498846008813)
      ·
        refine ⟨885799503133687067253305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2362132008356498846008813 885799503133687067253305)
        ·
          refine ⟨664349627350265300439979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 885799503133687067253305 664349627350265300439979)
          ·
            refine ⟨996524441025397950659969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 664349627350265300439979 996524441025397950659969)
            ·
              refine ⟨747393330769048462994977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 996524441025397950659969 747393330769048462994977)
              ·
                refine ⟨560544998076786347246233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 747393330769048462994977 560544998076786347246233)
                ·
                  refine ⟨420408748557589760434675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 560544998076786347246233 420408748557589760434675)
                  ·
                    rfl

theorem cell20_921086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 2, 2, 2].length) (baseStart_921086 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_921086 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_921086 prefixEnd_921086 := by exact prefixLift 921086
  have htrace : WordTrace (prefixWord ++ tailWord_921086) baseStart_921086 baseEnd_921086 := by
    simpa [prefixWord, tailWord_921086, baseEnd_921086] using wordTrace_append hprefix tailTrace_921086
  have hstable : (prefixWord ++ tailWord_921086).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921086).length < 2 ^ (prefixWord ++ tailWord_921086).sum := by decide
  have hdescent : baseEnd_921086 < baseStart_921086 := by decide
  rcases family_descends (prefixWord ++ tailWord_921086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921090 : List Nat := [3, 4, 1, 2, 1, 1, 4, 2, 2]
def baseStart_921090 : Nat := 118140960795 + 921090 * 2 ^ 59
def prefixEnd_921090 : Nat := 4983230072969 + 3 ^ 40 * 921090 * 2
def baseEnd_921090 : Nat := 420410574266583524301325

theorem tailTrace_921090 : CollatzResearch.WordTrace tailWord_921090 prefixEnd_921090 420410574266583524301325 := by
  unfold tailWord_921090
  simp only [CollatzResearch.WordTrace]
  refine ⟨8398728058263928623262181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22396608155370476328699149 8398728058263928623262181)
  ·
    refine ⟨1574761510924486616861659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8398728058263928623262181 1574761510924486616861659)
    ·
      refine ⟨2362142266386729925292489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1574761510924486616861659 2362142266386729925292489)
      ·
        refine ⟨1771606699790047443969367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2362142266386729925292489 1771606699790047443969367)
        ·
          refine ⟨2657410049685071165954051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1771606699790047443969367 2657410049685071165954051)
          ·
            refine ⟨3986115074527606748931077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2657410049685071165954051 3986115074527606748931077)
            ·
              refine ⟨747396576473926265424577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3986115074527606748931077 747396576473926265424577)
              ·
                refine ⟨560547432355444699068433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 747396576473926265424577 560547432355444699068433)
                ·
                  refine ⟨420410574266583524301325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 560547432355444699068433 420410574266583524301325)
                  ·
                    rfl

theorem cell20_921090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 4, 2, 2].length) (baseStart_921090 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_921090 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_921090 prefixEnd_921090 := by exact prefixLift 921090
  have htrace : WordTrace (prefixWord ++ tailWord_921090) baseStart_921090 baseEnd_921090 := by
    simpa [prefixWord, tailWord_921090, baseEnd_921090] using wordTrace_append hprefix tailTrace_921090
  have hstable : (prefixWord ++ tailWord_921090).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921090).length < 2 ^ (prefixWord ++ tailWord_921090).sum := by decide
  have hdescent : baseEnd_921090 < baseStart_921090 := by decide
  rcases family_descends (prefixWord ++ tailWord_921090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921142 : List Nat := [5, 1, 2, 1, 3, 2, 1, 2, 3]
def baseStart_921142 : Nat := 118140960795 + 921142 * 2 ^ 59
def prefixEnd_921142 : Nat := 4983230072969 + 3 ^ 40 * 921142 * 2
def baseEnd_921142 : Nat := 420434308483502454567779

theorem tailTrace_921142 : CollatzResearch.WordTrace tailWord_921142 prefixEnd_921142 420434308483502454567779 := by
  unfold tailWord_921142
  simp only [CollatzResearch.WordTrace]
  refine ⟨2099800551804207960871355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22397872552578218249294453 2099800551804207960871355)
  ·
    refine ⟨3149700827706311941307033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2099800551804207960871355 3149700827706311941307033)
    ·
      refine ⟨2362275620779733955980275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3149700827706311941307033 2362275620779733955980275)
      ·
        refine ⟨3543413431169600933970413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2362275620779733955980275 3543413431169600933970413)
        ·
          refine ⟨1328780036688600350238905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3543413431169600933970413 1328780036688600350238905)
          ·
            refine ⟨996585027516450262679179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1328780036688600350238905 996585027516450262679179)
            ·
              refine ⟨1494877541274675394018769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 996585027516450262679179 1494877541274675394018769)
              ·
                refine ⟨1121158155956006545514077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1494877541274675394018769 1121158155956006545514077)
                ·
                  refine ⟨420434308483502454567779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1121158155956006545514077 420434308483502454567779)
                  ·
                    rfl

theorem cell20_921142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 1, 2, 3].length) (baseStart_921142 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_921142 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_921142 prefixEnd_921142 := by exact prefixLift 921142
  have htrace : WordTrace (prefixWord ++ tailWord_921142) baseStart_921142 baseEnd_921142 := by
    simpa [prefixWord, tailWord_921142, baseEnd_921142] using wordTrace_append hprefix tailTrace_921142
  have hstable : (prefixWord ++ tailWord_921142).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921142).length < 2 ^ (prefixWord ++ tailWord_921142).sum := by decide
  have hdescent : baseEnd_921142 < baseStart_921142 := by decide
  rcases family_descends (prefixWord ++ tailWord_921142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921143 : List Nat := [1, 1, 3, 1, 2, 5, 7]
def baseStart_921143 : Nat := 118140960795 + 921143 * 2 ^ 59
def prefixEnd_921143 : Nat := 4983230072969 + 3 ^ 40 * 921143 * 2
def baseEnd_921143 : Nat := 46714973878972321726049

theorem tailTrace_921143 : CollatzResearch.WordTrace tailWord_921143 prefixEnd_921143 46714973878972321726049 := by
  unfold tailWord_921143
  simp only [CollatzResearch.WordTrace]
  refine ⟨33596845301863704544728083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22397896867909136363152055 33596845301863704544728083)
  ·
    refine ⟨50395267952795556817092125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33596845301863704544728083 50395267952795556817092125)
    ·
      refine ⟨18898225482298333806409547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50395267952795556817092125 18898225482298333806409547)
      ·
        refine ⟨28347338223447500709614321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18898225482298333806409547 28347338223447500709614321)
        ·
          refine ⟨21260503667585625532210741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28347338223447500709614321 21260503667585625532210741)
          ·
            refine ⟨1993172218836152393644757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21260503667585625532210741 1993172218836152393644757)
            ·
              refine ⟨46714973878972321726049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1993172218836152393644757 46714973878972321726049)
              ·
                rfl

theorem cell20_921143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 7].length) (baseStart_921143 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_921143 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_921143 prefixEnd_921143 := by exact prefixLift 921143
  have htrace : WordTrace (prefixWord ++ tailWord_921143) baseStart_921143 baseEnd_921143 := by
    simpa [prefixWord, tailWord_921143, baseEnd_921143] using wordTrace_append hprefix tailTrace_921143
  have hstable : (prefixWord ++ tailWord_921143).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921143).length < 2 ^ (prefixWord ++ tailWord_921143).sum := by decide
  have hdescent : baseEnd_921143 < baseStart_921143 := by decide
  rcases family_descends (prefixWord ++ tailWord_921143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921153 : List Nat := [1, 2, 5, 1, 1, 1, 4, 1, 4]
def baseStart_921153 : Nat := 118140960795 + 921153 * 2 ^ 59
def prefixEnd_921153 : Nat := 4983230072969 + 3 ^ 40 * 921153 * 2
def baseEnd_921153 : Nat := 420439329183235305201067

theorem tailTrace_921153 : CollatzResearch.WordTrace tailWord_921153 prefixEnd_921153 420439329183235305201067 := by
  unfold tailWord_921153
  simp only [CollatzResearch.WordTrace]
  refine ⟨33597210031827476252592113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22398140021218317501728075 33597210031827476252592113)
  ·
    refine ⟨25197907523870607189444085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33597210031827476252592113 25197907523870607189444085)
    ·
      refine ⟨2362303830362869424010383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25197907523870607189444085 2362303830362869424010383)
      ·
        refine ⟨3543455745544304136015575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2362303830362869424010383 3543455745544304136015575)
        ·
          refine ⟨5315183618316456204023363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3543455745544304136015575 5315183618316456204023363)
          ·
            refine ⟨7972775427474684306035045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5315183618316456204023363 7972775427474684306035045)
            ·
              refine ⟨1494895392651503307381571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7972775427474684306035045 1494895392651503307381571)
              ·
                refine ⟨2242343088977254961072357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1494895392651503307381571 2242343088977254961072357)
                ·
                  refine ⟨420439329183235305201067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2242343088977254961072357 420439329183235305201067)
                  ·
                    rfl

theorem cell20_921153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 4, 1, 4].length) (baseStart_921153 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_921153 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_921153 prefixEnd_921153 := by exact prefixLift 921153
  have htrace : WordTrace (prefixWord ++ tailWord_921153) baseStart_921153 baseEnd_921153 := by
    simpa [prefixWord, tailWord_921153, baseEnd_921153] using wordTrace_append hprefix tailTrace_921153
  have hstable : (prefixWord ++ tailWord_921153).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921153).length < 2 ^ (prefixWord ++ tailWord_921153).sum := by decide
  have hdescent : baseEnd_921153 < baseStart_921153 := by decide
  rcases family_descends (prefixWord ++ tailWord_921153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921264 : List Nat := [2, 1, 1, 1, 2, 1, 4, 3, 5]
def baseStart_921264 : Nat := 118140960795 + 921264 * 2 ^ 59
def prefixEnd_921264 : Nat := 4983230072969 + 3 ^ 40 * 921264 * 2
def baseEnd_921264 : Nat := 420489992607812252500613

theorem tailTrace_921264 : CollatzResearch.WordTrace tailWord_921264 prefixEnd_921264 420489992607812252500613 := by
  unfold tailWord_921264
  simp only [CollatzResearch.WordTrace]
  refine ⟨16800629267212671104941423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22400839022950228139921897 16800629267212671104941423)
  ·
    refine ⟨25200943900819006657412135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16800629267212671104941423 25200943900819006657412135)
    ·
      refine ⟨37801415851228509986118203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25200943900819006657412135 37801415851228509986118203)
      ·
        refine ⟨56702123776842764979177305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37801415851228509986118203 56702123776842764979177305)
        ·
          refine ⟨42526592832632073734382979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56702123776842764979177305 42526592832632073734382979)
          ·
            refine ⟨63789889248948110601574469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42526592832632073734382979 63789889248948110601574469)
            ·
              refine ⟨11960604234177770737795213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63789889248948110601574469 11960604234177770737795213)
              ·
                refine ⟨4485226587816664026673205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11960604234177770737795213 4485226587816664026673205)
                ·
                  refine ⟨420489992607812252500613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4485226587816664026673205 420489992607812252500613)
                  ·
                    rfl

theorem cell20_921264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 3, 5].length) (baseStart_921264 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_921264 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_921264 prefixEnd_921264 := by exact prefixLift 921264
  have htrace : WordTrace (prefixWord ++ tailWord_921264) baseStart_921264 baseEnd_921264 := by
    simpa [prefixWord, tailWord_921264, baseEnd_921264] using wordTrace_append hprefix tailTrace_921264
  have hstable : (prefixWord ++ tailWord_921264).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921264).length < 2 ^ (prefixWord ++ tailWord_921264).sum := by decide
  have hdescent : baseEnd_921264 < baseStart_921264 := by decide
  rcases family_descends (prefixWord ++ tailWord_921264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921267 : List Nat := [1, 1, 1, 2, 3, 3, 3, 4, 2]
def baseStart_921267 : Nat := 118140960795 + 921267 * 2 ^ 59
def prefixEnd_921267 : Nat := 4983230072969 + 3 ^ 40 * 921267 * 2
def baseEnd_921267 : Nat := 420491361889557575400601

theorem tailTrace_921267 : CollatzResearch.WordTrace tailWord_921267 prefixEnd_921267 420491361889557575400601 := by
  unfold tailWord_921267
  simp only [CollatzResearch.WordTrace]
  refine ⟨33601367953414473722242055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22400911968942982481494703 33601367953414473722242055)
  ·
    refine ⟨50402051930121710583363083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33601367953414473722242055 50402051930121710583363083)
    ·
      refine ⟨75603077895182565875044625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50402051930121710583363083 75603077895182565875044625)
      ·
        refine ⟨56702308421386924406283469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75603077895182565875044625 56702308421386924406283469)
        ·
          refine ⟨21263365658020096652356301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56702308421386924406283469 21263365658020096652356301)
          ·
            refine ⟨7973762121757536244633613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21263365658020096652356301 7973762121757536244633613)
            ·
              refine ⟨2990160795659076091737605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7973762121757536244633613 2990160795659076091737605)
              ·
                refine ⟨560655149186076767200801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2990160795659076091737605 560655149186076767200801)
                ·
                  refine ⟨420491361889557575400601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 560655149186076767200801 420491361889557575400601)
                  ·
                    rfl

theorem cell20_921267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 4, 2].length) (baseStart_921267 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_921267 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_921267 prefixEnd_921267 := by exact prefixLift 921267
  have htrace : WordTrace (prefixWord ++ tailWord_921267) baseStart_921267 baseEnd_921267 := by
    simpa [prefixWord, tailWord_921267, baseEnd_921267] using wordTrace_append hprefix tailTrace_921267
  have hstable : (prefixWord ++ tailWord_921267).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921267).length < 2 ^ (prefixWord ++ tailWord_921267).sum := by decide
  have hdescent : baseEnd_921267 < baseStart_921267 := by decide
  rcases family_descends (prefixWord ++ tailWord_921267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921270 : List Nat := [5, 1, 3, 1, 1, 3, 1, 5]
def baseStart_921270 : Nat := 118140960795 + 921270 * 2 ^ 59
def prefixEnd_921270 : Nat := 4983230072969 + 3 ^ 40 * 921270 * 2
def baseEnd_921270 : Nat := 140164243723767632766863

theorem tailTrace_921270 : CollatzResearch.WordTrace tailWord_921270 prefixEnd_921270 140164243723767632766863 := by
  unfold tailWord_921270
  simp only [CollatzResearch.WordTrace]
  refine ⟨2100092335775225327162579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22400984914935736823067509 2100092335775225327162579)
  ·
    refine ⟨3150138503662837990743869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2100092335775225327162579 3150138503662837990743869)
    ·
      refine ⟨1181301938873564246528951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3150138503662837990743869 1181301938873564246528951)
      ·
        refine ⟨1771952908310346369793427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1181301938873564246528951 1771952908310346369793427)
        ·
          refine ⟨2657929362465519554690141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1771952908310346369793427 2657929362465519554690141)
          ·
            refine ⟨996723510924569833008803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2657929362465519554690141 996723510924569833008803)
            ·
              refine ⟨1495085266386854749513205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 996723510924569833008803 1495085266386854749513205)
              ·
                refine ⟨140164243723767632766863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1495085266386854749513205 140164243723767632766863)
                ·
                  rfl

theorem cell20_921270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 1, 5].length) (baseStart_921270 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_921270 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_921270 prefixEnd_921270 := by exact prefixLift 921270
  have htrace : WordTrace (prefixWord ++ tailWord_921270) baseStart_921270 baseEnd_921270 := by
    simpa [prefixWord, tailWord_921270, baseEnd_921270] using wordTrace_append hprefix tailTrace_921270
  have hstable : (prefixWord ++ tailWord_921270).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921270).length < 2 ^ (prefixWord ++ tailWord_921270).sum := by decide
  have hdescent : baseEnd_921270 < baseStart_921270 := by decide
  rcases family_descends (prefixWord ++ tailWord_921270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921274 : List Nat := [3, 1, 1, 1, 2, 6, 1, 5]
def baseStart_921274 : Nat := 118140960795 + 921274 * 2 ^ 59
def prefixEnd_921274 : Nat := 4983230072969 + 3 ^ 40 * 921274 * 2
def baseEnd_921274 : Nat := 140164852293432220722413

theorem tailTrace_921274 : CollatzResearch.WordTrace tailWord_921274 prefixEnd_921274 140164852293432220722413 := by
  unfold tailWord_921274
  simp only [CollatzResearch.WordTrace]
  refine ⟨8400405816097278479436719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22401082176259409278497917 8400405816097278479436719)
  ·
    refine ⟨12600608724145917719155079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8400405816097278479436719 12600608724145917719155079)
    ·
      refine ⟨18900913086218876578732619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12600608724145917719155079 18900913086218876578732619)
      ·
        refine ⟨28351369629328314868098929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18900913086218876578732619 28351369629328314868098929)
        ·
          refine ⟨21263527221996236151074197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28351369629328314868098929 21263527221996236151074197)
          ·
            refine ⟨996727838531073569581603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 21263527221996236151074197 996727838531073569581603)
            ·
              refine ⟨1495091757796610354372405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 996727838531073569581603 1495091757796610354372405)
              ·
                refine ⟨140164852293432220722413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1495091757796610354372405 140164852293432220722413)
                ·
                  rfl

theorem cell20_921274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 1, 5].length) (baseStart_921274 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_921274 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_921274 prefixEnd_921274 := by exact prefixLift 921274
  have htrace : WordTrace (prefixWord ++ tailWord_921274) baseStart_921274 baseEnd_921274 := by
    simpa [prefixWord, tailWord_921274, baseEnd_921274] using wordTrace_append hprefix tailTrace_921274
  have hstable : (prefixWord ++ tailWord_921274).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921274).length < 2 ^ (prefixWord ++ tailWord_921274).sum := by decide
  have hdescent : baseEnd_921274 < baseStart_921274 := by decide
  rcases family_descends (prefixWord ++ tailWord_921274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921288 : List Nat := [2, 1, 3, 1, 2, 2, 3, 2, 4]
def baseStart_921288 : Nat := 118140960795 + 921288 * 2 ^ 59
def prefixEnd_921288 : Nat := 4983230072969 + 3 ^ 40 * 921288 * 2
def baseEnd_921288 : Nat := 420500946861774835700515

theorem tailTrace_921288 : CollatzResearch.WordTrace tailWord_921288 prefixEnd_921288 420500946861774835700515 := by
  unfold tailWord_921288
  simp only [CollatzResearch.WordTrace]
  refine ⟨16801066943169197154378259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22401422590892262872504345 16801066943169197154378259)
  ·
    refine ⟨25201600414753795731567389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16801066943169197154378259 25201600414753795731567389)
    ·
      refine ⟨9450600155532673399337771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25201600414753795731567389 9450600155532673399337771)
      ·
        refine ⟨14175900233299010099006657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9450600155532673399337771 14175900233299010099006657)
        ·
          refine ⟨10631925174974257574254993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14175900233299010099006657 10631925174974257574254993)
          ·
            refine ⟨7973943881230693180691245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10631925174974257574254993 7973943881230693180691245)
            ·
              refine ⟨2990228955461509942759217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7973943881230693180691245 2990228955461509942759217)
              ·
                refine ⟨2242671716596132457069413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2990228955461509942759217 2242671716596132457069413)
                ·
                  refine ⟨420500946861774835700515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2242671716596132457069413 420500946861774835700515)
                  ·
                    rfl

theorem cell20_921288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 2, 4].length) (baseStart_921288 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_921288 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_921288 prefixEnd_921288 := by exact prefixLift 921288
  have htrace : WordTrace (prefixWord ++ tailWord_921288) baseStart_921288 baseEnd_921288 := by
    simpa [prefixWord, tailWord_921288, baseEnd_921288] using wordTrace_append hprefix tailTrace_921288
  have hstable : (prefixWord ++ tailWord_921288).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921288).length < 2 ^ (prefixWord ++ tailWord_921288).sum := by decide
  have hdescent : baseEnd_921288 < baseStart_921288 := by decide
  rcases family_descends (prefixWord ++ tailWord_921288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921305 : List Nat := [1, 2, 1, 2, 3, 3, 1, 5, 2]
def baseStart_921305 : Nat := 118140960795 + 921305 * 2 ^ 59
def prefixEnd_921305 : Nat := 4983230072969 + 3 ^ 40 * 921305 * 2
def baseEnd_921305 : Nat := 420508706124998332133779

theorem tailTrace_921305 : CollatzResearch.WordTrace tailWord_921305 prefixEnd_921305 420508706124998332133779 := by
  unfold tailWord_921305
  simp only [CollatzResearch.WordTrace]
  refine ⟨33602753927276806212125369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22401835951517870808083579 33602753927276806212125369)
  ·
    refine ⟨25202065445457604659094027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33602753927276806212125369 25202065445457604659094027)
    ·
      refine ⟨37803098168186406988641041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25202065445457604659094027 37803098168186406988641041)
      ·
        refine ⟨28352323626139805241480781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37803098168186406988641041 28352323626139805241480781)
        ·
          refine ⟨10632121359802426965555293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28352323626139805241480781 10632121359802426965555293)
          ·
            refine ⟨3987045509925910112083235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10632121359802426965555293 3987045509925910112083235)
            ·
              refine ⟨5980568264888865168124853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3987045509925910112083235 5980568264888865168124853)
              ·
                refine ⟨560678274833331109511705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5980568264888865168124853 560678274833331109511705)
                ·
                  refine ⟨420508706124998332133779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 560678274833331109511705 420508706124998332133779)
                  ·
                    rfl

theorem cell20_921305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 5, 2].length) (baseStart_921305 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_921305 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_921305 prefixEnd_921305 := by exact prefixLift 921305
  have htrace : WordTrace (prefixWord ++ tailWord_921305) baseStart_921305 baseEnd_921305 := by
    simpa [prefixWord, tailWord_921305, baseEnd_921305] using wordTrace_append hprefix tailTrace_921305
  have hstable : (prefixWord ++ tailWord_921305).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921305).length < 2 ^ (prefixWord ++ tailWord_921305).sum := by decide
  have hdescent : baseEnd_921305 < baseStart_921305 := by decide
  rcases family_descends (prefixWord ++ tailWord_921305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921315 : List Nat := [1, 1, 1, 7, 2, 2, 1, 2, 3]
def baseStart_921315 : Nat := 118140960795 + 921315 * 2 ^ 59
def prefixEnd_921315 : Nat := 4983230072969 + 3 ^ 40 * 921315 * 2
def baseEnd_921315 : Nat := 420513270397482741800405

theorem tailTrace_921315 : CollatzResearch.WordTrace tailWord_921315 prefixEnd_921315 420513270397482741800405 := by
  unfold tailWord_921315
  simp only [CollatzResearch.WordTrace]
  refine ⟨33603118657240577919989399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22402079104827051946659599 33603118657240577919989399)
  ·
    refine ⟨50404677985860866879984099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33603118657240577919989399 50404677985860866879984099)
    ·
      refine ⟨75607016978791300319976149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50404677985860866879984099 75607016978791300319976149)
      ·
        refine ⟨1772039460440421101249441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 75607016978791300319976149 1772039460440421101249441)
        ·
          refine ⟨1329029595330315825937081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1772039460440421101249441 1329029595330315825937081)
          ·
            refine ⟨996772196497736869452811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1329029595330315825937081 996772196497736869452811)
            ·
              refine ⟨1495158294746605304179217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 996772196497736869452811 1495158294746605304179217)
              ·
                refine ⟨1121368721059953978134413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1495158294746605304179217 1121368721059953978134413)
                ·
                  refine ⟨420513270397482741800405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1121368721059953978134413 420513270397482741800405)
                  ·
                    rfl

theorem cell20_921315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 1, 2, 3].length) (baseStart_921315 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_921315 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_921315 prefixEnd_921315 := by exact prefixLift 921315
  have htrace : WordTrace (prefixWord ++ tailWord_921315) baseStart_921315 baseEnd_921315 := by
    simpa [prefixWord, tailWord_921315, baseEnd_921315] using wordTrace_append hprefix tailTrace_921315
  have hstable : (prefixWord ++ tailWord_921315).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921315).length < 2 ^ (prefixWord ++ tailWord_921315).sum := by decide
  have hdescent : baseEnd_921315 < baseStart_921315 := by decide
  rcases family_descends (prefixWord ++ tailWord_921315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921381 : List Nat := [1, 3, 1, 2, 3, 4, 1, 1, 4]
def baseStart_921381 : Nat := 118140960795 + 921381 * 2 ^ 59
def prefixEnd_921381 : Nat := 4983230072969 + 3 ^ 40 * 921381 * 2
def baseEnd_921381 : Nat := 420543394595879845600135

theorem tailTrace_921381 : CollatzResearch.WordTrace tailWord_921381 prefixEnd_921381 420543394595879845600135 := by
  unfold tailWord_921381
  simp only [CollatzResearch.WordTrace]
  refine ⟨33605525875001471191891997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22403683916667647461261331 33605525875001471191891997)
  ·
    refine ⟨12602072203125551696959499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33605525875001471191891997 12602072203125551696959499)
    ·
      refine ⟨18903108304688327545439249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12602072203125551696959499 18903108304688327545439249)
      ·
        refine ⟨14177331228516245659079437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18903108304688327545439249 14177331228516245659079437)
        ·
          refine ⟨5316499210693592122154789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14177331228516245659079437 5316499210693592122154789)
          ·
            refine ⟨996843602005048522904023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5316499210693592122154789 996843602005048522904023)
            ·
              refine ⟨1495265403007572784356035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 996843602005048522904023 1495265403007572784356035)
              ·
                refine ⟨2242898104511359176534053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1495265403007572784356035 2242898104511359176534053)
                ·
                  refine ⟨420543394595879845600135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2242898104511359176534053 420543394595879845600135)
                  ·
                    rfl

theorem cell20_921381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 1, 1, 4].length) (baseStart_921381 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_921381 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_921381 prefixEnd_921381 := by exact prefixLift 921381
  have htrace : WordTrace (prefixWord ++ tailWord_921381) baseStart_921381 baseEnd_921381 := by
    simpa [prefixWord, tailWord_921381, baseEnd_921381] using wordTrace_append hprefix tailTrace_921381
  have hstable : (prefixWord ++ tailWord_921381).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921381).length < 2 ^ (prefixWord ++ tailWord_921381).sum := by decide
  have hdescent : baseEnd_921381 < baseStart_921381 := by decide
  rcases family_descends (prefixWord ++ tailWord_921381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921433 : List Nat := [1, 2, 1, 2, 2, 3, 4, 2, 3]
def baseStart_921433 : Nat := 118140960795 + 921433 * 2 ^ 59
def prefixEnd_921433 : Nat := 4983230072969 + 3 ^ 40 * 921433 * 2
def baseEnd_921433 : Nat := 420567128812798775866589

theorem tailTrace_921433 : CollatzResearch.WordTrace tailWord_921433 prefixEnd_921433 420567128812798775866589 := by
  unfold tailWord_921433
  simp only [CollatzResearch.WordTrace]
  refine ⟨33607422470813084072784953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22404948313875389381856635 33607422470813084072784953)
  ·
    refine ⟨25205566853109813054588715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33607422470813084072784953 25205566853109813054588715)
    ·
      refine ⟨37808350279664719581883073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25205566853109813054588715 37808350279664719581883073)
      ·
        refine ⟨28356262709748539686412305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37808350279664719581883073 28356262709748539686412305)
        ·
          refine ⟨21267197032311404764809229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28356262709748539686412305 21267197032311404764809229)
          ·
            refine ⟨7975198887116776786803461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21267197032311404764809229 7975198887116776786803461)
            ·
              refine ⟨1495349791334395647525649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7975198887116776786803461 1495349791334395647525649)
              ·
                refine ⟨1121512343500796735644237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1495349791334395647525649 1121512343500796735644237)
                ·
                  refine ⟨420567128812798775866589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1121512343500796735644237 420567128812798775866589)
                  ·
                    rfl

theorem cell20_921433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 4, 2, 3].length) (baseStart_921433 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_921433 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_921433 prefixEnd_921433 := by exact prefixLift 921433
  have htrace : WordTrace (prefixWord ++ tailWord_921433) baseStart_921433 baseEnd_921433 := by
    simpa [prefixWord, tailWord_921433, baseEnd_921433] using wordTrace_append hprefix tailTrace_921433
  have hstable : (prefixWord ++ tailWord_921433).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921433).length < 2 ^ (prefixWord ++ tailWord_921433).sum := by decide
  have hdescent : baseEnd_921433 < baseStart_921433 := by decide
  rcases family_descends (prefixWord ++ tailWord_921433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921443 : List Nat := [1, 1, 1, 5, 5, 1, 1, 5]
def baseStart_921443 : Nat := 118140960795 + 921443 * 2 ^ 59
def prefixEnd_921443 : Nat := 4983230072969 + 3 ^ 40 * 921443 * 2
def baseEnd_921443 : Nat := 140190564361761061844405

theorem tailTrace_921443 : CollatzResearch.WordTrace tailWord_921443 prefixEnd_921443 140190564361761061844405 := by
  unfold tailWord_921443
  simp only [CollatzResearch.WordTrace]
  refine ⟨33607787200776855780648983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22405191467184570520432655 33607787200776855780648983)
  ·
    refine ⟨50411680801165283670973475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33607787200776855780648983 50411680801165283670973475)
    ·
      refine ⟨75617521201747925506460213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50411680801165283670973475 75617521201747925506460213)
      ·
        refine ⟨7089142612663868016230645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 75617521201747925506460213 7089142612663868016230645)
        ·
          refine ⟨664607119937237626521623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7089142612663868016230645 664607119937237626521623)
          ·
            refine ⟨996910679905856439782435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 664607119937237626521623 996910679905856439782435)
            ·
              refine ⟨1495366019858784659673653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 996910679905856439782435 1495366019858784659673653)
              ·
                refine ⟨140190564361761061844405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1495366019858784659673653 140190564361761061844405)
                ·
                  rfl

theorem cell20_921443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 1, 5].length) (baseStart_921443 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_921443 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_921443 prefixEnd_921443 := by exact prefixLift 921443
  have htrace : WordTrace (prefixWord ++ tailWord_921443) baseStart_921443 baseEnd_921443 := by
    simpa [prefixWord, tailWord_921443, baseEnd_921443] using wordTrace_append hprefix tailTrace_921443
  have hstable : (prefixWord ++ tailWord_921443).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921443).length < 2 ^ (prefixWord ++ tailWord_921443).sum := by decide
  have hdescent : baseEnd_921443 < baseStart_921443 := by decide
  rcases family_descends (prefixWord ++ tailWord_921443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921495 : List Nat := [1, 1, 3, 3, 1, 3, 2, 4, 2]
def baseStart_921495 : Nat := 118140960795 + 921495 * 2 ^ 59
def prefixEnd_921495 : Nat := 4983230072969 + 3 ^ 40 * 921495 * 2
def baseEnd_921495 : Nat := 420595427302202115799669

theorem tailTrace_921495 : CollatzResearch.WordTrace tailWord_921495 prefixEnd_921495 420595427302202115799669 := by
  unfold tailWord_921495
  simp only [CollatzResearch.WordTrace]
  refine ⟨33609683796588468661541939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22406455864392312441027959 33609683796588468661541939)
  ·
    refine ⟨50414525694882702992312909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33609683796588468661541939 50414525694882702992312909)
    ·
      refine ⟨18905447135581013622117341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50414525694882702992312909 18905447135581013622117341)
      ·
        refine ⟨7089542675842880108294003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18905447135581013622117341 7089542675842880108294003)
        ·
          refine ⟨10634314013764320162441005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7089542675842880108294003 10634314013764320162441005)
          ·
            refine ⟨3987867755161620060915377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10634314013764320162441005 3987867755161620060915377)
            ·
              refine ⟨2990900816371215045686533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3987867755161620060915377 2990900816371215045686533)
              ·
                refine ⟨560793903069602821066225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2990900816371215045686533 560793903069602821066225)
                ·
                  refine ⟨420595427302202115799669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 560793903069602821066225 420595427302202115799669)
                  ·
                    rfl

theorem cell20_921495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 4, 2].length) (baseStart_921495 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_921495 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_921495 prefixEnd_921495 := by exact prefixLift 921495
  have htrace : WordTrace (prefixWord ++ tailWord_921495) baseStart_921495 baseEnd_921495 := by
    simpa [prefixWord, tailWord_921495, baseEnd_921495] using wordTrace_append hprefix tailTrace_921495
  have hstable : (prefixWord ++ tailWord_921495).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921495).length < 2 ^ (prefixWord ++ tailWord_921495).sum := by decide
  have hdescent : baseEnd_921495 < baseStart_921495 := by decide
  rcases family_descends (prefixWord ++ tailWord_921495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921505 : List Nat := [1, 2, 3, 4, 2, 1, 3, 1, 3]
def baseStart_921505 : Nat := 118140960795 + 921505 * 2 ^ 59
def prefixEnd_921505 : Nat := 4983230072969 + 3 ^ 40 * 921505 * 2
def baseEnd_921505 : Nat := 420599991574686525466295

theorem tailTrace_921505 : CollatzResearch.WordTrace tailWord_921505 prefixEnd_921505 420599991574686525466295 := by
  unfold tailWord_921505
  simp only [CollatzResearch.WordTrace]
  refine ⟨33610048526552240369405969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22406699017701493579603979 33610048526552240369405969)
  ·
    refine ⟨25207536394914180277054477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33610048526552240369405969 25207536394914180277054477)
    ·
      refine ⟨9452826148092817603895429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25207536394914180277054477 9452826148092817603895429)
      ·
        refine ⟨1772404902767403300730393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9452826148092817603895429 1772404902767403300730393)
        ·
          refine ⟨1329303677075552475547795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1772404902767403300730393 1329303677075552475547795)
          ·
            refine ⟨1993955515613328713321693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1329303677075552475547795 1993955515613328713321693)
            ·
              refine ⟨747733318354998267495635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1993955515613328713321693 747733318354998267495635)
              ·
                refine ⟨1121599977532497401243453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 747733318354998267495635 1121599977532497401243453)
                ·
                  refine ⟨420599991574686525466295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1121599977532497401243453 420599991574686525466295)
                  ·
                    rfl

theorem cell20_921505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 3, 1, 3].length) (baseStart_921505 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_921505 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_921505 prefixEnd_921505 := by exact prefixLift 921505
  have htrace : WordTrace (prefixWord ++ tailWord_921505) baseStart_921505 baseEnd_921505 := by
    simpa [prefixWord, tailWord_921505, baseEnd_921505] using wordTrace_append hprefix tailTrace_921505
  have hstable : (prefixWord ++ tailWord_921505).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921505).length < 2 ^ (prefixWord ++ tailWord_921505).sum := by decide
  have hdescent : baseEnd_921505 < baseStart_921505 := by decide
  rcases family_descends (prefixWord ++ tailWord_921505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921550 : List Nat := [4, 1, 1, 1, 2, 2, 5, 2, 2]
def baseStart_921550 : Nat := 118140960795 + 921550 * 2 ^ 59
def prefixEnd_921550 : Nat := 4983230072969 + 3 ^ 40 * 921550 * 2
def baseEnd_921550 : Nat := 420620530800866368966111

theorem tailTrace_921550 : CollatzResearch.WordTrace tailWord_921550 prefixEnd_921550 420620530800866368966111 := by
  unfold tailWord_921550
  simp only [CollatzResearch.WordTrace]
  refine ⟨4201461226423651631849263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22407793207592808703196069 4201461226423651631849263)
  ·
    refine ⟨6302191839635477447773895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4201461226423651631849263 6302191839635477447773895)
    ·
      refine ⟨9453287759453216171660843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6302191839635477447773895 9453287759453216171660843)
      ·
        refine ⟨14179931639179824257491265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9453287759453216171660843 14179931639179824257491265)
        ·
          refine ⟨10634948729384868193118449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14179931639179824257491265 10634948729384868193118449)
          ·
            refine ⟨7976211547038651144838837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10634948729384868193118449 7976211547038651144838837)
            ·
              refine ⟨747769832534873544828641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7976211547038651144838837 747769832534873544828641)
              ·
                refine ⟨560827374401155158621481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 747769832534873544828641 560827374401155158621481)
                ·
                  refine ⟨420620530800866368966111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 560827374401155158621481 420620530800866368966111)
                  ·
                    rfl

theorem cell20_921550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 5, 2, 2].length) (baseStart_921550 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_921550 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_921550 prefixEnd_921550 := by exact prefixLift 921550
  have htrace : WordTrace (prefixWord ++ tailWord_921550) baseStart_921550 baseEnd_921550 := by
    simpa [prefixWord, tailWord_921550, baseEnd_921550] using wordTrace_append hprefix tailTrace_921550
  have hstable : (prefixWord ++ tailWord_921550).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921550).length < 2 ^ (prefixWord ++ tailWord_921550).sum := by decide
  have hdescent : baseEnd_921550 < baseStart_921550 := by decide
  rcases family_descends (prefixWord ++ tailWord_921550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921657 : List Nat := [1, 2, 1, 5, 4, 1, 1, 2, 3]
def baseStart_921657 : Nat := 118140960795 + 921657 * 2 ^ 59
def prefixEnd_921657 : Nat := 4983230072969 + 3 ^ 40 * 921657 * 2
def baseEnd_921657 : Nat := 420669368516449552399007

theorem tailTrace_921657 : CollatzResearch.WordTrace tailWord_921657 prefixEnd_921657 420669368516449552399007 := by
  unfold tailWord_921657
  simp only [CollatzResearch.WordTrace]
  refine ⟨33615592422001570328939225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22410394948001046885959483 33615592422001570328939225)
  ·
    refine ⟨25211694316501177746704419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33615592422001570328939225 25211694316501177746704419)
    ·
      refine ⟨37817541474751766620056629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25211694316501177746704419 37817541474751766620056629)
      ·
        refine ⟨3545394513257978120630309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37817541474751766620056629 3545394513257978120630309)
        ·
          refine ⟨664761471235870897618183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3545394513257978120630309 664761471235870897618183)
          ·
            refine ⟨997142206853806346427275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 664761471235870897618183 997142206853806346427275)
            ·
              refine ⟨1495713310280709519640913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 997142206853806346427275 1495713310280709519640913)
              ·
                refine ⟨1121784982710532139730685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1495713310280709519640913 1121784982710532139730685)
                ·
                  refine ⟨420669368516449552399007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1121784982710532139730685 420669368516449552399007)
                  ·
                    rfl

theorem cell20_921657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 1, 2, 3].length) (baseStart_921657 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_921657 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_921657 prefixEnd_921657 := by exact prefixLift 921657
  have htrace : WordTrace (prefixWord ++ tailWord_921657) baseStart_921657 baseEnd_921657 := by
    simpa [prefixWord, tailWord_921657, baseEnd_921657] using wordTrace_append hprefix tailTrace_921657
  have hstable : (prefixWord ++ tailWord_921657).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921657).length < 2 ^ (prefixWord ++ tailWord_921657).sum := by decide
  have hdescent : baseEnd_921657 < baseStart_921657 := by decide
  rcases family_descends (prefixWord ++ tailWord_921657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921678 : List Nat := [4, 1, 1, 1, 1, 5, 3, 1, 3]
def baseStart_921678 : Nat := 118140960795 + 921678 * 2 ^ 59
def prefixEnd_921678 : Nat := 4983230072969 + 3 ^ 40 * 921678 * 2
def baseEnd_921678 : Nat := 420678953488666812698921

theorem tailTrace_921678 : CollatzResearch.WordTrace tailWord_921678 prefixEnd_921678 420678953488666812698921 := by
  unfold tailWord_921678
  simp only [CollatzResearch.WordTrace]
  refine ⟨4202044794365686364431711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22410905569950327276969125 4202044794365686364431711)
  ·
    refine ⟨6303067191548529546647567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4202044794365686364431711 6303067191548529546647567)
    ·
      refine ⟨9454600787322794319971351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6303067191548529546647567 9454600787322794319971351)
      ·
        refine ⟨14181901180984191479957027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9454600787322794319971351 14181901180984191479957027)
        ·
          refine ⟨21272851771476287219935541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14181901180984191479957027 21272851771476287219935541)
          ·
            refine ⟨1994329853575901926868957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21272851771476287219935541 1994329853575901926868957)
            ·
              refine ⟨747873695090963222575859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1994329853575901926868957 747873695090963222575859)
              ·
                refine ⟨1121810542636444833863789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 747873695090963222575859 1121810542636444833863789)
                ·
                  refine ⟨420678953488666812698921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1121810542636444833863789 420678953488666812698921)
                  ·
                    rfl

theorem cell20_921678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 3, 1, 3].length) (baseStart_921678 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_921678 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_921678 prefixEnd_921678 := by exact prefixLift 921678
  have htrace : WordTrace (prefixWord ++ tailWord_921678) baseStart_921678 baseEnd_921678 := by
    simpa [prefixWord, tailWord_921678, baseEnd_921678] using wordTrace_append hprefix tailTrace_921678
  have hstable : (prefixWord ++ tailWord_921678).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921678).length < 2 ^ (prefixWord ++ tailWord_921678).sum := by decide
  have hdescent : baseEnd_921678 < baseStart_921678 := by decide
  rcases family_descends (prefixWord ++ tailWord_921678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921689 : List Nat := [1, 2, 1, 2, 2, 1, 3, 4, 4]
def baseStart_921689 : Nat := 118140960795 + 921689 * 2 ^ 59
def prefixEnd_921689 : Nat := 4983230072969 + 3 ^ 40 * 921689 * 2
def baseEnd_921689 : Nat := 420683974188399663332209

theorem tailTrace_921689 : CollatzResearch.WordTrace tailWord_921689 prefixEnd_921689 420683974188399663332209 := by
  unfold tailWord_921689
  simp only [CollatzResearch.WordTrace]
  refine ⟨33616759557885639794104121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22411173038590426529402747 33616759557885639794104121)
  ·
    refine ⟨25212569668414229845578091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33616759557885639794104121 25212569668414229845578091)
    ·
      refine ⟨37818854502621344768367137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25212569668414229845578091 37818854502621344768367137)
      ·
        refine ⟨28364140876966008576275353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37818854502621344768367137 28364140876966008576275353)
        ·
          refine ⟨21273105657724506432206515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28364140876966008576275353 21273105657724506432206515)
          ·
            refine ⟨31909658486586759648309773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21273105657724506432206515 31909658486586759648309773)
            ·
              refine ⟨11966121932470034868116165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31909658486586759648309773 11966121932470034868116165)
              ·
                refine ⟨2243647862338131537771781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11966121932470034868116165 2243647862338131537771781)
                ·
                  refine ⟨420683974188399663332209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2243647862338131537771781 420683974188399663332209)
                  ·
                    rfl

theorem cell20_921689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 4, 4].length) (baseStart_921689 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_921689 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_921689 prefixEnd_921689 := by exact prefixLift 921689
  have htrace : WordTrace (prefixWord ++ tailWord_921689) baseStart_921689 baseEnd_921689 := by
    simpa [prefixWord, tailWord_921689, baseEnd_921689] using wordTrace_append hprefix tailTrace_921689
  have hstable : (prefixWord ++ tailWord_921689).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921689).length < 2 ^ (prefixWord ++ tailWord_921689).sum := by decide
  have hdescent : baseEnd_921689 < baseStart_921689 := by decide
  rcases family_descends (prefixWord ++ tailWord_921689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921692 : List Nat := [2, 2, 4, 1, 1, 2, 4, 4]
def baseStart_921692 : Nat := 118140960795 + 921692 * 2 ^ 59
def prefixEnd_921692 : Nat := 4983230072969 + 3 ^ 40 * 921692 * 2
def baseEnd_921692 : Nat := 140228447823381662077399

theorem tailTrace_921692 : CollatzResearch.WordTrace tailWord_921692 prefixEnd_921692 140228447823381662077399 := by
  unfold tailWord_921692
  simp only [CollatzResearch.WordTrace]
  refine ⟨16808434488437385653231665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22411245984583180870975553 16808434488437385653231665)
  ·
    refine ⟨12606325866328039239923749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16808434488437385653231665 12606325866328039239923749)
    ·
      refine ⟨2363686099936507357485703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12606325866328039239923749 2363686099936507357485703)
      ·
        refine ⟨3545529149904761036228555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2363686099936507357485703 3545529149904761036228555)
        ·
          refine ⟨5318293724857141554342833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3545529149904761036228555 5318293724857141554342833)
          ·
            refine ⟨3988720293642856165757125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5318293724857141554342833 3988720293642856165757125)
            ·
              refine ⟨747885055058035531079461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3988720293642856165757125 747885055058035531079461)
              ·
                refine ⟨140228447823381662077399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 747885055058035531079461 140228447823381662077399)
                ·
                  rfl

theorem cell20_921692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 4, 4].length) (baseStart_921692 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_921692 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_921692 prefixEnd_921692 := by exact prefixLift 921692
  have htrace : WordTrace (prefixWord ++ tailWord_921692) baseStart_921692 baseEnd_921692 := by
    simpa [prefixWord, tailWord_921692, baseEnd_921692] using wordTrace_append hprefix tailTrace_921692
  have hstable : (prefixWord ++ tailWord_921692).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921692).length < 2 ^ (prefixWord ++ tailWord_921692).sum := by decide
  have hdescent : baseEnd_921692 < baseStart_921692 := by decide
  rcases family_descends (prefixWord ++ tailWord_921692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921698 : List Nat := [3, 3, 2, 2, 3, 1, 1, 3, 2]
def baseStart_921698 : Nat := 118140960795 + 921698 * 2 ^ 59
def prefixEnd_921698 : Nat := 4983230072969 + 3 ^ 40 * 921698 * 2
def baseEnd_921698 : Nat := 420688082033635632032173

theorem tailTrace_921698 : CollatzResearch.WordTrace tailWord_921698 prefixEnd_921698 420688082033635632032173 := by
  unfold tailWord_921698
  simp only [CollatzResearch.WordTrace]
  refine ⟨8404271953713258582795437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22411391876568689554121165 8404271953713258582795437)
  ·
    refine ⟨3151601982642471968548289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8404271953713258582795437 3151601982642471968548289)
    ·
      refine ⟨2363701486981853976411217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3151601982642471968548289 2363701486981853976411217)
      ·
        refine ⟨1772776115236390482308413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2363701486981853976411217 1772776115236390482308413)
        ·
          refine ⟨664791043213646430865655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1772776115236390482308413 664791043213646430865655)
          ·
            refine ⟨997186564820469646298483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 664791043213646430865655 997186564820469646298483)
            ·
              refine ⟨1495779847230704469447725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 997186564820469646298483 1495779847230704469447725)
              ·
                refine ⟨560917442711514176042897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1495779847230704469447725 560917442711514176042897)
                ·
                  refine ⟨420688082033635632032173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 560917442711514176042897 420688082033635632032173)
                  ·
                    rfl

theorem cell20_921698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 1, 3, 2].length) (baseStart_921698 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_921698 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_921698 prefixEnd_921698 := by exact prefixLift 921698
  have htrace : WordTrace (prefixWord ++ tailWord_921698) baseStart_921698 baseEnd_921698 := by
    simpa [prefixWord, tailWord_921698, baseEnd_921698] using wordTrace_append hprefix tailTrace_921698
  have hstable : (prefixWord ++ tailWord_921698).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921698).length < 2 ^ (prefixWord ++ tailWord_921698).sum := by decide
  have hdescent : baseEnd_921698 < baseStart_921698 := by decide
  rcases family_descends (prefixWord ++ tailWord_921698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921720 : List Nat := [2, 1, 2, 1, 1, 1, 3, 6, 3]
def baseStart_921720 : Nat := 118140960795 + 921720 * 2 ^ 59
def prefixEnd_921720 : Nat := 4983230072969 + 3 ^ 40 * 921720 * 2
def baseEnd_921720 : Nat := 420698123433101333298749

theorem tailTrace_921720 : CollatzResearch.WordTrace tailWord_921720 prefixEnd_921720 420698123433101333298749 := by
  unfold tailWord_921720
  simp only [CollatzResearch.WordTrace]
  refine ⟨16808945110386666044241307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22411926813848888058988409 16808945110386666044241307)
  ·
    refine ⟨25213417665579999066361961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16808945110386666044241307 25213417665579999066361961)
    ·
      refine ⟨18910063249184999299771471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25213417665579999066361961 18910063249184999299771471)
      ·
        refine ⟨28365094873777498949657207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18910063249184999299771471 28365094873777498949657207)
        ·
          refine ⟨42547642310666248424485811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28365094873777498949657207 42547642310666248424485811)
          ·
            refine ⟨63821463465999372636728717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42547642310666248424485811 63821463465999372636728717)
            ·
              refine ⟨23933048799749764738773269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63821463465999372636728717 23933048799749764738773269)
              ·
                refine ⟨1121861662488270222129997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 23933048799749764738773269 1121861662488270222129997)
                ·
                  refine ⟨420698123433101333298749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1121861662488270222129997 420698123433101333298749)
                  ·
                    rfl

theorem cell20_921720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 6, 3].length) (baseStart_921720 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_921720 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_921720 prefixEnd_921720 := by exact prefixLift 921720
  have htrace : WordTrace (prefixWord ++ tailWord_921720) baseStart_921720 baseEnd_921720 := by
    simpa [prefixWord, tailWord_921720, baseEnd_921720] using wordTrace_append hprefix tailTrace_921720
  have hstable : (prefixWord ++ tailWord_921720).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921720).length < 2 ^ (prefixWord ++ tailWord_921720).sum := by decide
  have hdescent : baseEnd_921720 < baseStart_921720 := by decide
  rcases family_descends (prefixWord ++ tailWord_921720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921803 : List Nat := [1, 1, 1, 1, 3, 2, 5, 2, 4]
def baseStart_921803 : Nat := 118140960795 + 921803 * 2 ^ 59
def prefixEnd_921803 : Nat := 4983230072969 + 3 ^ 40 * 921803 * 2
def baseEnd_921803 : Nat := 420736006894721933531743

theorem tailTrace_921803 : CollatzResearch.WordTrace tailWord_921803 prefixEnd_921803 420736006894721933531743 := by
  unfold tailWord_921803
  simp only [CollatzResearch.WordTrace]
  refine ⟨33620917479472637263754063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22413944986315091509169375 33620917479472637263754063)
  ·
    refine ⟨50431376219208955895631095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33620917479472637263754063 50431376219208955895631095)
    ·
      refine ⟨75647064328813433843446643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50431376219208955895631095 75647064328813433843446643)
      ·
        refine ⟨113470596493220150765169965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75647064328813433843446643 113470596493220150765169965)
        ·
          refine ⟨42551473684957556536938737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113470596493220150765169965 42551473684957556536938737)
          ·
            refine ⟨31913605263718167402704053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42551473684957556536938737 31913605263718167402704053)
            ·
              refine ⟨2991900493473578194003505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31913605263718167402704053 2991900493473578194003505)
              ·
                refine ⟨2243925370105183645502629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2991900493473578194003505 2243925370105183645502629)
                ·
                  refine ⟨420736006894721933531743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2243925370105183645502629 420736006894721933531743)
                  ·
                    rfl

theorem cell20_921803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 2, 4].length) (baseStart_921803 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_921803 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_921803 prefixEnd_921803 := by exact prefixLift 921803
  have htrace : WordTrace (prefixWord ++ tailWord_921803) baseStart_921803 baseEnd_921803 := by
    simpa [prefixWord, tailWord_921803, baseEnd_921803] using wordTrace_append hprefix tailTrace_921803
  have hstable : (prefixWord ++ tailWord_921803).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921803).length < 2 ^ (prefixWord ++ tailWord_921803).sum := by decide
  have hdescent : baseEnd_921803 < baseStart_921803 := by decide
  rcases family_descends (prefixWord ++ tailWord_921803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921806 : List Nat := [4, 1, 1, 1, 4, 2, 3, 4]
def baseStart_921806 : Nat := 118140960795 + 921806 * 2 ^ 59
def prefixEnd_921806 : Nat := 4983230072969 + 3 ^ 40 * 921806 * 2
def baseEnd_921806 : Nat := 140245792058822418810577

theorem tailTrace_921806 : CollatzResearch.WordTrace tailWord_921806 prefixEnd_921806 140245792058822418810577 := by
  unfold tailWord_921806
  simp only [CollatzResearch.WordTrace]
  refine ⟨4202628362307721097014159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22414017932307845850742181 4202628362307721097014159)
  ·
    refine ⟨6303942543461581645521239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4202628362307721097014159 6303942543461581645521239)
    ·
      refine ⟨9455913815192372468281859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6303942543461581645521239 9455913815192372468281859)
      ·
        refine ⟨14183870722788558702422789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9455913815192372468281859 14183870722788558702422789)
        ·
          refine ⟨2659475760522854756704273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14183870722788558702422789 2659475760522854756704273)
          ·
            refine ⟨1994606820392141067528205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2659475760522854756704273 1994606820392141067528205)
            ·
              refine ⟨747977557647052900323077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1994606820392141067528205 747977557647052900323077)
              ·
                refine ⟨140245792058822418810577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 747977557647052900323077 140245792058822418810577)
                ·
                  rfl

theorem cell20_921806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 3, 4].length) (baseStart_921806 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_921806 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_921806 prefixEnd_921806 := by exact prefixLift 921806
  have htrace : WordTrace (prefixWord ++ tailWord_921806) baseStart_921806 baseEnd_921806 := by
    simpa [prefixWord, tailWord_921806, baseEnd_921806] using wordTrace_append hprefix tailTrace_921806
  have hstable : (prefixWord ++ tailWord_921806).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921806).length < 2 ^ (prefixWord ++ tailWord_921806).sum := by decide
  have hdescent : baseEnd_921806 < baseStart_921806 := by decide
  rcases family_descends (prefixWord ++ tailWord_921806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921834 : List Nat := [3, 1, 3, 1, 1, 2, 3, 1, 5]
def baseStart_921834 : Nat := 118140960795 + 921834 * 2 ^ 59
def prefixEnd_921834 : Nat := 4983230072969 + 3 ^ 40 * 921834 * 2
def baseEnd_921834 : Nat := 420750156139423603498283

theorem tailTrace_921834 : CollatzResearch.WordTrace tailWord_921834 prefixEnd_921834 420750156139423603498283 := by
  unfold tailWord_921834
  simp only [CollatzResearch.WordTrace]
  refine ⟨8405512035590082389533139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22414698761573553038755037 8405512035590082389533139)
  ·
    refine ⟨12608268053385123584299709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8405512035590082389533139 12608268053385123584299709)
    ·
      refine ⟨4728100520019421344112391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12608268053385123584299709 4728100520019421344112391)
      ·
        refine ⟨7092150780029132016168587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4728100520019421344112391 7092150780029132016168587)
        ·
          refine ⟨10638226170043698024252881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7092150780029132016168587 10638226170043698024252881)
          ·
            refine ⟨7978669627532773518189661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10638226170043698024252881 7978669627532773518189661)
            ·
              refine ⟨2992001110324790069321123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7978669627532773518189661 2992001110324790069321123)
              ·
                refine ⟨4488001665487185103981685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2992001110324790069321123 4488001665487185103981685)
                ·
                  refine ⟨420750156139423603498283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4488001665487185103981685 420750156139423603498283)
                  ·
                    rfl

theorem cell20_921834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 1, 5].length) (baseStart_921834 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_921834 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_921834 prefixEnd_921834 := by exact prefixLift 921834
  have htrace : WordTrace (prefixWord ++ tailWord_921834) baseStart_921834 baseEnd_921834 := by
    simpa [prefixWord, tailWord_921834, baseEnd_921834] using wordTrace_append hprefix tailTrace_921834
  have hstable : (prefixWord ++ tailWord_921834).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921834).length < 2 ^ (prefixWord ++ tailWord_921834).sum := by decide
  have hdescent : baseEnd_921834 < baseStart_921834 := by decide
  rcases family_descends (prefixWord ++ tailWord_921834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921837 : List Nat := [1, 5, 1, 2, 3, 1, 2, 1, 4]
def baseStart_921837 : Nat := 118140960795 + 921837 * 2 ^ 59
def prefixEnd_921837 : Nat := 4983230072969 + 3 ^ 40 * 921837 * 2
def baseEnd_921837 : Nat := 420751525421168926398271

theorem tailTrace_921837 : CollatzResearch.WordTrace tailWord_921837 prefixEnd_921837 420751525421168926398271 := by
  unfold tailWord_921837
  simp only [CollatzResearch.WordTrace]
  refine ⟨33622157561349461070491765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22414771707566307380327843 33622157561349461070491765)
  ·
    refine ⟨3152077271376511975358603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33622157561349461070491765 3152077271376511975358603)
    ·
      refine ⟨4728115907064767963037905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3152077271376511975358603 4728115907064767963037905)
      ·
        refine ⟨3546086930298575972278429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4728115907064767963037905 3546086930298575972278429)
        ·
          refine ⟨1329782598861965989604411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3546086930298575972278429 1329782598861965989604411)
          ·
            refine ⟨1994673898292948984406617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1329782598861965989604411 1994673898292948984406617)
            ·
              refine ⟨1496005423719711738304963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1994673898292948984406617 1496005423719711738304963)
              ·
                refine ⟨2244008135579567607457445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1496005423719711738304963 2244008135579567607457445)
                ·
                  refine ⟨420751525421168926398271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2244008135579567607457445 420751525421168926398271)
                  ·
                    rfl

theorem cell20_921837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 2, 1, 4].length) (baseStart_921837 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_921837 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_921837 prefixEnd_921837 := by exact prefixLift 921837
  have htrace : WordTrace (prefixWord ++ tailWord_921837) baseStart_921837 baseEnd_921837 := by
    simpa [prefixWord, tailWord_921837, baseEnd_921837] using wordTrace_append hprefix tailTrace_921837
  have hstable : (prefixWord ++ tailWord_921837).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921837).length < 2 ^ (prefixWord ++ tailWord_921837).sum := by decide
  have hdescent : baseEnd_921837 < baseStart_921837 := by decide
  rcases family_descends (prefixWord ++ tailWord_921837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921841 : List Nat := [1, 2, 2, 2, 2, 1, 3, 3, 4]
def baseStart_921841 : Nat := 118140960795 + 921841 * 2 ^ 59
def prefixEnd_921841 : Nat := 4983230072969 + 3 ^ 40 * 921841 * 2
def baseEnd_921841 : Nat := 420753351130162690264921

theorem tailTrace_921841 : CollatzResearch.WordTrace tailWord_921841 prefixEnd_921841 420753351130162690264921 := by
  unfold tailWord_921841
  simp only [CollatzResearch.WordTrace]
  refine ⟨33622303453334969753637377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22414868968889979835758251 33622303453334969753637377)
  ·
    refine ⟨25216727590001227315228033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33622303453334969753637377 25216727590001227315228033)
    ·
      refine ⟨18912545692500920486421025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25216727590001227315228033 18912545692500920486421025)
      ·
        refine ⟨14184409269375690364815769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18912545692500920486421025 14184409269375690364815769)
        ·
          refine ⟨10638306952031767773611827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14184409269375690364815769 10638306952031767773611827)
          ·
            refine ⟨15957460428047651660417741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10638306952031767773611827 15957460428047651660417741)
            ·
              refine ⟨5984047660517869372656653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15957460428047651660417741 5984047660517869372656653)
              ·
                refine ⟨2244017872694201014746245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5984047660517869372656653 2244017872694201014746245)
                ·
                  refine ⟨420753351130162690264921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2244017872694201014746245 420753351130162690264921)
                  ·
                    rfl

theorem cell20_921841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 3, 4].length) (baseStart_921841 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_921841 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_921841 prefixEnd_921841 := by exact prefixLift 921841
  have htrace : WordTrace (prefixWord ++ tailWord_921841) baseStart_921841 baseEnd_921841 := by
    simpa [prefixWord, tailWord_921841, baseEnd_921841] using wordTrace_append hprefix tailTrace_921841
  have hstable : (prefixWord ++ tailWord_921841).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921841).length < 2 ^ (prefixWord ++ tailWord_921841).sum := by decide
  have hdescent : baseEnd_921841 < baseStart_921841 := by decide
  rcases family_descends (prefixWord ++ tailWord_921841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921865 : List Nat := [1, 2, 1, 1, 3, 4, 4, 4]
def baseStart_921865 : Nat := 118140960795 + 921865 * 2 ^ 59
def prefixEnd_921865 : Nat := 4983230072969 + 3 ^ 40 * 921865 * 2
def baseEnd_921865 : Nat := 140254768461375091154941

theorem tailTrace_921865 : CollatzResearch.WordTrace tailWord_921865 prefixEnd_921865 140254768461375091154941 := by
  unfold tailWord_921865
  simp only [CollatzResearch.WordTrace]
  refine ⟨33623178805248021852511049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22415452536832014568340699 33623178805248021852511049)
  ·
    refine ⟨25217384103936016389383287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33623178805248021852511049 25217384103936016389383287)
    ·
      refine ⟨37826076155904024584074931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25217384103936016389383287 37826076155904024584074931)
      ·
        refine ⟨56739114233856036876112397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37826076155904024584074931 56739114233856036876112397)
        ·
          refine ⟨21277167837696013828542149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56739114233856036876112397 21277167837696013828542149)
          ·
            refine ⟨3989468969568002592851653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21277167837696013828542149 3989468969568002592851653)
            ·
              refine ⟨748025431794000486159685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3989468969568002592851653 748025431794000486159685)
              ·
                refine ⟨140254768461375091154941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 748025431794000486159685 140254768461375091154941)
                ·
                  rfl

theorem cell20_921865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 4, 4].length) (baseStart_921865 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_921865 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_921865 prefixEnd_921865 := by exact prefixLift 921865
  have htrace : WordTrace (prefixWord ++ tailWord_921865) baseStart_921865 baseEnd_921865 := by
    simpa [prefixWord, tailWord_921865, baseEnd_921865] using wordTrace_append hprefix tailTrace_921865
  have hstable : (prefixWord ++ tailWord_921865).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921865).length < 2 ^ (prefixWord ++ tailWord_921865).sum := by decide
  have hdescent : baseEnd_921865 < baseStart_921865 := by decide
  rcases family_descends (prefixWord ++ tailWord_921865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921882 : List Nat := [3, 1, 1, 3, 5, 1, 6]
def baseStart_921882 : Nat := 118140960795 + 921882 * 2 ^ 59
def prefixEnd_921882 : Nat := 4983230072969 + 3 ^ 40 * 921882 * 2
def baseEnd_921882 : Nat := 46752451627483196655343

theorem tailTrace_921882 : CollatzResearch.WordTrace tailWord_921882 prefixEnd_921882 46752451627483196655343 := by
  unfold tailWord_921882
  simp only [CollatzResearch.WordTrace]
  refine ⟨8405949711546608438969975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22415865897457622503919933 8405949711546608438969975)
  ·
    refine ⟨12608924567319912658454963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8405949711546608438969975 12608924567319912658454963)
    ·
      refine ⟨18913386850979868987682445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12608924567319912658454963 18913386850979868987682445)
      ·
        refine ⟨7092520069117450870380917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18913386850979868987682445 7092520069117450870380917)
        ·
          refine ⟨664923756479761019098211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7092520069117450870380917 664923756479761019098211)
          ·
            refine ⟨997385634719641528647317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 664923756479761019098211 997385634719641528647317)
            ·
              refine ⟨46752451627483196655343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 997385634719641528647317 46752451627483196655343)
              ·
                rfl

theorem cell20_921882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 6].length) (baseStart_921882 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_921882 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_921882 prefixEnd_921882 := by exact prefixLift 921882
  have htrace : WordTrace (prefixWord ++ tailWord_921882) baseStart_921882 baseEnd_921882 := by
    simpa [prefixWord, tailWord_921882, baseEnd_921882] using wordTrace_append hprefix tailTrace_921882
  have hstable : (prefixWord ++ tailWord_921882).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921882).length < 2 ^ (prefixWord ++ tailWord_921882).sum := by decide
  have hdescent : baseEnd_921882 < baseStart_921882 := by decide
  rcases family_descends (prefixWord ++ tailWord_921882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921892 : List Nat := [2, 3, 1, 3, 1, 3, 3, 2, 2]
def baseStart_921892 : Nat := 118140960795 + 921892 * 2 ^ 59
def prefixEnd_921892 : Nat := 4983230072969 + 3 ^ 40 * 921892 * 2
def baseEnd_921892 : Nat := 420776628919833179564713

theorem tailTrace_921892 : CollatzResearch.WordTrace tailWord_921892 prefixEnd_921892 420776628919833179564713 := by
  unfold tailWord_921892
  simp only [CollatzResearch.WordTrace]
  refine ⟨16812081788075102731871965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22416109050766803642495953 16812081788075102731871965)
  ·
    refine ⟨6304530670528163524451987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16812081788075102731871965 6304530670528163524451987)
    ·
      refine ⟨9456796005792245286677981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6304530670528163524451987 9456796005792245286677981)
      ·
        refine ⟨3546298502172091982504243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9456796005792245286677981 3546298502172091982504243)
        ·
          refine ⟨5319447753258137973756365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3546298502172091982504243 5319447753258137973756365)
          ·
            refine ⟨1994792907471801740158637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5319447753258137973756365 1994792907471801740158637)
            ·
              refine ⟨748047340301925652559489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1994792907471801740158637 748047340301925652559489)
              ·
                refine ⟨561035505226444239419617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 748047340301925652559489 561035505226444239419617)
                ·
                  refine ⟨420776628919833179564713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 561035505226444239419617 420776628919833179564713)
                  ·
                    rfl

theorem cell20_921892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 3, 2, 2].length) (baseStart_921892 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_921892 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_921892 prefixEnd_921892 := by exact prefixLift 921892
  have htrace : WordTrace (prefixWord ++ tailWord_921892) baseStart_921892 baseEnd_921892 := by
    simpa [prefixWord, tailWord_921892, baseEnd_921892] using wordTrace_append hprefix tailTrace_921892
  have hstable : (prefixWord ++ tailWord_921892).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921892).length < 2 ^ (prefixWord ++ tailWord_921892).sum := by decide
  have hdescent : baseEnd_921892 < baseStart_921892 := by decide
  rcases family_descends (prefixWord ++ tailWord_921892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921902 : List Nat := [4, 1, 3, 3, 1, 2, 2, 1, 3]
def baseStart_921902 : Nat := 118140960795 + 921902 * 2 ^ 59
def prefixEnd_921902 : Nat := 4983230072969 + 3 ^ 40 * 921902 * 2
def baseEnd_921902 : Nat := 420781193192317589231339

theorem tailTrace_921902 : CollatzResearch.WordTrace tailWord_921902 prefixEnd_921902 420781193192317589231339 := by
  unfold tailWord_921902
  simp only [CollatzResearch.WordTrace]
  refine ⟨4203066038264247146450995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22416352204075984781071973 4203066038264247146450995)
  ·
    refine ⟨6304599057396370719676493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4203066038264247146450995 6304599057396370719676493)
    ·
      refine ⟨2364224646523639019878685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6304599057396370719676493 2364224646523639019878685)
      ·
        refine ⟨886584242446364632454507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2364224646523639019878685 886584242446364632454507)
        ·
          refine ⟨1329876363669546948681761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 886584242446364632454507 1329876363669546948681761)
          ·
            refine ⟨997407272752160211511321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1329876363669546948681761 997407272752160211511321)
            ·
              refine ⟨748055454564120158633491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 997407272752160211511321 748055454564120158633491)
              ·
                refine ⟨1122083181846180237950237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 748055454564120158633491 1122083181846180237950237)
                ·
                  refine ⟨420781193192317589231339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1122083181846180237950237 420781193192317589231339)
                  ·
                    rfl

theorem cell20_921902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 2, 1, 3].length) (baseStart_921902 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_921902 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_921902 prefixEnd_921902 := by exact prefixLift 921902
  have htrace : WordTrace (prefixWord ++ tailWord_921902) baseStart_921902 baseEnd_921902 := by
    simpa [prefixWord, tailWord_921902, baseEnd_921902] using wordTrace_append hprefix tailTrace_921902
  have hstable : (prefixWord ++ tailWord_921902).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921902).length < 2 ^ (prefixWord ++ tailWord_921902).sum := by decide
  have hdescent : baseEnd_921902 < baseStart_921902 := by decide
  rcases family_descends (prefixWord ++ tailWord_921902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921931 : List Nat := [1, 1, 1, 1, 3, 1, 1, 6, 5]
def baseStart_921931 : Nat := 118140960795 + 921931 * 2 ^ 59
def prefixEnd_921931 : Nat := 4983230072969 + 3 ^ 40 * 921931 * 2
def baseEnd_921931 : Nat := 420794429582522377264553

theorem tailTrace_921931 : CollatzResearch.WordTrace tailWord_921931 prefixEnd_921931 420794429582522377264553 := by
  unfold tailWord_921931
  simp only [CollatzResearch.WordTrace]
  refine ⟨33625586023008915124413647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22417057348672610082942431 33625586023008915124413647)
  ·
    refine ⟨50438379034513372686620471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33625586023008915124413647 50438379034513372686620471)
    ·
      refine ⟨75657568551770059029930707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50438379034513372686620471 75657568551770059029930707)
      ·
        refine ⟨113486352827655088544896061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75657568551770059029930707 113486352827655088544896061)
        ·
          refine ⟨42557382310370658204336023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113486352827655088544896061 42557382310370658204336023)
          ·
            refine ⟨63836073465555987306504035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42557382310370658204336023 63836073465555987306504035)
            ·
              refine ⟨95754110198333980959756053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63836073465555987306504035 95754110198333980959756053)
              ·
                refine ⟨4488473915546905357488565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 95754110198333980959756053 4488473915546905357488565)
                ·
                  refine ⟨420794429582522377264553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4488473915546905357488565 420794429582522377264553)
                  ·
                    rfl

theorem cell20_921931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 6, 5].length) (baseStart_921931 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_921931 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_921931 prefixEnd_921931 := by exact prefixLift 921931
  have htrace : WordTrace (prefixWord ++ tailWord_921931) baseStart_921931 baseEnd_921931 := by
    simpa [prefixWord, tailWord_921931, baseEnd_921931] using wordTrace_append hprefix tailTrace_921931
  have hstable : (prefixWord ++ tailWord_921931).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921931).length < 2 ^ (prefixWord ++ tailWord_921931).sum := by decide
  have hdescent : baseEnd_921931 < baseStart_921931 := by decide
  rcases family_descends (prefixWord ++ tailWord_921931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921941 : List Nat := [1, 3, 2, 2, 5, 7]
def baseStart_921941 : Nat := 118140960795 + 921941 * 2 ^ 59
def prefixEnd_921941 : Nat := 4983230072969 + 3 ^ 40 * 921941 * 2
def baseEnd_921941 : Nat := 15585147920555806923377

theorem tailTrace_921941 : CollatzResearch.WordTrace tailWord_921941 prefixEnd_921941 15585147920555806923377 := by
  unfold tailWord_921941
  simp only [CollatzResearch.WordTrace]
  refine ⟨33625950752972686832277677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22417300501981791221518451 33625950752972686832277677)
  ·
    refine ⟨12609731532364757562104129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33625950752972686832277677 12609731532364757562104129)
    ·
      refine ⟨9457298649273568171578097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12609731532364757562104129 9457298649273568171578097)
      ·
        refine ⟨7092973986955176128683573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9457298649273568171578097 7092973986955176128683573)
        ·
          refine ⟨664966311277047762064085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7092973986955176128683573 664966311277047762064085)
          ·
            refine ⟨15585147920555806923377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 664966311277047762064085 15585147920555806923377)
            ·
              rfl

theorem cell20_921941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 7].length) (baseStart_921941 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_921941 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_921941 prefixEnd_921941 := by exact prefixLift 921941
  have htrace : WordTrace (prefixWord ++ tailWord_921941) baseStart_921941 baseEnd_921941 := by
    simpa [prefixWord, tailWord_921941, baseEnd_921941] using wordTrace_append hprefix tailTrace_921941
  have hstable : (prefixWord ++ tailWord_921941).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921941).length < 2 ^ (prefixWord ++ tailWord_921941).sum := by decide
  have hdescent : baseEnd_921941 < baseStart_921941 := by decide
  rcases family_descends (prefixWord ++ tailWord_921941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921950 : List Nat := [4, 4, 2, 1, 2, 1, 1, 5]
def baseStart_921950 : Nat := 118140960795 + 921950 * 2 ^ 59
def prefixEnd_921950 : Nat := 4983230072969 + 3 ^ 40 * 921950 * 2
def baseEnd_921950 : Nat := 140267700566747585210381

theorem tailTrace_921950 : CollatzResearch.WordTrace tailWord_921950 prefixEnd_921950 140267700566747585210381 := by
  unfold tailWord_921950
  simp only [CollatzResearch.WordTrace]
  refine ⟨4203284876242510171169413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22417519339960054246236869 4203284876242510171169413)
  ·
    refine ⟨788115914295470657094265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4203284876242510171169413 788115914295470657094265)
    ·
      refine ⟨591086935721602992820699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 788115914295470657094265 591086935721602992820699)
      ·
        refine ⟨886630403582404489231049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 591086935721602992820699 886630403582404489231049)
        ·
          refine ⟨664972802686803366923287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 886630403582404489231049 664972802686803366923287)
          ·
            refine ⟨997459204030205050384931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 664972802686803366923287 997459204030205050384931)
            ·
              refine ⟨1496188806045307575577397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 997459204030205050384931 1496188806045307575577397)
              ·
                refine ⟨140267700566747585210381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1496188806045307575577397 140267700566747585210381)
                ·
                  rfl

theorem cell20_921950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 1, 5].length) (baseStart_921950 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_921950 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_921950 prefixEnd_921950 := by exact prefixLift 921950
  have htrace : WordTrace (prefixWord ++ tailWord_921950) baseStart_921950 baseEnd_921950 := by
    simpa [prefixWord, tailWord_921950, baseEnd_921950] using wordTrace_append hprefix tailTrace_921950
  have hstable : (prefixWord ++ tailWord_921950).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921950).length < 2 ^ (prefixWord ++ tailWord_921950).sum := by decide
  have hdescent : baseEnd_921950 < baseStart_921950 := by decide
  rcases family_descends (prefixWord ++ tailWord_921950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921951 : List Nat := [1, 1, 2, 3, 1, 2, 6, 2, 2]
def baseStart_921951 : Nat := 118140960795 + 921951 * 2 ^ 59
def prefixEnd_921951 : Nat := 4983230072969 + 3 ^ 40 * 921951 * 2
def baseEnd_921951 : Nat := 420803558127491196597805

theorem tailTrace_921951 : CollatzResearch.WordTrace tailWord_921951 prefixEnd_921951 420803558127491196597805 := by
  unfold tailWord_921951
  simp only [CollatzResearch.WordTrace]
  refine ⟨33626315482936458540141707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22417543655290972360094471 33626315482936458540141707)
  ·
    refine ⟨50439473224404687810212561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33626315482936458540141707 50439473224404687810212561)
    ·
      refine ⟨37829604918303515857659421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50439473224404687810212561 37829604918303515857659421)
      ·
        refine ⟨14186101844363818446622283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37829604918303515857659421 14186101844363818446622283)
        ·
          refine ⟨21279152766545727669933425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14186101844363818446622283 21279152766545727669933425)
          ·
            refine ⟨15959364574909295752450069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21279152766545727669933425 15959364574909295752450069)
            ·
              refine ⟨748095214448873238396097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 15959364574909295752450069 748095214448873238396097)
              ·
                refine ⟨561071410836654928797073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 748095214448873238396097 561071410836654928797073)
                ·
                  refine ⟨420803558127491196597805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 561071410836654928797073 420803558127491196597805)
                  ·
                    rfl

theorem cell20_921951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 6, 2, 2].length) (baseStart_921951 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_921951 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_921951 prefixEnd_921951 := by exact prefixLift 921951
  have htrace : WordTrace (prefixWord ++ tailWord_921951) baseStart_921951 baseEnd_921951 := by
    simpa [prefixWord, tailWord_921951, baseEnd_921951] using wordTrace_append hprefix tailTrace_921951
  have hstable : (prefixWord ++ tailWord_921951).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921951).length < 2 ^ (prefixWord ++ tailWord_921951).sum := by decide
  have hdescent : baseEnd_921951 < baseStart_921951 := by decide
  rcases family_descends (prefixWord ++ tailWord_921951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921955 : List Nat := [1, 1, 1, 5, 2, 1, 2, 3, 4]
def baseStart_921955 : Nat := 118140960795 + 921955 * 2 ^ 59
def prefixEnd_921955 : Nat := 4983230072969 + 3 ^ 40 * 921955 * 2
def baseEnd_921955 : Nat := 420805383836484960464455

theorem tailTrace_921955 : CollatzResearch.WordTrace tailWord_921955 prefixEnd_921955 420805383836484960464455 := by
  unfold tailWord_921955
  simp only [CollatzResearch.WordTrace]
  refine ⟨33626461374921967223287319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22417640916614644815524879 33626461374921967223287319)
  ·
    refine ⟨50439692062382950834930979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33626461374921967223287319 50439692062382950834930979)
    ·
      refine ⟨75659538093574426252396469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50439692062382950834930979 75659538093574426252396469)
      ·
        refine ⟨7093081696272602461162169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 75659538093574426252396469 7093081696272602461162169)
        ·
          refine ⟨5319811272204451845871627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7093081696272602461162169 5319811272204451845871627)
          ·
            refine ⟨7979716908306677768807441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5319811272204451845871627 7979716908306677768807441)
            ·
              refine ⟨5984787681230008326605581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7979716908306677768807441 5984787681230008326605581)
              ·
                refine ⟨2244295380461253122477093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5984787681230008326605581 2244295380461253122477093)
                ·
                  refine ⟨420805383836484960464455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2244295380461253122477093 420805383836484960464455)
                  ·
                    rfl

theorem cell20_921955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 3, 4].length) (baseStart_921955 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_921955 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_921955 prefixEnd_921955 := by exact prefixLift 921955
  have htrace : WordTrace (prefixWord ++ tailWord_921955) baseStart_921955 baseEnd_921955 := by
    simpa [prefixWord, tailWord_921955, baseEnd_921955] using wordTrace_append hprefix tailTrace_921955
  have hstable : (prefixWord ++ tailWord_921955).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921955).length < 2 ^ (prefixWord ++ tailWord_921955).sum := by decide
  have hdescent : baseEnd_921955 < baseStart_921955 := by decide
  rcases family_descends (prefixWord ++ tailWord_921955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921969 : List Nat := [1, 2, 2, 2, 1, 2, 1, 2, 7]
def baseStart_921969 : Nat := 118140960795 + 921969 * 2 ^ 59
def prefixEnd_921969 : Nat := 4983230072969 + 3 ^ 40 * 921969 * 2
def baseEnd_921969 : Nat := 420811773817963133997731

theorem tailTrace_921969 : CollatzResearch.WordTrace tailWord_921969 prefixEnd_921969 420811773817963133997731 := by
  unfold tailWord_921969
  simp only [CollatzResearch.WordTrace]
  refine ⟨33626971996871247614296961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22417981331247498409531307 33626971996871247614296961)
  ·
    refine ⟨25220228997653435710722721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33626971996871247614296961 25220228997653435710722721)
    ·
      refine ⟨18915171748240076783042041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25220228997653435710722721 18915171748240076783042041)
      ·
        refine ⟨14186378811180057587281531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18915171748240076783042041 14186378811180057587281531)
        ·
          refine ⟨21279568216770086380922297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14186378811180057587281531 21279568216770086380922297)
          ·
            refine ⟨15959676162577564785691723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21279568216770086380922297 15959676162577564785691723)
            ·
              refine ⟨23939514243866347178537585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15959676162577564785691723 23939514243866347178537585)
              ·
                refine ⟨17954635682899760383903189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23939514243866347178537585 17954635682899760383903189)
                ·
                  refine ⟨420811773817963133997731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17954635682899760383903189 420811773817963133997731)
                  ·
                    rfl

theorem cell20_921969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 2, 7].length) (baseStart_921969 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_921969 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_921969 prefixEnd_921969 := by exact prefixLift 921969
  have htrace : WordTrace (prefixWord ++ tailWord_921969) baseStart_921969 baseEnd_921969 := by
    simpa [prefixWord, tailWord_921969, baseEnd_921969] using wordTrace_append hprefix tailTrace_921969
  have hstable : (prefixWord ++ tailWord_921969).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921969).length < 2 ^ (prefixWord ++ tailWord_921969).sum := by decide
  have hdescent : baseEnd_921969 < baseStart_921969 := by decide
  rcases family_descends (prefixWord ++ tailWord_921969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921979 : List Nat := [1, 1, 1, 1, 1, 8, 3, 4]
def baseStart_921979 : Nat := 118140960795 + 921979 * 2 ^ 59
def prefixEnd_921979 : Nat := 4983230072969 + 3 ^ 40 * 921979 * 2
def baseEnd_921979 : Nat := 140272112696815847888119

theorem tailTrace_921979 : CollatzResearch.WordTrace tailWord_921979 prefixEnd_921979 140272112696815847888119 := by
  unfold tailWord_921979
  simp only [CollatzResearch.WordTrace]
  refine ⟨33627336726835019322160991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22418224484556679548107327 33627336726835019322160991)
  ·
    refine ⟨50441005090252528983241487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33627336726835019322160991 50441005090252528983241487)
    ·
      refine ⟨75661507635378793474862231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50441005090252528983241487 75661507635378793474862231)
      ·
        refine ⟨113492261453068190212293347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75661507635378793474862231 113492261453068190212293347)
        ·
          refine ⟨170238392179602285318440021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113492261453068190212293347 170238392179602285318440021)
          ·
            refine ⟨1994981158354714281075469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 170238392179602285318440021 1994981158354714281075469)
            ·
              refine ⟨748117934383017855403301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1994981158354714281075469 748117934383017855403301)
              ·
                refine ⟨140272112696815847888119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 748117934383017855403301 140272112696815847888119)
                ·
                  rfl

theorem cell20_921979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 3, 4].length) (baseStart_921979 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_921979 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_921979 prefixEnd_921979 := by exact prefixLift 921979
  have htrace : WordTrace (prefixWord ++ tailWord_921979) baseStart_921979 baseEnd_921979 := by
    simpa [prefixWord, tailWord_921979, baseEnd_921979] using wordTrace_append hprefix tailTrace_921979
  have hstable : (prefixWord ++ tailWord_921979).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921979).length < 2 ^ (prefixWord ++ tailWord_921979).sum := by decide
  have hdescent : baseEnd_921979 < baseStart_921979 := by decide
  rcases family_descends (prefixWord ++ tailWord_921979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922010 : List Nat := [3, 1, 1, 4, 1, 3, 2, 1, 4]
def baseStart_922010 : Nat := 118140960795 + 922010 * 2 ^ 59
def prefixEnd_922010 : Nat := 4983230072969 + 3 ^ 40 * 922010 * 2
def baseEnd_922010 : Nat := 420830487335149213630897

theorem tailTrace_922010 : CollatzResearch.WordTrace tailWord_922010 prefixEnd_922010 420830487335149213630897 := by
  unfold tailWord_922010
  simp only [CollatzResearch.WordTrace]
  refine ⟨8407116847430677904134871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22418978259815141077692989 8407116847430677904134871)
  ·
    refine ⟨12610675271146016856202307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8407116847430677904134871 12610675271146016856202307)
    ·
      refine ⟨18916012906719025284303461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12610675271146016856202307 18916012906719025284303461)
      ·
        refine ⟨3546752420009817240806899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18916012906719025284303461 3546752420009817240806899)
        ·
          refine ⟨5320128630014725861210349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3546752420009817240806899 5320128630014725861210349)
          ·
            refine ⟨1995048236255522197953881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5320128630014725861210349 1995048236255522197953881)
            ·
              refine ⟨1496286177191641648465411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1995048236255522197953881 1496286177191641648465411)
              ·
                refine ⟨2244429265787462472698117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1496286177191641648465411 2244429265787462472698117)
                ·
                  refine ⟨420830487335149213630897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2244429265787462472698117 420830487335149213630897)
                  ·
                    rfl

theorem cell20_922010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 2, 1, 4].length) (baseStart_922010 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_922010 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_922010 prefixEnd_922010 := by exact prefixLift 922010
  have htrace : WordTrace (prefixWord ++ tailWord_922010) baseStart_922010 baseEnd_922010 := by
    simpa [prefixWord, tailWord_922010, baseEnd_922010] using wordTrace_append hprefix tailTrace_922010
  have hstable : (prefixWord ++ tailWord_922010).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922010).length < 2 ^ (prefixWord ++ tailWord_922010).sum := by decide
  have hdescent : baseEnd_922010 < baseStart_922010 := by decide
  rcases family_descends (prefixWord ++ tailWord_922010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922044 : List Nat := [2, 2, 2, 4, 1, 3, 1, 3, 2]
def baseStart_922044 : Nat := 118140960795 + 922044 * 2 ^ 59
def prefixEnd_922044 : Nat := 4983230072969 + 3 ^ 40 * 922044 * 2
def baseEnd_922044 : Nat := 420846005861596206497425

theorem tailTrace_922044 : CollatzResearch.WordTrace tailWord_922044 prefixEnd_922044 420846005861596206497425 := by
  unfold tailWord_922044
  simp only [CollatzResearch.WordTrace]
  refine ⟨16814853735799767711638593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22419804981066356948851457 16814853735799767711638593)
  ·
    refine ⟨12611140301849825783728945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16814853735799767711638593 12611140301849825783728945)
    ·
      refine ⟨9458355226387369337796709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12611140301849825783728945 9458355226387369337796709)
      ·
        refine ⟨1773441604947631750836883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9458355226387369337796709 1773441604947631750836883)
        ·
          refine ⟨2660162407421447626255325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1773441604947631750836883 2660162407421447626255325)
          ·
            refine ⟨997560902783042859845747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2660162407421447626255325 997560902783042859845747)
            ·
              refine ⟨1496341354174564289768621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 997560902783042859845747 1496341354174564289768621)
              ·
                refine ⟨561128007815461608663233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1496341354174564289768621 561128007815461608663233)
                ·
                  refine ⟨420846005861596206497425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 561128007815461608663233 420846005861596206497425)
                  ·
                    rfl

theorem cell20_922044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 1, 3, 2].length) (baseStart_922044 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_922044 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_922044 prefixEnd_922044 := by exact prefixLift 922044
  have htrace : WordTrace (prefixWord ++ tailWord_922044) baseStart_922044 baseEnd_922044 := by
    simpa [prefixWord, tailWord_922044, baseEnd_922044] using wordTrace_append hprefix tailTrace_922044
  have hstable : (prefixWord ++ tailWord_922044).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922044).length < 2 ^ (prefixWord ++ tailWord_922044).sum := by decide
  have hdescent : baseEnd_922044 < baseStart_922044 := by decide
  rcases family_descends (prefixWord ++ tailWord_922044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922062 : List Nat := [4, 1, 1, 1, 2, 1, 1, 6, 3]
def baseStart_922062 : Nat := 118140960795 + 922062 * 2 ^ 59
def prefixEnd_922062 : Nat := 4983230072969 + 3 ^ 40 * 922062 * 2
def baseEnd_922062 : Nat := 420854221552068143897351

theorem tailTrace_922062 : CollatzResearch.WordTrace tailWord_922062 prefixEnd_922062 420854221552068143897351 := by
  unfold tailWord_922062
  simp only [CollatzResearch.WordTrace]
  refine ⟨4203795498191790562179055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22420242657022882998288293 4203795498191790562179055)
  ·
    refine ⟨6305693247287685843268583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4203795498191790562179055 6305693247287685843268583)
    ·
      refine ⟨9458539870931528764902875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6305693247287685843268583 9458539870931528764902875)
      ·
        refine ⟨14187809806397293147354313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9458539870931528764902875 14187809806397293147354313)
        ·
          refine ⟨10640857354797969860515735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14187809806397293147354313 10640857354797969860515735)
          ·
            refine ⟨15961286032196954790773603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10640857354797969860515735 15961286032196954790773603)
            ·
              refine ⟨23941929048295432186160405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15961286032196954790773603 23941929048295432186160405)
              ·
                refine ⟨1122277924138848383726269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 23941929048295432186160405 1122277924138848383726269)
                ·
                  refine ⟨420854221552068143897351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1122277924138848383726269 420854221552068143897351)
                  ·
                    rfl

theorem cell20_922062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 6, 3].length) (baseStart_922062 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_922062 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_922062 prefixEnd_922062 := by exact prefixLift 922062
  have htrace : WordTrace (prefixWord ++ tailWord_922062) baseStart_922062 baseEnd_922062 := by
    simpa [prefixWord, tailWord_922062, baseEnd_922062] using wordTrace_append hprefix tailTrace_922062
  have hstable : (prefixWord ++ tailWord_922062).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922062).length < 2 ^ (prefixWord ++ tailWord_922062).sum := by decide
  have hdescent : baseEnd_922062 < baseStart_922062 := by decide
  rcases family_descends (prefixWord ++ tailWord_922062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922079 : List Nat := [1, 1, 2, 3, 3, 2, 4, 1, 3]
def baseStart_922079 : Nat := 118140960795 + 922079 * 2 ^ 59
def prefixEnd_922079 : Nat := 4983230072969 + 3 ^ 40 * 922079 * 2
def baseEnd_922079 : Nat := 420861980815291640330615

theorem tailTrace_922079 : CollatzResearch.WordTrace tailWord_922079 prefixEnd_922079 420861980815291640330615 := by
  unfold tailWord_922079
  simp only [CollatzResearch.WordTrace]
  refine ⟨33630984026472736400801291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22420656017648490933867527 33630984026472736400801291)
  ·
    refine ⟨50446476039709104601201937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33630984026472736400801291 50446476039709104601201937)
    ·
      refine ⟨37834857029781828450901453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50446476039709104601201937 37834857029781828450901453)
      ·
        refine ⟨14188071386168185669088045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37834857029781828450901453 14188071386168185669088045)
        ·
          refine ⟨5320526769813069625908017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14188071386168185669088045 5320526769813069625908017)
          ·
            refine ⟨3990395077359802219431013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5320526769813069625908017 3990395077359802219431013)
            ·
              refine ⟨748199077004962916143315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3990395077359802219431013 748199077004962916143315)
              ·
                refine ⟨1122298615507444374214973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 748199077004962916143315 1122298615507444374214973)
                ·
                  refine ⟨420861980815291640330615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1122298615507444374214973 420861980815291640330615)
                  ·
                    rfl

theorem cell20_922079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 4, 1, 3].length) (baseStart_922079 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_922079 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_922079 prefixEnd_922079 := by exact prefixLift 922079
  have htrace : WordTrace (prefixWord ++ tailWord_922079) baseStart_922079 baseEnd_922079 := by
    simpa [prefixWord, tailWord_922079, baseEnd_922079] using wordTrace_append hprefix tailTrace_922079
  have hstable : (prefixWord ++ tailWord_922079).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922079).length < 2 ^ (prefixWord ++ tailWord_922079).sum := by decide
  have hdescent : baseEnd_922079 < baseStart_922079 := by decide
  rcases family_descends (prefixWord ++ tailWord_922079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922093 : List Nat := [1, 5, 1, 3, 1, 1, 2, 6]
def baseStart_922093 : Nat := 118140960795 + 922093 * 2 ^ 59
def prefixEnd_922093 : Nat := 4983230072969 + 3 ^ 40 * 922093 * 2
def baseEnd_922093 : Nat := 140289456932256604621297

theorem tailTrace_922093 : CollatzResearch.WordTrace tailWord_922093 prefixEnd_922093 140289456932256604621297 := by
  unfold tailWord_922093
  simp only [CollatzResearch.WordTrace]
  refine ⟨33631494648422016791810933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22420996432281344527873955 33631494648422016791810933)
  ·
    refine ⟨3152952623289564074232275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33631494648422016791810933 3152952623289564074232275)
    ·
      refine ⟨4729428934934346111348413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3152952623289564074232275 4729428934934346111348413)
      ·
        refine ⟨1773535850600379791755655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4729428934934346111348413 1773535850600379791755655)
        ·
          refine ⟨2660303775900569687633483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1773535850600379791755655 2660303775900569687633483)
          ·
            refine ⟨3990455663850854531450225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2660303775900569687633483 3990455663850854531450225)
            ·
              refine ⟨2992841747888140898587669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3990455663850854531450225 2992841747888140898587669)
              ·
                refine ⟨140289456932256604621297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2992841747888140898587669 140289456932256604621297)
                ·
                  rfl

theorem cell20_922093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 6].length) (baseStart_922093 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_922093 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_922093 prefixEnd_922093 := by exact prefixLift 922093
  have htrace : WordTrace (prefixWord ++ tailWord_922093) baseStart_922093 baseEnd_922093 := by
    simpa [prefixWord, tailWord_922093, baseEnd_922093] using wordTrace_append hprefix tailTrace_922093
  have hstable : (prefixWord ++ tailWord_922093).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922093).length < 2 ^ (prefixWord ++ tailWord_922093).sum := by decide
  have hdescent : baseEnd_922093 < baseStart_922093 := by decide
  rcases family_descends (prefixWord ++ tailWord_922093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922138 : List Nat := [3, 1, 1, 3, 1, 1, 4, 3, 3]
def baseStart_922138 : Nat := 118140960795 + 922138 * 2 ^ 59
def prefixEnd_922138 : Nat := 4983230072969 + 3 ^ 40 * 922138 * 2
def baseEnd_922138 : Nat := 420888910022949657363707

theorem tailTrace_922138 : CollatzResearch.WordTrace tailWord_922138 prefixEnd_922138 420888910022949657363707 := by
  unfold tailWord_922138
  simp only [CollatzResearch.WordTrace]
  refine ⟨8408283983314747369299767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22422090622172659651466045 8408283983314747369299767)
  ·
    refine ⟨12612425974972121053949651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8408283983314747369299767 12612425974972121053949651)
    ·
      refine ⟨18918638962458181580924477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12612425974972121053949651 18918638962458181580924477)
      ·
        refine ⟨7094489610921818092846679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18918638962458181580924477 7094489610921818092846679)
        ·
          refine ⟨10641734416382727139270019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7094489610921818092846679 10641734416382727139270019)
          ·
            refine ⟨15962601624574090708905029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10641734416382727139270019 15962601624574090708905029)
            ·
              refine ⟨2992987804607642007919693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15962601624574090708905029 2992987804607642007919693)
              ·
                refine ⟨1122370426727865752969885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2992987804607642007919693 1122370426727865752969885)
                ·
                  refine ⟨420888910022949657363707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1122370426727865752969885 420888910022949657363707)
                  ·
                    rfl

theorem cell20_922138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 3, 3].length) (baseStart_922138 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_922138 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_922138 prefixEnd_922138 := by exact prefixLift 922138
  have htrace : WordTrace (prefixWord ++ tailWord_922138) baseStart_922138 baseEnd_922138 := by
    simpa [prefixWord, tailWord_922138, baseEnd_922138] using wordTrace_append hprefix tailTrace_922138
  have hstable : (prefixWord ++ tailWord_922138).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922138).length < 2 ^ (prefixWord ++ tailWord_922138).sum := by decide
  have hdescent : baseEnd_922138 < baseStart_922138 := by decide
  rcases family_descends (prefixWord ++ tailWord_922138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922145 : List Nat := [1, 2, 3, 2, 2, 1, 3, 2, 4]
def baseStart_922145 : Nat := 118140960795 + 922145 * 2 ^ 59
def prefixEnd_922145 : Nat := 4983230072969 + 3 ^ 40 * 922145 * 2
def baseEnd_922145 : Nat := 420892105013688744130345

theorem tailTrace_922145 : CollatzResearch.WordTrace tailWord_922145 prefixEnd_922145 420892105013688744130345 := by
  unfold tailWord_922145
  simp only [CollatzResearch.WordTrace]
  refine ⟨33633391244233629672703889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22422260829489086448469259 33633391244233629672703889)
  ·
    refine ⟨25225043433175222254527917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33633391244233629672703889 25225043433175222254527917)
    ·
      refine ⟨9459391287440708345447969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25225043433175222254527917 9459391287440708345447969)
      ·
        refine ⟨7094543465580531259085977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9459391287440708345447969 7094543465580531259085977)
        ·
          refine ⟨5320907599185398444314483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7094543465580531259085977 5320907599185398444314483)
          ·
            refine ⟨7981361398778097666471725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5320907599185398444314483 7981361398778097666471725)
            ·
              refine ⟨2993010524541786624926897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7981361398778097666471725 2993010524541786624926897)
              ·
                refine ⟨2244757893406339968695173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2993010524541786624926897 2244757893406339968695173)
                ·
                  refine ⟨420892105013688744130345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2244757893406339968695173 420892105013688744130345)
                  ·
                    rfl

theorem cell20_922145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 2, 4].length) (baseStart_922145 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_922145 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_922145 prefixEnd_922145 := by exact prefixLift 922145
  have htrace : WordTrace (prefixWord ++ tailWord_922145) baseStart_922145 baseEnd_922145 := by
    simpa [prefixWord, tailWord_922145, baseEnd_922145] using wordTrace_append hprefix tailTrace_922145
  have hstable : (prefixWord ++ tailWord_922145).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922145).length < 2 ^ (prefixWord ++ tailWord_922145).sum := by decide
  have hdescent : baseEnd_922145 < baseStart_922145 := by decide
  rcases family_descends (prefixWord ++ tailWord_922145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922158 : List Nat := [4, 1, 3, 1, 3, 1, 2, 3, 2]
def baseStart_922158 : Nat := 118140960795 + 922158 * 2 ^ 59
def prefixEnd_922158 : Nat := 4983230072969 + 3 ^ 40 * 922158 * 2
def baseEnd_922158 : Nat := 420898038567918476696959

theorem tailTrace_922158 : CollatzResearch.WordTrace tailWord_922158 prefixEnd_922158 420898038567918476696959 := by
  unfold tailWord_922158
  simp only [CollatzResearch.WordTrace]
  refine ⟨4204233174148316611615891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22422576928791021928618085 4204233174148316611615891)
  ·
    refine ⟨6306349761222474917423837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4204233174148316611615891 6306349761222474917423837)
    ·
      refine ⟨2364881160458428094033939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6306349761222474917423837 2364881160458428094033939)
      ·
        refine ⟨3547321740687642141050909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2364881160458428094033939 3547321740687642141050909)
        ·
          refine ⟨1330245652757865802894091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3547321740687642141050909 1330245652757865802894091)
          ·
            refine ⟨1995368479136798704341137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1330245652757865802894091 1995368479136798704341137)
            ·
              refine ⟨1496526359352599028255853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1995368479136798704341137 1496526359352599028255853)
              ·
                refine ⟨561197384757224635595945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1496526359352599028255853 561197384757224635595945)
                ·
                  refine ⟨420898038567918476696959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 561197384757224635595945 420898038567918476696959)
                  ·
                    rfl

theorem cell20_922158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 2, 3, 2].length) (baseStart_922158 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_922158 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_922158 prefixEnd_922158 := by exact prefixLift 922158
  have htrace : WordTrace (prefixWord ++ tailWord_922158) baseStart_922158 baseEnd_922158 := by
    simpa [prefixWord, tailWord_922158, baseEnd_922158] using wordTrace_append hprefix tailTrace_922158
  have hstable : (prefixWord ++ tailWord_922158).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922158).length < 2 ^ (prefixWord ++ tailWord_922158).sum := by decide
  have hdescent : baseEnd_922158 < baseStart_922158 := by decide
  rcases family_descends (prefixWord ++ tailWord_922158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922162 : List Nat := [3, 2, 1, 1, 2, 1, 3, 5, 2]
def baseStart_922162 : Nat := 118140960795 + 922162 * 2 ^ 59
def prefixEnd_922162 : Nat := 4983230072969 + 3 ^ 40 * 922162 * 2
def baseEnd_922162 : Nat := 420899864276912240563609

theorem tailTrace_922162 : CollatzResearch.WordTrace tailWord_922162 prefixEnd_922162 420899864276912240563609 := by
  unfold tailWord_922162
  simp only [CollatzResearch.WordTrace]
  refine ⟨8408502821293010394018185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22422674190114694384048493 8408502821293010394018185)
  ·
    refine ⟨6306377115969757795513639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8408502821293010394018185 6306377115969757795513639)
    ·
      refine ⟨9459565673954636693270459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6306377115969757795513639 9459565673954636693270459)
      ·
        refine ⟨14189348510931955039905689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9459565673954636693270459 14189348510931955039905689)
        ·
          refine ⟨10642011383198966279929267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14189348510931955039905689 10642011383198966279929267)
          ·
            refine ⟨15963017074798449419893901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10642011383198966279929267 15963017074798449419893901)
            ·
              refine ⟨5986131403049418532460213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15963017074798449419893901 5986131403049418532460213)
              ·
                refine ⟨561199819035882987418145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5986131403049418532460213 561199819035882987418145)
                ·
                  refine ⟨420899864276912240563609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 561199819035882987418145 420899864276912240563609)
                  ·
                    rfl

theorem cell20_922162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 5, 2].length) (baseStart_922162 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_922162 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_922162 prefixEnd_922162 := by exact prefixLift 922162
  have htrace : WordTrace (prefixWord ++ tailWord_922162) baseStart_922162 baseEnd_922162 := by
    simpa [prefixWord, tailWord_922162, baseEnd_922162] using wordTrace_append hprefix tailTrace_922162
  have hstable : (prefixWord ++ tailWord_922162).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922162).length < 2 ^ (prefixWord ++ tailWord_922162).sum := by decide
  have hdescent : baseEnd_922162 < baseStart_922162 := by decide
  rcases family_descends (prefixWord ++ tailWord_922162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922176 : List Nat := [2, 1, 1, 2, 2, 2, 5, 2, 3]
def baseStart_922176 : Nat := 118140960795 + 922176 * 2 ^ 59
def prefixEnd_922176 : Nat := 4983230072969 + 3 ^ 40 * 922176 * 2
def baseEnd_922176 : Nat := 420906254258390414096885

theorem tailTrace_922176 : CollatzResearch.WordTrace tailWord_922176 prefixEnd_922176 420906254258390414096885 := by
  unfold tailWord_922176
  simp only [CollatzResearch.WordTrace]
  refine ⟨16817260953560660983541191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22423014604747547978054921 16817260953560660983541191)
  ·
    refine ⟨25225891430340991475311787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16817260953560660983541191 25225891430340991475311787)
    ·
      refine ⟨37838837145511487212967681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25225891430340991475311787 37838837145511487212967681)
      ·
        refine ⟨28379127859133615409725761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37838837145511487212967681 28379127859133615409725761)
        ·
          refine ⟨21284345894350211557294321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28379127859133615409725761 21284345894350211557294321)
          ·
            refine ⟨15963259420762658667970741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21284345894350211557294321 15963259420762658667970741)
            ·
              refine ⟨1496555570696499250122257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15963259420762658667970741 1496555570696499250122257)
              ·
                refine ⟨1122416678022374437591693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1496555570696499250122257 1122416678022374437591693)
                ·
                  refine ⟨420906254258390414096885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1122416678022374437591693 420906254258390414096885)
                  ·
                    rfl

theorem cell20_922176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 5, 2, 3].length) (baseStart_922176 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_922176 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_922176 prefixEnd_922176 := by exact prefixLift 922176
  have htrace : WordTrace (prefixWord ++ tailWord_922176) baseStart_922176 baseEnd_922176 := by
    simpa [prefixWord, tailWord_922176, baseEnd_922176] using wordTrace_append hprefix tailTrace_922176
  have hstable : (prefixWord ++ tailWord_922176).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922176).length < 2 ^ (prefixWord ++ tailWord_922176).sum := by decide
  have hdescent : baseEnd_922176 < baseStart_922176 := by decide
  rcases family_descends (prefixWord ++ tailWord_922176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922183 : List Nat := [1, 1, 4, 1, 4, 1, 1, 3, 4]
def baseStart_922183 : Nat := 118140960795 + 922183 * 2 ^ 59
def prefixEnd_922183 : Nat := 4983230072969 + 3 ^ 40 * 922183 * 2
def baseEnd_922183 : Nat := 420909449249129500863523

theorem tailTrace_922183 : CollatzResearch.WordTrace tailWord_922183 prefixEnd_922183 420909449249129500863523 := by
  unfold tailWord_922183
  simp only [CollatzResearch.WordTrace]
  refine ⟨33634777218095962162587203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22423184812063974775058135 33634777218095962162587203)
  ·
    refine ⟨50452165827143943243880805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33634777218095962162587203 50452165827143943243880805)
    ·
      refine ⟨9459781092589489358227651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50452165827143943243880805 9459781092589489358227651)
      ·
        refine ⟨14189671638884234037341477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9459781092589489358227651 14189671638884234037341477)
        ·
          refine ⟨2660563432290793882001527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14189671638884234037341477 2660563432290793882001527)
          ·
            refine ⟨3990845148436190823002291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2660563432290793882001527 3990845148436190823002291)
            ·
              refine ⟨5986267722654286234503437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3990845148436190823002291 5986267722654286234503437)
              ·
                refine ⟨2244850395995357337938789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5986267722654286234503437 2244850395995357337938789)
                ·
                  refine ⟨420909449249129500863523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2244850395995357337938789 420909449249129500863523)
                  ·
                    rfl

theorem cell20_922183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 3, 4].length) (baseStart_922183 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_922183 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_922183 prefixEnd_922183 := by exact prefixLift 922183
  have htrace : WordTrace (prefixWord ++ tailWord_922183) baseStart_922183 baseEnd_922183 := by
    simpa [prefixWord, tailWord_922183, baseEnd_922183] using wordTrace_append hprefix tailTrace_922183
  have hstable : (prefixWord ++ tailWord_922183).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922183).length < 2 ^ (prefixWord ++ tailWord_922183).sum := by decide
  have hdescent : baseEnd_922183 < baseStart_922183 := by decide
  rcases family_descends (prefixWord ++ tailWord_922183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922193 : List Nat := [1, 2, 2, 1, 3, 4, 3, 1, 3]
def baseStart_922193 : Nat := 118140960795 + 922193 * 2 ^ 59
def prefixEnd_922193 : Nat := 4983230072969 + 3 ^ 40 * 922193 * 2
def baseEnd_922193 : Nat := 420914013521613910530149

theorem tailTrace_922193 : CollatzResearch.WordTrace tailWord_922193 prefixEnd_922193 420914013521613910530149 := by
  unfold tailWord_922193
  simp only [CollatzResearch.WordTrace]
  refine ⟨33635141948059733870451233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22423427965373155913634155 33635141948059733870451233)
  ·
    refine ⟨25226356461044800402838425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33635141948059733870451233 25226356461044800402838425)
    ·
      refine ⟨18919767345783600302128819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25226356461044800402838425 18919767345783600302128819)
      ·
        refine ⟨28379651018675400453193229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18919767345783600302128819 28379651018675400453193229)
        ·
          refine ⟨10642369132003275169947461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28379651018675400453193229 10642369132003275169947461)
          ·
            refine ⟨1995444212250614094365149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10642369132003275169947461 1995444212250614094365149)
            ·
              refine ⟨748291579593980285386931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1995444212250614094365149 748291579593980285386931)
              ·
                refine ⟨1122437369390970428080397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 748291579593980285386931 1122437369390970428080397)
                ·
                  refine ⟨420914013521613910530149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1122437369390970428080397 420914013521613910530149)
                  ·
                    rfl

theorem cell20_922193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 3, 1, 3].length) (baseStart_922193 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_922193 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_922193 prefixEnd_922193 := by exact prefixLift 922193
  have htrace : WordTrace (prefixWord ++ tailWord_922193) baseStart_922193 baseEnd_922193 := by
    simpa [prefixWord, tailWord_922193, baseEnd_922193] using wordTrace_append hprefix tailTrace_922193
  have hstable : (prefixWord ++ tailWord_922193).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922193).length < 2 ^ (prefixWord ++ tailWord_922193).sum := by decide
  have hdescent : baseEnd_922193 < baseStart_922193 := by decide
  rcases family_descends (prefixWord ++ tailWord_922193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922276 : List Nat := [2, 3, 1, 2, 2, 1, 2, 5, 2]
def baseStart_922276 : Nat := 118140960795 + 922276 * 2 ^ 59
def prefixEnd_922276 : Nat := 4983230072969 + 3 ^ 40 * 922276 * 2
def baseEnd_922276 : Nat := 420951896983234510763143

theorem tailTrace_922276 : CollatzResearch.WordTrace tailWord_922276 prefixEnd_922276 420951896983234510763143 := by
  unfold tailWord_922276
  simp only [CollatzResearch.WordTrace]
  refine ⟨16819084603379519522861341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22425446137839359363815121 16819084603379519522861341)
  ·
    refine ⟨6307156726267319821073003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16819084603379519522861341 6307156726267319821073003)
    ·
      refine ⟨9460735089400979731609505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6307156726267319821073003 9460735089400979731609505)
      ·
        refine ⟨7095551317050734798707129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9460735089400979731609505 7095551317050734798707129)
        ·
          refine ⟨5321663487788051099030347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7095551317050734798707129 5321663487788051099030347)
          ·
            refine ⟨7982495231682076648545521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5321663487788051099030347 7982495231682076648545521)
            ·
              refine ⟨5986871423761557486409141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7982495231682076648545521 5986871423761557486409141)
              ·
                refine ⟨561269195977646014350857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5986871423761557486409141 561269195977646014350857)
                ·
                  refine ⟨420951896983234510763143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 561269195977646014350857 420951896983234510763143)
                  ·
                    rfl

theorem cell20_922276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 5, 2].length) (baseStart_922276 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_922276 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_922276 prefixEnd_922276 := by exact prefixLift 922276
  have htrace : WordTrace (prefixWord ++ tailWord_922276) baseStart_922276 baseEnd_922276 := by
    simpa [prefixWord, tailWord_922276, baseEnd_922276] using wordTrace_append hprefix tailTrace_922276
  have hstable : (prefixWord ++ tailWord_922276).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922276).length < 2 ^ (prefixWord ++ tailWord_922276).sum := by decide
  have hdescent : baseEnd_922276 < baseStart_922276 := by decide
  rcases family_descends (prefixWord ++ tailWord_922276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922286 : List Nat := [4, 1, 4, 1, 1, 2, 2, 2, 3]
def baseStart_922286 : Nat := 118140960795 + 922286 * 2 ^ 59
def prefixEnd_922286 : Nat := 4983230072969 + 3 ^ 40 * 922286 * 2
def baseEnd_922286 : Nat := 420956461255718920429769

theorem tailTrace_922286 : CollatzResearch.WordTrace tailWord_922286 prefixEnd_922286 420956461255718920429769 := by
  unfold tailWord_922286
  simp only [CollatzResearch.WordTrace]
  refine ⟨4204816742090351344198339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22425689291148540502391141 4204816742090351344198339)
  ·
    refine ⟨6307225113135527016297509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4204816742090351344198339 6307225113135527016297509)
    ·
      refine ⟨1182604708712911315555783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6307225113135527016297509 1182604708712911315555783)
      ·
        refine ⟨1773907063069366973333675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1182604708712911315555783 1773907063069366973333675)
        ·
          refine ⟨2660860594604050460000513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1773907063069366973333675 2660860594604050460000513)
          ·
            refine ⟨1995645445953037845000385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2660860594604050460000513 1995645445953037845000385)
            ·
              refine ⟨1496734084464778383750289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1995645445953037845000385 1496734084464778383750289)
              ·
                refine ⟨1122550563348583787812717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1496734084464778383750289 1122550563348583787812717)
                ·
                  refine ⟨420956461255718920429769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1122550563348583787812717 420956461255718920429769)
                  ·
                    rfl

theorem cell20_922286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 2, 2, 3].length) (baseStart_922286 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_922286 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_922286 prefixEnd_922286 := by exact prefixLift 922286
  have htrace : WordTrace (prefixWord ++ tailWord_922286) baseStart_922286 baseEnd_922286 := by
    simpa [prefixWord, tailWord_922286, baseEnd_922286] using wordTrace_append hprefix tailTrace_922286
  have hstable : (prefixWord ++ tailWord_922286).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922286).length < 2 ^ (prefixWord ++ tailWord_922286).sum := by decide
  have hdescent : baseEnd_922286 < baseStart_922286 := by decide
  rcases family_descends (prefixWord ++ tailWord_922286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922287 : List Nat := [1, 1, 2, 1, 2, 13]
def baseStart_922287 : Nat := 118140960795 + 922287 * 2 ^ 59
def prefixEnd_922287 : Nat := 4983230072969 + 3 ^ 40 * 922287 * 2
def baseEnd_922287 : Nat := 15590996951221013385053

theorem tailTrace_922287 : CollatzResearch.WordTrace tailWord_922287 prefixEnd_922287 15590996951221013385053 := by
  unfold tailWord_922287
  simp only [CollatzResearch.WordTrace]
  refine ⟨33638570409719187924373115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22425713606479458616248743 33638570409719187924373115)
  ·
    refine ⟨50457855614578781886559673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33638570409719187924373115 50457855614578781886559673)
    ·
      refine ⟨37843391710934086414919755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50457855614578781886559673 37843391710934086414919755)
      ·
        refine ⟨56765087566401129622379633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37843391710934086414919755 56765087566401129622379633)
        ·
          refine ⟨42573815674800847216784725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56765087566401129622379633 42573815674800847216784725)
          ·
            refine ⟨15590996951221013385053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 42573815674800847216784725 15590996951221013385053)
            ·
              rfl

theorem cell20_922287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 13].length) (baseStart_922287 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_922287 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_922287 prefixEnd_922287 := by exact prefixLift 922287
  have htrace : WordTrace (prefixWord ++ tailWord_922287) baseStart_922287 baseEnd_922287 := by
    simpa [prefixWord, tailWord_922287, baseEnd_922287] using wordTrace_append hprefix tailTrace_922287
  have hstable : (prefixWord ++ tailWord_922287).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922287).length < 2 ^ (prefixWord ++ tailWord_922287).sum := by decide
  have hdescent : baseEnd_922287 < baseStart_922287 := by decide
  rcases family_descends (prefixWord ++ tailWord_922287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922289 : List Nat := [1, 2, 2, 6, 1, 2, 2, 2, 2]
def baseStart_922289 : Nat := 118140960795 + 922289 * 2 ^ 59
def prefixEnd_922289 : Nat := 4983230072969 + 3 ^ 40 * 922289 * 2
def baseEnd_922289 : Nat := 420957830537464243329757

theorem tailTrace_922289 : CollatzResearch.WordTrace tailWord_922289 prefixEnd_922289 420957830537464243329757 := by
  unfold tailWord_922289
  simp only [CollatzResearch.WordTrace]
  refine ⟨33638643355711942265945921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22425762237141294843963947 33638643355711942265945921)
  ·
    refine ⟨25228982516783956699459441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33638643355711942265945921 25228982516783956699459441)
    ·
      refine ⟨18921736887587967524594581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25228982516783956699459441 18921736887587967524594581)
      ·
        refine ⟨886956416605685977715371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 18921736887587967524594581 886956416605685977715371)
        ·
          refine ⟨1330434624908528966573057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 886956416605685977715371 1330434624908528966573057)
          ·
            refine ⟨997825968681396724929793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1330434624908528966573057 997825968681396724929793)
            ·
              refine ⟨748369476511047543697345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 997825968681396724929793 748369476511047543697345)
              ·
                refine ⟨561277107383285657773009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 748369476511047543697345 561277107383285657773009)
                ·
                  refine ⟨420957830537464243329757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 561277107383285657773009 420957830537464243329757)
                  ·
                    rfl

theorem cell20_922289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 2, 2, 2].length) (baseStart_922289 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_922289 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_922289 prefixEnd_922289 := by exact prefixLift 922289
  have htrace : WordTrace (prefixWord ++ tailWord_922289) baseStart_922289 baseEnd_922289 := by
    simpa [prefixWord, tailWord_922289, baseEnd_922289] using wordTrace_append hprefix tailTrace_922289
  have hstable : (prefixWord ++ tailWord_922289).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922289).length < 2 ^ (prefixWord ++ tailWord_922289).sum := by decide
  have hdescent : baseEnd_922289 < baseStart_922289 := by decide
  rcases family_descends (prefixWord ++ tailWord_922289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922293 : List Nat := [1, 3, 3, 3, 1, 2, 1, 4, 2]
def baseStart_922293 : Nat := 118140960795 + 922293 * 2 ^ 59
def prefixEnd_922293 : Nat := 4983230072969 + 3 ^ 40 * 922293 * 2
def baseEnd_922293 : Nat := 420959656246458007196407

theorem tailTrace_922293 : CollatzResearch.WordTrace tailWord_922293 prefixEnd_922293 420959656246458007196407 := by
  unfold tailWord_922293
  simp only [CollatzResearch.WordTrace]
  refine ⟨33638789247697450949091533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22425859498464967299394355 33638789247697450949091533)
  ·
    refine ⟨12614545967886544105909325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33638789247697450949091533 12614545967886544105909325)
    ·
      refine ⟨4730454737957454039715997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12614545967886544105909325 4730454737957454039715997)
      ·
        refine ⟨1773920526734045264893499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4730454737957454039715997 1773920526734045264893499)
        ·
          refine ⟨2660880790101067897340249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1773920526734045264893499 2660880790101067897340249)
          ·
            refine ⟨1995660592575800923005187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2660880790101067897340249 1995660592575800923005187)
            ·
              refine ⟨2993490888863701384507781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1995660592575800923005187 2993490888863701384507781)
              ·
                refine ⟨561279541661944009595209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2993490888863701384507781 561279541661944009595209)
                ·
                  refine ⟨420959656246458007196407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 561279541661944009595209 420959656246458007196407)
                  ·
                    rfl

theorem cell20_922293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 4, 2].length) (baseStart_922293 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_922293 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_922293 prefixEnd_922293 := by exact prefixLift 922293
  have htrace : WordTrace (prefixWord ++ tailWord_922293) baseStart_922293 baseEnd_922293 := by
    simpa [prefixWord, tailWord_922293, baseEnd_922293] using wordTrace_append hprefix tailTrace_922293
  have hstable : (prefixWord ++ tailWord_922293).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922293).length < 2 ^ (prefixWord ++ tailWord_922293).sum := by decide
  have hdescent : baseEnd_922293 < baseStart_922293 := by decide
  rcases family_descends (prefixWord ++ tailWord_922293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922304 : List Nat := [2, 1, 1, 2, 4, 2, 3, 5]
def baseStart_922304 : Nat := 118140960795 + 922304 * 2 ^ 59
def prefixEnd_922304 : Nat := 4983230072969 + 3 ^ 40 * 922304 * 2
def baseEnd_922304 : Nat := 140321558982063619276565

theorem tailTrace_922304 : CollatzResearch.WordTrace tailWord_922304 prefixEnd_922304 140321558982063619276565 := by
  unfold tailWord_922304
  simp only [CollatzResearch.WordTrace]
  refine ⟨16819595225328799913870983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22426126967105066551827977 16819595225328799913870983)
  ·
    refine ⟨25229392837993199870806475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16819595225328799913870983 25229392837993199870806475)
    ·
      refine ⟨37844089256989799806209713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25229392837993199870806475 37844089256989799806209713)
      ·
        refine ⟨28383066942742349854657285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37844089256989799806209713 28383066942742349854657285)
        ·
          refine ⟨5321825051764190597748241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28383066942742349854657285 5321825051764190597748241)
          ·
            refine ⟨3991368788823142948311181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5321825051764190597748241 3991368788823142948311181)
            ·
              refine ⟨1496763295808678605616693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3991368788823142948311181 1496763295808678605616693)
              ·
                refine ⟨140321558982063619276565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1496763295808678605616693 140321558982063619276565)
                ·
                  rfl

theorem cell20_922304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 3, 5].length) (baseStart_922304 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_922304 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_922304 prefixEnd_922304 := by exact prefixLift 922304
  have htrace : WordTrace (prefixWord ++ tailWord_922304) baseStart_922304 baseEnd_922304 := by
    simpa [prefixWord, tailWord_922304, baseEnd_922304] using wordTrace_append hprefix tailTrace_922304
  have hstable : (prefixWord ++ tailWord_922304).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922304).length < 2 ^ (prefixWord ++ tailWord_922304).sum := by decide
  have hdescent : baseEnd_922304 < baseStart_922304 := by decide
  rcases family_descends (prefixWord ++ tailWord_922304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922310 : List Nat := [6, 1, 2, 1, 2, 1, 1, 2, 4]
def baseStart_922310 : Nat := 118140960795 + 922310 * 2 ^ 59
def prefixEnd_922310 : Nat := 4983230072969 + 3 ^ 40 * 922310 * 2
def baseEnd_922310 : Nat := 420967415509681503629671

theorem tailTrace_922310 : CollatzResearch.WordTrace tailWord_922310 prefixEnd_922310 420967415509681503629671 := by
  unfold tailWord_922310
  simp only [CollatzResearch.WordTrace]
  refine ⟨1051231540269870714139387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 22426272859090575234973589 1051231540269870714139387)
  ·
    refine ⟨1576847310404806071209081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1051231540269870714139387 1576847310404806071209081)
    ·
      refine ⟨1182635482803604553406811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1576847310404806071209081 1182635482803604553406811)
      ·
        refine ⟨1773953224205406830110217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1182635482803604553406811 1773953224205406830110217)
        ·
          refine ⟨1330464918154055122582663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1773953224205406830110217 1330464918154055122582663)
          ·
            refine ⟨1995697377231082683873995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1330464918154055122582663 1995697377231082683873995)
            ·
              refine ⟨2993546065846624025810993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1995697377231082683873995 2993546065846624025810993)
              ·
                refine ⟨2245159549384968019358245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2993546065846624025810993 2245159549384968019358245)
                ·
                  refine ⟨420967415509681503629671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2245159549384968019358245 420967415509681503629671)
                  ·
                    rfl

theorem cell20_922310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_922310 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_922310 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_922310 prefixEnd_922310 := by exact prefixLift 922310
  have htrace : WordTrace (prefixWord ++ tailWord_922310) baseStart_922310 baseEnd_922310 := by
    simpa [prefixWord, tailWord_922310, baseEnd_922310] using wordTrace_append hprefix tailTrace_922310
  have hstable : (prefixWord ++ tailWord_922310).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922310).length < 2 ^ (prefixWord ++ tailWord_922310).sum := by decide
  have hdescent : baseEnd_922310 < baseStart_922310 := by decide
  rcases family_descends (prefixWord ++ tailWord_922310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922317 : List Nat := [1, 6, 2, 1, 2, 1, 3, 4]
def baseStart_922317 : Nat := 118140960795 + 922317 * 2 ^ 59
def prefixEnd_922317 : Nat := 4983230072969 + 3 ^ 40 * 922317 * 2
def baseEnd_922317 : Nat := 140323536833473530132103

theorem tailTrace_922317 : CollatzResearch.WordTrace tailWord_922317 prefixEnd_922317 140323536833473530132103 := by
  unfold tailWord_922317
  simp only [CollatzResearch.WordTrace]
  refine ⟨33639664599610503047965205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22426443066407002031976803 33639664599610503047965205)
  ·
    refine ⟨1576859278106742330373369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 33639664599610503047965205 1576859278106742330373369)
    ·
      refine ⟨1182644458580056747780027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1576859278106742330373369 1182644458580056747780027)
      ·
        refine ⟨1773966687870085121670041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1182644458580056747780027 1773966687870085121670041)
        ·
          refine ⟨1330475015902563841252531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1773966687870085121670041 1330475015902563841252531)
          ·
            refine ⟨1995712523853845761878797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1330475015902563841252531 1995712523853845761878797)
            ·
              refine ⟨748392196445192160704549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1995712523853845761878797 748392196445192160704549)
              ·
                refine ⟨140323536833473530132103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 748392196445192160704549 140323536833473530132103)
                ·
                  rfl

theorem cell20_922317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 3, 4].length) (baseStart_922317 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_922317 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_922317 prefixEnd_922317 := by exact prefixLift 922317
  have htrace : WordTrace (prefixWord ++ tailWord_922317) baseStart_922317 baseEnd_922317 := by
    simpa [prefixWord, tailWord_922317, baseEnd_922317] using wordTrace_append hprefix tailTrace_922317
  have hstable : (prefixWord ++ tailWord_922317).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922317).length < 2 ^ (prefixWord ++ tailWord_922317).sum := by decide
  have hdescent : baseEnd_922317 < baseStart_922317 := by decide
  rcases family_descends (prefixWord ++ tailWord_922317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922418 : List Nat := [3, 2, 1, 1, 3, 1, 4, 5]
def baseStart_922418 : Nat := 118140960795 + 922418 * 2 ^ 59
def prefixEnd_922418 : Nat := 4983230072969 + 3 ^ 40 * 922418 * 2
def baseEnd_922418 : Nat := 140338903217504376009743

theorem tailTrace_922418 : CollatzResearch.WordTrace tailWord_922418 prefixEnd_922418 140338903217504376009743 := by
  unfold tailWord_922418
  simp only [CollatzResearch.WordTrace]
  refine ⟨8410837093061149324347977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22428898914829731531594605 8410837093061149324347977)
  ·
    refine ⟨6308127819795861993260983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8410837093061149324347977 6308127819795861993260983)
    ·
      refine ⟨9462191729693792989891475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6308127819795861993260983 9462191729693792989891475)
      ·
        refine ⟨14193287594540689484837213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9462191729693792989891475 14193287594540689484837213)
        ·
          refine ⟨5322482847952758556813955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14193287594540689484837213 5322482847952758556813955)
          ·
            refine ⟨7983724271929137835220933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5322482847952758556813955 7983724271929137835220933)
            ·
              refine ⟨1496948300986713344103925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7983724271929137835220933 1496948300986713344103925)
              ·
                refine ⟨140338903217504376009743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1496948300986713344103925 140338903217504376009743)
                ·
                  rfl

theorem cell20_922418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 4, 5].length) (baseStart_922418 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_922418 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_922418 prefixEnd_922418 := by exact prefixLift 922418
  have htrace : WordTrace (prefixWord ++ tailWord_922418) baseStart_922418 baseEnd_922418 := by
    simpa [prefixWord, tailWord_922418, baseEnd_922418] using wordTrace_append hprefix tailTrace_922418
  have hstable : (prefixWord ++ tailWord_922418).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922418).length < 2 ^ (prefixWord ++ tailWord_922418).sum := by decide
  have hdescent : baseEnd_922418 < baseStart_922418 := by decide
  rcases family_descends (prefixWord ++ tailWord_922418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922421 : List Nat := [1, 3, 3, 1, 3, 1, 4, 1, 3]
def baseStart_922421 : Nat := 118140960795 + 922421 * 2 ^ 59
def prefixEnd_922421 : Nat := 4983230072969 + 3 ^ 40 * 922421 * 2
def baseEnd_922421 : Nat := 421018078934258450929217

theorem tailTrace_922421 : CollatzResearch.WordTrace tailWord_922421 prefixEnd_922421 421018078934258450929217 := by
  unfold tailWord_922421
  simp only [CollatzResearch.WordTrace]
  refine ⟨33643457791233728809751117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22428971860822485873167411 33643457791233728809751117)
  ·
    refine ⟨12616296671712648303656669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33643457791233728809751117 12616296671712648303656669)
    ·
      refine ⟨4731111251892243113871251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12616296671712648303656669 4731111251892243113871251)
      ·
        refine ⟨7096666877838364670806877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4731111251892243113871251 7096666877838364670806877)
        ·
          refine ⟨2661250079189386751552579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7096666877838364670806877 2661250079189386751552579)
          ·
            refine ⟨3991875118784080127328869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2661250079189386751552579 3991875118784080127328869)
            ·
              refine ⟨748476584772015023874163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3991875118784080127328869 748476584772015023874163)
              ·
                refine ⟨1122714877158022535811245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 748476584772015023874163 1122714877158022535811245)
                ·
                  refine ⟨421018078934258450929217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1122714877158022535811245 421018078934258450929217)
                  ·
                    rfl

theorem cell20_922421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 4, 1, 3].length) (baseStart_922421 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_922421 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_922421 prefixEnd_922421 := by exact prefixLift 922421
  have htrace : WordTrace (prefixWord ++ tailWord_922421) baseStart_922421 baseEnd_922421 := by
    simpa [prefixWord, tailWord_922421, baseEnd_922421] using wordTrace_append hprefix tailTrace_922421
  have hstable : (prefixWord ++ tailWord_922421).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922421).length < 2 ^ (prefixWord ++ tailWord_922421).sum := by decide
  have hdescent : baseEnd_922421 < baseStart_922421 := by decide
  rcases family_descends (prefixWord ++ tailWord_922421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922432 : List Nat := [2, 1, 1, 2, 2, 1, 1, 6, 4]
def baseStart_922432 : Nat := 118140960795 + 922432 * 2 ^ 59
def prefixEnd_922432 : Nat := 4983230072969 + 3 ^ 40 * 922432 * 2
def baseEnd_922432 : Nat := 421023099633991301562505

theorem tailTrace_922432 : CollatzResearch.WordTrace tailWord_922432 prefixEnd_922432 421023099633991301562505 := by
  unfold tailWord_922432
  simp only [CollatzResearch.WordTrace]
  refine ⟨16821929497096938844200775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22429239329462585125601033 16821929497096938844200775)
  ·
    refine ⟨25232894245645408266301163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16821929497096938844200775 25232894245645408266301163)
    ·
      refine ⟨37849341368468112399451745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25232894245645408266301163 37849341368468112399451745)
      ·
        refine ⟨28387006026351084299588809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37849341368468112399451745 28387006026351084299588809)
        ·
          refine ⟨21290254519763313224691607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28387006026351084299588809 21290254519763313224691607)
          ·
            refine ⟨31935381779644969837037411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21290254519763313224691607 31935381779644969837037411)
            ·
              refine ⟨47903072669467454755556117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31935381779644969837037411 47903072669467454755556117)
              ·
                refine ⟨2245456531381286941666693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 47903072669467454755556117 2245456531381286941666693)
                ·
                  refine ⟨421023099633991301562505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2245456531381286941666693 421023099633991301562505)
                  ·
                    rfl

theorem cell20_922432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 6, 4].length) (baseStart_922432 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_922432 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_922432 prefixEnd_922432 := by exact prefixLift 922432
  have htrace : WordTrace (prefixWord ++ tailWord_922432) baseStart_922432 baseEnd_922432 := by
    simpa [prefixWord, tailWord_922432, baseEnd_922432] using wordTrace_append hprefix tailTrace_922432
  have hstable : (prefixWord ++ tailWord_922432).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922432).length < 2 ^ (prefixWord ++ tailWord_922432).sum := by decide
  have hdescent : baseEnd_922432 < baseStart_922432 := by decide
  rcases family_descends (prefixWord ++ tailWord_922432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922504 : List Nat := [2, 1, 3, 3, 2, 1, 1, 5, 2]
def baseStart_922504 : Nat := 118140960795 + 922504 * 2 ^ 59
def prefixEnd_922504 : Nat := 4983230072969 + 3 ^ 40 * 922504 * 2
def baseEnd_922504 : Nat := 421055962395879051162211

theorem tailTrace_922504 : CollatzResearch.WordTrace tailWord_922504 prefixEnd_922504 421055962395879051162211 := by
  unfold tailWord_922504
  simp only [CollatzResearch.WordTrace]
  refine ⟨16823242524966516992511283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22430990033288689323348377 16823242524966516992511283)
  ·
    refine ⟨25234863787449775488766925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16823242524966516992511283 25234863787449775488766925)
    ·
      refine ⟨9463073920293665808287597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25234863787449775488766925 9463073920293665808287597)
      ·
        refine ⟨3548652720110124678107849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9463073920293665808287597 3548652720110124678107849)
        ·
          refine ⟨2661489540082593508580887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3548652720110124678107849 2661489540082593508580887)
          ·
            refine ⟨3992234310123890262871331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2661489540082593508580887 3992234310123890262871331)
            ·
              refine ⟨5988351465185835394306997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3992234310123890262871331 5988351465185835394306997)
              ·
                refine ⟨561407949861172068216281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5988351465185835394306997 561407949861172068216281)
                ·
                  refine ⟨421055962395879051162211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 561407949861172068216281 421055962395879051162211)
                  ·
                    rfl

theorem cell20_922504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 5, 2].length) (baseStart_922504 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_922504 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_922504 prefixEnd_922504 := by exact prefixLift 922504
  have htrace : WordTrace (prefixWord ++ tailWord_922504) baseStart_922504 baseEnd_922504 := by
    simpa [prefixWord, tailWord_922504, baseEnd_922504] using wordTrace_append hprefix tailTrace_922504
  have hstable : (prefixWord ++ tailWord_922504).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922504).length < 2 ^ (prefixWord ++ tailWord_922504).sum := by decide
  have hdescent : baseEnd_922504 < baseStart_922504 := by decide
  rcases family_descends (prefixWord ++ tailWord_922504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922514 : List Nat := [3, 2, 3, 2, 2, 2, 1, 2, 3]
def baseStart_922514 : Nat := 118140960795 + 922514 * 2 ^ 59
def prefixEnd_922514 : Nat := 4983230072969 + 3 ^ 40 * 922514 * 2
def baseEnd_922514 : Nat := 421060526668363460828837

theorem tailTrace_922514 : CollatzResearch.WordTrace tailWord_922514 prefixEnd_922514 421060526668363460828837 := by
  unfold tailWord_922514
  simp only [CollatzResearch.WordTrace]
  refine ⟨8411712444974201423221649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22431233186597870461924397 8411712444974201423221649)
  ·
    refine ⟨6308784333730651067416237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8411712444974201423221649 6308784333730651067416237)
    ·
      refine ⟨2365794125148994150281089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6308784333730651067416237 2365794125148994150281089)
      ·
        refine ⟨1774345593861745612710817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2365794125148994150281089 1774345593861745612710817)
        ·
          refine ⟨1330759195396309209533113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1774345593861745612710817 1330759195396309209533113)
          ·
            refine ⟨998069396547231907149835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1330759195396309209533113 998069396547231907149835)
            ·
              refine ⟨1497104094820847860724753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 998069396547231907149835 1497104094820847860724753)
              ·
                refine ⟨1122828071115635895543565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1497104094820847860724753 1122828071115635895543565)
                ·
                  refine ⟨421060526668363460828837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1122828071115635895543565 421060526668363460828837)
                  ·
                    rfl

theorem cell20_922514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 1, 2, 3].length) (baseStart_922514 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_922514 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_922514 prefixEnd_922514 := by exact prefixLift 922514
  have htrace : WordTrace (prefixWord ++ tailWord_922514) baseStart_922514 baseEnd_922514 := by
    simpa [prefixWord, tailWord_922514, baseEnd_922514] using wordTrace_append hprefix tailTrace_922514
  have hstable : (prefixWord ++ tailWord_922514).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922514).length < 2 ^ (prefixWord ++ tailWord_922514).sum := by decide
  have hdescent : baseEnd_922514 < baseStart_922514 := by decide
  rcases family_descends (prefixWord ++ tailWord_922514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922525 : List Nat := [1, 4, 2, 1, 2, 1, 4, 1, 4]
def baseStart_922525 : Nat := 118140960795 + 922525 * 2 ^ 59
def prefixEnd_922525 : Nat := 4983230072969 + 3 ^ 40 * 922525 * 2
def baseEnd_922525 : Nat := 421065547368096311462125

theorem tailTrace_922525 : CollatzResearch.WordTrace tailWord_922525 prefixEnd_922525 421065547368096311462125 := by
  unfold tailWord_922525
  simp only [CollatzResearch.WordTrace]
  refine ⟨33647250982856954571537029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22431500655237969714358019 33647250982856954571537029)
  ·
    refine ⟨6308859559285678982163193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33647250982856954571537029 6308859559285678982163193)
    ·
      refine ⟨4731644669464259236622395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6308859559285678982163193 4731644669464259236622395)
      ·
        refine ⟨7097467004196388854933593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4731644669464259236622395 7097467004196388854933593)
        ·
          refine ⟨5323100253147291641200195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7097467004196388854933593 5323100253147291641200195)
          ·
            refine ⟨7984650379720937461800293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5323100253147291641200195 7984650379720937461800293)
            ·
              refine ⟨1497121946197675774087555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7984650379720937461800293 1497121946197675774087555)
              ·
                refine ⟨2245682919296513661131333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1497121946197675774087555 2245682919296513661131333)
                ·
                  refine ⟨421065547368096311462125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2245682919296513661131333 421065547368096311462125)
                  ·
                    rfl

theorem cell20_922525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 4, 1, 4].length) (baseStart_922525 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_922525 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_922525 prefixEnd_922525 := by exact prefixLift 922525
  have htrace : WordTrace (prefixWord ++ tailWord_922525) baseStart_922525 baseEnd_922525 := by
    simpa [prefixWord, tailWord_922525, baseEnd_922525] using wordTrace_append hprefix tailTrace_922525
  have hstable : (prefixWord ++ tailWord_922525).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922525).length < 2 ^ (prefixWord ++ tailWord_922525).sum := by decide
  have hdescent : baseEnd_922525 < baseStart_922525 := by decide
  rcases family_descends (prefixWord ++ tailWord_922525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922577 : List Nat := [1, 2, 2, 1, 2, 1, 4, 4, 3]
def baseStart_922577 : Nat := 118140960795 + 922577 * 2 ^ 59
def prefixEnd_922577 : Nat := 4983230072969 + 3 ^ 40 * 922577 * 2
def baseEnd_922577 : Nat := 421089281585015241728579

theorem tailTrace_922577 : CollatzResearch.WordTrace tailWord_922577 prefixEnd_922577 421089281585015241728579 := by
  unfold tailWord_922577
  simp only [CollatzResearch.WordTrace]
  refine ⟨33649147578668567452429985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22432765052445711634953323 33649147578668567452429985)
  ·
    refine ⟨25236860684001425589322489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33649147578668567452429985 25236860684001425589322489)
    ·
      refine ⟨18927645513001069191991867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25236860684001425589322489 18927645513001069191991867)
      ·
        refine ⟨28391468269501603787987801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18927645513001069191991867 28391468269501603787987801)
        ·
          refine ⟨21293601202126202840990851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28391468269501603787987801 21293601202126202840990851)
          ·
            refine ⟨31940401803189304261486277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21293601202126202840990851 31940401803189304261486277)
            ·
              refine ⟨5988825338097994549028677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31940401803189304261486277 5988825338097994549028677)
              ·
                refine ⟨1122904750893373977942877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5988825338097994549028677 1122904750893373977942877)
                ·
                  refine ⟨421089281585015241728579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1122904750893373977942877 421089281585015241728579)
                  ·
                    rfl

theorem cell20_922577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 4, 3].length) (baseStart_922577 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_922577 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_922577 prefixEnd_922577 := by exact prefixLift 922577
  have htrace : WordTrace (prefixWord ++ tailWord_922577) baseStart_922577 baseEnd_922577 := by
    simpa [prefixWord, tailWord_922577, baseEnd_922577] using wordTrace_append hprefix tailTrace_922577
  have hstable : (prefixWord ++ tailWord_922577).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922577).length < 2 ^ (prefixWord ++ tailWord_922577).sum := by decide
  have hdescent : baseEnd_922577 < baseStart_922577 := by decide
  rcases family_descends (prefixWord ++ tailWord_922577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922580 : List Nat := [2, 4, 1, 2, 1, 4, 1, 1, 4]
def baseStart_922580 : Nat := 118140960795 + 922580 * 2 ^ 59
def prefixEnd_922580 : Nat := 4983230072969 + 3 ^ 40 * 922580 * 2
def baseEnd_922580 : Nat := 421090650866760564628567

theorem tailTrace_922580 : CollatzResearch.WordTrace tailWord_922580 prefixEnd_922580 421090650866760564628567 := by
  unfold tailWord_922580
  simp only [CollatzResearch.WordTrace]
  refine ⟨16824628498828849482394597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22432837998438465976526129 16824628498828849482394597)
  ·
    refine ⟨3154617843530409277948987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16824628498828849482394597 3154617843530409277948987)
    ·
      refine ⟨4731926765295613916923481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3154617843530409277948987 4731926765295613916923481)
      ·
        refine ⟨3548945073971710437692611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4731926765295613916923481 3548945073971710437692611)
        ·
          refine ⟨5323417610957565656538917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3548945073971710437692611 5323417610957565656538917)
          ·
            refine ⟨998140802054543560601047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5323417610957565656538917 998140802054543560601047)
            ·
              refine ⟨1497211203081815340901571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 998140802054543560601047 1497211203081815340901571)
              ·
                refine ⟨2245816804622723011352357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1497211203081815340901571 2245816804622723011352357)
                ·
                  refine ⟨421090650866760564628567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2245816804622723011352357 421090650866760564628567)
                  ·
                    rfl

theorem cell20_922580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 1, 1, 4].length) (baseStart_922580 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_922580 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_922580 prefixEnd_922580 := by exact prefixLift 922580
  have htrace : WordTrace (prefixWord ++ tailWord_922580) baseStart_922580 baseEnd_922580 := by
    simpa [prefixWord, tailWord_922580, baseEnd_922580] using wordTrace_append hprefix tailTrace_922580
  have hstable : (prefixWord ++ tailWord_922580).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922580).length < 2 ^ (prefixWord ++ tailWord_922580).sum := by decide
  have hdescent : baseEnd_922580 < baseStart_922580 := by decide
  rcases family_descends (prefixWord ++ tailWord_922580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922632 : List Nat := [2, 1, 3, 2, 1, 4, 2, 2, 3]
def baseStart_922632 : Nat := 118140960795 + 922632 * 2 ^ 59
def prefixEnd_922632 : Nat := 4983230072969 + 3 ^ 40 * 922632 * 2
def baseEnd_922632 : Nat := 421114385083679494895021

theorem tailTrace_922632 : CollatzResearch.WordTrace tailWord_922632 prefixEnd_922632 421114385083679494895021 := by
  unfold tailWord_922632
  simp only [CollatzResearch.WordTrace]
  refine ⟨16825576796734655922841075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22434102395646207897121433 16825576796734655922841075)
  ·
    refine ⟨25238365195101983884261613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16825576796734655922841075 25238365195101983884261613)
    ·
      refine ⟨9464386948163243956598105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25238365195101983884261613 9464386948163243956598105)
      ·
        refine ⟨7098290211122432967448579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9464386948163243956598105 7098290211122432967448579)
        ·
          refine ⟨10647435316683649451172869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7098290211122432967448579 10647435316683649451172869)
          ·
            refine ⟨1996394121878184272094913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10647435316683649451172869 1996394121878184272094913)
            ·
              refine ⟨1497295591408638204071185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1996394121878184272094913 1497295591408638204071185)
              ·
                refine ⟨1122971693556478653053389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1497295591408638204071185 1122971693556478653053389)
                ·
                  refine ⟨421114385083679494895021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1122971693556478653053389 421114385083679494895021)
                  ·
                    rfl

theorem cell20_922632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 2, 2, 3].length) (baseStart_922632 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_922632 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_922632 prefixEnd_922632 := by exact prefixLift 922632
  have htrace : WordTrace (prefixWord ++ tailWord_922632) baseStart_922632 baseEnd_922632 := by
    simpa [prefixWord, tailWord_922632, baseEnd_922632] using wordTrace_append hprefix tailTrace_922632
  have hstable : (prefixWord ++ tailWord_922632).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922632).length < 2 ^ (prefixWord ++ tailWord_922632).sum := by decide
  have hdescent : baseEnd_922632 < baseStart_922632 := by decide
  rcases family_descends (prefixWord ++ tailWord_922632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922635 : List Nat := [1, 1, 1, 1, 6, 4, 2, 2, 2]
def baseStart_922635 : Nat := 118140960795 + 922635 * 2 ^ 59
def prefixEnd_922635 : Nat := 4983230072969 + 3 ^ 40 * 922635 * 2
def baseEnd_922635 : Nat := 421115754365424817795009

theorem tailTrace_922635 : CollatzResearch.WordTrace tailWord_922635 prefixEnd_922635 421115754365424817795009 := by
  unfold tailWord_922635
  simp only [CollatzResearch.WordTrace]
  refine ⟨33651263012458443358041359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22434175341638962238694239 33651263012458443358041359)
  ·
    refine ⟨50476894518687665037062039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33651263012458443358041359 50476894518687665037062039)
    ·
      refine ⟨75715341778031497555593059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50476894518687665037062039 75715341778031497555593059)
      ·
        refine ⟨113573012667047246333389589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75715341778031497555593059 113573012667047246333389589)
        ·
          refine ⟨5323734968767839671877637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 113573012667047246333389589 5323734968767839671877637)
          ·
            refine ⟨998200306643969938477057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5323734968767839671877637 998200306643969938477057)
            ·
              refine ⟨748650229982977453857793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 998200306643969938477057 748650229982977453857793)
              ·
                refine ⟨561487672487233090393345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 748650229982977453857793 561487672487233090393345)
                ·
                  refine ⟨421115754365424817795009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 561487672487233090393345 421115754365424817795009)
                  ·
                    rfl

theorem cell20_922635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 2, 2, 2].length) (baseStart_922635 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_922635 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_922635 prefixEnd_922635 := by exact prefixLift 922635
  have htrace : WordTrace (prefixWord ++ tailWord_922635) baseStart_922635 baseEnd_922635 := by
    simpa [prefixWord, tailWord_922635, baseEnd_922635] using wordTrace_append hprefix tailTrace_922635
  have hstable : (prefixWord ++ tailWord_922635).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922635).length < 2 ^ (prefixWord ++ tailWord_922635).sum := by decide
  have hdescent : baseEnd_922635 < baseStart_922635 := by decide
  rcases family_descends (prefixWord ++ tailWord_922635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922656 : List Nat := [2, 1, 1, 7, 1, 1, 1, 2, 4]
def baseStart_922656 : Nat := 118140960795 + 922656 * 2 ^ 59
def prefixEnd_922656 : Nat := 4983230072969 + 3 ^ 40 * 922656 * 2
def baseEnd_922656 : Nat := 421125339337642078094923

theorem tailTrace_922656 : CollatzResearch.WordTrace tailWord_922656 prefixEnd_922656 421125339337642078094923 := by
  unfold tailWord_922656
  simp only [CollatzResearch.WordTrace]
  refine ⟨16826014472691181972277911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22434685963588242629703881 16826014472691181972277911)
  ·
    refine ⟨25239021709036772958416867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16826014472691181972277911 25239021709036772958416867)
    ·
      refine ⟨37858532563555159437625301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25239021709036772958416867 37858532563555159437625301)
      ·
        refine ⟨887309356958324049319343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 37858532563555159437625301 887309356958324049319343)
        ·
          refine ⟨1330964035437486073979015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 887309356958324049319343 1330964035437486073979015)
          ·
            refine ⟨1996446053156229110968523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1330964035437486073979015 1996446053156229110968523)
            ·
              refine ⟨2994669079734343666452785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1996446053156229110968523 2994669079734343666452785)
              ·
                refine ⟨2246001809800757749839589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2994669079734343666452785 2246001809800757749839589)
                ·
                  refine ⟨421125339337642078094923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2246001809800757749839589 421125339337642078094923)
                  ·
                    rfl

theorem cell20_922656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 2, 4].length) (baseStart_922656 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_922656 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_922656 prefixEnd_922656 := by exact prefixLift 922656
  have htrace : WordTrace (prefixWord ++ tailWord_922656) baseStart_922656 baseEnd_922656 := by
    simpa [prefixWord, tailWord_922656, baseEnd_922656] using wordTrace_append hprefix tailTrace_922656
  have hstable : (prefixWord ++ tailWord_922656).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922656).length < 2 ^ (prefixWord ++ tailWord_922656).sum := by decide
  have hdescent : baseEnd_922656 < baseStart_922656 := by decide
  rcases family_descends (prefixWord ++ tailWord_922656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922694 : List Nat := [6, 1, 1, 1, 1, 2, 1, 3, 4]
def baseStart_922694 : Nat := 118140960795 + 922694 * 2 ^ 59
def prefixEnd_922694 : Nat := 4983230072969 + 3 ^ 40 * 922694 * 2
def baseEnd_922694 : Nat := 421142683573082834828101

theorem tailTrace_922694 : CollatzResearch.WordTrace tailWord_922694 prefixEnd_922694 421142683573082834828101 := by
  unfold tailWord_922694
  simp only [CollatzResearch.WordTrace]
  refine ⟨1051669216226396763576223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 22435609946163130956292757 1051669216226396763576223)
  ·
    refine ⟨1577503824339595145364335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1051669216226396763576223 1577503824339595145364335)
    ·
      refine ⟨2366255736509392718046503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1577503824339595145364335 2366255736509392718046503)
      ·
        refine ⟨3549383604764089077069755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2366255736509392718046503 3549383604764089077069755)
        ·
          refine ⟨5324075407146133615604633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3549383604764089077069755 5324075407146133615604633)
          ·
            refine ⟨3993056555359600211703475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5324075407146133615604633 3993056555359600211703475)
            ·
              refine ⟨5989584833039400317555213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3993056555359600211703475 5989584833039400317555213)
              ·
                refine ⟨2246094312389775119083205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5989584833039400317555213 2246094312389775119083205)
                ·
                  refine ⟨421142683573082834828101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2246094312389775119083205 421142683573082834828101)
                  ·
                    rfl

theorem cell20_922694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_922694 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_922694 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_922694 prefixEnd_922694 := by exact prefixLift 922694
  have htrace : WordTrace (prefixWord ++ tailWord_922694) baseStart_922694 baseEnd_922694 := by
    simpa [prefixWord, tailWord_922694, baseEnd_922694] using wordTrace_append hprefix tailTrace_922694
  have hstable : (prefixWord ++ tailWord_922694).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922694).length < 2 ^ (prefixWord ++ tailWord_922694).sum := by decide
  have hdescent : baseEnd_922694 < baseStart_922694 := by decide
  rcases family_descends (prefixWord ++ tailWord_922694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922698 : List Nat := [3, 1, 2, 1, 1, 2, 3, 3, 4]
def baseStart_922698 : Nat := 118140960795 + 922698 * 2 ^ 59
def prefixEnd_922698 : Nat := 4983230072969 + 3 ^ 40 * 922698 * 2
def baseEnd_922698 : Nat := 421144509282076598694751

theorem tailTrace_922698 : CollatzResearch.WordTrace tailWord_922698 prefixEnd_922698 421144509282076598694751 := by
  unfold tailWord_922698
  simp only [CollatzResearch.WordTrace]
  refine ⟨8413390202807551279396187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22435707207486803411723165 8413390202807551279396187)
  ·
    refine ⟨12620085304211326919094281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8413390202807551279396187 12620085304211326919094281)
    ·
      refine ⟨9465063978158495189320711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12620085304211326919094281 9465063978158495189320711)
      ·
        refine ⟨14197595967237742783981067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9465063978158495189320711 14197595967237742783981067)
        ·
          refine ⟨21296393950856614175971601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14197595967237742783981067 21296393950856614175971601)
          ·
            refine ⟨15972295463142460631978701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21296393950856614175971601 15972295463142460631978701)
            ·
              refine ⟨5989610798678422736992013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15972295463142460631978701 5989610798678422736992013)
              ·
                refine ⟨2246104049504408526372005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5989610798678422736992013 2246104049504408526372005)
                ·
                  refine ⟨421144509282076598694751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2246104049504408526372005 421144509282076598694751)
                  ·
                    rfl

theorem cell20_922698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 3, 4].length) (baseStart_922698 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_922698 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_922698 prefixEnd_922698 := by exact prefixLift 922698
  have htrace : WordTrace (prefixWord ++ tailWord_922698) baseStart_922698 baseEnd_922698 := by
    simpa [prefixWord, tailWord_922698, baseEnd_922698] using wordTrace_append hprefix tailTrace_922698
  have hstable : (prefixWord ++ tailWord_922698).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922698).length < 2 ^ (prefixWord ++ tailWord_922698).sum := by decide
  have hdescent : baseEnd_922698 < baseStart_922698 := by decide
  rcases family_descends (prefixWord ++ tailWord_922698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922718 : List Nat := [4, 4, 1, 1, 1, 2, 1, 6]
def baseStart_922718 : Nat := 118140960795 + 922718 * 2 ^ 59
def prefixEnd_922718 : Nat := 4983230072969 + 3 ^ 40 * 922718 * 2
def baseEnd_922718 : Nat := 140384545942348472676001

theorem tailTrace_922718 : CollatzResearch.WordTrace tailWord_922718 prefixEnd_922718 140384545942348472676001 := by
  unfold tailWord_922718
  simp only [CollatzResearch.WordTrace]
  refine ⟨4206786283894718566664101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22436193514105165688875205 4206786283894718566664101)
  ·
    refine ⟨788772428230259731249519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4206786283894718566664101 788772428230259731249519)
    ·
      refine ⟨1183158642345389596874279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 788772428230259731249519 1183158642345389596874279)
      ·
        refine ⟨1774737963518084395311419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1183158642345389596874279 1774737963518084395311419)
        ·
          refine ⟨2662106945277126592967129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1774737963518084395311419 2662106945277126592967129)
          ·
            refine ⟨1996580208957844944725347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2662106945277126592967129 1996580208957844944725347)
            ·
              refine ⟨2994870313436767417088021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1996580208957844944725347 2994870313436767417088021)
              ·
                refine ⟨140384545942348472676001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2994870313436767417088021 140384545942348472676001)
                ·
                  rfl

theorem cell20_922718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 6].length) (baseStart_922718 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_922718 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_922718 prefixEnd_922718 := by exact prefixLift 922718
  have htrace : WordTrace (prefixWord ++ tailWord_922718) baseStart_922718 baseEnd_922718 := by
    simpa [prefixWord, tailWord_922718, baseEnd_922718] using wordTrace_append hprefix tailTrace_922718
  have hstable : (prefixWord ++ tailWord_922718).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922718).length < 2 ^ (prefixWord ++ tailWord_922718).sum := by decide
  have hdescent : baseEnd_922718 < baseStart_922718 := by decide
  rcases family_descends (prefixWord ++ tailWord_922718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922728 : List Nat := [2, 1, 4, 4, 1, 2, 1, 3, 2]
def baseStart_922728 : Nat := 118140960795 + 922728 * 2 ^ 59
def prefixEnd_922728 : Nat := 4983230072969 + 3 ^ 40 * 922728 * 2
def baseEnd_922728 : Nat := 421158202099529827694629

theorem tailTrace_922728 : CollatzResearch.WordTrace tailWord_922728 prefixEnd_922728 421158202099529827694629 := by
  unfold tailWord_922728
  simp only [CollatzResearch.WordTrace]
  refine ⟨16827327500560760120588419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22436436667414346827451225 16827327500560760120588419)
  ·
    refine ⟨25240991250841140180882629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16827327500560760120588419 25240991250841140180882629)
    ·
      refine ⟨4732685859532713783915493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25240991250841140180882629 4732685859532713783915493)
      ·
        refine ⟨887378598662383834484155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4732685859532713783915493 887378598662383834484155)
        ·
          refine ⟨1331067897993575751726233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 887378598662383834484155 1331067897993575751726233)
          ·
            refine ⟨998300923495181813794675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1331067897993575751726233 998300923495181813794675)
            ·
              refine ⟨1497451385242772720692013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 998300923495181813794675 1497451385242772720692013)
              ·
                refine ⟨561544269466039770259505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1497451385242772720692013 561544269466039770259505)
                ·
                  refine ⟨421158202099529827694629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 561544269466039770259505 421158202099529827694629)
                  ·
                    rfl

theorem cell20_922728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 1, 3, 2].length) (baseStart_922728 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_922728 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_922728 prefixEnd_922728 := by exact prefixLift 922728
  have htrace : WordTrace (prefixWord ++ tailWord_922728) baseStart_922728 baseEnd_922728 := by
    simpa [prefixWord, tailWord_922728, baseEnd_922728] using wordTrace_append hprefix tailTrace_922728
  have hstable : (prefixWord ++ tailWord_922728).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922728).length < 2 ^ (prefixWord ++ tailWord_922728).sum := by decide
  have hdescent : baseEnd_922728 < baseStart_922728 := by decide
  rcases family_descends (prefixWord ++ tailWord_922728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922753 : List Nat := [1, 2, 4, 2, 2, 1, 3, 1, 4]
def baseStart_922753 : Nat := 118140960795 + 922753 * 2 ^ 59
def prefixEnd_922753 : Nat := 4983230072969 + 3 ^ 40 * 922753 * 2
def baseEnd_922753 : Nat := 421169612780740851861193

theorem tailTrace_922753 : CollatzResearch.WordTrace tailWord_922753 prefixEnd_922753 421169612780740851861193 := by
  unfold tailWord_922753
  simp only [CollatzResearch.WordTrace]
  refine ⟨33655566826030949510836913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22437044550687299673891275 33655566826030949510836913)
  ·
    refine ⟨25241675119523212133127685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33655566826030949510836913 25241675119523212133127685)
    ·
      refine ⟨4732814084910602274961441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25241675119523212133127685 4732814084910602274961441)
      ·
        refine ⟨3549610563682951706221081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4732814084910602274961441 3549610563682951706221081)
        ·
          refine ⟨2662207922762213779665811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3549610563682951706221081 2662207922762213779665811)
          ·
            refine ⟨3993311884143320669498717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2662207922762213779665811 3993311884143320669498717)
            ·
              refine ⟨1497491956553745251062019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3993311884143320669498717 1497491956553745251062019)
              ·
                refine ⟨2246237934830617876593029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1497491956553745251062019 2246237934830617876593029)
                ·
                  refine ⟨421169612780740851861193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2246237934830617876593029 421169612780740851861193)
                  ·
                    rfl

theorem cell20_922753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 3, 1, 4].length) (baseStart_922753 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_922753 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_922753 prefixEnd_922753 := by exact prefixLift 922753
  have htrace : WordTrace (prefixWord ++ tailWord_922753) baseStart_922753 baseEnd_922753 := by
    simpa [prefixWord, tailWord_922753, baseEnd_922753] using wordTrace_append hprefix tailTrace_922753
  have hstable : (prefixWord ++ tailWord_922753).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922753).length < 2 ^ (prefixWord ++ tailWord_922753).sum := by decide
  have hdescent : baseEnd_922753 < baseStart_922753 := by decide
  rcases family_descends (prefixWord ++ tailWord_922753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922781 : List Nat := [1, 4, 2, 1, 1, 2, 1, 8]
def baseStart_922781 : Nat := 118140960795 + 922781 * 2 ^ 59
def prefixEnd_922781 : Nat := 4983230072969 + 3 ^ 40 * 922781 * 2
def baseEnd_922781 : Nat := 140394130914565732975915

theorem tailTrace_922781 : CollatzResearch.WordTrace tailWord_922781 prefixEnd_922781 140394130914565732975915 := by
  unfold tailWord_922781
  simp only [CollatzResearch.WordTrace]
  refine ⟨33656588069929510292856197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22437725379953006861904131 33656588069929510292856197)
  ·
    refine ⟨6310610263111783179910537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33656588069929510292856197 6310610263111783179910537)
    ·
      refine ⟨4732957697333837384932903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6310610263111783179910537 4732957697333837384932903)
      ·
        refine ⟨7099436546000756077399355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4732957697333837384932903 7099436546000756077399355)
        ·
          refine ⟨10649154819001134116099033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7099436546000756077399355 10649154819001134116099033)
          ·
            refine ⟨7986866114250850587074275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10649154819001134116099033 7986866114250850587074275)
            ·
              refine ⟨11980299171376275880611413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7986866114250850587074275 11980299171376275880611413)
              ·
                refine ⟨140394130914565732975915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11980299171376275880611413 140394130914565732975915)
                ·
                  rfl

theorem cell20_922781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 8].length) (baseStart_922781 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_922781 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_922781 prefixEnd_922781 := by exact prefixLift 922781
  have htrace : WordTrace (prefixWord ++ tailWord_922781) baseStart_922781 baseEnd_922781 := by
    simpa [prefixWord, tailWord_922781, baseEnd_922781] using wordTrace_append hprefix tailTrace_922781
  have hstable : (prefixWord ++ tailWord_922781).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922781).length < 2 ^ (prefixWord ++ tailWord_922781).sum := by decide
  have hdescent : baseEnd_922781 < baseStart_922781 := by decide
  rcases family_descends (prefixWord ++ tailWord_922781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922860 : List Nat := [2, 2, 1, 1, 2, 6, 1, 2, 3]
def baseStart_922860 : Nat := 118140960795 + 922860 * 2 ^ 59
def prefixEnd_922860 : Nat := 4983230072969 + 3 ^ 40 * 922860 * 2
def baseEnd_922860 : Nat := 421218450496324035294089

theorem tailTrace_922860 : CollatzResearch.WordTrace tailWord_922860 prefixEnd_922860 421218450496324035294089 := by
  unfold tailWord_922860
  simp only [CollatzResearch.WordTrace]
  refine ⟨16829734718321653392491017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22439646291095537856654689 16829734718321653392491017)
  ·
    refine ⟨12622301038741240044368263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16829734718321653392491017 12622301038741240044368263)
    ·
      refine ⟨18933451558111860066552395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12622301038741240044368263 18933451558111860066552395)
      ·
        refine ⟨28400177337167790099828593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18933451558111860066552395 28400177337167790099828593)
        ·
          refine ⟨21300133002875842574871445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28400177337167790099828593 21300133002875842574871445)
          ·
            refine ⟨998443734509805120697099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 21300133002875842574871445 998443734509805120697099)
            ·
              refine ⟨1497665601764707681045649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 998443734509805120697099 1497665601764707681045649)
              ·
                refine ⟨1123249201323530760784237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1497665601764707681045649 1123249201323530760784237)
                ·
                  refine ⟨421218450496324035294089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1123249201323530760784237 421218450496324035294089)
                  ·
                    rfl

theorem cell20_922860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 3].length) (baseStart_922860 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_922860 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_922860 prefixEnd_922860 := by exact prefixLift 922860
  have htrace : WordTrace (prefixWord ++ tailWord_922860) baseStart_922860 baseEnd_922860 := by
    simpa [prefixWord, tailWord_922860, baseEnd_922860] using wordTrace_append hprefix tailTrace_922860
  have hstable : (prefixWord ++ tailWord_922860).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922860).length < 2 ^ (prefixWord ++ tailWord_922860).sum := by decide
  have hdescent : baseEnd_922860 < baseStart_922860 := by decide
  rcases family_descends (prefixWord ++ tailWord_922860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922867 : List Nat := [1, 1, 1, 2, 2, 5, 2, 4, 2]
def baseStart_922867 : Nat := 118140960795 + 922867 * 2 ^ 59
def prefixEnd_922867 : Nat := 4983230072969 + 3 ^ 40 * 922867 * 2
def baseEnd_922867 : Nat := 421221645487063122060727

theorem tailTrace_922867 : CollatzResearch.WordTrace tailWord_922867 prefixEnd_922867 421221645487063122060727 := by
  unfold tailWord_922867
  simp only [CollatzResearch.WordTrace]
  refine ⟨33659724747617946980486855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22439816498411964653657903 33659724747617946980486855)
  ·
    refine ⟨50489587121426920470730283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33659724747617946980486855 50489587121426920470730283)
    ·
      refine ⟨75734380682140380706095425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50489587121426920470730283 75734380682140380706095425)
      ·
        refine ⟨56800785511605285529571569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75734380682140380706095425 56800785511605285529571569)
        ·
          refine ⟨42600589133703964147178677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56800785511605285529571569 42600589133703964147178677)
          ·
            refine ⟨3993805231284746638798001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42600589133703964147178677 3993805231284746638798001)
            ·
              refine ⟨2995353923463559979098501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3993805231284746638798001 2995353923463559979098501)
              ·
                refine ⟨561628860649417496080969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2995353923463559979098501 561628860649417496080969)
                ·
                  refine ⟨421221645487063122060727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 561628860649417496080969 421221645487063122060727)
                  ·
                    rfl

theorem cell20_922867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 4, 2].length) (baseStart_922867 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_922867 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_922867 prefixEnd_922867 := by exact prefixLift 922867
  have htrace : WordTrace (prefixWord ++ tailWord_922867) baseStart_922867 baseEnd_922867 := by
    simpa [prefixWord, tailWord_922867, baseEnd_922867] using wordTrace_append hprefix tailTrace_922867
  have hstable : (prefixWord ++ tailWord_922867).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922867).length < 2 ^ (prefixWord ++ tailWord_922867).sum := by decide
  have hdescent : baseEnd_922867 < baseStart_922867 := by decide
  rcases family_descends (prefixWord ++ tailWord_922867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922871 : List Nat := [1, 1, 3, 1, 1, 1, 2, 2, 8]
def baseStart_922871 : Nat := 118140960795 + 922871 * 2 ^ 59
def prefixEnd_922871 : Nat := 4983230072969 + 3 ^ 40 * 922871 * 2
def baseEnd_922871 : Nat := 421223471196056885927377

theorem tailTrace_922871 : CollatzResearch.WordTrace tailWord_922871 prefixEnd_922871 421223471196056885927377 := by
  unfold tailWord_922871
  simp only [CollatzResearch.WordTrace]
  refine ⟨33659870639603455663632467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22439913759735637109088311 33659870639603455663632467)
  ·
    refine ⟨50489805959405183495448701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33659870639603455663632467 50489805959405183495448701)
    ·
      refine ⟨18933677234776943810793263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50489805959405183495448701 18933677234776943810793263)
      ·
        refine ⟨28400515852165415716189895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18933677234776943810793263 28400515852165415716189895)
        ·
          refine ⟨42600773778248123574284843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28400515852165415716189895 42600773778248123574284843)
          ·
            refine ⟨63901160667372185361427265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42600773778248123574284843 63901160667372185361427265)
            ·
              refine ⟨47925870500529139021070449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63901160667372185361427265 47925870500529139021070449)
              ·
                refine ⟨35944402875396854265802837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47925870500529139021070449 35944402875396854265802837)
                ·
                  refine ⟨421223471196056885927377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35944402875396854265802837 421223471196056885927377)
                  ·
                    rfl

theorem cell20_922871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 8].length) (baseStart_922871 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_922871 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_922871 prefixEnd_922871 := by exact prefixLift 922871
  have htrace : WordTrace (prefixWord ++ tailWord_922871) baseStart_922871 baseEnd_922871 := by
    simpa [prefixWord, tailWord_922871, baseEnd_922871] using wordTrace_append hprefix tailTrace_922871
  have hstable : (prefixWord ++ tailWord_922871).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922871).length < 2 ^ (prefixWord ++ tailWord_922871).sum := by decide
  have hdescent : baseEnd_922871 < baseStart_922871 := by decide
  rcases family_descends (prefixWord ++ tailWord_922871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922912 : List Nat := [2, 1, 1, 5, 3, 2, 6]
def baseStart_922912 : Nat := 118140960795 + 922912 * 2 ^ 59
def prefixEnd_922912 : Nat := 4983230072969 + 3 ^ 40 * 922912 * 2
def baseEnd_922912 : Nat := 46804687190360329506727

theorem tailTrace_922912 : CollatzResearch.WordTrace tailWord_922912 prefixEnd_922912 46804687190360329506727 := by
  unfold tailWord_922912
  simp only [CollatzResearch.WordTrace]
  refine ⟨16830683016227459832937495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22440910688303279777249993 16830683016227459832937495)
  ·
    refine ⟨25246024524341189749406243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16830683016227459832937495 25246024524341189749406243)
    ·
      refine ⟨37869036786511784624109365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25246024524341189749406243 37869036786511784624109365)
      ·
        refine ⟨3550222198735479808510253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37869036786511784624109365 3550222198735479808510253)
        ·
          refine ⟨1331333324525804928191345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3550222198735479808510253 1331333324525804928191345)
          ·
            refine ⟨998499993394353696143509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1331333324525804928191345 998499993394353696143509)
            ·
              refine ⟨46804687190360329506727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 998499993394353696143509 46804687190360329506727)
              ·
                rfl

theorem cell20_922912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 6].length) (baseStart_922912 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_922912 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_922912 prefixEnd_922912 := by exact prefixLift 922912
  have htrace : WordTrace (prefixWord ++ tailWord_922912) baseStart_922912 baseEnd_922912 := by
    simpa [prefixWord, tailWord_922912, baseEnd_922912] using wordTrace_append hprefix tailTrace_922912
  have hstable : (prefixWord ++ tailWord_922912).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922912).length < 2 ^ (prefixWord ++ tailWord_922912).sum := by decide
  have hdescent : baseEnd_922912 < baseStart_922912 := by decide
  rcases family_descends (prefixWord ++ tailWord_922912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922922 : List Nat := [3, 1, 4, 2, 1, 3, 1, 1, 4]
def baseStart_922922 : Nat := 118140960795 + 922922 * 2 ^ 59
def prefixEnd_922922 : Nat := 4983230072969 + 3 ^ 40 * 922922 * 2
def baseEnd_922922 : Nat := 421246748985727375227169

theorem tailTrace_922922 : CollatzResearch.WordTrace tailWord_922922 prefixEnd_922922 421246748985727375227169 := by
  unfold tailWord_922922
  simp only [CollatzResearch.WordTrace]
  refine ⟨8415432690604672843434755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22441153841612460915826013 8415432690604672843434755)
  ·
    refine ⟨12623149035907009265152133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8415432690604672843434755 12623149035907009265152133)
    ·
      refine ⟨2366840444232564237216025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12623149035907009265152133 2366840444232564237216025)
      ·
        refine ⟨1775130333174423177912019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2366840444232564237216025 1775130333174423177912019)
        ·
          refine ⟨2662695499761634766868029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1775130333174423177912019 2662695499761634766868029)
          ·
            refine ⟨998510812410613037575511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2662695499761634766868029 998510812410613037575511)
            ·
              refine ⟨1497766218615919556363267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 998510812410613037575511 1497766218615919556363267)
              ·
                refine ⟨2246649327923879334544901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1497766218615919556363267 2246649327923879334544901)
                ·
                  refine ⟨421246748985727375227169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2246649327923879334544901 421246748985727375227169)
                  ·
                    rfl

theorem cell20_922922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 1, 1, 4].length) (baseStart_922922 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_922922 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_922922 prefixEnd_922922 := by exact prefixLift 922922
  have htrace : WordTrace (prefixWord ++ tailWord_922922) baseStart_922922 baseEnd_922922 := by
    simpa [prefixWord, tailWord_922922, baseEnd_922922] using wordTrace_append hprefix tailTrace_922922
  have hstable : (prefixWord ++ tailWord_922922).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922922).length < 2 ^ (prefixWord ++ tailWord_922922).sum := by decide
  have hdescent : baseEnd_922922 < baseStart_922922 := by decide
  rcases family_descends (prefixWord ++ tailWord_922922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922933 : List Nat := [1, 3, 3, 1, 2, 2, 1, 7]
def baseStart_922933 : Nat := 118140960795 + 922933 * 2 ^ 59
def prefixEnd_922933 : Nat := 4983230072969 + 3 ^ 40 * 922933 * 2
def baseEnd_922933 : Nat := 140417256561820075286819

theorem tailTrace_922933 : CollatzResearch.WordTrace tailWord_922933 prefixEnd_922933 140417256561820075286819 := by
  unfold tailWord_922933
  simp only [CollatzResearch.WordTrace]
  refine ⟨33662131965378840252389453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22441421310252560168259635 33662131965378840252389453)
  ·
    refine ⟨12623299487017065094646045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33662131965378840252389453 12623299487017065094646045)
    ·
      refine ⟨4733737307631399410492267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12623299487017065094646045 4733737307631399410492267)
      ·
        refine ⟨7100605961447099115738401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4733737307631399410492267 7100605961447099115738401)
        ·
          refine ⟨5325454471085324336803801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7100605961447099115738401 5325454471085324336803801)
          ·
            refine ⟨3994090853313993252602851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5325454471085324336803801 3994090853313993252602851)
            ·
              refine ⟨5991136279970989878904277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3994090853313993252602851 5991136279970989878904277)
              ·
                refine ⟨140417256561820075286819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5991136279970989878904277 140417256561820075286819)
                ·
                  rfl

theorem cell20_922933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 7].length) (baseStart_922933 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_922933 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_922933 prefixEnd_922933 := by exact prefixLift 922933
  have htrace : WordTrace (prefixWord ++ tailWord_922933) baseStart_922933 baseEnd_922933 := by
    simpa [prefixWord, tailWord_922933, baseEnd_922933] using wordTrace_append hprefix tailTrace_922933
  have hstable : (prefixWord ++ tailWord_922933).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922933).length < 2 ^ (prefixWord ++ tailWord_922933).sum := by decide
  have hdescent : baseEnd_922933 < baseStart_922933 := by decide
  rcases family_descends (prefixWord ++ tailWord_922933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922947 : List Nat := [1, 1, 1, 3, 1, 3, 1, 3, 6]
def baseStart_922947 : Nat := 118140960795 + 922947 * 2 ^ 59
def prefixEnd_922947 : Nat := 4983230072969 + 3 ^ 40 * 922947 * 2
def baseEnd_922947 : Nat := 421258159666938399393733

theorem tailTrace_922947 : CollatzResearch.WordTrace tailWord_922947 prefixEnd_922947 421258159666938399393733 := by
  unfold tailWord_922947
  simp only [CollatzResearch.WordTrace]
  refine ⟨33662642587328120643399095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22441761724885413762266063 33662642587328120643399095)
  ·
    refine ⟨50493963880992180965098643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33662642587328120643399095 50493963880992180965098643)
    ·
      refine ⟨75740945821488271447647965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50493963880992180965098643 75740945821488271447647965)
      ·
        refine ⟨28402854683058101792867987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75740945821488271447647965 28402854683058101792867987)
        ·
          refine ⟨42604282024587152689301981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28402854683058101792867987 42604282024587152689301981)
          ·
            refine ⟨15976605759220182258488243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42604282024587152689301981 15976605759220182258488243)
            ·
              refine ⟨23964908638830273387732365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15976605759220182258488243 23964908638830273387732365)
              ·
                refine ⟨8986840739561352520399637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23964908638830273387732365 8986840739561352520399637)
                ·
                  refine ⟨421258159666938399393733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8986840739561352520399637 421258159666938399393733)
                  ·
                    rfl

theorem cell20_922947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 3, 6].length) (baseStart_922947 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_922947 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_922947 prefixEnd_922947 := by exact prefixLift 922947
  have htrace : WordTrace (prefixWord ++ tailWord_922947) baseStart_922947 baseEnd_922947 := by
    simpa [prefixWord, tailWord_922947, baseEnd_922947] using wordTrace_append hprefix tailTrace_922947
  have hstable : (prefixWord ++ tailWord_922947).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922947).length < 2 ^ (prefixWord ++ tailWord_922947).sum := by decide
  have hdescent : baseEnd_922947 < baseStart_922947 := by decide
  rcases family_descends (prefixWord ++ tailWord_922947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922981 : List Nat := [1, 3, 1, 3, 1, 2, 3, 4, 2]
def baseStart_922981 : Nat := 118140960795 + 922981 * 2 ^ 59
def prefixEnd_922981 : Nat := 4983230072969 + 3 ^ 40 * 922981 * 2
def baseEnd_922981 : Nat := 421273678193385392260261

theorem tailTrace_922981 : CollatzResearch.WordTrace tailWord_922981 prefixEnd_922981 421273678193385392260261 := by
  unfold tailWord_922981
  simp only [CollatzResearch.WordTrace]
  refine ⟨33663882669204944450136797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22442588446136629633424531 33663882669204944450136797)
  ·
    refine ⟨12623956000951854168801299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33663882669204944450136797 12623956000951854168801299)
    ·
      refine ⟨18935934001427781253201949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12623956000951854168801299 18935934001427781253201949)
      ·
        refine ⟨7100975250535417969950731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18935934001427781253201949 7100975250535417969950731)
        ·
          refine ⟨10651462875803126954926097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7100975250535417969950731 10651462875803126954926097)
          ·
            refine ⟨7988597156852345216194573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10651462875803126954926097 7988597156852345216194573)
            ·
              refine ⟨2995723933819629456072965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7988597156852345216194573 2995723933819629456072965)
              ·
                refine ⟨561698237591180523013681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2995723933819629456072965 561698237591180523013681)
                ·
                  refine ⟨421273678193385392260261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 561698237591180523013681 421273678193385392260261)
                  ·
                    rfl

theorem cell20_922981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 4, 2].length) (baseStart_922981 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_922981 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_922981 prefixEnd_922981 := by exact prefixLift 922981
  have htrace : WordTrace (prefixWord ++ tailWord_922981) baseStart_922981 baseEnd_922981 := by
    simpa [prefixWord, tailWord_922981, baseEnd_922981] using wordTrace_append hprefix tailTrace_922981
  have hstable : (prefixWord ++ tailWord_922981).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922981).length < 2 ^ (prefixWord ++ tailWord_922981).sum := by decide
  have hdescent : baseEnd_922981 < baseStart_922981 := by decide
  rcases family_descends (prefixWord ++ tailWord_922981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922988 : List Nat := [2, 2, 1, 1, 5, 3, 1, 5]
def baseStart_922988 : Nat := 118140960795 + 922988 * 2 ^ 59
def prefixEnd_922988 : Nat := 4983230072969 + 3 ^ 40 * 922988 * 2
def baseEnd_922988 : Nat := 140425624394708159675633

theorem tailTrace_922988 : CollatzResearch.WordTrace tailWord_922988 prefixEnd_922988 140425624394708159675633 := by
  unfold tailWord_922988
  simp only [CollatzResearch.WordTrace]
  refine ⟨16832068990089792322820809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22442758653453056430427745 16832068990089792322820809)
  ·
    refine ⟨12624051742567344242115607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16832068990089792322820809 12624051742567344242115607)
    ·
      refine ⟨18936077613851016363173411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12624051742567344242115607 18936077613851016363173411)
      ·
        refine ⟨28404116420776524544760117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18936077613851016363173411 28404116420776524544760117)
        ·
          refine ⟨2662885914447799176071261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28404116420776524544760117 2662885914447799176071261)
          ·
            refine ⟨998582217917924691026723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2662885914447799176071261 998582217917924691026723)
            ·
              refine ⟨1497873326876887036540085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 998582217917924691026723 1497873326876887036540085)
              ·
                refine ⟨140425624394708159675633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1497873326876887036540085 140425624394708159675633)
                ·
                  rfl

theorem cell20_922988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 1, 5].length) (baseStart_922988 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_922988 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_922988 prefixEnd_922988 := by exact prefixLift 922988
  have htrace : WordTrace (prefixWord ++ tailWord_922988) baseStart_922988 baseEnd_922988 := by
    simpa [prefixWord, tailWord_922988, baseEnd_922988] using wordTrace_append hprefix tailTrace_922988
  have hstable : (prefixWord ++ tailWord_922988).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922988).length < 2 ^ (prefixWord ++ tailWord_922988).sum := by decide
  have hdescent : baseEnd_922988 < baseStart_922988 := by decide
  rcases family_descends (prefixWord ++ tailWord_922988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923019 : List Nat := [1, 1, 1, 1, 4, 3, 4, 3, 2]
def baseStart_923019 : Nat := 118140960795 + 923019 * 2 ^ 59
def prefixEnd_923019 : Nat := 4983230072969 + 3 ^ 40 * 923019 * 2
def baseEnd_923019 : Nat := 421291022428826148993439

theorem tailTrace_923019 : CollatzResearch.WordTrace tailWord_923019 prefixEnd_923019 421291022428826148993439 := by
  unfold tailWord_923019
  simp only [CollatzResearch.WordTrace]
  refine ⟨33665268643067276940020111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22443512428711517960013407 33665268643067276940020111)
  ·
    refine ⟨50497902964600915410030167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33665268643067276940020111 50497902964600915410030167)
    ·
      refine ⟨75746854446901373115045251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50497902964600915410030167 75746854446901373115045251)
      ·
        refine ⟨113620281670352059672567877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75746854446901373115045251 113620281670352059672567877)
        ·
          refine ⟨21303802813191011188606477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 113620281670352059672567877 21303802813191011188606477)
          ·
            refine ⟨7988926054946629195727429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21303802813191011188606477 7988926054946629195727429)
            ·
              refine ⟨1497923635302492974198893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7988926054946629195727429 1497923635302492974198893)
              ·
                refine ⟨561721363238434865324585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1497923635302492974198893 561721363238434865324585)
                ·
                  refine ⟨421291022428826148993439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 561721363238434865324585 421291022428826148993439)
                  ·
                    rfl

theorem cell20_923019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 4, 3, 2].length) (baseStart_923019 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_923019 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_923019 prefixEnd_923019 := by exact prefixLift 923019
  have htrace : WordTrace (prefixWord ++ tailWord_923019) baseStart_923019 baseEnd_923019 := by
    simpa [prefixWord, tailWord_923019, baseEnd_923019] using wordTrace_append hprefix tailTrace_923019
  have hstable : (prefixWord ++ tailWord_923019).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923019).length < 2 ^ (prefixWord ++ tailWord_923019).sum := by decide
  have hdescent : baseEnd_923019 < baseStart_923019 := by decide
  rcases family_descends (prefixWord ++ tailWord_923019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923033 : List Nat := [1, 2, 1, 2, 1, 5, 3, 2, 3]
def baseStart_923033 : Nat := 118140960795 + 923033 * 2 ^ 59
def prefixEnd_923033 : Nat := 4983230072969 + 3 ^ 40 * 923033 * 2
def baseEnd_923033 : Nat := 421297412410304322526715

theorem tailTrace_923033 : CollatzResearch.WordTrace tailWord_923033 prefixEnd_923033 421297412410304322526715 := by
  unfold tailWord_923033
  simp only [CollatzResearch.WordTrace]
  refine ⟨33665779265016557331029753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22443852843344371554019835 33665779265016557331029753)
  ·
    refine ⟨25249334448762417998272315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33665779265016557331029753 25249334448762417998272315)
    ·
      refine ⟨37874001673143626997408473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25249334448762417998272315 37874001673143626997408473)
      ·
        refine ⟨28405501254857720248056355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37874001673143626997408473 28405501254857720248056355)
        ·
          refine ⟨42608251882286580372084533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28405501254857720248056355 42608251882286580372084533)
          ·
            refine ⟨3994523613964366909882925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42608251882286580372084533 3994523613964366909882925)
            ·
              refine ⟨1497946355236637591206097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3994523613964366909882925 1497946355236637591206097)
              ·
                refine ⟨1123459766427478193404573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1497946355236637591206097 1123459766427478193404573)
                ·
                  refine ⟨421297412410304322526715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1123459766427478193404573 421297412410304322526715)
                  ·
                    rfl

theorem cell20_923033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 3, 2, 3].length) (baseStart_923033 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_923033 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_923033 prefixEnd_923033 := by exact prefixLift 923033
  have htrace : WordTrace (prefixWord ++ tailWord_923033) baseStart_923033 baseEnd_923033 := by
    simpa [prefixWord, tailWord_923033, baseEnd_923033] using wordTrace_append hprefix tailTrace_923033
  have hstable : (prefixWord ++ tailWord_923033).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923033).length < 2 ^ (prefixWord ++ tailWord_923033).sum := by decide
  have hdescent : baseEnd_923033 < baseStart_923033 := by decide
  rcases family_descends (prefixWord ++ tailWord_923033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923036 : List Nat := [2, 2, 3, 4, 1, 1, 2, 1, 4]
def baseStart_923036 : Nat := 118140960795 + 923036 * 2 ^ 59
def prefixEnd_923036 : Nat := 4983230072969 + 3 ^ 40 * 923036 * 2
def baseEnd_923036 : Nat := 421298781692049645426703

theorem tailTrace_923036 : CollatzResearch.WordTrace tailWord_923036 prefixEnd_923036 421298781692049645426703 := by
  unfold tailWord_923036
  simp only [CollatzResearch.WordTrace]
  refine ⟨16832944342002844421694481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22443925789337125895592641 16832944342002844421694481)
  ·
    refine ⟨12624708256502133316270861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16832944342002844421694481 12624708256502133316270861)
    ·
      refine ⟨4734265596188299993601573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12624708256502133316270861 4734265596188299993601573)
      ·
        refine ⟨887674799285306248800295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4734265596188299993601573 887674799285306248800295)
        ·
          refine ⟨1331512198927959373200443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 887674799285306248800295 1331512198927959373200443)
          ·
            refine ⟨1997268298391939059800665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1331512198927959373200443 1997268298391939059800665)
            ·
              refine ⟨1497951223793954294850499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1997268298391939059800665 1497951223793954294850499)
              ·
                refine ⟨2246926835690931442275749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1497951223793954294850499 2246926835690931442275749)
                ·
                  refine ⟨421298781692049645426703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2246926835690931442275749 421298781692049645426703)
                  ·
                    rfl

theorem cell20_923036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 2, 1, 4].length) (baseStart_923036 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_923036 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_923036 prefixEnd_923036 := by exact prefixLift 923036
  have htrace : WordTrace (prefixWord ++ tailWord_923036) baseStart_923036 baseEnd_923036 := by
    simpa [prefixWord, tailWord_923036, baseEnd_923036] using wordTrace_append hprefix tailTrace_923036
  have hstable : (prefixWord ++ tailWord_923036).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923036).length < 2 ^ (prefixWord ++ tailWord_923036).sum := by decide
  have hdescent : baseEnd_923036 < baseStart_923036 := by decide
  rcases family_descends (prefixWord ++ tailWord_923036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923040 : List Nat := [2, 1, 1, 4, 1, 2, 4, 1, 4]
def baseStart_923040 : Nat := 118140960795 + 923040 * 2 ^ 59
def prefixEnd_923040 : Nat := 4983230072969 + 3 ^ 40 * 923040 * 2
def baseEnd_923040 : Nat := 421300607401043409293353

theorem tailTrace_923040 : CollatzResearch.WordTrace tailWord_923040 prefixEnd_923040 421300607401043409293353 := by
  unfold tailWord_923040
  simp only [CollatzResearch.WordTrace]
  refine ⟨16833017287995598763267287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22444023050660798351023049 16833017287995598763267287)
  ·
    refine ⟨25249525931993398144900931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16833017287995598763267287 25249525931993398144900931)
    ·
      refine ⟨37874288897990097217351397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25249525931993398144900931 37874288897990097217351397)
      ·
        refine ⟨7101429168373143228253387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37874288897990097217351397 7101429168373143228253387)
        ·
          refine ⟨10652143752559714842380081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7101429168373143228253387 10652143752559714842380081)
          ·
            refine ⟨7989107814419786131785061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10652143752559714842380081 7989107814419786131785061)
            ·
              refine ⟨1497957715203709899709699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7989107814419786131785061 1497957715203709899709699)
              ·
                refine ⟨2246936572805564849564549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1497957715203709899709699 2246936572805564849564549)
                ·
                  refine ⟨421300607401043409293353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2246936572805564849564549 421300607401043409293353)
                  ·
                    rfl

theorem cell20_923040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 4, 1, 4].length) (baseStart_923040 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_923040 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_923040 prefixEnd_923040 := by exact prefixLift 923040
  have htrace : WordTrace (prefixWord ++ tailWord_923040) baseStart_923040 baseEnd_923040 := by
    simpa [prefixWord, tailWord_923040, baseEnd_923040] using wordTrace_append hprefix tailTrace_923040
  have hstable : (prefixWord ++ tailWord_923040).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923040).length < 2 ^ (prefixWord ++ tailWord_923040).sum := by decide
  have hdescent : baseEnd_923040 < baseStart_923040 := by decide
  rcases family_descends (prefixWord ++ tailWord_923040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923047 : List Nat := [1, 1, 6, 1, 1, 1, 2, 7]
def baseStart_923047 : Nat := 118140960795 + 923047 * 2 ^ 59
def prefixEnd_923047 : Nat := 4983230072969 + 3 ^ 40 * 923047 * 2
def baseEnd_923047 : Nat := 140434600797260832019997

theorem tailTrace_923047 : CollatzResearch.WordTrace tailWord_923047 prefixEnd_923047 140434600797260832019997 := by
  unfold tailWord_923047
  simp only [CollatzResearch.WordTrace]
  refine ⟨33666289886965837722039395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22444193257977225148026263 33666289886965837722039395)
  ·
    refine ⟨50499434830448756583059093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33666289886965837722039395 50499434830448756583059093)
    ·
      refine ⟨2367161007677285464830895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 50499434830448756583059093 2367161007677285464830895)
      ·
        refine ⟨3550741511515928197246343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2367161007677285464830895 3550741511515928197246343)
        ·
          refine ⟨5326112267273892295869515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3550741511515928197246343 5326112267273892295869515)
          ·
            refine ⟨7989168400910838443804273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5326112267273892295869515 7989168400910838443804273)
            ·
              refine ⟨5991876300683128832853205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7989168400910838443804273 5991876300683128832853205)
              ·
                refine ⟨140434600797260832019997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5991876300683128832853205 140434600797260832019997)
                ·
                  rfl

theorem cell20_923047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 7].length) (baseStart_923047 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_923047 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_923047 prefixEnd_923047 := by exact prefixLift 923047
  have htrace : WordTrace (prefixWord ++ tailWord_923047) baseStart_923047 baseEnd_923047 := by
    simpa [prefixWord, tailWord_923047, baseEnd_923047] using wordTrace_append hprefix tailTrace_923047
  have hstable : (prefixWord ++ tailWord_923047).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923047).length < 2 ^ (prefixWord ++ tailWord_923047).sum := by decide
  have hdescent : baseEnd_923047 < baseStart_923047 := by decide
  rcases family_descends (prefixWord ++ tailWord_923047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923140 : List Nat := [2, 3, 2, 3, 3, 7]
def baseStart_923140 : Nat := 118140960795 + 923140 * 2 ^ 59
def prefixEnd_923140 : Nat := 4983230072969 + 3 ^ 40 * 923140 * 2
def baseEnd_923140 : Nat := 15605416671329166887393

theorem tailTrace_923140 : CollatzResearch.WordTrace tailWord_923140 prefixEnd_923140 15605416671329166887393 := by
  unfold tailWord_923140
  simp only [CollatzResearch.WordTrace]
  refine ⟨16834840937814457302587437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22446454583752609736783249 16834840937814457302587437)
  ·
    refine ⟨6313065351680421488470289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16834840937814457302587437 6313065351680421488470289)
    ·
      refine ⟨4734799013760316116352717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6313065351680421488470289 4734799013760316116352717)
      ·
        refine ⟨1775549630160118543632269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4734799013760316116352717 1775549630160118543632269)
        ·
          refine ⟨665831111310044453862101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1775549630160118543632269 665831111310044453862101)
          ·
            refine ⟨15605416671329166887393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 665831111310044453862101 15605416671329166887393)
            ·
              rfl

theorem cell20_923140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 7].length) (baseStart_923140 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_923140 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_923140 prefixEnd_923140 := by exact prefixLift 923140
  have htrace : WordTrace (prefixWord ++ tailWord_923140) baseStart_923140 baseEnd_923140 := by
    simpa [prefixWord, tailWord_923140, baseEnd_923140] using wordTrace_append hprefix tailTrace_923140
  have hstable : (prefixWord ++ tailWord_923140).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923140).length < 2 ^ (prefixWord ++ tailWord_923140).sum := by decide
  have hdescent : baseEnd_923140 < baseStart_923140 := by decide
  rcases family_descends (prefixWord ++ tailWord_923140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923142 : List Nat := [6, 2, 1, 1, 2, 2, 2, 2, 2]
def baseStart_923142 : Nat := 118140960795 + 923142 * 2 ^ 59
def prefixEnd_923142 : Nat := 4983230072969 + 3 ^ 40 * 923142 * 2
def baseEnd_923142 : Nat := 421347162980384387892937

theorem tailTrace_923142 : CollatzResearch.WordTrace tailWord_923142 prefixEnd_923142 421347162980384387892937 := by
  unfold tailWord_923142
  simp only [CollatzResearch.WordTrace]
  refine ⟨1052179838175677154585865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 22446503214414445964498453 1052179838175677154585865)
  ·
    refine ⟨789134878631757865939399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1052179838175677154585865 789134878631757865939399)
    ·
      refine ⟨1183702317947636798909099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 789134878631757865939399 1183702317947636798909099)
      ·
        refine ⟨1775553476921455198363649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1183702317947636798909099 1775553476921455198363649)
        ·
          refine ⟨1331665107691091398772737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1775553476921455198363649 1331665107691091398772737)
          ·
            refine ⟨998748830768318549079553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1331665107691091398772737 998748830768318549079553)
            ·
              refine ⟨749061623076238911809665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 998748830768318549079553 749061623076238911809665)
              ·
                refine ⟨561796217307179183857249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 749061623076238911809665 561796217307179183857249)
                ·
                  refine ⟨421347162980384387892937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 561796217307179183857249 421347162980384387892937)
                  ·
                    rfl

theorem cell20_923142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_923142 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_923142 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_923142 prefixEnd_923142 := by exact prefixLift 923142
  have htrace : WordTrace (prefixWord ++ tailWord_923142) baseStart_923142 baseEnd_923142 := by
    simpa [prefixWord, tailWord_923142, baseEnd_923142] using wordTrace_append hprefix tailTrace_923142
  have hstable : (prefixWord ++ tailWord_923142).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923142).length < 2 ^ (prefixWord ++ tailWord_923142).sum := by decide
  have hdescent : baseEnd_923142 < baseStart_923142 := by decide
  rcases family_descends (prefixWord ++ tailWord_923142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923150 : List Nat := [4, 1, 1, 2, 4, 1, 1, 4, 2]
def baseStart_923150 : Nat := 118140960795 + 923150 * 2 ^ 59
def prefixEnd_923150 : Nat := 4983230072969 + 3 ^ 40 * 923150 * 2
def baseEnd_923150 : Nat := 421350814398371915626237

theorem tailTrace_923150 : CollatzResearch.WordTrace tailWord_923150 prefixEnd_923150 421350814398371915626237 := by
  unfold tailWord_923150
  simp only [CollatzResearch.WordTrace]
  refine ⟨4208755825699085789129863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22446697737061790875359269 4208755825699085789129863)
  ·
    refine ⟨6313133738548628683694795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4208755825699085789129863 6313133738548628683694795)
    ·
      refine ⟨9469700607822943025542193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6313133738548628683694795 9469700607822943025542193)
      ·
        refine ⟨7102275455867207269156645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9469700607822943025542193 7102275455867207269156645)
        ·
          refine ⟨1331676647975101362966871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7102275455867207269156645 1331676647975101362966871)
          ·
            refine ⟨1997514971962652044450307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1331676647975101362966871 1997514971962652044450307)
            ·
              refine ⟨2996272457943978066675461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1997514971962652044450307 2996272457943978066675461)
              ·
                refine ⟨561801085864495887501649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2996272457943978066675461 561801085864495887501649)
                ·
                  refine ⟨421350814398371915626237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 561801085864495887501649 421350814398371915626237)
                  ·
                    rfl

theorem cell20_923150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 4, 2].length) (baseStart_923150 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_923150 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_923150 prefixEnd_923150 := by exact prefixLift 923150
  have htrace : WordTrace (prefixWord ++ tailWord_923150) baseStart_923150 baseEnd_923150 := by
    simpa [prefixWord, tailWord_923150, baseEnd_923150] using wordTrace_append hprefix tailTrace_923150
  have hstable : (prefixWord ++ tailWord_923150).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923150).length < 2 ^ (prefixWord ++ tailWord_923150).sum := by decide
  have hdescent : baseEnd_923150 < baseStart_923150 := by decide
  rcases family_descends (prefixWord ++ tailWord_923150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923178 : List Nat := [3, 1, 4, 1, 1, 1, 5, 4]
def baseStart_923178 : Nat := 118140960795 + 923178 * 2 ^ 59
def prefixEnd_923178 : Nat := 4983230072969 + 3 ^ 40 * 923178 * 2
def baseEnd_923178 : Nat := 140454531453776087564263

theorem tailTrace_923178 : CollatzResearch.WordTrace tailWord_923178 prefixEnd_923178 140454531453776087564263 := by
  unfold tailWord_923178
  simp only [CollatzResearch.WordTrace]
  refine ⟨8417766962372811773764547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22447378566327498063372125 8417766962372811773764547)
  ·
    refine ⟨12626650443559217660646821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8417766962372811773764547 12626650443559217660646821)
    ·
      refine ⟨2367496958167353311371279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12626650443559217660646821 2367496958167353311371279)
      ·
        refine ⟨3551245437251029967056919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2367496958167353311371279 3551245437251029967056919)
        ·
          refine ⟨5326868155876544950585379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3551245437251029967056919 5326868155876544950585379)
          ·
            refine ⟨7990302233814817425878069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5326868155876544950585379 7990302233814817425878069)
            ·
              refine ⟨749090834420139133676069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7990302233814817425878069 749090834420139133676069)
              ·
                refine ⟨140454531453776087564263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 749090834420139133676069 140454531453776087564263)
                ·
                  rfl

theorem cell20_923178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 5, 4].length) (baseStart_923178 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_923178 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_923178 prefixEnd_923178 := by exact prefixLift 923178
  have htrace : WordTrace (prefixWord ++ tailWord_923178) baseStart_923178 baseEnd_923178 := by
    simpa [prefixWord, tailWord_923178, baseEnd_923178] using wordTrace_append hprefix tailTrace_923178
  have hstable : (prefixWord ++ tailWord_923178).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923178).length < 2 ^ (prefixWord ++ tailWord_923178).sum := by decide
  have hdescent : baseEnd_923178 < baseStart_923178 := by decide
  rcases family_descends (prefixWord ++ tailWord_923178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923229 : List Nat := [1, 4, 4, 2, 2, 1, 2, 4]
def baseStart_923229 : Nat := 118140960795 + 923229 * 2 ^ 59
def prefixEnd_923229 : Nat := 4983230072969 + 3 ^ 40 * 923229 * 2
def baseEnd_923229 : Nat := 140462290716999583997527

theorem tailTrace_923229 : CollatzResearch.WordTrace tailWord_923229 prefixEnd_923229 140462290716999583997527 := by
  unfold tailWord_923229
  simp only [CollatzResearch.WordTrace]
  refine ⟨33672927972306482805164741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22448618648204321870109827 33672927972306482805164741)
  ·
    refine ⟨6313673994807465525968389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33672927972306482805164741 6313673994807465525968389)
    ·
      refine ⟨1183813874026399786119073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6313673994807465525968389 1183813874026399786119073)
      ·
        refine ⟨887860405519799839589305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1183813874026399786119073 887860405519799839589305)
        ·
          refine ⟨665895304139849879691979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 887860405519799839589305 665895304139849879691979)
          ·
            refine ⟨998842956209774819537969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 665895304139849879691979 998842956209774819537969)
            ·
              refine ⟨749132217157331114653477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 998842956209774819537969 749132217157331114653477)
              ·
                refine ⟨140462290716999583997527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 749132217157331114653477 140462290716999583997527)
                ·
                  rfl

theorem cell20_923229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 2, 4].length) (baseStart_923229 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_923229 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_923229 prefixEnd_923229 := by exact prefixLift 923229
  have htrace : WordTrace (prefixWord ++ tailWord_923229) baseStart_923229 baseEnd_923229 := by
    simpa [prefixWord, tailWord_923229, baseEnd_923229] using wordTrace_append hprefix tailTrace_923229
  have hstable : (prefixWord ++ tailWord_923229).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923229).length < 2 ^ (prefixWord ++ tailWord_923229).sum := by decide
  have hdescent : baseEnd_923229 < baseStart_923229 := by decide
  rcases family_descends (prefixWord ++ tailWord_923229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923237 : List Nat := [1, 3, 1, 3, 3, 2, 1, 6]
def baseStart_923237 : Nat := 118140960795 + 923237 * 2 ^ 59
def prefixEnd_923237 : Nat := 4983230072969 + 3 ^ 40 * 923237 * 2
def baseEnd_923237 : Nat := 140463507856328759908627

theorem tailTrace_923237 : CollatzResearch.WordTrace tailWord_923237 prefixEnd_923237 140463507856328759908627 := by
  unfold tailWord_923237
  simp only [CollatzResearch.WordTrace]
  refine ⟨33673219756277500171455965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22448813170851666780970643 33673219756277500171455965)
  ·
    refine ⟨12627457408604062564295987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33673219756277500171455965 12627457408604062564295987)
    ·
      refine ⟨18941186112906093846443981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12627457408604062564295987 18941186112906093846443981)
      ·
        refine ⟨7102944792339785192416493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18941186112906093846443981 7102944792339785192416493)
        ·
          refine ⟨2663604297127419447156185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7102944792339785192416493 2663604297127419447156185)
          ·
            refine ⟨1997703222845564585367139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2663604297127419447156185 1997703222845564585367139)
            ·
              refine ⟨2996554834268346878050709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1997703222845564585367139 2996554834268346878050709)
              ·
                refine ⟨140463507856328759908627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2996554834268346878050709 140463507856328759908627)
                ·
                  rfl

theorem cell20_923237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 6].length) (baseStart_923237 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_923237 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_923237 prefixEnd_923237 := by exact prefixLift 923237
  have htrace : WordTrace (prefixWord ++ tailWord_923237) baseStart_923237 baseEnd_923237 := by
    simpa [prefixWord, tailWord_923237, baseEnd_923237] using wordTrace_append hprefix tailTrace_923237
  have hstable : (prefixWord ++ tailWord_923237).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923237).length < 2 ^ (prefixWord ++ tailWord_923237).sum := by decide
  have hdescent : baseEnd_923237 < baseStart_923237 := by decide
  rcases family_descends (prefixWord ++ tailWord_923237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923254 : List Nat := [5, 1, 1, 2, 2, 3, 6]
def baseStart_923254 : Nat := 118140960795 + 923254 * 2 ^ 59
def prefixEnd_923254 : Nat := 4983230072969 + 3 ^ 40 * 923254 * 2
def baseEnd_923254 : Nat := 46822031425801086239905

theorem tailTrace_923254 : CollatzResearch.WordTrace tailWord_923254 prefixEnd_923254 46822031425801086239905 := by
  unfold tailWord_923254
  simp only [CollatzResearch.WordTrace]
  refine ⟨2104614987325994504676551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22449226531477274716549877 2104614987325994504676551)
  ·
    refine ⟨3156922480988991757014827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2104614987325994504676551 3156922480988991757014827)
    ·
      refine ⟨4735383721483487635522241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3156922480988991757014827 4735383721483487635522241)
      ·
        refine ⟨3551537791112615726641681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4735383721483487635522241 3551537791112615726641681)
        ·
          refine ⟨2663653343334461794981261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3551537791112615726641681 2663653343334461794981261)
          ·
            refine ⟨998870003750423173117973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2663653343334461794981261 998870003750423173117973)
            ·
              refine ⟨46822031425801086239905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 998870003750423173117973 46822031425801086239905)
              ·
                rfl

theorem cell20_923254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 6].length) (baseStart_923254 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_923254 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_923254 prefixEnd_923254 := by exact prefixLift 923254
  have htrace : WordTrace (prefixWord ++ tailWord_923254) baseStart_923254 baseEnd_923254 := by
    simpa [prefixWord, tailWord_923254, baseEnd_923254] using wordTrace_append hprefix tailTrace_923254
  have hstable : (prefixWord ++ tailWord_923254).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923254).length < 2 ^ (prefixWord ++ tailWord_923254).sum := by decide
  have hdescent : baseEnd_923254 < baseStart_923254 := by decide
  rcases family_descends (prefixWord ++ tailWord_923254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923278 : List Nat := [4, 1, 1, 3, 1, 2, 4, 1, 3]
def baseStart_923278 : Nat := 118140960795 + 923278 * 2 ^ 59
def prefixEnd_923278 : Nat := 4983230072969 + 3 ^ 40 * 923278 * 2
def baseEnd_923278 : Nat := 421409237086172359359047

theorem tailTrace_923278 : CollatzResearch.WordTrace tailWord_923278 prefixEnd_923278 421409237086172359359047 := by
  unfold tailWord_923278
  simp only [CollatzResearch.WordTrace]
  refine ⟨4209339393641120521712311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22449810099419309449132325 4209339393641120521712311)
  ·
    refine ⟨6314009090461680782568467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4209339393641120521712311 6314009090461680782568467)
    ·
      refine ⟨9471013635692521173852701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6314009090461680782568467 9471013635692521173852701)
      ·
        refine ⟨3551630113384695440194763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9471013635692521173852701 3551630113384695440194763)
        ·
          refine ⟨5327445170077043160292145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3551630113384695440194763 5327445170077043160292145)
          ·
            refine ⟨3995583877557782370219109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5327445170077043160292145 3995583877557782370219109)
            ·
              refine ⟨749171977042084194416083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3995583877557782370219109 749171977042084194416083)
              ·
                refine ⟨1123757965563126291624125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 749171977042084194416083 1123757965563126291624125)
                ·
                  refine ⟨421409237086172359359047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1123757965563126291624125 421409237086172359359047)
                  ·
                    rfl

theorem cell20_923278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 4, 1, 3].length) (baseStart_923278 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_923278 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_923278 prefixEnd_923278 := by exact prefixLift 923278
  have htrace : WordTrace (prefixWord ++ tailWord_923278) baseStart_923278 baseEnd_923278 := by
    simpa [prefixWord, tailWord_923278, baseEnd_923278] using wordTrace_append hprefix tailTrace_923278
  have hstable : (prefixWord ++ tailWord_923278).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923278).length < 2 ^ (prefixWord ++ tailWord_923278).sum := by decide
  have hdescent : baseEnd_923278 < baseStart_923278 := by decide
  rcases family_descends (prefixWord ++ tailWord_923278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923327 : List Nat := [1, 1, 2, 2, 2, 3, 2, 3, 4]
def baseStart_923327 : Nat := 118140960795 + 923327 * 2 ^ 59
def prefixEnd_923327 : Nat := 4983230072969 + 3 ^ 40 * 923327 * 2
def baseEnd_923327 : Nat := 421431602021345966725513

theorem tailTrace_923327 : CollatzResearch.WordTrace tailWord_923327 prefixEnd_923327 421431602021345966725513 := by
  unfold tailWord_923327
  simp only [CollatzResearch.WordTrace]
  refine ⟨33676502325951445542232235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22451001550634297028154823 33676502325951445542232235)
  ·
    refine ⟨50514753488927168313348353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33676502325951445542232235 50514753488927168313348353)
    ·
      refine ⟨37886065116695376235011265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50514753488927168313348353 37886065116695376235011265)
      ·
        refine ⟨28414548837521532176258449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37886065116695376235011265 28414548837521532176258449)
        ·
          refine ⟨21310911628141149132193837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28414548837521532176258449 21310911628141149132193837)
          ·
            refine ⟨7991591860552930924572689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21310911628141149132193837 7991591860552930924572689)
            ·
              refine ⟨5993693895414698193429517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7991591860552930924572689 5993693895414698193429517)
              ·
                refine ⟨2247635210780511822536069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5993693895414698193429517 2247635210780511822536069)
                ·
                  refine ⟨421431602021345966725513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2247635210780511822536069 421431602021345966725513)
                  ·
                    rfl

theorem cell20_923327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 3, 4].length) (baseStart_923327 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_923327 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_923327 prefixEnd_923327 := by exact prefixLift 923327
  have htrace : WordTrace (prefixWord ++ tailWord_923327) baseStart_923327 baseEnd_923327 := by
    simpa [prefixWord, tailWord_923327, baseEnd_923327] using wordTrace_append hprefix tailTrace_923327
  have hstable : (prefixWord ++ tailWord_923327).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923327).length < 2 ^ (prefixWord ++ tailWord_923327).sum := by decide
  have hdescent : baseEnd_923327 < baseStart_923327 := by decide
  rcases family_descends (prefixWord ++ tailWord_923327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923351 : List Nat := [1, 1, 3, 2, 1, 3, 5, 4]
def baseStart_923351 : Nat := 118140960795 + 923351 * 2 ^ 59
def prefixEnd_923351 : Nat := 4983230072969 + 3 ^ 40 * 923351 * 2
def baseEnd_923351 : Nat := 140480852091769516641805

theorem tailTrace_923351 : CollatzResearch.WordTrace tailWord_923351 prefixEnd_923351 140480852091769516641805 := by
  unfold tailWord_923351
  simp only [CollatzResearch.WordTrace]
  refine ⟨33677377677864497641105907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22451585118576331760737271 33677377677864497641105907)
  ·
    refine ⟨50516066516796746461658861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33677377677864497641105907 50516066516796746461658861)
    ·
      refine ⟨18943524943798779923122073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50516066516796746461658861 18943524943798779923122073)
      ·
        refine ⟨14207643707849084942341555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18943524943798779923122073 14207643707849084942341555)
        ·
          refine ⟨21311465561773627413512333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14207643707849084942341555 21311465561773627413512333)
          ·
            refine ⟨7991799585665110280067125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21311465561773627413512333 7991799585665110280067125)
            ·
              refine ⟨749231211156104088756293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7991799585665110280067125 749231211156104088756293)
              ·
                refine ⟨140480852091769516641805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 749231211156104088756293 140480852091769516641805)
                ·
                  rfl

theorem cell20_923351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 5, 4].length) (baseStart_923351 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_923351 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_923351 prefixEnd_923351 := by exact prefixLift 923351
  have htrace : WordTrace (prefixWord ++ tailWord_923351) baseStart_923351 baseEnd_923351 := by
    simpa [prefixWord, tailWord_923351, baseEnd_923351] using wordTrace_append hprefix tailTrace_923351
  have hstable : (prefixWord ++ tailWord_923351).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923351).length < 2 ^ (prefixWord ++ tailWord_923351).sum := by decide
  have hdescent : baseEnd_923351 < baseStart_923351 := by decide
  rcases family_descends (prefixWord ++ tailWord_923351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923357 : List Nat := [1, 4, 3, 3, 1, 1, 2, 3, 2]
def baseStart_923357 : Nat := 118140960795 + 923357 * 2 ^ 59
def prefixEnd_923357 : Nat := 4983230072969 + 3 ^ 40 * 923357 * 2
def baseEnd_923357 : Nat := 421445294838799195725391

theorem tailTrace_923357 : CollatzResearch.WordTrace tailWord_923357 prefixEnd_923357 421445294838799195725391 := by
  unfold tailWord_923357
  simp only [CollatzResearch.WordTrace]
  refine ⟨33677596515842760665824325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22451731010561840443882883 33677596515842760665824325)
  ·
    refine ⟨6314549346720517624842061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33677596515842760665824325 6314549346720517624842061)
    ·
      refine ⟨2367956005020194109315773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6314549346720517624842061 2367956005020194109315773)
      ·
        refine ⟨887983501882572790993415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2367956005020194109315773 887983501882572790993415)
        ·
          refine ⟨1331975252823859186490123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 887983501882572790993415 1331975252823859186490123)
          ·
            refine ⟨1997962879235788779735185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1331975252823859186490123 1997962879235788779735185)
            ·
              refine ⟨1498472159426841584801389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1997962879235788779735185 1498472159426841584801389)
              ·
                refine ⟨561927059785065594300521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1498472159426841584801389 561927059785065594300521)
                ·
                  refine ⟨421445294838799195725391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 561927059785065594300521 421445294838799195725391)
                  ·
                    rfl

theorem cell20_923357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 2, 3, 2].length) (baseStart_923357 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_923357 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_923357 prefixEnd_923357 := by exact prefixLift 923357
  have htrace : WordTrace (prefixWord ++ tailWord_923357) baseStart_923357 baseEnd_923357 := by
    simpa [prefixWord, tailWord_923357, baseEnd_923357] using wordTrace_append hprefix tailTrace_923357
  have hstable : (prefixWord ++ tailWord_923357).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923357).length < 2 ^ (prefixWord ++ tailWord_923357).sum := by decide
  have hdescent : baseEnd_923357 < baseStart_923357 := by decide
  rcases family_descends (prefixWord ++ tailWord_923357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923365 : List Nat := [1, 3, 1, 4, 1, 1, 1, 2, 6]
def baseStart_923365 : Nat := 118140960795 + 923365 * 2 ^ 59
def prefixEnd_923365 : Nat := 4983230072969 + 3 ^ 40 * 923365 * 2
def baseEnd_923365 : Nat := 421448946256786723458691

theorem tailTrace_923365 : CollatzResearch.WordTrace tailWord_923365 prefixEnd_923365 421448946256786723458691 := by
  unfold tailWord_923365
  simp only [CollatzResearch.WordTrace]
  refine ⟨33677888299813778032115549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22451925533209185354743699 33677888299813778032115549)
  ·
    refine ⟨12629208112430166762043331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33677888299813778032115549 12629208112430166762043331)
    ·
      refine ⟨18943812168645250143064997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12629208112430166762043331 18943812168645250143064997)
      ·
        refine ⟨3551964781620984401824687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18943812168645250143064997 3551964781620984401824687)
        ·
          refine ⟨5327947172431476602737031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3551964781620984401824687 5327947172431476602737031)
          ·
            refine ⟨7991920758647214904105547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5327947172431476602737031 7991920758647214904105547)
            ·
              refine ⟨11987881137970822356158321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7991920758647214904105547 11987881137970822356158321)
              ·
                refine ⟨8990910853478116767118741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11987881137970822356158321 8990910853478116767118741)
                ·
                  refine ⟨421448946256786723458691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8990910853478116767118741 421448946256786723458691)
                  ·
                    rfl

theorem cell20_923365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 2, 6].length) (baseStart_923365 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_923365 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_923365 prefixEnd_923365 := by exact prefixLift 923365
  have htrace : WordTrace (prefixWord ++ tailWord_923365) baseStart_923365 baseEnd_923365 := by
    simpa [prefixWord, tailWord_923365, baseEnd_923365] using wordTrace_append hprefix tailTrace_923365
  have hstable : (prefixWord ++ tailWord_923365).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923365).length < 2 ^ (prefixWord ++ tailWord_923365).sum := by decide
  have hdescent : baseEnd_923365 < baseStart_923365 := by decide
  rcases family_descends (prefixWord ++ tailWord_923365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923382 : List Nat := [5, 1, 1, 1, 1, 3, 1, 3, 4]
def baseStart_923382 : Nat := 118140960795 + 923382 * 2 ^ 59
def prefixEnd_923382 : Nat := 4983230072969 + 3 ^ 40 * 923382 * 2
def baseEnd_923382 : Nat := 421456705520010219891955

theorem tailTrace_923382 : CollatzResearch.WordTrace tailWord_923382 prefixEnd_923382 421456705520010219891955 := by
  unfold tailWord_923382
  simp only [CollatzResearch.WordTrace]
  refine ⟨2104906771297011870967775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22452338893834793290322933 2104906771297011870967775)
  ·
    refine ⟨3157360156945517806451663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2104906771297011870967775 3157360156945517806451663)
    ·
      refine ⟨4736040235418276709677495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3157360156945517806451663 4736040235418276709677495)
      ·
        refine ⟨7104060353127415064516243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4736040235418276709677495 7104060353127415064516243)
        ·
          refine ⟨10656090529691122596774365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7104060353127415064516243 10656090529691122596774365)
          ·
            refine ⟨3996033948634170973790387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10656090529691122596774365 3996033948634170973790387)
            ·
              refine ⟨5994050922951256460685581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3996033948634170973790387 5994050922951256460685581)
              ·
                refine ⟨2247769096106721172757093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5994050922951256460685581 2247769096106721172757093)
                ·
                  refine ⟨421456705520010219891955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2247769096106721172757093 421456705520010219891955)
                  ·
                    rfl

theorem cell20_923382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_923382 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_923382 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_923382 prefixEnd_923382 := by exact prefixLift 923382
  have htrace : WordTrace (prefixWord ++ tailWord_923382) baseStart_923382 baseEnd_923382 := by
    simpa [prefixWord, tailWord_923382, baseEnd_923382] using wordTrace_append hprefix tailTrace_923382
  have hstable : (prefixWord ++ tailWord_923382).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923382).length < 2 ^ (prefixWord ++ tailWord_923382).sum := by decide
  have hdescent : baseEnd_923382 < baseStart_923382 := by decide
  rcases family_descends (prefixWord ++ tailWord_923382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923403 : List Nat := [1, 1, 1, 1, 5, 1, 4, 2, 4]
def baseStart_923403 : Nat := 118140960795 + 923403 * 2 ^ 59
def prefixEnd_923403 : Nat := 4983230072969 + 3 ^ 40 * 923403 * 2
def baseEnd_923403 : Nat := 421466290492227480191869

theorem tailTrace_923403 : CollatzResearch.WordTrace tailWord_923403 prefixEnd_923403 421466290492227480191869 := by
  unfold tailWord_923403
  simp only [CollatzResearch.WordTrace]
  refine ⟨33679274273676110521998863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22452849515784073681332575 33679274273676110521998863)
  ·
    refine ⟨50518911410514165782998295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33679274273676110521998863 50518911410514165782998295)
    ·
      refine ⟨75778367115771248674497443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50518911410514165782998295 75778367115771248674497443)
      ·
        refine ⟨113667550673656873011746165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75778367115771248674497443 113667550673656873011746165)
        ·
          refine ⟨10656332875655331844851203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 113667550673656873011746165 10656332875655331844851203)
          ·
            refine ⟨15984499313482997767276805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10656332875655331844851203 15984499313482997767276805)
            ·
              refine ⟨2997093621278062081364401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15984499313482997767276805 2997093621278062081364401)
              ·
                refine ⟨2247820215958546561023301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2997093621278062081364401 2247820215958546561023301)
                ·
                  refine ⟨421466290492227480191869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2247820215958546561023301 421466290492227480191869)
                  ·
                    rfl

theorem cell20_923403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 2, 4].length) (baseStart_923403 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_923403 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_923403 prefixEnd_923403 := by exact prefixLift 923403
  have htrace : WordTrace (prefixWord ++ tailWord_923403) baseStart_923403 baseEnd_923403 := by
    simpa [prefixWord, tailWord_923403, baseEnd_923403] using wordTrace_append hprefix tailTrace_923403
  have hstable : (prefixWord ++ tailWord_923403).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923403).length < 2 ^ (prefixWord ++ tailWord_923403).sum := by decide
  have hdescent : baseEnd_923403 < baseStart_923403 := by decide
  rcases family_descends (prefixWord ++ tailWord_923403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923444 : List Nat := [2, 5, 1, 1, 2, 2, 2, 5]
def baseStart_923444 : Nat := 118140960795 + 923444 * 2 ^ 59
def prefixEnd_923444 : Nat := 4983230072969 + 3 ^ 40 * 923444 * 2
def baseEnd_923444 : Nat := 140495001336471186608345

theorem tailTrace_923444 : CollatzResearch.WordTrace tailWord_923444 prefixEnd_923444 140495001336471186608345 := by
  unfold tailWord_923444
  simp only [CollatzResearch.WordTrace]
  refine ⟨16840384833263787262120693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22453846444351716349494257 16840384833263787262120693)
  ·
    refine ⟨1578786078118480055823815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16840384833263787262120693 1578786078118480055823815)
    ·
      refine ⟨2368179117177720083735723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1578786078118480055823815 2368179117177720083735723)
      ·
        refine ⟨3552268675766580125603585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2368179117177720083735723 3552268675766580125603585)
        ·
          refine ⟨2664201506824935094202689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3552268675766580125603585 2664201506824935094202689)
          ·
            refine ⟨1998151130118701320652017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2664201506824935094202689 1998151130118701320652017)
            ·
              refine ⟨1498613347589025990489013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1998151130118701320652017 1498613347589025990489013)
              ·
                refine ⟨140495001336471186608345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1498613347589025990489013 140495001336471186608345)
                ·
                  rfl

theorem cell20_923444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 2, 5].length) (baseStart_923444 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_923444 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_923444 prefixEnd_923444 := by exact prefixLift 923444
  have htrace : WordTrace (prefixWord ++ tailWord_923444) baseStart_923444 baseEnd_923444 := by
    simpa [prefixWord, tailWord_923444, baseEnd_923444] using wordTrace_append hprefix tailTrace_923444
  have hstable : (prefixWord ++ tailWord_923444).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923444).length < 2 ^ (prefixWord ++ tailWord_923444).sum := by decide
  have hdescent : baseEnd_923444 < baseStart_923444 := by decide
  rcases family_descends (prefixWord ++ tailWord_923444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923448 : List Nat := [2, 1, 2, 1, 3, 3, 1, 7]
def baseStart_923448 : Nat := 118140960795 + 923448 * 2 ^ 59
def prefixEnd_923448 : Nat := 4983230072969 + 3 ^ 40 * 923448 * 2
def baseEnd_923448 : Nat := 140495609906135774563895

theorem tailTrace_923448 : CollatzResearch.WordTrace tailWord_923448 prefixEnd_923448 140495609906135774563895 := by
  unfold tailWord_923448
  simp only [CollatzResearch.WordTrace]
  refine ⟨16840457779256541603693499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22453943705675388804924665 16840457779256541603693499)
  ·
    refine ⟨25260686668884812405540249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16840457779256541603693499 25260686668884812405540249)
    ·
      refine ⟨18945515001663609304155187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25260686668884812405540249 18945515001663609304155187)
      ·
        refine ⟨28418272502495413956232781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18945515001663609304155187 28418272502495413956232781)
        ·
          refine ⟨10656852188435780233587293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28418272502495413956232781 10656852188435780233587293)
          ·
            refine ⟨3996319570663417587595235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10656852188435780233587293 3996319570663417587595235)
            ·
              refine ⟨5994479355995126381392853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3996319570663417587595235 5994479355995126381392853)
              ·
                refine ⟨140495609906135774563895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5994479355995126381392853 140495609906135774563895)
                ·
                  rfl

theorem cell20_923448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 7].length) (baseStart_923448 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_923448 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_923448 prefixEnd_923448 := by exact prefixLift 923448
  have htrace : WordTrace (prefixWord ++ tailWord_923448) baseStart_923448 baseEnd_923448 := by
    simpa [prefixWord, tailWord_923448, baseEnd_923448] using wordTrace_append hprefix tailTrace_923448
  have hstable : (prefixWord ++ tailWord_923448).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923448).length < 2 ^ (prefixWord ++ tailWord_923448).sum := by decide
  have hdescent : baseEnd_923448 < baseStart_923448 := by decide
  rcases family_descends (prefixWord ++ tailWord_923448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923524 : List Nat := [2, 3, 2, 1, 1, 1, 2, 8]
def baseStart_923524 : Nat := 118140960795 + 923524 * 2 ^ 59
def prefixEnd_923524 : Nat := 4983230072969 + 3 ^ 40 * 923524 * 2
def baseEnd_923524 : Nat := 140507172729762945719347

theorem tailTrace_923524 : CollatzResearch.WordTrace tailWord_923524 prefixEnd_923524 140507172729762945719347 := by
  unfold tailWord_923524
  simp only [CollatzResearch.WordTrace]
  refine ⟨16841843753118874093576813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22455791670825165458102417 16841843753118874093576813)
  ·
    refine ⟨6315691407419577785091305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16841843753118874093576813 6315691407419577785091305)
    ·
      refine ⟨4736768555564683338818479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6315691407419577785091305 4736768555564683338818479)
      ·
        refine ⟨7105152833347025008227719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4736768555564683338818479 7105152833347025008227719)
        ·
          refine ⟨10657729250020537512341579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7105152833347025008227719 10657729250020537512341579)
          ·
            refine ⟨15986593875030806268512369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10657729250020537512341579 15986593875030806268512369)
            ·
              refine ⟨11989945406273104701384277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15986593875030806268512369 11989945406273104701384277)
              ·
                refine ⟨140507172729762945719347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11989945406273104701384277 140507172729762945719347)
                ·
                  rfl

theorem cell20_923524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 8].length) (baseStart_923524 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_923524 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_923524 prefixEnd_923524 := by exact prefixLift 923524
  have htrace : WordTrace (prefixWord ++ tailWord_923524) baseStart_923524 baseEnd_923524 := by
    simpa [prefixWord, tailWord_923524, baseEnd_923524] using wordTrace_append hprefix tailTrace_923524
  have hstable : (prefixWord ++ tailWord_923524).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923524).length < 2 ^ (prefixWord ++ tailWord_923524).sum := by decide
  have hdescent : baseEnd_923524 < baseStart_923524 := by decide
  rcases family_descends (prefixWord ++ tailWord_923524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923530 : List Nat := [3, 1, 2, 4, 2, 1, 2, 3, 2]
def baseStart_923530 : Nat := 118140960795 + 923530 * 2 ^ 59
def prefixEnd_923530 : Nat := 4983230072969 + 3 ^ 40 * 923530 * 2
def baseEnd_923530 : Nat := 421524256752779482958017

theorem tailTrace_923530 : CollatzResearch.WordTrace tailWord_923530 prefixEnd_923530 421524256752779482958017 := by
  unfold tailWord_923530
  simp only [CollatzResearch.WordTrace]
  refine ⟨8420976586054002802968011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22455937562810674141248029 8420976586054002802968011)
  ·
    refine ⟨12631464879081004204452017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8420976586054002802968011 12631464879081004204452017)
    ·
      refine ⟨9473598659310753153339013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12631464879081004204452017 9473598659310753153339013)
      ·
        refine ⟨1776299748620766216251065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9473598659310753153339013 1776299748620766216251065)
        ·
          refine ⟨1332224811465574662188299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1776299748620766216251065 1332224811465574662188299)
          ·
            refine ⟨1998337217198361993282449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1332224811465574662188299 1998337217198361993282449)
            ·
              refine ⟨1498752912898771494961837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1998337217198361993282449 1498752912898771494961837)
              ·
                refine ⟨562032342337039310610689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1498752912898771494961837 562032342337039310610689)
                ·
                  refine ⟨421524256752779482958017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 562032342337039310610689 421524256752779482958017)
                  ·
                    rfl

theorem cell20_923530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 2, 3, 2].length) (baseStart_923530 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_923530 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_923530 prefixEnd_923530 := by exact prefixLift 923530
  have htrace : WordTrace (prefixWord ++ tailWord_923530) baseStart_923530 baseEnd_923530 := by
    simpa [prefixWord, tailWord_923530, baseEnd_923530] using wordTrace_append hprefix tailTrace_923530
  have hstable : (prefixWord ++ tailWord_923530).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923530).length < 2 ^ (prefixWord ++ tailWord_923530).sum := by decide
  have hdescent : baseEnd_923530 < baseStart_923530 := by decide
  rcases family_descends (prefixWord ++ tailWord_923530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923531 : List Nat := [1, 1, 1, 1, 4, 2, 1, 4, 5]
def baseStart_923531 : Nat := 118140960795 + 923531 * 2 ^ 59
def prefixEnd_923531 : Nat := 4983230072969 + 3 ^ 40 * 923531 * 2
def baseEnd_923531 : Nat := 421524713180027923924679

theorem tailTrace_923531 : CollatzResearch.WordTrace tailWord_923531 prefixEnd_923531 421524713180027923924679 := by
  unfold tailWord_923531
  simp only [CollatzResearch.WordTrace]
  refine ⟨33683942817212388382658447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22455961878141592255105631 33683942817212388382658447)
  ·
    refine ⟨50525914225818582573987671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33683942817212388382658447 50525914225818582573987671)
    ·
      refine ⟨75788871338727873860981507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50525914225818582573987671 75788871338727873860981507)
      ·
        refine ⟨113683307008091810791472261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75788871338727873860981507 113683307008091810791472261)
        ·
          refine ⟨21315620064017214523401049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 113683307008091810791472261 21315620064017214523401049)
          ·
            refine ⟨15986715048012910892550787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21315620064017214523401049 15986715048012910892550787)
            ·
              refine ⟨23980072572019366338826181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15986715048012910892550787 23980072572019366338826181)
              ·
                refine ⟨4496263607253631188529909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23980072572019366338826181 4496263607253631188529909)
                ·
                  refine ⟨421524713180027923924679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4496263607253631188529909 421524713180027923924679)
                  ·
                    rfl

theorem cell20_923531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 4, 5].length) (baseStart_923531 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_923531 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_923531 prefixEnd_923531 := by exact prefixLift 923531
  have htrace : WordTrace (prefixWord ++ tailWord_923531) baseStart_923531 baseEnd_923531 := by
    simpa [prefixWord, tailWord_923531, baseEnd_923531] using wordTrace_append hprefix tailTrace_923531
  have hstable : (prefixWord ++ tailWord_923531).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923531).length < 2 ^ (prefixWord ++ tailWord_923531).sum := by decide
  have hdescent : baseEnd_923531 < baseStart_923531 := by decide
  rcases family_descends (prefixWord ++ tailWord_923531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923606 : List Nat := [5, 2, 1, 1, 3, 2, 1, 1, 4]
def baseStart_923606 : Nat := 118140960795 + 923606 * 2 ^ 59
def prefixEnd_923606 : Nat := 4983230072969 + 3 ^ 40 * 923606 * 2
def baseEnd_923606 : Nat := 421558945223660996424373

theorem tailTrace_923606 : CollatzResearch.WordTrace tailWord_923606 prefixEnd_923606 421558945223660996424373 := by
  unfold tailWord_923606
  simp only [CollatzResearch.WordTrace]
  refine ⟨2105417393246292261977417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22457785527960450794425781 2105417393246292261977417)
  ·
    refine ⟨1579063044934719196483063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2105417393246292261977417 1579063044934719196483063)
    ·
      refine ⟨2368594567402078794724595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1579063044934719196483063 2368594567402078794724595)
      ·
        refine ⟨3552891851103118192086893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2368594567402078794724595 3552891851103118192086893)
        ·
          refine ⟨1332334444163669322032585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3552891851103118192086893 1332334444163669322032585)
          ·
            refine ⟨999250833122751991524439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1332334444163669322032585 999250833122751991524439)
            ·
              refine ⟨1498876249684127987286659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 999250833122751991524439 1498876249684127987286659)
              ·
                refine ⟨2248314374526191980929989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1498876249684127987286659 2248314374526191980929989)
                ·
                  refine ⟨421558945223660996424373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2248314374526191980929989 421558945223660996424373)
                  ·
                    rfl

theorem cell20_923606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_923606 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_923606 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_923606 prefixEnd_923606 := by exact prefixLift 923606
  have htrace : WordTrace (prefixWord ++ tailWord_923606) baseStart_923606 baseEnd_923606 := by
    simpa [prefixWord, tailWord_923606, baseEnd_923606] using wordTrace_append hprefix tailTrace_923606
  have hstable : (prefixWord ++ tailWord_923606).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923606).length < 2 ^ (prefixWord ++ tailWord_923606).sum := by decide
  have hdescent : baseEnd_923606 < baseStart_923606 := by decide
  rcases family_descends (prefixWord ++ tailWord_923606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923607 : List Nat := [1, 1, 3, 2, 1, 1, 3, 3, 5]
def baseStart_923607 : Nat := 118140960795 + 923607 * 2 ^ 59
def prefixEnd_923607 : Nat := 4983230072969 + 3 ^ 40 * 923607 * 2
def baseEnd_923607 : Nat := 421559401650909437391035

theorem tailTrace_923607 : CollatzResearch.WordTrace tailWord_923607 prefixEnd_923607 421559401650909437391035 := by
  unfold tailWord_923607
  simp only [CollatzResearch.WordTrace]
  refine ⟨33686714764937053362425075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22457809843291368908283383 33686714764937053362425075)
  ·
    refine ⟨50530072147405580043637613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33686714764937053362425075 50530072147405580043637613)
    ·
      refine ⟨18948777055277092516364105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50530072147405580043637613 18948777055277092516364105)
      ·
        refine ⟨14211582791457819387273079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18948777055277092516364105 14211582791457819387273079)
        ·
          refine ⟨21317374187186729080909619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14211582791457819387273079 21317374187186729080909619)
          ·
            refine ⟨31976061280780093621364429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21317374187186729080909619 31976061280780093621364429)
            ·
              refine ⟨11991022980292535108011661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31976061280780093621364429 11991022980292535108011661)
              ·
                refine ⟨4496633617609700665504373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11991022980292535108011661 4496633617609700665504373)
                ·
                  refine ⟨421559401650909437391035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4496633617609700665504373 421559401650909437391035)
                  ·
                    rfl

theorem cell20_923607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 3, 5].length) (baseStart_923607 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_923607 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_923607 prefixEnd_923607 := by exact prefixLift 923607
  have htrace : WordTrace (prefixWord ++ tailWord_923607) baseStart_923607 baseEnd_923607 := by
    simpa [prefixWord, tailWord_923607, baseEnd_923607] using wordTrace_append hprefix tailTrace_923607
  have hstable : (prefixWord ++ tailWord_923607).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923607).length < 2 ^ (prefixWord ++ tailWord_923607).sum := by decide
  have hdescent : baseEnd_923607 < baseStart_923607 := by decide
  rcases family_descends (prefixWord ++ tailWord_923607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923645 : List Nat := [1, 4, 1, 1, 1, 2, 2, 1, 7]
def baseStart_923645 : Nat := 118140960795 + 923645 * 2 ^ 59
def prefixEnd_923645 : Nat := 4983230072969 + 3 ^ 40 * 923645 * 2
def baseEnd_923645 : Nat := 421576745886350194124213

theorem tailTrace_923645 : CollatzResearch.WordTrace tailWord_923645 prefixEnd_923645 421576745886350194124213 := by
  unfold tailWord_923645
  simp only [CollatzResearch.WordTrace]
  refine ⟨33688100738799385852308389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22458733825866257234872259 33688100738799385852308389)
  ·
    refine ⟨6316518888524884847307823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33688100738799385852308389 6316518888524884847307823)
    ·
      refine ⟨9474778332787327270961735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6316518888524884847307823 9474778332787327270961735)
      ·
        refine ⟨14212167499180990906442603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9474778332787327270961735 14212167499180990906442603)
        ·
          refine ⟨21318251248771486359663905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14212167499180990906442603 21318251248771486359663905)
          ·
            refine ⟨15988688436578614769747929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21318251248771486359663905 15988688436578614769747929)
            ·
              refine ⟨11991516327433961077310947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15988688436578614769747929 11991516327433961077310947)
              ·
                refine ⟨17987274491150941615966421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11991516327433961077310947 17987274491150941615966421)
                ·
                  refine ⟨421576745886350194124213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17987274491150941615966421 421576745886350194124213)
                  ·
                    rfl

theorem cell20_923645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 1, 7].length) (baseStart_923645 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_923645 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_923645 prefixEnd_923645 := by exact prefixLift 923645
  have htrace : WordTrace (prefixWord ++ tailWord_923645) baseStart_923645 baseEnd_923645 := by
    simpa [prefixWord, tailWord_923645, baseEnd_923645] using wordTrace_append hprefix tailTrace_923645
  have hstable : (prefixWord ++ tailWord_923645).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923645).length < 2 ^ (prefixWord ++ tailWord_923645).sum := by decide
  have hdescent : baseEnd_923645 < baseStart_923645 := by decide
  rcases family_descends (prefixWord ++ tailWord_923645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923668 : List Nat := [2, 4, 3, 2, 2, 1, 1, 5]
def baseStart_923668 : Nat := 118140960795 + 923668 * 2 ^ 59
def prefixEnd_923668 : Nat := 4983230072969 + 3 ^ 40 * 923668 * 2
def baseEnd_923668 : Nat := 140529081237688112119151

theorem tailTrace_923668 : CollatzResearch.WordTrace tailWord_923668 prefixEnd_923668 140529081237688112119151 := by
  unfold tailWord_923668
  simp only [CollatzResearch.WordTrace]
  refine ⟨16844469808858030390197829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22459293078477373853597105 16844469808858030390197829)
  ·
    refine ⟨3158338089160880698162093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16844469808858030390197829 3158338089160880698162093)
    ·
      refine ⟨1184376783435330261810785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3158338089160880698162093 1184376783435330261810785)
      ·
        refine ⟨888282587576497696358089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1184376783435330261810785 888282587576497696358089)
        ·
          refine ⟨666211940682373272268567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 888282587576497696358089 666211940682373272268567)
          ·
            refine ⟨999317911023559908402851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 666211940682373272268567 999317911023559908402851)
            ·
              refine ⟨1498976866535339862604277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 999317911023559908402851 1498976866535339862604277)
              ·
                refine ⟨140529081237688112119151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1498976866535339862604277 140529081237688112119151)
                ·
                  rfl

theorem cell20_923668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 1, 5].length) (baseStart_923668 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_923668 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_923668 prefixEnd_923668 := by exact prefixLift 923668
  have htrace : WordTrace (prefixWord ++ tailWord_923668) baseStart_923668 baseEnd_923668 := by
    simpa [prefixWord, tailWord_923668, baseEnd_923668] using wordTrace_append hprefix tailTrace_923668
  have hstable : (prefixWord ++ tailWord_923668).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923668).length < 2 ^ (prefixWord ++ tailWord_923668).sum := by decide
  have hdescent : baseEnd_923668 < baseStart_923668 := by decide
  rcases family_descends (prefixWord ++ tailWord_923668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923721 : List Nat := [1, 2, 1, 1, 2, 2, 5, 1, 5]
def baseStart_923721 : Nat := 118140960795 + 923721 * 2 ^ 59
def prefixEnd_923721 : Nat := 4983230072969 + 3 ^ 40 * 923721 * 2
def baseEnd_923721 : Nat := 421611434357231707590569

theorem tailTrace_923721 : CollatzResearch.WordTrace tailWord_923721 prefixEnd_923721 421611434357231707590569 := by
  unfold tailWord_923721
  simp only [CollatzResearch.WordTrace]
  refine ⟨33690872686524050832075017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22460581791016033888050011 33690872686524050832075017)
  ·
    refine ⟨25268154514893038124056263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33690872686524050832075017 25268154514893038124056263)
    ·
      refine ⟨37902231772339557186084395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25268154514893038124056263 37902231772339557186084395)
      ·
        refine ⟨56853347658509335779126593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37902231772339557186084395 56853347658509335779126593)
        ·
          refine ⟨42640010743882001834344945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56853347658509335779126593 42640010743882001834344945)
          ·
            refine ⟨31980008057911501375758709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42640010743882001834344945 31980008057911501375758709)
            ·
              refine ⟨2998125755429203253977379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31980008057911501375758709 2998125755429203253977379)
              ·
                refine ⟨4497188633143804880966069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2998125755429203253977379 4497188633143804880966069)
                ·
                  refine ⟨421611434357231707590569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4497188633143804880966069 421611434357231707590569)
                  ·
                    rfl

theorem cell20_923721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 1, 5].length) (baseStart_923721 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_923721 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_923721 prefixEnd_923721 := by exact prefixLift 923721
  have htrace : WordTrace (prefixWord ++ tailWord_923721) baseStart_923721 baseEnd_923721 := by
    simpa [prefixWord, tailWord_923721, baseEnd_923721] using wordTrace_append hprefix tailTrace_923721
  have hstable : (prefixWord ++ tailWord_923721).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923721).length < 2 ^ (prefixWord ++ tailWord_923721).sum := by decide
  have hdescent : baseEnd_923721 < baseStart_923721 := by decide
  rcases family_descends (prefixWord ++ tailWord_923721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923724 : List Nat := [2, 2, 1, 3, 1, 1, 4, 4, 2]
def baseStart_923724 : Nat := 118140960795 + 923724 * 2 ^ 59
def prefixEnd_923724 : Nat := 4983230072969 + 3 ^ 40 * 923724 * 2
def baseEnd_923724 : Nat := 421612803638977030490557

theorem tailTrace_923724 : CollatzResearch.WordTrace tailWord_923724 prefixEnd_923724 421612803638977030490557 := by
  unfold tailWord_923724
  simp only [CollatzResearch.WordTrace]
  refine ⟨16845491052756591172217113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22460654737008788229622817 16845491052756591172217113)
  ·
    refine ⟨12634118289567443379162835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16845491052756591172217113 12634118289567443379162835)
    ·
      refine ⟨18951177434351165068744253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12634118289567443379162835 18951177434351165068744253)
      ·
        refine ⟨7106691537881686900779095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18951177434351165068744253 7106691537881686900779095)
        ·
          refine ⟨10660037306822530351168643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7106691537881686900779095 10660037306822530351168643)
          ·
            refine ⟨15990055960233795526752965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10660037306822530351168643 15990055960233795526752965)
            ·
              refine ⟨2998135492543836661266181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15990055960233795526752965 2998135492543836661266181)
              ·
                refine ⟨562150404851969373987409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2998135492543836661266181 562150404851969373987409)
                ·
                  refine ⟨421612803638977030490557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 562150404851969373987409 421612803638977030490557)
                  ·
                    rfl

theorem cell20_923724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 4, 2].length) (baseStart_923724 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_923724 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_923724 prefixEnd_923724 := by exact prefixLift 923724
  have htrace : WordTrace (prefixWord ++ tailWord_923724) baseStart_923724 baseEnd_923724 := by
    simpa [prefixWord, tailWord_923724, baseEnd_923724] using wordTrace_append hprefix tailTrace_923724
  have hstable : (prefixWord ++ tailWord_923724).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923724).length < 2 ^ (prefixWord ++ tailWord_923724).sum := by decide
  have hdescent : baseEnd_923724 < baseStart_923724 := by decide
  rcases family_descends (prefixWord ++ tailWord_923724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923759 : List Nat := [1, 1, 2, 1, 3, 4, 1, 2, 5]
def baseStart_923759 : Nat := 118140960795 + 923759 * 2 ^ 59
def prefixEnd_923759 : Nat := 4983230072969 + 3 ^ 40 * 923759 * 2
def baseEnd_923759 : Nat := 421628778592672464323747

theorem tailTrace_923759 : CollatzResearch.WordTrace tailWord_923759 prefixEnd_923759 421628778592672464323747 := by
  unfold tailWord_923759
  simp only [CollatzResearch.WordTrace]
  refine ⟨33692258660386383321958331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22461505773590922214638887 33692258660386383321958331)
  ·
    refine ⟨50538387990579574982937497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33692258660386383321958331 50538387990579574982937497)
    ·
      refine ⟨37903790992934681237203123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50538387990579574982937497 37903790992934681237203123)
      ·
        refine ⟨56855686489402021855804685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37903790992934681237203123 56855686489402021855804685)
        ·
          refine ⟨21320882433525758195926757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56855686489402021855804685 21320882433525758195926757)
          ·
            refine ⟨3997665456286079661736267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21320882433525758195926757 3997665456286079661736267)
            ·
              refine ⟨5996498184429119492604401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3997665456286079661736267 5996498184429119492604401)
              ·
                refine ⟨4497373638321839619453301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5996498184429119492604401 4497373638321839619453301)
                ·
                  refine ⟨421628778592672464323747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4497373638321839619453301 421628778592672464323747)
                  ·
                    rfl

theorem cell20_923759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 2, 5].length) (baseStart_923759 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_923759 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_923759 prefixEnd_923759 := by exact prefixLift 923759
  have htrace : WordTrace (prefixWord ++ tailWord_923759) baseStart_923759 baseEnd_923759 := by
    simpa [prefixWord, tailWord_923759, baseEnd_923759] using wordTrace_append hprefix tailTrace_923759
  have hstable : (prefixWord ++ tailWord_923759).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923759).length < 2 ^ (prefixWord ++ tailWord_923759).sum := by decide
  have hdescent : baseEnd_923759 < baseStart_923759 := by decide
  rcases family_descends (prefixWord ++ tailWord_923759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923779 : List Nat := [1, 1, 1, 3, 3, 4, 3, 2, 2]
def baseStart_923779 : Nat := 118140960795 + 923779 * 2 ^ 59
def prefixEnd_923779 : Nat := 4983230072969 + 3 ^ 40 * 923779 * 2
def baseEnd_923779 : Nat := 421637907137641283656999

theorem tailTrace_923779 : CollatzResearch.WordTrace tailWord_923779 prefixEnd_923779 421637907137641283656999 := by
  unfold tailWord_923779
  simp only [CollatzResearch.WordTrace]
  refine ⟨33692988120313926737686391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22461992080209284491790927 33692988120313926737686391)
  ·
    refine ⟨50539482180470890106529587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33692988120313926737686391 50539482180470890106529587)
    ·
      refine ⟨75809223270706335159794381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50539482180470890106529587 75809223270706335159794381)
      ·
        refine ⟨28428458726514875684922893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75809223270706335159794381 28428458726514875684922893)
        ·
          refine ⟨10660672022443078381846085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28428458726514875684922893 10660672022443078381846085)
          ·
            refine ⟨1998876004208077196596141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10660672022443078381846085 1998876004208077196596141)
            ·
              refine ⟨749578501578028948723553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1998876004208077196596141 749578501578028948723553)
              ·
                refine ⟨562183876183521711542665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 749578501578028948723553 562183876183521711542665)
                ·
                  refine ⟨421637907137641283656999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 562183876183521711542665 421637907137641283656999)
                  ·
                    rfl

theorem cell20_923779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 3, 2, 2].length) (baseStart_923779 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_923779 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_923779 prefixEnd_923779 := by exact prefixLift 923779
  have htrace : WordTrace (prefixWord ++ tailWord_923779) baseStart_923779 baseEnd_923779 := by
    simpa [prefixWord, tailWord_923779, baseEnd_923779] using wordTrace_append hprefix tailTrace_923779
  have hstable : (prefixWord ++ tailWord_923779).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923779).length < 2 ^ (prefixWord ++ tailWord_923779).sum := by decide
  have hdescent : baseEnd_923779 < baseStart_923779 := by decide
  rcases family_descends (prefixWord ++ tailWord_923779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923783 : List Nat := [1, 1, 4, 2, 1, 1, 5, 1, 4]
def baseStart_923783 : Nat := 118140960795 + 923783 * 2 ^ 59
def prefixEnd_923783 : Nat := 4983230072969 + 3 ^ 40 * 923783 * 2
def baseEnd_923783 : Nat := 421639732846635047523649

theorem tailTrace_923783 : CollatzResearch.WordTrace tailWord_923783 prefixEnd_923783 421639732846635047523649 := by
  unfold tailWord_923783
  simp only [CollatzResearch.WordTrace]
  refine ⟨33693134012299435420832003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22462089341532956947221335 33693134012299435420832003)
  ·
    refine ⟨50539701018449153131248005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33693134012299435420832003 50539701018449153131248005)
    ·
      refine ⟨9476193940959216212109001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50539701018449153131248005 9476193940959216212109001)
      ·
        refine ⟨7107145455719412159081751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9476193940959216212109001 7107145455719412159081751)
        ·
          refine ⟨10660718183579118238622627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7107145455719412159081751 10660718183579118238622627)
          ·
            refine ⟨15991077275368677357933941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10660718183579118238622627 15991077275368677357933941)
            ·
              refine ⟨1499163494565813502306307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15991077275368677357933941 1499163494565813502306307)
              ·
                refine ⟨2248745241848720253459461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1499163494565813502306307 2248745241848720253459461)
                ·
                  refine ⟨421639732846635047523649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2248745241848720253459461 421639732846635047523649)
                  ·
                    rfl

theorem cell20_923783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 5, 1, 4].length) (baseStart_923783 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_923783 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_923783 prefixEnd_923783 := by exact prefixLift 923783
  have htrace : WordTrace (prefixWord ++ tailWord_923783) baseStart_923783 baseEnd_923783 := by
    simpa [prefixWord, tailWord_923783, baseEnd_923783] using wordTrace_append hprefix tailTrace_923783
  have hstable : (prefixWord ++ tailWord_923783).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923783).length < 2 ^ (prefixWord ++ tailWord_923783).sum := by decide
  have hdescent : baseEnd_923783 < baseStart_923783 := by decide
  rcases family_descends (prefixWord ++ tailWord_923783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923841 : List Nat := [1, 2, 6, 1, 3, 1, 1, 5]
def baseStart_923841 : Nat := 118140960795 + 923841 * 2 ^ 59
def prefixEnd_923841 : Nat := 4983230072969 + 3 ^ 40 * 923841 * 2
def baseEnd_923841 : Nat := 140555401875681541196693

theorem tailTrace_923841 : CollatzResearch.WordTrace tailWord_923841 prefixEnd_923841 140555401875681541196693 := by
  unfold tailWord_923841
  simp only [CollatzResearch.WordTrace]
  refine ⟨33695249446089311326443377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22463499630726207550962251 33695249446089311326443377)
  ·
    refine ⟨25271437084566983494832533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33695249446089311326443377 25271437084566983494832533)
    ·
      refine ⟨1184598613339077351320275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 25271437084566983494832533 1184598613339077351320275)
      ·
        refine ⟨1776897920008616026980413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1184598613339077351320275 1776897920008616026980413)
        ·
          refine ⟨666336720003231010117655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1776897920008616026980413 666336720003231010117655)
          ·
            refine ⟨999505080004846515176483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 666336720003231010117655 999505080004846515176483)
            ·
              refine ⟨1499257620007269772764725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 999505080004846515176483 1499257620007269772764725)
              ·
                refine ⟨140555401875681541196693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1499257620007269772764725 140555401875681541196693)
                ·
                  rfl

theorem cell20_923841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 1, 5].length) (baseStart_923841 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_923841 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_923841 prefixEnd_923841 := by exact prefixLift 923841
  have htrace : WordTrace (prefixWord ++ tailWord_923841) baseStart_923841 baseEnd_923841 := by
    simpa [prefixWord, tailWord_923841, baseEnd_923841] using wordTrace_append hprefix tailTrace_923841
  have hstable : (prefixWord ++ tailWord_923841).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923841).length < 2 ^ (prefixWord ++ tailWord_923841).sum := by decide
  have hdescent : baseEnd_923841 < baseStart_923841 := by decide
  rcases family_descends (prefixWord ++ tailWord_923841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923849 : List Nat := [1, 2, 1, 1, 2, 1, 1, 11]
def baseStart_923849 : Nat := 118140960795 + 923849 * 2 ^ 59
def prefixEnd_923849 : Nat := 4983230072969 + 3 ^ 40 * 923849 * 2
def baseEnd_923849 : Nat := 140556619015010717107793

theorem tailTrace_923849 : CollatzResearch.WordTrace tailWord_923849 prefixEnd_923849 140556619015010717107793 := by
  unfold tailWord_923849
  simp only [CollatzResearch.WordTrace]
  refine ⟨33695541230060328692734601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22463694153373552461823067 33695541230060328692734601)
  ·
    refine ⟨25271655922545246519550951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33695541230060328692734601 25271655922545246519550951)
    ·
      refine ⟨37907483883817869779326427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25271655922545246519550951 37907483883817869779326427)
      ·
        refine ⟨56861225825726804668989641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37907483883817869779326427 56861225825726804668989641)
        ·
          refine ⟨42645919369295103501742231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56861225825726804668989641 42645919369295103501742231)
          ·
            refine ⟨63968879053942655252613347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42645919369295103501742231 63968879053942655252613347)
            ·
              refine ⟨95953318580913982878920021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63968879053942655252613347 95953318580913982878920021)
              ·
                refine ⟨140556619015010717107793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 95953318580913982878920021 140556619015010717107793)
                ·
                  rfl

theorem cell20_923849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 11].length) (baseStart_923849 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_923849 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_923849 prefixEnd_923849 := by exact prefixLift 923849
  have htrace : WordTrace (prefixWord ++ tailWord_923849) baseStart_923849 baseEnd_923849 := by
    simpa [prefixWord, tailWord_923849, baseEnd_923849] using wordTrace_append hprefix tailTrace_923849
  have hstable : (prefixWord ++ tailWord_923849).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923849).length < 2 ^ (prefixWord ++ tailWord_923849).sum := by decide
  have hdescent : baseEnd_923849 < baseStart_923849 := by decide
  rcases family_descends (prefixWord ++ tailWord_923849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923873 : List Nat := [1, 2, 3, 1, 3, 1, 2, 2, 5]
def baseStart_923873 : Nat := 118140960795 + 923873 * 2 ^ 59
def prefixEnd_923873 : Nat := 4983230072969 + 3 ^ 40 * 923873 * 2
def baseEnd_923873 : Nat := 421680811298994734523281

theorem tailTrace_923873 : CollatzResearch.WordTrace tailWord_923873 prefixEnd_923873 421680811298994734523281 := by
  unfold tailWord_923873
  simp only [CollatzResearch.WordTrace]
  refine ⟨33696416581973380791608273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22464277721315587194405515 33696416581973380791608273)
  ·
    refine ⟨25272312436480035593706205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33696416581973380791608273 25272312436480035593706205)
    ·
      refine ⟨9477117163680013347639827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25272312436480035593706205 9477117163680013347639827)
      ·
        refine ⟨14215675745520020021459741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9477117163680013347639827 14215675745520020021459741)
        ·
          refine ⟨5330878404570007508047403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14215675745520020021459741 5330878404570007508047403)
          ·
            refine ⟨7996317606855011262071105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5330878404570007508047403 7996317606855011262071105)
            ·
              refine ⟨5997238205141258446553329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7996317606855011262071105 5997238205141258446553329)
              ·
                refine ⟨4497928653855943834914997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5997238205141258446553329 4497928653855943834914997)
                ·
                  refine ⟨421680811298994734523281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4497928653855943834914997 421680811298994734523281)
                  ·
                    rfl

theorem cell20_923873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 2, 5].length) (baseStart_923873 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_923873 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_923873 prefixEnd_923873 := by exact prefixLift 923873
  have htrace : WordTrace (prefixWord ++ tailWord_923873) baseStart_923873 baseEnd_923873 := by
    simpa [prefixWord, tailWord_923873, baseEnd_923873] using wordTrace_append hprefix tailTrace_923873
  have hstable : (prefixWord ++ tailWord_923873).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923873).length < 2 ^ (prefixWord ++ tailWord_923873).sum := by decide
  have hdescent : baseEnd_923873 < baseStart_923873 := by decide
  rcases family_descends (prefixWord ++ tailWord_923873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923890 : List Nat := [3, 2, 1, 3, 2, 2, 1, 1, 5]
def baseStart_923890 : Nat := 118140960795 + 923890 * 2 ^ 59
def prefixEnd_923890 : Nat := 4983230072969 + 3 ^ 40 * 923890 * 2
def baseEnd_923890 : Nat := 421688570562218230956545

theorem tailTrace_923890 : CollatzResearch.WordTrace tailWord_923890 prefixEnd_923890 421688570562218230956545 := by
  unfold tailWord_923890
  simp only [CollatzResearch.WordTrace]
  refine ⟨8424259155727948173744281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22464691081941195129984749 8424259155727948173744281)
  ·
    refine ⟨6318194366795961130308211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8424259155727948173744281 6318194366795961130308211)
    ·
      refine ⟨9477291550193941695462317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6318194366795961130308211 9477291550193941695462317)
      ·
        refine ⟨3553984331322728135798369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9477291550193941695462317 3553984331322728135798369)
        ·
          refine ⟨2665488248492046101848777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3553984331322728135798369 2665488248492046101848777)
          ·
            refine ⟨1999116186369034576386583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2665488248492046101848777 1999116186369034576386583)
            ·
              refine ⟨2998674279553551864579875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1999116186369034576386583 2998674279553551864579875)
              ·
                refine ⟨4498011419330327796869813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2998674279553551864579875 4498011419330327796869813)
                ·
                  refine ⟨421688570562218230956545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4498011419330327796869813 421688570562218230956545)
                  ·
                    rfl

theorem cell20_923890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 1, 5].length) (baseStart_923890 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_923890 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_923890 prefixEnd_923890 := by exact prefixLift 923890
  have htrace : WordTrace (prefixWord ++ tailWord_923890) baseStart_923890 baseEnd_923890 := by
    simpa [prefixWord, tailWord_923890, baseEnd_923890] using wordTrace_append hprefix tailTrace_923890
  have hstable : (prefixWord ++ tailWord_923890).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923890).length < 2 ^ (prefixWord ++ tailWord_923890).sum := by decide
  have hdescent : baseEnd_923890 < baseStart_923890 := by decide
  rcases family_descends (prefixWord ++ tailWord_923890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923921 : List Nat := [1, 2, 2, 1, 1, 7, 2, 4]
def baseStart_923921 : Nat := 118140960795 + 923921 * 2 ^ 59
def prefixEnd_923921 : Nat := 4983230072969 + 3 ^ 40 * 923921 * 2
def baseEnd_923921 : Nat := 140567573268973300307695

theorem tailTrace_923921 : CollatzResearch.WordTrace tailWord_923921 prefixEnd_923921 140567573268973300307695 := by
  unfold tailWord_923921
  simp only [CollatzResearch.WordTrace]
  refine ⟨33698167285799484989355617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22465444857199656659570411 33698167285799484989355617)
  ·
    refine ⟨25273625464349613742016713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33698167285799484989355617 25273625464349613742016713)
    ·
      refine ⟨18955219098262210306512535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25273625464349613742016713 18955219098262210306512535)
      ·
        refine ⟨28432828647393315459768803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18955219098262210306512535 28432828647393315459768803)
        ·
          refine ⟨42649242971089973189653205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28432828647393315459768803 42649242971089973189653205)
          ·
            refine ⟨999591632134921246632497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 42649242971089973189653205 999591632134921246632497)
            ·
              refine ⟨749693724101190934974373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 999591632134921246632497 749693724101190934974373)
              ·
                refine ⟨140567573268973300307695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 749693724101190934974373 140567573268973300307695)
                ·
                  rfl

theorem cell20_923921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 2, 4].length) (baseStart_923921 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_923921 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_923921 prefixEnd_923921 := by exact prefixLift 923921
  have htrace : WordTrace (prefixWord ++ tailWord_923921) baseStart_923921 baseEnd_923921 := by
    simpa [prefixWord, tailWord_923921, baseEnd_923921] using wordTrace_append hprefix tailTrace_923921
  have hstable : (prefixWord ++ tailWord_923921).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923921).length < 2 ^ (prefixWord ++ tailWord_923921).sum := by decide
  have hdescent : baseEnd_923921 < baseStart_923921 := by decide
  rcases family_descends (prefixWord ++ tailWord_923921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924004 : List Nat := [2, 3, 1, 1, 3, 1, 4, 2, 3]
def baseStart_924004 : Nat := 118140960795 + 924004 * 2 ^ 59
def prefixEnd_924004 : Nat := 4983230072969 + 3 ^ 40 * 924004 * 2
def baseEnd_924004 : Nat := 421740603268540501156079

theorem tailTrace_924004 : CollatzResearch.WordTrace tailWord_924004 prefixEnd_924004 421740603268540501156079 := by
  unfold tailWord_924004
  simp only [CollatzResearch.WordTrace]
  refine ⟨16850597272249395082313533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22467463029665860109751377 16850597272249395082313533)
  ·
    refine ⟨6318973977093523155867575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16850597272249395082313533 6318973977093523155867575)
    ·
      refine ⟨9478460965640284733801363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6318973977093523155867575 9478460965640284733801363)
      ·
        refine ⟨14217691448460427100702045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9478460965640284733801363 14217691448460427100702045)
        ·
          refine ⟨5331634293172660162763267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14217691448460427100702045 5331634293172660162763267)
          ·
            refine ⟨7997451439758990244144901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5331634293172660162763267 7997451439758990244144901)
            ·
              refine ⟨1499522144954810670777169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7997451439758990244144901 1499522144954810670777169)
              ·
                refine ⟨1124641608716108003082877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1499522144954810670777169 1124641608716108003082877)
                ·
                  refine ⟨421740603268540501156079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1124641608716108003082877 421740603268540501156079)
                  ·
                    rfl

theorem cell20_924004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 4, 2, 3].length) (baseStart_924004 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_924004 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_924004 prefixEnd_924004 := by exact prefixLift 924004
  have htrace : WordTrace (prefixWord ++ tailWord_924004) baseStart_924004 baseEnd_924004 := by
    simpa [prefixWord, tailWord_924004, baseEnd_924004] using wordTrace_append hprefix tailTrace_924004
  have hstable : (prefixWord ++ tailWord_924004).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924004).length < 2 ^ (prefixWord ++ tailWord_924004).sum := by decide
  have hdescent : baseEnd_924004 < baseStart_924004 := by decide
  rcases family_descends (prefixWord ++ tailWord_924004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924007 : List Nat := [1, 1, 5, 1, 3, 1, 4, 2, 2]
def baseStart_924007 : Nat := 118140960795 + 924007 * 2 ^ 59
def prefixEnd_924007 : Nat := 4983230072969 + 3 ^ 40 * 924007 * 2
def baseEnd_924007 : Nat := 421741972550285824056067

theorem tailTrace_924007 : CollatzResearch.WordTrace tailWord_924007 prefixEnd_924007 421741972550285824056067 := by
  unfold tailWord_924007
  simp only [CollatzResearch.WordTrace]
  refine ⟨33701303963487921676986275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22467535975658614451324183 33701303963487921676986275)
  ·
    refine ⟨50551955945231882515479413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33701303963487921676986275 50551955945231882515479413)
    ·
      refine ⟨4739245869865488985826195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 50551955945231882515479413 4739245869865488985826195)
      ·
        refine ⟨7108868804798233478739293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4739245869865488985826195 7108868804798233478739293)
        ·
          refine ⟨2665825801799337554527235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7108868804798233478739293 2665825801799337554527235)
          ·
            refine ⟨3998738702699006331790853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2665825801799337554527235 3998738702699006331790853)
            ·
              refine ⟨749763506756063687210785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3998738702699006331790853 749763506756063687210785)
              ·
                refine ⟨562322630067047765408089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 749763506756063687210785 562322630067047765408089)
                ·
                  refine ⟨421741972550285824056067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 562322630067047765408089 421741972550285824056067)
                  ·
                    rfl

theorem cell20_924007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 4, 2, 2].length) (baseStart_924007 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_924007 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_924007 prefixEnd_924007 := by exact prefixLift 924007
  have htrace : WordTrace (prefixWord ++ tailWord_924007) baseStart_924007 baseEnd_924007 := by
    simpa [prefixWord, tailWord_924007, baseEnd_924007] using wordTrace_append hprefix tailTrace_924007
  have hstable : (prefixWord ++ tailWord_924007).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924007).length < 2 ^ (prefixWord ++ tailWord_924007).sum := by decide
  have hdescent : baseEnd_924007 < baseStart_924007 := by decide
  rcases family_descends (prefixWord ++ tailWord_924007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924011 : List Nat := [1, 1, 1, 1, 2, 2, 2, 8, 2]
def baseStart_924011 : Nat := 118140960795 + 924011 * 2 ^ 59
def prefixEnd_924011 : Nat := 4983230072969 + 3 ^ 40 * 924011 * 2
def baseEnd_924011 : Nat := 421743798259279587922717

theorem tailTrace_924011 : CollatzResearch.WordTrace tailWord_924011 prefixEnd_924011 421743798259279587922717 := by
  unfold tailWord_924011
  simp only [CollatzResearch.WordTrace]
  refine ⟨33701449855473430360131887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22467633236982286906754591 33701449855473430360131887)
  ·
    refine ⟨50552174783210145540197831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33701449855473430360131887 50552174783210145540197831)
    ·
      refine ⟨75828262174815218310296747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50552174783210145540197831 75828262174815218310296747)
      ·
        refine ⟨113742393262222827465445121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75828262174815218310296747 113742393262222827465445121)
        ·
          refine ⟨85306794946667120599083841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113742393262222827465445121 85306794946667120599083841)
          ·
            refine ⟨63980096210000340449312881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85306794946667120599083841 63980096210000340449312881)
            ·
              refine ⟨47985072157500255336984661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63980096210000340449312881 47985072157500255336984661)
              ·
                refine ⟨562325064345706117230289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 47985072157500255336984661 562325064345706117230289)
                ·
                  refine ⟨421743798259279587922717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 562325064345706117230289 421743798259279587922717)
                  ·
                    rfl

theorem cell20_924011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 8, 2].length) (baseStart_924011 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_924011 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_924011 prefixEnd_924011 := by exact prefixLift 924011
  have htrace : WordTrace (prefixWord ++ tailWord_924011) baseStart_924011 baseEnd_924011 := by
    simpa [prefixWord, tailWord_924011, baseEnd_924011] using wordTrace_append hprefix tailTrace_924011
  have hstable : (prefixWord ++ tailWord_924011).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924011).length < 2 ^ (prefixWord ++ tailWord_924011).sum := by decide
  have hdescent : baseEnd_924011 < baseStart_924011 := by decide
  rcases family_descends (prefixWord ++ tailWord_924011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924018 : List Nat := [3, 2, 1, 2, 1, 3, 3, 5]
def baseStart_924018 : Nat := 118140960795 + 924018 * 2 ^ 59
def prefixEnd_924018 : Nat := 4983230072969 + 3 ^ 40 * 924018 * 2
def baseEnd_924018 : Nat := 140582331083339558229785

theorem tailTrace_924018 : CollatzResearch.WordTrace tailWord_924018 prefixEnd_924018 140582331083339558229785 := by
  unfold tailWord_924018
  simp only [CollatzResearch.WordTrace]
  refine ⟨8425426291612017638909177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22467803444298713703757805 8425426291612017638909177)
  ·
    refine ⟨6319069718709013229181883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8425426291612017638909177 6319069718709013229181883)
    ·
      refine ⟨9478604578063519843772825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6319069718709013229181883 9478604578063519843772825)
      ·
        refine ⟨7108953433547639882829619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9478604578063519843772825 7108953433547639882829619)
        ·
          refine ⟨10663430150321459824244429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7108953433547639882829619 10663430150321459824244429)
          ·
            refine ⟨3998786306370547434091661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10663430150321459824244429 3998786306370547434091661)
            ·
              refine ⟨1499544864888955287784373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3998786306370547434091661 1499544864888955287784373)
              ·
                refine ⟨140582331083339558229785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1499544864888955287784373 140582331083339558229785)
                ·
                  rfl

theorem cell20_924018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 3, 5].length) (baseStart_924018 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_924018 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_924018 prefixEnd_924018 := by exact prefixLift 924018
  have htrace : WordTrace (prefixWord ++ tailWord_924018) baseStart_924018 baseEnd_924018 := by
    simpa [prefixWord, tailWord_924018, baseEnd_924018] using wordTrace_append hprefix tailTrace_924018
  have hstable : (prefixWord ++ tailWord_924018).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924018).length < 2 ^ (prefixWord ++ tailWord_924018).sum := by decide
  have hdescent : baseEnd_924018 < baseStart_924018 := by decide
  rcases family_descends (prefixWord ++ tailWord_924018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924035 : List Nat := [1, 1, 1, 3, 6, 1, 3, 4]
def baseStart_924035 : Nat := 118140960795 + 924035 * 2 ^ 59
def prefixEnd_924035 : Nat := 4983230072969 + 3 ^ 40 * 924035 * 2
def baseEnd_924035 : Nat := 140584917504414057040873

theorem tailTrace_924035 : CollatzResearch.WordTrace tailWord_924035 prefixEnd_924035 140584917504414057040873 := by
  unfold tailWord_924035
  simp only [CollatzResearch.WordTrace]
  refine ⟨33702325207386482459005559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22468216804924321639337039 33702325207386482459005559)
  ·
    refine ⟨50553487811079723688508339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33702325207386482459005559 50553487811079723688508339)
    ·
      refine ⟨75830231716619585532762509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50553487811079723688508339 75830231716619585532762509)
      ·
        refine ⟨28436336893732344574785941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75830231716619585532762509 28436336893732344574785941)
        ·
          refine ⟨1332953291893703651943091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 28436336893732344574785941 1332953291893703651943091)
          ·
            refine ⟨1999429937840555477914637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1332953291893703651943091 1999429937840555477914637)
            ·
              refine ⟨749786226690208304217989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1999429937840555477914637 749786226690208304217989)
              ·
                refine ⟨140584917504414057040873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 749786226690208304217989 140584917504414057040873)
                ·
                  rfl

theorem cell20_924035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 3, 4].length) (baseStart_924035 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_924035 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_924035 prefixEnd_924035 := by exact prefixLift 924035
  have htrace : WordTrace (prefixWord ++ tailWord_924035) baseStart_924035 baseEnd_924035 := by
    simpa [prefixWord, tailWord_924035, baseEnd_924035] using wordTrace_append hprefix tailTrace_924035
  have hstable : (prefixWord ++ tailWord_924035).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924035).length < 2 ^ (prefixWord ++ tailWord_924035).sum := by decide
  have hdescent : baseEnd_924035 < baseStart_924035 := by decide
  rcases family_descends (prefixWord ++ tailWord_924035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924056 : List Nat := [2, 1, 2, 5, 1, 2, 7]
def baseStart_924056 : Nat := 118140960795 + 924056 * 2 ^ 59
def prefixEnd_924056 : Nat := 4983230072969 + 3 ^ 40 * 924056 * 2
def baseEnd_924056 : Nat := 46862704165051047935837

theorem tailTrace_924056 : CollatzResearch.WordTrace tailWord_924056 prefixEnd_924056 46862704165051047935837 := by
  unfold tailWord_924056
  simp only [CollatzResearch.WordTrace]
  refine ⟨16851545570155201522760011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22468727426873602030346681 16851545570155201522760011)
  ·
    refine ⟨25277318355232802284140017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16851545570155201522760011 25277318355232802284140017)
    ·
      refine ⟨18957988766424601713105013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25277318355232802284140017 18957988766424601713105013)
      ·
        refine ⟨1777311446852306410603595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18957988766424601713105013 1777311446852306410603595)
        ·
          refine ⟨2665967170278459615905393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1777311446852306410603595 2665967170278459615905393)
          ·
            refine ⟨1999475377708844711929045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2665967170278459615905393 1999475377708844711929045)
            ·
              refine ⟨46862704165051047935837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1999475377708844711929045 46862704165051047935837)
              ·
                rfl

theorem cell20_924056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 7].length) (baseStart_924056 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_924056 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_924056 prefixEnd_924056 := by exact prefixLift 924056
  have htrace : WordTrace (prefixWord ++ tailWord_924056) baseStart_924056 baseEnd_924056 := by
    simpa [prefixWord, tailWord_924056, baseEnd_924056] using wordTrace_append hprefix tailTrace_924056
  have hstable : (prefixWord ++ tailWord_924056).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924056).length < 2 ^ (prefixWord ++ tailWord_924056).sum := by decide
  have hdescent : baseEnd_924056 < baseStart_924056 := by decide
  rcases family_descends (prefixWord ++ tailWord_924056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924063 : List Nat := [1, 1, 2, 5, 1, 1, 3, 1, 5]
def baseStart_924063 : Nat := 118140960795 + 924063 * 2 ^ 59
def prefixEnd_924063 : Nat := 4983230072969 + 3 ^ 40 * 924063 * 2
def baseEnd_924063 : Nat := 421767532476198518189171

theorem tailTrace_924063 : CollatzResearch.WordTrace tailWord_924063 prefixEnd_924063 421767532476198518189171 := by
  unfold tailWord_924063
  simp only [CollatzResearch.WordTrace]
  refine ⟨33703346451285043241024843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22468897634190028827349895 33703346451285043241024843)
  ·
    refine ⟨50555019676927564861537265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33703346451285043241024843 50555019676927564861537265)
    ·
      refine ⟨37916264757695673646152949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50555019676927564861537265 37916264757695673646152949)
      ·
        refine ⟨3554649821033969404326839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37916264757695673646152949 3554649821033969404326839)
        ·
          refine ⟨5331974731550954106490259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3554649821033969404326839 5331974731550954106490259)
          ·
            refine ⟨7997962097326431159735389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5331974731550954106490259 7997962097326431159735389)
            ·
              refine ⟨2999235786497411684900771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7997962097326431159735389 2999235786497411684900771)
              ·
                refine ⟨4498853679746117527351157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2999235786497411684900771 4498853679746117527351157)
                ·
                  refine ⟨421767532476198518189171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4498853679746117527351157 421767532476198518189171)
                  ·
                    rfl

theorem cell20_924063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 1, 5].length) (baseStart_924063 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_924063 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_924063 prefixEnd_924063 := by exact prefixLift 924063
  have htrace : WordTrace (prefixWord ++ tailWord_924063) baseStart_924063 baseEnd_924063 := by
    simpa [prefixWord, tailWord_924063, baseEnd_924063] using wordTrace_append hprefix tailTrace_924063
  have hstable : (prefixWord ++ tailWord_924063).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924063).length < 2 ^ (prefixWord ++ tailWord_924063).sum := by decide
  have hdescent : baseEnd_924063 < baseStart_924063 := by decide
  rcases family_descends (prefixWord ++ tailWord_924063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924066 : List Nat := [3, 3, 1, 2, 1, 1, 1, 6, 2]
def baseStart_924066 : Nat := 118140960795 + 924066 * 2 ^ 59
def prefixEnd_924066 : Nat := 4983230072969 + 3 ^ 40 * 924066 * 2
def baseEnd_924066 : Nat := 421768901757943841089159

theorem tailTrace_924066 : CollatzResearch.WordTrace tailWord_924066 prefixEnd_924066 421768901757943841089159 := by
  unfold tailWord_924066
  simp only [CollatzResearch.WordTrace]
  refine ⟨8425863967568543688346013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22468970580182783168922701 8425863967568543688346013)
  ·
    refine ⟨3159698987838203883129755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8425863967568543688346013 3159698987838203883129755)
    ·
      refine ⟨4739548481757305824694633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3159698987838203883129755 4739548481757305824694633)
      ·
        refine ⟨3554661361317979368520975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4739548481757305824694633 3554661361317979368520975)
        ·
          refine ⟨5331992041976969052781463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3554661361317979368520975 5331992041976969052781463)
          ·
            refine ⟨7997988062965453579172195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5331992041976969052781463 7997988062965453579172195)
            ·
              refine ⟨11996982094448180368758293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7997988062965453579172195 11996982094448180368758293)
              ·
                refine ⟨562358535677258454785545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11996982094448180368758293 562358535677258454785545)
                ·
                  refine ⟨421768901757943841089159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 562358535677258454785545 421768901757943841089159)
                  ·
                    rfl

theorem cell20_924066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 6, 2].length) (baseStart_924066 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_924066 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_924066 prefixEnd_924066 := by exact prefixLift 924066
  have htrace : WordTrace (prefixWord ++ tailWord_924066) baseStart_924066 baseEnd_924066 := by
    simpa [prefixWord, tailWord_924066, baseEnd_924066] using wordTrace_append hprefix tailTrace_924066
  have hstable : (prefixWord ++ tailWord_924066).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924066).length < 2 ^ (prefixWord ++ tailWord_924066).sum := by decide
  have hdescent : baseEnd_924066 < baseStart_924066 := by decide
  rcases family_descends (prefixWord ++ tailWord_924066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924100 : List Nat := [2, 3, 3, 2, 2, 2, 1, 3, 2]
def baseStart_924100 : Nat := 118140960795 + 924100 * 2 ^ 59
def prefixEnd_924100 : Nat := 4983230072969 + 3 ^ 40 * 924100 * 2
def baseEnd_924100 : Nat := 421784420284390833955687

theorem tailTrace_924100 : CollatzResearch.WordTrace tailWord_924100 prefixEnd_924100 421784420284390833955687 := by
  unfold tailWord_924100
  simp only [CollatzResearch.WordTrace]
  refine ⟨16852347976075499280060877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22469797301433999040081169 16852347976075499280060877)
  ·
    refine ⟨6319630491028312230022829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16852347976075499280060877 6319630491028312230022829)
    ·
      refine ⟨2369861434135617086258561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6319630491028312230022829 2369861434135617086258561)
      ·
        refine ⟨1777396075601712814693921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2369861434135617086258561 1777396075601712814693921)
        ·
          refine ⟨1333047056701284611020441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1777396075601712814693921 1333047056701284611020441)
          ·
            refine ⟨999785292525963458265331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1333047056701284611020441 999785292525963458265331)
            ·
              refine ⟨1499677938788945187397997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 999785292525963458265331 1499677938788945187397997)
              ·
                refine ⟨562379227045854445274249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1499677938788945187397997 562379227045854445274249)
                ·
                  refine ⟨421784420284390833955687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 562379227045854445274249 421784420284390833955687)
                  ·
                    rfl

theorem cell20_924100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 1, 3, 2].length) (baseStart_924100 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_924100 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_924100 prefixEnd_924100 := by exact prefixLift 924100
  have htrace : WordTrace (prefixWord ++ tailWord_924100) baseStart_924100 baseEnd_924100 := by
    simpa [prefixWord, tailWord_924100, baseEnd_924100] using wordTrace_append hprefix tailTrace_924100
  have hstable : (prefixWord ++ tailWord_924100).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924100).length < 2 ^ (prefixWord ++ tailWord_924100).sum := by decide
  have hdescent : baseEnd_924100 < baseStart_924100 := by decide
  rcases family_descends (prefixWord ++ tailWord_924100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924104 : List Nat := [2, 1, 3, 1, 3, 2, 3, 3, 2]
def baseStart_924104 : Nat := 118140960795 + 924104 * 2 ^ 59
def prefixEnd_924104 : Nat := 4983230072969 + 3 ^ 40 * 924104 * 2
def baseEnd_924104 : Nat := 421786245993384597822337

theorem tailTrace_924104 : CollatzResearch.WordTrace tailWord_924104 prefixEnd_924104 421786245993384597822337 := by
  unfold tailWord_924104
  simp only [CollatzResearch.WordTrace]
  refine ⟨16852420922068253621633683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22469894562757671495511577 16852420922068253621633683)
  ·
    refine ⟨25278631383102380432450525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16852420922068253621633683 25278631383102380432450525)
    ·
      refine ⟨9479486768663392662168947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25278631383102380432450525 9479486768663392662168947)
      ·
        refine ⟨14219230152995088993253421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9479486768663392662168947 14219230152995088993253421)
        ·
          refine ⟨5332211307373158372470033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14219230152995088993253421 5332211307373158372470033)
          ·
            refine ⟨3999158480529868779352525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5332211307373158372470033 3999158480529868779352525)
            ·
              refine ⟨1499684430198700792257197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3999158480529868779352525 1499684430198700792257197)
              ·
                refine ⟨562381661324512797096449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1499684430198700792257197 562381661324512797096449)
                ·
                  refine ⟨421786245993384597822337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 562381661324512797096449 421786245993384597822337)
                  ·
                    rfl

theorem cell20_924104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 3, 3, 2].length) (baseStart_924104 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_924104 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_924104 prefixEnd_924104 := by exact prefixLift 924104
  have htrace : WordTrace (prefixWord ++ tailWord_924104) baseStart_924104 baseEnd_924104 := by
    simpa [prefixWord, tailWord_924104, baseEnd_924104] using wordTrace_append hprefix tailTrace_924104
  have hstable : (prefixWord ++ tailWord_924104).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924104).length < 2 ^ (prefixWord ++ tailWord_924104).sum := by decide
  have hdescent : baseEnd_924104 < baseStart_924104 := by decide
  rcases family_descends (prefixWord ++ tailWord_924104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924118 : List Nat := [5, 2, 1, 1, 1, 1, 1, 3, 5]
def baseStart_924118 : Nat := 118140960795 + 924118 * 2 ^ 59
def prefixEnd_924118 : Nat := 4983230072969 + 3 ^ 40 * 924118 * 2
def baseEnd_924118 : Nat := 421792635974862771355613

theorem tailTrace_924118 : CollatzResearch.WordTrace tailWord_924118 prefixEnd_924118 421792635974862771355613 := by
  unfold tailWord_924118
  simp only [CollatzResearch.WordTrace]
  refine ⟨2106584529130361727142313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22470234977390525089518005 2106584529130361727142313)
  ·
    refine ⟨1579938396847771295356735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2106584529130361727142313 1579938396847771295356735)
    ·
      refine ⟨2369907595271656943035103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1579938396847771295356735 2369907595271656943035103)
      ·
        refine ⟨3554861392907485414552655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2369907595271656943035103 3554861392907485414552655)
        ·
          refine ⟨5332292089361228121828983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3554861392907485414552655 5332292089361228121828983)
          ·
            refine ⟨7998438134041842182743475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5332292089361228121828983 7998438134041842182743475)
            ·
              refine ⟨11997657201062763274115213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7998438134041842182743475 11997657201062763274115213)
              ·
                refine ⟨4499121450398536227793205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11997657201062763274115213 4499121450398536227793205)
                ·
                  refine ⟨421792635974862771355613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4499121450398536227793205 421792635974862771355613)
                  ·
                    rfl

theorem cell20_924118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_924118 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_924118 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_924118 prefixEnd_924118 := by exact prefixLift 924118
  have htrace : WordTrace (prefixWord ++ tailWord_924118) baseStart_924118 baseEnd_924118 := by
    simpa [prefixWord, tailWord_924118, baseEnd_924118] using wordTrace_append hprefix tailTrace_924118
  have hstable : (prefixWord ++ tailWord_924118).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924118).length < 2 ^ (prefixWord ++ tailWord_924118).sum := by decide
  have hdescent : baseEnd_924118 < baseStart_924118 := by decide
  rcases family_descends (prefixWord ++ tailWord_924118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924139 : List Nat := [1, 1, 1, 1, 2, 3, 5, 3, 3]
def baseStart_924139 : Nat := 118140960795 + 924139 * 2 ^ 59
def prefixEnd_924139 : Nat := 4983230072969 + 3 ^ 40 * 924139 * 2
def baseEnd_924139 : Nat := 421802220947080031655527

theorem tailTrace_924139 : CollatzResearch.WordTrace tailWord_924139 prefixEnd_924139 421802220947080031655527 := by
  unfold tailWord_924139
  simp only [CollatzResearch.WordTrace]
  refine ⟨33706118399009708220791471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22470745599339805480527647 33706118399009708220791471)
  ·
    refine ⟨50559177598514562331187207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33706118399009708220791471 50559177598514562331187207)
    ·
      refine ⟨75838766397771843496780811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50559177598514562331187207 75838766397771843496780811)
      ·
        refine ⟨113758149596657765245171217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75838766397771843496780811 113758149596657765245171217)
        ·
          refine ⟨85318612197493323933878413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113758149596657765245171217 85318612197493323933878413)
          ·
            refine ⟨31994479574059996475204405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85318612197493323933878413 31994479574059996475204405)
            ·
              refine ⟨2999482460068124669550413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31994479574059996475204405 2999482460068124669550413)
              ·
                refine ⟨1124805922525546751081405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2999482460068124669550413 1124805922525546751081405)
                ·
                  refine ⟨421802220947080031655527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1124805922525546751081405 421802220947080031655527)
                  ·
                    rfl

theorem cell20_924139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 3, 3].length) (baseStart_924139 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_924139 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_924139 prefixEnd_924139 := by exact prefixLift 924139
  have htrace : WordTrace (prefixWord ++ tailWord_924139) baseStart_924139 baseEnd_924139 := by
    simpa [prefixWord, tailWord_924139, baseEnd_924139] using wordTrace_append hprefix tailTrace_924139
  have hstable : (prefixWord ++ tailWord_924139).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924139).length < 2 ^ (prefixWord ++ tailWord_924139).sum := by decide
  have hdescent : baseEnd_924139 < baseStart_924139 := by decide
  rcases family_descends (prefixWord ++ tailWord_924139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924153 : List Nat := [1, 2, 1, 3, 1, 2, 4, 6]
def baseStart_924153 : Nat := 118140960795 + 924153 * 2 ^ 59
def prefixEnd_924153 : Nat := 4983230072969 + 3 ^ 40 * 924153 * 2
def baseEnd_924153 : Nat := 140602870309519401729601

theorem tailTrace_924153 : CollatzResearch.WordTrace tailWord_924153 prefixEnd_924153 140602870309519401729601 := by
  unfold tailWord_924153
  simp only [CollatzResearch.WordTrace]
  refine ⟨33706629020958988611801113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22471086013972659074534075 33706629020958988611801113)
  ·
    refine ⟨25279971765719241458850835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33706629020958988611801113 25279971765719241458850835)
    ·
      refine ⟨37919957648578862188276253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25279971765719241458850835 37919957648578862188276253)
      ·
        refine ⟨14219984118217073320603595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37919957648578862188276253 14219984118217073320603595)
        ·
          refine ⟨21329976177325609980905393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14219984118217073320603595 21329976177325609980905393)
          ·
            refine ⟨15997482132994207485679045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21329976177325609980905393 15997482132994207485679045)
            ·
              refine ⟨2999527899936413903564821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15997482132994207485679045 2999527899936413903564821)
              ·
                refine ⟨140602870309519401729601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2999527899936413903564821 140602870309519401729601)
                ·
                  rfl

theorem cell20_924153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 6].length) (baseStart_924153 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_924153 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_924153 prefixEnd_924153 := by exact prefixLift 924153
  have htrace : WordTrace (prefixWord ++ tailWord_924153) baseStart_924153 baseEnd_924153 := by
    simpa [prefixWord, tailWord_924153, baseEnd_924153] using wordTrace_append hprefix tailTrace_924153
  have hstable : (prefixWord ++ tailWord_924153).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924153).length < 2 ^ (prefixWord ++ tailWord_924153).sum := by decide
  have hdescent : baseEnd_924153 < baseStart_924153 := by decide
  rcases family_descends (prefixWord ++ tailWord_924153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924163 : List Nat := [1, 1, 1, 3, 2, 1, 4, 5, 2]
def baseStart_924163 : Nat := 118140960795 + 924163 * 2 ^ 59
def prefixEnd_924163 : Nat := 4983230072969 + 3 ^ 40 * 924163 * 2
def baseEnd_924163 : Nat := 421813175201042614855429

theorem tailTrace_924163 : CollatzResearch.WordTrace tailWord_924163 prefixEnd_924163 421813175201042614855429 := by
  unfold tailWord_924163
  simp only [CollatzResearch.WordTrace]
  refine ⟨33706993750922760319665143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22471329167281840213110095 33706993750922760319665143)
  ·
    refine ⟨50560490626384140479497715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33706993750922760319665143 50560490626384140479497715)
    ·
      refine ⟨75840735939576210719246573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50560490626384140479497715 75840735939576210719246573)
      ·
        refine ⟨28440275977341079019717465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75840735939576210719246573 28440275977341079019717465)
        ·
          refine ⟨21330206983005809264788099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28440275977341079019717465 21330206983005809264788099)
          ·
            refine ⟨31995310474508713897182149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21330206983005809264788099 31995310474508713897182149)
            ·
              refine ⟨5999120713970383855721653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31995310474508713897182149 5999120713970383855721653)
              ·
                refine ⟨562417566934723486473905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5999120713970383855721653 562417566934723486473905)
                ·
                  refine ⟨421813175201042614855429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 562417566934723486473905 421813175201042614855429)
                  ·
                    rfl

theorem cell20_924163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 5, 2].length) (baseStart_924163 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_924163 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_924163 prefixEnd_924163 := by exact prefixLift 924163
  have htrace : WordTrace (prefixWord ++ tailWord_924163) baseStart_924163 baseEnd_924163 := by
    simpa [prefixWord, tailWord_924163, baseEnd_924163] using wordTrace_append hprefix tailTrace_924163
  have hstable : (prefixWord ++ tailWord_924163).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924163).length < 2 ^ (prefixWord ++ tailWord_924163).sum := by decide
  have hdescent : baseEnd_924163 < baseStart_924163 := by decide
  rcases family_descends (prefixWord ++ tailWord_924163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924166 : List Nat := [6, 2, 1, 1, 1, 9]
def baseStart_924166 : Nat := 118140960795 + 924166 * 2 ^ 59
def prefixEnd_924166 : Nat := 4983230072969 + 3 ^ 40 * 924166 * 2
def baseEnd_924166 : Nat := 15622760906769923620571

theorem tailTrace_924166 : CollatzResearch.WordTrace tailWord_924166 prefixEnd_924166 15622760906769923620571 := by
  unfold tailWord_924166
  simp only [CollatzResearch.WordTrace]
  refine ⟨1053346974059746619750761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 22471402113274594554682901 1053346974059746619750761)
  ·
    refine ⟨790010230544809964813071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1053346974059746619750761 790010230544809964813071)
    ·
      refine ⟨1185015345817214947219607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 790010230544809964813071 1185015345817214947219607)
      ·
        refine ⟨1777523018725822420829411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1185015345817214947219607 1777523018725822420829411)
        ·
          refine ⟨2666284528088733631244117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1777523018725822420829411 2666284528088733631244117)
          ·
            refine ⟨15622760906769923620571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2666284528088733631244117 15622760906769923620571)
            ·
              rfl

theorem cell20_924166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 9].length) (baseStart_924166 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_924166 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_924166 prefixEnd_924166 := by exact prefixLift 924166
  have htrace : WordTrace (prefixWord ++ tailWord_924166) baseStart_924166 baseEnd_924166 := by
    simpa [prefixWord, tailWord_924166, baseEnd_924166] using wordTrace_append hprefix tailTrace_924166
  have hstable : (prefixWord ++ tailWord_924166).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924166).length < 2 ^ (prefixWord ++ tailWord_924166).sum := by decide
  have hdescent : baseEnd_924166 < baseStart_924166 := by decide
  rcases family_descends (prefixWord ++ tailWord_924166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924218 : List Nat := [3, 1, 1, 1, 3, 4, 2, 3, 2]
def baseStart_924218 : Nat := 118140960795 + 924218 * 2 ^ 59
def prefixEnd_924218 : Nat := 4983230072969 + 3 ^ 40 * 924218 * 2
def baseEnd_924218 : Nat := 421838278699706868021871

theorem tailTrace_924218 : CollatzResearch.WordTrace tailWord_924218 prefixEnd_924218 421838278699706868021871 := by
  unfold tailWord_924218
  simp only [CollatzResearch.WordTrace]
  refine ⟨8427249941430876178229327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22472666510482336475278205 8427249941430876178229327)
  ·
    refine ⟨12640874912146314267343991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8427249941430876178229327 12640874912146314267343991)
    ·
      refine ⟨18961312368219471401015987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12640874912146314267343991 18961312368219471401015987)
      ·
        refine ⟨28441968552329207101523981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18961312368219471401015987 28441968552329207101523981)
        ·
          refine ⟨10665738207123452663071493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28441968552329207101523981 10665738207123452663071493)
          ·
            refine ⟨1999825913835647374325905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10665738207123452663071493 1999825913835647374325905)
            ·
              refine ⟨1499869435376735530744429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1999825913835647374325905 1499869435376735530744429)
              ·
                refine ⟨562451038266275824029161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1499869435376735530744429 562451038266275824029161)
                ·
                  refine ⟨421838278699706868021871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 562451038266275824029161 421838278699706868021871)
                  ·
                    rfl

theorem cell20_924218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 2, 3, 2].length) (baseStart_924218 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_924218 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_924218 prefixEnd_924218 := by exact prefixLift 924218
  have htrace : WordTrace (prefixWord ++ tailWord_924218) baseStart_924218 baseEnd_924218 := by
    simpa [prefixWord, tailWord_924218, baseEnd_924218] using wordTrace_append hprefix tailTrace_924218
  have hstable : (prefixWord ++ tailWord_924218).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924218).length < 2 ^ (prefixWord ++ tailWord_924218).sum := by decide
  have hdescent : baseEnd_924218 < baseStart_924218 := by decide
  rcases family_descends (prefixWord ++ tailWord_924218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924228 : List Nat := [2, 3, 5, 1, 1, 1, 1, 1, 5]
def baseStart_924228 : Nat := 118140960795 + 924228 * 2 ^ 59
def prefixEnd_924228 : Nat := 4983230072969 + 3 ^ 40 * 924228 * 2
def baseEnd_924228 : Nat := 421842842972191277688497

theorem tailTrace_924228 : CollatzResearch.WordTrace tailWord_924228 prefixEnd_924228 421842842972191277688497 := by
  unfold tailWord_924228
  simp only [CollatzResearch.WordTrace]
  refine ⟨16854682247843638210390669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22472909663791517613854225 16854682247843638210390669)
  ·
    refine ⟨6320505842941364328896501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16854682247843638210390669 6320505842941364328896501)
    ·
      refine ⟨592547422775752905834047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6320505842941364328896501 592547422775752905834047)
      ·
        refine ⟨888821134163629358751071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 592547422775752905834047 888821134163629358751071)
        ·
          refine ⟨1333231701245444038126607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 888821134163629358751071 1333231701245444038126607)
          ·
            refine ⟨1999847551868166057189911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1333231701245444038126607 1999847551868166057189911)
            ·
              refine ⟨2999771327802249085784867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1999847551868166057189911 2999771327802249085784867)
              ·
                refine ⟨4499656991703373628677301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2999771327802249085784867 4499656991703373628677301)
                ·
                  refine ⟨421842842972191277688497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4499656991703373628677301 421842842972191277688497)
                  ·
                    rfl

theorem cell20_924228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 1, 5].length) (baseStart_924228 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_924228 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_924228 prefixEnd_924228 := by exact prefixLift 924228
  have htrace : WordTrace (prefixWord ++ tailWord_924228) baseStart_924228 baseEnd_924228 := by
    simpa [prefixWord, tailWord_924228, baseEnd_924228] using wordTrace_append hprefix tailTrace_924228
  have hstable : (prefixWord ++ tailWord_924228).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924228).length < 2 ^ (prefixWord ++ tailWord_924228).sum := by decide
  have hdescent : baseEnd_924228 < baseStart_924228 := by decide
  rcases family_descends (prefixWord ++ tailWord_924228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924229 : List Nat := [1, 3, 1, 1, 1, 6, 7]
def baseStart_924229 : Nat := 118140960795 + 924229 * 2 ^ 59
def prefixEnd_924229 : Nat := 4983230072969 + 3 ^ 40 * 924229 * 2
def baseEnd_924229 : Nat := 46871477711048857628351

theorem tailTrace_924229 : CollatzResearch.WordTrace tailWord_924229 prefixEnd_924229 46871477711048857628351 := by
  unfold tailWord_924229
  simp only [CollatzResearch.WordTrace]
  refine ⟨33709400968683653591567741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22472933979122435727711827 33709400968683653591567741)
  ·
    refine ⟨12641025363256370096837903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33709400968683653591567741 12641025363256370096837903)
    ·
      refine ⟨18961538044884555145256855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12641025363256370096837903 18961538044884555145256855)
      ·
        refine ⟨28442307067326832717885283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18961538044884555145256855 28442307067326832717885283)
        ·
          refine ⟨42663460600990249076827925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28442307067326832717885283 42663460600990249076827925)
          ·
            refine ⟨1999849715671417925476309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 42663460600990249076827925 1999849715671417925476309)
            ·
              refine ⟨46871477711048857628351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1999849715671417925476309 46871477711048857628351)
              ·
                rfl

theorem cell20_924229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 7].length) (baseStart_924229 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_924229 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_924229 prefixEnd_924229 := by exact prefixLift 924229
  have htrace : WordTrace (prefixWord ++ tailWord_924229) baseStart_924229 baseEnd_924229 := by
    simpa [prefixWord, tailWord_924229, baseEnd_924229] using wordTrace_append hprefix tailTrace_924229
  have hstable : (prefixWord ++ tailWord_924229).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924229).length < 2 ^ (prefixWord ++ tailWord_924229).sum := by decide
  have hdescent : baseEnd_924229 < baseStart_924229 := by decide
  rcases family_descends (prefixWord ++ tailWord_924229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924239 : List Nat := [1, 1, 2, 1, 1, 2, 6, 4, 2]
def baseStart_924239 : Nat := 118140960795 + 924239 * 2 ^ 59
def prefixEnd_924239 : Nat := 4983230072969 + 3 ^ 40 * 924239 * 2
def baseEnd_924239 : Nat := 421847863671924128321785

theorem tailTrace_924239 : CollatzResearch.WordTrace tailWord_924239 prefixEnd_924239 421847863671924128321785 := by
  unfold tailWord_924239
  simp only [CollatzResearch.WordTrace]
  refine ⟨33709765698647425299431771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22473177132431616866287847 33709765698647425299431771)
  ·
    refine ⟨50564648547971137949147657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33709765698647425299431771 50564648547971137949147657)
    ·
      refine ⟨37923486410978353461860743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50564648547971137949147657 37923486410978353461860743)
      ·
        refine ⟨56885229616467530192791115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37923486410978353461860743 56885229616467530192791115)
        ·
          refine ⟨85327844424701295289186673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56885229616467530192791115 85327844424701295289186673)
          ·
            refine ⟨63995883318525971466890005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85327844424701295289186673 63995883318525971466890005)
            ·
              refine ⟨2999807030555904912510469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 63995883318525971466890005 2999807030555904912510469)
              ·
                refine ⟨562463818229232171095713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2999807030555904912510469 562463818229232171095713)
                ·
                  refine ⟨421847863671924128321785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 562463818229232171095713 421847863671924128321785)
                  ·
                    rfl

theorem cell20_924239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 4, 2].length) (baseStart_924239 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_924239 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_924239 prefixEnd_924239 := by exact prefixLift 924239
  have htrace : WordTrace (prefixWord ++ tailWord_924239) baseStart_924239 baseEnd_924239 := by
    simpa [prefixWord, tailWord_924239, baseEnd_924239] using wordTrace_append hprefix tailTrace_924239
  have hstable : (prefixWord ++ tailWord_924239).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924239).length < 2 ^ (prefixWord ++ tailWord_924239).sum := by decide
  have hdescent : baseEnd_924239 < baseStart_924239 := by decide
  rcases family_descends (prefixWord ++ tailWord_924239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924260 : List Nat := [2, 3, 1, 1, 2, 2, 1, 4, 4]
def baseStart_924260 : Nat := 118140960795 + 924260 * 2 ^ 59
def prefixEnd_924260 : Nat := 4983230072969 + 3 ^ 40 * 924260 * 2
def baseEnd_924260 : Nat := 421857448644141388621699

theorem tailTrace_924260 : CollatzResearch.WordTrace tailWord_924260 prefixEnd_924260 421857448644141388621699 := by
  unfold tailWord_924260
  simp only [CollatzResearch.WordTrace]
  refine ⟨16855265815785672942973117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22473687754380897257297489 16855265815785672942973117)
  ·
    refine ⟨6320724680919627353614919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16855265815785672942973117 6320724680919627353614919)
    ·
      refine ⟨9481087021379441030422379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6320724680919627353614919 9481087021379441030422379)
      ·
        refine ⟨14221630532069161545633569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9481087021379441030422379 14221630532069161545633569)
        ·
          refine ⟨10666222899051871159225177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14221630532069161545633569 10666222899051871159225177)
          ·
            refine ⟨7999667174288903369418883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10666222899051871159225177 7999667174288903369418883)
            ·
              refine ⟨11999500761433355054128325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7999667174288903369418883 11999500761433355054128325)
              ·
                refine ⟨2249906392768754072649061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11999500761433355054128325 2249906392768754072649061)
                ·
                  refine ⟨421857448644141388621699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2249906392768754072649061 421857448644141388621699)
                  ·
                    rfl

theorem cell20_924260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 4, 4].length) (baseStart_924260 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_924260 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_924260 prefixEnd_924260 := by exact prefixLift 924260
  have htrace : WordTrace (prefixWord ++ tailWord_924260) baseStart_924260 baseEnd_924260 := by
    simpa [prefixWord, tailWord_924260, baseEnd_924260] using wordTrace_append hprefix tailTrace_924260
  have hstable : (prefixWord ++ tailWord_924260).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924260).length < 2 ^ (prefixWord ++ tailWord_924260).sum := by decide
  have hdescent : baseEnd_924260 < baseStart_924260 := by decide
  rcases family_descends (prefixWord ++ tailWord_924260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924342 : List Nat := [5, 1, 3, 1, 2, 1, 2, 2, 3]
def baseStart_924342 : Nat := 118140960795 + 924342 * 2 ^ 59
def prefixEnd_924342 : Nat := 4983230072969 + 3 ^ 40 * 924342 * 2
def baseEnd_924342 : Nat := 421894875678513547888031

theorem tailTrace_924342 : CollatzResearch.WordTrace tailWord_924342 prefixEnd_924342 421894875678513547888031 := by
  unfold tailWord_924342
  simp only [CollatzResearch.WordTrace]
  refine ⟨2107095151079642118151955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22475681611516182593620853 2107095151079642118151955)
  ·
    refine ⟨3160642726619463177227933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2107095151079642118151955 3160642726619463177227933)
    ·
      refine ⟨1185241022482298691460475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3160642726619463177227933 1185241022482298691460475)
      ·
        refine ⟨1777861533723448037190713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1185241022482298691460475 1777861533723448037190713)
        ·
          refine ⟨1333396150292586027893035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1777861533723448037190713 1333396150292586027893035)
          ·
            refine ⟨2000094225438879041839553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1333396150292586027893035 2000094225438879041839553)
            ·
              refine ⟨1500070669079159281379665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2000094225438879041839553 1500070669079159281379665)
              ·
                refine ⟨1125053001809369461034749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1500070669079159281379665 1125053001809369461034749)
                ·
                  refine ⟨421894875678513547888031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1125053001809369461034749 421894875678513547888031)
                  ·
                    rfl

theorem cell20_924342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 2, 2, 3].length) (baseStart_924342 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_924342 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_924342 prefixEnd_924342 := by exact prefixLift 924342
  have htrace : WordTrace (prefixWord ++ tailWord_924342) baseStart_924342 baseEnd_924342 := by
    simpa [prefixWord, tailWord_924342, baseEnd_924342] using wordTrace_append hprefix tailTrace_924342
  have hstable : (prefixWord ++ tailWord_924342).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924342).length < 2 ^ (prefixWord ++ tailWord_924342).sum := by decide
  have hdescent : baseEnd_924342 < baseStart_924342 := by decide
  rcases family_descends (prefixWord ++ tailWord_924342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924343 : List Nat := [1, 1, 3, 1, 6, 8]
def baseStart_924343 : Nat := 118140960795 + 924343 * 2 ^ 59
def prefixEnd_924343 : Nat := 4983230072969 + 3 ^ 40 * 924343 * 2
def baseEnd_924343 : Nat := 15625753040954147735359

theorem tailTrace_924343 : CollatzResearch.WordTrace tailWord_924343 prefixEnd_924343 15625753040954147735359 := by
  unfold tailWord_924343
  simp only [CollatzResearch.WordTrace]
  refine ⟨33713558890270651061217683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22475705926847100707478455 33713558890270651061217683)
  ·
    refine ⟨50570338335405976591826525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33713558890270651061217683 50570338335405976591826525)
    ·
      refine ⟨18963876875777241221934947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50570338335405976591826525 18963876875777241221934947)
      ·
        refine ⟨28445815313665861832902421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18963876875777241221934947 28445815313665861832902421)
        ·
          refine ⟨1333397592828087273417301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 28445815313665861832902421 1333397592828087273417301)
          ·
            refine ⟨15625753040954147735359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1333397592828087273417301 15625753040954147735359)
            ·
              rfl

theorem cell20_924343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 8].length) (baseStart_924343 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_924343 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_924343 prefixEnd_924343 := by exact prefixLift 924343
  have htrace : WordTrace (prefixWord ++ tailWord_924343) baseStart_924343 baseEnd_924343 := by
    simpa [prefixWord, tailWord_924343, baseEnd_924343] using wordTrace_append hprefix tailTrace_924343
  have hstable : (prefixWord ++ tailWord_924343).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924343).length < 2 ^ (prefixWord ++ tailWord_924343).sum := by decide
  have hdescent : baseEnd_924343 < baseStart_924343 := by decide
  rcases family_descends (prefixWord ++ tailWord_924343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924349 : List Nat := [1, 4, 1, 2, 1, 5, 2, 2, 2]
def baseStart_924349 : Nat := 118140960795 + 924349 * 2 ^ 59
def prefixEnd_924349 : Nat := 4983230072969 + 3 ^ 40 * 924349 * 2
def baseEnd_924349 : Nat := 421898070669252634654669

theorem tailTrace_924349 : CollatzResearch.WordTrace tailWord_924349 prefixEnd_924349 421898070669252634654669 := by
  unfold tailWord_924349
  simp only [CollatzResearch.WordTrace]
  refine ⟨33713777728248914085936101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22475851818832609390624067 33713777728248914085936101)
  ·
    refine ⟨6321333324046671391113019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33713777728248914085936101 6321333324046671391113019)
    ·
      refine ⟨9481999986070007086669529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6321333324046671391113019 9481999986070007086669529)
      ·
        refine ⟨7111499989552505315002147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9481999986070007086669529 7111499989552505315002147)
        ·
          refine ⟨10667249984328757972503221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7111499989552505315002147 10667249984328757972503221)
          ·
            refine ⟨1000054686030821059922177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10667249984328757972503221 1000054686030821059922177)
            ·
              refine ⟨750041014523115794941633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1000054686030821059922177 750041014523115794941633)
              ·
                refine ⟨562530760892336846206225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 750041014523115794941633 562530760892336846206225)
                ·
                  refine ⟨421898070669252634654669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 562530760892336846206225 421898070669252634654669)
                  ·
                    rfl

theorem cell20_924349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 2, 2, 2].length) (baseStart_924349 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_924349 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_924349 prefixEnd_924349 := by exact prefixLift 924349
  have htrace : WordTrace (prefixWord ++ tailWord_924349) baseStart_924349 baseEnd_924349 := by
    simpa [prefixWord, tailWord_924349, baseEnd_924349] using wordTrace_append hprefix tailTrace_924349
  have hstable : (prefixWord ++ tailWord_924349).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924349).length < 2 ^ (prefixWord ++ tailWord_924349).sum := by decide
  have hdescent : baseEnd_924349 < baseStart_924349 := by decide
  rcases family_descends (prefixWord ++ tailWord_924349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924360 : List Nat := [2, 1, 3, 1, 2, 5, 1, 5]
def baseStart_924360 : Nat := 118140960795 + 924360 * 2 ^ 59
def prefixEnd_924360 : Nat := 4983230072969 + 3 ^ 40 * 924360 * 2
def baseEnd_924360 : Nat := 140634363789661828429319

theorem tailTrace_924360 : CollatzResearch.WordTrace tailWord_924360 prefixEnd_924360 140634363789661828429319 := by
  unfold tailWord_924360
  simp only [CollatzResearch.WordTrace]
  refine ⟨16857089465604531482293267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22476119287472708643057689 16857089465604531482293267)
  ·
    refine ⟨25285634198406797223439901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16857089465604531482293267 25285634198406797223439901)
    ·
      refine ⟨9482112824402548958789963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25285634198406797223439901 9482112824402548958789963)
      ·
        refine ⟨14223169236603823438184945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9482112824402548958789963 14223169236603823438184945)
        ·
          refine ⟨10667376927452867578638709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14223169236603823438184945 10667376927452867578638709)
          ·
            refine ⟨1000066586948706335497379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10667376927452867578638709 1000066586948706335497379)
            ·
              refine ⟨1500099880423059503246069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1000066586948706335497379 1500099880423059503246069)
              ·
                refine ⟨140634363789661828429319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1500099880423059503246069 140634363789661828429319)
                ·
                  rfl

theorem cell20_924360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 1, 5].length) (baseStart_924360 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_924360 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_924360 prefixEnd_924360 := by exact prefixLift 924360
  have htrace : WordTrace (prefixWord ++ tailWord_924360) baseStart_924360 baseEnd_924360 := by
    simpa [prefixWord, tailWord_924360, baseEnd_924360] using wordTrace_append hprefix tailTrace_924360
  have hstable : (prefixWord ++ tailWord_924360).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924360).length < 2 ^ (prefixWord ++ tailWord_924360).sum := by decide
  have hdescent : baseEnd_924360 < baseStart_924360 := by decide
  rcases family_descends (prefixWord ++ tailWord_924360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
